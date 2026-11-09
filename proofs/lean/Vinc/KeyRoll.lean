import Vinc.Axioms
import Vinc.Varint
import Vinc.Record

/-!
# The key roll: the REKEY codec, the Roll state machine, post-compromise security and the roll trigger

A model of `vinc-security/src/keyroll.rs`, written to be read against it.

* `Rekey` is the wire form of a REKEY body: `kind(1)` (0 request, 1 answer), `share(32)`, and for an answer `echo(8)`
  (the identifier of the request it answers) and a varint `switch_pn`. `encode`/`decode` follow the code, strictly: an unknown kind, a short body, a trailing byte and
  a `switch_pn` of 2^63 or more are refused. `decode (encode r) = r` and an accepted body is the one encoding of
  its message (the varint is `Vinc.Varint`).
* `Roll` is the state machine: Idle or Requested, the dialer flag, `last` (the last request answered and the answer
  given) and the completed-rolls counter. `start`, `onRequest` and `onAnswer` keep the order of the checks of the
  code, including the state a failure leaves behind (the accepting side that dropped its own request and then
  failed on the random generator or the peer share stays Idle). A fresh X25519 secret is an input (`fresh`), an
  atom drawn by the caller; `none` stands for a refused generator.
* The Diffie-Hellman model is symbolic and perfect: a share is `pub a` of an atom `a` owned by a node, the
  Diffie-Hellman value of two atoms is the unordered pair (`Dh_comm`), the identifier of a request share `sh` is
  `id sh` (a short hash, injective here), the value of a roll has the identifier bound into it (`bound (id sh) dh`,
  the code's `extract(dh, id)`), a traffic secret is the free term `base d`, `roll s dh`, and a key is `key s`.
  Terms are equal iff built the same way.
* An answer carries the identifier of the request it answers (`Msg.to`, the echo) and `onAnswer` takes it only when
  the echo names the request that is out: an answer to any other request is ignored and changes nothing.
* `Known` is the deduction of a passive attacker that owns the atoms of one node `att` and a set of leaked base
  secrets. `post_compromise`: if it learned a secret `s` of the old generation, it does not know the key after a
  roll whose Diffie-Hellman atoms it does not own, and (`post_compromise_chain`) neither any later one.
  The attacker of this theorem is PASSIVE during the roll: REKEY travels inside packets authenticated under the
  current keys, so an attacker who holds the current keys can forge a REKEY and mount a man-in-the-middle (it then
  owns an atom of the Diffie-Hellman value); a roll recovers confidentiality only against an attacker that stole the
  secrets and then stopped acting on the path.
* `due` is the roll trigger.

The Lean counterpart of `proofs/tla/KeyRoll.tla` (layer, system), `RekeyCodec.tla` (codec). Trace validation:
`TraceKeyRoll.lean`.
-/

namespace Vinc.KeyRoll
open Vinc

/-! ## The codec -/

/-- A REKEY message: `answer`, the 32-byte `share` and, for an answer, the 8-byte `echo` (the identifier of the
request it answers) and the first packet number sealed under the new keys. A request has `echo` zero and
`switchPn = 0` (`Rekey.echo` and `Rekey.switch_pn` "zero in a request"). -/
structure Rekey where
  answer : Bool
  share : List Nat
  echo : List Nat
  switchPn : Nat
  deriving DecidableEq

/-- A message the code can build: a 32-byte share and an 8-byte echo of bytes; a request carries zeros; a number is
a `u64`. -/
def Rekey.WF (r : Rekey) : Prop :=
  r.share.length = 32 ∧ Varint.ValidBytes r.share ∧ r.echo.length = 8 ∧ Varint.ValidBytes r.echo ∧
    (r.answer = false → r.echo = List.replicate 8 0 ∧ r.switchPn = 0) ∧ r.switchPn < 2 ^ 64

/-- `Rekey::encode` into a buffer large enough; `none` is the `VarintOverflow` of a switch number of 2^63 or more. -/
def Rekey.encode (r : Rekey) : Option (List Nat) :=
  if r.answer then
    if r.switchPn ≥ Varint.limit then none
    else some (1 :: r.share ++ r.echo ++ Varint.encodeBytes r.switchPn)
  else some (0 :: r.share)

/-- The reasons `Rekey::decode` refuses. -/
inductive DecErr where
  | kind | short | trailing | varint
  deriving DecidableEq, Repr

/-- `Rekey::decode`: the kind byte, the 32-byte share, for an answer the 8-byte echo and the varint, then nothing. -/
def Rekey.decode (buf : List Nat) : Except DecErr Rekey :=
  match buf with
  | [] => .error .short
  | k :: rest =>
    if k > 1 then .error .kind
    else if rest.length < 32 then .error .short
    else
      let share := rest.take 32
      let after := rest.drop 32
      if k = 1 then
        if after.length < 8 then .error .short
        else
          match Varint.decode (after.drop 8) with
          | .error _ => .error .varint
          | .ok (v, n) => if n = (after.drop 8).length then .ok ⟨true, share, after.take 8, v⟩ else .error .trailing
      else if after.isEmpty then .ok ⟨false, share, List.replicate 8 0, 0⟩ else .error .trailing

/-- A request is 33 bytes. -/
theorem encode_request_len (r : Rekey) (h : r.answer = false) (hw : r.share.length = 32) :
    ∃ b, r.encode = some b ∧ b.length = 33 := by
  refine ⟨0 :: r.share, by simp [Rekey.encode, h], by simp [hw]⟩

/-- An answer is 42 to 50 bytes. -/
theorem encode_answer_len (r : Rekey) (h : r.answer = true) (hw : r.share.length = 32) (he : r.echo.length = 8)
    (hv : r.switchPn < Varint.limit) :
    ∃ b, r.encode = some b ∧ 42 ≤ b.length ∧ b.length ≤ 50 := by
  have hl := Varint.encode_length r.switchPn hv
  have h1 := Varint.encodedLen_pos r.switchPn
  have hn : ¬ r.switchPn ≥ Varint.limit := Nat.not_le.mpr hv
  refine ⟨(1 :: r.share) ++ r.echo ++ Varint.encodeBytes r.switchPn, by simp [Rekey.encode, h, hn], ?_⟩
  simp only [List.length_append, List.length_cons, hw, he, Varint.length_encodeBytes]
  have := hl.2
  unfold Varint.maxLen at this
  omega

/-- Decoding a request body. -/
theorem decode_request_body (share : List Nat) (hs : share.length = 32) :
    Rekey.decode (0 :: share) = .ok ⟨false, share, List.replicate 8 0, 0⟩ := by
  have e1 : share.take 32 = share := List.take_of_length_le (by omega)
  have e2 : share.drop 32 = [] := List.drop_of_length_le (by omega)
  have h2 : ¬ (share.length < 32) := by omega
  simp [Rekey.decode, h2, e1, e2]

/-- Decoding an answer body. -/
theorem decode_answer_body (share echo : List Nat) (v : Nat) (hs : share.length = 32) (he : echo.length = 8)
    (hv : v < Varint.limit) :
    Rekey.decode ((1 :: share) ++ echo ++ Varint.encodeBytes v) = .ok ⟨true, share, echo, v⟩ := by
  have key := Varint.decode_encode v [] hv
  simp only [List.append_nil] at key
  have h2 : ¬ ((share ++ echo ++ Varint.encodeBytes v).length < 32) := by simp [hs, he]
  have e0 : (share ++ echo ++ Varint.encodeBytes v) = share ++ (echo ++ Varint.encodeBytes v) := by simp
  have e1 : (share ++ echo ++ Varint.encodeBytes v).take 32 = share := by
    rw [e0, List.take_append_of_le_length (by omega)]; exact List.take_of_length_le (by omega)
  have e2 : (share ++ echo ++ Varint.encodeBytes v).drop 32 = echo ++ Varint.encodeBytes v := by
    rw [e0, List.drop_append_of_le_length (by omega)]; simp [hs]
  have e3 : (echo ++ Varint.encodeBytes v).take 8 = echo := by
    rw [List.take_append_of_le_length (by omega)]; exact List.take_of_length_le (by omega)
  have e4 : (echo ++ Varint.encodeBytes v).drop 8 = Varint.encodeBytes v := by
    rw [List.drop_append_of_le_length (by omega)]; simp [he]
  have h4 : ¬ (32 + (8 + (Varint.encodeBytes v).length) < 32) := by omega
  have h5 : ¬ (8 + (Varint.encodeBytes v).length < 8) := by omega
  simp [Rekey.decode, hs, he, e3, e4, key, h4, h5]

/-- The round trip: decoding an encoding gives the message back. -/
theorem decode_encode (r : Rekey) (hw : r.WF) (b : List Nat) (h : r.encode = some b) : Rekey.decode b = .ok r := by
  obtain ⟨hs, hv, he, hev, hq, hp⟩ := hw
  obtain ⟨a, s, e, p⟩ := r
  simp only at hs hq he
  cases a with
  | true =>
    by_cases hn : p ≥ Varint.limit
    · simp [Rekey.encode, hn] at h
    · simp only [Rekey.encode, hn, if_false, if_true] at h
      simp only [Option.some.injEq] at h
      subst h
      exact decode_answer_body s e p hs he (Nat.lt_of_not_ge hn)
  | false =>
    simp only [Rekey.encode, Bool.false_eq_true, if_false, Option.some.injEq] at h
    subst h
    obtain ⟨he0, hp0⟩ := hq rfl
    subst he0; subst hp0
    exact decode_request_body s hs

/-- Strict decoding: an accepted body is exactly the one encoding of its message, so the encoding is unique:
an accepted body re-encodes to itself. -/
theorem encode_decode (b : List Nat) (hb : Varint.ValidBytes b) (r : Rekey) (h : Rekey.decode b = .ok r) :
    r.encode = some b ∧ r.WF := by
  cases b with
  | nil => simp [Rekey.decode] at h
  | cons k rest =>
    have hrest : Varint.ValidBytes rest := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hsh : ∀ n, n ≤ rest.length → (rest.take n).length = n := fun n hn => by simp; omega
    unfold Rekey.decode at h
    by_cases hk : k > 1
    · simp [hk] at h
    · by_cases hs : rest.length < 32
      · simp [hk, hs] at h
      · have hs' : 32 ≤ rest.length := by omega
        simp only [hk, hs, if_false, Bool.false_eq_true] at h
        have hshare : (rest.take 32).length = 32 := hsh 32 hs'
        have hvs : Varint.ValidBytes (rest.take 32) := fun x hx => hrest x (List.mem_of_mem_take hx)
        by_cases h1 : k = 1
        · subst h1
          simp only [if_true] at h
          by_cases hshort : (rest.drop 32).length < 8
          · have hshort' : rest.length - 32 < 8 := by simpa using hshort
            simp [hshort'] at h
          · simp only [hshort, ite_false] at h
            simp only [List.drop_drop, List.length_drop] at h
            have hshort' : ¬ rest.length - 32 < 8 := by simpa using hshort
            have hecho : ((rest.drop 32).take 8).length = 8 := by simp; omega
            have hevs : Varint.ValidBytes ((rest.drop 32).take 8) := fun x hx =>
              hrest x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
            have hva : Varint.ValidBytes (rest.drop 40) := fun x hx => hrest x (List.mem_of_mem_drop hx)
            have hd2 : (rest.drop 40).length = rest.length - 40 := by simp
            rcases hd : Varint.decode (rest.drop 40) with e | ⟨v, n⟩
            · rw [hd] at h; simp at h
            · rw [hd] at h
              simp only at h
              by_cases hn : n = rest.length - 40
              · rw [if_pos hn, Except.ok.injEq] at h
                subst h
                have hn' : n = (rest.drop 40).length := by rw [hd2]; exact hn
                rw [hn'] at hd
                have hcan := Varint.decode_canonical (rest.drop 40) hva v _ hd
                have hbnd := Varint.decode_bounds (rest.drop 40) hva v _ hd
                rw [List.take_length] at hcan
                have hlt : v < Varint.limit := hbnd.1
                refine ⟨?_, hshare, hvs, hecho, hevs, by simp, ?_⟩
                · have hnl : ¬ v ≥ Varint.limit := by omega
                  simp only [Rekey.encode, ite_true, hnl, ite_false]
                  rw [← hcan.1]
                  have e8 : (rest.drop 32).drop 8 = rest.drop 40 := by simp [List.drop_drop]
                  have := List.take_append_drop 8 (rest.drop 32)
                  rw [e8] at this
                  simp [this]
                · show v < 2 ^ 64
                  have : Varint.limit = 2 ^ 63 := rfl
                  omega
              · rw [if_neg hn] at h; simp at h
        · have hk0 : k = 0 := by omega
          subst hk0
          simp only [show ¬ ((0:Nat) = 1) by omega, if_false] at h
          by_cases hae : (rest.drop 32).isEmpty = true
          · simp only [hae, if_true, Except.ok.injEq] at h
            subst h
            have hd0 : rest.drop 32 = [] := by simpa using hae
            have hrt : rest.take 32 = rest := by
              have := List.take_append_drop 32 rest
              rw [hd0] at this; simpa using this
            refine ⟨?_, hshare, hvs, by simp, ?_, by simp, by simp⟩
            · simp only [Rekey.encode, Bool.false_eq_true, if_false, hrt]
            · intro x hx; simp at hx; omega
          · simp [hae] at h

/-- The encoding is unique: two well-formed messages with the same body are equal. -/
theorem encode_injective (r s : Rekey) (hr : r.WF) (hs : s.WF) (b : List Nat) (h1 : r.encode = some b)
    (h2 : s.encode = some b) : r = s := by
  have a := decode_encode r hr b h1
  have c := decode_encode s hs b h2
  rw [a] at c; exact Except.ok.inj c

/-- Refusals. -/
theorem decode_empty : Rekey.decode [] = .error .short := rfl
theorem decode_unknown_kind (k : Nat) (rest : List Nat) (h : k > 1) : Rekey.decode (k :: rest) = .error .kind := by
  simp [Rekey.decode, h]
theorem decode_short (k : Nat) (rest : List Nat) (h : k ≤ 1) (hs : rest.length < 32) :
    Rekey.decode (k :: rest) = .error .short := by
  have : ¬ k > 1 := by omega
  simp [Rekey.decode, this, hs]
theorem encode_big_switch (r : Rekey) (ha : r.answer = true) (h : r.switchPn ≥ Varint.limit) : r.encode = none := by
  simp [Rekey.encode, ha, h]
/-- A request with a byte after the share is refused. -/
theorem decode_request_trailing (share : List Nat) (x : Nat) (rest : List Nat) (hs : share.length = 32) :
    Rekey.decode (0 :: (share ++ x :: rest)) = .error .trailing := by
  have h1 : ¬ ((0:Nat) > 1) := by omega
  have h2 : ¬ ((share ++ x :: rest).length < 32) := by simp [hs]
  have e2 : (share ++ x :: rest).drop 32 = x :: rest := by
    rw [List.drop_append_of_le_length (by omega)]; simp [hs]
  simp [Rekey.decode, hs, e2]

/-! ## Symbolic terms -/

/-- A secret atom: owned by the node `n`, counter `k`. -/
structure Atom where
  n : Nat
  k : Nat
  deriving DecidableEq, Repr

/-- A total order on atoms, to name the unordered pair of a Diffie-Hellman value. -/
def Atom.le (a b : Atom) : Bool := decide (a.n < b.n ∨ (a.n = b.n ∧ a.k ≤ b.k))

/-- Terms; a free algebra (perfect primitives). -/
inductive T where
  | pub (a : Atom)
  | dh (a b : Atom)
  | base (d : Nat)
  | roll (s dh : T)
  | key (s : T)
  | junk
  /-- The identifier of a request share: a short hash, injective in this model. -/
  | id (s : T)
  /-- A Diffie-Hellman value with the request identifier bound in: `extract(dh, id)`. -/
  | bound (i dh : T)
  deriving DecidableEq, Repr

/-- The Diffie-Hellman value of two atoms: the unordered pair. -/
def Dh (a b : Atom) : T := if Atom.le a b then .dh a b else .dh b a

theorem Dh_comm (a b : Atom) : Dh a b = Dh b a := by
  obtain ⟨an, ak⟩ := a
  obtain ⟨bn, bk⟩ := b
  unfold Dh Atom.le
  by_cases h1 : an < bn ∨ (an = bn ∧ ak ≤ bk) <;> by_cases h2 : bn < an ∨ (bn = an ∧ bk ≤ ak) <;>
    simp only [h1, h2, decide_true, decide_false, if_true, if_false, Bool.false_eq_true]
  all_goals first
    | rfl
    | (exfalso; omega)
    | (have e : an = bn ∧ ak = bk := by omega
       obtain ⟨e1, e2⟩ := e
       subst e1; subst e2; rfl)

/-- `x25519_dh(secret of own, share)`: the share must be a public value (anything else gives no shared secret). -/
def dhOf (own : Atom) : T → Option T
  | .pub b => some (Dh own b)
  | _ => none

/-- The depth of a secret term: the number of rolls behind it. -/
def T.depth : T → Nat
  | .roll s _ => s.depth + 1
  | _ => 0

/-! ## The Roll machine -/

/-- A REKEY message. `to` is the echo of an answer, the identifier of the request it answers (`id` of the request
share); a request carries `junk` (zeros on the wire). `gdh` is a GHOST field (no code reads it): the
Diffie-Hellman value its sender used. -/
structure Msg where
  answer : Bool
  share : T
  spn : Nat
  to : T
  gdh : T
  deriving DecidableEq, Repr

def Msg.req (sh : T) : Msg := ⟨false, sh, 0, .junk, .junk⟩

/-- `Roll::state`. -/
inductive St where
  | idle
  | req (seed : Atom) (request : Msg)
  deriving DecidableEq

/-- The `Failure` variants `Roll` returns. -/
inductive Fail where
  | unexpected | randomness | invalid
  deriving DecidableEq, Repr

/-- `Roll`. -/
structure Roll where
  dialer : Bool
  st : St
  last : Option (T × Msg)
  rolls : Nat
  deriving DecidableEq

def Roll.new (dialer : Bool) : Roll := ⟨dialer, .idle, none, 0⟩

def Roll.isIdle (r : Roll) : Bool := match r.st with | .idle => true | _ => false

/-- `Roll::pending`: the request to send again. -/
def Roll.pending (r : Roll) : Option Msg := match r.st with | .req _ m => some m | .idle => none

/-- `Roll::start`. -/
def Roll.start (r : Roll) (fresh : Option Atom) : Roll × Except Fail Msg :=
  if !r.isIdle then (r, .error .unexpected)
  else match fresh with
    | none => (r, .error .randomness)
    | some a =>
      let m := Msg.req (.pub a)
      ({ r with st := .req a m }, .ok m)

/-- A request whose share is the share of the last request answered. -/
def Roll.isDup (r : Roll) (req : Msg) : Bool :=
  match r.last with
  | some (sh, _) => decide (sh = req.share)
  | none => false

/-- `Roll::on_request`: the answer, and the Diffie-Hellman value to roll with (`none` for a duplicate). The order of
the checks is the code's. -/
def Roll.onRequest (r : Roll) (req : Msg) (spn : Nat) (fresh : Option Atom) :
    Roll × Except Fail (Msg × Option T) :=
  if req.answer then (r, .error .unexpected)
  else if r.isDup req then
    match r.last with
    | some (_, a) => (r, .ok (a, none))
    | none => (r, .error .unexpected)
  else if !r.isIdle && r.dialer then (r, .error .unexpected)
  else
    let r1 := if r.isIdle then r else { r with st := .idle }
    match fresh with
    | none => (r1, .error .randomness)
    | some a =>
      match dhOf a req.share with
      | none => (r1, .error .invalid)
      | some dh =>
        let bd := T.bound (.id req.share) dh
        let ans : Msg := ⟨true, .pub a, spn, .id req.share, bd⟩
        ({ r1 with last := some (req.share, ans), rolls := Record.inc r.rolls }, .ok (ans, some bd))

/-- `Roll::on_answer`: the Diffie-Hellman value (with the request identifier bound in) and the peer's switch
number. An answer whose echo is not the identifier of the request that is out is ignored. -/
def Roll.onAnswer (r : Roll) (a : Msg) : Roll × Except Fail (T × Nat) :=
  if !a.answer then (r, .error .unexpected)
  else match r.st with
    | .idle => (r, .error .unexpected)
    | .req seed m =>
      if a.to != .id m.share then (r, .error .unexpected)
      else
        match dhOf seed a.share with
        | none => (r, .error .invalid)
        | some dh => ({ r with st := .idle, last := none, rolls := Record.inc r.rolls }, .ok (.bound (.id m.share) dh, a.spn))

/-! ### What the machine does -/

theorem start_busy (r : Roll) (fresh : Option Atom) (h : r.isIdle = false) :
    r.start fresh = (r, .error .unexpected) := by simp [Roll.start, h]

theorem start_ok (r : Roll) (a : Atom) (h : r.isIdle = true) :
    r.start (some a) = ({ r with st := .req a (Msg.req (.pub a)) }, .ok (Msg.req (.pub a))) := by
  simp [Roll.start, h]

/-- An answer sent to `on_request`, or a request sent to `on_answer`, is refused and changes nothing. -/
theorem onRequest_answer_kind (r : Roll) (m : Msg) (spn : Nat) (fresh : Option Atom) (h : m.answer = true) :
    r.onRequest m spn fresh = (r, .error .unexpected) := by simp [Roll.onRequest, h]

theorem onAnswer_request_kind (r : Roll) (m : Msg) (h : m.answer = false) :
    r.onAnswer m = (r, .error .unexpected) := by simp [Roll.onAnswer, h]

/-- A duplicate request (the answer was lost) gets the same answer again, no Diffie-Hellman value (so no new key) and
changes nothing: the completed-rolls counter does not move. -/
theorem onRequest_dup (r : Roll) (req : Msg) (spn : Nat) (fresh : Option Atom) (sh : T) (a : Msg)
    (hl : r.last = some (sh, a)) (hs : sh = req.share) (hk : req.answer = false) :
    r.onRequest req spn fresh = (r, .ok (a, none)) := by
  have hd : r.isDup req = true := by simp [Roll.isDup, hl, hs]
  simp [Roll.onRequest, hk, hd, hl]

/-- The dialer wins a collision: while its own request is out, the dialing side refuses the other side's request
(unless it repeats the last one answered) and keeps its request. -/
theorem onRequest_dialer_collision (r : Roll) (req : Msg) (spn : Nat) (fresh : Option Atom) (seed : Atom) (m : Msg)
    (hd : r.dialer = true) (hs : r.st = .req seed m) (hk : req.answer = false) (hn : r.isDup req = false) :
    r.onRequest req spn fresh = (r, .error .unexpected) := by
  simp [Roll.onRequest, hk, hn, hd, hs, Roll.isIdle]

/-- ... and the accepting side drops its own request and answers: it ends Idle, with the answer
(a fresh public value, the switch number) and the Diffie-Hellman value of its fresh atom and the peer's share. -/
theorem onRequest_acceptor_collision (r : Roll) (req : Msg) (spn : Nat) (a b : Atom) (seed : Atom) (m : Msg)
    (hd : r.dialer = false) (hs : r.st = .req seed m) (hk : req.answer = false) (hn : r.isDup req = false)
    (hsh : req.share = .pub b) :
    (r.onRequest req spn (some a)).1.st = .idle ∧
    (r.onRequest req spn (some a)).2 =
      .ok (⟨true, .pub a, spn, .id req.share, .bound (.id req.share) (Dh a b)⟩, some (.bound (.id req.share) (Dh a b))) := by
  simp [Roll.onRequest, hk, hn, hd, hs, Roll.isIdle, hsh, dhOf]


/-- The completed-rolls counter moves by one exactly when a fresh request is answered with a Diffie-Hellman
value (a roll is counted once); every other outcome, a duplicate request and every refusal included, leaves it. -/
theorem onRequest_rolls (r : Roll) (req : Msg) (spn : Nat) (fresh : Option Atom) :
    (r.onRequest req spn fresh).1.rolls =
      (match (r.onRequest req spn fresh).2 with
        | .ok (_, some _) => Record.inc r.rolls
        | _ => r.rolls) := by
  have hr1 : ∀ r : Roll, (if r.isIdle = true then r else { r with st := St.idle }).rolls = r.rolls := by
    intro r; split <;> rfl
  unfold Roll.onRequest
  by_cases a1 : req.answer = true
  · simp [a1]
  · by_cases a2 : r.isDup req = true
    · cases hl : r.last <;> simp [a1, a2, hl]
    · by_cases a3 : (!r.isIdle && r.dialer) = true
      · simp [a1, a2, a3]
      · cases fresh with
        | none => simp [a1, a2, a3, hr1]
        | some a =>
          cases hd : dhOf a req.share with
          | none => simp [a1, a2, a3, hd, hr1]
          | some dh => simp [a1, a2, a3, hd]

/-- A duplicate answer to a duplicate request: when the machine returns no Diffie-Hellman value, it did not change. -/
theorem onRequest_no_dh_unchanged (r : Roll) (req : Msg) (spn : Nat) (fresh : Option Atom) (ans : Msg)
    (h : (r.onRequest req spn fresh).2 = .ok (ans, none)) : (r.onRequest req spn fresh).1 = r := by
  unfold Roll.onRequest at h ⊢
  by_cases a1 : req.answer = true
  · simp [a1] at h
  · by_cases a2 : r.isDup req = true
    · cases hl : r.last <;> simp [a1, a2, hl]
    · by_cases a3 : (!r.isIdle && r.dialer) = true
      · simp [a1, a2, a3] at h
      · cases fresh with
        | none => simp [a1, a2, a3] at h
        | some a =>
          cases hd : dhOf a req.share with
          | none => simp [a1, a2, a3, hd] at h
          | some dh => simp [a1, a2, a3, hd] at h

/-- Taking an answer to the request that is out: the machine is Idle (the request share is spent: it served this one
roll), the counter moves by one, and the value is the Diffie-Hellman value of the seed and the answer's share with
the request identifier bound in. -/
theorem onAnswer_ok (r : Roll) (a : Msg) (seed : Atom) (m : Msg) (b : Atom) (ha : a.answer = true)
    (hs : r.st = .req seed m) (hsh : a.share = .pub b) (he : a.to = .id m.share) :
    r.onAnswer a =
      ({ r with st := .idle, last := none, rolls := Record.inc r.rolls }, .ok (.bound (.id m.share) (Dh seed b), a.spn)) := by
  simp [Roll.onAnswer, ha, hs, hsh, dhOf, he]

/-- An answer that echoes another request than the one out is ignored and changes nothing (a stale answer of an
earlier roll, an answer to a request that is gone). -/
theorem onAnswer_other_request (r : Roll) (a : Msg) (seed : Atom) (m : Msg) (ha : a.answer = true)
    (hs : r.st = .req seed m) (he : a.to ≠ .id m.share) : r.onAnswer a = (r, .error .unexpected) := by
  simp [Roll.onAnswer, ha, hs, he]

/-- A stale or repeated answer (no request out) is refused and changes nothing. -/
theorem onAnswer_stale (r : Roll) (a : Msg) (hs : r.st = .idle) : r.onAnswer a = (r, .error .unexpected) := by
  unfold Roll.onAnswer
  by_cases h : a.answer = true <;> simp [h, hs]

/-- A repeated answer never gives a second key: after a successful answer the machine is Idle, so the same answer
is refused. -/
theorem onAnswer_once (r : Roll) (a : Msg) (c : T × Nat) (hok : (r.onAnswer a).2 = .ok c) :
    (r.onAnswer a).1.st = .idle ∧ ((r.onAnswer a).1.onAnswer a).2 = .error .unexpected := by
  unfold Roll.onAnswer at hok ⊢
  by_cases h : a.answer = true
  · cases hs : r.st with
    | idle => simp [h, hs] at hok
    | req seed m =>
      by_cases he : a.to = .id m.share
      · cases hd : dhOf seed a.share with
        | none => simp [h, hs, hd, he] at hok
        | some dh => simp [h, hs, hd, he]
      · simp [h, hs, he] at hok
  · simp [h] at hok

/-- Agreement: when the requester completes with the answer to its request, both sides computed the same
Diffie-Hellman value (the unordered pair of the two atoms), and the requester learned the switch number the answerer
announced. -/
theorem agreement (A B : Roll) (ra rb : Atom) (spn : Nat) (hnd : B.isDup (Msg.req (.pub ra)) = false)
    (hB : B.dialer = false ∨ B.isIdle = true) :
    ∃ B' ans dhB dhA,
      B.onRequest (Msg.req (.pub ra)) spn (some rb) = (B', .ok (ans, some dhB)) ∧
      (({ A with st := .req ra (Msg.req (.pub ra)) } : Roll).onAnswer ans).2 = .ok (dhA, spn) ∧ dhA = dhB := by
  have hc : (!B.isIdle && B.dialer) = false := by
    rcases hB with h | h <;> simp [h]
  refine ⟨(B.onRequest (Msg.req (.pub ra)) spn (some rb)).1,
    ⟨true, .pub rb, spn, .id (.pub ra), .bound (.id (.pub ra)) (Dh rb ra)⟩, .bound (.id (.pub ra)) (Dh rb ra),
    .bound (.id (.pub ra)) (Dh ra rb), ?_, ?_, by rw [Dh_comm]⟩
  · have hnd' : B.isDup ⟨false, .pub ra, 0, .junk, .junk⟩ = false := hnd
    simp [Roll.onRequest, Msg.req, hnd', hc, dhOf]
  · simp [Roll.onAnswer, Msg.req, dhOf]

/-! ## Post-compromise security (symbolic) -/

/-- What a passive attacker that owns the atoms of node `att` and the base secrets `leaked` can compute. -/
def Known (att : Nat) (leaked : Nat → Prop) : T → Prop
  | .pub _ => True
  | .dh a b => a.n = att ∨ b.n = att
  | .base d => leaked d
  | .roll s d => Known att leaked s ∧ Known att leaked d
  | .key s => Known att leaked s
  | .junk => False
  | .id s => Known att leaked s
  | .bound i d => Known att leaked i ∧ Known att leaked d

theorem known_roll (att : Nat) (leaked : Nat → Prop) (s d : T) :
    Known att leaked (.roll s d) ↔ Known att leaked s ∧ Known att leaked d := Iff.rfl

theorem known_key (att : Nat) (leaked : Nat → Prop) (s : T) : Known att leaked (.key s) ↔ Known att leaked s := Iff.rfl

/-- A Diffie-Hellman value is known only if the attacker owns one of the two secret atoms. -/
theorem known_dh (att : Nat) (leaked : Nat → Prop) (a b : Atom) : Known att leaked (Dh a b) ↔ a.n = att ∨ b.n = att := by
  unfold Dh
  split
  · exact Iff.rfl
  · simp only [Known]; exact or_comm

/-- CN8: an attacker that learned the old secret `s` does not know the key after a roll whose Diffie-Hellman atoms
it does not own, whatever request identifier is bound into the value. -/
theorem post_compromise (att : Nat) (leaked : Nat → Prop) (s i : T) (hs : Known att leaked s) (a b : Atom)
    (ha : a.n ≠ att) (hb : b.n ≠ att) :
    ¬ Known att leaked (.roll s (.bound i (Dh a b))) ∧ ¬ Known att leaked (.key (.roll s (.bound i (Dh a b)))) := by
  have hn : ¬ Known att leaked (Dh a b) := by rw [known_dh]; omega
  exact ⟨fun h => hn h.2.2, fun h => hn h.2.2⟩

/-- The secret after a list of rolls. -/
def rollAll (s : T) : List T → T
  | [] => s
  | d :: ds => rollAll (.roll s d) ds

theorem known_rollAll (att : Nat) (leaked : Nat → Prop) (s : T) (ds : List T) :
    Known att leaked (rollAll s ds) ↔ Known att leaked s ∧ ∀ d ∈ ds, Known att leaked d := by
  induction ds generalizing s with
  | nil => simp [rollAll]
  | cons d ds ih =>
    simp only [rollAll, ih, Known, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- One unknown Diffie-Hellman value protects every later generation, however the other rolls went. -/
theorem post_compromise_chain (att : Nat) (leaked : Nat → Prop) (s : T) (ds : List T) (d : T) (hd : d ∈ ds)
    (hu : ¬ Known att leaked d) : ¬ Known att leaked (rollAll s ds) := by
  rw [known_rollAll]; exact fun h => hu (h.2 d hd)

/-- Rolls of one secret with different Diffie-Hellman values are different secrets, and different keys. -/
theorem roll_injective (s s' d d' : T) : T.roll s d = T.roll s' d' ↔ s = s' ∧ d = d' := by
  constructor
  · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem roll_keys_distinct (s d d' : T) (h : d ≠ d') : T.key (.roll s d) ≠ T.key (.roll s d') := by
  intro c; injection c with c; injection c with _ c2; exact h c2

/-- There is no hash-only successor: no function of the old secret alone gives the rolled secret for every
Diffie-Hellman value. -/
theorem roll_not_a_function_of_the_secret (s : T) (f : T → T) : ¬ ∀ d, T.roll s d = f s := by
  intro h
  have h1 := h .junk
  have h2 := h (.base 0)
  rw [← h2] at h1
  injection h1 with _ c; cases c

/-! ## The roll trigger -/

/-- `MAX_KEY_AGE_NS`: 10 minutes. -/
def maxAgeNs : Nat := 600 * 1000000000

/-- `PacketKey::limit_reached`. -/
def limitReached (k : Record.Key) : Bool :=
  match k.aead with
  | .aes => decide (k.sealed ≥ k.limits.aesGcmPackets)
  | .chacha => decide (k.failed ≥ k.limits.chachaFailures)

/-- `keyroll::due`. -/
def due (send recv : Record.Key) (ageNs after : Nat) : Bool :=
  limitReached send || limitReached recv || decide (send.sealed ≥ after) || decide (ageNs ≥ maxAgeNs)

/-- A roll is due iff a limit is reached, or the sending key sealed `after` packets, or the keys are 10 minutes old. -/
theorem due_iff (send recv : Record.Key) (ageNs after : Nat) :
    due send recv ageNs after = true ↔
      (limitReached send = true ∨ limitReached recv = true ∨ send.sealed ≥ after ∨ ageNs ≥ 600000000000) := by
  simp [due, maxAgeNs, or_assoc]

theorem limitReached_aes (k : Record.Key) (h : k.aead = .aes) : limitReached k = true ↔ k.sealed ≥ k.limits.aesGcmPackets := by
  simp [limitReached, h]

theorem limitReached_chacha (k : Record.Key) (h : k.aead = .chacha) :
    limitReached k = true ↔ k.failed ≥ k.limits.chachaFailures := by
  simp [limitReached, h]

/-- The limit is exactly what makes the key refuse: an AES key at its limit refuses to seal, a ChaCha20-Poly1305 key
at its limit refuses to open (`KeyRollRequired`), and below it they work. -/
theorem limit_reached_refuses (k : Record.Key) (pn : Nat) (hp : pn ≤ Record.maxPn) (hn : Record.atOrBelow k.last pn = false) :
    (k.aead = .aes → (limitReached k = true ↔ Record.sealK k pn = (k, some .keyRollRequired))) ∧
    (k.aead = .chacha → (limitReached k = true ↔ Record.openFail k pn = (k, some .keyRollRequired))) := by
  constructor
  · intro ha
    rw [limitReached_aes k ha]
    constructor
    · intro hl; exact Record.seal_aes_limit k pn hp hn ha hl
    · intro e
      by_cases hl : k.sealed ≥ k.limits.aesGcmPackets
      · exact hl
      · have : k.sealed < k.limits.aesGcmPackets := by omega
        rw [Record.seal_ok k pn hp hn (fun _ => this)] at e
        simp at e
  · intro ha
    rw [limitReached_chacha k ha]
    constructor
    · intro hl; exact Record.openFail_chacha_limit k pn hp ha hl
    · intro e
      by_cases hl : k.failed ≥ k.limits.chachaFailures
      · exact hl
      · have : k.failed < k.limits.chachaFailures := by omega
        rw [Record.openFail_counts k pn hp (fun _ => this)] at e
        simp at e

/-! ## The receive keys of the transport layer (conn/keys.rs: RecvKeys)

The current key, the previous one with its hold deadline, the staged next one with its floor, the phase bit and the
first number seen in the phase. A packet picks its key by phase bit and number (`select`), and is accepted iff it
opens under that key (`accepts`: the packet's secret is the key's). The first packet that opens under the staged
key promotes it and holds the old key for one probe timeout `pto`. -/

structure RecvKeys where
  cur : T
  phase : Bool
  first : Nat
  prev : Option (T × Nat)
  nxt : Option (T × Nat)

/-- `RecvKeys::expire`: the previous key is dropped once its deadline passed. -/
def RecvKeys.expire (k : RecvKeys) (now : Nat) : RecvKeys :=
  match k.prev with
  | some (_, dl) => if dl ≤ now then { k with prev := none } else k
  | none => k

inductive Sel where
  | cur | next | prev | err
  deriving DecidableEq

/-- `RecvKeys::select` (after `expire`). -/
def RecvKeys.select (k : RecvKeys) (ph : Bool) (pn : Nat) : Sel :=
  if ph == k.phase then .cur
  else match k.nxt with
    | some (_, floor) => if floor ≤ pn then .next else if pn < k.first && k.prev.isSome then .prev else .err
    | none => if pn < k.first && k.prev.isSome then .prev else .err

/-- `RecvKeys::promote`: the staged key becomes current, the old one is held dl `now + pto`. -/
def RecvKeys.promote (k : RecvKeys) (pn now pto : Nat) : RecvKeys :=
  match k.nxt with
  | some (n, _) => { cur := n, phase := !k.phase, first := pn, prev := some (k.cur, now + pto), nxt := none }
  | none => k

/-- Whether a packet sealed under secret `s` with phase bit `ph` and number `pn` is accepted at `now`. -/
def RecvKeys.accepts (k : RecvKeys) (s : T) (ph : Bool) (pn now : Nat) : Bool :=
  let k1 := k.expire now
  match k1.select ph pn with
  | .cur => decide (s = k1.cur)
  | .next => match k1.nxt with | some (n, _) => decide (s = n) | none => false
  | .prev => match k1.prev with | some (p, _) => decide (s = p) | none => false
  | .err => false

/-- The old key is held exactly one probe timeout: after a promotion at `now`, a packet of the old generation (the
phase bit the old key had, a number below the first of the new phase) is accepted before `now + pto` and refused from
it on. -/
theorem old_key_held_one_pto (k : RecvKeys) (old new : T) (floor pn now pto t : Nat)
    (hk : k.cur = old) (hn : k.nxt = some (new, floor)) (hpn : pn < pn0) (t0 : Nat) :
    let k' := k.promote pn0 now pto
    k'.accepts old k.phase pn t = decide (t < now + pto) := by
  intro k'
  have hp : k' = { cur := new, phase := !k.phase, first := pn0, prev := some (old, now + pto), nxt := none } := by
    simp [k', RecvKeys.promote, hn, hk]
  rw [hp]
  by_cases h : t < now + pto
  · have : ¬ (now + pto ≤ t) := by omega
    simp [RecvKeys.accepts, RecvKeys.expire, RecvKeys.select, this, h, hpn]
  · have : now + pto ≤ t := by omega
    simp [RecvKeys.accepts, RecvKeys.expire, RecvKeys.select, this, h]

/-- A forged phase bit (a flipped bit never verifies) costs one failed open and changes nothing: the state after is
the state after `expire`, which any packet would cause. -/
theorem forged_phase_changes_nothing (k : RecvKeys) (now : Nat) : (k.expire now).expire now = k.expire now := by
  unfold RecvKeys.expire
  cases hp : k.prev with
  | none => simp [hp]
  | some p =>
    obtain ⟨s, u⟩ := p
    by_cases h : u ≤ now <;> simp [hp, h]

#audit_axioms Vinc.KeyRoll.decode_encode
#audit_axioms Vinc.KeyRoll.encode_decode
#audit_axioms Vinc.KeyRoll.encode_injective
#audit_axioms Vinc.KeyRoll.decode_unknown_kind
#audit_axioms Vinc.KeyRoll.encode_big_switch
#audit_axioms Vinc.KeyRoll.encode_answer_len
#audit_axioms Vinc.KeyRoll.Dh_comm
#audit_axioms Vinc.KeyRoll.onRequest_dup
#audit_axioms Vinc.KeyRoll.onRequest_dialer_collision
#audit_axioms Vinc.KeyRoll.onRequest_acceptor_collision
#audit_axioms Vinc.KeyRoll.onRequest_rolls
#audit_axioms Vinc.KeyRoll.onRequest_no_dh_unchanged
#audit_axioms Vinc.KeyRoll.onAnswer_ok
#audit_axioms Vinc.KeyRoll.onAnswer_other_request
#audit_axioms Vinc.KeyRoll.onAnswer_stale
#audit_axioms Vinc.KeyRoll.onAnswer_once
#audit_axioms Vinc.KeyRoll.agreement
#audit_axioms Vinc.KeyRoll.known_dh
#audit_axioms Vinc.KeyRoll.post_compromise
#audit_axioms Vinc.KeyRoll.post_compromise_chain
#audit_axioms Vinc.KeyRoll.roll_injective
#audit_axioms Vinc.KeyRoll.roll_not_a_function_of_the_secret
#audit_axioms Vinc.KeyRoll.due_iff
#audit_axioms Vinc.KeyRoll.limit_reached_refuses
#audit_axioms Vinc.KeyRoll.old_key_held_one_pto
#audit_axioms Vinc.KeyRoll.forged_phase_changes_nothing

end Vinc.KeyRoll
