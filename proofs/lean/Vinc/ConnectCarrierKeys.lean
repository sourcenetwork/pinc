import Vinc.Axioms
import Vinc.ConnectCarrierThm

/-!
# The protected carrier: packet numbers, keys and the end

What the model proves about the record sequence of `ProtectedCarrier`, over every reachable carrier (`Reach`: from
`accept` or `dial`, any sequence of reads, transmits, polls with any stream and any handshake outcome, key answers
and seals of any length into any buffer):

- the send key is a `Record.Sys` reachable by `Record.Reach`, so `Record.no_nonce_reuse` holds for it: no
  (key, nonce) pair is used twice (`carrier_no_nonce_reuse`); the packet numbers it sealed are exactly
  `0, 1, ..., send_pn - 1`, in order (`KInv`), so the `k`-th record sealed carries packet number `k` and a seal is
  never refused as `NotIncreasing` (`sealIn_never_not_increasing`);
- a seal that succeeds writes a unit of `2 + n + 16` bytes (the length, the ciphertext, the tag) at packet number
  `send_pn` and raises `send_pn` by one (`sealIn_ok`); a refusal for room, size, stage or encoding changes nothing
  (`sealIn_refused`, `sealFrame_refused`, `sealBytes_refused`), a key at its limit ends the carrier (`sealIn_limit`);
- a whole record of a live open carrier is opened at `recv_pn`: when it authenticates `recv_pn` rises by one and the
  frame is delivered or dropped as its plaintext decodes; when it does not, the carrier ends with `Authentication`
  and `recv_pn` is unchanged (`procRec_ok`, `procRec_auth`); no frame comes before the handshake completed
  (`poll_frame_open`);
- a call that ends the carrier delivers nothing, opens nothing, seals nothing and leaves both packet numbers as they
  were (`ends_change_nothing`), and on an ended carrier every call leaves it ended and delivers, opens and seals
  nothing (`ended_stays`).
-/

namespace Vinc.ConnectCarrier
open Vinc.Record (Key Sys sealK openK)

/-! ## Seals -/

theorem sealIn_ok (k : Konst) (c : C) (n cap : Nat) (h : (sealIn k c n cap).2.1 = .ok) :
    c.st = .open_ ∧ n + k.tag ≤ 65535 ∧ 2 + n + k.tag ≤ cap ∧ ∃ s, c.sk = some s ∧ (sealK s.key c.spn).2 = none ∧
      sealIn k c n cap = ({ c with sk := some (s.seal c.spn), spn := c.spn + 1 }, .ok, 2 + n + k.tag) := by
  unfold sealIn at h ⊢
  by_cases a : c.st ≠ .open_
  · simp [a] at h
  · simp only [a, ite_false] at h ⊢
    have a' : c.st = .open_ := by simpa using a
    by_cases b : 65535 < n + k.tag
    · simp [b] at h
    · simp only [b, ite_false] at h ⊢
      cases hs : c.sk with
      | none => simp [hs] at h
      | some s =>
        simp only [hs] at h ⊢
        by_cases d : cap < 2 + n + k.tag
        · simp [d] at h
        · simp only [d, ite_false] at h ⊢
          cases hk : sealK s.key c.spn with
          | mk k' r =>
            cases r with
            | none => exact ⟨a', by omega, by omega, s, rfl, by rw [hk], by simp⟩
            | some e => simp only [hk] at h; cases e <;> simp at h

theorem sealIn_cases (k : Konst) (c : C) (n cap : Nat) :
    (sealIn k c n cap).2.1 = .ok ∨
    ((sealIn k c n cap).1 = c ∧ (sealIn k c n cap).2.1 ∈ [.err .closed, .err .notOpen, .err .unitSize, .err .noRoom]) ∨
    ((sealIn k c n cap).1 = endC c ∧ (sealIn k c n cap).2.1 ∈ [.err .keyLimit, .err .record] ∧ c.st = .open_) := by
  unfold sealIn
  by_cases a : c.st = .open_
  · have a2 : ¬ c.st ≠ .open_ := by simpa using a
    simp only [a2, ite_false]
    by_cases b : 65535 < n + k.tag
    · right; left; simp [b]
    · simp only [b, ite_false]
      cases hs : c.sk with
      | none => right; left; simp
      | some s =>
        by_cases d : cap < 2 + n + k.tag
        · right; left; simp [d]
        · simp only [d, ite_false]
          cases hk : sealK s.key c.spn with
          | mk k' r =>
            cases r with
            | none => left; rfl
            | some e => right; right; cases e <;> simp [a]
  · right; left
    split
    · refine ⟨rfl, ?_⟩
      by_cases e : c.st = .ended <;> simp [e]
    · contradiction

/-- A refusal of a seal for its stage, its size or its room changes nothing. -/
theorem sealIn_refused (k : Konst) (c : C) (n cap : Nat) (e : Err)
    (h : (sealIn k c n cap).2.1 = .err e) (he : e ∉ [.keyLimit, .record]) : (sealIn k c n cap).1 = c := by
  rcases sealIn_cases k c n cap with h1 | ⟨h1, -⟩ | ⟨-, h2, -⟩
  · rw [h1] at h; cases h
  · exact h1
  · rw [h] at h2; simp at h2 he; rcases h2 with rfl | rfl <;> simp at he

/-- A packet key at its limit, or a packet number past `MAX_PACKET_NUMBER`, ends the carrier. -/
theorem sealIn_limit (k : Konst) (c : C) (n cap : Nat) (e : Err)
    (h : (sealIn k c n cap).2.1 = .err e) (he : e ∈ [.keyLimit, .record]) :
    (sealIn k c n cap).1 = endC c := by
  rcases sealIn_cases k c n cap with h1 | ⟨-, h2⟩ | ⟨h1, -⟩
  · rw [h1] at h; cases h
  · rw [h] at h2; simp at h2 he; rcases he with rfl | rfl <;> simp at h2
  · exact h1

theorem sealFrame_refused (k : Konst) (c : C) (plen cap : Nat) (fe : Fe) (h : fe ≠ .ok ∨ cap < 2) :
    (sealFrame k c plen cap fe).1 = c ∧ (sealFrame k c plen cap fe).2.1 ≠ .ok := by
  unfold sealFrame
  by_cases a : cap < 2 ∨ fe = .wire
  · simp [a]
  · simp only [a, ite_false]
    have : fe = .frame := by
      cases fe <;> simp_all
    simp [this]

theorem sealBytes_refused (k : Konst) (c : C) (plen cap : Nat) (h : plen = 0 ∨ k.maxf < plen ∨ cap < 2 + plen) :
    (sealBytes k c plen cap).1 = c ∧ (sealBytes k c plen cap).2.1 ≠ .ok := by
  unfold sealBytes
  by_cases a : plen = 0 ∨ k.maxf < plen
  · simp [a]
  · simp only [a, ite_false]
    have : cap < 2 + plen := by omega
    simp [this]

/-! ## Reachable carriers -/

/-- Every carrier the public API reaches: a listener or a dialer, then any call with any argument. -/
inductive Reach (k : Konst) : C → Prop where
  | accept : Reach k accept
  | dial (hs : Hs) : Reach k (dial k hs).1
  | recv {c : C} (n : Nat) : Reach k c → Reach k (receive k c n).2
  | tx {c : C} (n : Nat) : Reach k c → Reach k (transmit c n).2
  | poll {c : C} (S : Strm) (hs : Hs) : Reach k c → Reach k (poll k S c hs).1
  | ans {c : C} (hs : Hs) : Reach k c → Reach k (answerSoft k c hs).1
  | kresp {c : C} (hs : Hs) : Reach k c → Reach k (keyResponse k c hs).1
  | sealF {c : C} (plen cap : Nat) (fe : Fe) : Reach k c → Reach k (sealFrame k c plen cap fe).1
  | sealB {c : C} (plen cap : Nat) : Reach k c → Reach k (sealBytes k c plen cap).1

/-- The last packet number sealed after `n` seals. -/
def lastOf : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

/-- The invariant of the packet numbers and keys. -/
structure KInv (k : Konst) (c : C) : Prop where
  hs : c.st = .hs → c.spn = 0 ∧ c.sk = none
  sk : ∀ s, c.sk = some s →
    (∃ b, Record.Reach k.aead k.lim b s) ∧ s.log.map Prod.snd = List.range c.spn ∧ s.key.last = lastOf c.spn

theorem kinv_endC (k : Konst) (c : C) : KInv k (endC c) :=
  ⟨fun h => by simp [endC] at h, fun s h => by simp [endC] at h⟩

/-- The fields a handshake step leaves: the send packet number, and the send key unless it establishes. -/
theorem finish_cases (k : Konst) (c : C) (r : DRes) (hs : Hs) :
    (finish k c r hs).1.spn = c.spn ∧
    ((finish k c r hs).1 = endC c ∨
     ((finish k c r hs).1.st = c.st ∧ (finish k c r hs).1.sk = c.sk) ∨
     ((finish k c r hs).1.st = .open_ ∧ (finish k c r hs).1.sk = some ⟨newKey k hs.sb, []⟩ ∧ r = .est)) := by
  unfold finish
  split
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩

theorem kinv_fresh (k : Konst) (c : C) (b : Nat) (h0 : c.spn = 0) (hsk : c.sk = some ⟨newKey k b, []⟩) :
    ∀ s, c.sk = some s →
      (∃ b, Record.Reach k.aead k.lim b s) ∧ s.log.map Prod.snd = List.range c.spn ∧ s.key.last = lastOf c.spn := by
  intro s hs
  rw [hsk] at hs; cases hs
  exact ⟨⟨b, Record.Reach.init⟩, by simp [h0], by simp [h0, lastOf, newKey, Key.fresh]⟩

/-- A step that keeps the send key, the send packet number and does not go back to the handshake keeps the
invariant. -/
theorem kinv_keep (k : Konst) (c c' : C) (hi : KInv k c) (hsk : c'.sk = c.sk) (hspn : c'.spn = c.spn)
    (hst : c'.st = .hs → c.st = .hs) : KInv k c' :=
  ⟨fun h => by rw [hsk, hspn]; exact hi.hs (hst h), fun s h => by rw [hspn]; rw [hsk] at h; exact hi.sk s h⟩

theorem kinv_finish (k : Konst) (c : C) (r : DRes) (hs : Hs) (hi : KInv k c) (hc : c.st = .hs) :
    KInv k (finish k c r hs).1 := by
  obtain ⟨h1, h2 | ⟨h2, h3⟩ | ⟨h2, h3, -⟩⟩ := finish_cases k c r hs
  · rw [h2]; exact kinv_endC k c
  · exact kinv_keep k c _ hi h3 h1 (fun _ => hc)
  · have h0 : (finish k c r hs).1.spn = 0 := by rw [h1]; exact (hi.hs hc).1
    exact ⟨fun h => (by rw [h2] at h; cases h), kinv_fresh k _ hs.sb h0 h3⟩

theorem release_kinv (k : Konst) (c : C) (hi : KInv k c) : KInv k (release c) := by
  obtain ⟨-, -, -, h4, -, h6, -, h8, -⟩ := release_fields c
  exact kinv_keep k c _ hi h8 h6 (fun h => by rw [h4] at h; exact h)

theorem kinv_setW (k : Konst) (c : C) (W : Nat) (hi : KInv k c) : KInv k (setW c W) :=
  kinv_keep k c _ hi rfl rfl (fun h => h)

theorem kinv_proc (k : Konst) (S : Strm) (c : C) (len : Nat) (hs : Hs) (hi : KInv k c) (hne : c.st ≠ .ended) :
    KInv k (proc k S c len hs).1 := by
  unfold proc
  cases hc : c.st with
  | ended => exact absurd hc hne
  | open_ =>
    dsimp only
    unfold procRec
    split
    · exact kinv_endC k _
    · split
      · exact kinv_endC k _
      · split
        · exact kinv_endC k _
        · exact kinv_endC k _
        · exact kinv_endC k _
        · exact kinv_keep k c _ hi rfl rfl (fun h => h)
  | hs =>
    dsimp only
    unfold procHs
    exact kinv_finish k _ _ hs (kinv_keep k c _ hi rfl rfl (fun h => h)) hc

theorem kinv_poll (k : Konst) (S : Strm) (c : C) (hs : Hs) (hi : KInv k c) : KInv k (poll k S c hs).1 := by
  have hr := release_kinv k c hi
  have hst := (release_fields c).2.2.2.1
  by_cases he : c.st = .ended
  · rw [poll_ended k S c hs he]; exact hr
  · rw [poll_eq k S c hs he]
    split
    · exact hr
    · split
      · exact kinv_endC k _
      · split
        · exact kinv_proc k S _ _ hs hr (by rw [hst]; exact he)
        · exact hr

theorem kinv_keyResponse (k : Konst) (c : C) (hs : Hs) (hi : KInv k c) : KInv k (keyResponse k c hs).1 := by
  unfold keyResponse
  split
  · exact kinv_endC k c
  · rename_i a
    have a' : c.st = .hs := by simpa using a
    exact kinv_finish k _ _ hs (kinv_keep k _ _ hi rfl rfl (fun h => h)) a'

theorem kinv_answerSoft (k : Konst) (c : C) (hs : Hs) (hi : KInv k c) : KInv k (answerSoft k c hs).1 := by
  unfold answerSoft
  split
  · exact kinv_endC k c
  · exact kinv_keyResponse k c hs hi

theorem kinv_sealIn (k : Konst) (c : C) (n cap : Nat) (hi : KInv k c) : KInv k (sealIn k c n cap).1 := by
  rcases sealIn_cases k c n cap with h | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨hst, -, -, s, hs, hok, he⟩ := sealIn_ok k c n cap h
    rw [he]
    obtain ⟨⟨b, hb⟩, hl, hlast⟩ := hi.sk s hs
    obtain ⟨-, -, -, hk⟩ := Record.seal_ok_cases s.key c.spn hok
    refine ⟨fun h' => by simp [hst] at h', fun s' hs' => ?_⟩
    simp only [Option.some.injEq] at hs'
    subst hs'
    refine ⟨⟨b, Record.Reach.sealStep c.spn hb⟩, ?_, ?_⟩
    · simp only [Sys.seal]
      cases hk' : sealK s.key c.spn with
      | mk k'' r =>
        rw [hk'] at hok; simp at hok; subst hok
        simp [hl, List.range_succ]
    · simp only [Sys.seal]
      cases hk' : sealK s.key c.spn with
      | mk k'' r =>
        rw [hk'] at hok hk; simp at hok; subst hok
        simp only at hk; rw [hk]; simp [lastOf]
  · rw [h]; exact hi
  · rw [h]; exact kinv_endC k c

theorem kinv_sealFrame (k : Konst) (c : C) (plen cap : Nat) (fe : Fe) (hi : KInv k c) :
    KInv k (sealFrame k c plen cap fe).1 := by
  unfold sealFrame
  split
  · exact hi
  · split
    · exact hi
    · exact kinv_sealIn k c plen cap hi

theorem kinv_sealBytes (k : Konst) (c : C) (plen cap : Nat) (hi : KInv k c) :
    KInv k (sealBytes k c plen cap).1 := by
  unfold sealBytes
  split
  · exact hi
  · split
    · exact hi
    · exact kinv_sealIn k c plen cap hi

theorem kinv_dial (k : Konst) (hs : Hs) : KInv k (dial k hs).1 := by
  unfold dial
  cases hsRun k 0 hs with
  | mk out r => cases r <;> exact ⟨fun _ => ⟨rfl, rfl⟩, fun s h => by simp at h⟩

theorem reach_kinv {k : Konst} {c : C} (h : Reach k c) : KInv k c := by
  induction h with
  | accept => exact ⟨fun _ => ⟨rfl, rfl⟩, fun s h => by simp [accept] at h⟩
  | dial hs => exact kinv_dial k hs
  | recv n _ ih =>
    rw [(receive_spec k _ n).2]; exact kinv_setW k _ _ (release_kinv k _ ih)
  | tx n _ ih => exact kinv_keep k _ _ ih rfl rfl (fun h => h)
  | poll S hs _ ih => exact kinv_poll k S _ hs ih
  | ans hs _ ih => exact kinv_answerSoft k _ hs ih
  | kresp hs _ ih => exact kinv_keyResponse k _ hs ih
  | sealF plen cap fe _ ih => exact kinv_sealFrame k _ plen cap fe ih
  | sealB plen cap _ ih => exact kinv_sealBytes k _ plen cap ih

/-- UNCONDITIONAL in the carrier: over every reachable carrier, no (key, nonce) pair is used by two seals. This is
`Record.no_nonce_reuse` applied to the carrier's send key, under its hypotheses on the primitives (the packet key is
an injective function of the secret, the IV has 12 bytes). -/
theorem carrier_no_nonce_reuse {K : Type} (keyOf : Record.Sec → K) (iv : Record.Sec → List Nat)
    (hk : ∀ s t, keyOf s = keyOf t → s = t) (hiv : ∀ s, (iv s).length = 12) {k : Konst} {c : C} (h : Reach k c)
    (s : Sys) (hs : c.sk = some s) :
    (s.log.map fun e => (keyOf e.1, Record.nonce (iv e.1) e.2)).Nodup := by
  obtain ⟨⟨b, hb⟩, -, -⟩ := (reach_kinv h).sk s hs
  exact Record.no_nonce_reuse keyOf iv hk hiv hb

/-- The `i`-th record sealed carries packet number `i`: the packet numbers of the send key's seals are
`0, 1, ..., send_pn - 1`. -/
theorem carrier_pns {k : Konst} {c : C} (h : Reach k c) (s : Sys) (hs : c.sk = some s) :
    s.log.map Prod.snd = List.range c.spn :=
  ((reach_kinv h).sk s hs).2.1

/-- A seal of a reachable carrier is never refused as `NotIncreasing`: it always offers `send_pn`, above every number
sealed before. -/
theorem sealIn_never_not_increasing {k : Konst} {c : C} (h : Reach k c) (s : Sys) (hs : c.sk = some s) :
    (sealK s.key c.spn).2 ≠ some .notIncreasing := by
  have hl := ((reach_kinv h).sk s hs).2.2
  unfold sealK
  have : Record.atOrBelow s.key.last c.spn = false := by
    rw [hl]; cases hc : c.spn with
    | zero => rfl
    | succ n => simp [lastOf, Record.atOrBelow]
  rw [this]
  by_cases a1 : c.spn > Record.maxPn
  · simp [a1]
  · simp only [a1, ite_false, Bool.false_eq_true]
    split <;> simp

/-! ## Records -/

/-- A whole record that authenticates at `recv_pn` (below the key's limits) raises `recv_pn` by one, is consumed, and
is delivered as a frame when its plaintext decodes, dropped with `Frame` otherwise; the carrier lives on. -/
theorem procRec_ok (k : Konst) (S : Strm) (c : C) (len : Nat) (key : Key) (hlen : k.tag < len) (hk : c.rk = some key)
    (hok : (openK key c.rpn (S.opens c.rd c.rpn)).2 = none) :
    (procRec k S c len).1 = { c with rk := some (openK key c.rpn (S.opens c.rd c.rpn)).1, rpn := c.rpn + 1,
                                     cons := 2 + len } ∧
    (procRec k S c len).2 = (if S.fok c.rd then .frame else .err .frame) := by
  unfold procRec
  have : ¬ len ≤ k.tag := by omega
  simp only [this, ite_false, hk]
  cases ho : openK key c.rpn (S.opens c.rd c.rpn) with
  | mk k' r => rw [ho] at hok; simp at hok; subst hok; exact ⟨rfl, rfl⟩

/-- A whole record that does not authenticate ends the carrier with `Authentication`; `recv_pn` is unchanged and
nothing is delivered. -/
theorem procRec_auth (k : Konst) (S : Strm) (c : C) (len : Nat) (key : Key) (hlen : k.tag < len)
    (hk : c.rk = some key) (hpn : c.rpn ≤ Record.maxPn)
    (hlim : ¬ (key.aead = .chacha ∧ key.failed ≥ key.limits.chachaFailures)) (hbad : S.opens c.rd c.rpn = false) :
    procRec k S c len = (endC c, .err .authentication) := by
  unfold procRec
  have : ¬ len ≤ k.tag := by omega
  simp only [this, ite_false, hk]
  have ho : openK key c.rpn false = ({ key with failed := Record.inc key.failed }, some .authentication) := by
    have : ¬ c.rpn > Record.maxPn := by omega
    simp [Record.openK, this, hlim]
  rw [hbad, ho]

/-- The drain of the handshake outputs fails only with `UnitSize`, `OutputFull` or `Handshake`. -/
theorem driveR_err (k : Konst) : ∀ (outs : List Out) (out : Nat) (r : DRes),
    (∀ e, r = .err e → e = .unitSize ∨ e = .outputFull ∨ e = .handshake) →
    ∀ e, (driveR k out outs r).2 = .err e → e = .unitSize ∨ e = .outputFull ∨ e = .handshake
  | [], out, r, h => by simpa [driveR] using h
  | .send m :: t, out, r, h => by
    unfold driveR
    split
    · exact driveR_err k t _ _ (by intro e he; cases he; simp)
    · split
      · exact driveR_err k t _ _ (by intro e he; cases he; simp)
      · exact driveR_err k t _ _ h
  | .est kok :: t, out, r, h => by
    unfold driveR
    apply driveR_err k t
    cases r with
    | err e' => exact h
    | ok => intro e he; cases kok <;> simp at he
    | est => intro e he; cases kok <;> simp at he
    | estbad => intro e he; cases kok <;> simp at he
  | .fail :: t, out, r, _ => by
    unfold driveR
    exact driveR_err k t _ _ (by intro e he; cases he; simp)

theorem hsRun_err (k : Konst) (out : Nat) (hs : Hs) (e : Err) (h : (hsRun k out hs).2 = .err e) :
    e = .unitSize ∨ e = .outputFull ∨ e = .handshake := by
  unfold hsRun at h
  split at h
  · cases h; simp
  · exact driveR_err k hs.outs out .ok (by intro e he; cases he) e h

theorem finish_frame (k : Konst) (c : C) (r : DRes) (hs : Hs)
    (h : (finish k c r hs).2 = .frame ∨ (finish k c r hs).2 = .err .frame) : r = .err .frame := by
  cases r with
  | err e => simp [finish] at h; rw [h]
  | ok => unfold finish at h; by_cases hk : hs.kreq <;> simp [hk] at h
  | est => simp [finish] at h
  | estbad => simp [finish] at h

/-- A handshake step never answers a frame. -/
theorem procHs_not_frame (k : Konst) (c : C) (len : Nat) (hs : Hs) :
    ¬ ((procHs k c len hs).2 = .frame ∨ (procHs k c len hs).2 = .err .frame) := by
  intro h
  have := finish_frame k _ _ hs h
  rcases hsRun_err k c.out hs .frame this with h | h | h <;> cases h

/-- No frame is delivered (nor dropped) before the handshake completed: a frame comes only from an open carrier. -/
theorem poll_frame_open (k : Konst) (S : Strm) (c : C) (hs : Hs)
    (h : (poll k S c hs).2 = .frame ∨ (poll k S c hs).2 = .err .frame) : c.st = .open_ := by
  by_cases he : c.st = .ended
  · rw [poll_ended k S c hs he] at h; simp at h
  · rw [poll_eq k S c hs he] at h
    have hst := (release_fields c).2.2.2.1
    revert h
    split
    · simp
    · split
      · simp
      · split
        · unfold proc
          rw [hst]
          cases hc : c.st with
          | open_ => intro; rfl
          | hs => intro h; exfalso; have := procHs_not_frame k (release c) (S.hdr (pos c)) hs; simp_all
          | ended => exact absurd hc he
        · simp

/-! ## The end -/

/-- What a call answers that hands something over: a frame, an open carrier, a sealed unit. -/
def Delivers : Res → Prop
  | .frame | .err .frame | .opened | .ok => True
  | _ => False

theorem endC_fields (c : C) : (endC c).st = .ended ∧ (endC c).rpn = c.rpn ∧ (endC c).spn = c.spn ∧
    (endC c).sk = none ∧ (endC c).rk = none := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A handshake step of a live carrier either ends it with an error (the machine's, or `Handshake`) or leaves it
live. -/
theorem finish_shape (k : Konst) (c : C) (r : DRes) (hs : Hs) (hc : c.st ≠ .ended) :
    (∃ e, finish k c r hs = (endC c, .err e) ∧ (r = .err e ∨ e = .handshake)) ∨ (finish k c r hs).1.st ≠ .ended := by
  cases r with
  | err e => exact Or.inl ⟨e, rfl, Or.inl rfl⟩
  | ok => exact Or.inr hc
  | est => right; simp [finish]
  | estbad => exact Or.inl ⟨.handshake, rfl, Or.inr rfl⟩

/-- A call that ends a live carrier delivers nothing, opens nothing, seals nothing, forgets both keys and leaves
both packet numbers as they were. -/
theorem ends_change_nothing (k : Konst) (S : Strm) (c : C) (hs : Hs) (hne : c.st ≠ .ended) :
    ((poll k S c hs).1.st = .ended →
      ¬ Delivers (poll k S c hs).2 ∧ (poll k S c hs).1.rpn = c.rpn ∧ (poll k S c hs).1.spn = c.spn ∧
      (poll k S c hs).1.sk = none ∧ (poll k S c hs).1.rk = none) ∧
    ((answerSoft k c hs).1.st = .ended →
      ¬ Delivers (answerSoft k c hs).2 ∧ (answerSoft k c hs).1.rpn = c.rpn ∧ (answerSoft k c hs).1.spn = c.spn ∧
      (answerSoft k c hs).1.sk = none) ∧
    (∀ n cap, (sealIn k c n cap).1.st = .ended →
      (sealIn k c n cap).2.1 ≠ .ok ∧ (sealIn k c n cap).1.rpn = c.rpn ∧ (sealIn k c n cap).1.spn = c.spn ∧
      (sealIn k c n cap).1.sk = none) := by
  have hr := release_fields c
  refine ⟨fun h => ?_, fun h => ?_, fun n cap h => ?_⟩
  · rw [poll_eq k S c hs hne] at h ⊢
    revert h
    split
    · intro h; rw [hr.2.2.2.1] at h; exact absurd h hne
    · split
      · intro _; simp [Delivers, endC, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]
      · split
        · unfold proc
          split
          · unfold procRec
            split
            · intro _; simp [Delivers, endC, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]
            · split
              · intro _; simp [Delivers, endC, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]
              · split
                · intro _; simp [Delivers, endC, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]
                · intro _; simp [Delivers, endC, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]
                · intro _; simp [Delivers, endC, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]
                · intro h; simp at h; rw [hr.2.2.2.1] at h; exact absurd h hne
          · unfold procHs
            have hc' : ({ release c with cons := 2 + S.hdr (pos c), out := (hsRun k (release c).out hs).1 } : C).st
                ≠ .ended := by show (release c).st ≠ .ended; rw [hr.2.2.2.1]; exact hne
            rcases finish_shape k _ (hsRun k (release c).out hs).2 hs hc' with ⟨e, he, hre⟩ | hn
            · rw [he]; intro _
              refine ⟨fun hd => ?_, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.1, rfl, rfl⟩
              have : e ≠ .frame := by
                rcases hre with hre | rfl
                · intro hf; subst hf
                  rcases hsRun_err k _ hs .frame hre with h | h | h <;> cases h
                · intro hf; cases hf
              cases e <;> simp_all [Delivers]
            · intro h; exact absurd h hn
        · intro h; rw [hr.2.2.2.1] at h; exact absurd h hne
  · unfold answerSoft keyResponse at h ⊢
    revert h
    split
    · intro _; simp [Delivers, endC]
    · split
      · intro _; simp [Delivers, endC]
      · have hc' : ({ c with out := (hsRun k c.out hs).1 } : C).st ≠ .ended := hne
        rcases finish_shape k _ (hsRun k c.out hs).2 hs hc' with ⟨e, he, hre⟩ | hn
        · rw [he]; intro _
          refine ⟨fun hd => ?_, rfl, rfl, rfl⟩
          have : e ≠ .frame := by
            rcases hre with hre | rfl
            · intro hf; subst hf
              rcases hsRun_err k _ hs .frame hre with h | h | h <;> cases h
            · intro hf; cases hf
          cases e <;> simp_all [Delivers]
        · intro h; exact absurd h hn
  · rcases sealIn_cases k c n cap with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
    · obtain ⟨hst, -⟩ := sealIn_ok k c n cap h1
      obtain ⟨-, -, -, s, -, -, he⟩ := sealIn_ok k c n cap h1
      rw [he] at h; simp [hst] at h
    · rw [h1] at h; exact absurd h hne
    · rcases sealIn_cases k c n cap with h2 | -
      · obtain ⟨-, -, -, s, -, -, he⟩ := sealIn_ok k c n cap h2
        rw [he] at h1; simp [endC] at h1
      · rw [h1]; refine ⟨fun h3 => ?_, rfl, rfl, rfl⟩
        rcases sealIn_cases k c n cap with h4 | ⟨-, h5⟩ | ⟨-, h5, -⟩
        · obtain ⟨-, -, -, s, -, -, he⟩ := sealIn_ok k c n cap h4
          rw [he] at h1; simp [endC] at h1
        · rw [h3] at h5; simp at h5
        · rw [h3] at h5; simp at h5

/-- On an ended carrier every call leaves it ended and delivers, opens and seals nothing; a poll answers `Closed`,
and the packet numbers stay. -/
theorem ended_stays (k : Konst) (S : Strm) (c : C) (hs : Hs) (he : c.st = .ended) :
    poll k S c hs = (release c, .err .closed) ∧
    (answerSoft k c hs).1.st = .ended ∧ ¬ Delivers (answerSoft k c hs).2 ∧
    (keyResponse k c hs).1.st = .ended ∧ (keyResponse k c hs).2 = .err .closed ∧
    (∀ n cap, sealIn k c n cap = (c, .err .closed, 0)) ∧
    (∀ plen cap fe, (sealFrame k c plen cap fe).1 = c ∧ (sealFrame k c plen cap fe).2.1 ≠ .ok) ∧
    (∀ plen cap, (sealBytes k c plen cap).1 = c ∧ (sealBytes k c plen cap).2.1 ≠ .ok) ∧
    (∀ n, (receive k c n).2.st = .ended ∧ (receive k c n).2.rpn = c.rpn ∧ (receive k c n).2.spn = c.spn) := by
  have hsi : ∀ n cap, sealIn k c n cap = (c, .err .closed, 0) := by
    intro n cap; unfold sealIn; simp [he]
  refine ⟨poll_ended k S c hs he, ?_, ?_, ?_, ?_, hsi, fun plen cap fe => ?_, fun plen cap => ?_, fun n => ?_⟩
  · unfold answerSoft; simp [he, endC]
  · unfold answerSoft; simp [he, Delivers]
  · unfold keyResponse; simp [he, endC]
  · unfold keyResponse; simp [he]
  · unfold sealFrame
    split
    · simp
    · split
      · simp
      · rw [hsi]; simp
  · unfold sealBytes
    split
    · simp
    · split
      · simp
      · rw [hsi]; simp
  · rw [(receive_spec k c n).2]
    obtain ⟨-, -, -, h4, -, h6, h7, -⟩ := release_fields c
    exact ⟨by rw [setW_st, h4, he], h7, h6⟩

#audit_axioms Vinc.ConnectCarrier.carrier_no_nonce_reuse
#audit_axioms Vinc.ConnectCarrier.carrier_pns
#audit_axioms Vinc.ConnectCarrier.sealIn_never_not_increasing
#audit_axioms Vinc.ConnectCarrier.sealIn_ok
#audit_axioms Vinc.ConnectCarrier.sealIn_refused
#audit_axioms Vinc.ConnectCarrier.procRec_ok
#audit_axioms Vinc.ConnectCarrier.procRec_auth
#audit_axioms Vinc.ConnectCarrier.poll_frame_open
#audit_axioms Vinc.ConnectCarrier.ends_change_nothing
#audit_axioms Vinc.ConnectCarrier.ended_stays

end Vinc.ConnectCarrier
