import Pinc.Axioms
import Pinc.DtnCodec
import Pinc.DtnCodecWire

/-!
# The saved state of the endpoint (`pinc-core` `state.rs`)

`Endpoint::export_state` writes `version(1) tickets_len(4) tickets krtt_count(2) { alg(1) node(32) rtt(8) }
ekk_count(2) { alg(1) node(32) prekey_hash(32) }`, the tickets being `ClientTickets::export`: `version(1) count(1)`
and per ticket `alg(1) node(32) alpn_len(1) alpn tid(16) psk(32) aead(1) expiry(8) credit(6)`. `restore_state` reads
the header (`Hdr`), checks every round trip and prekey entry, lets `ClientTickets::restore` check and then store its
slice, and stores the round trips and the prekey peers.

This file is the model: the byte format as a `Codec` of `Pinc.DtnCodec` (the two laws, parse after emit and emit
after parse, for every byte string and unbounded counts), the tables a restore writes, and the staged restore
against a live state. `CoreStateThm.lean` proves the properties: round trip, one encoding, refusal without effect,
the bounds, and what a fresh endpoint holds after a restore. As in the code, a restore never reads further than the
bytes it is given (`bytesC` checks the length before it takes anything) and a count is checked against the input
before any entry is read.

Bytes are `Fin 256`; the u64 fields (expiry, round trip) are naturals of 8 bytes, so a mutated high byte is a large
number, not an overflow.
-/

namespace Pinc.CoreState
open Pinc.DtnCodec Pinc.DtnCodecWire

/-! ## The list combinator: `n` entries in a row -/

def listEmit {α : Type} (c : Codec α) : List α → Bytes
  | [] => []
  | a :: l => c.emit a ++ listEmit c l

def listParse {α : Type} (c : Codec α) : Nat → Bytes → Option (List α × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match c.parse bs with
    | none => none
    | some (a, r) =>
      match listParse c n r with
      | none => none
      | some (l, r') => some (a :: l, r')

def listWf {α : Type} (c : Codec α) (n : Nat) (l : List α) : Prop := l.length = n ∧ ∀ a ∈ l, c.wf a

theorem list_rt {α : Type} (c : Codec α) : ∀ (l : List α) (n : Nat) (rest : Bytes), listWf c n l →
    listParse c n (listEmit c l ++ rest) = some (l, rest)
  | [], n, rest, h => by
    obtain ⟨h1, _⟩ := h
    simp at h1
    subst h1
    simp [listEmit, listParse]
  | a :: l, n, rest, h => by
    obtain ⟨h1, h2⟩ := h
    simp only [List.length_cons] at h1
    subst h1
    have ha := h2 a (by simp)
    have hl : listWf c l.length l := ⟨rfl, fun x hx => h2 x (by simp [hx])⟩
    simp only [listEmit, List.append_assoc, listParse]
    rw [c.rt a _ ha]
    simp only
    rw [list_rt c l l.length rest hl]

theorem list_inv {α : Type} (c : Codec α) : ∀ (n : Nat) (bs : Bytes) (l : List α) (r : Bytes),
    listParse c n bs = some (l, r) → bs = listEmit c l ++ r ∧ listWf c n l
  | 0, bs, l, r, h => by
    simp only [listParse, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [listEmit, listWf]
  | n + 1, bs, l, r, h => by
    simp only [listParse] at h
    cases hp : c.parse bs with
    | none => simp [hp] at h
    | some x =>
      obtain ⟨a, r1⟩ := x
      simp only [hp] at h
      cases hq : listParse c n r1 with
      | none => simp [hq] at h
      | some y =>
        obtain ⟨l', r2⟩ := y
        simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := c.inv bs a r1 hp
        have h2 := list_inv c n r1 l' r2 hq
        refine ⟨?_, ?_, ?_⟩
        · rw [h1.1, h2.1]; simp [listEmit, List.append_assoc]
        · simp [h2.2.1]
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact h1.2
          · exact h2.2.2 x hx

/-- `n` entries of `c` in a row. -/
def listC {α : Type} (c : Codec α) (n : Nat) : Codec (List α) where
  wf := listWf c n
  emit := listEmit c
  parse := listParse c n
  rt l rest h := list_rt c l n rest h
  inv bs l r h := list_inv c n bs l r h

/-! ## The entries -/

/-- The version byte of a state and of its tickets: 1. -/
def verC : Codec Nat := guardC (uC 1) (fun v => v = 1)

/-- The length of an ALPN: 1 to 32 (`Alpn::new`). -/
def alpnLenC : Codec Nat := guardC (uC 1) (fun l => 1 ≤ l ∧ l ≤ 32)

/-- The AEAD tag: 1 or 2 (`aead_from_tag`). -/
def aeadC : Codec Nat := guardC (uC 1) (fun a => 1 ≤ a ∧ a ≤ 2)

/-- A ticket: node, ALPN length, ALPN, ticket id, pre-shared key, AEAD, expiry, credit record. -/
abbrev TkT := Node × Nat × Bytes × Bytes × Bytes × Nat × Nat × Bytes

def tkC : Codec TkT :=
  pair nodeC (pairD alpnLenC fun l => pair (bytesC l) (pair (bytesC 16) (pair (bytesC 32) (pair aeadC
    (pair (uC 8) (bytesC 6))))))

/-- A round trip: node and nanoseconds. -/
def krC : Codec (Node × Nat) := pair nodeC (uC 8)

/-- A prekey peer: node and the hash of the prekey it caches. -/
def ekC : Codec (Node × Bytes) := pair nodeC (bytesC 32)

def tkExp (t : TkT) : Nat := t.2.2.2.2.2.2.1

/-- The tickets section: version, count, entries (`ClientTickets::export`, and the check of `restore`). -/
def tkSecC : Codec (Nat × Nat × List TkT) :=
  pairD verC fun _ => pairD (uC 1) fun n => listC tkC n

def tkEnc (l : List TkT) : Bytes := tkSecC.emit (1, l.length, l)

def tkDec (b : Bytes) : Option (List TkT) := (decodeAll tkSecC b).map fun x => x.2.2

def krEnc (l : List (Node × Nat)) : Bytes := listEmit krC l
def ekEnc (l : List (Node × Bytes)) : Bytes := listEmit ekC l

def krDec (n : Nat) (b : Bytes) : Option (List (Node × Nat)) := decodeAll (listC krC n) b
def ekDec (n : Nat) (b : Bytes) : Option (List (Node × Bytes)) := decodeAll (listC ekC n) b

/-! ## The header and the state -/

/-- What `restore_state` reads before it looks inside: version, tickets length, tickets, round trip count, round
trips (41 bytes each), prekey count, prekey peers (65 bytes each). -/
abbrev HdT := Nat × Nat × Bytes × Nat × Bytes × Nat × Bytes

def hdrC : Codec HdT :=
  pairD verC fun _ => pairD (uC 4) fun tl => pairD (bytesC tl) fun _ => pairD (uC 2) fun nk =>
    pairD (bytesC (41 * nk)) fun _ => pairD (uC 2) fun ne => bytesC (65 * ne)

def hTk (h : HdT) : Bytes := h.2.2.1
def hNk (h : HdT) : Nat := h.2.2.2.1
def hKr (h : HdT) : Bytes := h.2.2.2.2.1
def hNe (h : HdT) : Nat := h.2.2.2.2.2.1
def hEk (h : HdT) : Bytes := h.2.2.2.2.2.2

/-- The tables: tickets (one per peer, newest last), round trips and prekey peers, each oldest first. -/
structure St where
  tk : List TkT
  kr : List (Node × Nat)
  ek : List (Node × Bytes)

/-- `export_state`: the bytes of a state. -/
def hdrOf (s : St) : HdT :=
  (1, (tkEnc s.tk).length, tkEnc s.tk, s.kr.length, krEnc s.kr, s.ek.length, ekEnc s.ek)

def enc (s : St) : Bytes := hdrC.emit (hdrOf s)

/-- The checks `restore_state` makes of the three slices, in order: the tickets (`ClientTickets::restore`), the
round trips and the prekey peers. -/
def stages (h : HdT) : Option St :=
  match tkDec (hTk h) with
  | none => none
  | some tk =>
    match krDec (hNk h) (hKr h) with
    | none => none
    | some kr =>
      match ekDec (hNe h) (hEk h) with
      | none => none
      | some ek => some ⟨tk, kr, ek⟩

/-- The header, with the check that nothing follows the state; `lax` is the reader without that check. -/
def hdrP (lax : Bool) (b : Bytes) : Option HdT :=
  match hdrC.parse b with
  | none => none
  | some (h, r) => if lax || r.isEmpty then some h else none

/-- The state the bytes hold, or a refusal. -/
def parse (b : Bytes) : Option St :=
  match hdrP false b with
  | none => none
  | some h => stages h

/-- What the encoder accepts: the counts fit their fields and every entry is well-formed. -/
def WFs (s : St) : Prop :=
  s.tk.length < 256 ∧ (∀ t ∈ s.tk, tkC.wf t) ∧ (tkEnc s.tk).length < 2 ^ 32 ∧
  s.kr.length < 2 ^ 16 ∧ (∀ e ∈ s.kr, krC.wf e) ∧ s.ek.length < 2 ^ 16 ∧ (∀ e ∈ s.ek, ekC.wf e)

/-! ## The tables a restore writes -/

/-- Replace the first element that satisfies `p`. -/
def setFirst {α : Type} (p : α → Bool) (v : α) : List α → List α
  | [] => []
  | x :: t => if p x then v :: t else x :: setFirst p v t

/-- `ClientTickets::insert`, as the bytes of an export show it: one ticket per peer, the newest last; the oldest
makes room when the store is full; a store of 0 slots keeps nothing. -/
def tkIns (ct : Nat) (tk : List TkT) (t : TkT) : List TkT :=
  if ct = 0 then tk
  else if tk.any (fun o => o.1 == t.1) then tk.eraseP (fun o => o.1 == t.1) ++ [t]
  else if tk.length = ct then tk.tail ++ [t] else tk ++ [t]

/-- The entries that have not expired by `now` are stored, in order; the count is how many. -/
def apTk (ct now : Nat) : List TkT → List TkT → List TkT × Nat
  | [], tk => (tk, 0)
  | e :: es, tk =>
    if now ≤ tkExp e then
      let r := apTk ct now es (tkIns ct tk e)
      (r.1, r.2 + 1)
    else apTk ct now es tk

/-- The ticket count `restore` reports (`ClientTickets::restore`): the tickets of the state `es` still in the store
`tk` once the whole state was applied. A ticket names its peer and the store holds one per peer, so a ticket of the
store equal to an unexpired ticket of the state is one this restore stored (`==`, the structural equality: the
instance search does not reach `DecidableEq` of the eight-field product). -/
def tkHeld (now : Nat) (es tk : List TkT) : Nat :=
  (tk.filter (fun x => es.any (fun e => decide (now ≤ tkExp e) && e == x))).length

/-- `NodeRtt::restore_peer`: a round trip of 0 is skipped, a known peer is overwritten in place, a new peer is
refused when the table is full. The second component is 1 when the entry was stored. -/
def krIns (cap : Nat) (kr : List (Node × Nat)) (e : Node × Nat) : List (Node × Nat) × Nat :=
  if e.2 = 0 then (kr, 0)
  else if kr.any (fun o => o.1 == e.1) then (setFirst (fun o => o.1 == e.1) e kr, 1)
  else if kr.length < cap then (kr ++ [e], 1) else (kr, 0)

def apKr (cap : Nat) : List (Node × Nat) → List (Node × Nat) → List (Node × Nat) × Nat
  | [], kr => (kr, 0)
  | e :: es, kr =>
    let s := krIns cap kr e
    let r := apKr cap es s.1
    (r.1, r.2 + s.2)

/-- `Table::insert` of the prekey peers: replaced in place, or the oldest makes room. -/
def ekIns (cap : Nat) (ek : List (Node × Bytes)) (e : Node × Bytes) : List (Node × Bytes) :=
  if ek.any (fun o => o.1 == e.1) then setFirst (fun o => o.1 == e.1) e ek
  else if cap = 0 then ek
  else if ek.length = cap then ek.tail ++ [e] else ek ++ [e]

def apEk (cap : Nat) : List (Node × Bytes) → List (Node × Bytes) → List (Node × Bytes)
  | [], ek => ek
  | e :: es, ek => apEk cap es (ekIns cap ek e)

/-! ## `restore_state` against a live state -/

/-- The bounds of the three tables and the two switches of the wrong readers the witnesses use: `lazy` checks the
round trips and prekey peers only while storing them, `lax` lets bytes follow the state. -/
structure Cfg where
  ct : Nat
  kr : Nat
  ek : Nat
  lazy : Bool
  lax : Bool

/-- Every stage in the order of the code: split, check the round trips and prekey peers, tickets (checked whole,
then stored), round trips, prekey peers. The result is the tables afterwards and, when the state was accepted, what
the restore reports (the state's tickets still in the store, round trips stored, prekey peers). -/
def restore (c : Cfg) (live : St) (b : Bytes) (now : Nat) : St × Option (Nat × Nat × Nat) :=
  match hdrP c.lax b with
  | none => (live, none)
  | some h =>
    if !c.lazy && !((krDec (hNk h) (hKr h)).isSome && (ekDec (hNe h) (hEk h)).isSome) then (live, none)
    else
      match tkDec (hTk h) with
      | none => (live, none)
      | some tl =>
        let t := apTk c.ct now tl live.tk
        let live1 : St := ⟨t.1, live.kr, live.ek⟩
        match krDec (hNk h) (hKr h) with
        | none => (live1, none)
        | some kl =>
          let k := apKr c.kr kl live.kr
          match ekDec (hNe h) (hEk h) with
          | none => (⟨t.1, k.1, live.ek⟩, none)
          | some el => (⟨t.1, k.1, apEk c.ek el live.ek⟩, some (tkHeld now tl t.1, k.2, hNe h))

end Pinc.CoreState
