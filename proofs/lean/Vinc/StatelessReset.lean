import Vinc.Axioms

/-!
# The stateless reset token check

A model of `crates/vinc-core/src/reset.rs`.

Who acts: a node A that holds a session to a peer B, and keeps the tokens B gave it in that session; B, which after a
restart answers a packet on an id it forgot with a reset carrying the id and its token; and anyone else, who can send
A a reset with any id and any token it can make or has seen.

- `token k c a` is `token(key, cid, remote)`: the keyed hash of the id and the address under the reset key. It is a
  free term here, so two tokens are equal only for the same key, id and address: the collision resistance of the
  keyed hash (BLAKE3 in keyed mode), the hypothesis `CryptoKdf` names `PrimInj`.
- `Store` is a session's `tokens` and `token_next`: four entries of an id and its token, and the entry the next new id
  replaces. `take` is `take_token`: a token for an id already held replaces that entry, a new id takes `token_next`,
  which then moves on (mod 4).
- `accepts` is the test `on_reset` makes for one session: an entry holds exactly the reset's id and token (`ct_eq`
  on the token), and the session heard nothing for a smoothed round trip (`now.saturating_sub(last_rx) >= srtt`, a
  truncating `Nat` subtraction).
- `isReset` and `isShort` are the first-byte forms of `is_reset` and `short_dcid`, and `answers` is the size rule of
  `answer_unknown`.

What must hold, and is proven below: a reset is taken only with an entry that matches it and only from a quiet session
(`accepts_sound`, `heard_refused`); if every token a session holds was made with B's key, a token made with any other
key, a made-up one included, is refused (`other_key_refused`), and so is a genuine token of another id, which is what a
replayed reset of an old session carries (`other_id_refused`); a key that survives the restart makes the restarted
B's reset taken (`restart_taken`), and a key that does not survive makes it refused (`fresh_key_refused`, the _freshkey
witness of `StatelessReset.tla`); taking a token keeps it and keeps the store's tokens all B's (`take_keeps`,
`take_genuine`); a reset is never mistaken for a packet (`reset_not_short`); and B's reset is shorter than what it
answers (`answers_shorter`).
-/

namespace Vinc.StatelessReset

/-- A token: the keyed hash of id `cid` used from address `addr`, under reset key `key`, as a free term. -/
structure Tok where
  key : Nat
  cid : Nat
  addr : Nat
deriving DecidableEq

/-- `token(key, cid, remote)`. -/
def token (k c a : Nat) : Tok := ⟨k, c, a⟩

/-- A session's tokens (`tokens`, four entries) and the entry the next new id replaces (`token_next`). -/
structure Store where
  e : Fin 4 → Option (Nat × Tok)
  next : Fin 4

/-- The store of a new session (`Meta::EMPTY`). -/
def Store.empty : Store := ⟨fun _ => none, 0⟩

/-- Whether entry `i` holds id `c`. -/
def holdsId (s : Store) (c : Nat) (i : Fin 4) : Bool :=
  match s.e i with
  | some (c', _) => c' == c
  | none => false

/-- The entry `take_token` writes: the first that holds the id, else `token_next`. -/
def slotOf (s : Store) (c : Nat) : Fin 4 :=
  if holdsId s c 0 then 0
  else if holdsId s c 1 then 1
  else if holdsId s c 2 then 2
  else if holdsId s c 3 then 3
  else s.next

/-- `take_token`: keep token `t` of id `c`. -/
def take (s : Store) (c : Nat) (t : Tok) : Store :=
  let w := slotOf s c
  { e := fun i => if i = w then some (c, t) else s.e i
    next := if w = s.next then s.next + 1 else s.next }

/-- Some entry `i` satisfies `p`: the scan of `tokens` in `on_reset`. -/
def any4 (p : Fin 4 → Bool) : Bool := p 0 || p 1 || p 2 || p 3

/-- `on_reset`'s test for one session: an entry is exactly the reset's id and token, and the session heard nothing
for `srtt` (its smoothed round trip) up to `now`. -/
def accepts (s : Store) (c : Nat) (t : Tok) (now lastRx srtt : Nat) : Bool :=
  any4 (fun i => decide (s.e i = some (c, t))) && decide (srtt ≤ now - lastRx)

/-- Every token the store holds is B's for its own id: made with key `k` for the id it is filed under. -/
def Genuine (k : Nat) (s : Store) : Prop :=
  ∀ i c t, s.e i = some (c, t) → t.key = k ∧ t.cid = c

/-- `any4` is a scan of the four entries. -/
theorem any4_true (p : Fin 4 → Bool) : any4 p = true ↔ ∃ i, p i = true := by
  constructor
  · intro h
    simp only [any4, Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · rintro ⟨i, hi⟩
    simp only [any4, Bool.or_eq_true]
    match i with
    | ⟨0, _⟩ => exact Or.inl (Or.inl (Or.inl hi))
    | ⟨1, _⟩ => exact Or.inl (Or.inl (Or.inr hi))
    | ⟨2, _⟩ => exact Or.inl (Or.inr hi)
    | ⟨3, _⟩ => exact Or.inr hi
    | ⟨n + 4, h⟩ => exact absurd h (by omega)

/-- A taken reset matches an entry exactly, id and token. -/
theorem accepts_sound {s : Store} {c : Nat} {t : Tok} {now l r : Nat} (h : accepts s c t now l r = true) :
    ∃ i, s.e i = some (c, t) := by
  simp only [accepts, Bool.and_eq_true] at h
  obtain ⟨i, hi⟩ := (any4_true _).1 h.1
  exact ⟨i, of_decide_eq_true hi⟩

/-- A session that heard its peer within a round trip takes no reset, whatever it carries. -/
theorem heard_refused (s : Store) (c : Nat) (t : Tok) {now l r : Nat} (h : now - l < r) :
    accepts s c t now l r = false := by
  simp only [accepts, Bool.and_eq_false_iff]
  exact Or.inr (decide_eq_false (by omega))

/-- With only B's tokens held, a token made with any other key is refused: a made-up token, or one of another node. -/
theorem other_key_refused {k : Nat} {s : Store} (g : Genuine k s) (c : Nat) {t : Tok} (hk : t.key ≠ k)
    (now l r : Nat) : accepts s c t now l r = false := by
  cases h : accepts s c t now l r with
  | false => rfl
  | true =>
    obtain ⟨i, hi⟩ := accepts_sound h
    exact absurd (g i c t hi).1 hk

/-- With only B's tokens held, B's genuine token of another id is refused: a reset replayed from another session
names an id this session does not use, and carries that id's token. -/
theorem other_id_refused {k : Nat} {s : Store} (g : Genuine k s) {c : Nat} {t : Tok} (hc : t.cid ≠ c)
    (now l r : Nat) : accepts s c t now l r = false := by
  cases h : accepts s c t now l r with
  | false => rfl
  | true =>
    obtain ⟨i, hi⟩ := accepts_sound h
    exact absurd (g i c t hi).2 hc

/-- The key survives the restart: the restarted B computes the same token for the id and address, and a quiet
session that holds it takes the reset. -/
theorem restart_taken {s : Store} {i : Fin 4} {k c a now l r : Nat} (hi : s.e i = some (c, token k c a))
    (hq : r ≤ now - l) : accepts s c (token k c a) now l r = true := by
  simp only [accepts, Bool.and_eq_true]
  exact ⟨(any4_true _).2 ⟨i, decide_eq_true hi⟩, decide_eq_true hq⟩

/-- The key does not survive the restart (a new key `k'`): the restarted B's reset is refused, so the dead session
stays up until its idle timeout. This is why the key comes from the identity. -/
theorem fresh_key_refused {k k' : Nat} {s : Store} (g : Genuine k s) (hk : k' ≠ k) (c a now l r : Nat) :
    accepts s c (token k' c a) now l r = false :=
  other_key_refused g c hk now l r

/-- A new session's store holds nothing, so it is B's. -/
theorem empty_genuine (k : Nat) : Genuine k Store.empty := by
  intro i c t h
  simp [Store.empty] at h

/-- Taking a token keeps it: the entry `take_token` writes holds the id and the token. -/
theorem take_keeps (s : Store) (c : Nat) (t : Tok) : (take s c t).e (slotOf s c) = some (c, t) := by
  simp [take]

/-- Taking B's token of an id keeps every held token B's. -/
theorem take_genuine {k : Nat} {s : Store} (g : Genuine k s) (c a : Nat) : Genuine k (take s c (token k c a)) := by
  intro i c' t' h
  simp only [take] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · exact g i c' t' h

/-- `is_reset`'s first byte form: bits 7, 6, 5 are 0, 1, 1. -/
def isReset (b : Nat) : Bool := b % 256 / 32 == 3
/-- `short_dcid`'s first byte form: bits 7, 6, 5 are 0, 1, 0. -/
def isShort (b : Nat) : Bool := b % 256 / 32 == 2

/-- A reset is never read as a packet, and a packet never as a reset. -/
theorem reset_not_short (b : Nat) : ¬(isReset b = true ∧ isShort b = true) := by
  simp only [isReset, isShort, beq_iff_eq]
  omega

/-- The bytes of a reset: one first byte, a 4-byte id, a 16-byte token. -/
def resetLen : Nat := 1 + 4 + 16

/-- `answer_unknown` answers only a datagram longer than a reset. -/
def answers (len : Nat) : Bool := resetLen < len

/-- A reset is shorter than the datagram it answers, so a spoofed source gets back less than it sent. -/
theorem answers_shorter {len : Nat} (h : answers len = true) : resetLen < len := by
  simpa [answers] using h

end Vinc.StatelessReset

#audit_axioms Vinc.StatelessReset.any4_true
#audit_axioms Vinc.StatelessReset.accepts_sound
#audit_axioms Vinc.StatelessReset.heard_refused
#audit_axioms Vinc.StatelessReset.other_key_refused
#audit_axioms Vinc.StatelessReset.other_id_refused
#audit_axioms Vinc.StatelessReset.restart_taken
#audit_axioms Vinc.StatelessReset.fresh_key_refused
#audit_axioms Vinc.StatelessReset.empty_genuine
#audit_axioms Vinc.StatelessReset.take_keeps
#audit_axioms Vinc.StatelessReset.take_genuine
#audit_axioms Vinc.StatelessReset.reset_not_short
#audit_axioms Vinc.StatelessReset.answers_shorter
