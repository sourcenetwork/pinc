import Pinc.ReconcileCostGuide
import Pinc.ReconcileWireMsg

/-!
vertexclique

# The bytes and the messages of a reconciliation: the bound in Lean

`ReconcileCostGuide` counts parts. That left the two numbers you actually pay for on a network, bytes and messages,
checked only by the model checker for a few fixed sizes. This file proves both, for every size.

The result, for one finished pass between an initiator holding `A` and a responder holding `B`:

* messages: at most `stepsBound f D nA nB`, the same bound as for parts;
* bytes of all the parts sent: at most `stepsBound f D nA nB * partCap L`;
* bytes with the framing of the messages added: at most `stepsBound f D nA nB * (partCap L + over)`.

So bytes and messages are `O(D log n)` too, with a factor that depends only on how long one item may be.

## The names, in plain words

The names of `ReconcileCostGuide` keep their meaning: `A`, `B`, `nA`, `nB`, `D`, part, fan `f`, `lg`, the state `s`
with `s.log` and `s.pend`, `IReach`, `stepsBound`. The new ones:

* `L` is the longest an item may be, in bytes (`Limits::max_item` in the Rust crate). A bound of a range is an item
  or the start of one, so it's never longer than `L` either.
* `aleaf = 32` and `bleaf = 6` are the code's leaf sizes. The initiator sends a range as ids or items once it holds
  at most 32 items there, and the responder does once it holds at most 6.
* `varMax = 9` is the room the code sets aside for one count. `fpLen = 16` is a fingerprint, `idLen = 8` an id.
* `boundLen L` is what one bound of `L` bytes takes on the wire. That's one byte for the prefix it shares with the
  bound before it, then the length, then the bytes.
* `itemLen L` is what one whole item of `L` bytes takes, which is its length followed by its bytes.
* `c.small p` says the part `p` doesn't carry much. A part with ids or items never covers more than 32 items of the
  set it was cut from. I don't assume that anywhere; section 1 proves it from the leaf rules of the code.
* `c.wire L p` is the room the part `p` takes on the wire, by its kind: a head (a tag and two bounds), then a
  fingerprint, or a count and ids, or a count and items, or the reply (a count, the bitmap, a count, the items).
* `partCap L` is the most any part can take, which you get from `c.wire L p` by putting every count at its
  largest.
* `ms` is the pass seen as messages, so a list of messages where each one is the list of parts it carried.
* `over` is whatever one message costs besides its parts: the three length bytes, the count of its parts, and on the
  first message the name of the set. The theorem holds for any `over`, so you can plug in the real one.

## What this still doesn't prove

There are three things it leaves out, and I'd rather say them here than have you find out later.

The theorems are about the part rules of the code (`Proc`, the same model the part bound uses). The sizes are tied
to the encoders the trace checks replay against the Rust code (`putHead`, `venc`, the item and id writers) by the
lemmas of section 2. What's missing is the step in between: that the function which answers a part writes exactly a
head and that payload. That step is the refinement `ReconcileCorrect` lists as open.

The bound is for one pass. A session that runs into an id collision does a second, exact pass, and each of the
two has this bound.

The cold stream isn't covered. When one side is tiny, or ten times smaller than the other, the code skips all of
this and the responder just sends its whole list, which costs `nB` items by design.

The bound is also generous on purpose: `partCap L` charges every part as if it carried 32 items of full length.
With 40-byte items it comes to about 1.7 KB a part, with 4 KiB items to about 140 KB.
-/

namespace Pinc.Reconcile

/-!
## 1. A part never carries more than 32 things

`smallK c kind toInit I` spells out, for each kind of part, what "few" means. `c` is the pair of sets, `kind` the
kind of the part, `toInit` whether the initiator is the one who handles it next, `I` its range of keys.
-/
def smallK (c : Cfg) : Kind → Bool → Iv → Prop
  -- A fingerprint part carries no items at all.
  | .fp, _, _ => True
  -- Ids always travel from the initiator: at most 32 of its items lie in the range.
  | .ids, _, I => cnt c.A I ≤ aleaf
  -- Whole items sent by the responder (the initiator handles them next): at most 6.
  | .full, true, I => cnt c.B I ≤ bleaf
  -- Whole items sent by the initiator: at most 32.
  | .full, false, I => cnt c.A I ≤ aleaf
  -- A reply answers at most 32 of the initiator's items and adds at most 32 of the responder's.
  | .reply _, _, I => cnt c.A I ≤ aleaf ∧ cnt c.B I ≤ aleaf

/-- `c.small p`: the part `p` is small in the sense above. -/
def Cfg.small (c : Cfg) (p : Part) : Prop := smallK c p.kind p.toInit p.iv

/-- Handling a small part only ever makes small parts. `h` is one step of the code on the part `p`, which produced
the parts `kids`; `hp` says `p` was small. Each case below is one arm of `Core::answer`. -/
theorem Proc.small {c : Cfg} {ex : Bool} {p : Part} {kids : List Part} {ha ta : List Item} {lf : Bool}
    (h : Proc c ex p kids ha ta lf) (hp : c.small p) : ∀ k ∈ kids, c.small k := by
  cases h with
  | @fpEq d t I h1 =>
    -- The fingerprints matched: nothing is sent back.
    intro k hk; cases hk
  | @fpLeafResp d I hne hcnt hf =>
    -- The responder answers with its own items; `hcnt` is the code's test that it holds at most 6 there.
    intro k hk
    have e : k = ⟨.full, true, I, d + 1⟩ := by simpa using hk
    subst e; exact hcnt
  | @fpLeafInit d I hne hcnt hf =>
    -- The initiator answers with ids, or with items in an exact pass; `hcnt`: it holds at most 32 there.
    intro k hk
    have e : k = ⟨if ex then .full else .ids, false, I, d + 1⟩ := by simpa using hk
    subst e
    cases ex <;> first | exact hcnt | (simp [Cfg.small, smallK]; exact hcnt)
  | @fpSplit d t I fan hne hno hf1 hf2 =>
    -- A split makes fingerprint parts only, and those carry nothing.
    intro k hk
    obtain ⟨J, _, rfl⟩ := List.mem_map.1 hk
    exact True.intro
  | @respLeaf d I k0 hk0 hcnt hf =>
    -- The responder replies to ids or items of the initiator. `hp` gives the initiator's 32, `hcnt` the responder's.
    intro k hk
    have e : k = ⟨.reply (decide (k0 = Kind.ids)), true, I, d + 1⟩ := by simpa using hk
    subst e
    rcases hk0 with rfl | rfl
    · exact ⟨hp, hcnt⟩
    · exact ⟨hp, hcnt⟩
  | @respNarrow d I k0 fan hk0 hno hf1 hf2 =>
    -- The reply wouldn't fit one message, so the responder splits instead: fingerprint parts again.
    intro k hk
    obtain ⟨J, _, rfl⟩ := List.mem_map.1 hk
    exact True.intro
  | @fullInit d I => intro k hk; cases hk
  | @replyExact d I => intro k hk; cases hk
  | @replyIds d I => intro k hk; cases hk

/-- Every part of a run is small: the ones already handled (`s.log`) and the ones waiting (`s.pend`). `h` says the
state `s` is reachable from the first message of a pass. -/
theorem small_all {c : Cfg} {s : St} (h : IReach c s) : ∀ q ∈ s.log ++ s.pend, c.small q := by
  induction h with
  | @init ex s0 hi =>
    -- The first message. Either one leaf (the initiator holds at most 32 items in all) or a split.
    cases hi with
    | leaf hcnt hf =>
      intro q hq
      have e : q = ⟨if ex then .full else .ids, false, Iv.top, 1⟩ := by simpa using hq
      subst e
      cases ex <;> first | exact hcnt | (simp [Cfg.small, smallK]; exact hcnt)
    | @split fan hno hf1 hf2 =>
      intro q hq
      have hq' : q ∈ (splitIvs c.A Iv.top fan).map (fun J => (⟨.fp, false, J, 1⟩ : Part)) := by simpa using hq
      obtain ⟨J, _, rfl⟩ := List.mem_map.1 hq'
      exact True.intro
  | @step s s' _ hs ih =>
    -- One more part `p` was handled. `rest` are the parts that were waiting beside it, `kids` the ones it made.
    cases hs with
    | @step p rest kids ha ta lf hperm hp =>
      -- `hpm`: `p` and `rest` were all waiting in `s`, so the claim already holds for them (`ih`).
      have hpm : ∀ x, x ∈ p :: rest → x ∈ s.pend := fun x hx => (hperm.mem_iff).2 hx
      have hpS : c.small p := ih p (List.mem_append_right _ (hpm p (by simp)))
      -- The new state has `s.log ++ [p]` handled and `kids ++ rest` waiting: four places a part `q` can be.
      have key : ∀ q, q ∈ (s.log ++ [p]) ++ (kids ++ rest) → c.small q := by
        intro q hq
        rcases List.mem_append.1 hq with h1 | h2
        · rcases List.mem_append.1 h1 with h3 | h4
          · exact ih q (List.mem_append_left _ h3)
          · have e : q = p := by simpa using h4
            subst e; exact hpS
        · rcases List.mem_append.1 h2 with h5 | h6
          · exact Proc.small hp hpS q h5
          · exact ih q (List.mem_append_right _ (hpm q (by simp [h6])))
      exact key

/-!
## 2. What a part takes on the wire

First the sizes of the encoders themselves, then the room of a part by its kind.
-/

/-- `itemLen L`: one item of at most `L` bytes on the wire, its length first and then its bytes. -/
def itemLen (L : Nat) : Nat := Varint.encodedLen L + L

/-- A longer bound never takes less room. `a` and `b` are two lengths in bytes. -/
theorem boundLen_mono {a b : Nat} (h : a ≤ b) : boundLen a ≤ boundLen b := by
  unfold boundLen
  -- `e`: the length field of the longer bound is at least as long.
  have e := encodedLen_mono b a h
  omega

/-- The head of a part (`putHead`, the encoder of `Out::head`): a tag and two bounds of at most `L` bytes each take
at most `1 + 2 * boundLen L` bytes. `last` is the bound written before it (bounds share their prefix with it), `kind`
the tag, `lo` and `hi` the two ends of the range; `hi` is absent when the range runs to the end. -/
theorem head_bytes_le (L : Nat) (last : Item) (kind : Nat) (lo : Item) (hi : Option Item)
    (hlo : lo.length ≤ L) (hhi : ∀ x, hi = some x → x.length ≤ L) :
    (putHead last kind lo hi).1.length ≤ 1 + 2 * boundLen L := by
  have a := boundLen_mono hlo
  cases hi with
  | none =>
    have t := putHead_length_le last kind lo none
    simp at t
    omega
  | some x =>
    have b := boundLen_mono (hhi x rfl)
    have t := putHead_length_le last kind lo (some x)
    simp at t
    omega

/-- A run of whole items (the payload `items_part` and the reply write): `xs` are the items, each at most `L` bytes
(`h`), and together they take at most `itemLen L` bytes each. -/
theorem items_bytes_le (L : Nat) : ∀ xs : List Item, (∀ x ∈ xs, x.length ≤ L) →
    ((xs.map fun x => venc x.length ++ x).flatten).length ≤ xs.length * itemLen L
  | [], _ => by simp
  | x :: xs, h => by
    -- `ih`: the claim for the rest of the list. `hx`: this item is at most `L` bytes. `e`: so is its length field.
    have ih := items_bytes_le L xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx : x.length ≤ L := h x (by simp)
    have e := encodedLen_mono L x.length hx
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, venc_length]
    unfold itemLen at ih ⊢
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- `beBytes w v` writes exactly `w` bytes, whatever the value `v`. -/
theorem beBytes_len : ∀ w v : Nat, (beBytes w v).length = w
  | 0, _ => rfl
  | w + 1, v => by simp [beBytes, beBytes_len w (v / 256)]

/-- A run of ids (the payload `ids_part` writes): `idLen` bytes for each item of `xs`. `o` is the keyed hash. -/
theorem ids_bytes (o : Oracle) : ∀ xs : List Item, ((xs.map (idBytes o)).flatten).length = idLen * xs.length
  | [] => by simp
  | x :: xs => by
    have ih := ids_bytes o xs
    have e : (idBytes o x).length = idLen := by unfold idBytes; exact beBytes_len idLen _
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, e]
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- A fingerprint is `fpLen` bytes. -/
theorem fp_bytes (v : Nat) : (fpBytes v).length = fpLen := by unfold fpBytes; exact beBytes_len fpLen v

/-- `wireK c L kind toInit I`: the payload of a part after its head, by kind. The four lemmas above are where each
term comes from. -/
def wireK (c : Cfg) (L : Nat) : Kind → Bool → Iv → Nat
  -- one fingerprint
  | .fp, _, _ => fpLen
  -- a count, then one id for each of the initiator's items in the range
  | .ids, _, I => varMax + idLen * cnt c.A I
  -- a count, then the responder's items in the range
  | .full, true, I => varMax + cnt c.B I * itemLen L
  -- a count, then the initiator's items in the range
  | .full, false, I => varMax + cnt c.A I * itemLen L
  -- a count, one bit for each item asked about, a count, then the responder's items the asker lacks
  | .reply _, _, I => varMax + (cnt c.A I + 7) / 8 + varMax + cnt c.B I * itemLen L

/-- `c.wire L p`: the room of the part `p`, head and payload. -/
def Cfg.wire (c : Cfg) (L : Nat) (p : Part) : Nat := 1 + 2 * boundLen L + wireK c L p.kind p.toInit p.iv

/-- `partCap L`: the most one part can take when items are at most `L` bytes: the head, two counts, the 4 bytes of a
32-bit bitmap, and 32 whole items. -/
def partCap (L : Nat) : Nat := 1 + 2 * boundLen L + 2 * varMax + aleaf / 8 + aleaf * (varMax + itemLen L)

/-- A small part fits `partCap L`. `h` is the smallness of `p` from section 1. -/
theorem wire_le (c : Cfg) (L : Nat) (p : Part) (h : c.small p) : c.wire L p ≤ partCap L := by
  obtain ⟨k, t, I, d⟩ := p
  cases k with
  | fp =>
    simp only [Cfg.wire, wireK, partCap, aleaf, varMax, fpLen]
    omega
  | ids =>
    -- `h'`: at most 32 ids, 8 bytes each.
    have h' : cnt c.A I ≤ aleaf := h
    simp only [Cfg.wire, wireK, partCap, aleaf, varMax, idLen] at h' ⊢
    omega
  | full =>
    cases t with
    | true =>
      -- `h'`: at most 6 items of the responder; `m`: so their bytes are at most those of 32 items.
      have h' : cnt c.B I ≤ bleaf := h
      have m := Nat.mul_le_mul_right (itemLen L) (Nat.le_trans h' (by decide : bleaf ≤ aleaf))
      simp only [Cfg.wire, wireK, partCap, aleaf, varMax] at m ⊢
      omega
    | false =>
      have h' : cnt c.A I ≤ aleaf := h
      have m := Nat.mul_le_mul_right (itemLen L) h'
      simp only [Cfg.wire, wireK, partCap, aleaf, varMax] at m ⊢
      omega
  | reply v =>
    -- `h'.1`: at most 32 items were asked about, so the bitmap is at most 4 bytes. `h'.2`: at most 32 come back.
    have h' : cnt c.A I ≤ aleaf ∧ cnt c.B I ≤ aleaf := h
    have h1 := h'.1
    have m := Nat.mul_le_mul_right (itemLen L) h'.2
    simp only [Cfg.wire, wireK, partCap, aleaf, varMax] at h1 m ⊢
    omega

/-!
## 3. The bytes of a pass

`c.bytes L ps` adds up the room of the parts `ps`.
-/
def Cfg.bytes (c : Cfg) (L : Nat) (ps : List Part) : Nat := lsum (c.wire L) ps

/-- The parts of a finished pass take at most `stepsBound f D nA nB * partCap L` bytes. `f` is a fan the run never
went below (`hfm`), `s` a finished state (`hp`: nothing is waiting), `L` the longest an item may be. -/
theorem bytes_bound {c : Cfg} {f : Nat} (L : Nat) (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s : St} (h : IReach c s)
    (hp : s.pend = []) : c.bytes L s.log ≤ stepsBound f c.diff c.A.length c.B.length * partCap L := by
  -- `hn`: how many parts there were, from the part bound.
  have hn := aps_steps_bound hfl hfm h hp
  -- `hs`: every one of them is small (section 1).
  have hs := small_all h
  -- `h1`: so each takes at most `partCap L`, and the sum is at most that many times `partCap L`.
  have h1 : lsum (c.wire L) s.log ≤ lsum (fun _ => partCap L) s.log :=
    lsum_le s.log (fun q hq => wire_le c L q (hs q (List.mem_append_left _ hq)))
  rw [lsum_const] at h1
  unfold Cfg.bytes
  exact Nat.le_trans h1 (Nat.mul_le_mul_right _ hn)

/-!
## 4. The messages of a pass

`ms` is the pass as a list of messages. A message that carries no part ends the exchange, so every message that
keeps a pass going carries at least one (`hne`). Then there can't be more messages than parts.
-/
theorem messages_le_parts : ∀ ms : List (List Part), (∀ m ∈ ms, m ≠ []) → ms.length ≤ ms.flatten.length
  | [], _ => by simp
  | m :: ms, h => by
    -- `ih`: the claim for the later messages. `h1`: this message has at least one part.
    have ih := messages_le_parts ms (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hm : m ≠ [] := h m (by simp)
    have h1 : 1 ≤ m.length := by
      cases m with
      | nil => exact absurd rfl hm
      | cons x xs => simp
    rw [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- A finished pass is at most `stepsBound f D nA nB` messages. `hcut` says the messages `ms`, laid end to end, are
exactly the parts the pass handled. -/
theorem messages_bound {c : Cfg} {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s : St} (h : IReach c s)
    (hp : s.pend = []) (ms : List (List Part)) (hcut : ms.flatten = s.log) (hne : ∀ m ∈ ms, m ≠ []) :
    ms.length ≤ stepsBound f c.diff c.A.length c.B.length := by
  have a := messages_le_parts ms hne
  rw [hcut] at a
  exact Nat.le_trans a (aps_steps_bound hfl hfm h hp)

/-- Everything on the wire: the parts and `over` more bytes for each message. -/
theorem wire_bound {c : Cfg} {f : Nat} (L over : Nat) (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s : St}
    (h : IReach c s) (hp : s.pend = []) (ms : List (List Part)) (hcut : ms.flatten = s.log)
    (hne : ∀ m ∈ ms, m ≠ []) :
    c.bytes L s.log + ms.length * over ≤ stepsBound f c.diff c.A.length c.B.length * (partCap L + over) := by
  -- `b`: the parts. `m`: the messages, each charged `over`.
  have b := bytes_bound L hfl hfm h hp
  have m := Nat.mul_le_mul_right over (messages_bound hfl hfm h hp ms hcut hne)
  rw [Nat.mul_add]
  omega

/-- Equal sets: at most 17 messages and `17 * partCap L` bytes of parts, whatever the sizes of the sets. -/
theorem equal_sets_wire {c : Cfg} (L : Nat) {s : St} (h : IReach c s) (hp : s.pend = []) (hD : c.diff = 0) :
    c.bytes L s.log ≤ 17 * partCap L := by
  have b := bytes_bound (f := 2) L (Nat.le_refl 2) c.hmin h hp
  unfold stepsBound at b
  rw [hD, Nat.zero_mul] at b
  simpa using b

#audit_axioms Pinc.Reconcile.Proc.small
#audit_axioms Pinc.Reconcile.small_all
#audit_axioms Pinc.Reconcile.head_bytes_le
#audit_axioms Pinc.Reconcile.items_bytes_le
#audit_axioms Pinc.Reconcile.ids_bytes
#audit_axioms Pinc.Reconcile.fp_bytes
#audit_axioms Pinc.Reconcile.wire_le
#audit_axioms Pinc.Reconcile.bytes_bound
#audit_axioms Pinc.Reconcile.messages_bound
#audit_axioms Pinc.Reconcile.wire_bound
#audit_axioms Pinc.Reconcile.equal_sets_wire

end Pinc.Reconcile
