import Vinc.ReconcileRefTail

/-!
# Reconcile refinement, part 2b: honest parts, their encoding and the head of `procPart`

`WP` is a part as it travels on the wire (kind, interval, payload) and `WP.enc` its bytes against the previous bound of
the message, exactly what `Out::head` and the payload writers produce. `HCtx` is the honest context of an arm: a sorted
receiver index whose items fit the item limit, bounds that fit it and are in order.
-/

namespace Vinc.Reconcile
open Vinc.Varint (ValidBytes)

theorem fromBE_append (l : List Nat) (b : Nat) : fromBE (l ++ [b]) = fromBE l * 256 + b := by
  simp [fromBE, List.foldl_append]

theorem fromBE_beBytes : ∀ (w v : Nat), v < 256 ^ w → fromBE (beBytes w v) = v
  | 0, v, h => by simp at h; simp [beBytes, fromBE, h]
  | w + 1, v, h => by
    have h' : v / 256 < 256 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.pow_succ] at h; exact h
    simp only [beBytes, fromBE_append, fromBE_beBytes w (v / 256) h']
    omega

theorem length_beBytes : ∀ (w v : Nat), (beBytes w v).length = w
  | 0, _ => rfl
  | w + 1, v => by simp [beBytes, length_beBytes w]

/-- A part on the wire. -/
inductive WP where
  | fp (I : Iv) (f : Nat)
  | ids (I : Iv) (is : List Nat)
  | full (I : Iv) (xs : List Item)
  | reply (I : Iv) (cc : Nat) (seen : List Nat) (extras : List Item)
  | cold (I : Iv) (xs : List Item)
  | check (f : Nat)
  | miss

/-- The bytes of a part against the previous bound `last` of the message, and the new previous bound. -/
def WP.enc (last : Item) : WP → List Nat × Item
  | .fp I f => let h := putHead last tFP I.lo I.hi; (h.1 ++ fpBytes f, h.2)
  | .ids I is => let h := putHead last tIDS I.lo I.hi; (h.1 ++ venc is.length ++ (is.map (beBytes idLen)).flatten, h.2)
  | .full I xs => let h := putHead last tFULL I.lo I.hi; (h.1 ++ putItems xs, h.2)
  | .reply I cc seen extras =>
    let h := putHead last tREPLY I.lo I.hi; (h.1 ++ venc cc ++ seen ++ putItems extras, h.2)
  | .cold I xs => let h := putHead last tCOLD I.lo I.hi; (h.1 ++ putItems xs, h.2)
  | .check f => let h := putHead last tCHECK [] none; (h.1 ++ fpBytes f, h.2)
  | .miss => putHead last tMISS [] none

/-- Append a part to the reply under construction. -/
def Out.addW (out : Out) (p : WP) : Out :=
  { out with body := out.body ++ (p.enc out.last).1, last := (p.enc out.last).2 }

/-- The honest context of a part whose interval is `I`, processed against the index `S` of the receiver. -/
structure HCtx (lim : Limits) (S : List Item) (c : Core) (I : Iv) : Prop where
  hS : Sorted S
  hlen : ∀ x ∈ S, x.length ≤ lim.maxItem
  hn : c.n = S.length
  hlim : c.lim = lim
  hmx : lim.maxItem < 2 ^ 63
  hlo : I.lo.length ≤ lim.maxItem
  hhi : ∀ h, I.hi = some h → h.length ≤ lim.maxItem
  hord : ∀ h, I.hi = some h → lexLt h I.lo = false

theorem HCtx.hi63 {lim S c I} (h : HCtx lim S c I) : ∀ x, I.hi = some x → x.length < 2 ^ 63 :=
  fun x hx => Nat.lt_of_le_of_lt (h.hhi x hx) h.hmx

theorem rankOf_mono {S : List Item} {lo h : Item} (hh : lexLt h lo = false) : rankOf S lo ≤ rankOf S h := by
  unfold rankOf
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro x _ hx
  rcases (lexLt_false_iff h lo).mp hh with rfl | h2
  · exact hx
  · simpa using lexLt_trans _ _ _ (by simpa using hx) h2

/-- The ranks of the bounds of the interval: `a ≤ b`, and the slice between them is the receiver's items of `I`. -/
theorem HCtx.ranks {lim S c I} (h : HCtx lim S c I) :
    rankOf S I.lo ≤ rankHi S I.hi ∧ rankHi S I.hi ≤ S.length ∧
    (S.drop (rankOf S I.lo)).take (rankHi S I.hi - rankOf S I.lo) = I.items S := by
  have hb : rankHi S I.hi ≤ S.length := by unfold rankHi; cases I.hi <;> simp [rankOf_le]
  refine ⟨?_, hb, slice_eq_filter I.lo I.hi S h.hS⟩
  unfold rankHi
  cases hh : I.hi with
  | none => exact rankOf_le S I.lo
  | some x => exact rankOf_mono (h.hord x hh)

/-- `procPart` on the bytes of a part with a well formed head: the head is consumed and the rest is `tailPart`. -/
theorem procPart_head (o : Oracle) (S : List Item) (c : Core) (I : Iv) (kind : Nat) (rest : List Nat) (mark : Nat)
    (lim : Limits) (h : HCtx lim S c I) (hk : kind < 128) :
    procPart o S c ((putHead c.blast kind I.lo I.hi).1 ++ rest) mark =
      tailPart o S { c with blast := (putHead c.blast kind I.lo I.hi).2 } kind I.lo I.hi rest mark := by
  rw [procPart_eq, show c.lim.maxItem = lim.maxItem from by rw [h.hlim],
    readHead_putHead c.blast kind I.lo I.hi rest lim.maxItem hk h.hlo
    (Nat.lt_of_le_of_lt h.hlo h.hmx) (fun x hx => ⟨h.hhi x hx, h.hi63 x hx⟩)]

end Vinc.Reconcile
