import Vinc.ReconcileWireProofs
import Vinc.ReconcileParts

/-!
# Reconcile wire proofs: part heads, frames, the count field, item lists, sizes

Unbounded theorems about the message layer of `vinc-reconcile/src/wire.rs` (see `ReconcileWireProofs.lean` for the
bounds). TLA+ counterpart: `proofs/tla/ReconcileWire.tla`.

* heads: `readHead_putHead` (the infinity bit included) and `readHead_canonical`;
* bound sequences against a running `last`: `readBounds_putBounds`, `readBounds_canonical`;
* frames: `frameBody_frameHeader`, `frameBody_canonical`, `frameBody_short`, `frameBody_mismatch`,
  `frameHeader_none_iff`;
* the count field: `readParts_putParts` (the `more` bit and the count rule), `readParts_canonical`,
  `readParts_zero_more`;
* item lists: `readItems_putItems`, `readItems_canonical`, the refusals of `IS.next`;
* sizes: `putBound_length_le`, `putHead_length_le`, `putItems_length`, `putParts_length`.
-/

namespace Vinc.Reconcile
open Vinc.Varint (ValidBytes)

/-! ## Heads -/

/-- The head of a part as `procPart` reads it: the tag byte, the lower bound, and unless infinite the upper bound.
Returns the kind, the bounds, the new previous bound and the rest. -/
def readHead (last : Item) (r : List Nat) (mx : Nat) :
    Except Reason ((Nat × Item × Option Item) × Item × List Nat) :=
  match readU8 r with
  | .error e => .error e
  | .ok (t, r) =>
    match readBound last r mx with
    | .error e => .error e
    | .ok (lo, r) =>
      if t ≥ 128 then .ok ((t % 128, lo, none), lo, r)
      else
        match readBound lo r mx with
        | .error e => .error e
        | .ok (hi, r) => .ok ((t, lo, some hi), hi, r)

theorem readHead_putHead (last : Item) (kind : Nat) (lo : Item) (hi : Option Item) (rest : List Nat) (mx : Nat)
    (hk : kind < 128) (hlo : lo.length ≤ mx) (hlo' : lo.length < 2 ^ 63)
    (hhi : ∀ h, hi = some h → h.length ≤ mx ∧ h.length < 2 ^ 63) :
    readHead last ((putHead last kind lo hi).1 ++ rest) mx = .ok ((kind, lo, hi), (putHead last kind lo hi).2, rest) := by
  cases hi with
  | none =>
    have e : (putHead last kind lo none).1 = (kind + 128) :: (putBound last lo).1 := by
      simp [putHead, Varint.or128 kind hk, tINF]
    have h2 : (putHead last kind lo none).2 = lo := rfl
    rw [e, h2]
    simp only [List.cons_append]
    simp [readHead, readU8, readBound_putBound last lo rest mx hlo hlo', hk]
  | some h =>
    obtain ⟨hh, hh'⟩ := hhi h rfl
    have e : (putHead last kind lo (some h)).1 = kind :: ((putBound last lo).1 ++ (putBound lo h).1) := rfl
    have h2 : (putHead last kind lo (some h)).2 = h := rfl
    rw [e, h2]
    simp only [List.cons_append, List.append_assoc]
    simp [readHead, readU8, readBound_putBound last lo _ mx hlo hlo',
      readBound_putBound lo h rest mx hh hh', hk]

/-- A head is accepted only as the encoding the encoder writes. -/
theorem readHead_canonical (last : Item) (r : List Nat) (mx : Nat) (hv : ValidBytes r) (kind : Nat) (lo : Item)
    (hi : Option Item) (last' : Item) (rest : List Nat)
    (h : readHead last r mx = .ok ((kind, lo, hi), last', rest)) :
    r = (putHead last kind lo hi).1 ++ rest ∧ last' = (putHead last kind lo hi).2 ∧ kind < 128 := by
  cases r with
  | nil => simp [readHead, readU8] at h
  | cons t r1 =>
    have ht : t < 256 := hv t (List.mem_cons_self ..)
    have hv1 : ValidBytes r1 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    simp only [readHead, readU8] at h
    cases hb1 : readBound last r1 mx with
    | error e => simp [hb1] at h
    | ok p =>
      obtain ⟨lo', r2⟩ := p
      simp only [hb1] at h
      by_cases htg : t ≥ 128
      · simp only [htg, if_true, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨hk1, hk2, hk3⟩, hk4, hk5⟩ := h
        subst hk1 hk2 hk3 hk4 hk5
        obtain ⟨c1, _⟩ := readBound_canonical last r1 mx hv1 lo' r2 hb1
        have hk : t % 128 < 128 := Nat.mod_lt _ (by omega)
        have e : (putHead last (t % 128) lo' none).1 = (t % 128 + 128) :: (putBound last lo').1 := by
          simp [putHead, Varint.or128 (t % 128) hk, tINF]
        rw [e]
        refine ⟨?_, rfl, hk⟩
        have : t % 128 + 128 = t := by omega
        rw [this, List.cons_append, ← c1]
      · have htg' : ¬ t ≥ 128 := htg
        simp only [htg', if_false] at h
        cases hb2 : readBound lo' r2 mx with
        | error e => simp [hb2] at h
        | ok q =>
          obtain ⟨hi', r3⟩ := q
          simp only [hb2, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨hk1, hk2, hk3⟩, hk4, hk5⟩ := h
          subst hk1 hk2 hk3 hk4 hk5
          have hv2 : ValidBytes r2 := by
            obtain ⟨c1, _⟩ := readBound_canonical last r1 mx hv1 lo' r2 hb1
            intro x hx; apply hv1; rw [c1]; exact List.mem_append_right _ hx
          obtain ⟨c1, _⟩ := readBound_canonical last r1 mx hv1 lo' r2 hb1
          obtain ⟨c2, _⟩ := readBound_canonical lo' r2 mx hv2 hi' r3 hb2
          have e : (putHead last t lo' (some hi')).1 = t :: ((putBound last lo').1 ++ (putBound lo' hi').1) := rfl
          rw [e]
          refine ⟨?_, rfl, by omega⟩
          rw [c1, c2]; simp

/-! ## Sequences of bounds against a running previous bound -/

def putBounds : Item → List Item → List Nat × Item
  | last, [] => ([], last)
  | last, b :: bs => ((putBound last b).1 ++ (putBounds b bs).1, (putBounds b bs).2)

def readBounds (mx : Nat) : Nat → Item → List Nat → Except Reason (List Item × Item × List Nat)
  | 0, last, r => .ok ([], last, r)
  | k + 1, last, r =>
    match readBound last r mx with
    | .error e => .error e
    | .ok (b, r) =>
      match readBounds mx k b r with
      | .error e => .error e
      | .ok (bs, l, r) => .ok (b :: bs, l, r)

theorem readBounds_putBounds (mx : Nat) : ∀ (bs : List Item) (last : Item) (rest : List Nat),
    (∀ b ∈ bs, b.length ≤ mx ∧ b.length < 2 ^ 63) →
    readBounds mx bs.length last ((putBounds last bs).1 ++ rest) = .ok (bs, (putBounds last bs).2, rest)
  | [], last, rest, _ => by simp [putBounds, readBounds]
  | b :: bs, last, rest, h => by
    have hb := h b (List.mem_cons_self ..)
    have ih := readBounds_putBounds mx bs b rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [putBounds, List.length_cons, readBounds, List.append_assoc]
    rw [readBound_putBound last b _ mx hb.1 hb.2]
    simp only [ih]

theorem readBounds_canonical (mx : Nat) : ∀ (k : Nat) (last : Item) (r : List Nat), ValidBytes r →
    ∀ bs l rest, readBounds mx k last r = .ok (bs, l, rest) →
      bs.length = k ∧ r = (putBounds last bs).1 ++ rest ∧ l = (putBounds last bs).2
  | 0, last, r, _, bs, l, rest, h => by
    simp [readBounds] at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp [putBounds]
  | k + 1, last, r, hv, bs, l, rest, h => by
    simp only [readBounds] at h
    cases hb : readBound last r mx with
    | error e => simp [hb] at h
    | ok p =>
      obtain ⟨b, r2⟩ := p
      simp only [hb] at h
      cases hs : readBounds mx k b r2 with
      | error e => simp [hs] at h
      | ok q =>
        obtain ⟨bs', l', r3⟩ := q
        simp only [hs, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨c1, _⟩ := readBound_canonical last r mx hv b r2 hb
        have hv2 : ValidBytes r2 := by
          intro x hx; apply hv; rw [c1]; exact List.mem_append_right _ hx
        obtain ⟨n, c2, c3⟩ := readBounds_canonical mx k b r2 hv2 bs' l' r3 hs
        refine ⟨by simp [n], ?_, ?_⟩
        · simp only [putBounds]; rw [c1, c2]; simp
        · simp only [putBounds]; exact c3

/-! ## Frames -/

theorem beBytes3 (v : Nat) (h : v ≤ frameMax) : beBytes 3 v = [v / 65536, v / 256 % 256, v % 256] := by
  unfold frameMax at h
  simp [beBytes]
  omega

theorem frameHeader_none_iff (len : Nat) : frameHeader len = none ↔ len > frameMax := by
  unfold frameHeader; split <;> simp_all

theorem frameHeader_some (len : Nat) (h : len ≤ frameMax) : frameHeader len = some [len / 65536, len / 256 % 256, len % 256] := by
  unfold frameHeader; simp [Nat.not_lt.mpr h, beBytes3 len h]

theorem frameBody_frameHeader (body hd : List Nat) (h : frameHeader body.length = some hd) :
    frameBody (hd ++ body) = .ok body := by
  have hle : body.length ≤ frameMax := by
    by_cases hg : body.length > frameMax
    · rw [(frameHeader_none_iff _).2 hg] at h; simp at h
    · omega
  rw [frameHeader_some _ hle] at h
  simp only [Option.some.injEq] at h
  subst h
  simp only [frameBody, List.cons_append, List.nil_append]
  unfold frameMax at hle
  simp; omega

theorem frameBody_short (msg : List Nat) (h : msg.length < 3) : frameBody msg = .error .truncated := by
  match msg, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl

theorem frameBody_mismatch (a b c : Nat) (body : List Nat) (h : (a * 256 + b) * 256 + c ≠ body.length) :
    frameBody (a :: b :: c :: body) = .error .frame := by
  simp [frameBody, h]

/-- A framed message is the one header of its body's length followed by the body. -/
theorem frameBody_canonical (msg body : List Nat) (hv : ValidBytes msg) (h : frameBody msg = .ok body) :
    ∃ hd, frameHeader body.length = some hd ∧ msg = hd ++ body := by
  match msg, h with
  | a :: b :: c :: bd, h =>
    simp only [frameBody] at h
    split at h
    · rename_i hl
      simp only [Except.ok.injEq] at h; subst h
      have ha : a < 256 := hv a (by simp)
      have hb : b < 256 := hv b (by simp)
      have hc : c < 256 := hv c (by simp)
      have hfm : frameMax = 0xffffff := rfl
      have hle : bd.length ≤ frameMax := by omega
      refine ⟨_, frameHeader_some _ hle, ?_⟩
      have e1 : ((a * 256 + b) * 256 + c) / 65536 = a := by omega
      have e2 : ((a * 256 + b) * 256 + c) / 256 % 256 = b := by omega
      have e3 : ((a * 256 + b) * 256 + c) % 256 = c := by omega
      rw [← hl]
      simp [e1, e2, e3]
    · simp at h
  | [], h => simp [frameBody] at h
  | [_], h => simp [frameBody] at h
  | [_, _], h => simp [frameBody] at h

/-! ## The count field -/

theorem putParts_length (cnt : Nat) (more : Bool) :
    (putParts cnt more).length = Varint.encodedLen (cnt * 2 + if more then 1 else 0) := by
  simp [putParts, venc_length]

theorem readParts_putParts (cnt : Nat) (more : Bool) (rest : List Nat) (h : cnt * 2 + 1 < 2 ^ 63) :
    readParts (putParts cnt more ++ rest) = if cnt = 0 ∧ more = true then .error .count else .ok ((cnt, more), rest) := by
  cases more
  · have hr : cnt * 2 + 0 < 2 ^ 63 := by omega
    have := count_venc (cnt * 2 + 0) rest hr
    simp only [putParts, Bool.false_eq_true, ite_false, this, readParts]
    have h1 : (cnt * 2 + 0) / 2 = cnt := by omega
    have h2 : (cnt * 2 + 0) % 2 = 0 := by omega
    simp [h1, h2]
  · have := count_venc (cnt * 2 + 1) rest h
    simp only [putParts, ite_true, this, readParts]
    have h1 : (cnt * 2 + 1) / 2 = cnt := by omega
    have h2 : (cnt * 2 + 1) % 2 = 1 := by omega
    simp [h1, h2]

/-- An empty message that claims more is refused with `Count`. -/
theorem readParts_zero_more (r : List Nat) (r' : List Nat) (h : count r = .ok (1, r')) :
    readParts r = .error .count := by
  simp [readParts, h]

theorem readParts_truncated (r : List Nat) (e : Reason) (h : count r = .error e) :
    readParts r = .error .truncated := by
  simp [readParts, h, count_err r e h]

/-- One encoding per count field: accepted only as the encoding of a pair other than `(0, more)`. -/
theorem readParts_canonical (r : List Nat) (hv : ValidBytes r) (cnt : Nat) (more : Bool) (rest : List Nat)
    (h : readParts r = .ok ((cnt, more), rest)) :
    r = putParts cnt more ++ rest ∧ ¬(cnt = 0 ∧ more = true) := by
  unfold readParts at h
  cases hc : count r with
  | error e => simp [hc] at h
  | ok p =>
    obtain ⟨raw, r2⟩ := p
    simp only [hc] at h
    by_cases hz : raw / 2 = 0 ∧ raw % 2 = 1
    · simp [hz] at h
    · simp only [hz, if_false, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, hm⟩, rfl⟩ := h
      obtain ⟨_, hr⟩ := count_canonical r hv raw r2 hc
      have hraw : raw = raw / 2 * 2 + (if more then 1 else 0) := by
        cases more <;> simp at hm ⊢ <;> omega
      refine ⟨?_, ?_⟩
      · unfold putParts; rw [← hraw]; exact hr
      · rintro ⟨h1, h2⟩; subst h2; apply hz; simp at hm; omega

/-! ## Item lists -/

/-- The items of a list as `Items` reads them: a count, then `venc(len) item` each. -/
def putItems (xs : List Item) : List Nat := venc xs.length ++ (xs.map fun x => venc x.length ++ x).flatten

/-- All items of a list, read as the machine reads them (`Items::read`, then `next_item` until the end). -/
def collect (mx : Nat) : Nat → IS → Except Reason (List Item × List Nat)
  | 0, is => .ok ([], is.r)
  | f + 1, is =>
    match IS.next mx is with
    | .error e => .error e
    | .ok none => .ok ([], is.r)
    | .ok (some (x, is')) =>
      match collect mx f is' with
      | .error e => .error e
      | .ok (xs, r) => .ok (x :: xs, r)

def readItems (mx : Nat) (r : List Nat) : Except Reason (List Item × List Nat) :=
  match IS.read r with
  | .error e => .error e
  | .ok is => collect mx (is.left + 1) is

theorem putItems_length (xs : List Item) :
    (putItems xs).length = Varint.encodedLen xs.length + dataLen xs := by
  simp [putItems, venc_length, dataLen, List.length_flatten, Function.comp_def]

theorem next_end (mx : Nat) (r : List Nat) : IS.next mx ⟨0, r⟩ = .ok none := rfl

theorem next_count_err (mx k : Nat) (r : List Nat) (e : Reason) (h : count r = .error e) :
    IS.next mx ⟨k + 1, r⟩ = .error .truncated := by
  simp [IS.next, h, count_err r e h]

theorem next_item_err (mx k n : Nat) (r r2 : List Nat) (h : count r = .ok (n, r2)) (hn : n > mx) :
    IS.next mx ⟨k + 1, r⟩ = .error .item := by
  simp [IS.next, h, hn]

theorem next_short (mx k n : Nat) (r r2 : List Nat) (h : count r = .ok (n, r2)) (hn : ¬ n > mx)
    (hs : r2.length < n) : IS.next mx ⟨k + 1, r⟩ = .error .truncated := by
  simp [IS.next, h, hn, readBytes_short n r2 hs]

theorem next_ok (mx k : Nat) (x : Item) (rest : List Nat) (hx : x.length ≤ mx) (hv : x.length < 2 ^ 63) :
    IS.next mx ⟨k + 1, venc x.length ++ (x ++ rest)⟩ = .ok (some (x, ⟨k, rest⟩)) := by
  have hc := count_venc x.length (x ++ rest) hv
  have hr := readBytes_ok x.length (x ++ rest) (by simp)
  simp [IS.next, hc, hx, hr, List.take_left', List.drop_left']

theorem collect_putItems (mx : Nat) : ∀ (xs : List Item) (rest : List Nat) (f : Nat),
    (∀ x ∈ xs, x.length ≤ mx ∧ x.length < 2 ^ 63) → f > xs.length →
    collect mx f ⟨xs.length, (xs.map fun x => venc x.length ++ x).flatten ++ rest⟩ = .ok (xs, rest)
  | [], rest, f, _, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp [collect, next_end]
  | x :: xs, rest, f, h, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hx := h x (List.mem_cons_self ..)
    have ih := collect_putItems mx xs rest f' (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by simp at hf; omega)
    have e : ((x :: xs).map fun x => venc x.length ++ x).flatten ++ rest
        = venc x.length ++ (x ++ ((xs.map fun x => venc x.length ++ x).flatten ++ rest)) := by simp
    simp only [List.length_cons, e, collect, next_ok mx xs.length x _ hx.1 hx.2, ih]

theorem readItems_putItems (mx : Nat) (xs : List Item) (rest : List Nat)
    (h : ∀ x ∈ xs, x.length ≤ mx ∧ x.length < 2 ^ 63) (hl : xs.length < 2 ^ 63) :
    readItems mx (putItems xs ++ rest) = .ok (xs, rest) := by
  unfold readItems putItems IS.read
  simp only [List.append_assoc, count_venc _ _ hl]
  exact collect_putItems mx xs rest _ h (by omega)

theorem collect_canonical (mx : Nat) : ∀ (f k : Nat) (r : List Nat), ValidBytes r → f > k →
    ∀ xs rest, collect mx f ⟨k, r⟩ = .ok (xs, rest) →
      xs.length = k ∧ r = (xs.map fun x => venc x.length ++ x).flatten ++ rest ∧ ∀ x ∈ xs, x.length ≤ mx
  | 0, k, r, _, hf, _, _, _ => by omega
  | f + 1, 0, r, _, _, xs, rest, h => by
    simp [collect, next_end] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | f + 1, k + 1, r, hv, hf, xs, rest, h => by
    simp only [collect] at h
    cases hc : count r with
    | error e => rw [next_count_err mx k r e hc] at h; simp at h
    | ok p =>
      obtain ⟨n, r2⟩ := p
      by_cases hn : n > mx
      · rw [next_item_err mx k n r r2 hc hn] at h; simp at h
      · by_cases hs : n ≤ r2.length
        · obtain ⟨hn63, hr⟩ := count_canonical r hv n r2 hc
          have hok : IS.next mx ⟨k + 1, r⟩ = .ok (some (r2.take n, ⟨k, r2.drop n⟩)) := by
            simp [IS.next, hc, hn, readBytes_ok n r2 hs]
          rw [hok] at h
          simp only at h
          cases hs2 : collect mx f ⟨k, r2.drop n⟩ with
          | error e => simp [hs2] at h
          | ok q =>
            obtain ⟨ys, r4⟩ := q
            simp only [hs2, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hv2 : ValidBytes (r2.drop n) := by
              intro y hy; apply hv; rw [hr]
              exact List.mem_append_right _ (List.mem_of_mem_drop hy)
            obtain ⟨c1, c2, c3⟩ := collect_canonical mx f k (r2.drop n) hv2 (by omega) ys r4 hs2
            have hlen : (r2.take n).length = n := by simp; omega
            refine ⟨by simp [c1], ?_, ?_⟩
            · simp only [List.map_cons, List.flatten_cons, hlen]
              rw [hr]
              have : r2 = r2.take n ++ r2.drop n := (List.take_append_drop n r2).symm
              rw [c2] at this
              conv => lhs; rw [this]
              simp
            · intro y hy
              simp only [List.mem_cons] at hy
              rcases hy with rfl | hy
              · omega
              · exact c3 y hy
        · rw [next_short mx k n r r2 hc hn (by omega)] at h; simp at h

theorem readItems_canonical (mx : Nat) (r : List Nat) (hv : ValidBytes r) (xs : List Item) (rest : List Nat)
    (h : readItems mx r = .ok (xs, rest)) : r = putItems xs ++ rest ∧ ∀ x ∈ xs, x.length ≤ mx := by
  unfold readItems IS.read at h
  cases hc : count r with
  | error e => simp [hc] at h
  | ok p =>
    obtain ⟨n, r2⟩ := p
    simp only [hc] at h
    obtain ⟨hn63, hr⟩ := count_canonical r hv n r2 hc
    have hv2 : ValidBytes r2 := by
      intro y hy; apply hv; rw [hr]; exact List.mem_append_right _ hy
    obtain ⟨c1, c2, c3⟩ := collect_canonical mx (n + 1) n r2 hv2 (by omega) xs rest h
    refine ⟨?_, c3⟩
    unfold putItems
    rw [hr, c2, ← c1]; simp

/-! ## Sizes -/

theorem encodedLen_mono : ∀ (b a : Nat), a ≤ b → Varint.encodedLen a ≤ Varint.encodedLen b
  | b, a, h => by
    by_cases hb : b < 128
    · rw [Varint.encodedLen_lt b hb, Varint.encodedLen_lt a (by omega)]; exact Nat.le_refl _
    · by_cases ha : a < 128
      · rw [Varint.encodedLen_lt a ha]; exact Varint.encodedLen_pos b
      · rw [Varint.encodedLen_ge b (by omega), Varint.encodedLen_ge a (by omega)]
        have := encodedLen_mono (b / 128) (a / 128) (Nat.div_le_div_right h)
        omega
termination_by b => b
decreasing_by omega

/-- An encoded bound is at most `boundLen` of the bound, the size the machine budgets. -/
theorem putBound_length_le (last b : Item) : (putBound last b).1.length ≤ boundLen b.length := by
  rw [putBound_length]; unfold boundLen
  have := encodedLen_mono b.length (b.length - min (cpl last b) cplMax) (by omega)
  omega

/-- A head is at most the tag and the two bounds the machine budgets; with an infinite upper bound, one bound. -/
theorem putHead_length_le (last : Item) (kind : Nat) (lo : Item) (hi : Option Item) :
    (putHead last kind lo hi).1.length ≤ 1 + boundLen lo.length + (match hi with | none => 0 | some h => boundLen h.length) := by
  cases hi with
  | none => simp [putHead]; have := putBound_length_le last lo; omega
  | some h =>
    simp [putHead, putBound_snd]
    have := putBound_length_le last lo
    have := putBound_length_le lo h
    omega

theorem putHead_length (last : Item) (kind : Nat) (lo : Item) (hi : Option Item) :
    (putHead last kind lo hi).1.length = 1 + (putBound last lo).1.length
      + (match hi with | none => 0 | some h => (putBound lo h).1.length) := by
  cases hi <;> simp [putHead, putBound_snd] <;> omega

#audit_axioms Vinc.Reconcile.count_venc
#audit_axioms Vinc.Reconcile.count_canonical
#audit_axioms Vinc.Reconcile.readBound_putBound
#audit_axioms Vinc.Reconcile.readBound_canonical
#audit_axioms Vinc.Reconcile.readBound_err_reason
#audit_axioms Vinc.Reconcile.readHead_putHead
#audit_axioms Vinc.Reconcile.readHead_canonical
#audit_axioms Vinc.Reconcile.readBounds_putBounds
#audit_axioms Vinc.Reconcile.readBounds_canonical
#audit_axioms Vinc.Reconcile.frameBody_frameHeader
#audit_axioms Vinc.Reconcile.frameBody_canonical
#audit_axioms Vinc.Reconcile.readParts_putParts
#audit_axioms Vinc.Reconcile.readParts_canonical
#audit_axioms Vinc.Reconcile.readItems_putItems
#audit_axioms Vinc.Reconcile.readItems_canonical
#audit_axioms Vinc.Reconcile.putBound_length_le
#audit_axioms Vinc.Reconcile.putItems_length

end Vinc.Reconcile
