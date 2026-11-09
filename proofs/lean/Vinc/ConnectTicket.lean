import Vinc.ConnectSigned

/-!
# Tickets and the punch candidate list

`Ticket::parse` and `Ticket::encode` of `ticket.rs`, and `punch::encode` and `punch::decode` of `client/punch.rs`.

A ticket is `version(1) flags(1) node(33) [home(33)] addrs`: the version is 1, bit 0 of the flags says a home relay
follows, bits 1 to 3 hold the address count (0 to 4), bits 4 to 7 are zero. The candidate list of a REACH_OUT is
`n(1)` and `n` addresses, `n` at most 8.
-/

namespace Vinc.ConnCodec
open Vinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

/-- A ticket: the node, an optional home relay and up to four address hints. -/
structure Tk where
  node : List Nat
  home : Option (List Nat)
  addrs : List (List Nat)
  deriving DecidableEq, Repr

/-- The flags byte of a ticket. -/
def Tk.flags (t : Tk) : Nat := (if t.home.isSome then 1 else 0) + 2 * t.addrs.length

/-- The optional home relay. -/
def Tk.homeBytes (t : Tk) : List Nat := t.home.getD []

/-- `Ticket::encode` bytes. -/
def Tk.bytes (t : Tk) : List Nat := [1, t.flags] ++ t.node ++ t.homeBytes ++ t.addrs.flatten

/-- The steps of `Ticket::encode`. -/
def Tk.ops (t : Tk) : List Op :=
  [.put [1], .put [t.flags], .put t.node] ++ (match t.home with | some h => [.put h] | none => []) ++
    t.addrs.map Op.put

/-- `Ticket::encode` into a buffer of `cap` bytes. -/
def Tk.encode (cap : Nat) (t : Tk) : Except CErr (List Nat) := run CErr.wire cap t.ops []

/-- The home relay of a ticket, read when the flag says so. -/
def rdHome (fl : Nat) (r : List Nat) : Except CErr (Option (List Nat) × List Nat) :=
  if fl % 2 = 1 then do
    let (h, r1) ← liftW CErr.wire (rdNode r)
    pure (some h, r1)
  else pure (none, r)

/-- `Ticket::parse`. -/
def Tk.parse (b : List Nat) : Except CErr Tk := do
  let (v, r) ← liftW CErr.wire (rdU8 b)
  chkE (v = 1) (CErr.version v)
  let (fl, r) ← liftW CErr.wire (rdU8 r)
  chkE (fl / 16 = 0 ∧ fl / 2 % 8 ≤ 4) (CErr.flags fl)
  let (node, r) ← liftW CErr.wire (rdNode r)
  let (home, r) ← rdHome fl r
  let (addrs, r) ← rdAddrs 2 (fl / 2 % 8) r
  chkE (r = []) (CErr.wire (.unexpected "trailing bytes"))
  pure ⟨node, home, addrs⟩

/-- A ticket the code can hold. -/
def Tk.valid (t : Tk) : Prop :=
  NodeOk t.node ∧ Byte t.node ∧ (∀ h, t.home = some h → NodeOk h ∧ Byte h) ∧ t.addrs.length ≤ 4 ∧
    ∀ a ∈ t.addrs, AddrOk a ∧ Byte a

theorem Tk.flags_lt (t : Tk) (h : t.addrs.length ≤ 4) : t.flags / 16 = 0 ∧ t.flags / 2 % 8 = t.addrs.length ∧
    t.flags % 2 = (if t.home.isSome then 1 else 0) ∧ t.flags < 256 := by
  unfold Tk.flags
  cases t.home.isSome <;> simp <;> omega

theorem Tk.parse_bytes (t : Tk) (hv : t.valid) : Tk.parse t.bytes = .ok t := by
  obtain ⟨hn, hbn, hhm, hna, hal⟩ := hv
  obtain ⟨node, home, addrs⟩ := t
  simp only at *
  obtain ⟨f1, f2, f3, f4⟩ := Tk.flags_lt ⟨node, home, addrs⟩ hna
  simp only at f1 f2 f3 f4
  have e2 := rdNode_app node (home.getD [] ++ addrs.flatten) hn
  have e5 := rdAddrs_app 2 addrs (fun a ha => (hal a ha).1) []
  have hh : rdHome (Tk.flags ⟨node, home, addrs⟩) (home.getD [] ++ addrs.flatten) = .ok (home, addrs.flatten) := by
    cases home with
    | none =>
      simp [rdHome, f3, pure, Except.pure]
    | some h =>
      obtain ⟨hh1, hh2⟩ := hhm h rfl
      simp [rdHome, f3, rdNode_app h _ hh1, liftW, bind, Except.bind, pure, Except.pure]
  have hc : Tk.flags ⟨node, home, addrs⟩ / 2 % 8 = addrs.length := f2
  simp only [Tk.bytes, Tk.homeBytes, List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at e2 e5 hh ⊢
  have hfl : Tk.flags ⟨node, home, addrs⟩ / 16 = 0 ∧ addrs.length ≤ 4 := ⟨f1, hna⟩
  simp [Tk.parse, rdU8, liftW, e2, hh, hc, e5, f1, hna, chkE, bind, Except.bind, pure, Except.pure]

theorem rdHome_inv {fl r home r'} (h : rdHome fl r = .ok (home, r')) (hb : Byte r) :
    (fl % 2 = 1 ∧ ∃ x, home = some x ∧ NodeOk x ∧ Byte x ∧ r = x ++ r') ∨ (fl % 2 ≠ 1 ∧ home = none ∧ r' = r) := by
  unfold rdHome at h
  by_cases h1 : fl % 2 = 1
  · rw [if_pos h1] at h
    simp only [bind_ok, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨x, r1⟩, h2, rfl, rfl⟩ := h
    obtain ⟨hx, e⟩ := rdNode_ok (liftW_eq_ok h2)
    subst e
    exact Or.inl ⟨h1, x, rfl, hx, (byte_append hb).1, rfl⟩
  · rw [if_neg h1] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨h1, rfl, rfl⟩

theorem Tk.parse_inv {b t} (h : Tk.parse b = .ok t) (hb : Byte b) : t.valid ∧ t.bytes = b := by
  unfold Tk.parse at h
  simp only [bind_ok] at h
  obtain ⟨⟨v, b1⟩, h1, u1, hu1, ⟨fl, b2⟩, h2, u2, hu2, ⟨node, b3⟩, h3, ⟨home, b4⟩, h4, ⟨addrs, b5⟩, h5, u3, hu3, h⟩ := h
  have hv := chkE_ok hu1
  have hf := chkE_ok hu2
  have hnil := chkE_ok hu3
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have e1 := rdU8_ok (liftW_eq_ok h1)
  have e2 := rdU8_ok (liftW_eq_ok h2)
  obtain ⟨hnode, e3⟩ := rdNode_ok (liftW_eq_ok h3)
  simp only at hv hnil hf
  subst hv hnil
  subst e1 e2 e3
  obtain ⟨_, hb1⟩ := byte_cons hb
  obtain ⟨_, hb2⟩ := byte_cons hb1
  obtain ⟨hbn, hb3⟩ := byte_append hb2
  obtain ⟨hlen, hal, e5⟩ := rdAddrs_inv 2 _ h5
  simp only [List.append_nil] at e5
  have hrd := rdHome_inv h4 hb3
  have hl4 : addrs.length ≤ 4 := by rw [hlen]; exact hf.2
  rcases hrd with ⟨hm, x, rfl, hx, hbx, e4⟩ | ⟨hm, rfl, e4⟩
  · subst e4 e5
    obtain ⟨_, hb4⟩ := byte_append hb3
    refine ⟨⟨hnode, hbn, ?_, hl4, fun a ha => ⟨hal a ha, addrs_byte hb4 a ha⟩⟩, ?_⟩
    · intro h hh; cases hh; exact ⟨hx, hbx⟩
    · simp [Tk.bytes, Tk.homeBytes, Tk.flags, hlen]
      omega
  · subst e4 e5
    refine ⟨⟨hnode, hbn, ?_, hl4, fun a ha => ⟨hal a ha, addrs_byte hb3 a ha⟩⟩, ?_⟩
    · intro h hh; cases hh
    · simp [Tk.bytes, Tk.homeBytes, Tk.flags, hlen]
      omega

theorem Tk.parse_injective {a b t} (ha : Tk.parse a = .ok t) (hb : Tk.parse b = .ok t) (hba : Byte a)
    (hbb : Byte b) : a = b := by
  rw [← (Tk.parse_inv ha hba).2, ← (Tk.parse_inv hb hbb).2]

theorem Tk.ops_good (t : Tk) (hv : t.valid) : (∀ o ∈ t.ops, o.good) ∧ opsBytes t.ops = t.bytes := by
  refine ⟨?_, ?_⟩
  · intro o ho
    simp only [Tk.ops, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ho
    rcases ho with (ho | ho) | ⟨a, _, rfl⟩
    · rcases ho with rfl | rfl | rfl <;> simp [Op.good]
    · cases hh : t.home with
      | none => simp [hh] at ho
      | some h => simp [hh] at ho; subst ho; simp [Op.good]
    · simp [Op.good]
  · cases hh : t.home <;> simp [opsBytes, Tk.ops, Tk.bytes, Tk.homeBytes, hh, List.flatMap_append, flatMap_put,
      Op.bytes]

theorem Tk.encode_ok (cap : Nat) (t : Tk) (hv : t.valid) (hc : t.bytes.length ≤ cap) :
    t.encode cap = .ok t.bytes := by
  obtain ⟨g, b⟩ := Tk.ops_good t hv
  have := run_ok CErr.wire cap t.ops g [] (by rw [b]; simpa using hc)
  simpa [Tk.encode, b] using this

theorem Tk.encode_short (cap : Nat) (t : Tk) (hv : t.valid) (hc : cap < t.bytes.length) :
    ∃ k, 0 < k ∧ t.encode cap = .error (CErr.wire (.small k)) := by
  obtain ⟨g, b⟩ := Tk.ops_good t hv
  exact run_short CErr.wire cap t.ops g [] (by simp) (by rw [b]; simpa using hc)

/-! ## The refusals of a ticket -/

theorem Tk.parse_empty : Tk.parse [] = .error (.wire (.trunc 1)) := by
  simp [Tk.parse, rdU8, liftW, bind, Except.bind]

theorem Tk.parse_version (v : Nat) (r : List Nat) (h : v ≠ 1) : Tk.parse (v :: r) = .error (.version v) := by
  simp [Tk.parse, rdU8, liftW, chkE_false _ h, bind, Except.bind]

theorem Tk.parse_flags (fl : Nat) (r : List Nat) (h : ¬ (fl / 16 = 0 ∧ fl / 2 % 8 ≤ 4)) :
    Tk.parse (1 :: fl :: r) = .error (.flags fl) := by
  have h' : ¬ (fl < 16 ∧ fl / 2 % 8 ≤ 4) := by omega
  simp [Tk.parse, rdU8, liftW, chkE_true, chkE_false _ h', bind, Except.bind]

/-- Bytes after the last address are refused. -/
theorem Tk.parse_trailing (t : Tk) (hv : t.valid) (x : Nat) (r : List Nat) :
    Tk.parse (t.bytes ++ x :: r) = .error (.wire (.unexpected "trailing bytes")) := by
  obtain ⟨hn, hbn, hhm, hna, hal⟩ := hv
  obtain ⟨node, home, addrs⟩ := t
  simp only at *
  obtain ⟨f1, f2, f3, f4⟩ := Tk.flags_lt ⟨node, home, addrs⟩ hna
  simp only at f1 f2 f3 f4
  have e2 := rdNode_app node (home.getD [] ++ addrs.flatten ++ x :: r) hn
  have e5 := rdAddrs_app 2 addrs (fun a ha => (hal a ha).1) (x :: r)
  have hh : rdHome (Tk.flags ⟨node, home, addrs⟩) (home.getD [] ++ (addrs.flatten ++ x :: r)) =
      .ok (home, addrs.flatten ++ x :: r) := by
    cases home with
    | none => simp [rdHome, f3, pure, Except.pure]
    | some h =>
      obtain ⟨hh1, hh2⟩ := hhm h rfl
      simp [rdHome, f3, rdNode_app h _ hh1, liftW, bind, Except.bind, pure, Except.pure]
  have hc : Tk.flags ⟨node, home, addrs⟩ / 2 % 8 = addrs.length := f2
  have hne : ¬ (x :: r = []) := by simp
  simp only [Tk.bytes, Tk.homeBytes, List.append_assoc, List.cons_append, List.nil_append] at e2 hh ⊢
  simp [Tk.parse, rdU8, liftW, e2, hh, hc, e5, f1, hna, chkE_false _ hne, chkE, bind, Except.bind]

/-! ## The candidate list of a REACH_OUT -/

/-- `punch::decode`: the addresses, or `none` for a malformed body. -/
def rdCands (b : List Nat) : Option (List (List Nat)) :=
  match rdU8 b with
  | .error _ => none
  | .ok (n, r) =>
    if 8 < n then none
    else match rdAddrs 0 n r with
    | .error _ => none
    | .ok (as, r') => if r' = [] then some as else none

/-- `punch::encode` of the first eight candidates (`none` when `out` is too small is the buffer's shortfall). -/
def encCands (cs : List (List Nat)) : List Nat :=
  let cs := cs.take 8
  cs.length :: cs.flatten

theorem rdCands_enc (cs : List (List Nat)) (h : ∀ a ∈ cs, AddrOk a ∧ Byte a) (hn : cs.length ≤ 8) :
    rdCands (encCands cs) = some cs := by
  have hc : cs.take 8 = cs := List.take_of_length_le hn
  have e5 := rdAddrs_app 0 cs (fun a ha => (h a ha).1) []
  simp only [List.append_nil] at e5
  have hn' : ¬ (8 < cs.length) := by omega
  simp [rdCands, encCands, hc, rdU8, hn', e5]

theorem rdCands_inv {b cs} (h : rdCands b = some cs) : cs.length ≤ 8 ∧ (∀ a ∈ cs, AddrOk a) ∧ b = cs.length :: cs.flatten := by
  unfold rdCands at h
  rcases hb : rdU8 b with _ | ⟨n, r⟩
  · simp [hb] at h
  · simp only [hb] at h
    by_cases hn : 8 < n
    · simp [hn] at h
    · simp only [hn, if_false] at h
      rcases hr : rdAddrs 0 n r with _ | ⟨as, r'⟩
      · simp [hr] at h
      · simp only [hr] at h
        by_cases hr' : r' = []
        · simp only [hr', if_true, Option.some.injEq] at h
          subst h hr'
          obtain ⟨hl, ha, e⟩ := rdAddrs_inv 0 n hr
          have eb := rdU8_ok hb
          simp only [List.append_nil] at e
          subst e
          exact ⟨by omega, ha, by rw [eb, hl]⟩
        · simp [hr'] at h

end Vinc.ConnCodec
