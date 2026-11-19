import Pinc.KeyRollSys

namespace Pinc.KeyRollSys
open Pinc.KeyRoll

/-! ## Helpers on terms and the machine -/

theorem rollAll_snoc (s : T) (l : List T) (d : T) : rollAll s (l ++ [d]) = .roll (rollAll s l) d := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => simp [rollAll, ih]

theorem depth_rollAll (b : Nat) (l : List T) : (rollAll (.base b) l).depth = l.length := by
  suffices h : ∀ (s : T) (l : List T), (rollAll s l).depth = s.depth + l.length by simpa [T.depth] using h (.base b) l
  intro s l
  induction l generalizing s with
  | nil => simp [rollAll]
  | cons x l ih => simp [rollAll, ih, T.depth]; omega

theorem rollAll_inj_aux : ∀ (l l' : List T) (s s' : T), l.length = l'.length → rollAll s l = rollAll s' l' →
    s = s' ∧ l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' s s' hl h
    cases l' with
    | nil => simpa [rollAll] using h
    | cons _ _ => simp at hl
  | cons x l ih =>
    intro l' s s' hl h
    cases l' with
    | nil => simp at hl
    | cons y l' =>
      simp only [rollAll] at h
      obtain ⟨h1, h2⟩ := ih l' _ _ (by simpa using hl) h
      injection h1 with e1 e2
      exact ⟨e1, by rw [e2, h2]⟩

theorem rollAll_base_inj (b b' : Nat) (l l' : List T) (h : rollAll (.base b) l = rollAll (.base b') l') :
    b = b' ∧ l = l' := by
  have hlen : l.length = l'.length := by
    have := congrArg T.depth h
    rwa [depth_rollAll, depth_rollAll] at this
  obtain ⟨h1, h2⟩ := rollAll_inj_aux l l' _ _ hlen h
  injection h1 with e
  exact ⟨e, h2⟩

/-! ## The machine, case by case -/

/-- The roll after it answered a request. -/
def _root_.Pinc.KeyRoll.Roll.answeredWith (r : Roll) (sh : T) (ans : Msg) : Roll :=
  { r with st := .idle, last := some (sh, ans), rolls := Record.inc r.rolls }

/-- The roll after it took the answer to its request. -/
def _root_.Pinc.KeyRoll.Roll.completed (r : Roll) : Roll := { r with st := .idle, last := none, rolls := Record.inc r.rolls }

/-- The answer a node `me` with counter `c` and next number `spn` gives to a request with share `sh` of atom `b`. -/
def answerTo (me : Bool) (c spn : Nat) (sh : T) (b : Atom) : Msg :=
  ⟨true, .pub (atomOf me c), spn, .id sh, .bound (.id sh) (Dh (atomOf me c) b)⟩

theorem isIdle_st (r : Roll) : r.isIdle = true ↔ r.st = .idle := by
  unfold Roll.isIdle; cases r.st <;> simp

theorem onRequest_fresh (r : Roll) (req : Msg) (spn : Nat) (a b : Atom) (hk : req.answer = false)
    (hn : r.isDup req = false) (hc : (!r.isIdle && r.dialer) = false) (hsh : req.share = .pub b) :
    r.onRequest req spn (some a) =
      (r.answeredWith req.share ⟨true, .pub a, spn, .id req.share, .bound (.id req.share) (Dh a b)⟩,
       .ok (⟨true, .pub a, spn, .id req.share, .bound (.id req.share) (Dh a b)⟩,
         some (.bound (.id req.share) (Dh a b)))) := by
  by_cases hi : r.isIdle = true
  · have := (isIdle_st r).1 hi
    simp [Roll.onRequest, Roll.answeredWith, hk, hn, hc, hsh, dhOf, hi, this]
  · have hi' : r.isIdle = false := by simpa using hi
    have hd : r.dialer = false := by simpa [hi'] using hc
    simp [Roll.onRequest, Roll.answeredWith, hk, hn, hsh, dhOf, hi', hd]

theorem onRequest_busy (r : Roll) (req : Msg) (spn : Nat) (fresh : Option Atom) (hk : req.answer = false)
    (hn : r.isDup req = false) (hc : (!r.isIdle && r.dialer) = true) :
    r.onRequest req spn fresh = (r, .error .unexpected) := by
  simp [Roll.onRequest, hk, hn, hc]

theorem onAnswer_refused (r : Roll) (a : Msg) (e : Fail) (h : (r.onAnswer a).2 = .error e) : (r.onAnswer a).1 = r := by
  unfold Roll.onAnswer at h ⊢
  by_cases ha : a.answer = true
  · cases hs : r.st with
    | idle => simp [ha, hs]
    | req seed m =>
      by_cases he : a.to = .id m.share
      · cases hd : dhOf seed a.share with
        | none => simp [ha, hs, hd, he]
        | some dh => simp [ha, hs, hd, he] at h
      · simp [ha, hs, he]
  · simp [ha]

theorem onAnswer_ok_st (r : Roll) (a : Msg) (c : T × Nat) (h : (r.onAnswer a).2 = .ok c) :
    ∃ seed m b, r.st = .req seed m ∧ a.answer = true ∧ a.share = .pub b ∧ a.to = .id m.share ∧
      c = (.bound (.id m.share) (Dh seed b), a.spn) := by
  unfold Roll.onAnswer at h
  by_cases ha : a.answer = true
  · cases hs : r.st with
    | idle => simp [ha, hs] at h
    | req seed m =>
      by_cases he : a.to = .id m.share
      · cases hsh : a.share with
        | pub b => simp [ha, hs, hsh, dhOf, he] at h; exact ⟨seed, m, b, rfl, ha, rfl, he, h.symm⟩
        | _ => simp [ha, hs, hsh, dhOf, he] at h
      · simp [ha, hs, he] at h
  · simp [ha] at h

/-- Whatever `onRequest` does to a request that is not an answer, it does one of these three things. -/
theorem onRequest_split (r : Roll) (req : Msg) (hk : req.answer = false) :
    r.isDup req = true ∨ (r.isDup req = false ∧ (!r.isIdle && r.dialer) = true) ∨
      (r.isDup req = false ∧ (!r.isIdle && r.dialer) = false) := by
  by_cases h1 : r.isDup req = true
  · exact Or.inl h1
  · have h1' : r.isDup req = false := by simpa using h1
    by_cases h2 : (!r.isIdle && r.dialer) = true
    · exact Or.inr (Or.inl ⟨h1', h2⟩)
    · exact Or.inr (Or.inr ⟨h1', by simpa using h2⟩)

theorem isDup_last (r : Roll) (req : Msg) (h : r.isDup req = true) :
    ∃ ans, r.last = some (req.share, ans) := by
  unfold Roll.isDup at h
  cases hl : r.last with
  | none => simp [hl] at h
  | some x => obtain ⟨sh, ans⟩ := x; simp [hl] at h; exact ⟨ans, by simp [h]⟩

theorem isDup_iff (r : Roll) (req : Msg) :
    r.isDup req = true ↔ ∃ ans, r.last = some (req.share, ans) := by
  constructor
  · exact isDup_last r req
  · rintro ⟨ans, h⟩; simp [Roll.isDup, h]

theorem start_spec (r : Roll) (a : Atom) (h : r.isIdle = true) :
    (r.start (some a)).1 = { r with st := .req a (Msg.req (.pub a)) } ∧ (r.start (some a)).2 = .ok (Msg.req (.pub a)) :=
  ⟨by simp [Roll.start, h], by simp [Roll.start, h]⟩

/-! ## `rekeyRx`, case by case -/

theorem isDupMsg_req (s : Node) (m : Msg) (hm : m.answer = false) : isDupMsg s m = s.roll.isDup m := by
  simp [isDupMsg, hm]

theorem gated_nodup (P : Params) (s : Node) (m : Msg) (hm : m.answer = false) (hn : s.roll.isDup m = false)
    (hg : gated s m = false) : s.nxt = none := by
  simp only [gated, isDupMsg_req s m hm, hn] at hg
  cases h : s.nxt <;> simp_all

theorem rekeyRx_consume (s : Node) (m : Msg) (me : Bool) (lvl : Nat) (seed : Atom) (rq : Msg) (b : Atom)
    (hm : m.answer = true) (hst : s.roll.st = .req seed rq) (hsh : m.share = .pub b) (he : m.to = .id rq.share) :
    rekeyRx s m me lvl =
      ⟨s.consumed s.roll.completed (.bound (.id rq.share) (Dh seed b)) m.spn rq.share,
       some ⟨me, .bound (.id rq.share) (Dh seed b), m.gdh, m.to, rq.share⟩, none⟩ := by
  have h1 := onAnswer_ok s.roll m seed rq b hm hst hsh he
  have h2 : s.roll.pending = some rq := by simp [Roll.pending, hst]
  simp [rekeyRx, hm, h1, h2, Roll.completed]

theorem rekeyRx_answer_refused (s : Node) (m : Msg) (me : Bool) (lvl : Nat) (hm : m.answer = true)
    (h : ∀ c, (s.roll.onAnswer m).2 ≠ .ok c) : rekeyRx s m me lvl = ⟨s, none, none⟩ := by
  cases h2 : (s.roll.onAnswer m).2 with
  | ok c => exact absurd h2 (h c)
  | error e =>
    have h3 := onAnswer_refused s.roll m e h2
    unfold rekeyRx
    rw [if_pos hm]
    generalize hh : s.roll.onAnswer m = oa at h2 h3 ⊢
    obtain ⟨r, res⟩ := oa
    simp only at h2 h3
    subst h2
    cases hp : s.roll.pending <;> simp [h3]

theorem rekeyRx_gated (s : Node) (m : Msg) (me : Bool) (lvl : Nat) (hm : m.answer = false)
    (hg : gated s m = true) : rekeyRx s m me lvl = ⟨s, none, none⟩ := by
  simp [rekeyRx, hm, hg]

theorem rekeyRx_dup (s : Node) (m : Msg) (me : Bool) (lvl : Nat) (hm : m.answer = false)
    (hg : gated s m = false) (ans : Msg) (hl : s.roll.last = some (m.share, ans)) :
    rekeyRx s m me lvl = ⟨{ s with out := some ans }, none, none⟩ := by
  have hd : s.roll.isDup m = true := (isDup_iff _ _).2 ⟨ans, hl⟩
  have := onRequest_dup s.roll m s.npn (some (atomOf me s.ctr)) m.share ans hl rfl hm
  simp [rekeyRx, hm, hg, this]

theorem rekeyRx_busy (s : Node) (m : Msg) (me : Bool) (lvl : Nat) (hm : m.answer = false)
    (hg : gated s m = false) (hn : s.roll.isDup m = false) (hc : (!s.roll.isIdle && s.roll.dialer) = true) :
    rekeyRx s m me lvl = ⟨s, none, none⟩ := by
  have := onRequest_busy s.roll m s.npn (some (atomOf me s.ctr)) hm hn hc
  simp [rekeyRx, hm, hg, this]

theorem rekeyRx_stage (s : Node) (m : Msg) (me : Bool) (lvl : Nat) (b : Atom) (hm : m.answer = false)
    (hg : gated s m = false) (hn : s.roll.isDup m = false) (hc : (!s.roll.isIdle && s.roll.dialer) = false)
    (hsh : m.share = .pub b) :
    rekeyRx s m me lvl =
      ⟨s.staged (s.roll.answeredWith m.share (answerTo me s.ctr s.npn m.share b)) (answerTo me s.ctr s.npn m.share b)
          (.bound (.id m.share) (Dh (atomOf me s.ctr) b)) m.share lvl,
       none, some ⟨me, answerTo me s.ctr s.npn m.share b, s.ders.length⟩⟩ := by
  have := onRequest_fresh s.roll m s.npn (atomOf me s.ctr) b hm hn hc hsh
  simp [rekeyRx, hm, hg, this, answerTo]

end Pinc.KeyRollSys
