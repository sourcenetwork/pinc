import Vinc.DtnScenarioSum

/-!
# The copy account of a scenario

`SysInv` holds in every reachable system: the ids are distinct, every forwarder is `FwdOk`, no fresh bundle message
carries copies to the destination (the copies of a delivery are 0) and, while no retransmitted hold was accepted
after the bundle finished (`replayed`, the finding of `DtnForwardWitness`), the copies held by all nodes plus those
in flight plus those dropped plus those released equal the budget of the bundle:

  `held + in flight + dropped + released = copies`.

Nothing is lost and nothing is created, whatever the network does (a lost message is counted as dropped, a refused
hold as dropped, a release or a forget as released) and whatever the contacts do. `held_le_budget` is the statement
under loss that no node set ever holds more than the budget.
-/

namespace Vinc.DtnScenario

theorem fwd_set {c : Cfg} {t : Nat} {s : Sys} (hf : ∀ m ∈ s.cfg.ids, FwdOk c t (s.nodes m).f) (n : Nat) (x : Node)
    (hx : FwdOk c t x.f) : ∀ m ∈ s.cfg.ids, FwdOk c t ((s.set n x).nodes m).f := by
  intro m hm
  by_cases hmn : m = n
  · subst hmn; rw [set_nodes_self]; exact hx
  · rw [set_nodes_same _ _ _ _ hmn]; exact hf m hm

theorem fwd_mono {c : Cfg} {t t' : Nat} (ht : t ≤ t') {f : DtnForward.F} (h : FwdOk c t f) : FwdOk c t' f :=
  ⟨h.uniq, h.live, h.bok, Nat.le_trans h.now ht⟩

/-- No fresh bundle message carries copies to the destination. -/
def MsgOk (d : Nat) (l : List Msg) : Prop :=
  ∀ m ∈ l, ∀ id fr to c, m = .bun id fr to c true → to = d → c = 0

/-- The invariant of a system. -/
structure SysInv (s : Sys) : Prop where
  nodup : s.cfg.ids.Nodup
  fwd : ∀ m ∈ s.cfg.ids, FwdOk s.cfg s.t (s.nodes m).f
  msgOk : MsgOk s.cfg.dest s.msgs
  acct : s.replayed = false → s.heldAll + s.inflight + s.dropped + s.released = s.cfg.copies

theorem msgOk_cons {d : Nat} {l : List Msg} (hm : MsgOk d l) (new : Msg)
    (hn : ∀ id fr to c, new = .bun id fr to c true → to = d → c = 0) : MsgOk d (new :: l) := by
  intro m hmem id fr to c h
  rcases List.mem_cons.1 hmem with rfl | hm'
  · exact hn id fr to c h
  · exact hm m hm' id fr to c h

theorem msgOk_erase {d : Nat} {l : List Msg} (hm : MsgOk d l) (x : Msg) : MsgOk d (l.erase x) :=
  fun m hmem => hm m (List.mem_of_mem_erase hmem)

/-! ### The initial system -/

theorem node_empty_fwd (c : Cfg) (n : Nat) : FwdOk c 0 (Node.empty c n).f := by
  have hF : (Node.empty c n).f = DtnForward.F.new c.retry c.maxSends 0 c.fb c.fl c.ft := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hF]; exact DtnForward.uniq_new _
  · intro i t ht
    rw [hF] at ht
    have : DtnForward.slot (DtnForward.F.new c.retry c.maxSends 0 c.fb c.fl c.ft).ts i = none :=
      DtnForward.slot_replicate_none _ _
    rw [this] at ht; cases ht
  · rw [hF]; exact allB_replicate _ _
  · rw [hF]; exact Nat.le_refl _

theorem sum_ite_src (k src : Nat) : ∀ (ids : List Nat), ids.Nodup → src ∈ ids →
    (ids.map fun m => if m = src then k else 0).sum = k
  | [], _, h => by simp at h
  | a :: r, hn, h => by
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.sum_cons]
    by_cases ha : a = src
    · subst ha
      have : (r.map fun m => if m = a then k else 0).sum = 0 := by
        have hz : ∀ l : List Nat, (∀ m ∈ l, m ≠ a) → (l.map fun m => if m = a then k else 0).sum = 0 := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons y t ih =>
            intro h
            simp only [List.map_cons, List.sum_cons, if_neg (h y (List.mem_cons_self))]
            rw [ih (fun m hm => h m (List.mem_cons_of_mem _ hm))]
        exact hz r (fun m hm e => hn.1 (e ▸ hm))
      simp [this]
    · have hm : src ∈ r := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm ha
        · exact e
      simp [ha, sum_ite_src k src r hn.2 hm]

theorem origin_step (c : Cfg) (hhold : (originHold c).2 = .ok) :
    DtnForward.step (Node.empty c c.src).f 0 (.hold bid c.dest c.exp c.copies) = ((originHold c).1, .ok) := by
  unfold originHold at hhold ⊢
  exact Prod.ext rfl hhold

theorem inv_init (c : Cfg) (hn : c.ids.Nodup) (hsrc : c.src ∈ c.ids) (hhold : (originHold c).2 = .ok) :
    SysInv (Sys.init c) := by
  have hs := origin_step c hhold
  have hok : FwdOk c 0 (originHold c).1 :=
    fwdOk_step (Nat.le_refl 0) hs (node_empty_fwd c c.src) (fun id d ex c' h => by
      simp only [DtnForward.Input.hold.injEq] at h; exact ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm⟩)
  have hheld : DtnForward.heldSum (originHold c).1 bid = c.copies := by
    have := held_hold_ok hs
    have h0 : DtnForward.heldSum (Node.empty c c.src).f bid = 0 := by
      unfold DtnForward.heldSum
      exact DtnForward.wsum_replicate_none _ _
    omega
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro m hm
    by_cases hms : m = c.src
    · subst hms; simpa [Sys.init] using hok
    · simpa [Sys.init, hms] using node_empty_fwd c m
  · intro m hm; simp [Sys.init] at hm
  · intro _
    have : (Sys.init c).heldAll = c.copies := by
      unfold Sys.heldAll
      show (c.ids.map fun m => DtnForward.heldSum ((Sys.init c).nodes m).f bid).sum = _
      have : (c.ids.map fun m => DtnForward.heldSum ((Sys.init c).nodes m).f bid) =
          c.ids.map fun m => if m = c.src then c.copies else 0 := by
        apply List.map_congr_left
        intro m _
        by_cases hms : m = c.src
        · subst hms; simpa [Sys.init] using hheld
        · simp only [Sys.init, hms, ite_false, Node.empty]
          unfold DtnForward.heldSum
          exact DtnForward.wsum_replicate_none _ _
      rw [this]
      exact sum_ite_src c.copies c.src c.ids hn hsrc
    show (Sys.init c).heldAll + (Sys.init c).inflight + 0 + 0 = c.copies
    have h0 : (Sys.init c).inflight = 0 := rfl
    omega

/-! ### One event -/

theorem fwd_step {c : Cfg} {t t' : Nat} (ht : t ≤ t') {f : DtnForward.F} (h : FwdOk c t f) (inp : DtnForward.Input)
    (hh : ∀ id d ex c', inp = .hold id d ex c' → id = bid ∧ ex = c.exp ∧ d = c.dest) :
    FwdOk c t' (DtnForward.step f t' inp).1 :=
  fwdOk_step ht (f' := (DtnForward.step f t' inp).1) (er := (DtnForward.step f t' inp).2) rfl h hh

theorem fwd_poll {c : Cfg} {t : Nat} {f : DtnForward.F} (h : FwdOk c t f) : FwdOk c t (DtnForward.poll f).1 :=
  fwdOk_poll (f' := (DtnForward.poll f).1) (a := (DtnForward.poll f).2) rfl h

theorem link_no_hold (up : Bool) (b : Nat) (id d ex c : Nat) : (if up then DtnForward.Input.linkUp b else .linkDown b) ≠ .hold id d ex c := by
  cases up <;> simp

theorem link_no_forget (up : Bool) (b : Nat) (id : Nat) : (if up then DtnForward.Input.linkUp b else .linkDown b) ≠ .forget id := by
  cases up <;> simp

theorem inv_contact {s : Sys} (hI : SysInv s) (a b : Nat) (up : Bool) (ha : a ∈ s.cfg.ids) (hb : b ∈ s.cfg.ids)
    (hab : a < b) : SysInv (exec0 s (.contact a b up)) := by
  have hne : b ≠ a := by omega
  obtain ⟨hnd, hfwd, hmsg, hacct⟩ := hI
  have hfa := fwd_step (Nat.le_refl s.t) (hfwd a ha) (if up then .linkUp b else .linkDown b)
    (fun id d ex c' h => absurd h (link_no_hold up b id d ex c'))
  have hfb := fwd_step (Nat.le_refl s.t) (hfwd b hb) (if up then .linkUp a else .linkDown a)
    (fun id d ex c' h => absurd h (link_no_hold up a id d ex c'))
  have ka := held_step_keep (f0 := (s.nodes a).f) (f' := (DtnForward.step (s.nodes a).f s.t (if up then .linkUp b else .linkDown b)).1)
    (n := s.t) (er := (DtnForward.step (s.nodes a).f s.t (if up then .linkUp b else .linkDown b)).2) rfl
    (link_no_hold up b) (link_no_forget up b)
  have kb := held_step_keep (f0 := (s.nodes b).f) (f' := (DtnForward.step (s.nodes b).f s.t (if up then .linkUp a else .linkDown a)).1)
    (n := s.t) (er := (DtnForward.step (s.nodes b).f s.t (if up then .linkUp a else .linkDown a)).2) rfl
    (link_no_hold up a) (link_no_forget up a)
  simp only [exec0]
  generalize hxa : ({ s.nodes a with f := (DtnForward.step (s.nodes a).f s.t (if up then .linkUp b else .linkDown b)).1 } : Node) = xa
  generalize hxb : ({ s.nodes b with f := (DtnForward.step (s.nodes b).f s.t (if up then .linkUp a else .linkDown a)).1 } : Node) = xb
  have hxaf : xa.f = (DtnForward.step (s.nodes a).f s.t (if up then .linkUp b else .linkDown b)).1 := by rw [← hxa]
  have hxbf : xb.f = (DtnForward.step (s.nodes b).f s.t (if up then .linkUp a else .linkDown a)).1 := by rw [← hxb]
  have h1 := fwd_set hfwd a xa (by rw [hxaf]; exact hfa)
  have h2 := fwd_set (s := s.set a xa) h1 b xb (by rw [hxbf]; exact hfb)
  have e1 : (s.set a xa).heldAll = s.heldAll := heldAll_set_eq s a xa (by rw [hxaf]; exact ka)
  have e2 : ((s.set a xa).set b xb).heldAll = (s.set a xa).heldAll := by
    apply heldAll_set_eq
    rw [set_nodes_same _ _ _ _ hne, hxbf]
    exact kb
  refine ⟨hnd, h2, hmsg, fun hr => ?_⟩
  have := hacct hr
  show ((s.set a xa).set b xb).heldAll + s.inflight + s.dropped + s.released = s.cfg.copies
  rw [e2, e1]; exact this

theorem inv_tick {s : Sys} (hI : SysInv s) : SysInv (exec0 s .tick) := by
  obtain ⟨hnd, hfwd, hmsg, hacct⟩ := hI
  have key : ∀ m ∈ s.cfg.ids, ((exec0 s .tick).nodes m).f = (DtnForward.step (s.nodes m).f (s.t + 1) .tick).1 := by
    intro m hm; simp [exec0, hm]
  refine ⟨hnd, fun m hm => ?_, hmsg, fun hr => ?_⟩
  · show FwdOk s.cfg (s.t + 1) ((exec0 s .tick).nodes m).f
    rw [key m hm]
    exact fwd_step (Nat.le_succ _) (hfwd m hm) .tick (fun id d ex c h => nomatch h)
  · have := hacct hr
    have hh : (exec0 s .tick).heldAll = s.heldAll := by
      unfold Sys.heldAll
      show (s.cfg.ids.map fun m => DtnForward.heldSum ((exec0 s .tick).nodes m).f bid).sum = _
      congr 1
      apply List.map_congr_left
      intro m hm
      rw [key m hm]
      exact held_step_keep (inp := .tick) (f0 := (s.nodes m).f) (f' := (DtnForward.step (s.nodes m).f (s.t + 1) .tick).1)
        (n := s.t + 1) (er := (DtnForward.step (s.nodes m).f (s.t + 1) .tick).2) rfl (fun _ _ _ _ h => nomatch h)
        (fun _ h => nomatch h)
    show (exec0 s .tick).heldAll + s.inflight + s.dropped + s.released = s.cfg.copies
    rw [hh]; exact this

theorem inv_poll {s : Sys} (hI : SysInv s) (n : Nat) (hn : n ∈ s.cfg.ids) : SysInv (exec0 s (.poll n)) := by
  obtain ⟨hnd, hfwd, hmsg, hacct⟩ := hI
  have hx := hfwd n hn
  simp only [exec0]
  cases hp : DtnForward.poll (s.nodes n).f with
  | mk f' a =>
    have hf' : FwdOk s.cfg s.t f' := by
      have := fwdOk_poll hp hx
      exact this
    cases a with
    | none =>
      simp only
      refine ⟨hnd, fwd_set hfwd n _ hf', hmsg, fun hr => ?_⟩
      have := hacct hr
      have e := heldAll_set_eq s n ⟨f', (ledgerAfter s (.poll n) n).B, (ledgerAfter s (.poll n) n).L⟩
        (held_poll_keep hp (fun _ h => nomatch h) (fun _ _ _ h => nomatch h))
      show (s.set n _).heldAll + s.inflight + s.dropped + s.released = s.cfg.copies
      rw [e]; exact this
    | send p b c r =>
      simp only
      have hdel : ∀ id fr to c', Msg.bun s.seq n p c (!r) = .bun id fr to c' true → to = s.cfg.dest → c' = 0 := by
        intro id fr to c' h hto
        simp only [Msg.bun.injEq] at h
        obtain ⟨-, -, hpp, hc, hr⟩ := h
        cases r
        · subst hpp hc
          obtain ⟨-, -, hfalse⟩ := DtnForward.poll_send_spec hp
          obtain ⟨-, -, bi, b0, hb0, -, -, hcase⟩ := hfalse rfl
          have hd := (hx.bok bi b0 hb0).2.2
          rcases hcase with ⟨_, h0⟩ | ⟨hne, _⟩
          · exact h0
          · exact absurd (hto.trans hd.symm) hne
        · simp at hr
      refine ⟨hnd, fwd_set hfwd n _ hf', msgOk_cons hmsg _ hdel, fun hr => ?_⟩
      have := hacct hr
      cases r
      · have hs := held_poll_send hp hx.bok
        have e := heldAll_set_delta s n ⟨f', (ledgerAfter s (.poll n) n).B, (ledgerAfter s (.poll n) n).L⟩ hnd hn
        show (s.set n _).heldAll + (c + (s.msgs.map Msg.freshCopies).sum) + s.dropped + s.released = s.cfg.copies
        simp only [Sys.inflight] at this
        simp only at e
        omega
      · have hs := held_poll_keep hp (fun _ h => nomatch h) (fun _ _ _ h => by simp at h)
        have e := heldAll_set_eq s n ⟨f', (ledgerAfter s (.poll n) n).B, (ledgerAfter s (.poll n) n).L⟩ hs
        show (s.set n _).heldAll + (0 + (s.msgs.map Msg.freshCopies).sum) + s.dropped + s.released = s.cfg.copies
        simp only [Sys.inflight] at this
        rw [e]; omega
    | release b =>
      simp only
      refine ⟨hnd, fwd_set hfwd n _ hf', hmsg, fun hr => ?_⟩
      have := hacct hr
      have h0 := held_poll_release hp hx.uniq hx.bok
      have e := heldAll_set_delta s n ⟨f', (ledgerAfter s (.poll n) n).B, (ledgerAfter s (.poll n) n).L⟩ hnd hn
      show (s.set n _).heldAll + s.inflight + s.dropped + (s.released + heldOf (s.nodes n).f) = s.cfg.copies
      unfold heldOf
      simp only at e
      omega

theorem fresh_bun (id fr to c : Nat) (fresh : Bool) :
    (Msg.bun id fr to c fresh).freshCopies = if fresh then c else 0 := by
  cases fresh <;> rfl

theorem inv_bun {s : Sys} (hI : SysInv s) (id from_ r c : Nat) (fresh : Bool)
    (hm : Msg.bun id from_ r c fresh ∈ s.msgs) (hr : r ∈ s.cfg.ids) :
    SysInv (exec0 s (.bun (.bun id from_ r c fresh))) := by
  obtain ⟨hnd, hfwd, hmsg, hacct⟩ := hI
  have hinfl := inflight_erase s _ hm
  by_cases hd : r = s.cfg.dest
  · subst hd
    simp only [exec0, ite_true]
    have hc0 : (Msg.bun id from_ s.cfg.dest c fresh).freshCopies = 0 := by
      rw [fresh_bun]
      cases fresh
      · rfl
      · exact hmsg _ hm id from_ s.cfg.dest c rfl rfl
    refine ⟨hnd, hfwd, msgOk_cons (msgOk_erase hmsg _) (Msg.ack s.seq s.cfg.dest from_) (fun _ _ _ _ h => nomatch h), fun hrep => ?_⟩
    have := hacct hrep
    show s.heldAll + (0 + (s.msgs.erase (Msg.bun id from_ s.cfg.dest c fresh) |>.map Msg.freshCopies).sum) + s.dropped + s.released = s.cfg.copies
    simp only [Sys.inflight] at this hinfl
    omega
  · simp only [exec0, hd, ite_false]
    have hx := hfwd r hr
    cases hacc : (DtnStore.accept (s.nodes r).B (s.nodes r).L bid 1 s.cfg.exp from_ s.t).err with
    | some e =>
      simp only [hacc]
      refine ⟨hnd, fwd_set hfwd r _ hx, msgOk_erase hmsg _, fun hrep => ?_⟩
      have := hacct hrep
      have e1 := heldAll_set_eq s r ⟨(s.nodes r).f, (ledgerAfter s (.bun (.bun id from_ r c fresh)) r).B,
        (ledgerAfter s (.bun (.bun id from_ r c fresh)) r).L⟩ rfl
      show (s.set r _).heldAll + (s.msgs.erase (Msg.bun id from_ r c fresh) |>.map Msg.freshCopies).sum +
        (s.dropped + (if fresh = true then c else 0)) + s.released = s.cfg.copies
      rw [e1]
      simp only [Sys.inflight, fresh_bun] at this hinfl
      omega
    | none =>
      simp only [hacc]
      by_cases hok : (DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).2 = .ok
      · have hhold := held_hold_ok (f0 := (s.nodes r).f) (f' := (DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).1)
          (n := s.t) (d := s.cfg.dest) (ex := s.cfg.exp) (c := c) (by
            have : DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c) =
                ((DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).1, .ok) :=
              Prod.ext rfl hok
            exact this)
        refine ⟨hnd, fwd_set hfwd r _ (fwd_step (Nat.le_refl _) hx _ (fun i d e c' h => by
            simp only [DtnForward.Input.hold.injEq] at h; exact ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm⟩)),
          msgOk_cons (msgOk_erase hmsg _) (Msg.ack s.seq r from_) (fun _ _ _ _ h => nomatch h), fun hrep => ?_⟩
        cases fresh
        · exfalso
          simp [hok] at hrep
        · have := hacct (by simpa [hok] using hrep)
          have e := heldAll_set_delta s r ⟨(DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).1,
            (ledgerAfter s (.bun (.bun id from_ r c true)) r).B, (ledgerAfter s (.bun (.bun id from_ r c true)) r).L⟩ hnd hr
          simp only at e
          show (s.set r _).heldAll + (0 + (s.msgs.erase (Msg.bun id from_ r c true) |>.map Msg.freshCopies).sum) +
            (s.dropped + (if ((DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).2 != .ok && true) = true then c else 0)) +
            s.released = s.cfg.copies
          simp only [Sys.inflight, fresh_bun, eq_self_iff_true, ite_true, if_true] at this hinfl
          simp only [hok, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false]
          omega
      · have hfh := fwd_step (Nat.le_refl _) hx (.hold bid s.cfg.dest s.cfg.exp c) (fun i d e c' h => by
            simp only [DtnForward.Input.hold.injEq] at h; exact ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm⟩)
        refine ⟨hnd, fwd_set hfwd r _ hfh, msgOk_cons (msgOk_erase hmsg _) (Msg.ack s.seq r from_)
          (fun _ _ _ _ h => nomatch h), fun hrep => ?_⟩
        have hh := held_hold_err (f0 := (s.nodes r).f) (f' := (DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).1)
          (n := s.t) (er := (DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).2) (id := bid) (d := s.cfg.dest)
          (ex := s.cfg.exp) (c := c) rfl hok
        have e1 := heldAll_set_eq s r ⟨(DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).1,
          (ledgerAfter s (.bun (.bun id from_ r c fresh)) r).B, (ledgerAfter s (.bun (.bun id from_ r c fresh)) r).L⟩ hh
        have := hacct (by simpa [hok] using hrep)
        show (s.set r _).heldAll + (0 + (s.msgs.erase (Msg.bun id from_ r c fresh) |>.map Msg.freshCopies).sum) +
          (s.dropped + (if ((DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).2 != .ok && fresh) = true then c else 0)) +
          s.released = s.cfg.copies
        have hne : ((DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).2 != .ok) = true := by
          simpa using hok
        simp only [hne, Bool.true_and]
        rw [e1]
        simp only [Sys.inflight, fresh_bun] at this hinfl
        omega

theorem inv_ack {s : Sys} (hI : SysInv s) (id c p : Nat) (hm : Msg.ack id c p ∈ s.msgs) (hp : p ∈ s.cfg.ids) :
    SysInv (exec0 s (.ack (.ack id c p))) := by
  obtain ⟨hnd, hfwd, hmsg, hacct⟩ := hI
  have hinfl := inflight_erase s _ hm
  have hx := hfwd p hp
  simp only [exec0]
  have hfa := fwd_step (Nat.le_refl s.t) hx (.acked c bid) (fun i d e c' h => nomatch h)
  have ka := held_step_keep (f0 := (s.nodes p).f) (f' := (DtnForward.step (s.nodes p).f s.t (.acked c bid)).1)
    (n := s.t) (er := (DtnForward.step (s.nodes p).f s.t (.acked c bid)).2) (inp := .acked c bid) rfl
    (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h)
  refine ⟨hnd, fwd_set hfwd p _ hfa, msgOk_erase hmsg _, fun hrep => ?_⟩
  have := hacct hrep
  have e := heldAll_set_eq s p ⟨(DtnForward.step (s.nodes p).f s.t (.acked c bid)).1,
    (ledgerAfter s (.ack (.ack id c p)) p).B, (ledgerAfter s (.ack (.ack id c p)) p).L⟩ ka
  show (s.set p _).heldAll + (s.msgs.erase (Msg.ack id c p) |>.map Msg.freshCopies).sum + s.dropped + s.released = s.cfg.copies
  rw [e]
  simp only [Sys.inflight] at this hinfl
  have : (Msg.ack id c p).freshCopies = 0 := rfl
  omega

theorem inv_lose {s : Sys} (hI : SysInv s) (m : Msg) (hm : m ∈ s.msgs) : SysInv (exec0 s (.lose m)) := by
  obtain ⟨hnd, hfwd, hmsg, hacct⟩ := hI
  have hinfl := inflight_erase s _ hm
  refine ⟨hnd, hfwd, msgOk_erase hmsg _, fun hrep => ?_⟩
  have := hacct hrep
  simp only [Sys.inflight] at this hinfl
  cases m with
  | bun a b c d e =>
    cases e
    · show s.heldAll + (s.msgs.erase (Msg.bun a b c d false) |>.map Msg.freshCopies).sum + (s.dropped + 0) + s.released = s.cfg.copies
      have : (Msg.bun a b c d false).freshCopies = 0 := rfl
      omega
    · show s.heldAll + (s.msgs.erase (Msg.bun a b c d true) |>.map Msg.freshCopies).sum + (s.dropped + d) + s.released = s.cfg.copies
      have : (Msg.bun a b c d true).freshCopies = d := rfl
      omega
  | ack a b c =>
    show s.heldAll + (s.msgs.erase (Msg.ack a b c) |>.map Msg.freshCopies).sum + (s.dropped + 0) + s.released = s.cfg.copies
    have : (Msg.ack a b c).freshCopies = 0 := rfl
    omega

theorem inv_press {s : Sys} (hI : SysInv s) (n k : Nat) (hn : n ∈ s.cfg.ids) : SysInv (exec0 s (.press n k)) := by
  obtain ⟨hnd, hfwd, hmsg, hacct⟩ := hI
  have hx := hfwd n hn
  simp only [exec0]
  cases hadm : (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).err with
  | some e => exact ⟨hnd, hfwd, hmsg, hacct⟩
  | none =>
    simp only
    by_cases hg : ((DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).ev.any
        fun e => e.key.space == 1) = true
    · simp only [hg, ite_true]
      have hfa := fwd_step (Nat.le_refl s.t) hx (.forget bid) (fun i d e c' h => nomatch h)
      have h0 := held_forget (f0 := (s.nodes n).f) (f' := (DtnForward.step (s.nodes n).f s.t (.forget bid)).1)
        (n := s.t) (er := (DtnForward.step (s.nodes n).f s.t (.forget bid)).2) rfl hx.uniq
      refine ⟨hnd, fwd_set hfwd n _ hfa, hmsg, fun hrep => ?_⟩
      have := hacct hrep
      have e := heldAll_set_delta s n ⟨(DtnForward.step (s.nodes n).f s.t (.forget bid)).1, (s.nodes n).B,
        (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).L⟩ hnd hn
      show (s.set n _).heldAll + s.inflight + s.dropped + (s.released + heldOf (s.nodes n).f) = s.cfg.copies
      unfold heldOf
      simp only at e
      omega
    · simp only [hg, Bool.false_eq_true, ite_false]
      refine ⟨hnd, fwd_set hfwd n _ hx, hmsg, fun hrep => ?_⟩
      have := hacct hrep
      have e := heldAll_set_eq s n ⟨(s.nodes n).f, (s.nodes n).B,
        (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).L⟩ rfl
      show (s.set n _).heldAll + s.inflight + s.dropped + (s.released + 0) = s.cfg.copies
      rw [e]; omega

theorem inv_exec0 {s : Sys} (hI : SysInv s) (ev : Ev) (hE : En s ev) : SysInv (exec0 s ev) := by
  cases ev with
  | contact a b up => exact inv_contact hI a b up hE.1 hE.2.1 hE.2.2
  | tick => exact inv_tick hI
  | poll n => exact inv_poll hI n hE
  | bun m =>
    cases m with
    | bun id f r c fr => exact inv_bun hI id f r c fr hE.1 hE.2
    | ack a b c => exact hE.2.elim
  | ack m =>
    cases m with
    | ack id c p => exact inv_ack hI id c p hE.1 hE.2
    | bun a b c d e => exact hE.2.elim
  | lose m => exact inv_lose hI m hE
  | press n k => exact inv_press hI n k hE
  | bad => exact hI

theorem inv_exec {s : Sys} (hI : SysInv s) (ev : Ev) (hE : En s ev) : SysInv (exec s ev) := by
  have h := inv_exec0 hI ev hE
  exact ⟨h.nodup, h.fwd, h.msgOk, h.acct⟩

/-- **Every reachable system is in the invariant.** -/
theorem reach_inv {s : Sys} (h : Reach s) : SysInv s := by
  induction h with
  | init c hn hsrc hmax hacc hhold => exact inv_init c hn hsrc hhold
  | step ev _ hE ih => exact inv_exec ih ev hE

/-- **The copy budget is conserved.** In every reachable system, while no retransmitted hold was accepted after the
bundle finished, the copies held by all nodes plus those in flight plus those dropped plus those released are exactly
the budget of the bundle: no copy is lost or duplicated, whatever the network and the contacts do, however many nodes
there are. -/
theorem copies_conserved {s : Sys} (h : Reach s) (hr : s.replayed = false) :
    s.heldAll + s.inflight + s.dropped + s.released = s.cfg.copies :=
  (reach_inv h).acct hr

/-- **Held is at most the budget under loss** (a lost message is counted as dropped, so nothing it carried is held
anywhere). -/
theorem held_le_budget {s : Sys} (h : Reach s) (hr : s.replayed = false) : s.heldAll ≤ s.cfg.copies := by
  have := copies_conserved h hr
  omega

end Vinc.DtnScenario
