import Vinc.BroadcastNodeSpacing

/-!
# Broadcast node: a timer leaves nothing expired (`Swept`)

The unbounded counterpart of `Swept` of `proofs/tla/BroadcastNode.tla`: in every reachable state whose last step was
the timer, no record of the dedupe set is older than the ttl and no entry of the hub log is older than the log
window (`swept`).

`Seen::expire` and `HubLog::expire` pop from the front only and stop at the first record that is young enough, so
the statement rests on the order of both tables: the records of the dedupe set and the entries of the log are in
the order of their times, and none is later than the clock (`TInv`, kept by every step of the system). The order
holds because an operator changes the dedupe set only by recording at the current time at the back and by dropping
the front (`SeenEv`, proved for every operator), and the log only by a write at the current time at the back and a
pop of the front.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

/-! ## What an operator does to the order of the dedupe set -/

/-- `S'` is `S` after any sequence of records made at `now` and drops of the oldest record. -/
inductive SeenEv (now : Nat) (S : Seen) : Seen → Prop where
  | refl : SeenEv now S S
  | push {S' : Seen} (mid : Nat) : SeenEv now S S' → SeenEv now S (SPush S' mid now)
  | pop {S' : Seen} : SeenEv now S S' → SeenEv now S (SPopFront S')

theorem SeenEv.trans {now : Nat} {A B C : Seen} (h1 : SeenEv now A B) (h2 : SeenEv now B C) : SeenEv now A C := by
  induction h2 with
  | refl => exact h1
  | push mid _ ih => exact .push mid ih
  | pop _ ih => exact .pop ih

theorem SInsert_ev (p : Params) (S : Seen) (mid now : Nat) (f : Bool) : SeenEv now S (SInsert p S mid now f) := by
  unfold SInsert
  split
  · split
    · exact .push mid (.pop .refl)
    · exact .refl
  · exact .push mid .refl

theorem SInsertAll_ev (p : Params) (now : Nat) (ids : List Nat) : ∀ S : Seen, SeenEv now S (SInsertAll p S now ids) := by
  induction ids with
  | nil => intro S; exact .refl
  | cons i ids ih =>
    intro S
    unfold SInsertAll
    refine SeenEv.trans ?_ (ih _)
    split
    · exact .refl
    · exact SInsert_ev p S i now true

theorem SweepIds_ev (p : Params) (now : Nat) (ids : List Nat) : ∀ S : Seen, SeenEv now S (SweepIds p S now ids) := by
  induction ids with
  | nil => intro S; exact .refl
  | cons i ids ih =>
    intro S
    unfold SweepIds
    refine SeenEv.trans ?_ (ih _)
    split
    · exact .refl
    · exact SInsert_ev p S i now true

theorem SExpireAux_ev (p : Params) (now : Nat) (f : Nat) : ∀ S : Seen, SeenEv now S (SExpireAux p now f S) := by
  induction f with
  | zero => intro S; simp only [SExpireAux]; exact .refl
  | succ f ih =>
    intro S; simp only [SExpireAux]
    split
    · exact .refl
    · split
      · exact SeenEv.trans (.pop .refl) (ih _)
      · exact .refl

theorem Offer_ev (p : Params) (N : Node) (now : Nat) (m : Ent) : SeenEv now N.seen (Offer p N now m).n.seen := by
  have F := Offer_form p N now m
  generalize Offer p N now m = r at F
  cases F with
  | topic _ => exact .refl
  | seenFull _ _ => exact .refl
  | floor _ _ _ _ => rw [(HoldFloor_frame p N m).2.1]; exact .refl
  | full _ _ _ _ _ =>
    show SeenEv now N.seen (HoldAndAsk p N m).n.seen
    rw [(HoldAndAsk_frame p N m).2.1]; exact .refl
  | skip _ _ _ => exact SInsert_ev p N.seen m.mid now false
  | deliver _ _ _ _ _ _ _ _ _ => exact SInsert_ev p N.seen m.mid now false
  | deny _ _ _ => exact SInsert_ev p N.seen m.mid now false
  | ask _ _ _ _ =>
    show SeenEv now N.seen (HoldAndAsk p (N1of p N now m) m).n.seen
    rw [(HoldAndAsk_frame p (N1of p N now m) m).2.1]
    exact SInsert_ev p N.seen m.mid now false

theorem OfferHeld_ev (p : Params) (N : Node) (now : Nat) (e : Ent) : SeenEv now N.seen (OfferHeld p N now e).n.seen := by
  unfold OfferHeld
  split
  · exact .refl
  · exact Offer_ev p N now e

theorem OfferAll_ev (p : Params) (now : Nat) (es : List Ent) :
    ∀ (r : Res) (A : Seen), SeenEv now A r.n.seen → SeenEv now A (OfferAll p now r es).n.seen := by
  induction es with
  | nil => intro r A h; exact h
  | cons e es ih =>
    intro r A h
    exact ih _ A (h.trans (OfferHeld_ev p r.n now e))

theorem FloorsSettled_ev (p : Params) (N : Node) (now : Nat) (used : Bool) (rf : Option Nat)
    (of_ : Option (Nat → Option Nat)) (nh : Bool) :
    SeenEv now N.seen (FloorsSettled p N now used rf of_ nh).n.seen := by
  unfold FloorsSettled
  exact OfferAll_ev p now _ _ N.seen .refl

/-- After the timer the dedupe set is the expired set, then records made at `now` and drops of the front. -/
theorem OnTimer_ev_expired (p : Params) (N : Node) (now : Nat) :
    SeenEv now (SExpire p N.seen now) (OnTimer p N now).n.seen := by
  have hsw : SeenEv now (SExpire p N.seen now) (Sweep p N now).seen := by
    unfold Sweep
    exact SweepIds_ev p now _ _
  unfold OnTimer
  dsimp only
  split
  · exact hsw.trans (FloorsSettled_ev p _ now _ _ _ _)
  · exact hsw

theorem OnTimer_ev (p : Params) (N : Node) (now : Nat) : SeenEv now N.seen (OnTimer p N now).n.seen :=
  (SExpireAux_ev p now _ N.seen).trans (OnTimer_ev_expired p N now)

theorem AcpAnswer_seen (p : Params) (N : Node) (now id : Nat) (allow : Bool) :
    (AcpAnswer p N now id allow).n.seen = N.seen := by
  unfold AcpAnswer
  rcases hf : N.checks.find? (fun c => c.id == id) with _ | c <;> simp [hf, Plain]

theorem HubStore_ev (p : Params) (N : Node) (now wall : Nat) (fanned : Bool) (m : Msg) :
    SeenEv now N.seen (HubStore p N now wall fanned m).n.seen := by
  unfold HubStore
  by_cases htf : p.topicFull = true
  · rw [if_pos htf]; exact .refl
  · rw [if_neg htf]
    dsimp only
    generalize LPush p N.lg m.mid now wall m.n = rr
    have h1 := SInsertAll_ev p now rr.ev N.seen
    by_cases hok : rr.ok = true
    · rw [if_neg (by simp [hok])]
      by_cases hsub : (N.sub && m.origin != p.me) = true
      · rw [if_pos hsub]
        exact h1.trans (Offer_ev p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} now m.ent)
      · rw [if_neg hsub]
        exact h1.trans (SInsert_ev p _ m.mid now true)
    · rw [if_pos (by simpa using hok)]
      exact h1

theorem OnMsg_ev (p : Params) (N : Node) (now wall : Nat) (t : Frame) (b : Bool) (m : Msg) :
    SeenEv now N.seen (OnMsg p N now wall t b m).n.seen := by
  unfold OnMsg
  by_cases h1 : (!Allowed p t b) = true
  · rw [if_pos h1]; exact .refl
  rw [if_neg h1]
  by_cases h2 : m.kind = .badhead
  · rw [if_pos h2]; exact .refl
  rw [if_neg h2]
  by_cases h3 : m.kind = .big
  · rw [if_pos h3]; exact .refl
  rw [if_neg h3]
  dsimp only
  by_cases h4 : IsDup p N m.mid now = true
  · rw [if_pos h4]; exact .refl
  rw [if_neg h4]
  by_cases h5 : p.revoked.contains m.origin = true
  · rw [if_pos h5]; exact .refl
  rw [if_neg h5]
  by_cases h6 : (m.kind = .badsig ∨ m.kind = .graft)
  · rw [if_pos h6]; exact .refl
  rw [if_neg h6]
  by_cases hhub : p.isHub = true
  · rw [if_pos hhub, NoteStored_seen]
    exact HubStore_ev p {N with req := N.req.filter (fun x => x != m.mid)} now wall _ m
  · rw [if_neg hhub]
    exact Offer_ev p {N with req := N.req.filter (fun x => x != m.mid)} now m.ent

/-! ## The records are in the order of their times -/

/-- The records of the dedupe set are in the order of their times, and none is later than `now`. -/
def SeenT (S : Seen) (now : Nat) : Prop :=
  S.order.Pairwise (fun a b => a.2 ≤ b.2) ∧ ∀ e ∈ S.order, e.2 ≤ now

/-- No record of the dedupe set is older than the ttl. -/
def SeenFresh (p : Params) (S : Seen) (now : Nat) : Prop := ∀ e ∈ S.order, now - e.2 ≤ p.ttl

theorem SPopFront_order (S : Seen) : (SPopFront S).order = S.order.tail := by
  unfold SPopFront; split <;> simp_all

theorem SeenT.mono {S : Seen} {now now' : Nat} (h : SeenT S now) (hle : now ≤ now') : SeenT S now' :=
  ⟨h.1, fun e he => Nat.le_trans (h.2 e he) hle⟩

theorem SeenEv.seenT {now : Nat} {S S' : Seen} (h : SeenEv now S S') (hT : SeenT S now) : SeenT S' now := by
  induction h with
  | refl => exact hT
  | @push S'' mid _ ih =>
    refine ⟨?_, ?_⟩
    · show (S''.order ++ [(mid, now)]).Pairwise (fun a b => a.2 ≤ b.2)
      rw [List.pairwise_append]
      refine ⟨ih.1, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact ih.2 a ha
    · intro e he
      have he' : e ∈ S''.order ++ [(mid, now)] := he
      rcases List.mem_append.1 he' with h1 | h1
      · exact ih.2 e h1
      · rw [List.mem_singleton] at h1; subst h1; exact Nat.le_refl _
  | @pop S'' _ ih =>
    unfold SeenT
    rw [SPopFront_order]
    exact ⟨List.Pairwise.sublist (List.tail_sublist _) ih.1, fun e he => ih.2 e (List.mem_of_mem_tail he)⟩

theorem SeenEv.fresh {p : Params} {now : Nat} {S S' : Seen} (h : SeenEv now S S') (hF : SeenFresh p S now) :
    SeenFresh p S' now := by
  induction h with
  | refl => exact hF
  | @push S'' mid _ ih =>
    intro e he
    have he' : e ∈ S''.order ++ [(mid, now)] := he
    rcases List.mem_append.1 he' with h1 | h1
    · exact ih e h1
    · rw [List.mem_singleton] at h1; subst h1; simp
  | @pop S'' _ ih =>
    intro e he
    rw [SPopFront_order] at he
    exact ih e (List.mem_of_mem_tail he)

/-- An expiry of a set whose records are in the order of their times leaves no expired record. -/
theorem SExpireAux_fresh (p : Params) (now : Nat) (f : Nat) :
    ∀ S : Seen, S.order.length ≤ f → S.order.Pairwise (fun a b => a.2 ≤ b.2) →
      SeenFresh p (SExpireAux p now f S) now := by
  induction f with
  | zero =>
    intro S hl _ e he
    simp only [SExpireAux] at he
    have : S.order = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
    rw [this] at he; cases he
  | succ f ih =>
    intro S hl hp
    unfold SExpireAux
    rcases hS : S.order with _ | ⟨e, rest⟩
    · intro x hx; rw [hS] at hx; cases hx
    · rw [hS] at hl hp
      by_cases hc : p.ttl < now - e.2
      · simp only [hc, ite_true]
        have ho : (SPopFront S).order = rest := by rw [SPopFront_order, hS]; rfl
        apply ih
        · rw [ho]; simp at hl; omega
        · rw [ho]; exact (List.pairwise_cons.1 hp).2
      · simp only [hc, ite_false]
        intro x hx
        rw [hS] at hx
        rcases List.mem_cons.1 hx with h1 | h1
        · subst h1; omega
        · have := (List.pairwise_cons.1 hp).1 x h1
          omega

theorem SExpire_fresh {p : Params} {S : Seen} {now : Nat} (h : SeenT S now) : SeenFresh p (SExpire p S now) now :=
  SExpireAux_fresh p now _ S (Nat.le_refl _) h.1

/-! ## The log entries are in the order of their arrival -/

/-- The entries of the hub log are in the order of their arrival times, and none is later than `now`. -/
def LogT (L : Log) (now : Nat) : Prop :=
  L.entries.Pairwise (fun a b => a.at_ ≤ b.at_) ∧ ∀ e ∈ L.entries, e.at_ ≤ now

theorem LogT.mono {L : Log} {now now' : Nat} (h : LogT L now) (hle : now ≤ now') : LogT L now' :=
  ⟨h.1, fun e he => Nat.le_trans (h.2 e he) hle⟩

theorem LPop_logT {L : Log} {now : Nat} (h : LogT L now) : LogT (LPop L) now := by
  unfold LogT
  rw [LPop_entries]
  exact ⟨List.Pairwise.sublist (List.tail_sublist _) h.1, fun e he => h.2 e (List.mem_of_mem_tail he)⟩

theorem LWrite_logT (p : Params) {L : Log} {now : Nat} (h : LogT L now) (mid wall n : Nat) :
    LogT (LWrite p L mid now wall n) now := by
  refine ⟨?_, ?_⟩
  · show (L.entries ++ [_]).Pairwise (fun (a b : LEntry) => a.at_ ≤ b.at_)
    rw [List.pairwise_append]
    refine ⟨h.1, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact h.2 a ha
  · intro e he
    have he' : e ∈ L.entries ++ [_] := he
    rcases List.mem_append.1 he' with h1 | h1
    · exact h.2 e h1
    · rw [List.mem_singleton] at h1; subst h1; exact Nat.le_refl _

theorem LLoop_logT (p : Params) (mid now wall n : Nat) (f : Nat) :
    ∀ (L : Log) (ev : List Nat), LogT L now → LogT (LLoop p mid now wall n f L ev).log now := by
  induction f with
  | zero => intro L ev h; exact h
  | succ f ih =>
    intro L ev h
    unfold LLoop
    split
    · exact LWrite_logT p h mid wall n
    · rcases hL : L.entries with _ | ⟨e, rest⟩
      · exact h
      · exact ih (LPop L) (ev ++ [e.mid]) (LPop_logT h)

theorem LPush_logT (p : Params) {L : Log} {now : Nat} (h : LogT L now) (mid wall n : Nat) :
    LogT (LPush p L mid now wall n).log now := by
  unfold LPush
  split
  · exact h
  · exact LLoop_logT p mid now wall n _ L [] h

theorem LExpireAux_logT (p : Params) (now t : Nat) (f : Nat) :
    ∀ (L : Log) (ev : List Nat), LogT L t → LogT (LExpireAux p now f L ev).log t := by
  induction f with
  | zero => intro L ev h; exact h
  | succ f ih =>
    intro L ev h
    unfold LExpireAux
    rcases hL : L.entries with _ | ⟨e, rest⟩
    · exact h
    · by_cases hc : p.logWin < now - e.at_
      · simp only [hc, ite_true]; exact ih (LPop L) (ev ++ [e.mid]) (LPop_logT h)
      · simp only [hc, ite_false]; exact h

/-- An expiry of a log whose entries are in the order of their arrival leaves no entry older than the window. -/
theorem LExpireAux_fresh (p : Params) (now : Nat) (f : Nat) :
    ∀ (L : Log) (ev : List Nat), L.entries.length ≤ f → L.entries.Pairwise (fun a b => a.at_ ≤ b.at_) →
      ∀ e ∈ (LExpireAux p now f L ev).log.entries, now - e.at_ ≤ p.logWin := by
  induction f with
  | zero =>
    intro L ev hl _ e he
    have : L.entries = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
    have he' : e ∈ L.entries := he
    rw [this] at he'; cases he'
  | succ f ih =>
    intro L ev hl hp
    unfold LExpireAux
    rcases hL : L.entries with _ | ⟨e, rest⟩
    · intro x hx
      have hx' : x ∈ L.entries := hx
      rw [hL] at hx'; cases hx'
    · rw [hL] at hl hp
      by_cases hc : p.logWin < now - e.at_
      · simp only [hc, ite_true]
        have ho : (LPop L).entries = rest := by rw [LPop_entries, hL]; rfl
        apply ih
        · rw [ho]; simp at hl; omega
        · rw [ho]; exact (List.pairwise_cons.1 hp).2
      · simp only [hc, ite_false]
        intro x hx
        have hx' : x ∈ L.entries := hx
        rw [hL] at hx'
        rcases List.mem_cons.1 hx' with h1 | h1
        · subst h1; omega
        · have := (List.pairwise_cons.1 hp).1 x h1
          omega

/-! ## What an operator does to the log -/

theorem HubStore_lg (p : Params) (N : Node) (now wall : Nat) (fanned : Bool) (m : Msg) :
    (HubStore p N now wall fanned m).n.lg = N.lg ∨
      (HubStore p N now wall fanned m).n.lg = (LPush p N.lg m.mid now wall m.n).log := by
  unfold HubStore
  by_cases htf : p.topicFull = true
  · rw [if_pos htf]; exact Or.inl rfl
  · rw [if_neg htf]
    dsimp only
    generalize LPush p N.lg m.mid now wall m.n = rr
    by_cases hok : rr.ok = true
    · rw [if_neg (by simp [hok])]
      by_cases hsub : (N.sub && m.origin != p.me) = true
      · rw [if_pos hsub]
        exact Or.inr (Offer_spec p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} now m.ent).lg
      · rw [if_neg hsub]; exact Or.inr rfl
    · rw [if_pos (by simpa using hok)]; exact Or.inr rfl

theorem OnMsg_lg (p : Params) (N : Node) (now wall : Nat) (t : Frame) (b : Bool) (m : Msg) :
    (OnMsg p N now wall t b m).n.lg = N.lg ∨
      (OnMsg p N now wall t b m).n.lg = (LPush p N.lg m.mid now wall m.n).log := by
  unfold OnMsg
  by_cases h1 : (!Allowed p t b) = true
  · rw [if_pos h1]; exact Or.inl rfl
  rw [if_neg h1]
  by_cases h2 : m.kind = .badhead
  · rw [if_pos h2]; exact Or.inl rfl
  rw [if_neg h2]
  by_cases h3 : m.kind = .big
  · rw [if_pos h3]; exact Or.inl rfl
  rw [if_neg h3]
  dsimp only
  by_cases h4 : IsDup p N m.mid now = true
  · rw [if_pos h4]; exact Or.inl rfl
  rw [if_neg h4]
  by_cases h5 : p.revoked.contains m.origin = true
  · rw [if_pos h5]; exact Or.inl rfl
  rw [if_neg h5]
  by_cases h6 : (m.kind = .badsig ∨ m.kind = .graft)
  · rw [if_pos h6]; exact Or.inl rfl
  rw [if_neg h6]
  by_cases hhub : p.isHub = true
  · rw [if_pos hhub, NoteStored_lg]
    exact HubStore_lg p {N with req := N.req.filter (fun x => x != m.mid)} now wall _ m
  · rw [if_neg hhub]
    exact Or.inl (Offer_spec p {N with req := N.req.filter (fun x => x != m.mid)} now m.ent).lg

theorem FloorsSettled_lg (p : Params) (N : Node) (now : Nat) (used : Bool) (rf : Option Nat)
    (of_ : Option (Nat → Option Nat)) (nh : Bool) : (FloorsSettled p N now used rf of_ nh).n.lg = N.lg := by
  unfold FloorsSettled
  have T := offerAllTrans p now N.fhold
    (Plain {N with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} [.floorDone used])
  rw [T.lg]; rfl

theorem OnTimer_lg (p : Params) (N : Node) (now : Nat) : (OnTimer p N now).n.lg = (LExpire p N.lg now).log := by
  unfold OnTimer
  dsimp only
  split
  · rw [FloorsSettled_lg]; rfl
  · rfl

theorem AcpAnswer_lg (p : Params) (N : Node) (now id : Nat) (allow : Bool) :
    (AcpAnswer p N now id allow).n.lg = N.lg := by
  unfold AcpAnswer
  rcases hf : N.checks.find? (fun c => c.id == id) with _ | c <;> simp [hf, Plain]

/-! ## The system invariant and `Swept` -/

/-- The invariant of a reachable state: both tables are in the order of their times and not ahead of the clock, and
after a timer step neither holds anything expired. -/
structure TInv (p : Params) (s : Sys) : Prop where
  seen : SeenT s.node.seen s.now
  lg : LogT s.node.lg s.now
  swept : s.last = .timer →
    SeenFresh p s.node.seen s.now ∧ ∀ e ∈ s.node.lg.entries, s.now - e.at_ ≤ p.logWin

theorem tinv_init (p : Params) : TInv p (SInit p) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, fun h => ?_⟩
  · show ([] : List (Nat × Nat)).Pairwise _; exact List.Pairwise.nil
  · intro e he; cases he
  · show ([] : List LEntry).Pairwise _; exact List.Pairwise.nil
  · intro e he; cases he
  · cases h

theorem step_tinv {p : Params} {s s' : Sys} (hs : TInv p s) (st : Step p s s') : TInv p s' := by
  cases st with
  | msg t b m =>
    refine ⟨(OnMsg_ev p s.node s.now s.now t b m).seenT hs.seen, ?_, fun h => by cases h⟩
    show LogT (OnMsg p s.node s.now s.now t b m).n.lg s.now
    rcases OnMsg_lg p s.node s.now s.now t b m with h | h
    · rw [h]; exact hs.lg
    · rw [h]; exact LPush_logT p hs.lg _ _ _
  | timer =>
    have hlg : (OnTimer p s.node s.now).n.lg = (LExpire p s.node.lg s.now).log := OnTimer_lg p s.node s.now
    refine ⟨(OnTimer_ev p s.node s.now).seenT hs.seen, ?_, fun _ => ⟨?_, ?_⟩⟩
    · show LogT (OnTimer p s.node s.now).n.lg s.now
      rw [hlg]; exact LExpireAux_logT p s.now s.now _ _ _ hs.lg
    · exact (OnTimer_ev_expired p s.node s.now).fresh (SExpire_fresh hs.seen)
    · show ∀ e ∈ (OnTimer p s.node s.now).n.lg.entries, s.now - e.at_ ≤ p.logWin
      rw [hlg]; exact LExpireAux_fresh p s.now _ _ _ (Nat.le_refl _) hs.lg.1
  | answer c hc allow =>
    refine ⟨?_, ?_, fun h => by cases h⟩
    · show SeenT (AcpAnswer p s.node s.now c.id allow).n.seen s.now
      rw [AcpAnswer_seen]; exact hs.seen
    · show LogT (AcpAnswer p s.node s.now c.id allow).n.lg s.now
      rw [AcpAnswer_lg]; exact hs.lg
  | floors rf of_ nh h =>
    refine ⟨(FloorsSettled_ev p s.node s.now true rf of_ nh).seenT hs.seen, ?_, fun h => by cases h⟩
    show LogT (FloorsSettled p s.node s.now true rf of_ nh).n.lg s.now
    rw [FloorsSettled_lg]; exact hs.lg
  | tick h =>
    exact ⟨hs.seen.mono (Nat.le_succ _), hs.lg.mono (Nat.le_succ _), fun h => by cases h⟩
  | restart =>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, fun h => by cases h⟩
    · show ([] : List (Nat × Nat)).Pairwise _; exact List.Pairwise.nil
    · intro e he; cases he
    · show ([] : List LEntry).Pairwise _; exact List.Pairwise.nil
    · intro e he; cases he

theorem reach_tinv {p : Params} {s : Sys} (r : Reach p s) : TInv p s := by
  induction r with
  | init => exact tinv_init p
  | step _ st ih => exact step_tinv ih st

/-- `Swept`: after a timer no record of the dedupe set is older than the ttl and no entry of the log is older than
the log window. -/
theorem swept {p : Params} {s : Sys} (r : Reach p s) (h : s.last = .timer) :
    (∀ e ∈ s.node.seen.order, s.now - e.2 ≤ p.ttl) ∧ (∀ e ∈ s.node.lg.entries, s.now - e.at_ ≤ p.logWin) :=
  (reach_tinv r).swept h

/-- The records of the dedupe set and the entries of the log are in the order of their times in every reachable
state, and none is ahead of the clock. -/
theorem tablesOrdered {p : Params} {s : Sys} (r : Reach p s) :
    s.node.seen.order.Pairwise (fun a b => a.2 ≤ b.2) ∧ (∀ e ∈ s.node.seen.order, e.2 ≤ s.now) ∧
    s.node.lg.entries.Pairwise (fun a b => a.at_ ≤ b.at_) ∧ (∀ e ∈ s.node.lg.entries, e.at_ ≤ s.now) :=
  ⟨(reach_tinv r).seen.1, (reach_tinv r).seen.2, (reach_tinv r).lg.1, (reach_tinv r).lg.2⟩

#audit_axioms Vinc.BroadcastNode.swept
#audit_axioms Vinc.BroadcastNode.tablesOrdered

end Vinc.BroadcastNode
