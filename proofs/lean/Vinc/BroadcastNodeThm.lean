import Vinc.BroadcastNodeLemmas6

/-!
# The node theorems

The unbounded counterpart of the invariants and properties of `proofs/tla/BroadcastNode.tla`, over every reachable
state of one node (`Reach p`, for any parameters with a non-empty dedupe set): the node under any message by any
frame, any timer, any answer to an access check, the floors settled in any way, time passing up to the next
deadline and any restart.

`SInv` collects the invariant; `reach_inv` proves it by induction on `Reach`, from the postconditions of the
operators (`OnMsg_post`, `OnTimer_post`, `AcpAnswer_post`, `FloorsSettled_post`). The named theorems are its
projections, with the names of the TLA properties:
* `epochBound`: an id is delivered at most once per epoch, an epoch being a record the dedupe set made while it held
  none for the id (and a record held by the access check counts against the epoch too);
* `onceNoDup`: no id is delivered twice in one step (with the hold set deduplicating);
* `seenAccounted`: every id the set or the log holds was delivered, held, refused with a reason or dropped for a
  stated cause (with full holds keeping the id unseen);
* `deliveredAllowed`, `denyDrops`, `floorRespected`, `floorHold`, `bounds`, `gatherBound`;
* `ackOnlyStored`: a hub acknowledges only the very message it holds (same id, origin, timestamp and body; the id is
  in the log or the dedupe set, whose print carries the content; a different message under a known id is refused,
  `rival_refused`, and an exact retry is acknowledged after the log let it go, `retry_acked`; a graft of it, its id and signature
  under another body, is acknowledged too, `graft_acked`, and stored never; a copy due no
  acknowledgement compares nothing, `undue_duplicate`); `garbage_inert`: a frame that is not a good message
  changes nothing (`OnMsg_garbage`); `gather_ends`: the first timer past the wait ends the gathering.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

/-! ## Facts about the operators the invariant needs -/

theorem MinOf_le : ∀ (l : List Nat) (x : Nat), x ∈ l → ∃ y, MinOf l = some y ∧ y ≤ x := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons a l ih =>
    intro x hx
    unfold MinOf
    rcases hm : MinOf l with _ | y
    · rcases List.mem_cons.1 hx with rfl | h
      · exact ⟨x, rfl, Nat.le_refl _⟩
      · obtain ⟨z, hz, _⟩ := ih x h; rw [hm] at hz; cases hz
    · simp only
      refine ⟨min a y, rfl, ?_⟩
      rcases List.mem_cons.1 hx with rfl | h
      · exact Nat.min_le_left _ _
      · obtain ⟨z, hz, hle⟩ := ih x h
        rw [hm] at hz; cases hz
        exact Nat.le_trans (Nat.min_le_right _ _) hle

theorem PollTimeout_gather (p : Params) (N : Node) (hg : N.phase = .gathering) :
    ∃ y, PollTimeout p N = some y ∧ y ≤ N.born + p.floorWait + 1 := by
  unfold PollTimeout
  refine MinOf_le _ _ ?_ |>.imp fun y hy => hy
  simp [hg]

theorem TickOk_gather {p : Params} {N : Node} {now : Nat} (h : TickOk p N now = true) (hg : N.phase = .gathering) :
    now + 1 ≤ N.born + p.floorWait + 1 := by
  obtain ⟨y, hy, hle⟩ := PollTimeout_gather p N hg
  unfold TickOk at h
  rw [hy] at h
  simp at h
  omega

theorem FloorsSettled_ack (p : Params) (hcap : 0 < p.seenCap) (N : Node) (now : Nat) (used : Bool)
    (rf : Option Nat) (of_ : Option (Nat → Option Nat)) (nh : Bool) :
    (FloorsSettled p N now used rf of_ nh).ack = 0 := by
  unfold FloorsSettled
  have T := offerAllTrans p now N.fhold (Plain {N with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} [.floorDone used])
  rw [T.ack]; rfl

theorem OnTimer_ack (p : Params) (hcap : 0 < p.seenCap) (N : Node) (now : Nat) : (OnTimer p N now).ack = 0 := by
  unfold OnTimer
  dsimp only
  split
  · exact FloorsSettled_ack p hcap _ _ _ _ _ _
  · rfl

theorem HubStore_stored {p : Params} {N : Node} {now wall : Nat} {fanned : Bool} {m : Msg}
    (hhub : p.isHub = true) :
    (HubStore p N now wall fanned m).ack = 0 ∧
      ((HubStore p N now wall fanned m).outs.any IsStored = true →
        m.mid ∈ LIds (HubStore p N now wall fanned m).n.lg) := by
  unfold HubStore
  by_cases htf : p.topicFull = true
  · rw [if_pos htf]; simp [Plain, IsStored]
  · rw [if_neg htf]
    dsimp only
    have PS := LPush_spec p N.lg m.mid now wall m.n
    generalize LPush p N.lg m.mid now wall m.n = rr at PS ⊢
    by_cases hok : rr.ok = true
    · rw [if_neg (by simp [hok])]
      by_cases hsub : (N.sub && m.origin != p.me) = true
      · rw [if_pos hsub]
        have S := Offer_spec p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} now m.ent
        refine ⟨(Nat.zero_add _).trans S.ack, fun _ => ?_⟩
        show m.mid ∈ LIds (Offer p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} now m.ent).n.lg
        rw [S.lg]
        exact PS.ok hok
      · rw [if_neg hsub]
        exact ⟨rfl, fun _ => PS.ok hok⟩
    · rw [if_pos (by simpa using hok)]
      simp [Plain, IsStored]

theorem OnMsg_garbage {p : Params} {N : Node} {now wall : Nat} {t : Frame} {b : Bool} {m : Msg}
    (h : m.kind ≠ .good) : (OnMsg p N now wall t b m).n = N ∧ (OnMsg p N now wall t b m).dl = [] := by
  unfold OnMsg
  by_cases h1 : (!Allowed p t b) = true
  · rw [if_pos h1]; exact ⟨rfl, rfl⟩
  rw [if_neg h1]
  by_cases h2 : m.kind = .badhead
  · rw [if_pos h2]; exact ⟨rfl, rfl⟩
  rw [if_neg h2]
  by_cases h3 : m.kind = .big
  · rw [if_pos h3]; exact ⟨rfl, rfl⟩
  rw [if_neg h3]
  dsimp only
  by_cases h4 : IsDup p N m.mid now = true
  · rw [if_pos h4]; exact ⟨rfl, rfl⟩
  rw [if_neg h4]
  by_cases h5 : p.revoked.contains m.origin = true
  · rw [if_pos h5]; exact ⟨rfl, rfl⟩
  rw [if_neg h5]
  by_cases h6 : (m.kind = .badsig ∨ m.kind = .graft)
  · rw [if_pos h6]; exact ⟨rfl, rfl⟩
  exfalso
  cases hk : m.kind <;> simp_all

theorem OnMsg_ack {p : Params} {N : Node} {now wall : Nat} {t : Frame} {b : Bool} {m : Msg}
    (hcap : 0 < p.seenCap) (hack : p.ackAfterStore = true) (hI : NodeInv p N)
    (h : 0 < (OnMsg p N now wall t b m).ack) :
    (m.mid ∈ LIds (OnMsg p N now wall t b m).n.lg ∨ (OnMsg p N now wall t b m).n.seen.map m.mid ≠ none) ∧
      (OnMsg p N now wall t b m).n.store m.mid = Print (OnMsg p N now wall t b m).n m := by
  unfold OnMsg at h ⊢
  by_cases h1 : (!Allowed p t b) = true
  · rw [if_pos h1] at h; simp [Plain] at h
  rw [if_neg h1] at h ⊢
  by_cases h2 : m.kind = .badhead
  · rw [if_pos h2] at h; simp [Plain] at h
  rw [if_neg h2] at h ⊢
  by_cases h3 : m.kind = .big
  · rw [if_pos h3] at h; simp [Plain] at h
  rw [if_neg h3] at h ⊢
  dsimp only at h ⊢
  by_cases h4 : IsDup p N m.mid now = true
  · rw [if_pos h4] at h ⊢
    -- a known id is acknowledged only when the node holds this very message's print
    by_cases hs : SameStored N m = true
    · refine ⟨?_, ?_⟩
      · simp only [IsDup, Bool.or_eq_true] at h4
        rcases h4 with h4 | h4
        · right
          rw [SContains_iff] at h4
          obtain ⟨t', ht, _⟩ := h4
          show N.seen.map m.mid ≠ none
          rw [ht]; simp
        · left; exact (LContains_iff N.lg m.mid).1 h4
      · simp only [SameStored, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
        show N.store m.mid = Print N m
        rcases hs with ⟨hg, hst⟩ | hg
        · simp [Print, hg, hst]
        · simp [Print, hg]
    · have hs' : SameStored N m = false := by simpa using hs
      simp [DupRes, hs'] at h
  rw [if_neg h4] at h ⊢
  by_cases h5 : p.revoked.contains m.origin = true
  · rw [if_pos h5] at h; simp [Plain] at h
  rw [if_neg h5] at h ⊢
  by_cases h6 : (m.kind = .badsig ∨ m.kind = .graft)
  · rw [if_pos h6] at h; simp [Plain] at h
  rw [if_neg h6] at h ⊢
  by_cases hhub : p.isHub = true
  · rw [if_pos hhub] at h ⊢
    rw [NoteStored_ack] at h
    have HS := HubStore_stored (p := p) (N := {N with req := N.req.filter (fun x => x != m.mid)}) (now := now)
      (wall := wall) (fanned := (decide (t = .fan) || decide (t = .fanp))) (m := m) hhub
    have hs : (HubStore p {N with req := N.req.filter (fun x => x != m.mid)} now wall
        (decide (t = .fan) || decide (t = .fanp)) m).outs.any IsStored = true := by
      refine Classical.byContradiction fun hs => ?_
      have hany : ∀ (o1 l : List TraceRec), (∀ o ∈ o1, ¬ IsStored o = true) → (o1 ++ l).any IsStored = l.any IsStored := by
        intro o1 l ho
        rw [List.any_append]
        have : o1.any IsStored = false := by
          rw [Bool.eq_false_iff]
          intro hh
          obtain ⟨o, hoo, hio⟩ := List.any_eq_true.1 hh
          exact ho o hoo hio
        rw [this]; rfl
      have ho1 : ∀ o ∈ (if N.req.contains m.mid = true then [TraceRec.repaired m.mid] else ([] : List TraceRec)),
          ¬ IsStored o = true := by
        intro o ho; split at ho <;> simp_all [IsStored]
      simp only [bind_eq, hack, if_true, HS.1, Nat.zero_add, hany _ _ ho1] at h
      have hs' : (HubStore p {N with req := N.req.filter (fun x => x != m.mid)} now wall
          (decide (t = .fan) || decide (t = .fanp)) m).outs.any IsStored = false := by simpa using hs
      simp [hs'] at h
    have hng : ¬ m.kind = .graft := fun hg => h6 (Or.inr hg)
    refine ⟨Or.inl ?_, ?_⟩
    · rw [NoteStored_lg]
      exact HS.2 hs
    · simp only [Print, hng, if_false]
      refine NoteStored_store m _ ?_
      show List.any (_ ++ (HubStore p {N with req := N.req.filter (fun x => x != m.mid)} now wall
        (decide (t = .fan) || decide (t = .fanp)) m).outs) IsStored = true
      rw [List.any_append, hs]
      simp
  · rw [if_neg hhub] at h
    exfalso
    have S := Offer_spec p {N with req := N.req.filter (fun x => x != m.mid)} now m.ent
    simp only [hack, if_true, bind_eq] at h
    have h' : 0 < 0 + (Offer p {N with req := N.req.filter (fun x => x != m.mid)} now m.ent).ack := h
    rw [S.ack] at h'
    exact absurd h' (Nat.lt_irrefl _)

/-- Another message under a held id is not the stored one: the print held for the id is a different content. -/
theorem rival_not_same {N : Node} {m : Msg} {c : Content} (hst : N.store m.mid = some c) (hne : c ≠ m.content)
    (hg : m.kind ≠ .graft) : SameStored N m = false := by
  unfold SameStored
  simp [hst, hne, hg]

/-- A rival PUB or FANP under a known id, after the log let the stored message go as much as while it holds it
(`keepPrint`), is refused with `idTaken` and no acknowledgement. -/
theorem rival_refused {p : Params} {N : Node} {m : Msg} {c : Content} {ack : Nat} (hk : p.keepPrint = true)
    (hack : 0 < ack) (hst : N.store m.mid = some c) (hne : c ≠ m.content) (hg : m.kind ≠ .graft) :
    (DupRes p N m ack).ack = 0 ∧ (DupRes p N m ack).outs = [.rejected m.mid .idTaken] := by
  have hs := rival_not_same hst hne hg
  refine ⟨?_, ?_⟩ <;> simp [DupRes, hs, hk, hack]

/-- A retry of the stored message due an acknowledgement, after the log let it go as much as while it holds it
(`keepPrint`), is acknowledged and is a duplicate. -/
theorem retry_acked {p : Params} {N : Node} {m : Msg} {ack : Nat} (hk : p.keepPrint = true) (hack : 0 < ack)
    (hg : m.kind = .good) (hst : N.store m.mid = some m.content) :
    (DupRes p N m ack).ack = ack ∧ (DupRes p N m ack).outs = [.rejected m.mid .duplicate] := by
  have hs : SameStored N m = true := by simp [SameStored, hg, hst]
  refine ⟨?_, ?_⟩ <;> simp [DupRes, hs, hk, hack]

/-- A graft of the stored message (its id and signature, another body) due an acknowledgement is acknowledged like
the message itself, after the log let it go as much as while it holds it; it is a duplicate, never stored (a known
id changes no state, see `OnMsg_garbage`). -/
theorem graft_acked {p : Params} {N : Node} {m : Msg} {ack : Nat} (hk : p.keepPrint = true) (hack : 0 < ack)
    (hg : m.kind = .graft) :
    (DupRes p N m ack).ack = ack ∧ (DupRes p N m ack).outs = [.rejected m.mid .duplicate] := by
  have hs : SameStored N m = true := by simp [SameStored, hg]
  refine ⟨?_, ?_⟩ <;> simp [DupRes, hs, hk, hack]

/-- A copy due no acknowledgement is a plain duplicate and compares nothing (`dueOnly`). -/
theorem undue_duplicate {p : Params} {N : Node} {m : Msg} (hd : p.dueOnly = true) :
    (DupRes p N m 0).ack = 0 ∧ (DupRes p N m 0).outs = [.rejected m.mid .duplicate] := by
  refine ⟨?_, ?_⟩ <;> simp [DupRes, hd]

/-! ## The system invariant -/

/-- The invariant of a reachable state. -/
structure SInv (p : Params) (s : Sys) : Prop where
  inv : NodeInv p s.node
  epoch : ∀ m, s.cnt m + hc s.node m ≤ s.ep m
  nodup : p.heldDedup = true → s.dls.Nodup
  acct : p.heldFullKeepsUnseen = true → JInv s.acct s.node
  del : DelOK s.node.acp s.now s.outs
  deny : DenyOK s.node.held s.outs
  resp : FreshDel p s.node s.outs
  floor : p.isHub = false → (s.last = .msg ∨ s.last = .timer ∨ s.last = .answer) → s.node.phase = .gathering →
    ∀ o ∈ s.outs, NoDel o
  gather : s.node.phase = .gathering → s.now ≤ s.node.born + p.floorWait + 1
  ack : p.ackAfterStore = true → 0 < s.ackd →
    (s.lm.mid ∈ LIds s.node.lg ∨ s.node.seen.map s.lm.mid ≠ none) ∧ s.node.store s.lm.mid = Print s.node s.lm

theorem sinit_inv (p : Params) : SInv p (SInit p) := by
  refine ⟨NodeInit_inv p 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; simp [SInit, hc, NodeInit]
  · intro _; simp [SInit]
  · intro _; refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simp_all [SInit, NodeInit, SeenEmpty, LEmpty, LIds]
  · intro mid org ts via h; simp [SInit] at h
  · intro id org h; simp [SInit] at h
  · intro mid org ts via h; simp [SInit] at h
  · intro _ _ _ o ho; simp [SInit] at ho
  · intro _; simp [SInit]
  · intro _ h; simp [SInit] at h

theorem apply_inv {p : Params} {s : Sys} {r : Res} {what : Last} {m : Msg} (hcap : 0 < p.seenCap)
    (hs : SInv p s) (P : Post p s.node s.now r) (hlast : what = .msg ∨ what = .timer ∨ what = .answer ∨ what = .floors)
    (hack : p.ackAfterStore = true → 0 < r.ack →
      (m.mid ∈ LIds r.n.lg ∨ r.n.seen.map m.mid ≠ none) ∧ r.n.store m.mid = Print r.n m) :
    SInv p (Apply p s r what m) := by
  refine ⟨P.inv, ?_, P.nodup, ?_, P.del, P.deny, P.resp, ?_, ?_, ?_⟩
  · intro m
    have d := P.delta m
    have e := hs.epoch m
    show s.cnt m + r.dl.count m + hc r.n m ≤ EpG p s.now s.node r.n s.ep m
    unfold EpG
    split <;> rename_i hn <;> simp [hn] at d ⊢ <;> omega
  · intro hk
    exact P.acc hk _ (hs.acct hk)
  · intro hh hl hg
    exact P.floor hh hg
  · intro hg
    obtain ⟨h1, h2⟩ := P.phase hg
    have := hs.gather h1
    show s.now ≤ r.n.born + p.floorWait + 1
    rw [h2]; exact this
  · intro hk hpos
    have hpos' : 0 < r.ack := hpos
    have hl : (Apply p s r what m).lm = m := by simp [Apply, hpos']
    rw [hl]
    exact hack hk hpos'

theorem AcpAnswer_ack (p : Params) (N : Node) (now id : Nat) (allow : Bool) : (AcpAnswer p N now id allow).ack = 0 := by
  unfold AcpAnswer
  rcases hf : N.checks.find? (fun c => c.id == id) with _ | c <;> simp [hf, Plain]

theorem step_inv {p : Params} {s s' : Sys} (hcap : 0 < p.seenCap) (hs : SInv p s) (st : Step p s s') :
    SInv p s' := by
  cases st with
  | msg t b m =>
    exact apply_inv hcap hs (OnMsg_post hcap hs.inv) (Or.inl rfl)
      (fun hk hpos => OnMsg_ack hcap hk hs.inv hpos)
  | timer =>
    exact apply_inv hcap hs (OnTimer_post hcap hs.inv) (Or.inr (Or.inl rfl))
      (fun _ hpos => absurd hpos (by rw [OnTimer_ack p hcap]; exact Nat.lt_irrefl _))
  | answer c hc allow =>
    exact apply_inv hcap hs (AcpAnswer_post hs.inv) (Or.inr (Or.inr (Or.inl rfl)))
      (fun _ hpos => absurd hpos (by rw [AcpAnswer_ack]; exact Nat.lt_irrefl _))
  | floors rf of_ nh h =>
    exact apply_inv hcap hs (FloorsSettled_post hcap hs.inv h true rf of_ nh) (Or.inr (Or.inr (Or.inr rfl)))
      (fun _ hpos => absurd hpos (by rw [FloorsSettled_ack p hcap]; exact Nat.lt_irrefl _))
  | tick h =>
    refine ⟨hs.inv, hs.epoch, ?_, hs.acct, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact List.nodup_nil
    · intro mid org ts via hm; cases hm
    · intro id org hm; cases hm
    · intro mid org ts via hm; cases hm
    · intro _ _ _ o ho; cases ho
    · intro hg; have := TickOk_gather h hg; show s.now + 1 ≤ _; exact this
    · intro _ hpos; exact absurd hpos (Nat.lt_irrefl _)
  | restart =>
    refine ⟨NodeInit_inv p _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro m; simp [Restarted, hc, NodeInit]
    · intro _; exact List.nodup_nil
    · intro _; refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simp_all [Restarted, NodeInit, SeenEmpty, LEmpty, LIds]
    · intro mid org ts via hm; cases hm
    · intro id org hm; cases hm
    · intro mid org ts via hm; cases hm
    · intro _ _ _ o ho; cases ho
    · intro hg; show s.now ≤ s.now + p.floorWait + 1; omega
    · intro _ hpos; exact absurd hpos (Nat.lt_irrefl _)

theorem reach_inv {p : Params} {s : Sys} (hcap : 0 < p.seenCap) (r : Reach p s) : SInv p s := by
  induction r with
  | init => exact sinit_inv p
  | step _ st ih => exact step_inv hcap ih st

section Named
variable {p : Params} {s : Sys} (hcap : 0 < p.seenCap) (r : Reach p s)
include hcap r

/-- An id is delivered, in all the epochs so far, at most as often as there were epochs (and a held copy counts). -/
theorem epochBound : ∀ m, s.cnt m ≤ s.ep m := fun m => by
  have := (reach_inv hcap r).epoch m; omega

theorem onceNoDup (h : p.heldDedup = true) : s.dls.Nodup := (reach_inv hcap r).nodup h

theorem seenAccounted (h : p.heldFullKeepsUnseen = true) :
    (∀ x, s.node.seen.map x ≠ none → x ∈ s.acct) ∧ (∀ x ∈ LIds s.node.lg, x ∈ s.acct) := (reach_inv hcap r).acct h

theorem deliveredAllowed : DelOK s.node.acp s.now s.outs := (reach_inv hcap r).del

theorem denyDrops : DenyOK s.node.held s.outs := (reach_inv hcap r).deny

theorem floorRespected : FreshDel p s.node s.outs := (reach_inv hcap r).resp

theorem bounds : s.node.held.length ≤ p.heldMax ∧ s.node.fhold.length ≤ p.fholdMax ∧
    s.node.checks.length ≤ p.checksMax ∧ s.node.seen.order.length ≤ p.seenCap ∧ s.node.lg.entries.length ≤ p.logCap ∧
    s.node.acp.length ≤ p.acpMax :=
  have h := (reach_inv hcap r).inv
  ⟨h.heldLen, h.fholdLen, h.checksLen, h.seen.len, h.lgLen, h.acpLen⟩

theorem floorHold (hh : p.isHub = false) (hl : s.last = .msg ∨ s.last = .timer ∨ s.last = .answer)
    (hg : s.node.phase = .gathering) : ∀ o ∈ s.outs, NoDel o := (reach_inv hcap r).floor hh hl hg

theorem gatherBound (h : s.node.phase = .gathering) : s.now ≤ s.node.born + p.floorWait + 1 :=
  (reach_inv hcap r).gather h

theorem ackOnlyStored (hk : p.ackAfterStore = true) (h : 0 < s.ackd) :
    (s.lm.mid ∈ LIds s.node.lg ∨ s.node.seen.map s.lm.mid ≠ none) ∧ s.node.store s.lm.mid = Print s.node s.lm :=
  (reach_inv hcap r).ack hk h

end Named

/-- A step whose message is not a good one changes nothing but the records. -/
theorem garbage_inert {p : Params} {s s' : Sys} {t : Frame} {b : Bool} {m : Msg} (h : m.kind ≠ .good)
    (st : s' = Apply p s (OnMsg p s.node s.now s.now t b m) .msg m) : s'.node = s.node ∧ s'.dls = [] := by
  subst st
  exact OnMsg_garbage h

/-- The first timer past the wait ends the gathering. -/
theorem gather_ends {p : Params} {N : Node} {now : Nat} (hg : N.phase = .gathering) (h : p.floorWait < now - N.born) :
    (OnTimer p N now).n.phase ≠ .gathering := by
  unfold OnTimer
  dsimp only
  rw [if_pos ⟨hg, h⟩]
  unfold FloorsSettled
  have T := offerAllTrans p now (Sweep p N now).fhold
    (Plain {Sweep p N now with phase := .done, rfloor := none, ofloor := none, nohist := false, fhold := []} [.floorDone false])
  rw [T.core.phase]
  simp [Plain]

theorem lk_cons_ne (o k : Nat) (w : AcpE) (l : List (Nat × AcpE)) (h : o ≠ k) :
    List.lookup o ((k, w) :: l) = List.lookup o l := by
  simp [List.lookup, beq_false_of_ne h]

theorem lk_cons_eq (o : Nat) (w : AcpE) (l : List (Nat × AcpE)) : List.lookup o ((o, w) :: l) = some w := by
  unfold List.lookup; simp

theorem lookup_map_upd (o : Nat) (v : AcpE) : ∀ L : List (Nat × AcpE),
    (L.map (fun e => if e.1 == o then (o, v) else e)).lookup o = if (L.lookup o).isSome then some v else none := by
  intro L
  induction L with
  | nil => simp
  | cons a l ih =>
    obtain ⟨k, w⟩ := a
    by_cases h : k = o
    · subst h
      rw [List.map_cons, lk_cons_eq]
      simp [lk_cons_eq]
    · have h' : o ≠ k := fun e => h e.symm
      have hf : (if ((k, w).1 == o) = true then (o, v) else (k, w)) = (k, w) := by
        simp [beq_false_of_ne h]
      rw [List.map_cons, hf, lk_cons_ne o k w _ h', ih, lk_cons_ne o k w _ h']

theorem lookup_append_new (o : Nat) (v : AcpE) : ∀ L : List (Nat × AcpE), L.lookup o = none →
    (L ++ [(o, v)]).lookup o = some v := by
  intro L
  induction L with
  | nil => intro _; exact lk_cons_eq o v []
  | cons a l ih =>
    intro h
    obtain ⟨k, w⟩ := a
    have hb : o ≠ k := by
      intro e; subst e; rw [lk_cons_eq] at h; cases h
    rw [lk_cons_ne o k w _ hb] at h
    rw [List.cons_append, lk_cons_ne o k w _ hb]
    exact ih h

/-- A verdict that the table holds for the origin it answered is the answer just given, trusted until `acpCap` after
now (and no entry is made when the table is full of other origins). -/
theorem AcpAnswer_cached {p : Params} {N : Node} {now id : Nat} {allow : Bool} {c : Check}
    (hf : N.checks.find? (fun c => c.id == id) = some c) (e : AcpE)
    (he : (AcpAnswer p N now id allow).n.acp.lookup c.origin = some e) :
    e.exp = now + p.acpCap ∧ e.allow = allow := by
  unfold AcpAnswer at he
  simp only [hf] at he
  by_cases h1 : (N.acp.lookup c.origin).isSome = true
  · simp only [h1, Bool.true_or, if_true, lookup_map_upd] at he
    simp at he
    rw [← he]; exact ⟨rfl, rfl⟩
  · have h1' : N.acp.lookup c.origin = none := by
      cases hh : N.acp.lookup c.origin
      · rfl
      · simp [hh] at h1
    by_cases h2 : N.acp.length < p.acpMax
    · simp only [h1, h2, Bool.false_or, decide_true, if_true, Bool.false_eq_true, if_false] at he
      rw [lookup_append_new _ _ _ h1'] at he
      cases he; exact ⟨rfl, rfl⟩
    · have h2' : decide (N.acp.length < p.acpMax) = false := decide_eq_false h2
      simp only [h1, h2', Bool.false_or, Bool.false_eq_true, if_false] at he
      rw [h1'] at he; cases he

#audit_axioms Vinc.BroadcastNode.AcpAnswer_cached

#audit_axioms Vinc.BroadcastNode.reach_inv
#audit_axioms Vinc.BroadcastNode.epochBound
#audit_axioms Vinc.BroadcastNode.onceNoDup
#audit_axioms Vinc.BroadcastNode.seenAccounted
#audit_axioms Vinc.BroadcastNode.deliveredAllowed
#audit_axioms Vinc.BroadcastNode.denyDrops
#audit_axioms Vinc.BroadcastNode.floorRespected
#audit_axioms Vinc.BroadcastNode.bounds
#audit_axioms Vinc.BroadcastNode.floorHold
#audit_axioms Vinc.BroadcastNode.gatherBound
#audit_axioms Vinc.BroadcastNode.ackOnlyStored
#audit_axioms Vinc.BroadcastNode.rival_not_same
#audit_axioms Vinc.BroadcastNode.rival_refused
#audit_axioms Vinc.BroadcastNode.retry_acked
#audit_axioms Vinc.BroadcastNode.graft_acked
#audit_axioms Vinc.BroadcastNode.undue_duplicate
#audit_axioms Vinc.BroadcastNode.garbage_inert
#audit_axioms Vinc.BroadcastNode.gather_ends

end Vinc.BroadcastNode
