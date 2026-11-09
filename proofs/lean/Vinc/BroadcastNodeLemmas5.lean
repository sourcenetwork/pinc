import Vinc.BroadcastNodeLemmas4

/-!
# Broadcast node: the receive path and the timer

`Post p N now r` (see `BroadcastNodeLemmas4`) for `HubStore`, `OnMsg` and `OnTimer`, and the facts about
`OnMsg` the system theorems need beyond it: a frame that is not a good message leaves the node unchanged
(`OnMsg_garbage`), a PACK is sent only for a message the hub holds (`OnMsg_ack`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

theorem NoDA.noDel {o : TraceRec} (h : NoDA o) : NoDel o := by cases o <;> simp_all [NoDA, NoDel]

theorem NodeInv.withReq {p : Params} {N : Node} (h : NodeInv p N) (q : List Nat) : NodeInv p {N with req := q} :=
  ⟨h.seen, h.heldLen, h.fholdLen, h.checksLen, h.lgLen, h.acpLen, h.heldNodup, h.fholdNodup, h.checksNodup,
   h.hubPhase, h.memberLg, h.gatherHeld, h.heldNotOld⟩

theorem Post.req {p : Params} {N : Node} {now : Nat} {r : Res} {q : List Nat} (h : Post p {N with req := q} now r) :
    Post p N now r :=
  ⟨h.inv, h.del, h.deny, h.resp, h.delta, h.nodup, h.acc, h.floor, h.phase⟩

/-- A result that delivers nothing, emits only quiet records, keeps the held set, the phase and the birth, and
accounts the ids it records. -/
theorem Post_quiet {p : Params} {N : Node} {now : Nat} {r : Res} (hn : NodeInv p r.n) (hph : r.n.phase = N.phase)
    (hb : r.n.born = N.born) (hheld : r.n.held = N.held) (hdl : r.dl = []) (hq : ∀ o ∈ r.outs, NoDA o)
    (hacc : p.heldFullKeepsUnseen = true → ∀ A, JInv A N → JInv (A ++ r.acc) r.n) : Post p N now r := by
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, hacc, ?_, ?_⟩
  · intro mid org ts via h; exact absurd (hq _ h) (by simp [Plain, NoDA])
  · intro id org h; exact absurd (hq _ h) (by simp [Plain, NoDA])
  · intro mid org ts via h; exact absurd (hq _ h) (by simp [Plain, NoDA])
  · intro x; rw [hdl, hc_eq hheld x]; simp
  · intro _; rw [hdl]; exact List.nodup_nil
  · intro _ _ o ho; exact (hq o ho).noDel
  · intro h; rw [hph] at h; exact ⟨h, hb⟩

theorem Post_req {p : Params} {N : Node} {now : Nat} (hI : NodeInv p N) (q : List Nat) (outs : List TraceRec)
    (a : Nat) (hq : ∀ o ∈ outs, NoDA o) : Post p N now ⟨{N with req := q}, outs, [], a, []⟩ :=
  Post_quiet (hI.withReq q) rfl rfl rfl rfl hq (fun _ A hA => by simpa [JInv] using hA)

theorem Post.congr {p : Params} {N : Node} {now : Nat} {r r' : Res} (h : Post p N now r) (hn : r'.n = r.n)
    (ho : r'.outs = r.outs) (hd : r'.dl = r.dl) (ha : r'.acc = r.acc) : Post p N now r' := by
  cases r; cases r'
  simp only at hn ho hd ha
  subst hn ho hd ha
  exact ⟨h.inv, h.del, h.deny, h.resp, h.delta, h.nodup, h.acc, h.floor, h.phase⟩

/-- A prefix of quiet records changes nothing the postcondition says. -/
theorem Post_prefix {p : Params} {N : Node} {now : Nat} {r : Res} (h : Post p N now r) (o1 : List TraceRec)
    (ho : ∀ o ∈ o1, NoDA o) (a : Nat) : Post p N now ⟨r.n, o1 ++ r.outs, r.dl, a, r.acc⟩ := by
  refine ⟨h.inv, ?_, ?_, ?_, h.delta, h.nodup, h.acc, ?_, h.phase⟩
  · intro mid org ts via hm
    rcases List.mem_append.1 hm with hm | hm
    · exact absurd (ho _ hm) (by simp [Plain, NoDA])
    · obtain ⟨h1, h2⟩ := h.del mid org ts via hm
      exact ⟨h1, fun hv => by
        obtain ⟨id, hid⟩ := h2 hv; exact ⟨id, List.mem_append_right _ hid⟩⟩
  · intro id org hm
    rcases List.mem_append.1 hm with hm | hm
    · exact absurd (ho _ hm) (by simp [Plain, NoDA])
    · obtain ⟨h1, h2⟩ := h.deny id org hm
      exact ⟨h1, fun mid ts via hv => by
        rcases List.mem_append.1 hv with hv | hv
        · exact absurd (ho _ hv) (by simp [Plain, NoDA])
        · exact h2 mid ts via hv⟩
  · intro mid org ts via hm
    rcases List.mem_append.1 hm with hm | hm
    · exact absurd (ho _ hm) (by simp [Plain, NoDA])
    · exact h.resp mid org ts via hm
  · intro hh hg o hom
    rcases List.mem_append.1 hom with hom | hom
    · exact (ho _ hom).noDel
    · exact h.floor hh hg o hom

/-- The result of a chain of offers onto `r0` satisfies the postcondition when the start does. -/
theorem Post_of_chain {p : Params} {N : Node} {now : Nat} {ms : List Nat} {r0 r : Res} (hcap : 0 < p.seenCap)
    (hI0 : NodeInv p r0.n) (T : TransSpec p now ms r0 r) (h0dl : r0.dl = []) (h0q : ∀ o ∈ r0.outs, NoDA o)
    (h0held : r0.n.held = N.held) (hph : r.n.phase = .gathering → N.phase = .gathering ∧ r.n.born = N.born)
    (hms : ∀ x ∈ ms, SContains p r0.n.seen x now = false → SContains p N.seen x now = false)
    (hnd : p.heldDedup = true → ms.Nodup)
    (hS0 : p.heldFullKeepsUnseen = true → ∀ A, JInv A N → ∀ x, r0.n.seen.map x ≠ none → x ∈ A ++ r0.acc)
    (hL0 : p.heldFullKeepsUnseen = true → ∀ A, JInv A N → ∀ x ∈ LIds r0.n.lg, x ∈ A ++ r0.acc ∨ x ∈ r.acc)
    (hfl : p.isHub = false → r.n.phase = .gathering → ∀ o ∈ r.outs, NoDel o) : Post p N now r := by
  have co := chain_outs T h0q
  obtain ⟨dx, hdl, hsub⟩ := T.dl
  refine ⟨T.inv hcap hI0, co.1, ?_, co.2.2, ?_, ?_, ?_, hfl, hph⟩
  · intro id org h; exact absurd h (co.2.1 id false org)
  · intro x
    have d := T.delta x
    have cv := delta_conv (p := p) (now := now) (N := N) (N0 := r0.n) (N' := r.n) (x := x) (ms := ms) hms
    have hh : hc r0.n x = hc N x := hc_eq h0held x
    rw [h0dl] at d
    simp only [List.count_nil] at d
    omega
  · intro hd; rw [hdl, h0dl]; simp only [List.nil_append]; exact (hnd hd).sublist hsub
  · intro hk A hJ
    obtain ⟨e, he⟩ := T.acc
    have lift : ∀ x, x ∈ A ++ r0.acc → x ∈ A ++ r.acc := by
      intro x hx; rw [he]
      rcases List.mem_append.1 hx with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases T.accN hk x hx with h | h
      · exact lift x (hS0 hk A hJ x h)
      · exact List.mem_append_right _ h
    · rw [T.lg] at hx
      rcases hL0 hk A hJ x hx with h | h
      · exact lift x h
      · exact List.mem_append_right _ h

/-! ## The dedupe set under inserts -/

theorem SInsert_map_ne (p : Params) (S : Seen) (i now x t : Nat) (f : Bool) (hx : x ≠ i)
    (h : (SInsert p S i now f).map x = some t) : S.map x = some t := by
  unfold SInsert at h
  split at h
  · split at h
    · rw [SPush_map] at h; simp only [hx, if_false] at h; exact SPopFront_map h
    · exact h
  · rw [SPush_map] at h; simp only [hx, if_false] at h; exact h

theorem SInsertAll_map_ne (p : Params) (now : Nat) (ids : List Nat) :
    ∀ (S : Seen) (x t : Nat), x ∉ ids → (SInsertAll p S now ids).map x = some t → S.map x = some t := by
  induction ids with
  | nil => intro S x t _ h; exact h
  | cons i ids ih =>
    intro S x t hx h
    simp only [List.mem_cons, not_or] at hx
    unfold SInsertAll at h
    have h2 := ih _ x t hx.2 h
    split at h2
    · exact h2
    · exact SInsert_map_ne p S i now x t true hx.1 h2

theorem SInsertAll_contains_ne (p : Params) (now : Nat) (ids : List Nat) (S : Seen) (x : Nat) (hx : x ∉ ids)
    (h : SContains p (SInsertAll p S now ids) x now = true) : SContains p S x now = true := by
  rw [SContains_iff] at h ⊢
  obtain ⟨t, ht, hle⟩ := h
  exact ⟨t, SInsertAll_map_ne p now ids S x t hx ht, hle⟩

theorem NodeInv.withSeenLg {p : Params} {N : Node} (h : NodeInv p N) {S : Seen} {L : Log} (hS : SeenInv p S)
    (hl : L.entries.length ≤ p.logCap) (hm : p.isHub = false → L.entries = []) :
    NodeInv p {N with seen := S, lg := L} :=
  ⟨hS, h.heldLen, h.fholdLen, h.checksLen, hl, h.acpLen, h.heldNodup, h.fholdNodup, h.checksNodup,
   h.hubPhase, hm, h.gatherHeld, h.heldNotOld⟩

theorem QuietRec.noDel {o : TraceRec} (h : QuietRec o) : NoDel o := by cases o <;> simp_all [QuietRec, NoDel]

theorem Post.ack {p : Params} {N : Node} {now : Nat} {r : Res} (h : Post p N now r) (a : Nat) :
    Post p N now {r with ack := a} :=
  ⟨h.inv, h.del, h.deny, h.resp, h.delta, h.nodup, h.acc, h.floor, h.phase⟩

/-! ## `hub_store` -/

theorem HubStore_post {p : Params} {N : Node} {now wall : Nat} {fanned : Bool} {m : Msg} (hcap : 0 < p.seenCap)
    (hhub : p.isHub = true) (hI : NodeInv p N) (hd : SContains p N.seen m.mid now = false)
    (hl : LContains N.lg m.mid = false) : Post p N now (HubStore p N now wall fanned m) := by
  unfold HubStore
  by_cases htf : p.topicFull = true
  · rw [if_pos htf]
    exact Post_req hI N.req _ 0 (by simp [Plain, NoDA])
  · rw [if_neg htf]
    dsimp only
    have PS := LPush_spec p N.lg m.mid now wall m.n
    generalize LPush p N.lg m.mid now wall m.n = rr at PS ⊢
    have hN1 : NodeInv p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} :=
      hI.withSeenLg (SInsertAll_inv hcap rr.ev hI.seen) (PS.len hI.lgLen) (fun h => by rw [hhub] at h; cases h)
    have hJs : ∀ A, JInv A N → ∀ x, (SInsertAll p N.seen now rr.ev).map x ≠ none → x ∈ A := by
      intro A hJ x hx
      rcases SInsertAll_map_sub p now rr.ev N.seen x hx with h | h
      · rcases PS.evSub x h with h | h
        · exact absurd h (by simp)
        · exact hJ.2 x h
      · exact hJ.1 x h
    by_cases hok : rr.ok = true
    · rw [if_neg (by simp [hok])]
      have hnot : m.mid ∉ rr.ev := by
        intro h
        rcases PS.evSub _ h with h | h
        · exact absurd h (by simp)
        · have := (LContains_iff N.lg m.mid).2 h
          rw [hl] at this; cases this
      have hf : SContains p (SInsertAll p N.seen now rr.ev) m.mid now = false := by
        refine Classical.byContradiction fun hc => ?_
        have hc' : SContains p (SInsertAll p N.seen now rr.ev) m.mid now = true := by simpa using hc
        have := SInsertAll_contains_ne p now rr.ev N.seen m.mid hnot hc'
        rw [hd] at this; cases this
      by_cases hsub : (N.sub && m.origin != p.me) = true
      · rw [if_pos hsub]
        have T := offerTrans p now (Plain {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log}
          [.stored m.mid fanned]) m.ent hf
        refine Post_of_chain hcap hN1 T rfl (by simp [Plain, NoDA]) rfl ?_ ?_ (fun _ => by simp [Msg.ent]) ?_ ?_ ?_
        · intro h
          have e : (Bind (Plain {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} [.stored m.mid fanned])
              (fun x => Offer p x now m.ent)).n.phase = .never := T.core.phase.trans (hI.hubPhase hhub)
          rw [e] at h; cases h
        · intro x hx hs; simp [Msg.ent] at hx; subst hx; exact hd
        · intro _ A hJ x hx; exact List.mem_append_left _ (hJs A hJ x hx)
        · intro hk A hJ x hx
          rcases PS.new x hx with h | h
          · exact Or.inl (List.mem_append_left _ (hJ.2 x h))
          · right
            subst h
            exact (((Offer_spec p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} now m.ent).acc hk).2 hhub)
        · intro h; rw [hhub] at h; cases h
      · rw [if_neg hsub]
        refine Post_quiet (hN1.withSeen (SInsert_inv hcap hN1.seen)) rfl rfl rfl rfl (by simp [Plain, NoDA]) ?_
        intro _ A hJ
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · rcases SInsert_map_sub p _ m.mid now x true hx with h | h
          · subst h; simp
          · exact List.mem_append_left _ (hJs A hJ x h)
        · rcases PS.new x hx with h | h
          · exact List.mem_append_left _ (hJ.2 x h)
          · subst h; simp
    · rw [if_pos (by simpa using hok)]
      have hok' : rr.ok = false := by simpa using hok
      refine Post_quiet hN1 rfl rfl rfl rfl (by simp [Plain, NoDA]) ?_
      intro _ A hJ
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · exact List.mem_append_left _ (hJs A hJ x hx)
      · exact List.mem_append_left _ (hJ.2 x (PS.noOk hok' x hx))

/-! ## `on_msg` -/

theorem OnMsg_post {p : Params} {N : Node} {now wall : Nat} {t : Frame} {b : Bool} {m : Msg} (hcap : 0 < p.seenCap)
    (hI : NodeInv p N) : Post p N now (OnMsg p N now wall t b m) := by
  unfold OnMsg
  by_cases h1 : (!Allowed p t b) = true
  · rw [if_pos h1]; exact Post_req hI N.req [] 0 (by simp)
  rw [if_neg h1]
  by_cases h2 : m.kind = .badhead
  · rw [if_pos h2]; exact Post_req hI N.req _ 0 (by simp [Plain, NoDA])
  rw [if_neg h2]
  by_cases h3 : m.kind = .big
  · rw [if_pos h3]; exact Post_req hI N.req _ 0 (by simp [Plain, NoDA])
  rw [if_neg h3]
  dsimp only
  by_cases h4 : IsDup p N m.mid now = true
  · rw [if_pos h4]; exact Post_req hI N.req _ _ (by simp [Plain, NoDA])
  rw [if_neg h4]
  by_cases h5 : p.revoked.contains m.origin = true
  · rw [if_pos h5]; exact Post_req hI N.req _ 0 (by simp [Plain, NoDA])
  rw [if_neg h5]
  by_cases h6 : m.kind = .badsig
  · rw [if_pos h6]; exact Post_req hI N.req _ 0 (by simp [Plain, NoDA])
  rw [if_neg h6]
  have hd : SContains p N.seen m.mid now = false ∧ LContains N.lg m.mid = false := by
    simp only [IsDup, Bool.or_eq_true, not_or] at h4
    simpa using h4
  have ho : ∀ o ∈ (if N.req.contains m.mid = true then [TraceRec.repaired m.mid] else ([] : List TraceRec)), NoDA o := by
    intro o ho; split at ho <;> simp_all [NoDA]
  by_cases hhub : p.isHub = true
  · rw [if_pos hhub]
    apply Post.req (q := N.req.filter (fun x => x != m.mid))
    have hP := HubStore_post (p := p) (N := {N with req := N.req.filter (fun x => x != m.mid)}) (now := now)
      (wall := wall) (fanned := (decide (t = .fan) || decide (t = .fanp))) (m := m) hcap hhub (hI.withReq _) hd.1 hd.2
    have hP2 := Post_prefix hP _ ho 0
    refine Post.congr hP2 ?_ ?_ ?_ ?_ <;> rfl
  · rw [if_neg hhub]
    have hhub' : p.isHub = false := by simpa using hhub
    apply Post.req (q := N.req.filter (fun x => x != m.mid))
    have hI1 := hI.withReq (N.req.filter (fun x => x != m.mid))
    have hf : SContains p {N with req := N.req.filter (fun x => x != m.mid)}.seen m.ent.mid now = false := hd.1
    have T := offerTrans p now
      (⟨{N with req := N.req.filter (fun x => x != m.mid)},
        (if N.req.contains m.mid = true then [TraceRec.repaired m.mid] else []), [], 0, []⟩ : Res) m.ent hf
    have key := Post_of_chain (N := {N with req := N.req.filter (fun x => x != m.mid)}) hcap hI1 T rfl ho rfl
      (fun h => ⟨T.core.phase.symm.trans h |>.symm ▸ rfl, T.core.born⟩) ?_ (fun _ => by simp) ?_ ?_ ?_
    · exact Post.congr key rfl rfl rfl rfl
    · intro x hx _; simp [Msg.ent] at hx; subst hx; exact hd.1
    · intro _ A hJ x hx; exact List.mem_append_left _ (hJ.1 x hx)
    · intro _ A hJ x hx; exact Or.inl (List.mem_append_left _ (hJ.2 x hx))
    · intro _ hg o ho'
      rcases List.mem_append.1 ho' with h | h
      · exact (ho o h).noDel
      · have e : N.phase = .gathering := T.core.phase.symm.trans hg
        exact ((Offer_spec p {N with req := N.req.filter (fun x => x != m.mid)} now m.ent).gath e hhub').2 o h |>.noDel

end Vinc.BroadcastNode
