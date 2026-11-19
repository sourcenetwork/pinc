import Pinc.BroadcastNodeLemmas1

/-!
# Broadcast node: the node invariant and the offer path

`NodeInv` (bounds, distinctness, the hub and member roles, the floors) is true at `NodeInit`. `OfferSpec` states what
`Offer` guarantees, proved once from the case split `OfferForm`; the later files combine it for `OfferAll`,
`HubStore`, `OnMsg`, `AcpAnswer`, `OnTimer`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Pinc.BroadcastNode

/-! ## The node invariant and the shape of `Offer` -/

/-- Number of held entries with the id. -/
def hc (N : Node) (x : Nat) : Nat := (N.held.map (·.mid)).count x

/-- What the operators leave alone: the verdict table, the phase, the floors, the subscription. -/
structure Core (N N' : Node) : Prop where
  acp : N'.acp = N.acp
  phase : N'.phase = N.phase
  rfloor : N'.rfloor = N.rfloor
  ofloor : N'.ofloor = N.ofloor
  nohist : N'.nohist = N.nohist
  born : N'.born = N.born
  sub : N'.sub = N.sub

theorem Core.refl (N : Node) : Core N N := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Core.trans {A B C : Node} (h1 : Core A B) (h2 : Core B C) : Core A C :=
  ⟨h2.acp.trans h1.acp, h2.phase.trans h1.phase, h2.rfloor.trans h1.rfloor, h2.ofloor.trans h1.ofloor,
   h2.nohist.trans h1.nohist, h2.born.trans h1.born, h2.sub.trans h1.sub⟩

theorem Core.isOld {p : Params} {N N' : Node} (h : Core N N') (o t : Nat) : IsOld p N' o t = IsOld p N o t := by
  simp only [IsOld, h.ofloor, h.rfloor, h.nohist, h.born]

/-- The invariant of a node, true at `NodeInit` and kept by every operator. -/
structure NodeInv (p : Params) (N : Node) : Prop where
  seen : SeenInv p N.seen
  heldLen : N.held.length ≤ p.heldMax
  fholdLen : N.fhold.length ≤ p.fholdMax
  checksLen : N.checks.length ≤ p.checksMax
  lgLen : N.lg.entries.length ≤ p.logCap
  acpLen : N.acp.length ≤ p.acpMax
  heldNodup : p.heldDedup = true → (N.held.map (·.mid)).Nodup
  fholdNodup : (N.fhold.map (·.mid)).Nodup
  checksNodup : (N.checks.map (·.origin)).Nodup
  hubPhase : p.isHub = true → N.phase = .never
  memberLg : p.isHub = false → N.lg.entries = []
  gatherHeld : p.isHub = false → N.phase = .gathering → N.held = []
  heldNotOld : ∀ e ∈ N.held, IsOld p N e.origin e.ts = false

theorem NodeInit_inv (p : Params) (born : Nat) : NodeInv p (NodeInit p born) := by
  refine ⟨SeenEmpty_inv p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NodeInit, LEmpty]
  · intro h; simp [h]

theorem NodeInv.withSeen {p : Params} {N : Node} (h : NodeInv p N) {S : Seen} (hS : SeenInv p S) :
    NodeInv p {N with seen := S} :=
  ⟨hS, h.heldLen, h.fholdLen, h.checksLen, h.lgLen, h.acpLen, h.heldNodup, h.fholdNodup, h.checksNodup,
   h.hubPhase, h.memberLg, h.gatherHeld, h.heldNotOld⟩

theorem nodup_snoc {α : Type} {l : List α} {a : α} (h : l.Nodup) (ha : a ∉ l) : (l ++ [a]).Nodup :=
  List.nodup_append.2 ⟨h, by simp, fun x hx y hy => by
    simp only [List.mem_singleton] at hy; subst hy; exact fun e => ha (e ▸ hx)⟩

theorem HoldFloor_inv {p : Params} {N : Node} (h : NodeInv p N) (m : Ent) : NodeInv p (HoldFloor p N m).n := by
  unfold HoldFloor
  split
  · exact h
  · rename_i hc
    rcases not_or.1 hc with ⟨h1, h2⟩
    have h1' : N.fhold.length < p.fholdMax := Nat.lt_of_not_le h1
    have h2' : ∀ x ∈ N.fhold, x.mid ≠ m.mid := by simpa [List.any_eq_true] using h2
    refine ⟨h.seen, h.heldLen, ?_, h.checksLen, h.lgLen, h.acpLen, h.heldNodup, ?_, h.checksNodup,
      h.hubPhase, h.memberLg, h.gatherHeld, h.heldNotOld⟩
    · simp [Plain]; omega
    · simp only [Plain, List.map_append, List.map_cons, List.map_nil]
      apply nodup_snoc h.fholdNodup
      intro hm
      obtain ⟨x, hx, hxm⟩ := List.mem_map.1 hm
      exact h2' x hx hxm

theorem bool_dedup (a b : Bool) (h : (!(a && b)) = true) : a = true → b = false := by
  cases a <;> cases b <;> simp_all

/-- What `HoldAndAsk` does to the node: it may append the message to the held set and a check to the checks. -/
theorem HoldAndAsk_shape (p : Params) (N : Node) (m : Ent) :
    ∃ (hd : List Ent) (ch : List Check) (nc : Nat),
      (HoldAndAsk p N m).n = {N with held := N.held ++ hd, checks := N.checks ++ ch, nextCheck := nc} ∧
      (hd = [] ∨ (hd = [m] ∧ N.held.length < p.heldMax ∧ (p.heldDedup = true → HeldHas N m.mid = false))) ∧
      (ch = [] ∨ (ch.length = 1 ∧ (∀ c ∈ ch, c.origin = m.origin) ∧ AskedFor N m.origin = false ∧
        N.checks.length < p.checksMax)) := by
  unfold HoldAndAsk; dsimp only
  by_cases hh : (decide (N.held.length < p.heldMax) && !(p.heldDedup && HeldHas N m.mid)) = true
  · have h1 := hh; rw [Bool.and_eq_true] at h1
    have h1a : N.held.length < p.heldMax := of_decide_eq_true h1.1
    have h1b := bool_dedup _ _ h1.2
    simp only [hh, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte]
    by_cases ha : (!AskedFor {N with held := N.held ++ [m]} m.origin && decide ((N.checks).length < p.checksMax)) = true
    · have h2 := ha; rw [Bool.and_eq_true] at h2
      have h2a : AskedFor N m.origin = false := by simpa [AskedFor] using h2.1
      have h2b : N.checks.length < p.checksMax := of_decide_eq_true h2.2
      simp only [ha, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte]
      exact ⟨[m], [⟨N.nextCheck, m.origin⟩], N.nextCheck + 1, rfl, Or.inr ⟨rfl, h1a, h1b⟩, Or.inr ⟨rfl, by simp, h2a, h2b⟩⟩
    · simp only [ha, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte]
      exact ⟨[m], [], N.nextCheck, by simp, Or.inr ⟨rfl, h1a, h1b⟩, Or.inl rfl⟩
  · simp only [hh, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte]
    by_cases ha : (!AskedFor N m.origin && decide ((N.checks).length < p.checksMax)) = true
    · have h2 := ha; rw [Bool.and_eq_true] at h2
      have h2a : AskedFor N m.origin = false := by simpa using h2.1
      have h2b : N.checks.length < p.checksMax := of_decide_eq_true h2.2
      simp only [ha, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte]
      exact ⟨[], [⟨N.nextCheck, m.origin⟩], N.nextCheck + 1, by simp, Or.inl rfl, Or.inr ⟨rfl, by simp, h2a, h2b⟩⟩
    · simp only [ha, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte]
      exact ⟨[], [], N.nextCheck, by cases N; simp, Or.inl rfl, Or.inl rfl⟩


theorem HeldHas_false {N : Node} {mid : Nat} (h : HeldHas N mid = false) : ∀ e ∈ N.held, e.mid ≠ mid := by
  simpa [HeldHas, List.any_eq_true] using h

theorem AskedFor_false {N : Node} {o : Nat} (h : AskedFor N o = false) : ∀ c ∈ N.checks, c.origin ≠ o := by
  simpa [AskedFor, List.any_eq_true] using h

theorem HoldAndAsk_inv {p : Params} {N : Node} (h : NodeInv p N) (m : Ent)
    (hO : IsOld p N m.origin m.ts = false ∨ p.heldMax ≤ N.held.length)
    (hg : p.isHub = false → N.phase = .gathering → False) : NodeInv p (HoldAndAsk p N m).n := by
  obtain ⟨hd, ch, nc, hn, hhd, hch⟩ := HoldAndAsk_shape p N m
  rw [hn]
  refine ⟨h.seen, ?_, h.fholdLen, ?_, h.lgLen, h.acpLen, ?_, h.fholdNodup, ?_, h.hubPhase, h.memberLg,
    fun a b => (hg a b).elim, ?_⟩
  · rcases hhd with rfl | ⟨rfl, h1, _⟩
    · simpa using h.heldLen
    · simp; omega
  · rcases hch with rfl | ⟨h1, _, _, h2⟩
    · simpa using h.checksLen
    · simp; omega
  · intro hdd
    rcases hhd with rfl | ⟨rfl, _, h2⟩
    · simpa using h.heldNodup hdd
    · simp only [List.map_append, List.map_cons, List.map_nil]
      apply nodup_snoc (h.heldNodup hdd)
      intro hm
      obtain ⟨x, hx, hxm⟩ := List.mem_map.1 hm
      exact HeldHas_false (h2 hdd) x hx hxm
  · rcases hch with rfl | ⟨h1, h2, h3, _⟩
    · simpa using h.checksNodup
    · simp only [List.map_append]
      match ch, h1, h2 with
      | [c], _, h2 =>
        simp only [List.map_cons, List.map_nil]
        apply nodup_snoc h.checksNodup
        intro hm
        obtain ⟨x, hx, hxm⟩ := List.mem_map.1 hm
        have := h2 c (by simp)
        exact AskedFor_false h3 x hx (hxm.trans this)
  · intro e he
    simp only [List.mem_append] at he
    rcases he with he | he
    · exact h.heldNotOld e he
    · rcases hhd with rfl | ⟨rfl, h1, _⟩
      · simp at he
      · simp at he; subst he
        rcases hO with hO | hO
        · exact hO
        · omega


/-- The node `Offer` continues with once the id is recorded. -/
def N1of (p : Params) (N : Node) (now : Nat) (m : Ent) : Node := {N with seen := SInsert p N.seen m.mid now false}

/-- The cases of `Offer`, each with the facts that select it. -/
inductive OfferForm (p : Params) (N : Node) (now : Nat) (m : Ent) : Res → Prop where
  | topic : p.topicFull = true → OfferForm p N now m ⟨N, [.rejected m.mid .topicsFull], [], 0, [m.mid]⟩
  | seenFull : p.topicFull = false → p.seenCap ≤ N.seen.order.length →
      OfferForm p N now m ⟨N, [.rejected m.mid .seenFull], [], 0, [m.mid]⟩
  | floor : p.topicFull = false → N.seen.order.length < p.seenCap → N.phase = .gathering → p.isHub = false →
      OfferForm p N now m (HoldFloor p N m)
  | full : p.topicFull = false → N.seen.order.length < p.seenCap → ¬(N.phase = .gathering ∧ p.isHub = false) →
      p.heldFullKeepsUnseen = true → p.heldMax ≤ N.held.length →
      OfferForm p N now m ⟨(HoldAndAsk p N m).n, (HoldAndAsk p N m).outs ++ [.rejected m.mid .heldFull], [], 0, [m.mid]⟩
  | skip : p.topicFull = false → N.seen.order.length < p.seenCap → ¬(N.phase = .gathering ∧ p.isHub = false) →
      OfferForm p N now m ⟨N1of p N now m, if IsOld p N m.origin m.ts then [.rejected m.mid .old] else [], [], 0, [m.mid]⟩
  | deliver : p.topicFull = false → N.seen.order.length < p.seenCap → ¬(N.phase = .gathering ∧ p.isHub = false) →
      N.sub = true → IsOld p N m.origin m.ts = false → m.origin ≠ p.me → ∀ e, N.acp.lookup m.origin = some e →
      now ≤ e.exp → e.allow = true →
      OfferForm p N now m ⟨N1of p N now m, [.delivered m.mid m.origin m.ts .cache], [m.mid], 0, [m.mid]⟩
  | deny : p.topicFull = false → N.seen.order.length < p.seenCap → ¬(N.phase = .gathering ∧ p.isHub = false) →
      OfferForm p N now m ⟨N1of p N now m, [], [], 0, [m.mid]⟩
  | ask : p.topicFull = false → N.seen.order.length < p.seenCap → ¬(N.phase = .gathering ∧ p.isHub = false) →
      IsOld p N m.origin m.ts = false →
      OfferForm p N now m (HoldAndAsk p (N1of p N now m) m)

theorem Offer_form (p : Params) (N : Node) (now : Nat) (m : Ent) : OfferForm p N now m (Offer p N now m) := by
  unfold Offer
  split
  · rename_i h; exact .topic h
  · rename_i h1
    have h1' : p.topicFull = false := by simpa using h1
    split
    · rename_i h2; exact .seenFull h1' h2
    · rename_i h2
      have h2' : N.seen.order.length < p.seenCap := Nat.lt_of_not_le h2
      dsimp only
      split
      · rename_i h3; exact .floor h1' h2' h3.1 (by simpa using h3.2)
      · rename_i h3
        have h3' : ¬(N.phase = .gathering ∧ p.isHub = false) := by simpa using h3
        rcases ha : N.acp.lookup m.origin with _ | e
        · simp only [Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
          split
          · rename_i h4
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
            obtain ⟨⟨⟨_, hk⟩, hlen⟩, _⟩ := h4
            exact .full h1' h2' h3' hk hlen
          · rename_i h4
            split
            · exact .skip h1' h2' h3'
            · rename_i h5
              simp at h5
              exact .ask h1' h2' h3' h5.1.2
        · simp only [ha]
          split
          · rename_i h4
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
            obtain ⟨⟨⟨_, hk⟩, hlen⟩, _⟩ := h4
            exact .full h1' h2' h3' hk hlen
          · rename_i h4
            split
            · exact .skip h1' h2' h3'
            · rename_i h5
              simp at h5
              split
              · rename_i h6
                simp at h6
                split
                · rename_i h7
                  exact .deliver h1' h2' h3' h5.1.1 h5.1.2 h5.2 e ha h6 h7
                · exact .deny h1' h2' h3'
              · exact .ask h1' h2' h3' h5.1.2


/-! ## What the offer path emits -/

/-- A record the offer path may emit: not `Stored`, not `AcpAnswered`, a delivery only from the cache. -/
def OfferRec : TraceRec → Prop
  | .stored .. => False
  | .acpAnswered .. => False
  | .delivered _ _ _ v => v = .cache
  | _ => True

/-- A record that is none of `Stored`, `AcpAnswered`, `Delivered`. -/
def QuietRec : TraceRec → Prop
  | .stored .. => False
  | .acpAnswered .. => False
  | .delivered .. => False
  | _ => True

/-- Every delivered record of `outs` came from the cache and the cache entry allows it at `now`. -/
def CacheGood (acp : List (Nat × AcpE)) (now : Nat) (outs : List TraceRec) : Prop :=
  ∀ mid org ts, TraceRec.delivered mid org ts .cache ∈ outs → ∃ e, acp.lookup org = some e ∧ e.allow = true ∧ now ≤ e.exp

/-- No delivered record of `outs` is at or below the floors of `N`. -/
def FreshDel (p : Params) (N : Node) (outs : List TraceRec) : Prop :=
  ∀ mid org ts via, TraceRec.delivered mid org ts via ∈ outs → IsOld p N org ts = false

theorem QuietRec.offer {o : TraceRec} (h : QuietRec o) : OfferRec o := by
  cases o <;> simp_all [QuietRec, OfferRec]

theorem HoldFloor_quiet (p : Params) (N : Node) (m : Ent) : ∀ o ∈ (HoldFloor p N m).outs, QuietRec o := by
  intro o ho; unfold HoldFloor at ho; split at ho <;> simp_all [Plain, QuietRec]

theorem HoldAndAsk_quiet (p : Params) (N : Node) (m : Ent) : ∀ o ∈ (HoldAndAsk p N m).outs, QuietRec o := by
  intro o ho; unfold HoldAndAsk at ho; dsimp only at ho
  simp only [List.mem_append] at ho
  rcases ho with ho | ho <;> split at ho <;> simp_all [QuietRec]

theorem HoldAndAsk_dl (p : Params) (N : Node) (m : Ent) : (HoldAndAsk p N m).dl = [] ∧ (HoldAndAsk p N m).ack = 0 := by
  simp [HoldAndAsk]

theorem HoldAndAsk_acc (p : Params) (N : Node) (m : Ent) (h : p.heldFullKeepsUnseen = true) :
    (HoldAndAsk p N m).acc = [m.mid] := by
  simp [HoldAndAsk, h]


theorem HoldAndAsk_frame (p : Params) (X : Node) (m : Ent) :
    Core X (HoldAndAsk p X m).n ∧ (HoldAndAsk p X m).n.seen = X.seen ∧ (HoldAndAsk p X m).n.lg = X.lg ∧
    (HoldAndAsk p X m).n.req = X.req ∧ (HoldAndAsk p X m).n.fhold = X.fhold := by
  obtain ⟨hd, ch, nc, hn, _, _⟩ := HoldAndAsk_shape p X m
  rw [hn]; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem HoldAndAsk_held (p : Params) (X : Node) (m : Ent) :
    (HoldAndAsk p X m).n.held = X.held ∨ ((HoldAndAsk p X m).n.held = X.held ++ [m] ∧ X.held.length < p.heldMax) := by
  obtain ⟨hd, ch, nc, hn, hhd, _⟩ := HoldAndAsk_shape p X m
  rw [hn]
  rcases hhd with rfl | ⟨rfl, h1, _⟩
  · left; simp
  · right; exact ⟨rfl, h1⟩

theorem HoldFloor_frame (p : Params) (N : Node) (m : Ent) :
    Core N (HoldFloor p N m).n ∧ (HoldFloor p N m).n.seen = N.seen ∧ (HoldFloor p N m).n.lg = N.lg ∧
    (HoldFloor p N m).n.req = N.req ∧ (HoldFloor p N m).n.held = N.held ∧ (HoldFloor p N m).dl = [] ∧
    (HoldFloor p N m).ack = 0 ∧ (HoldFloor p N m).acc = [] := by
  unfold HoldFloor; split <;> exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SInsert_nf {p : Params} {S : Seen} (mid now : Nat) (f : Bool) (hl : S.order.length < p.seenCap) :
    SInsert p S mid now f = SPush S mid now := by
  unfold SInsert; simp [Nat.not_le.2 hl]

theorem N1_contains {p : Params} {S : Seen} (mid now : Nat) (hl : S.order.length < p.seenCap) :
    SContains p (SInsert p S mid now false) mid now = true := by
  rw [SInsert_nf mid now false hl]; exact SPush_contains_self p S mid now

theorem N1_mono {p : Params} {S : Seen} (mid now x : Nat) (hl : S.order.length < p.seenCap)
    (h : SContains p S x now = true) : SContains p (SInsert p S mid now false) x now = true := by
  rw [SInsert_nf mid now false hl]; exact SPush_contains_mono p S mid now x h

/-- Everything `Offer` guarantees. -/
structure OfferSpec (p : Params) (N : Node) (now : Nat) (m : Ent) (r : Res) : Prop where
  core : Core N r.n
  lg : r.n.lg = N.lg
  req : r.n.req = N.req
  inv : 0 < p.seenCap → NodeInv p N → NodeInv p r.n
  outs : ∀ o ∈ r.outs, OfferRec o
  cache : CacheGood N.acp now r.outs
  fresh : FreshDel p N r.outs
  ack : r.ack = 0
  held : (r.dl = [] ∧ (r.n.held = N.held ∨ r.n.held = N.held ++ [m])) ∨ (r.dl = [m.mid] ∧ r.n.held = N.held)
  hit : (r.n.held ≠ N.held ∨ r.dl ≠ []) → SContains p r.n.seen m.mid now = true
  mono : ∀ x, SContains p N.seen x now = true → SContains p r.n.seen x now = true
  gath : N.phase = .gathering → p.isHub = false → r.dl = [] ∧ ∀ o ∈ r.outs, QuietRec o
  acc : p.heldFullKeepsUnseen = true →
    (∀ x, r.n.seen.map x ≠ none → N.seen.map x ≠ none ∨ x ∈ r.acc) ∧ (p.isHub = true → m.mid ∈ r.acc)

theorem OfferSpec_of_form {p : Params} {N : Node} {now : Nat} {m : Ent} {r : Res}
    (hf : OfferForm p N now m r) : OfferSpec p N now m r := by
  cases hf with
  | topic h =>
    exact ⟨Core.refl N, rfl, rfl, fun _ hI => hI, by simp [OfferRec], by simp [CacheGood], by simp [FreshDel],
      rfl, Or.inl ⟨rfl, Or.inl rfl⟩, by simp, fun x hx => hx, fun _ _ => ⟨rfl, by simp [QuietRec]⟩,
      fun _ => ⟨fun x hx => Or.inl hx, fun _ => by simp⟩⟩
  | seenFull h1 h2 =>
    exact ⟨Core.refl N, rfl, rfl, fun _ hI => hI, by simp [OfferRec], by simp [CacheGood], by simp [FreshDel],
      rfl, Or.inl ⟨rfl, Or.inl rfl⟩, by simp, fun x hx => hx, fun _ _ => ⟨rfl, by simp [QuietRec]⟩,
      fun _ => ⟨fun x hx => Or.inl hx, fun _ => by simp⟩⟩
  | floor h1 h2 h3 h4 =>
    obtain ⟨c, s, lg, rq, hh, dl, ak, ac⟩ := HoldFloor_frame p N m
    refine ⟨c, lg, rq, fun _ hI => HoldFloor_inv hI m, fun o ho => (HoldFloor_quiet p N m o ho).offer, ?_, ?_, ak,
      Or.inl ⟨dl, Or.inl hh⟩, ?_, ?_, fun _ _ => ⟨dl, HoldFloor_quiet p N m⟩, ?_⟩
    · intro mid org ts h; exact absurd (HoldFloor_quiet p N m _ h) (by simp [QuietRec])
    · intro mid org ts via h; exact absurd (HoldFloor_quiet p N m _ h) (by simp [QuietRec])
    · intro h; rcases h with h | h; exact absurd hh h; exact absurd dl h
    · intro x hx; rw [s]; exact hx
    · intro _
      refine ⟨fun x hx => Or.inl (by rwa [s] at hx), fun hh => by simp_all⟩
  | full h1 h2 h3 h4 h5 =>
    obtain ⟨c, s, lg, rq, fh⟩ := HoldAndAsk_frame p N m
    have hh : (HoldAndAsk p N m).n.held = N.held := by
      rcases HoldAndAsk_held p N m with h | ⟨_, h⟩
      · exact h
      · omega
    refine ⟨c, lg, rq, fun hc hI => HoldAndAsk_inv hI m (Or.inr h5) (fun a b => h3 ⟨b, a⟩), ?_, ?_, ?_, rfl,
      Or.inl ⟨rfl, Or.inl hh⟩, ?_, ?_, fun hg hh2 => absurd ⟨hg, hh2⟩ h3, ?_⟩
    · intro o ho
      simp only [List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · exact (HoldAndAsk_quiet p N m o ho).offer
      · simp [OfferRec]
    · intro mid org ts h
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact absurd (HoldAndAsk_quiet p N m _ h) (by simp [QuietRec])
      · cases h
    · intro mid org ts via h
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact absurd (HoldAndAsk_quiet p N m _ h) (by simp [QuietRec])
      · cases h
    · intro h; rcases h with h | h; exact absurd hh h; exact absurd rfl h
    · intro x hx; rw [s]; exact hx
    · intro _
      exact ⟨fun x hx => Or.inl (by rwa [s] at hx), fun _ => by simp⟩
  | skip h1 h2 h3 =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, fun hc hI => hI.withSeen (SInsert_inv hc hI.seen),
      by intro o ho; split at ho <;> simp_all [OfferRec], by intro mid org ts h; split at h <;> simp_all,
      by intro mid org ts via h; split at h <;> simp_all, rfl, Or.inl ⟨rfl, Or.inl rfl⟩,
      by intro h; rcases h with h | h; exact absurd rfl h; simp at h, fun x hx => N1_mono _ _ x h2 hx,
      fun hg hh2 => absurd ⟨hg, hh2⟩ h3, ?_⟩
    intro hk
    refine ⟨fun x hx => ?_, fun _ => by simp⟩
    rcases SInsert_map_sub p N.seen m.mid now x false hx with h | h
    · exact Or.inr (by simp [h])
    · exact Or.inl h
  | deliver h1 h2 h3 hs ho hm e he hexp hal =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, fun hc hI => hI.withSeen (SInsert_inv hc hI.seen),
      by simp [OfferRec], ?_, ?_, rfl, Or.inr ⟨rfl, rfl⟩, fun _ => N1_contains _ _ h2,
      fun x hx => N1_mono _ _ x h2 hx, fun hg hh2 => absurd ⟨hg, hh2⟩ h3, ?_⟩
    · intro mid org ts h
      simp at h; obtain ⟨_, rfl, _⟩ := h
      exact ⟨e, he, hal, hexp⟩
    · intro mid org ts via h
      simp at h; obtain ⟨_, rfl, rfl, _⟩ := h
      exact ho
    · intro hk
      refine ⟨fun x hx => ?_, fun _ => by simp⟩
      rcases SInsert_map_sub p N.seen m.mid now x false hx with h | h
      · exact Or.inr (by simp [h])
      · exact Or.inl h
  | deny h1 h2 h3 =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, fun hc hI => hI.withSeen (SInsert_inv hc hI.seen),
      by simp [OfferRec], by simp [CacheGood], by simp [FreshDel], rfl, Or.inl ⟨rfl, Or.inl rfl⟩,
      by intro h; rcases h with h | h; exact absurd rfl h; simp at h, fun x hx => N1_mono _ _ x h2 hx,
      fun hg hh2 => absurd ⟨hg, hh2⟩ h3, ?_⟩
    intro hk
    refine ⟨fun x hx => ?_, fun _ => by simp⟩
    rcases SInsert_map_sub p N.seen m.mid now x false hx with h | h
    · exact Or.inr (by simp [h])
    · exact Or.inl h
  | ask h1 h2 h3 ho =>
    obtain ⟨c, s, lg, rq, fh⟩ := HoldAndAsk_frame p (N1of p N now m) m
    have hdl := HoldAndAsk_dl p (N1of p N now m) m
    have hq := HoldAndAsk_quiet p (N1of p N now m) m
    refine ⟨Core.trans (B := N1of p N now m) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ c, lg, rq,
      fun hc hI => HoldAndAsk_inv (hI.withSeen (SInsert_inv hc hI.seen)) m (Or.inl ho) (fun a b => h3 ⟨b, a⟩),
      fun o h => (hq o h).offer, ?_, ?_, hdl.2, ?_, ?_, ?_, fun hg hh2 => absurd ⟨hg, hh2⟩ h3, ?_⟩
    · intro mid org ts h; exact absurd (hq _ h) (by simp [QuietRec])
    · intro mid org ts via h; exact absurd (hq _ h) (by simp [QuietRec])
    · rcases HoldAndAsk_held p (N1of p N now m) m with h | ⟨h, _⟩
      · exact Or.inl ⟨hdl.1, Or.inl h⟩
      · exact Or.inl ⟨hdl.1, Or.inr h⟩
    · intro _; rw [s]; exact N1_contains _ _ h2
    · intro x hx; rw [s]; exact N1_mono _ _ x h2 hx
    · intro hk
      refine ⟨fun x hx => ?_, fun _ => by rw [HoldAndAsk_acc p _ m hk]; simp⟩
      rw [s] at hx
      rcases SInsert_map_sub p N.seen m.mid now x false hx with h | h
      · exact Or.inr (by rw [HoldAndAsk_acc p _ m hk]; simp [h])
      · exact Or.inl h

theorem Offer_spec (p : Params) (N : Node) (now : Nat) (m : Ent) : OfferSpec p N now m (Offer p N now m) :=
  OfferSpec_of_form (Offer_form p N now m)

end Pinc.BroadcastNode
