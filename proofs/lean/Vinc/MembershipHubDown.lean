import Vinc.MembershipHubFrame

/-!
# Hub theorems, part 2: another hub's DOWN (`on_down`)

Property 3 (d): a DOWN from another hub never removes a member while this hub's own lease for it is fresh, and the
independent-path rule at the receiving hub.

* `onDown_boot`, `onDown_unknown`: a hub is never reported down this way, nor a member this hub holds no lease for.
* `onDown_refuses`: unless every condition of `DownOk` holds, the roster keeps exactly the same members (only a
  lease's renewal time can change), the held table, the broadcast-layer calls and the sent frames are untouched.
* `onDown_accepts`: when every condition holds, the call is exactly `hub_down` with cause `remote`.
* `onDown_fresh_keeps` (the headline): a lease renewed (by a frame or by transport evidence) within
  `max(oldest probe, RENEW)` keeps the member, whatever the proof says.
* `DownOk` lists the whole rule: the sender is a hub (the dispatcher), the member is not a hub, this hub holds a lease
  of the same epoch, the proof lists two different paths, claims at least as much silence as its probes span, the
  member holds no carrier to this hub, and this hub's own lease is stale.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

@[simp] theorem trace_outSent (n : N) (t : Tr) : (n.trace t).outSent = n.outSent := by
  unfold N.trace; split <;> (try split) <;> rfl
@[simp] theorem emit_outSent (n : N) (e : Ev) : (n.emit e).outSent = n.outSent := by
  unfold N.emit; split <;> rfl

namespace AMap
variable {α : Type}
@[simp] theorem modify_keys (m : AMap α) (k : Nat) (f : α → α) : (m.modify k f).keys = m.keys := by
  unfold modify keys; induction m with
  | nil => rfl
  | cons p r ih => simp only [List.map_cons, List.cons.injEq]; exact ⟨by split <;> rfl, ih⟩

@[simp] theorem modify_has (m : AMap α) (k j : Nat) (f : α → α) : (m.modify k f).has j = m.has j := by
  unfold modify has; induction m with
  | nil => rfl
  | cons p r ih => simp only [List.map_cons, List.any_cons]; rw [ih]; split <;> simp_all

theorem modify_length (m : AMap α) (k : Nat) (f : α → α) : (m.modify k f).length = m.length := by
  unfold modify; simp
end AMap

/-- The renewal time `on_down` compares: the lease's, or the transport's if later. -/
def downRenewed (e : Env) (l : Lease) (m : Nat) : Nat :=
  match e.evidence m with | some ev => max l.renewed ev.rx | none => l.renewed

/-- Every condition under which a hub accepts another hub's DOWN. -/
def DownOk (e : Env) (n : N) (now m inc : Nat) (pf : Proof) : Prop :=
  n.isBoot m = false ∧
  ∃ l, n.roster.get? m = some l ∧ l.rc.inc / 65536 = inc / 65536 ∧
    pf.independent = true ∧ ¬ pf.sil < pf.oldest ∧ e.carrier m ≠ .open_ ∧
    max (pf.oldest * 1000000) RENEW < now - downRenewed e l m

theorem onDown_boot (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (h : n.isBoot m = true) :
    N.onDown e n now m inc pf = n.trace (.downRefused m Refusal.notApplicable.toNat) := by
  unfold N.onDown; simp [h]

theorem onDown_unknown (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (h : n.isBoot m = false)
    (h2 : n.roster.get? m = none) :
    N.onDown e n now m inc pf = n.trace (.downRefused m Refusal.unknown.toNat) := by
  unfold N.onDown; simp [h, h2]

/-- A refused DOWN leaves everything but a lease's renewal time alone. -/
theorem onDown_refuses (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (h : ¬ DownOk e n now m inc pf) :
    (N.onDown e n now m inc pf).roster.keys = n.roster.keys ∧ (N.onDown e n now m inc pf).downed = n.downed ∧
    (N.onDown e n now m inc pf).outBc = n.outBc ∧ (N.onDown e n now m inc pf).outSent = n.outSent ∧
    (N.onDown e n now m inc pf).susp = n.susp := by
  unfold N.onDown
  dsimp only
  repeat' split
  all_goals first | (simp; done) | (simp_all [DownOk, downRenewed]; done) | skip


theorem AMap.has_keys {α : Type} (m : AMap α) (k : Nat) : m.has k = true ↔ k ∈ m.keys := by
  unfold AMap.has AMap.keys; simp [List.any_eq_true]

theorem AMap.get?_has {α : Type} (m : AMap α) (k : Nat) (v : α) (h : m.get? k = some v) : m.has k = true := by
  unfold AMap.get? at h; unfold AMap.has
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨p, hp, _⟩ := h
  have h2 : (p.fst == k) = true := @List.find?_some (Nat × α) (fun p : Nat × α => p.fst == k) p m hp
  exact List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some hp, h2⟩

/-- Accepted: exactly `hub_down` with cause `remote`, after the lease's renewal time was brought up to the transport's. -/
theorem onDown_accepts (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (l : Lease) (hb : n.isBoot m = false)
    (hl : n.roster.get? m = some l) (he : l.rc.inc / 65536 = inc / 65536) (hi : pf.independent = true)
    (hs : ¬ pf.sil < pf.oldest) (hc : e.carrier m ≠ .open_) (hw : max (pf.oldest * 1000000) RENEW < now - downRenewed e l m) :
    N.onDown e n now m inc pf =
      N.hubDown e (({ n with roster := n.roster.modify m (fun x => { x with renewed := downRenewed e l m }) } : N).trace
        (.downAccepted m)) now m .remote := by
  unfold N.onDown
  unfold downRenewed at *
  simp [hb, hl, he, hi, hs, hc]
  cases hev : e.evidence m <;> simp [hev] at hw ⊢ <;> omega

/-- The headline of property 3 (d): another hub's DOWN never removes a member while this hub's own lease for it is
fresh, whatever the proof says. -/
theorem onDown_fresh_keeps (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (l : Lease) (hl : n.roster.get? m = some l)
    (hfresh : now - downRenewed e l m ≤ max (pf.oldest * 1000000) RENEW) :
    (N.onDown e n now m inc pf).roster.has m = true := by
  have hn : ¬ DownOk e n now m inc pf := by
    intro hd
    obtain ⟨_, l', hl', _, _, _, _, hw⟩ := hd
    rw [hl] at hl'; injection hl' with h; subst h; omega
  have h := (onDown_refuses e n now m inc pf hn).1
  rw [AMap.has_keys, h, ← AMap.has_keys]
  exact AMap.get?_has _ _ _ hl

/-- The independent-path rule at the receiving hub: a proof of one path never removes a member. -/
theorem onDown_one_path_keeps (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (hp : pf.independent = false) :
    (N.onDown e n now m inc pf).roster.keys = n.roster.keys := by
  apply (onDown_refuses e n now m inc pf _).1
  rintro ⟨-, l', -, -, hi, -⟩; rw [hp] at hi; cases hi

/-- An open carrier to this hub refuses the DOWN. -/
theorem onDown_open_carrier_keeps (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (hc : e.carrier m = .open_) :
    (N.onDown e n now m inc pf).roster.keys = n.roster.keys := by
  apply (onDown_refuses e n now m inc pf _).1
  rintro ⟨-, l', -, -, -, -, hc', -⟩; exact hc' hc

/-- A proof that claims less silence than its own probes span is refused. -/
theorem onDown_bad_proof_keeps (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (hb : pf.sil < pf.oldest) :
    (N.onDown e n now m inc pf).roster.keys = n.roster.keys := by
  apply (onDown_refuses e n now m inc pf _).1
  rintro ⟨-, l', -, -, -, hs, -⟩; exact hs hb

end Vinc.Membership
