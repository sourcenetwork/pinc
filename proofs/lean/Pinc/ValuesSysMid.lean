import Pinc.ValuesSysOnce

/-!
# The mid-group race and the scheduler operations

The in-order frame of a stream can arrive in two events: its header and proof are accepted while the group is not
stored (`acceptHdr`), its bytes complete later. Another stream may store the group in between. Then the completion
finds the group stored and only accounts for it (`acceptDup`): no write, no `Readable` event, nothing in the store
changes (`acceptDup_silent`), and the completion of a frame for an unstored group is the only one that writes
(`acceptEnd` needs `ver g = false`). `Once.step` (the announced-once invariant) holds across all of it.

The scheduler operations are enabled exactly under the conditions of the code: a holder of a share takes missing
wanted groups of the queue (`topUp_enabled`); every operation keeps the work conserved (`Op.plumbOk`).
-/

namespace Pinc.ValuesSys
open Classical

/-- A frame completing for a group another stream stored changes nothing but the bookkeeping. -/
theorem acceptDup_silent {c : Cfg} {s : St} {p g : Nat} {k : Kind}
    (h : Step c s { s with mid := s.mid.erase (p, g, k) }) :
    ({ s with mid := s.mid.erase (p, g, k) } : St).ann = s.ann ∧ ({ s with mid := s.mid.erase (p, g, k) } : St).pd = s.pd ∧
    ({ s with mid := s.mid.erase (p, g, k) } : St).wr = s.wr ∧ ({ s with mid := s.mid.erase (p, g, k) } : St).ver = s.ver :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- After the race the completion is enabled and silent: the stream that lost the race is accounted for, and the group
was announced once. -/
theorem midrace_enabled {c : Cfg} {s : St} {p g : Nat} {k : Kind} (hr : s.run = .running) (hp : s.pd = none)
    (hi : s.inP p = true) (hm : (p, g, k) ∈ s.mid) (hv : s.ver g = true) :
    ∃ s', Step c s s' ∧ s'.ann = s.ann ∧ s'.pd = s.pd ∧ s'.wr = s.wr ∧ s'.ver = s.ver :=
  ⟨_, Step.acceptDup s p g k hr hp hi hm hv, rfl, rfl, rfl, rfl⟩

/-- A frame completing for an unstored group goes to the store: the only way a mid frame writes. -/
theorem acceptEnd_writes {c : Cfg} {s : St} {p g : Nat} {k : Kind} (hr : s.run = .running) (hp : s.pd = none)
    (hi : s.inP p = true) (hm : (p, g, k) ∈ s.mid) (hv : s.ver g = false) (hk : k.verifies = true) :
    ∃ s', Step c s s' ∧ s'.pd = some { g := g, c := k.content, committing := false } :=
  ⟨_, Step.acceptEnd s p g k hr hp hi hm hv hk, rfl⟩

/-- A holder of a share takes missing wanted groups of the queue. -/
theorem topUp_enabled {c : Cfg} {s : St} {p g : Nat} (hr : s.run = .running) (hp : s.pd = none)
    (hh : s.inA p = true) (hq : s.queue g = true) (hw : c.want g = true) (hv : s.ver g = false) :
    ∃ s', Step c s s' ∧ s'.asg p g = true ∧ s'.reqd g = true := by
  refine ⟨_, Step.sched s (Op.topUp p (fun x => decide (x = g))) hr hp ⟨hh, fun x hx => ?_⟩, ?_, ?_⟩
  · have : x = g := by simpa using hx
    subst this; exact ⟨hq, hw, hv⟩
  · simp [Op.out, setAt, uni]
  · simp [Op.out, uni]

end Pinc.ValuesSys

#audit_axioms Pinc.ValuesSys.midrace_enabled
#audit_axioms Pinc.ValuesSys.acceptEnd_writes
#audit_axioms Pinc.ValuesSys.topUp_enabled
