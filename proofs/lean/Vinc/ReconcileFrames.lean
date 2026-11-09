import Vinc.ReconcileKeeps

/-!
# Reconcile frames: the frame stack is at most `maxNest` deep after every call, and every message is a bounded frame

Task property 7, unbounded, on the byte machine, for every input the peer can send and every state the machine can be in
(the stack starts empty and the bound is the induction hypothesis):

* `turn_frames`: a turn (`Core::turn`: the parts of a message, the push of the unread tail, the held frames resumed) leaves
  at most `maxNest` frames. The part rules keep the stack (`ReconcileKeeps`), `pushFrame` refuses past the bound
  (`Err.tooManyRounds`), and a resumed frame is dropped or replaced by its own tail.
* `initStart_frames`, `initHandle_frames`, `respHandle_frames`, `respResume_frames`: every handler of the initiator and the
  responder keeps the bound, including `restartExact` (it empties the stack) and a cold stream.
* `finish_framed`: every message a handler writes is a valid frame (`frameBody` reads it back) whose body is at most
  `frameCap = cap + 2 * maxItem + 4 * varMax`: the parts of a reply fit `cap` (the rollback of `answerLoop`) and the
  part count and, in the first message, the set reference ride on top.
-/

namespace Vinc.Reconcile

macro "okf" : tactic => `(tactic| first
  | (refine Ok.bind_any (fun _ => ?_))
  | (refine Ok.ite (fun _ => ?_) (fun _ => ?_))
  | (apply Ok.pure; first | rfl | (split <;> rfl) | simp)
  | exact Ok.throw _
  | split
  | (dsimp only [letFun])
  | (dsimp only))

theorem round_frames (c : Core) : Ok (fun c' => c'.frames = c.frames) c.round := by
  unfold Core.round; split
  · exact Ok.throw _
  · exact Ok.pure _ rfl

theorem root_frames (o : Oracle) (S : List Item) (c : Core) :
    Ok (fun p => p.1.frames = c.frames) (c.root o S) := by
  unfold Core.root
  repeat' okf

theorem checkMsg_frames (o : Oracle) (S : List Item) (c : Core) :
    Ok (fun p => p.1.frames = c.frames) (c.checkMsg o S) := by
  unfold Core.checkMsg
  repeat' okf

theorem coldChunk_frames (S : List Item) (c : Core) :
    Ok (fun p => p.1.frames = c.frames) (c.coldChunk S) := by
  unfold Core.coldChunk
  repeat' okf

theorem answerLoop_frames (o : Oracle) (S : List Item) (c : Core) (r : List Nat) (k : Nat) {fs : List Frame}
    (hc : c.frames = fs) : Ok (fun p => p.1.frames = fs) (answerLoop o S c r k) :=
  Ok.mono (answerLoop_keeps o S k c r) (fun _ hp => hp.1.trans hc)

theorem pushFrame_frames (c : Core) (rest : List Nat) (left : Nat) :
    Ok (fun c' => c'.frames.length ≤ maxNest) (c.pushFrame rest left) := by
  unfold Core.pushFrame
  split
  · exact Ok.throw _
  · next h => exact Ok.pure _ (by simp only [List.length_cons]; omega)

theorem resume_frames (o : Oracle) (S : List Item) (c : Core) (h : c.frames.length ≤ maxNest) :
    Ok (fun p => p.1.frames.length ≤ maxNest) (c.resume o S) := by
  unfold Core.resume
  cases hf : c.frames with
  | nil => exact Ok.throw _
  | cons f tl =>
    simp only [hf, List.length_cons] at h
    refine Ok.bind (P := fun p : Core × List Nat × Nat => p.1.frames = f :: tl) ?_ ?_
    · exact answerLoop_frames o S _ f.buf f.left rfl
    · rintro ⟨c2, rest, left⟩ hc2
      simp only at hc2
      refine Ok.ite (fun _ => Ok.ite (fun _ => Ok.throw _) (fun _ => Ok.pure _ ?_)) (fun _ => Ok.pure _ ?_)
      · simp only [hc2] at *; omega
      · simp only [hc2] at *; omega

theorem resumeLoop_frames (o : Oracle) (S : List Item) :
    ∀ (f : Nat) (c : Core), c.frames.length ≤ maxNest → Ok (fun c' => c'.frames.length ≤ maxNest) (resumeLoop o S f c)
  | 0, c, h => Ok.pure _ h
  | f + 1, c, h => by
    unfold resumeLoop
    refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure _ h)
    refine Ok.bind (P := fun p : Core × Bool => p.1.frames.length ≤ maxNest) (resume_frames o S c h) ?_
    rintro ⟨c', adv⟩ hc'
    refine Ok.ite (fun _ => resumeLoop_frames o S f c' hc') (fun _ => Ok.pure _ hc')

/-- A turn leaves at most `maxNest` frames held, whatever the peer sent. -/
theorem turn_frames (o : Oracle) (S : List Item) (c : Core) (r : List Nat) (np : Nat)
    (h : c.frames.length ≤ maxNest) : Ok (fun p => p.1.frames.length ≤ maxNest) (c.turn o S r np) := by
  unfold Core.turn
  dsimp only
  refine Ok.bind (P := fun p : Core × List Nat × Nat => p.1.frames = c.frames) ?_ ?_
  · exact answerLoop_frames o S _ r np rfl
  · rintro ⟨c1, rest, left⟩ h1
    simp only at h1 ⊢
    have h1' : c1.frames.length ≤ maxNest := by rw [h1]; exact h
    have tail : ∀ c2 : Core, c2.frames.length ≤ maxNest →
        Ok (fun p : Core × Ans => p.1.frames.length ≤ maxNest)
          (resumeLoop o S (c2.frames.foldl (fun s f => s + f.left + 1) 1) c2 >>= fun c3 => pure (c3, c3.ans)) :=
      fun c2 h2 => Ok.bind (P := fun c3 : Core => c3.frames.length ≤ maxNest) (resumeLoop_frames o S _ c2 h2)
        (fun c3 h3 => Ok.pure _ h3)
    refine Ok.ite (fun _ => Ok.bind (P := fun c2 : Core => c2.frames.length ≤ maxNest) (pushFrame_frames c1 rest left)
        (fun c2 h2 => tail c2 h2)) (fun _ => Ok.ite (fun _ => Ok.bind (P := fun _ => False) (Ok.throw _)
        (fun _ ha => ha.elim)) (fun _ => Ok.bind (P := fun c2 : Core => c2.frames.length ≤ maxNest) (Ok.pure _ h1')
        (fun c2 h2 => tail c2 h2)))

theorem start_frames (o : Oracle) (S : List Item) (c : Core) (ref : Item) :
    Ok (fun p => p.1.frames.length ≤ maxNest) (c.start o S ref) := by
  unfold Core.start
  dsimp only
  refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
  refine Ok.bind (P := fun p : Core × Nat => p.1.frames = []) ?_ ?_
  · refine Ok.mono (root_frames o S _) ?_
    intro p hp; simpa [Core.clear] using hp
  · rintro ⟨c1, cnt⟩ h1
    simp only at h1 ⊢
    refine Ok.bind_any (fun _ => Ok.pure _ ?_)
    simp [h1]

theorem close_frames (o : Oracle) (S : List Item) (s : Initiator) (pd : Bool) (h : s.core.frames.length ≤ maxNest) :
    Ok (fun p => p.2.2.core.frames.length ≤ maxNest) (s.close o S pd) := by
  unfold Initiator.close
  dsimp only
  refine Ok.ite (fun _ => Ok.pure _ h) (fun _ => Ok.ite (fun _ => ?_) (fun _ => ?_))
  · refine Ok.bind (P := fun p : Core × List Nat => p.1.frames = s.core.frames) (checkMsg_frames o S _) ?_
    rintro ⟨c1, m⟩ h1
    simp only at h1 ⊢
    exact Ok.pure _ (by simpa [h1] using h)
  · refine Ok.ite (fun _ => Ok.pure _ h) (fun _ => Ok.bind_any (fun _ => Ok.pure _ h))

theorem restartExact_frames (o : Oracle) (S : List Item) (c : Core) :
    Ok (fun p => p.1.frames.length ≤ maxNest) (c.restartExact o S) := by
  unfold Core.restartExact
  dsimp only
  refine Ok.bind (P := fun p : Core × Nat => p.1.frames = []) (Ok.mono (root_frames o S _) fun p hp => by simpa using hp) ?_
  rintro ⟨c1, cnt⟩ h1
  simp only at h1 ⊢
  exact Ok.bind_any (fun _ => Ok.pure _ (by simp [h1]))

theorem initStart_frames (o : Oracle) (S : List Item) (s : Initiator) (ref : Item) :
    Ok (fun p => p.1.core.frames.length ≤ maxNest) (s.start o S ref) := by
  unfold Initiator.start
  exact Ok.bind (P := fun p : Core × List Nat => p.1.frames.length ≤ maxNest) (start_frames o S _ ref)
    (fun _ hp => Ok.pure _ hp)

/-- An initiator keeps at most `maxNest` frames after every message it handles. -/
theorem initHandle_frames (o : Oracle) (S : List Item) (s : Initiator) (msg : List Nat)
    (h : s.core.frames.length ≤ maxNest) : Ok (fun p => p.2.2.core.frames.length ≤ maxNest) (s.handle o S msg) := by
  unfold Initiator.handle
  dsimp only
  refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
  refine Ok.bind (P := fun c : Core => c.frames = s.core.frames) (Ok.mono (round_frames _) fun c hc => hc) ?_
  intro c hc
  refine Ok.bind_any (fun body => Ok.bind_any (fun pr => ?_))
  obtain ⟨⟨np, more⟩, r⟩ := pr
  dsimp only
  have hc' : c.frames.length ≤ maxNest := by rw [hc]; exact h
  refine Ok.bind (P := fun p : Core × Ans => p.1.frames.length ≤ maxNest) (turn_frames o S c r np hc') ?_
  rintro ⟨c2, ans⟩ h2
  simp only at h2 ⊢
  refine Ok.ite (fun _ => Ok.ite (fun _ => Ok.pure _ h2) (fun _ => Ok.pure _ h2)) (fun _ => ?_)
  refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
  refine Ok.ite (fun _ => Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)) (fun _ => ?_)
  · refine Ok.bind (P := fun p : Core × List Nat => p.1.frames.length ≤ maxNest) (restartExact_frames o S c2) ?_
    rintro ⟨c3, m⟩ h3
    exact Ok.pure _ h3
  · refine Ok.ite (fun _ => Ok.bind_any (fun _ => Ok.pure _ h2)) (fun _ => Ok.ite (fun _ => Ok.bind_any (fun _ => Ok.pure _ h2)) (fun _ => ?_))
    exact close_frames o S { s with core := c2 } _ h2

theorem respRun_frames (o : Oracle) (S : List Item) (s : Responder) (r : List Nat)
    (h : s.core.frames.length ≤ maxNest) : Ok (fun p => p.2.2.core.frames.length ≤ maxNest) (s.run o S r) := by
  unfold Responder.run
  dsimp only
  refine Ok.bind (P := fun c : Core => c.frames = s.core.frames) (Ok.mono (round_frames _) fun c hc => hc) ?_
  intro c hc
  refine Ok.bind_any (fun pr => ?_)
  obtain ⟨⟨np, more⟩, r1⟩ := pr
  dsimp only
  have hc' : c.frames.length ≤ maxNest := by rw [hc]; exact h
  refine Ok.bind (P := fun p : Core × Ans => p.1.frames.length ≤ maxNest) (turn_frames o S c r1 np hc') ?_
  rintro ⟨c2, ans⟩ h2
  simp only at h2 ⊢
  refine Ok.ite (fun _ => Ok.bind_any (fun _ => Ok.pure _ h2)) (fun _ => Ok.ite (fun _ => Ok.bind_any (fun _ => Ok.pure _ h2)) (fun _ => ?_))
  refine Ok.ite (fun _ => Ok.pure _ h2) (fun _ => Ok.bind_any (fun _ => Ok.pure _ h2))

theorem respResume_frames (o : Oracle) (S : List Item) (s : Responder) (h : s.core.frames.length ≤ maxNest) :
    Ok (fun p => p.2.2.core.frames.length ≤ maxNest) (s.resume o S) := by
  intro v hv
  unfold Responder.resume at hv
  split at hv
  · cases hv
  · cases hc : s.core.coldChunk S with
    | error e => simp [hc] at hv
    | ok q =>
      obtain ⟨c, m, last⟩ := q
      have hf : c.frames = s.core.frames := coldChunk_frames S s.core _ hc |>.symm ▸ rfl
      simp only [hc] at hv
      split at hv
      · cases hv; simp only; rw [hf]; exact h
      · cases hv; simp only; rw [hf]; exact h

theorem respHandle_frames (o : Oracle) (S : List Item) (s : Responder) (msg : List Nat)
    (h : s.core.frames.length ≤ maxNest) : Ok (fun p => p.2.2.core.frames.length ≤ maxNest) (s.handle o S msg) := by
  unfold Responder.handle
  dsimp only
  refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
  refine Ok.bind_any (fun body => ?_)
  refine Ok.ite (fun _ => ?_) (fun _ => respRun_frames o S s body h)
  refine Ok.bind_any (fun pr => ?_)
  obtain ⟨l, r1⟩ := pr
  dsimp only
  refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
  refine Ok.bind_any (fun pr => ?_)
  obtain ⟨u, r2⟩ := pr
  dsimp only
  refine Ok.bind_any (fun pr => ?_)
  obtain ⟨na, r3⟩ := pr
  dsimp only
  refine Ok.ite (fun _ => respResume_frames o S _ (by simp [Core.clear, maxNest])) (fun _ => respRun_frames o S _ r3 (by simp [Core.clear, maxNest]))

/-- A message the machine writes is a frame of at most `frameCap` body bytes, and `frameBody` reads it back. -/
theorem finish_framed (c : Core) (withHdr : Bool) (cnt : Nat) (more : Bool) (m : List Nat)
    (h : c.finish withHdr cnt more = .ok m) :
    ∃ body, frameBody m = .ok body ∧ body.length ≤ c.frameCap := by
  unfold Core.finish at h
  dsimp only at h
  generalize (if withHdr = true then c.hdr else []) ++ putParts cnt more ++ c.out.body = body at h
  cases hh : frameHeader body.length with
  | none => simp [hh] at h
  | some hd =>
    simp only [hh] at h
    split at h
    · cases h
    · next hle =>
      cases h
      exact ⟨_, frameBody_frameHeader _ _ hh, Nat.le_of_not_lt hle⟩

#audit_axioms Vinc.Reconcile.turn_frames
#audit_axioms Vinc.Reconcile.initStart_frames
#audit_axioms Vinc.Reconcile.initHandle_frames
#audit_axioms Vinc.Reconcile.respHandle_frames
#audit_axioms Vinc.Reconcile.respResume_frames
#audit_axioms Vinc.Reconcile.finish_framed

end Vinc.Reconcile
