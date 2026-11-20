import Pinc.TransportStreamsGrant

/-!
# Credit against the ledger, stream caps, resets, and in-order delivery

Unbounded theorems about the receive half and the table of `Pinc.TransportStreams`.

* `missing_le`, `frame_needs_no_more_than_ledger`: the pool chunks a frame inside the span the ledger counts still has
  to take are at most what the ledger counted for the stream (`pool_demand` up to `chargeTo`: the chunks of the span
  from the read position to the limit that are not held, so holes below the highest byte are counted; the first
  `firstk` chunks only while the stream has carried no data). With `grantOne_ledger`
  (`Pinc.TransportStreamsGrant`), which keeps the sum of those counts within the pool bytes left whenever a limit is
  raised, credit never exceeds the ledger (POOL_GRANT).
* `admits_cap`, `locate_error_pure`, `locate_held_back`, `frame_held_back`, `locate_ok_next`: a peer stream is
  admitted only under the cap; one that does not fit is held back (the call answers `Exhausted`, the table is
  unchanged, nothing is stored or charged, no counter moves, the packet goes unacknowledged), so its retransmission
  meets the table the first arrival met; an admitted stream moves the next index past its own id (STREAM_CAP).
* `onReset_ok`, `onReset_final_fixed`, `onData_final_fixed`: a reset frees the buffered bytes, leaves nothing
  readable and fixes the final size, and a final size once fixed never changes.
* `Slot.discard_spec`, `onData_stopped_end_discards`, `stopReq_given_up`, `stopReq_given_up_frees`,
  `stopReq_given_up_keeps`, `stopReq_given_up_rl` (c0706819): a stream given up after its end arrived, or whose end
  arrives after a stop was asked, holds no bytes and is read to its end; the stop request asks nothing and settles it,
  so it leaves the table at once when its send half is done, and a counted peer stream gives back exactly its place in
  the peer's limit (`regrant_rl`: a regrant moves no count).
* `Content`, `exactly_once_in_order`, `stored_immutable`: with the checks of `Recv::store` (a byte received twice
  must be identical) and the rule that a consume stays inside the stored prefix, the bytes delivered are the bytes
  stored, in offset order, each once; `held_back_delivers_once`: a held-back first arrival changes nothing and its
  retransmission is delivered exactly once.
-/

namespace Pinc.TransportStreams

/-! ### Credit against the ledger -/
theorem missing_le (a b : Nat) (held : List Nat) (hnd : held.Nodup) (hb : ∀ k ∈ held, a ≤ k ∧ k ≤ b)
    (first last : Nat) (h1 : a ≤ first) (h2 : last ≤ b) :
    (((List.range (last + 1 - first)).map (first + ·)).filter (fun k => !held.contains k)).length + held.length
      ≤ b + 1 - a := by
  let M := ((List.range (last + 1 - first)).map (first + ·)).filter (fun k => !held.contains k)
  have hMnd : M.Nodup := by
    exact List.Pairwise.sublist (List.filter_sublist)
      (List.Pairwise.map (fun x => first + x) (fun a b h => by omega) List.nodup_range)
  have hdisj : ∀ x ∈ M, x ∉ held := by
    intro x hx
    simp [M] at hx
    exact hx.2
  have hnd2 : (M ++ held).Nodup := by
    rw [List.nodup_append]
    refine ⟨hMnd, hnd, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact hdisj x hx hy
  have hsub : (M ++ held) ⊆ List.range' a (b + 1 - a) := by
    intro x hx
    rw [List.mem_range'_1]
    rcases List.mem_append.mp hx with hx | hx
    · simp [M] at hx
      obtain ⟨⟨i, hi, rfl⟩, -⟩ := hx
      omega
    · have := hb x hx
      omega
  have := List.Nodup.length_le_of_subset hnd2 hsub
  simp at this
  omega

/-- A frame inside the span the ledger counts (`chargeTo`: the whole window of a stream that has carried data, the first
`firstk` chunks of one that has not) needs no more fresh chunks than the ledger counts for its stream. -/
theorem frame_needs_no_more_than_ledger (p : P) (r : Slot) (hch : 0 < p.ch) (hnd : r.held.Nodup)
    (hopen : r.open_ = true) (hr : r.read < r.reach (r.chargeTo p r.limit))
    (hheld : ∀ k ∈ r.held, r.read / p.ch ≤ k ∧ k ≤ (r.reach (r.chargeTo p r.limit) - 1) / p.ch)
    (lo e : Nat) (hlo : r.read ≤ lo) (hlt : lo < e) (he : e ≤ r.reach (r.chargeTo p r.limit)) :
    (((List.range ((e - 1) / p.ch + 1 - lo / p.ch)).map (lo / p.ch + ·)).filter
        (fun k => !r.held.contains k)).length * p.ch ≤ r.unreceived p := by
  have h1 : r.read / p.ch ≤ lo / p.ch := Nat.div_le_div_right hlo
  have h2 : (e - 1) / p.ch ≤ (r.reach (r.chargeTo p r.limit) - 1) / p.ch := Nat.div_le_div_right (by omega)
  have h3 : r.read / p.ch ≤ (r.reach (r.chargeTo p r.limit) - 1) / p.ch := Nat.div_le_div_right (by omega)
  have key := missing_le (r.read / p.ch) ((r.reach (r.chargeTo p r.limit) - 1) / p.ch) r.held hnd hheld (lo / p.ch)
    ((e - 1) / p.ch) h1 h2
  have hd : r.unreceived p
      = ((r.reach (r.chargeTo p r.limit) - 1) / p.ch - r.read / p.ch + 1 - r.held.length) * p.ch := by
    unfold Slot.unreceived Slot.demandTo poolDemand
    simp [hopen, Nat.not_le.mpr hr]
  rw [hd]
  apply Nat.mul_le_mul_right
  omega

/-! ### STREAM_CAP -/
theorem admits_cap (p : P) (T : Tab) (c next count : Nat) (h : admits p T c next count = true) :
    T.rl + count ≤ p.maxrem := by
  unfold admits at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- A locate that answers with an error leaves the table exactly as it was and finds no slot: nothing of a stream
that does not fit (or is invalid) is stored, no pool chunk is charged and no counter moves. -/
theorem locate_error_pure (p : P) (T : Tab) (id : Nat) (h : (locate p T id).2.2 ≠ "ok") :
    (locate p T id).1 = T ∧ (locate p T id).2.1 = none := by
  by_cases h1 : isLocal id = true
  · by_cases h2 : idx id ≥ cget T.lo (cls id)
    · simp [locate, h1, h2]
    · simp [locate, h1, h2] at h
  · by_cases h2 : idx id < cget T.rn (cls id)
    · simp [locate, h1, h2] at h
    · by_cases h4 : idx id ≥ cget T.rn (cls id) + p.maxrem
      · simp [locate, h1, h2, h4]
      · by_cases h5 : admits p T (cls id) (cget T.rn (cls id)) (idx id - cget T.rn (cls id) + 1) = true
        · simp [locate, h1, h2, h4, h5] at h
        · simp [locate, h1, h2, h4, h5]

theorem locate_error_stores_nothing (p : P) (T : Tab) (id : Nat) (h : (locate p T id).2.2 ≠ "ok") :
    (locate p T id).1.slots = T.slots := by
  rw [(locate_error_pure p T id h).1]

/-- A peer stream that does not fit yet is held back: the locate answers `Exhausted` with the table unchanged, so
the opener's retransmission on the same id meets the table the first arrival met. -/
theorem locate_held_back (p : P) (T : Tab) (id : Nat) (h : (locate p T id).2.2 = "Exhausted") :
    locate p T id = (T, none, "Exhausted") := by
  have hp := locate_error_pure p T id (by rw [h]; decide)
  exact Prod.ext hp.1 (Prod.ext hp.2 h)

/-- A frame for a held-back stream changes nothing: not a slot, not a pool charge, not a counter. -/
theorem frame_held_back (p : P) (T : Tab) (id off len : Nat) (fin diff : Bool)
    (h : (locate p T id).2.2 = "Exhausted") : frame p T id off len fin diff = (T, "Exhausted") := by
  unfold frame
  rw [locate_held_back p T id h]

/-- An arriving peer stream that is admitted moves the next index of its kind past its own id: every lower id was
opened, one event each (the count of new ids is the distance moved). -/
theorem locate_ok_next (p : P) (T : Tab) (id : Nat) (hl : isLocal id = false) (h2 : ¬ idx id < cget T.rn (cls id))
    (h4 : ¬ idx id ≥ cget T.rn (cls id) + p.maxrem)
    (h5 : admits p T (cls id) (cget T.rn (cls id)) (idx id - cget T.rn (cls id) + 1) = true) :
    cget (locate p T id).1.rn (cls id) = idx id + 1 := by
  have hl' : ¬ isLocal id = true := by simp [hl]
  have hn : ¬ (!admits p T (cls id) (cget T.rn (cls id)) (idx id - cget T.rn (cls id) + 1)) = true := by simp [h5]
  simp only [locate, hl', h2, h4, hn, if_false]
  unfold cget cset
  by_cases hk : cls id = 0 <;> simp [hk]

/-! ### Reset and the final size -/
/-- A peer reset frees the buffered bytes, leaves nothing readable, fixes the final size and the read position
there, and marks the stream reset. -/
theorem onReset_ok (p : P) (r : Slot) (code fs : Nat) (hn : r.rst = none)
    (h : (onReset p r code fs).2 = "ok") :
    (onReset p r code fs).1.held = [] ∧ (onReset p r code fs).1.rs = [] ∧ (onReset p r code fs).1.read = fs ∧
      (onReset p r code fs).1.fin = some fs ∧ (onReset p r code fs).1.readable = 0 ∧
      (onReset p r code fs).1.status = 2 := by
  unfold onReset at h ⊢
  by_cases h1 : (fs > p.maxoff || r.fin.any (· != fs) || decide (fs < r.hi)) = true
  · simp [h1] at h
  · by_cases h2 : fs > r.limit
    · simp [h1, h2] at h
    · simp [h1, h2, hn, Slot.readable, Slot.status]

theorem onReset_final_fixed (p : P) (r : Slot) (code fs f : Nat) (hf : r.fin = some f) :
    (onReset p r code fs).1.fin = some f := by
  unfold onReset
  repeat' split
  all_goals simp_all

theorem storeStep_fin (p : P) (T : Tab) (r : Slot) (off len : Nat) (diff : Bool) :
    (storeStep p T r off len diff).1.fin = r.fin := by
  unfold storeStep
  dsimp only
  repeat' split
  all_goals simp

theorem storeStep_rst (p : P) (T : Tab) (r : Slot) (off len : Nat) (diff : Bool) :
    (storeStep p T r off len diff).1.rst = r.rst := by
  unfold storeStep
  dsimp only
  repeat' split
  all_goals simp

@[simp] theorem Slot.discard_fin (r : Slot) : r.discard.fin = r.fin := by
  unfold Slot.discard
  split <;> rfl

/-- A discard touches only the receive half's bytes: the stream, its count, its send half and its end stay. -/
theorem Slot.discard_keeps (r : Slot) :
    r.discard.id = r.id ∧ r.discard.cnt = r.cnt ∧ r.discard.open_ = r.open_ ∧ r.discard.sendDone = r.sendDone := by
  unfold Slot.discard
  split <;> simp [Slot.sendDone]

/-- A discard of a stream whose end is known and that was not reset holds no bytes, is read to its end and its
receive half is done. -/
theorem Slot.discard_spec (r : Slot) (f : Nat) (hf : r.fin = some f) (hr : r.rst = none) :
    r.discard.held = [] ∧ r.discard.rs = [] ∧ r.discard.read = f ∧ r.discard.recvDone = true := by
  simp [Slot.discard, hf, hr, Slot.recvDone, Slot.status]

/-- The final size, once fixed, never changes. -/
theorem onData_final_fixed (p : P) (T : Tab) (r : Slot) (off len f : Nat) (fin diff : Bool) (hf : r.fin = some f) :
    (onData p T r off len fin diff).1.fin = some f := by
  have hs := storeStep_fin p T r off len diff
  unfold onData
  dsimp only
  repeat' split
  all_goals simp_all

/-! ### Giving a stream up after its end arrived (c0706819) -/
/-- The end arriving on a stream asked to stop: the stream holds no bytes, is read to its end and its receive half is
done. -/
theorem onData_stopped_end_discards (p : P) (T : Tab) (r : Slot) (off len : Nat) (diff : Bool) (hr : r.rst = none)
    (hs : r.stop ≠ 0) :
    (onData p T r off len true diff).2 = "ok" →
      (onData p T r off len true diff).1.held = [] ∧ (onData p T r off len true diff).1.rs = [] ∧
      (onData p T r off len true diff).1.fin = some (onData p T r off len true diff).1.read ∧
      (onData p T r off len true diff).1.recvDone = true := by
  have hst := storeStep_rst p T r off len diff
  unfold onData
  dsimp only
  repeat' split
  all_goals simp_all [Slot.discard, Slot.recvDone, Slot.status]

theorem grantOne_rl (p : P) (first : Nat) (T : Tab) (i : Nat) : (grantOne p first T i).rl = T.rl := by
  unfold grantOne
  dsimp only
  split <;> rfl

theorem grantRun_rl (p : P) (T : Tab) (first : Nat) : (grantRun p T first).rl = T.rl := by
  unfold grantRun
  generalize List.range p.n = l
  induction l generalizing T with
  | nil => rfl
  | cons a t ih => simp only [List.foldl_cons]; rw [ih]; exact grantOne_rl p first T a

/-- A regrant moves no stream count. -/
theorem regrant_rl (p : P) (T : Tab) : (regrant p T).rl = T.rl := by
  have ha : (refreshAdmit p T).rl = T.rl := by
    unfold refreshAdmit
    dsimp only
    split <;> rfl
  unfold regrant
  dsimp only
  split
  · rw [grantRun_rl, ha]
  · exact ha

/-- A stop request on a stream whose end arrived and that was not reset asks nothing: it discards the stream and
settles it. -/
theorem stopReq_given_up (p : P) (T : Tab) (id code i f : Nat) (hi : findSlot T id = some i)
    (ho : (T.slots.getD i Slot.new).open_ = true) (hr : (T.slots.getD i Slot.new).rst = none)
    (hf : (T.slots.getD i Slot.new).fin = some f) :
    stopReq p T id code = (settle p (setSlot T i (T.slots.getD i Slot.new).discard) i, "ok") := by
  unfold stopReq
  rw [hi]
  simp only [ho, hr, hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_none, Option.isSome_some]

/-- Its send half done, the stream leaves the table at once. -/
theorem stopReq_given_up_frees (p : P) (T : Tab) (id code i f : Nat) (hi : findSlot T id = some i)
    (ho : (T.slots.getD i Slot.new).open_ = true) (hr : (T.slots.getD i Slot.new).rst = none)
    (hf : (T.slots.getD i Slot.new).fin = some f) (hd : (T.slots.getD i Slot.new).sendDone = true) :
    (stopReq p T id code).1 = regrant p (freeSlot (setSlot T i (T.slots.getD i Slot.new).discard) i) := by
  rw [stopReq_given_up p T id code i f hi ho hr hf]
  have hl := lt_of_open T.slots i ho
  have hs := Slot.discard_spec _ f hf hr
  have hk := Slot.discard_keeps (T.slots.getD i Slot.new)
  unfold settle
  dsimp only
  simp only [getD_setSlot T i i _ hl, eq_self, ↓reduceIte, hs.2.2.2, hk.2.2.2, hd, Bool.and_self]

/-- Its send half not done, the slot is kept with its receive half done (release_limit may then free its place). -/
theorem stopReq_given_up_keeps (p : P) (T : Tab) (id code i f : Nat) (hi : findSlot T id = some i)
    (ho : (T.slots.getD i Slot.new).open_ = true) (hr : (T.slots.getD i Slot.new).rst = none)
    (hf : (T.slots.getD i Slot.new).fin = some f) (hd : (T.slots.getD i Slot.new).sendDone = false) :
    (stopReq p T id code).1 = regrant p (releaseLimit (setSlot T i (T.slots.getD i Slot.new).discard) i) := by
  rw [stopReq_given_up p T id code i f hi ho hr hf]
  have hl := lt_of_open T.slots i ho
  have hk := Slot.discard_keeps (T.slots.getD i Slot.new)
  have hs := Slot.discard_spec _ f hf hr
  unfold settle
  dsimp only
  simp only [getD_setSlot T i i _ hl, eq_self, ↓reduceIte, hs.2.2.2, hk.2.2.2, hd, Bool.and_false,
    Bool.false_eq_true]

/-- A counted peer stream given up with its send half done gives its place in the peer's limit back: the count drops
by exactly the one slot freed. -/
theorem stopReq_given_up_rl (p : P) (T : Tab) (id code i f id' : Nat) (hi : findSlot T id = some i)
    (ho : (T.slots.getD i Slot.new).open_ = true) (hr : (T.slots.getD i Slot.new).rst = none)
    (hf : (T.slots.getD i Slot.new).fin = some f) (hd : (T.slots.getD i Slot.new).sendDone = true)
    (hid : (T.slots.getD i Slot.new).id = some id') (hloc : isLocal id' = false)
    (hc : (T.slots.getD i Slot.new).cnt = true) :
    (stopReq p T id code).1.rl = T.rl - 1 := by
  rw [stopReq_given_up_frees p T id code i f hi ho hr hf hd, regrant_rl]
  have hl := lt_of_open T.slots i ho
  have hk := Slot.discard_keeps (T.slots.getD i Slot.new)
  unfold freeSlot
  dsimp only
  simp only [getD_setSlot T i i _ hl, eq_self, ↓reduceIte, hk.1, hid, hk.2.1, hc, hloc, Bool.false_eq_true]
  rfl


/-! ### In-order delivery, each byte once -/
/-- The bytes of one stream as the receive half keeps them: the byte stored at an offset (the first one ever stored
there), the read position, and the bytes delivered so far. -/
structure Content where
  st : Nat → Option Nat
  read : Nat
  log : List Nat

/-- A frame's bytes `g` for offsets `lo..e` are stored when they agree with every byte already stored there (a byte
received twice must be identical, else `Conflict` and nothing changes); only offsets with nothing stored take a byte. -/
def Content.store (c : Content) (lo e : Nat) (g : Nat → Nat) : Content :=
  { c with st := fun o => if lo ≤ o ∧ o < e then (match c.st o with | some v => some v | none => some (g o)) else c.st o }

/-- A consume of `n` bytes stays inside the stored prefix (`n <= contig - read`) and delivers them in order. -/
def Content.consume (c : Content) (n : Nat) : Content :=
  { c with read := c.read + n, log := c.log ++ (List.range n).map (fun k => (c.st (c.read + k)).getD 0) }

inductive Step : Content → Content → Prop
  | store (c : Content) (lo e : Nat) (g : Nat → Nat)
      (hok : ∀ o, lo ≤ o → o < e → ∀ v, c.st o = some v → v = g o) : Step c (c.store lo e g)
  | consume (c : Content) (n : Nat) (hs : ∀ o, c.read ≤ o → o < c.read + n → (c.st o).isSome = true) :
      Step c (c.consume n)

inductive Reaches : Content → Content → Prop
  | refl (c : Content) : Reaches c c
  | step {a b c : Content} : Reaches a b → Step b c → Reaches a c

def Content.init : Content := ⟨fun _ => none, 0, []⟩

/-- No stored byte is ever changed. -/
theorem stored_immutable {a b : Content} (h : Step a b) (o v : Nat) (hv : a.st o = some v) : b.st o = some v := by
  cases h with
  | store lo e g hok => simp [Content.store, hv]
  | consume n hs => simpa [Content.consume] using hv

def Inv (c : Content) : Prop := c.log.length = c.read ∧ ∀ o, o < c.read → c.log[o]? = c.st o

theorem inv_step {a b : Content} (hi : Inv a) (h : Step a b) : Inv b := by
  cases h with
  | store lo e g hok =>
    refine ⟨hi.1, fun o ho => ?_⟩
    have h1 := hi.2 o ho
    have hsome : ∃ v, a.st o = some v := by
      have hlen : o < a.log.length := by rw [hi.1]; exact ho
      have : a.log[o]?.isSome = true := by
        simp [List.getElem?_eq_getElem hlen]
      rw [h1] at this
      exact Option.isSome_iff_exists.mp this
    obtain ⟨v, hv⟩ := hsome
    show a.log[o]? = (a.store lo e g).st o
    simp [Content.store, hv, h1]
  | consume n hs =>
    refine ⟨?_, fun o ho => ?_⟩
    · simp [Content.consume, hi.1]
    · have ho' : o < a.read + n := ho
      have hl : a.log.length = a.read := hi.1
      show (a.log ++ (List.range n).map (fun k => (a.st (a.read + k)).getD 0))[o]? = a.st o
      by_cases hlt : o < a.read
      · rw [List.getElem?_append_left (by omega)]
        exact hi.2 o hlt
      · have hk : o - a.read < n := by omega
        rw [List.getElem?_append_right (by omega), hi.1]
        have hs' := hs o (by omega) (by omega)
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs'
        simp [hk, hv]
        have : a.read + (o - a.read) = o := by omega
        rw [this, hv]
        rfl

theorem inv_reaches {a b : Content} (hi : Inv a) (h : Reaches a b) : Inv b := by
  induction h with
  | refl => exact hi
  | step _ hs ih => exact inv_step ih hs

/-- The bytes delivered are the bytes stored, in offset order, each once: after any run of stores and consumes the
log has one byte per offset below the read position, and the byte at an offset is the one stored there. -/
theorem exactly_once_in_order {c : Content} (h : Reaches Content.init c) :
    c.log.length = c.read ∧ ∀ o, o < c.read → c.log[o]? = c.st o :=
  inv_reaches ⟨rfl, fun o ho => by simp [Content.init] at ho⟩ h

/-- A held-back frame stores nothing (`frame_held_back`), so it is the identity on the content, and its
retransmission, once the stream is admitted, stores the same bytes as the first arrival would have: the bytes
delivered are the bytes stored, in offset order, each once, whether or not the first arrival was held back. -/
theorem held_back_delivers_once {c : Content} (h : Reaches Content.init c) (lo e : Nat) (g : Nat → Nat)
    (hok : ∀ o, lo ≤ o → o < e → ∀ v, c.st o = some v → v = g o) :
    Reaches c c ∧ Reaches c (c.store lo e g) ∧ (c.store lo e g).log.length = (c.store lo e g).read ∧
      ∀ o, o < (c.store lo e g).read → (c.store lo e g).log[o]? = (c.store lo e g).st o :=
  ⟨Reaches.refl c, Reaches.step (Reaches.refl c) (Step.store c lo e g hok),
    exactly_once_in_order (Reaches.step h (Step.store c lo e g hok))⟩

end Pinc.TransportStreams
