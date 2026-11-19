import Pinc.TransportFramePack

/-!
# The PINCER packet builder: the theorems

For the model of `TransportFramePack.lean`:

* **The header** (`header_eq`, `chunk_bytes`): `put_stream_header` into exactly `stream_overhead` bytes fills them
  with the header `write` gives a STREAM frame with its length, so a chunk is written as the encoding of its frame.
* **The dropped length** (`implicit_spec`, `implicit_refuses`): `implicit_stream_len` on frames that end with the
  encoding of a STREAM frame with its length, at the place and header size of that frame, gives the frames with
  the encoding of the same frame without its length, shorter by the bytes of the length; when anything follows that
  frame it refuses and changes nothing.
* **The place kept** (`fill_hint`): the place the fill keeps is the start of its last frame, a STREAM frame with its
  length, and the header size of that frame.
* **The tail of `build_packet`** (`finish_ok`, `finish_frames`, `finish_lastOnly`): the `?` after
  `implicit_stream_len` never gives up a fill, and the payload sealed is read by `FrameIter`, with no error, as the
  frames written in order, the last one without its length when it was dropped, then one PADDING frame for the
  padding; a frame without a length is only the last, and never in a padded payload.
* **The order** (`fill_ordered`): the frames of a fill come in the order of the slots of `fill_frames`.
* **The tail repair** (`pick_took`, `pick_keeps`, `pick_probe_then_repair`): only a packet `build_app` builds as a
  repair reads the pending repair; a path MTU probe, the probe timeout's packet and a packet on another path leave it
  pending, so a repair due together with a probe goes with the next packet. `pickOld_loses` is the witness of the rule
  before #293: the probe packet took the repair and carried none of it.
* **The end of the build** (`dropped_iff`, `carried_or_short`, `after_nofill`, `after_unsealed`, `after_leaves`): the
  fill drops exactly a repair no packet can carry, and otherwise writes its first frame or stops at it for want of
  room in the payload; the repair leaves the pending state exactly when the packet built for it is sealed or nothing a
  packet can carry is left of it, so a build that ends without a packet leaves it pending. `afterOld_loses` is the
  witness of the rule before #433 (taken when the build started, so a build that ended without a packet lost it).
  `after_short_sealed` and `after_short_reached` are a finding: a packet whose payload has no room for the repair's
  first frame, sealed with its ACK alone, takes the repair that no packet then carries.
-/

namespace Pinc.TransportFramePack
open Pinc Pinc.TransportFrame
open Pinc.Varint (ValidBytes)

/-! ## `put_stream_header` -/

theorem runPutsPart_of_ok (cap : Nat) : ∀ (ps : List Put) (w w' : List Nat), runPuts cap w ps = .ok w' →
    runPutsPart cap w ps = (true, w')
  | [], w, w', h => by
    simp only [runPuts, Except.ok.injEq] at h
    simp [runPutsPart, h]
  | p :: ps, w, w', h => by
    simp only [runPuts] at h
    simp only [runPutsPart]
    cases hp : put cap w p with
    | error e => rw [hp] at h; cases h
    | ok w1 =>
      rw [hp] at h
      exact runPutsPart_of_ok cap ps w1 w' h

/-- The bytes of the header. -/
def headerBytes (id off len : Nat) (fin : Bool) : List Nat := flat (headerPuts id off len fin)

theorem stype_small (off : Nat) (fin imp : Bool) : Varint.encodeBytes (streamType off fin imp) = [streamType off fin imp] :=
  enc_small _ (Nat.lt_trans (streamType_lt off fin imp) (by omega))

theorem headerBytes_eq (id off len : Nat) (fin : Bool) :
    headerBytes id off len fin =
      [streamType off fin false] ++ Varint.encodeBytes id ++ (if off = 0 then [] else Varint.encodeBytes off) ++
        Varint.encodeBytes len := by
  unfold headerBytes headerPuts
  by_cases ho : off = 0 <;> simp [ho, flat, stype_small]

theorem headerBytes_length (id off len : Nat) (fin : Bool) :
    (headerBytes id off len fin).length = streamOverhead id off len false := by
  rw [headerBytes_eq]
  unfold streamOverhead
  by_cases ho : off = 0 <;> simp [ho, Varint.length_encodeBytes] <;> omega

/-- `put_stream_header` into exactly `stream_overhead` bytes writes the header and reports it full. -/
theorem header_eq (id off len : Nat) (fin : Bool) (hid : id < Varint.limit) (hoff : off < Varint.limit)
    (hlen : len < Varint.limit) :
    putStreamHeader (streamOverhead id off len false) id off len fin = (true, headerBytes id off len fin) := by
  have hok : PutsOk (headerPuts id off len fin) := by
    intro x hx
    unfold headerPuts at hx
    have := streamType_lt off fin false
    by_cases ho : off = 0
    · simp [ho] at hx
      rcases hx with rfl | rfl | rfl <;> first | assumption | (have := streamType_lt 0 fin false; rw [limit_eq]; omega)
    · simp [ho] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> first | assumption | (rw [limit_eq]; omega)
  have hl := headerBytes_length id off len fin
  unfold headerBytes at hl
  have hrun := runPuts_ok (streamOverhead id off len false) (headerPuts id off len fin) [] hok (by simp [hl])
  have := runPutsPart_of_ok _ _ _ _ hrun
  unfold putStreamHeader
  rw [this]
  simp [headerBytes, hl]

theorem chunk_good_bounds (c : Chunk) (hg : c.frame.Good) :
    c.id < Varint.limit ∧ c.off < Varint.limit ∧ c.data.length < Varint.limit ∧ ValidBytes c.data := by
  obtain ⟨hwf, hv⟩ := hg
  rw [validate_ok_iff] at hv
  obtain ⟨hv, hs, _⟩ := hv
  have h1 := hv c.id (by simp [Chunk.frame, Frame.varintFields])
  have h2 := hv c.off (by simp [Chunk.frame, Frame.varintFields])
  have h3 := hs c.id c.off c.fin c.data false rfl
  refine ⟨h1, h2, ?_, hwf⟩
  simp only [maxEnd] at h3
  rw [limit_eq]
  omega

/-- A chunk is written as the encoding of its STREAM frame with its length. -/
theorem chunk_bytes (c : Chunk) (hg : c.frame.Good) : c.bytes = c.frame.bytes := by
  obtain ⟨h1, h2, h3, _⟩ := chunk_good_bounds c hg
  unfold Chunk.bytes
  rw [header_eq _ _ _ _ h1 h2 h3]
  simp only [Chunk.frame, Frame.bytes, Frame.puts, headerBytes, headerPuts]
  simp only [Bool.false_eq_true, ite_false, flat_append]
  simp [flat]

/-! ## `implicit_stream_len` -/

theorem clearLen_stype (off : Nat) (fin : Bool) : clearLen (streamType off fin false) = streamType off fin true := by
  unfold clearLen streamType
  by_cases ho : off = 0 <;> cases fin <;> simp [ho]

/-- The encoding of a chunk's frame: the header up to the length, the length, the data. -/
theorem chunk_frame_bytes (c : Chunk) :
    c.frame.bytes = (streamType c.off c.fin false :: (Varint.encodeBytes c.id ++
        (if c.off = 0 then [] else Varint.encodeBytes c.off))) ++ (Varint.encodeBytes c.data.length ++ c.data) := by
  simp only [Chunk.frame, Frame.bytes, Frame.puts]
  by_cases ho : c.off = 0 <;> simp [ho, flat, stype_small]

theorem implicit_frame_bytes (c : Chunk) :
    (Frame.stream c.id c.off c.fin c.data true).bytes = (streamType c.off c.fin true :: (Varint.encodeBytes c.id ++
        (if c.off = 0 then [] else Varint.encodeBytes c.off))) ++ c.data := by
  simp only [Frame.bytes, Frame.puts]
  by_cases ho : c.off = 0 <;> simp [ho, flat, stype_small]

theorem chunk_head (c : Chunk) :
    (streamType c.off c.fin false :: (Varint.encodeBytes c.id ++
        (if c.off = 0 then [] else Varint.encodeBytes c.off))).length = c.head := by
  unfold Chunk.head streamOverhead
  by_cases ho : c.off = 0 <;> simp [ho, Varint.length_encodeBytes] <;> omega

/-- The dropped length: at the place and header size of a STREAM frame with its length that ends the frames,
`implicit_stream_len` gives the frames with the same STREAM frame without its length, shorter by the length's
bytes. -/
theorem implicit_spec (P : List Nat) (c : Chunk) (hg : c.frame.Good) :
    implicitStreamLen (P ++ c.frame.bytes) P.length c.head =
      some (Varint.encodedLen c.data.length, P ++ (Frame.stream c.id c.off c.fin c.data true).bytes) := by
  obtain ⟨_, _, h3, _⟩ := chunk_good_bounds c hg
  rw [chunk_frame_bytes, implicit_frame_bytes, ← clearLen_stype]
  have hhead := chunk_head c
  generalize hH : (Varint.encodeBytes c.id ++ if c.off = 0 then [] else Varint.encodeBytes c.off) = H at *
  rw [← hhead]
  generalize streamType c.off c.fin false = t
  generalize c.data = D at *
  have hpos : P.length + (t :: H).length = (P ++ t :: H).length := by simp
  unfold implicitStreamLen
  have hdrop : (P ++ (t :: H ++ (Varint.encodeBytes D.length ++ D))).drop (P.length + (t :: H).length) =
      Varint.encodeBytes D.length ++ D := by
    rw [hpos, ← List.append_assoc, List.drop_left]
  have htake : (P ++ (t :: H ++ (Varint.encodeBytes D.length ++ D))).take (P.length + (t :: H).length) = P ++ t :: H := by
    rw [hpos, ← List.append_assoc, List.take_left]
  have hdrop2 : (P ++ (t :: H ++ (Varint.encodeBytes D.length ++ D))).drop
      (P.length + (t :: H).length + (Varint.encodeBytes D.length).length) = D := by
    have : P.length + (t :: H).length + (Varint.encodeBytes D.length).length =
        (P ++ t :: H ++ Varint.encodeBytes D.length).length := by simp; omega
    rw [this, ← List.append_assoc, ← List.append_assoc, List.drop_left]
  have hlen : (P ++ (t :: H ++ (Varint.encodeBytes D.length ++ D))).length =
      P.length + (t :: H).length + (Varint.encodeBytes D.length).length + D.length := by simp; omega
  rw [if_neg (by rw [hlen]; omega), hdrop, Varint.decode_encode _ _ h3]
  simp only
  rw [if_neg (by rw [hlen]; omega), htake, hdrop2, if_pos (by simp)]
  have hget : (P ++ (t :: H ++ (Varint.encodeBytes D.length ++ D))).getD P.length 0 = t := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  rw [hget, Varint.length_encodeBytes]
  simp [List.set_append_right]


/-- The check: when anything follows the STREAM frame, `implicit_stream_len` refuses (and so changes nothing). -/
theorem implicit_refuses (P : List Nat) (c : Chunk) (hg : c.frame.Good) (rest : List Nat) (hr : rest ≠ []) :
    implicitStreamLen (P ++ c.frame.bytes ++ rest) P.length c.head = none := by
  obtain ⟨_, _, h3, _⟩ := chunk_good_bounds c hg
  rw [chunk_frame_bytes]
  have hhead := chunk_head c
  generalize hH : (Varint.encodeBytes c.id ++ if c.off = 0 then [] else Varint.encodeBytes c.off) = H at *
  rw [← hhead]
  generalize streamType c.off c.fin false = t
  generalize c.data = D at *
  have hr' : 0 < rest.length := by cases rest <;> simp_all
  have hpos : P.length + (t :: H).length = (P ++ t :: H).length := by simp
  unfold implicitStreamLen
  have hdrop : (P ++ (t :: H ++ (Varint.encodeBytes D.length ++ D)) ++ rest).drop (P.length + (t :: H).length) =
      Varint.encodeBytes D.length ++ (D ++ rest) := by
    rw [hpos]
    simp
  have hlen : (P ++ (t :: H ++ (Varint.encodeBytes D.length ++ D)) ++ rest).length =
      P.length + (t :: H).length + (Varint.encodeBytes D.length).length + D.length + rest.length := by simp; omega
  rw [if_neg (by rw [hlen]; omega), hdrop, Varint.decode_encode _ _ h3]
  simp only
  rw [if_pos (by rw [hlen]; omega)]

/-! ## The fill -/

/-- A frame as `fill_frames` writes it: never PADDING, always with its length. -/
def Plain : Frame → Prop
  | .padding _ => False
  | .stream _ _ _ _ imp => imp = false
  | .datagram _ imp => imp = false
  | _ => True

theorem plain_sep (f : Frame) (h : Plain f) (rest : List Nat) : f.Sep rest := by
  cases f <;> simp_all [Plain, Frame.Sep]

/-- What the fill wrote: every frame is one `write` accepts, never PADDING, always with its length (the code writes
only through `write`, `write_ack` and `put_stream_header`, and builds every STREAM and DATAGRAM frame with its
length). -/
def Fill.WF (f : Fill) : Prop := ∀ x ∈ f.items, x.2.frame.Good ∧ Plain x.2.frame

theorem itemBytes_append (xs ys : List (Nat × Item)) : itemBytes (xs ++ ys) = itemBytes xs ++ itemBytes ys := by
  simp [itemBytes]

theorem item_bytes (x : Item) (hg : x.frame.Good) : x.bytes = x.frame.bytes := by
  cases x with
  | fr f => rfl
  | ch c => exact chunk_bytes c hg

theorem itemBytes_eq : ∀ (xs : List (Nat × Item)), (∀ x ∈ xs, x.2.frame.Good) →
    itemBytes xs = payload (xs.map (fun x => x.2.frame))
  | [], _ => by simp [itemBytes, payload]
  | x :: xs, h => by
    have := itemBytes_eq xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [itemBytes, List.map_cons, List.flatten_cons] at this ⊢
    rw [this, item_bytes x.2 (h x (List.mem_cons_self ..))]
    rfl

/-- The fill is the encodings of its frames one after the other. -/
theorem fill_bytes (f : Fill) (hwf : f.WF) : f.bytes = payload f.frames :=
  itemBytes_eq f.items (fun x hx => (hwf x hx).1)

theorem payload_append : ∀ (fs gs : List Frame), payload (fs ++ gs) = payload fs ++ payload gs
  | [], gs => by simp [payload]
  | f :: fs, gs => by simp [payload, payload_append fs gs]

theorem packet_plain : ∀ (fs gs : List Frame), (∀ f ∈ fs, f.Good ∧ Plain f) → Packet gs → Packet (fs ++ gs)
  | [], _, _, hg => hg
  | f :: fs, gs, h, hg => by
    have hf := h f (List.mem_cons_self ..)
    exact ⟨hf.1, plain_sep f hf.2 _, packet_plain fs gs (fun g hg' => h g (List.mem_cons_of_mem _ hg')) hg⟩

/-- The place kept: the start of the last frame of the fill, a STREAM frame with its length, and the size of its
header before the length. -/
theorem fill_hint (f : Fill) (hwf : f.WF) (p hd : Nat) (h : f.hint = some (p, hd)) :
    ∃ (pre : List Frame) (c : Chunk), f.frames = pre ++ [c.frame] ∧ p = (payload pre).length ∧ hd = c.head ∧
      c.frame.Good ∧
      ∀ g ∈ pre, g.Good ∧ Plain g := by
  cases f with
  | normal ack ctl path streams dgrams late ping =>
    simp only [Fill.hint] at h
    split at h
    · rename_i hdl
      obtain ⟨rfl, rfl⟩ := hdl
      cases hl : streams.getLast? with
      | none => rw [hl] at h; simp at h
      | some c =>
        rw [hl] at h
        simp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
          let X := optF 1 ack ++ ctl.items ++ path.items ++ ys.map (fun c => (13, Item.ch c))
          have hbody : bodyItems ack ctl path (ys ++ [c]) [] [] = X ++ [(13, .ch c)] := by
            simp [bodyItems, X]
          have hany : (bodyItems ack ctl path (ys ++ [c]) [] []).any (fun x => x.2.elicits) = true := by
            rw [hbody, List.any_eq_true]
            exact ⟨(13, .ch c), by simp, rfl⟩
          have hitems : (Fill.normal ack ctl path (ys ++ [c]) [] [] ping).items = X ++ [(13, .ch c)] := by
            rw [hbody] at hany
            simp only [Fill.items, hbody, hany, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false,
              List.append_nil]
          have hwf' : ∀ x ∈ X ++ [(13, Item.ch c)], x.2.frame.Good ∧ Plain x.2.frame := by
            rw [← hitems]; exact hwf
          refine ⟨X.map (fun x => x.2.frame), c, ?_, ?_, rfl, ?_, ?_⟩
          · simp only [Fill.frames, hitems, List.map_append, List.map_cons, List.map_nil]
            rfl
          · rw [← itemBytes_eq X (fun x hx => (hwf' x (List.mem_append_left _ hx)).1)]
            simp [X, List.dropLast_concat]
          · exact (hwf' (13, .ch c) (by simp)).1
          · intro g hg
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
            exact hwf' x (List.mem_append_left _ hx)
        · simp at h
    · simp at h
  | pingOnly => simp [Fill.hint] at h
  | probe => simp [Fill.hint] at h
  | repair => simp [Fill.hint] at h

theorem padding_good (k : Nat) (hk : 0 < k) : (Frame.padding k).Good :=
  ⟨by simp only [Frame.WF]; omega, by simp [Frame.validate, Frame.varintFields, Varint.limit]⟩

theorem implicit_good (c : Chunk) (hg : c.frame.Good) : (Frame.stream c.id c.off c.fin c.data true).Good := by
  obtain ⟨hwf, hv⟩ := hg
  exact ⟨hwf, by simpa [Chunk.frame, Frame.validate, Frame.varintFields] using hv⟩

theorem padding_bytes (k : Nat) : (Frame.padding k).bytes = List.replicate k 0 := by
  simp [Frame.bytes, Frame.puts, zeroChunks_flat]

/-- The tail of `build_packet` on a fill: the `?` never gives it up, and the payload sealed reads back, with no
error, as the frames written in order, the last without its length when it was dropped, then one PADDING frame for
the padding; it is the fill padded to the least payload, or the fill less the bytes of the length dropped. -/
theorem finish_frames (f : Fill) (hwf : f.WF) (minp : Nat) :
    ∃ pay pad n, finish f.bytes f.hint minp = some (pay, pad, n) ∧ frames pay = (expected f.frames pad n, none) ∧
      (0 < pad → n = 0 ∧ pay.length = minp) ∧ (pad = 0 → pay.length + n = f.bytes.length) := by
  have hb := fill_bytes f hwf
  have hpl : ∀ g ∈ f.frames, g.Good ∧ Plain g := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
    exact hwf x hx
  unfold finish
  by_cases hlt : f.bytes.length < minp
  · rw [if_pos hlt]
    refine ⟨_, _, _, rfl, ?_, fun _ => ⟨rfl, by simp; omega⟩, fun h => by omega⟩
    have hk : 0 < minp - f.bytes.length := by omega
    have : f.bytes ++ List.replicate (minp - f.bytes.length) 0 =
        payload (f.frames ++ [.padding (minp - f.bytes.length)]) := by
      rw [payload_append, hb]
      simp [payload, padding_bytes]
    rw [this, frames_bytes _ (packet_plain _ _ hpl
      (by simp only [Packet]; exact ⟨padding_good _ hk, by simp [Frame.Sep, zeroRun, payload], trivial⟩))]
    simp [expected, hk]
  · rw [if_neg hlt]
    have hplain : frames f.bytes = (f.frames, none) := by
      rw [hb]
      have := frames_bytes (f.frames ++ []) (packet_plain _ _ hpl (by simp [Packet]))
      simpa using this
    cases hh : f.hint with
    | none =>
      simp only
      exact ⟨_, _, _, rfl, by simpa [expected] using hplain, fun h => by omega, fun _ => by simp⟩
    | some ph =>
      obtain ⟨p, hd⟩ := ph
      simp only
      by_cases hle : p + hd ≤ f.bytes.length
      · rw [if_pos hle]
        obtain ⟨pre, c, hfs, rfl, rfl, hgc, hpre⟩ := fill_hint f hwf p hd hh
        have hbytes : f.bytes = payload pre ++ c.frame.bytes := by
          rw [hb, hfs, payload_append]
          simp [payload]
        rw [hbytes, implicit_spec _ c hgc]
        simp only
        refine ⟨_, _, _, rfl, ?_, fun h => by omega, fun _ => ?_⟩
        · have : payload pre ++ (Frame.stream c.id c.off c.fin c.data true).bytes =
              payload (pre ++ [.stream c.id c.off c.fin c.data true]) := by
            rw [payload_append]
            simp [payload]
          rw [this, frames_bytes _ (packet_plain _ _ hpre
            (by simp only [Packet]; exact ⟨implicit_good c hgc, by simp [Frame.Sep, payload], trivial⟩))]
          have hpos := Varint.encodedLen_pos c.data.length
          simp [expected, hfs, hpos, Chunk.frame, List.dropLast_concat]
        · have h1 := implicit_frame_bytes c
          have h2 := chunk_frame_bytes c
          rw [h1]
          rw [h2]
          simp [Varint.length_encodeBytes]
          omega
      · rw [if_neg hle]
        exact ⟨_, _, _, rfl, by simpa [expected] using hplain, fun h => by omega, fun _ => by simp⟩

/-- The `?` after `implicit_stream_len` never gives up a fill: its frames were already taken from their owners. -/
theorem finish_ok (f : Fill) (hwf : f.WF) (minp : Nat) : finish f.bytes f.hint minp ≠ none := by
  obtain ⟨pay, pad, n, h, _⟩ := finish_frames f hwf minp
  rw [h]
  simp

/-- A frame without a length is only the last frame read: every frame before it is one with its length, and so is
every frame of a padded payload but the PADDING. -/
theorem finish_lastOnly (fs : List Frame) (h : ∀ g ∈ fs, Plain g) (pad n : Nat) (hpn : 0 < pad → n = 0) :
    ∀ g ∈ (expected fs pad n).dropLast, Plain g := by
  intro g hg
  unfold expected at hg
  by_cases hp : 0 < pad
  · have hn := hpn hp
    subst hn
    simp only [Nat.lt_irrefl, ite_false, hp, ite_true, List.dropLast_concat] at hg
    exact h g hg
  · simp only [hp, ite_false] at hg
    split at hg
    · split at hg
      · rename_i heq
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp heq
        simp only [List.dropLast_concat] at hg
        exact h g (List.mem_append_left _ hg)
      · exact h g ((List.dropLast_sublist _).subset hg)
    · exact h g ((List.dropLast_sublist _).subset hg)


/-! ## The order of the slots -/

section Order
variable (tbl : List (List String × Bool))

/-- Frames with their slots and kinds that the slots of `tbl` allow from slot `i`: each slot at or after the
current one, writing the frame's kind, and a slot of at most one frame passed after its frame. -/
def SlotsOK : Nat → List (Nat × String) → Prop
  | _, [] => True
  | i, (s, k) :: xs =>
    i ≤ s ∧ 1 ≤ s ∧ s ≤ tbl.length ∧ (slotAt tbl s).1.contains k = true ∧ SlotsOK (nextSlot tbl s) xs

theorem firstSlotFrom_le (k : String) (s : Nat) (hk : (slotAt tbl s).1.contains k = true) :
    ∀ n j, j ≤ s → s < j + n → ∃ j', firstSlotFrom tbl k j n = some j' ∧ j ≤ j' ∧ j' ≤ s := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j hj hs
    simp only [firstSlotFrom]
    split
    · exact ⟨j, rfl, Nat.le_refl _, hj⟩
    · rename_i hne
      have hjs : j ≠ s := by intro e; subst e; exact hne hk
      obtain ⟨j', h1, h2, h3⟩ := ih (j + 1) (by omega) (by omega)
      exact ⟨j', h1, by omega, h3⟩

theorem nextSlot_le (j s : Nat) (h : j ≤ s) : nextSlot tbl j ≤ nextSlot tbl s := by
  unfold nextSlot
  by_cases hj : j = s
  · subst hj; exact Nat.le_refl _
  · split <;> split <;> omega

/-- The greedy matcher accepts every list of frames the slots allow, from any earlier slot. -/
theorem matchFrom_of : ∀ (xs : List (Nat × String)) (i i' : Nat), SlotsOK tbl i xs → i' ≤ i →
    matchFrom tbl (xs.map Prod.snd) i' = true
  | [], _, _, _, _ => by simp [matchFrom]
  | (s, k) :: xs, i, i', h, hi => by
    obtain ⟨his, hs1, hsl, hk, hrest⟩ := h
    obtain ⟨j, hj, hj1, hj2⟩ := firstSlotFrom_le tbl k s hk (tbl.length + 1 - max i' 1) (max i' 1)
      (by omega) (by omega)
    simp only [List.map_cons, matchFrom, firstSlot, hj]
    exact matchFrom_of xs _ _ hrest (nextSlot_le tbl j s hj2)

/-- Where the slots stand after a list of frames. -/
def nextAfter : Nat → List (Nat × String) → Nat
  | i, [] => i
  | _, (s, _) :: xs => nextAfter (nextSlot tbl s) xs

theorem slotsOK_append : ∀ (xs ys : List (Nat × String)) (i : Nat), SlotsOK tbl i xs →
    SlotsOK tbl (nextAfter tbl i xs) ys →
      SlotsOK tbl i (xs ++ ys) ∧ nextAfter tbl i (xs ++ ys) = nextAfter tbl (nextAfter tbl i xs) ys
  | [], ys, i, _, h => ⟨h, rfl⟩
  | (s, k) :: xs, ys, i, ⟨h1, h2, h3, h4, h5⟩, h => by
    obtain ⟨a, b⟩ := slotsOK_append xs ys (nextSlot tbl s) h5 h
    exact ⟨⟨h1, h2, h3, h4, a⟩, b⟩

/-- A section of a fill: frames the slots allow from any slot up to `lo`, after which the slots stand at most at
`hi` (or where they were). -/
def Sec (lo hi : Nat) (xs : List (Nat × String)) : Prop :=
  ∀ i, i ≤ lo → SlotsOK tbl i xs ∧ nextAfter tbl i xs ≤ max i hi

theorem sec_append (lo1 hi1 lo2 hi2 : Nat) (xs ys : List (Nat × String)) (h1 : Sec tbl lo1 hi1 xs)
    (h2 : Sec tbl lo2 hi2 ys) (h12 : hi1 ≤ lo2) (hlo : lo1 ≤ hi1) (hhi : hi1 ≤ hi2) : Sec tbl lo1 hi2 (xs ++ ys) := by
  intro i hi
  obtain ⟨a1, b1⟩ := h1 i hi
  obtain ⟨a2, b2⟩ := h2 (nextAfter tbl i xs) (by omega)
  obtain ⟨c, d⟩ := slotsOK_append tbl xs ys i a1 a2
  exact ⟨c, by rw [d]; omega⟩

theorem sec_nil (lo hi : Nat) : Sec tbl lo hi [] := fun i _ => ⟨trivial, by simp only [nextAfter]; omega⟩

theorem sec_one (s : Nat) (k : String) (hs1 : 1 ≤ s) (hsl : s ≤ tbl.length) (hk : (slotAt tbl s).1.contains k = true)
    (hl : (slotAt tbl s).2 = false) : Sec tbl s (s + 1) [(s, k)] := by
  intro i hi
  refine ⟨⟨hi, hs1, hsl, hk, trivial⟩, ?_⟩
  simp only [nextAfter, nextSlot, hl]; simp; omega

theorem sec_loop (s : Nat) (hs1 : 1 ≤ s) (hsl : s ≤ tbl.length) (hl : (slotAt tbl s).2 = true) :
    ∀ xs : List (Nat × String), (∀ x ∈ xs, x.1 = s ∧ (slotAt tbl s).1.contains x.2 = true) → Sec tbl s s xs
  | [], _ => sec_nil tbl s s
  | (s', k) :: xs, h => by
    obtain ⟨rfl, hk⟩ := h (s', k) (List.mem_cons_self ..)
    have ih := sec_loop s' hs1 hsl hl xs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    intro i hi
    have hn : nextSlot tbl s' = s' := by simp [nextSlot, hl]
    obtain ⟨a, b⟩ := ih s' (Nat.le_refl _)
    refine ⟨⟨hi, hs1, hsl, hk, by rw [hn]; exact a⟩, ?_⟩
    simp only [nextAfter, hn]
    omega

theorem sec_opt (s : Nat) (k : String) (hs1 : 1 ≤ s) (hsl : s ≤ tbl.length)
    (hk : (slotAt tbl s).1.contains k = true) (hl : (slotAt tbl s).2 = false) (xs : List (Nat × String))
    (h : xs = [] ∨ xs = [(s, k)]) : Sec tbl s (s + 1) xs := by
  rcases h with rfl | rfl
  · exact sec_nil tbl _ _
  · exact sec_one tbl s k hs1 hsl hk hl

end Order

/-- The kinds the code gives the frames of the slots that take any frame value: the ACK is an ACK, the REKEY a
REKEY, and the stream layer's control frames (`control_frame`) are credit, reset and stop frames. -/
def Fill.Kinds : Fill → Prop
  | .normal ack ctl _ _ _ late _ =>
    (∀ a, ack = some a → a.kind = "Ack") ∧ (∀ r, ctl.rekey = some r → r.kind = "Rekey") ∧
      (∀ g ∈ ctl.sc, scKinds.contains g.kind = true) ∧ (∀ g ∈ late, scKinds.contains g.kind = true)
  | .pingOnly ack .. | .probe ack .. | .repair ack .. => ∀ a, ack = some a → a.kind = "Ack"

/-- The slots and kinds of the items. -/
def sk (xs : List (Nat × Item)) : List (Nat × String) := xs.map (fun x => (x.1, x.2.frame.kind))

theorem sk_append (xs ys : List (Nat × Item)) : sk (xs ++ ys) = sk xs ++ sk ys := by simp [sk]

theorem sk_opt (s : Nat) (b : Bool) (f : Frame) : sk (opt s b f) = [] ∨ sk (opt s b f) = [(s, f.kind)] := by
  cases b <;> simp [sk, opt, Item.frame]

theorem sk_optF (s : Nat) (o : Option Frame) (k : String) (h : ∀ a, o = some a → a.kind = k) :
    sk (optF s o) = [] ∨ sk (optF s o) = [(s, k)] := by
  cases o with
  | none => simp [sk, optF]
  | some a => simp [sk, optF, Item.frame, h a rfl]

theorem sk_map_loop (s : Nat) {α : Type} (l : List α) (g : α → Item) (p : String → Prop)
    (h : ∀ a ∈ l, p (g a).frame.kind) : ∀ x ∈ sk (l.map (fun a => (s, g a))), x.1 = s ∧ p x.2 := by
  intro x hx
  simp only [sk, List.map_map, List.mem_map, Function.comp] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨rfl, h a ha⟩

theorem map_kind {α : Type} (o : Option α) (g : α → Frame) (k : String) (hk : ∀ x, (g x).kind = k) :
    ∀ a, o.map g = some a → a.kind = k := by
  intro a h
  cases o with
  | none => simp at h
  | some v =>
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact hk v

/-- The order: the frames of a fill come in the order of the slots of `fill_frames` for its mode. -/
theorem fill_ordered (f : Fill) (hk : f.Kinds) : ordered f.mode f.frames = true := by
  have key : ∀ (m : Mode) (xs : List (Nat × Item)) (hi : Nat), Sec (slotTable m) 1 hi (sk xs) →
      matchFrom (slotTable m) (xs.map (fun x => x.2.frame.kind)) 1 = true := by
    intro m xs hi h
    have := matchFrom_of (slotTable m) (sk xs) 1 1 (h 1 (Nat.le_refl _)).1 (Nat.le_refl _)
    have e : (sk xs).map Prod.snd = xs.map (fun x => x.2.frame.kind) := by simp [sk]
    rwa [e] at this
  unfold ordered Fill.frames
  rw [List.map_map]
  cases f with
  | normal ack ctl path streams dgrams late ping =>
    obtain ⟨hack, hrk, hsc, hlate⟩ := hk
    let T := slotTable .normal
    apply key .normal _ 17
    have one : ∀ s k, 1 ≤ s → s ≤ 16 → (slotAt T s).1.contains k = true → (slotAt T s).2 = false →
        ∀ xs, (xs = [] ∨ xs = [(s, k)]) → Sec T s (s + 1) xs :=
      fun s k h1 h2 hk hl xs h => sec_opt T s k h1 (by simp [T, slotTable]; omega) hk hl xs h
    have loop : ∀ s, 1 ≤ s → s ≤ 16 → (slotAt T s).2 = true → ∀ xs : List (Nat × String),
        (∀ x ∈ xs, x.1 = s ∧ (slotAt T s).1.contains x.2 = true) → Sec T s s xs :=
      fun s h1 h2 hl xs h => sec_loop T s h1 (by simp [T, slotTable]; omega) hl xs h
    have s1 := one 1 "Ack" (by omega) (by omega) (by decide) (by decide) _ (sk_optF 1 ack "Ack" hack)
    have s2 := one 2 "Sleep" (by omega) (by omega) (by decide) (by decide) _ (sk_opt 2 ctl.sleep .sleep)
    have s3 := one 3 "Wake" (by omega) (by omega) (by decide) (by decide) _ (sk_opt 3 ctl.wake .wake)
    have s4 := one 4 "MtuProbeEcho" (by omega) (by omega) (by decide) (by decide) _
      (sk_optF 4 (ctl.echo.map .mtuProbeEcho) "MtuProbeEcho" (map_kind _ _ _ fun _ => rfl))
    have s5 := one 5 "Ready" (by omega) (by omega) (by decide) (by decide) _ (sk_opt 5 ctl.ready .ready)
    have s6 := one 6 "NewTickets" (by omega) (by omega) (by decide) (by decide) _
      (sk_optF 6 (ctl.tickets.map .newTickets) "NewTickets" (map_kind _ _ _ fun _ => rfl))
    have s7 := one 7 "Rekey" (by omega) (by omega) (by decide) (by decide) _ (sk_optF 7 ctl.rekey "Rekey" hrk)
    have s8 := loop 8 (by omega) (by omega) (by decide) _
      (sk_map_loop 8 ctl.exts (fun e => Item.fr (.ext e.1 e.2)) (fun k => (slotAt T 8).1.contains k = true)
        (fun a _ => by simp only [Item.frame, Chunk.frame, Frame.kind]; decide))
    have s9 := loop 9 (by omega) (by omega) (by decide) _
      (sk_map_loop 9 ctl.sc (fun g => Item.fr g) (fun k => (slotAt T 9).1.contains k = true)
        (fun a ha => by show scKinds.contains a.kind = true; exact hsc a ha))
    have s10 := one 10 "PathResponse" (by omega) (by omega) (by decide) (by decide) _
      (sk_optF 10 (path.resp.map .pathResponse) "PathResponse" (map_kind _ _ _ fun _ => rfl))
    have s11 := one 11 "Ping" (by omega) (by omega) (by decide) (by decide) _ (sk_opt 11 path.ping .ping)
    have s12 := one 12 "PathChallenge" (by omega) (by omega) (by decide) (by decide) _
      (sk_optF 12 (path.chal.map .pathChallenge) "PathChallenge" (map_kind _ _ _ fun _ => rfl))
    have s13 := loop 13 (by omega) (by omega) (by decide) _
      (sk_map_loop 13 streams (fun c => Item.ch c) (fun k => (slotAt T 13).1.contains k = true)
        (fun a _ => by simp only [Item.frame, Chunk.frame, Frame.kind]; decide))
    have s14 := loop 14 (by omega) (by omega) (by decide) _
      (sk_map_loop 14 dgrams (fun d => Item.fr (.datagram d false)) (fun k => (slotAt T 14).1.contains k = true)
        (fun a _ => by simp only [Item.frame, Chunk.frame, Frame.kind]; decide))
    have s15 := loop 15 (by omega) (by omega) (by decide) _
      (sk_map_loop 15 late (fun g => Item.fr g) (fun k => (slotAt T 15).1.contains k = true)
        (fun a ha => by show scKinds.contains a.kind = true; exact hlate a ha))
    have s16 : ∀ b : Bool, Sec T 16 17 (sk (if b = true then [(16, Item.fr Frame.ping)] else [])) :=
      fun b => one 16 "Ping" (by omega) (by omega) (by decide) (by decide) _
        (by split <;> simp [sk, Item.frame, Frame.kind])
    simp only [Fill.items, bodyItems, Ctl.items, PathFr.items, sk_append, List.append_assoc]
    refine sec_append T 1 2 2 17 _ _ s1 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 2 3 3 17 _ _ s2 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 3 4 4 17 _ _ s3 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 4 5 5 17 _ _ s4 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 5 6 6 17 _ _ s5 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 6 7 7 17 _ _ s6 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 7 8 8 17 _ _ s7 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 8 8 9 17 _ _ s8 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 9 9 10 17 _ _ s9 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 10 11 11 17 _ _ s10 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 11 12 12 17 _ _ s11 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 12 13 13 17 _ _ s12 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 13 13 14 17 _ _ s13 ?_ (by omega) (by omega) (by omega)
    refine sec_append T 14 14 15 17 _ _ s14 ?_ (by omega) (by omega) (by omega)
    exact sec_append T 15 15 16 17 _ _ s15 (s16 _) (by omega) (by omega) (by omega)
  | pingOnly ack wake ping =>
    let T := slotTable .pingOnly
    apply key .pingOnly _ 4
    simp only [Fill.items, sk_append]
    have s1 := sec_opt T 1 "Ack" (by omega) (by decide) (by decide) (by decide) _ (sk_optF 1 ack "Ack" hk)
    have s2 := sec_opt T 2 "Wake" (by omega) (by decide) (by decide) (by decide) _ (sk_opt 2 wake .wake)
    have s3 := sec_opt T 3 "Ping" (by omega) (by decide) (by decide) (by decide) _ (sk_opt 3 ping .ping)
    have := sec_append T _ _ _ _ _ _ s1 s2 (by omega) (by omega) (by omega)
    have := sec_append T _ _ _ _ _ _ this s3 (by omega) (by omega) (by omega)
    simpa [List.append_assoc] using this
  | probe ack ping =>
    let T := slotTable .probe
    apply key .probe _ 3
    simp only [Fill.items, sk_append]
    have s1 := sec_opt T 1 "Ack" (by omega) (by decide) (by decide) (by decide) _ (sk_optF 1 ack "Ack" hk)
    have s2 := sec_opt T 2 "Ping" (by omega) (by decide) (by decide) (by decide) _ (sk_opt 2 ping .ping)
    exact sec_append T _ _ _ _ _ _ s1 s2 (by omega) (by omega) (by omega)
  | repair ack chunks =>
    let T := slotTable .repair
    apply key .repair _ 2
    simp only [Fill.items, sk_append]
    have s1 := sec_opt T 1 "Ack" (by omega) (by decide) (by decide) (by decide) _ (sk_optF 1 ack "Ack" hk)
    have s2 := sec_loop T 2 (by omega) (by decide) (by decide) _
      (sk_map_loop 2 chunks (fun c => Item.ch c) (fun k => (slotAt T 2).1.contains k = true)
        (fun a _ => by simp only [Item.frame, Chunk.frame, Frame.kind]; decide))
    exact sec_append T _ _ _ _ _ _ s1 s2 (by omega) (by omega) (by omega)

/-! ## The tail repair -/

/-- The pending repair is read exactly by a packet built as a repair, which goes on the active path with no path MTU
probe due and no probe timeout's packet owed; once a packet is sealed, a repair is still pending exactly when that
packet did not read it. -/
theorem pick_took (probes mtu pending active : Bool) :
    ((pick probes mtu pending active).2.1 = true ↔ (pick probes mtu pending active).1 = .repair) ∧
      ((pick probes mtu pending active).1 = .repair →
        pending = true ∧ active = true ∧ probes = false ∧ mtu = false) ∧
      (pick probes mtu pending active).2.2 = (pending && !(pick probes mtu pending active).2.1) := by
  cases probes <;> cases mtu <;> cases pending <;> cases active <;> decide

/-- A path MTU probe, the probe timeout's packet and a packet on another path do not read the repair and leave a pending
one pending. -/
theorem pick_keeps (probes mtu pending active : Bool) (h : probes = true ∨ mtu = true ∨ active = false) :
    (pick probes mtu pending active).2.1 = false ∧ (pick probes mtu pending active).2.2 = pending := by
  revert h
  cases probes <;> cases mtu <;> cases pending <;> cases active <;> decide

/-- A repair due together with a path MTU probe: the probe leaves without it, and it goes with the next packet built
on the active path with no probe due. -/
theorem pick_probe_then_repair :
    pick false true true true = (.probe, false, true) ∧ pick false false true true = (.repair, true, false) := by
  decide

/-- The rule before #293: the repair was taken for every packet on the active path with no probe timeout's packet
owed, a path MTU probe too. -/
def pickOld (probes mtu pending active : Bool) : Mode × Bool × Bool :=
  let took := pending && active && !probes
  (if probes then .pingOnly else if mtu then .probe else if took then .repair else .normal, took, pending && !took)

/-- The witness of the rule before #293: the probe packet, which carries only its PING, takes the pending repair, so
the repair is gone. -/
theorem pickOld_loses : pickOld false true true true = (.probe, true, false) := by decide

/-! ## The end of the build (#433) -/

/-- The first turn of the loop of `fill_repair`. -/
theorem repLoop_eight (c : Chunk) (cs : List Chunk) (room cap : Nat) :
    repLoop 8 (c :: cs) room cap =
      if room < c.data.length + 24 then ([], false)
      else if cap < c.size then ([], true)
      else (c :: (repLoop 7 cs (room - c.size) (cap - c.size)).1, (repLoop 7 cs (room - c.size) (cap - c.size)).2) :=
  rfl

/-- `fill_repair` drops exactly a repair that no packet can carry: its packet left the sent ring, each of its frames is
acknowledged, or the first does not fit the repair's budget. -/
theorem dropped_iff (inRing : Bool) (cs : List Chunk) (room cap : Nat) :
    dropped inRing cs room cap = !carriable inRing cs room := by
  cases inRing with
  | false => cases cs <;> simp [dropped, carriable]
  | true =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      simp only [dropped, carriable, repLoop_eight]
      by_cases h1 : room < c.data.length + 24
      · have h1' : ¬ c.data.length + 24 ≤ room := by omega
        simp [h1, h1']
      · have h1' : c.data.length + 24 ≤ room := by omega
        by_cases h2 : cap < c.size <;> simp [h1, h1', h2]

/-- A fill that reads a repair a packet can carry writes its first frame or stops at it for want of room in the
payload, so it never drops it. -/
theorem carried_or_short (cs : List Chunk) (room cap : Nat) (h : carriable true cs room = true) :
    (repLoop 8 cs room cap).1 ≠ [] ∨ (repLoop 8 cs room cap).2 = true := by
  cases cs with
  | nil => simp [carriable] at h
  | cons c cs =>
    simp only [carriable, Bool.true_and, decide_eq_true_eq] at h
    have h1 : ¬ room < c.data.length + 24 := by omega
    rw [repLoop_eight]
    by_cases h2 : cap < c.size <;> simp [h1, h2]

/-- A build that ends before its fill (a buffer with no room for a packet, no destination id) leaves the repair
pending. -/
theorem after_nofill : repairAfter false false = true := rfl

/-- A build whose fill read a repair a packet can carry and that ends without a packet (the sent ring has no slot,
sealing fails, nothing to send) leaves it pending. -/
theorem after_unsealed (inRing : Bool) (cs : List Chunk) (room cap : Nat) (h : carriable inRing cs room = true) :
    repairAfter false (dropped inRing cs room cap) = true := by
  simp [repairAfter, dropped_iff, h]

/-- A pending repair that a fill read leaves the pending state exactly when the packet built for it is sealed or
nothing a packet can carry is left of it. -/
theorem after_leaves (sealed inRing : Bool) (cs : List Chunk) (room cap : Nat) :
    repairAfter sealed (dropped inRing cs room cap) = false ↔
      (sealed = true ∨ carriable inRing cs room = false) := by
  rw [dropped_iff]
  cases sealed <;> cases hc : carriable inRing cs room <;> simp [repairAfter]

/-- The rule before #433: `build_app` took the pending repair when the build started, so it was gone whatever the
build then did. -/
def repairAfterOld (_sealed _dropped : Bool) : Bool := false

/-- The witness of the rule before #433: a repair a packet can carry (a FIN with no data, its packet in the ring) and a
build whose fill writes it but that ends without a packet (the sent ring has no slot): the rule before #433 loses it,
the code keeps it pending. -/
theorem afterOld_loses :
    carriable true [⟨0, 0, true, []⟩] 600 = true ∧
      repLoop 8 [⟨0, 0, true, []⟩] 600 64 = ([⟨0, 0, true, []⟩], false) ∧
      repairAfterOld false (dropped true [⟨0, 0, true, []⟩] 600 64) = false ∧
      repairAfter false (dropped true [⟨0, 0, true, []⟩] 600 64) = true := by
  decide

/-- The finding (`FramePack_short.cfg`): a repair packet whose payload has no room for the first frame of a repair a
packet can carry stops at that frame and writes none of the repair, and the fill keeps it; but when the packet's ACK
is due the packet is sealed with the ACK alone, and the seal takes the repair, which no packet carries then. -/
theorem after_short_sealed (c : Chunk) (cs : List Chunk) (room cap : Nat) (h1 : c.data.length + 24 ≤ room)
    (h2 : cap < c.size) :
    carriable true (c :: cs) room = true ∧ repLoop 8 (c :: cs) room cap = ([], true) ∧
      dropped true (c :: cs) room cap = false ∧ repairAfter true (dropped true (c :: cs) room cap) = false := by
  have h1' : ¬ room < c.data.length + 24 := by omega
  refine ⟨by simp [carriable, h1], by rw [repLoop_eight]; simp [h1', h2], ?_, by simp [repairAfter]⟩
  rw [dropped_iff]
  simp [carriable, h1]

/-- The case of the finding is reached: a FIN with no data and 2 bytes left in the payload after the ACK. -/
theorem after_short_reached :
    carriable true [⟨0, 0, true, []⟩] 600 = true ∧ repLoop 8 [⟨0, 0, true, []⟩] 600 2 = ([], true) ∧
      repairAfter true (dropped true [⟨0, 0, true, []⟩] 600 2) = false := by
  decide

end Pinc.TransportFramePack

#audit_axioms Pinc.TransportFramePack.header_eq
#audit_axioms Pinc.TransportFramePack.chunk_bytes
#audit_axioms Pinc.TransportFramePack.implicit_spec
#audit_axioms Pinc.TransportFramePack.implicit_refuses
#audit_axioms Pinc.TransportFramePack.fill_bytes
#audit_axioms Pinc.TransportFramePack.fill_hint
#audit_axioms Pinc.TransportFramePack.finish_frames
#audit_axioms Pinc.TransportFramePack.finish_ok
#audit_axioms Pinc.TransportFramePack.finish_lastOnly
#audit_axioms Pinc.TransportFramePack.matchFrom_of
#audit_axioms Pinc.TransportFramePack.fill_ordered
#audit_axioms Pinc.TransportFramePack.pick_took
#audit_axioms Pinc.TransportFramePack.pick_keeps
#audit_axioms Pinc.TransportFramePack.pick_probe_then_repair
#audit_axioms Pinc.TransportFramePack.pickOld_loses
#audit_axioms Pinc.TransportFramePack.dropped_iff
#audit_axioms Pinc.TransportFramePack.carried_or_short
#audit_axioms Pinc.TransportFramePack.after_nofill
#audit_axioms Pinc.TransportFramePack.after_unsealed
#audit_axioms Pinc.TransportFramePack.after_leaves
#audit_axioms Pinc.TransportFramePack.afterOld_loses
#audit_axioms Pinc.TransportFramePack.after_short_sealed
#audit_axioms Pinc.TransportFramePack.after_short_reached
