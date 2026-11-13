import Vinc.TransportFrame

/-!
# The VINCER frame codecs: the reader, the writer and the lengths

Theorems about the model of `TransportFrame.lean`:

* the reader: a varint read accepts exactly the encoding of its value (`rdVarint_enc`, `rdVarint_inv`, from
  `Varint.decode_encode` and `Varint.decode_canonical`), a byte read exactly its bytes (`rdBytes_append`,
  `rdBytes_inv`);
* the writer: once the varints are below 2^63 and the bytes fit, no call fails and the writer holds the bytes in
  order (`runPuts_ok`);
* `Frame.WF` says what a frame value of the code is (array lengths, byte ranges, an ACK whose ranges were
  validated), and for such a frame `write` is `validate`, then the room check against `encoded_len`, then exactly
  the bytes of the frame (`write_eq`): `encoded_len` is the number of bytes written (`bytes_length`), the only
  errors are those of `validate` and `BufferTooSmall` with the shortfall, and an error returns no writer, so the
  writer is as it was.
-/

namespace Vinc.TransportFrame
open Vinc
open Vinc.Varint (ValidBytes)

/-! ## The reader -/

@[simp] theorem andThen_ok {α β : Type} (a : α) (r : List Nat) (f : α → List Nat → Except Err β) :
    andThen (.ok (a, r)) f = f a r := rfl

@[simp] theorem andThen_error {α β : Type} (e : Err) (f : α → List Nat → Except Err β) :
    andThen (.error e : Rd α) f = .error e := rfl

theorem andThen_eq_ok {α β : Type} (x : Rd α) (f : α → List Nat → Except Err β) (y : β) :
    andThen x f = .ok y ↔ ∃ a r, x = .ok (a, r) ∧ f a r = .ok y := by
  cases x with
  | error e => simp [andThen]
  | ok p =>
    cases p with
    | mk a0 r0 =>
      show f a0 r0 = _ ↔ _
      constructor
      · intro h; exact ⟨_, _, rfl, h⟩
      · rintro ⟨a, r, h1, h2⟩; cases h1; exact h2

theorem valid_append (a b : List Nat) : ValidBytes (a ++ b) ↔ ValidBytes a ∧ ValidBytes b := by
  simp [ValidBytes, List.mem_append, or_imp, forall_and]

theorem valid_nil : ValidBytes [] := by simp [ValidBytes]

theorem valid_cons (a : Nat) (b : List Nat) : ValidBytes (a :: b) ↔ a < 256 ∧ ValidBytes b := by
  simp [ValidBytes]

theorem valid_enc (v : Nat) : ValidBytes (Varint.encodeBytes v) := by
  rw [Varint.encodeBytes_eq]; exact Varint.encRec_valid v

theorem valid_replicate (n : Nat) : ValidBytes (List.replicate n 0) := by
  intro b hb
  simp [List.mem_replicate] at hb
  omega

theorem limit_eq : Varint.limit = 2 ^ 63 := rfl

theorem enc_small (t : Nat) (h : t < 128) : Varint.encodeBytes t = [t] := by
  rw [Varint.encodeBytes_eq, Varint.encRec_lt _ h]

theorem vlen_small (t : Nat) (h : t < 128) : Varint.encodedLen t = 1 := Varint.encodedLen_lt t h

/-- A varint read of an encoding followed by anything returns the value and what follows. -/
theorem rdVarint_enc (v : Nat) (rest : List Nat) (hv : v < Varint.limit) :
    rdVarint (Varint.encodeBytes v ++ rest) = .ok (v, rest) := by
  unfold rdVarint
  rw [Varint.decode_encode v rest hv]
  simp

/-- A varint read accepts only the one encoding of the value it returns, and the value is below 2^63. -/
theorem rdVarint_inv {b : List Nat} {v : Nat} {r : List Nat} (hb : ValidBytes b)
    (h : rdVarint b = .ok (v, r)) : b = Varint.encodeBytes v ++ r ∧ v < Varint.limit ∧ ValidBytes r := by
  unfold rdVarint at h
  split at h
  · rename_i v' n hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc := Varint.decode_canonical b hb v' n hd
    have hbd := Varint.decode_bounds b hb v' n hd
    refine ⟨?_, hbd.1, fun x hx => hb x (List.mem_of_mem_drop hx)⟩
    rw [← hc.1, List.take_append_drop]
  · simp at h

theorem rdVarint_byte (t : Nat) (r : List Nat) (h : t < 128) : rdVarint (t :: r) = .ok (t, r) := by
  have := rdVarint_enc t r (by rw [limit_eq]; omega)
  rwa [enc_small t h] at this

theorem rdBytes_append (x r : List Nat) (n : Nat) (h : x.length = n) : rdBytes n (x ++ r) = .ok (x, r) := by
  subst h
  simp [rdBytes]

theorem rdBytes_inv {n : Nat} {b x r : List Nat} (hb : ValidBytes b) (h : rdBytes n b = .ok (x, r)) :
    b = x ++ r ∧ x.length = n ∧ ValidBytes x ∧ ValidBytes r := by
  unfold rdBytes at h
  split at h
  · rename_i hn
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(List.take_append_drop n b).symm, by simp [List.length_take]; omega,
      fun y hy => hb y (List.mem_of_mem_take hy), fun y hy => hb y (List.mem_of_mem_drop hy)⟩
  · simp at h

theorem rdLenPrefixed_enc (x rest : List Nat) (hx : x.length < Varint.limit) :
    rdLenPrefixed (Varint.encodeBytes x.length ++ (x ++ rest)) = .ok (x, rest) := by
  unfold rdLenPrefixed
  rw [rdVarint_enc _ _ hx]
  simp [rdBytes_append]

theorem rdLenPrefixed_inv {b x r : List Nat} (hb : ValidBytes b) (h : rdLenPrefixed b = .ok (x, r)) :
    b = Varint.encodeBytes x.length ++ (x ++ r) ∧ x.length < Varint.limit ∧ ValidBytes x ∧ ValidBytes r := by
  unfold rdLenPrefixed at h
  rw [andThen_eq_ok] at h
  obtain ⟨n, r1, h1, h2⟩ := h
  obtain ⟨e1, hn, hv1⟩ := rdVarint_inv hb h1
  obtain ⟨e2, hl, hvx, hvr⟩ := rdBytes_inv hv1 h2
  subst hl
  exact ⟨by rw [e1, e2], hn, hvx, hvr⟩

/-! ## The writer -/

theorem flat_append (a b : List Put) : flat (a ++ b) = flat a ++ flat b := by
  induction a with
  | nil => simp [flat]
  | cons p ps ih => cases p <;> simp [flat, ih]

/-- Every varint the calls write is below 2^63. -/
def PutsOk (ps : List Put) : Prop := ∀ x, Put.v x ∈ ps → x < Varint.limit

/-- Once every varint is below 2^63 and the bytes fit in the room left, no call fails and the writer holds the
bytes in order. -/
theorem runPuts_ok (cap : Nat) (ps : List Put) : ∀ (w : List Nat), PutsOk ps → (flat ps).length ≤ cap - w.length →
    runPuts cap w ps = .ok (w ++ flat ps) := by
  induction ps with
  | nil => intro w _ _; simp [runPuts, flat]
  | cons p ps ih =>
    intro w hok hlen
    have hok' : PutsOk ps := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    cases p with
    | v x =>
      have hx : x < Varint.limit := hok x (List.mem_cons_self ..)
      simp only [flat, List.length_append, Varint.length_encodeBytes] at hlen
      have h1 : ¬ x ≥ Varint.limit := by have := hx; omega
      have h2 : ¬ Varint.encodedLen x > cap - w.length := by omega
      simp only [runPuts, put, Varint.encodeInto, h1, h2, ite_false]
      rw [ih _ hok' (by simp only [List.length_append, Varint.length_encodeBytes]; omega)]
      simp [flat]
    | s bs =>
      simp only [flat, List.length_append] at hlen
      have h1 : bs.length ≤ cap - w.length := by omega
      simp only [runPuts, put, h1, ite_true]
      rw [ih _ hok' (by simp only [List.length_append]; omega)]
      simp [flat]

theorem rep_add (a b : Nat) : List.replicate a 0 ++ List.replicate b 0 = List.replicate (a + b) 0 := by
  induction a with
  | zero => simp
  | succ a ih => simp [List.replicate_succ, ih, Nat.succ_add]

theorem be32_len (v : Nat) : (be32 v).length = 4 := rfl

theorem zeroChunks_flat (len : Nat) : flat (zeroChunks len) = List.replicate len 0 := by
  induction len using Nat.strongRecOn with
  | _ len ih =>
    rw [zeroChunks]
    split
    · rename_i h; subst h; simp [flat]
    · rename_i h
      simp only [flat]
      rw [ih _ (by omega), rep_add]
      congr 1
      omega

theorem zeroChunks_ok (len : Nat) : PutsOk (zeroChunks len) := by
  induction len using Nat.strongRecOn with
  | _ len ih =>
    rw [zeroChunks]
    split
    · intro x hx; simp at hx
    · rename_i h
      intro x hx
      simp only [List.mem_cons, reduceCtorEq, false_or] at hx
      exact ih _ (by omega) x hx

/-! ## Frame values -/

/-- The first range of an ACK and the bytes of the further ones were validated by `Ack::parse`. -/
def AckOk (l f x : Nat) (tail : List Nat) : Prop :=
  l ≤ maxPn ∧ x < maxAckRanges ∧ f ≤ l ∧ ValidBytes tail ∧ ∃ ps, ackLoop x (l - f) tail = .ok (ps, [])

/-- A frame value of the code: the arrays have their lengths, a byte is a byte, a slice written with its length is
shorter than 2^63 (a STREAM frame's data is bounded by `validate`), an ACK was validated (only decoding produces one), a REKEY request carries zeros, a batch has at most 4 tickets.
A PADDING of no bytes writes nothing and is no frame on the wire. -/
def Frame.WF : Frame → Prop
  | .padding len => 1 ≤ len
  | .ack l f x tail => AckOk l f x tail
  | .stream _ _ _ data _ => ValidBytes data
  | .pathChallenge d | .pathResponse d => d.length = 8 ∧ ValidBytes d
  | .datagram d imp => ValidBytes d ∧ (imp = false → d.length < Varint.limit)
  | .mtuProbeEcho m => m < 65536
  | .rekey a sh echo spn =>
    sh.length = 32 ∧ ValidBytes sh ∧ echo.length = 8 ∧ ValidBytes echo ∧
      (a = false → echo = List.replicate 8 0 ∧ spn = 0)
  | .newTickets es => es.length ≤ maxBatch ∧ ∀ e ∈ es, e.1.length = 16 ∧ ValidBytes e.1 ∧ e.2 < 2 ^ 32
  | .ext _ body => ValidBytes body ∧ body.length < Varint.limit
  | _ => True

/-- A frame value that `validate` accepts. -/
def Frame.Good (f : Frame) : Prop := f.WF ∧ f.validate = .ok ()

theorem streamType_lt (o : Nat) (fin imp : Bool) : streamType o fin imp < 16 := by
  unfold streamType
  split <;> split <;> split <;> omega

theorem tickets_ok (es : List (List Nat × Nat)) :
    PutsOk (es.flatMap (fun e => [Put.s e.1, Put.s (be32 e.2)])) := by
  intro x hx
  simp [List.mem_flatMap] at hx

theorem tickets_flat_len (es : List (List Nat × Nat)) (h : ∀ e ∈ es, e.1.length = 16) :
    (flat (es.flatMap (fun e => [Put.s e.1, Put.s (be32 e.2)]))).length = es.length * 20 := by
  induction es with
  | nil => simp [flat]
  | cons e es ih =>
    have h1 := h e (List.mem_cons_self ..)
    have h2 := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, flat, List.length_append, h1, h2, be32_len,
      List.length_cons]
    omega

/-- What `validate` checks. -/
theorem validate_ok_iff (f : Frame) : f.validate = .ok () ↔
    (∀ v ∈ f.varintFields, v < Varint.limit) ∧
      (∀ id off fin data imp, f = .stream id off fin data imp → off + data.length ≤ maxEnd) ∧
      (∀ ty body, f = .ext ty body → extBase ≤ ty) := by
  unfold Frame.validate
  by_cases hany : f.varintFields.any (fun v => decide (v ≥ Varint.limit)) = true
  · rw [if_pos hany]
    simp only [List.any_eq_true, decide_eq_true_eq] at hany
    obtain ⟨v, hv, hge⟩ := hany
    constructor
    · intro h; cases h
    · intro h; have := h.1 v hv; omega
  · rw [if_neg hany]
    have hall : ∀ v ∈ f.varintFields, v < Varint.limit := by
      intro v hv
      apply Nat.lt_of_not_ge
      intro hge
      exact hany (List.any_eq_true.mpr ⟨v, hv, by simpa using hge⟩)
    constructor
    · intro h
      refine ⟨hall, ?_, ?_⟩
      · rintro id off fin data imp rfl
        dsimp only at h
        split at h
        · cases h
        · omega
      · rintro ty body rfl
        dsimp only at h
        split at h
        · cases h
        · omega
    · rintro ⟨_, hs, he⟩
      cases f with
      | stream id off fin data imp =>
        have := hs _ _ _ _ _ rfl
        dsimp only
        rw [if_neg (by omega)]
      | ext ty body =>
        have := he _ _ rfl
        dsimp only
        rw [if_neg (by omega)]
      | _ => rfl

/-- The varints a good frame writes are below 2^63. -/
theorem puts_ok (f : Frame) (hg : f.Good) : PutsOk f.puts := by
  obtain ⟨hwf, hval⟩ := hg
  rw [validate_ok_iff] at hval
  obtain ⟨hv, hs, he⟩ := hval
  have h0 : (0 : Nat) < Varint.limit := by rw [limit_eq]; omega
  have hsm : ∀ t : Nat, t < 128 → t < Varint.limit := fun t ht => by rw [limit_eq]; omega
  cases f with
  | padding len => exact zeroChunks_ok len
  | ack l f x tail =>
    obtain ⟨h1, h2, h3, _, _⟩ := hwf
    intro y hy
    simp only [Frame.puts, List.mem_cons, Put.v.injEq, reduceCtorEq, List.not_mem_nil, or_false] at hy
    simp only [maxPn, maxAckRanges] at h1 h2
    rw [limit_eq]
    omega
  | stream id off fin data imp =>
    have h1 := hv id (by simp [Frame.varintFields])
    have h2 := hv off (by simp [Frame.varintFields])
    have h3 := streamType_lt off fin imp
    intro y hy
    simp only [Frame.puts, List.mem_append, List.mem_cons, Put.v.injEq, List.not_mem_nil, or_false] at hy
    rcases hy with ((rfl | rfl) | hy) | hy
    · exact hsm _ (by omega)
    · exact h1
    · split at hy
      · simp at hy
      · simp at hy; subst hy; exact h2
    · split at hy
      · simp at hy
      · simp at hy; subst hy
        have := hs _ _ _ _ _ rfl
        simp only [maxEnd] at this
        rw [limit_eq]; omega
  | datagram d imp =>
    intro y hy
    cases imp with
    | true => simp [Frame.puts] at hy; subst hy; exact hsm _ (by omega)
    | false =>
      simp [Frame.puts] at hy
      rcases hy with rfl | rfl
      · exact hsm _ (by omega)
      · exact hwf.2 rfl
  | rekey a sh echo spn =>
    have h1 := hv spn (by simp [Frame.varintFields])
    intro y hy
    simp only [Frame.puts, List.mem_append, List.mem_cons, Put.v.injEq, reduceCtorEq, List.not_mem_nil,
      or_false] at hy
    rcases hy with rfl | hy
    · exact hsm _ (by omega)
    · split at hy
      · simp at hy; subst hy; exact h1
      · simp at hy
  | newTickets es =>
    intro y hy
    simp only [Frame.puts, List.mem_append, List.mem_cons, Put.v.injEq, reduceCtorEq, List.not_mem_nil,
      or_false] at hy
    rcases hy with rfl | hy
    · exact hsm _ (by omega)
    · exact tickets_ok es y hy
  | ext ty body =>
    have h1 := hv ty (by simp [Frame.varintFields])
    intro y hy
    simp only [Frame.puts, List.mem_cons, Put.v.injEq, reduceCtorEq, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact h1
    · exact hwf.2
  | _ =>
    intro y hy
    simp only [Frame.puts, List.mem_cons, Put.v.injEq, reduceCtorEq, List.not_mem_nil, or_false] at hy
    first
      | (subst hy; exact hsm _ (by omega))
      | (rcases hy with rfl | rfl
         · exact hsm _ (by omega)
         · exact hv _ (by simp [Frame.varintFields]))
      | (rcases hy with rfl | rfl | rfl
         · exact hsm _ (by omega)
         · exact hv _ (by simp [Frame.varintFields])
         · exact hv _ (by simp [Frame.varintFields]))
      | (rcases hy with rfl | rfl | rfl | rfl
         · exact hsm _ (by omega)
         · exact hv _ (by simp [Frame.varintFields])
         · exact hv _ (by simp [Frame.varintFields])
         · exact hv _ (by simp [Frame.varintFields]))

/-- Length: `encoded_len` is the number of bytes of the encoding, for every frame the code can hold; this includes
a STREAM or DATAGRAM frame that omits its length (`stream_overhead`, `datagram_overhead`). -/
theorem bytes_length (f : Frame) (hwf : f.WF) : f.bytes.length = f.encodedLen := by
  cases f with
  | padding len => simp [Frame.bytes, Frame.puts, zeroChunks_flat, Frame.encodedLen]
  | stream id off fin data imp =>
    have h3 := vlen_small _ (Nat.lt_trans (streamType_lt off fin imp) (by omega))
    simp only [Frame.bytes, Frame.puts, Frame.encodedLen, streamOverhead, flat_append, flat, List.length_append,
      Varint.length_encodeBytes, h3, List.length_nil]
    by_cases ho : off = 0 <;> by_cases hi : imp = true <;>
      simp [ho, hi, flat, Varint.length_encodeBytes] <;> omega
  | datagram d imp =>
    by_cases hi : imp = true <;>
      simp [Frame.bytes, Frame.puts, Frame.encodedLen, datagramOverhead, hi, flat, Varint.length_encodeBytes,
        vlen_small] <;> omega
  | rekey a sh echo spn =>
    obtain ⟨h1, _, h2, _, _⟩ := hwf
    by_cases ha : a = true <;>
      simp [Frame.bytes, Frame.puts, Frame.encodedLen, ha, flat, Varint.length_encodeBytes,
        vlen_small, h1, h2] <;> omega
  | newTickets es =>
    have := tickets_flat_len es (fun e he => (hwf.2 e he).1)
    simp only [Frame.bytes, Frame.puts, Frame.encodedLen, flat_append, flat, List.length_append,
      Varint.length_encodeBytes, this, List.length_cons, List.length_nil]
    simp [vlen_small]
  | pathChallenge d => simp [Frame.bytes, Frame.puts, Frame.encodedLen, flat, Varint.length_encodeBytes, vlen_small, hwf.1]
  | pathResponse d => simp [Frame.bytes, Frame.puts, Frame.encodedLen, flat, Varint.length_encodeBytes, vlen_small, hwf.1]
  | _ =>
    simp [Frame.bytes, Frame.puts, Frame.encodedLen, flat, Varint.length_encodeBytes, vlen_small, be16] <;> omega

/-- Errors are total and a refusal changes nothing: for every frame value of the code, `write` is `validate` (an
overflowing varint field, a stream end beyond 2^62 - 1, an extension type below `0x40`), then the room check
against `encoded_len` (`BufferTooSmall` with the shortfall), then the bytes of the frame appended, none of the
calls failing. An error returns no writer: the caller's is as it was. -/
theorem write_eq (cap : Nat) (w : List Nat) (f : Frame) (hwf : f.WF) :
    f.write cap w =
      match f.validate with
      | .error e => .error e
      | .ok () =>
        if f.encodedLen ≤ cap - w.length then .ok (w ++ f.bytes)
        else .error (.bufferTooSmall (f.encodedLen - (cap - w.length))) := by
  unfold Frame.write
  cases hv : f.validate with
  | error e => rfl
  | ok u =>
    cases u
    simp only
    split
    · rename_i hle
      exact runPuts_ok cap f.puts w (puts_ok f ⟨hwf, hv⟩) (by
        have := bytes_length f hwf; unfold Frame.bytes at this; omega)
    · rfl

/-- The errors of `validate`, in the order the code checks. -/
theorem validate_error (f : Frame) (e : Err) (h : f.validate = .error e) :
    e = .overflow ∨ e = .streamEnd ∨ ∃ t, t < extBase ∧ e = .unknownType t := by
  unfold Frame.validate at h
  split at h
  · simp at h; exact Or.inl h.symm
  · cases f <;> dsimp only at h <;> try (cases h)
    · split at h
      · cases h; exact Or.inr (Or.inl rfl)
      · cases h
    · split at h
      · rename_i hlt; cases h; exact Or.inr (Or.inr ⟨_, hlt, rfl⟩)
      · cases h

end Vinc.TransportFrame

#audit_axioms Vinc.TransportFrame.rdVarint_inv
#audit_axioms Vinc.TransportFrame.runPuts_ok
#audit_axioms Vinc.TransportFrame.bytes_length
#audit_axioms Vinc.TransportFrame.write_eq
#audit_axioms Vinc.TransportFrame.validate_error
