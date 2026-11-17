import Vinc.Axioms

/-!
# The broadcast wire format

A model of the frame and message head codec of `vinc-broadcast/src/wire.rs`: `Head::write`, `Head::parse` and
`build`. Bytes are `Nat`s; `ValidBytes` says every byte is below 256. Multi-byte integers are big-endian
(`beBytes`, `beVal`), and `u32`/`u64` fields are `Nat`s below `2^32`/`2^64` (`Head.WF`).

The head is `mid8 origin32 alg1 [public_key] signature isb1 blen4 wall8 counter4`. The algorithm tags and the
lengths are those of `vinc-crypto` (`IdentityAlg`): tags 1 to 4; the public key is absent for Ed25519 (its node id
is the key) and present, with the algorithm's length, for the others. `parse` returns the head and the body that
follows and requires the body length to equal `blen`.

The signed envelope of `envelope.rs` is `version | kind | topic_len2 | topic | head | body` over this head codec:
`encEnv` and `decEnv`, with `env_roundtrip`, `env_canonical`, `env_trailing`, `env_cut`, `env_version`, `env_kind`
(kind 1 the only accepted case) and `env_topic_bound`.

Over every input: `parse_write` (round trip), `parse_canonical` (a parse determines its input), the rejections
`parse_short`, `parse_unknown_alg`, `parse_bad_flag`, `parse_blen_mismatch`, `parse_trunc`, the length law
`head_len`, and the frame codec `frame_roundtrip` and `frame_canonical`.
-/

namespace Vinc.BroadcastWire

/-! ## Big-endian integers -/

def ValidBytes (bs : List Nat) : Prop := ∀ b ∈ bs, b < 256

/-- `n` bytes of `x`, most significant first (`to_be_bytes`). -/
def beBytes : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => beBytes n (x / 256) ++ [x % 256]

/-- The number a big-endian byte string denotes (`from_be_bytes`). -/
def beVal (bs : List Nat) : Nat := bs.foldl (fun a b => a * 256 + b) 0

theorem snoc_ind {P : List Nat → Prop} (h0 : P []) (hs : ∀ l a, P l → P (l ++ [a])) (l : List Nat) : P l := by
  have : ∀ n (l : List Nat), l.length = n → P l := by
    intro n
    induction n with
    | zero => intro l hl; rw [List.length_eq_zero_iff.mp hl]; exact h0
    | succ n ih =>
      intro l hl
      rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩
      · simp at hl
      rw [List.concat_eq_append]
      · exact hs l' a (ih l' (by simpa using hl))
  exact this _ l rfl

theorem beVal_snoc (l : List Nat) (a : Nat) : beVal (l ++ [a]) = beVal l * 256 + a := by
  simp [beVal, List.foldl_append]

theorem length_beBytes (n x : Nat) : (beBytes n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [beBytes, ih]

theorem beVal_beBytes (n x : Nat) : beVal (beBytes n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [beBytes, beVal, Nat.mod_one]
  | succ n ih =>
    rw [beBytes, beVal_snoc, ih, Nat.pow_succ', Nat.mod_mul]
    omega

theorem beVal_of_lt {n x : Nat} (h : x < 256 ^ n) : beVal (beBytes n x) = x := by
  rw [beVal_beBytes]; exact Nat.mod_eq_of_lt h

theorem beVal_lt (bs : List Nat) (h : ValidBytes bs) : beVal bs < 256 ^ bs.length := by
  induction bs using snoc_ind with
  | h0 => simp [beVal]
  | hs l a ih =>
    have hl : ValidBytes l := fun b hb => h b (by simp [hb])
    have ha : a < 256 := h a (by simp)
    have := ih hl
    rw [beVal_snoc, List.length_append, List.length_singleton, Nat.pow_succ]
    omega

theorem beBytes_beVal (n : Nat) (bs : List Nat) (hl : bs.length = n) (hv : ValidBytes bs) :
    beBytes n (beVal bs) = bs := by
  induction bs using snoc_ind generalizing n with
  | h0 => subst hl; rfl
  | hs l a ih =>
    subst hl
    have hlv : ValidBytes l := fun b hb => hv b (by simp [hb])
    have ha : a < 256 := hv a (by simp)
    rw [List.length_append, List.length_singleton, beBytes, beVal_snoc]
    have h1 : (beVal l * 256 + a) / 256 = beVal l := by omega
    have h2 : (beVal l * 256 + a) % 256 = a := by omega
    rw [h1, h2, ih _ rfl hlv]

/-! ## The algorithms of `vinc-crypto` -/

inductive Alg where
  | ed25519 | ecdsaP256 | mlDsa65 | hybrid
  deriving DecidableEq, Repr

/-- `IdentityAlg::tag`. -/
def Alg.tag : Alg → Nat
  | .ed25519 => 1 | .ecdsaP256 => 2 | .mlDsa65 => 3 | .hybrid => 4

/-- `IdentityAlg::from_tag`. -/
def Alg.fromTag : Nat → Option Alg
  | 1 => some .ed25519 | 2 => some .ecdsaP256 | 3 => some .mlDsa65 | 4 => some .hybrid | _ => none

/-- `IdentityAlg::public_key_len`. -/
def Alg.pubLen : Alg → Nat
  | .ed25519 => 32 | .ecdsaP256 => 33 | .mlDsa65 => 1952 | .hybrid => 32 + 1952

/-- `IdentityAlg::signature_len`. -/
def Alg.sigLen : Alg → Nat
  | .ed25519 => 64 | .ecdsaP256 => 64 | .mlDsa65 => 3309 | .hybrid => 64 + 3309

/-- The public key bytes a head carries: none for Ed25519, whose node id is the key. -/
def Alg.wirePk (a : Alg) : Nat := if a = .ed25519 then 0 else a.pubLen

theorem Alg.fromTag_tag (a : Alg) : Alg.fromTag a.tag = some a := by cases a <;> rfl

theorem Alg.tag_of_fromTag {t : Nat} {a : Alg} (h : Alg.fromTag t = some a) : a.tag = t := by
  match t, a, h with
  | 1, .ed25519, _ | 2, .ecdsaP256, _ | 3, .mlDsa65, _ | 4, .hybrid, _ => rfl

theorem Alg.fromTag_none {t : Nat} (h : t = 0 ∨ 5 ≤ t) : Alg.fromTag t = none := by
  match t, h with
  | 0, _ => rfl
  | t + 5, _ => rfl

/-! ## The head -/

structure Head where
  mid : List Nat
  origin : List Nat
  alg : Alg
  pk : List Nat
  sig : List Nat
  isb : Bool
  wall : Nat
  counter : Nat

/-- The shape `Head::parse` yields and `Head::write` is given: lengths per the algorithm, `u64`/`u32` timestamps. -/
structure Head.WF (h : Head) : Prop where
  mid : h.mid.length = 8
  origin : h.origin.length = 32
  pk : h.pk.length = h.alg.wirePk
  sig : h.sig.length = h.alg.sigLen
  wall : h.wall < 2 ^ 64
  counter : h.counter < 2 ^ 32

def flagByte (b : Bool) : Nat := if b then 1 else 0

/-- `Head::write` with `blen` the body length. -/
def write (h : Head) (blen : Nat) : List Nat :=
  h.mid ++ h.origin ++ [h.alg.tag] ++ h.pk ++ h.sig ++ [flagByte h.isb] ++ beBytes 4 blen ++ beBytes 8 h.wall ++
    beBytes 4 h.counter

def flagOf : Nat → Option Bool
  | 0 => some false | 1 => some true | _ => none

/-- Read `n` bytes (`Reader::read_bytes`). -/
def rd (n : Nat) (l : List Nat) : Option (List Nat × List Nat) :=
  if n ≤ l.length then some (l.take n, l.drop n) else none

def rd1 : List Nat → Option (Nat × List Nat)
  | [] => none
  | x :: r => some (x, r)

/-- `Head::parse`. -/
def parse (b : List Nat) : Option (Head × List Nat) := do
  let (mid, l) ← rd 8 b
  let (origin, l) ← rd 32 l
  let (t, l) ← rd1 l
  let alg ← Alg.fromTag t
  let (pk, l) ← rd alg.wirePk l
  let (sig, l) ← rd alg.sigLen l
  let (f, l) ← rd1 l
  let isb ← flagOf f
  let (bl, l) ← rd 4 l
  let (w, l) ← rd 8 l
  let (c, l) ← rd 4 l
  if l.length = beVal bl then
    some ({ mid, origin, alg, pk, sig, isb, wall := beVal w, counter := beVal c }, l)
  else none

theorem rd_append {n : Nat} {a : List Nat} (b : List Nat) (h : a.length = n) : rd n (a ++ b) = some (a, b) := by
  subst h; simp [rd, List.take_left', List.drop_left']

theorem rd_eq {n : Nat} {l a r : List Nat} (h : rd n l = some (a, r)) : l = a ++ r ∧ a.length = n := by
  unfold rd at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(List.take_append_drop _ _).symm, by simp; omega⟩
  · simp at h

theorem flagOf_flagByte (b : Bool) : flagOf (flagByte b) = some b := by cases b <;> rfl

/-- The pieces `parse` cuts a successful input into. -/
theorem parse_split {b : List Nat} {h : Head} {body : List Nat} (hp : parse b = some (h, body)) :
    ∃ bl w c : List Nat, b = h.mid ++ h.origin ++ [h.alg.tag] ++ h.pk ++ h.sig ++ [flagByte h.isb] ++ bl ++ w ++ c ++ body ∧
      h.mid.length = 8 ∧ h.origin.length = 32 ∧ h.pk.length = h.alg.wirePk ∧ h.sig.length = h.alg.sigLen ∧
      bl.length = 4 ∧ w.length = 8 ∧ c.length = 4 ∧ body.length = beVal bl ∧ h.wall = beVal w ∧
      h.counter = beVal c := by
  unfold parse at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨⟨mid, l1⟩, e1, ⟨origin, l2⟩, e2, ⟨t, l3⟩, e3, alg, e4, ⟨pk, l5⟩, e5, ⟨sig, l6⟩, e6, ⟨f, l7⟩, e7, isb, e8,
    ⟨bl, l9⟩, e9, ⟨w, l10⟩, e10, ⟨c, l11⟩, e11, hp⟩ := hp
  dsimp only at e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  have hlen : l11.length = beVal bl := Classical.byContradiction fun hn => by simp [hn] at hp
  simp only [hlen, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨r1, n1⟩ := rd_eq e1
  obtain ⟨r2, n2⟩ := rd_eq e2
  have r3 : l2 = t :: l3 := by cases l2 <;> simp_all [rd1]
  obtain ⟨r5, n5⟩ := rd_eq e5
  obtain ⟨r6, n6⟩ := rd_eq e6
  have r7 : l6 = f :: l7 := by cases l6 <;> simp_all [rd1]
  obtain ⟨r9, n9⟩ := rd_eq e9
  obtain ⟨r10, n10⟩ := rd_eq e10
  obtain ⟨r11, n11⟩ := rd_eq e11
  have ht : alg.tag = t := Alg.tag_of_fromTag e4
  have hf : flagByte isb = f := by
    unfold flagOf at e8; split at e8 <;> simp_all [flagByte]
  refine ⟨bl, w, c, ?_, n1, n2, n5, n6, n9, n10, n11, hlen, rfl, rfl⟩
  simp only [ht, hf]
  rw [r1, r2, r3, r5, r6, r7, r9, r10, r11]
  simp

/-- `parse_write` generalised: the body length decides. -/
theorem parse_write_gen (h : Head) (hw : h.WF) (blen : Nat) (hb : blen < 2 ^ 32) (body : List Nat) :
    parse (write h blen ++ body) = if body.length = blen then some (h, body) else none := by
  have e4 := beVal_of_lt (n := 4) (x := blen) (by simpa using hb)
  have e8 := beVal_of_lt (n := 8) (x := h.wall) (by simpa using hw.wall)
  have ec := beVal_of_lt (n := 4) (x := h.counter) (by simpa using hw.counter)
  simp only [write, List.append_assoc, List.cons_append]
  unfold parse
  simp only [Option.bind_eq_bind]
  rw [rd_append _ hw.mid, Option.bind_some, rd_append _ hw.origin, Option.bind_some]
  simp only [rd1, Option.bind_some, Alg.fromTag_tag, List.nil_append]
  rw [rd_append _ hw.pk, Option.bind_some, rd_append _ hw.sig, Option.bind_some]
  simp only [flagOf_flagByte, Option.bind_some]
  rw [rd_append _ (length_beBytes 4 blen), Option.bind_some, rd_append _ (length_beBytes 8 _),
    Option.bind_some, rd_append _ (length_beBytes 4 _), Option.bind_some, e4, e8, ec]

theorem parse_write (h : Head) (hw : h.WF) (body : List Nat) (hb : body.length < 2 ^ 32) :
    parse (write h body.length ++ body) = some (h, body) := by
  rw [parse_write_gen h hw _ hb]; simp

/-- A body whose length differs from `blen` is rejected. -/
theorem parse_blen_mismatch (h : Head) (hw : h.WF) (blen : Nat) (hb : blen < 2 ^ 32) (body : List Nat)
    (hne : body.length ≠ blen) : parse (write h blen ++ body) = none := by
  rw [parse_write_gen h hw _ hb]; simp [hne]

/-- A parse determines its input (canonical encoding): re-encoding the parsed head and body gives the bytes. -/
theorem parse_canonical {b : List Nat} {h : Head} {body : List Nat} (hv : ValidBytes b)
    (hp : parse b = some (h, body)) : h.WF ∧ body.length < 2 ^ 32 ∧ write h body.length ++ body = b := by
  obtain ⟨bl, w, c, hb, hm, ho, hpk, hsig, hbl, hw, hc, hbody, hwall, hcnt⟩ := parse_split hp
  have vbl : ValidBytes bl := fun x hx => hv x (by rw [hb]; simp [hx])
  have vw : ValidBytes w := fun x hx => hv x (by rw [hb]; simp [hx])
  have vc : ValidBytes c := fun x hx => hv x (by rw [hb]; simp [hx])
  have l4 := hbl ▸ beVal_lt bl vbl
  have l8 := hw ▸ beVal_lt w vw
  have l4' := hc ▸ beVal_lt c vc
  refine ⟨⟨hm, ho, hpk, hsig, ?_, ?_⟩, ?_, ?_⟩
  · rw [hwall]; simpa using l8
  · rw [hcnt]; simpa using l4'
  · rw [hbody]; simpa using l4
  · rw [hb, write, hbody, hwall, hcnt, beBytes_beVal _ _ hbl vbl, beBytes_beVal _ _ hw vw,
      beBytes_beVal _ _ hc vc]

/-- Fewer than the 41 fixed leading bytes: rejected. -/
theorem parse_short (b : List Nat) (hb : b.length < 41) : parse b = none := by
  cases hp : parse b with
  | none => rfl
  | some r =>
    obtain ⟨h, body⟩ := r
    obtain ⟨bl, w, c, hb', hm, ho, -⟩ := parse_split hp
    have := congrArg List.length hb'
    simp at this; omega

/-- An unknown algorithm tag (0 or 5 and above) is rejected. -/
theorem parse_unknown_alg (mid origin rest : List Nat) (t : Nat) (hm : mid.length = 8) (ho : origin.length = 32)
    (ht : t = 0 ∨ 5 ≤ t) : parse (mid ++ origin ++ t :: rest) = none := by
  unfold parse
  simp only [Option.bind_eq_bind, List.append_assoc]
  rw [rd_append _ hm, Option.bind_some, rd_append _ ho, Option.bind_some]
  simp [rd1, Alg.fromTag_none ht]

/-- A flag byte other than 0 or 1 is rejected. -/
theorem parse_bad_flag (mid origin pk sig rest : List Nat) (a : Alg) (f : Nat) (hm : mid.length = 8)
    (ho : origin.length = 32) (hpk : pk.length = a.wirePk) (hs : sig.length = a.sigLen) (hf : 2 ≤ f) :
    parse (mid ++ origin ++ [a.tag] ++ pk ++ sig ++ f :: rest) = none := by
  unfold parse
  simp only [Option.bind_eq_bind, List.append_assoc, List.cons_append]
  rw [rd_append _ hm, Option.bind_some, rd_append _ ho, Option.bind_some]
  simp only [rd1, Option.bind_some, Alg.fromTag_tag, List.nil_append]
  rw [rd_append _ hpk, Option.bind_some, rd_append _ hs, Option.bind_some]
  match f, hf with
  | f + 2, _ => simp [flagOf]

/-- The encoded length of a head. -/
def headLen (h : Head) : Nat := 8 + 32 + 1 + h.pk.length + h.sig.length + 1 + 4 + 12

/-- The length law: a parsed input is exactly its head followed by its body. -/
theorem head_len {b : List Nat} {h : Head} {body : List Nat} (hp : parse b = some (h, body)) :
    b.length = headLen h + body.length := by
  obtain ⟨bl, w, c, hb, hm, ho, -, -, hbl, hw, hc, -⟩ := parse_split hp
  have := congrArg List.length hb
  simp [headLen] at this ⊢; omega

/-- Cut short: a head with a known algorithm tag and fewer bytes than the key, signature and fixed tail is rejected. -/
theorem parse_trunc (mid origin rest : List Nat) (a : Alg) (hm : mid.length = 8) (ho : origin.length = 32)
    (hr : rest.length < a.wirePk + a.sigLen + 1 + 4 + 12) : parse (mid ++ origin ++ [a.tag] ++ rest) = none := by
  cases hp : parse (mid ++ origin ++ [a.tag] ++ rest) with
  | none => rfl
  | some r =>
    obtain ⟨h, body⟩ := r
    obtain ⟨bl, w, c, hb, hm', ho', hpk, hsig, hbl, hw, hc, -⟩ := parse_split hp
    have h1 : (mid ++ origin ++ [a.tag]) ++ rest
        = (h.mid ++ h.origin ++ [h.alg.tag]) ++ (h.pk ++ h.sig ++ [flagByte h.isb] ++ bl ++ w ++ c ++ body) := by
      have := hb; simp only [List.append_assoc] at this ⊢; exact this
    obtain ⟨hp1, hp2⟩ := List.append_inj h1 (by simp [hm, ho, hm', ho'])
    obtain ⟨-, htag⟩ := List.append_inj hp1 (by simp [hm, ho, hm', ho'])
    have hat : a = h.alg := by
      have e2 := Alg.fromTag_tag a
      rw [(List.cons.inj htag).1, Alg.fromTag_tag] at e2
      exact (Option.some.inj e2).symm
    have := congrArg List.length hp2
    subst hat
    simp at this; omega

/-! ## Frames -/

/-- `build`: `len32 | ty | topic_len | topic | parts`, refused for a topic over 255 or a frame over `u32`. -/
def build (ty : Nat) (topic : List Nat) (parts : List (List Nat)) : Option (List Nat) :=
  let rest := parts.flatten
  if topic.length ≤ 255 ∧ 2 + topic.length + rest.length < 2 ^ 32 then
    some (beBytes 4 (2 + topic.length + rest.length) ++ [ty, topic.length] ++ topic ++ rest)
  else none

/-- The host's frame splitter: the type, the topic and the rest of one whole frame. -/
def parseFrame (b : List Nat) : Option (Nat × List Nat × List Nat) := do
  let (lb, l) ← rd 4 b
  let (ty, l) ← rd1 l
  let (tl, l) ← rd1 l
  let (topic, l) ← rd tl l
  if 2 + tl + l.length = beVal lb then some (ty, topic, l) else none

theorem frame_roundtrip (ty : Nat) (topic : List Nat) (parts : List (List Nat)) (ht : topic.length ≤ 255)
    (hb : 2 + topic.length + parts.flatten.length < 2 ^ 32) :
    ∃ fr, build ty topic parts = some fr ∧ parseFrame fr = some (ty, topic, parts.flatten) := by
  refine ⟨beBytes 4 (2 + topic.length + parts.flatten.length) ++ [ty, topic.length] ++ topic ++ parts.flatten,
    by simp only [build, ht, hb, and_self, ↓reduceIte], ?_⟩
  have e := beVal_of_lt (n := 4) (x := 2 + topic.length + parts.flatten.length) (by simpa using hb)
  unfold parseFrame
  simp only [Option.bind_eq_bind, List.append_assoc, List.cons_append, List.nil_append]
  rw [rd_append _ (length_beBytes 4 _), Option.bind_some]
  simp only [rd1, Option.bind_some]
  rw [rd_append _ rfl, Option.bind_some, e]
  simp

theorem frame_canonical {b : List Nat} {ty : Nat} {topic rest : List Nat} (hv : ValidBytes b)
    (hp : parseFrame b = some (ty, topic, rest)) : build ty topic [rest] = some b := by
  unfold parseFrame at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨⟨lb, l1⟩, e1, ⟨ty', l2⟩, e2, ⟨tl, l3⟩, e3, ⟨tp, l4⟩, e4, hp⟩ := hp
  dsimp only at e2 e3 e4
  have hlen : 2 + tl + l4.length = beVal lb := Classical.byContradiction fun hn => by simp [hn] at hp
  simp only [hlen, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  obtain ⟨r1, n1⟩ := rd_eq e1
  obtain ⟨r4, n4⟩ := rd_eq e4
  have r2 : l1 = ty' :: l2 := by cases l1 <;> simp_all [rd1]
  have r3 : l2 = tl :: l3 := by cases l2 <;> simp_all [rd1]
  have vlb : ValidBytes lb := fun x hx => hv x (by rw [r1]; simp [hx])
  have vtl : tl < 256 := hv tl (by rw [r1, r2, r3]; simp)
  have lt := beVal_lt lb vlb
  rw [n1] at lt
  simp only [build, List.flatten_cons, List.flatten_nil, List.append_nil]
  have vsz : 2 + tp.length + l4.length < 2 ^ 32 := by
    rw [n4, hlen]; simpa [n1] using lt
  have hif : (tp.length ≤ 255 ∧ 2 + tp.length + l4.length < 2 ^ 32) := ⟨by omega, vsz⟩
  simp only [hif, and_self, ↓reduceIte]
  rw [n4, hlen, beBytes_beVal _ _ n1 vlb, r1, r2, r3, r4]
  simp

/-! ## The signed envelope -/

/-- `Envelope::encode_into` of a topic message (kind 1): `version 1 | kind 1 | topic_len2 | topic | head | body`, the
head being `write` with the body's length. -/
def encEnv (topic : List Nat) (h : Head) (body : List Nat) : List Nat :=
  [1, 1] ++ beBytes 2 topic.length ++ topic ++ write h body.length ++ body

/-- `Envelope::decode`: the version, the kind (a dispatch whose only accepted case is kind 1), the topic bound
(`MAX_TOPIC`, 255), the head and a body of exactly the length the head names. -/
def decEnv (b : List Nat) : Option (List Nat × Head × List Nat) :=
  match rd1 b with
  | none => none
  | some (v, l) =>
    if v ≠ 1 then none else
    match rd1 l with
    | none => none
    | some (k, l) =>
      if k ≠ 1 then none else
      match rd 2 l with
      | none => none
      | some (tb, l) =>
        if 255 < beVal tb then none else
        match rd (beVal tb) l with
        | none => none
        | some (topic, l) =>
          match parse l with
          | none => none
          | some (h, body) => some (topic, h, body)

theorem rd1_eq {l r : List Nat} {x : Nat} (h : rd1 l = some (x, r)) : l = x :: r := by
  cases l with
  | nil => simp [rd1] at h
  | cons y ys =>
    simp only [rd1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Decoding an encoding followed by a tail: the message when the tail is empty, a refusal for any trailing byte. -/
theorem env_dec_enc (topic : List Nat) (h : Head) (hw : h.WF) (body tail : List Nat) (ht : topic.length ≤ 255)
    (hb : body.length < 2 ^ 32) :
    decEnv (encEnv topic h body ++ tail) = if tail = [] then some (topic, h, body) else none := by
  have e2 : beVal (beBytes 2 topic.length) = topic.length :=
    beVal_of_lt (n := 2) (x := topic.length) (by show topic.length < 65536; omega)
  unfold decEnv encEnv
  simp only [List.append_assoc, List.cons_append, List.nil_append, rd1, ne_eq, not_true_eq_false, if_false]
  rw [rd_append _ (length_beBytes 2 topic.length)]
  simp only [e2, Nat.not_lt.mpr ht, if_false]
  rw [rd_append _ rfl]
  simp only [parse_write_gen h hw _ hb]
  cases tail with
  | nil => simp
  | cons x xs =>
    have hne : ¬ (body ++ x :: xs).length = body.length := by
      simp only [List.length_append, List.length_cons]; omega
    simp [hne]

/-- Round trip: what `encode_into` writes `decode` reads back. -/
theorem env_roundtrip (topic : List Nat) (h : Head) (hw : h.WF) (body : List Nat) (ht : topic.length ≤ 255)
    (hb : body.length < 2 ^ 32) : decEnv (encEnv topic h body) = some (topic, h, body) := by
  have := env_dec_enc topic h hw body [] ht hb
  simpa using this

/-- A trailing byte is refused. -/
theorem env_trailing (topic : List Nat) (h : Head) (hw : h.WF) (body tail : List Nat) (ht : topic.length ≤ 255)
    (hb : body.length < 2 ^ 32) (hne : tail ≠ []) : decEnv (encEnv topic h body ++ tail) = none := by
  rw [env_dec_enc topic h hw body tail ht hb]; simp [hne]

/-- Canonical form: whatever decodes is exactly what `encode_into` writes for its parts, within the bounds. -/
theorem env_canonical {b : List Nat} {topic : List Nat} {h : Head} {body : List Nat} (hv : ValidBytes b)
    (hd : decEnv b = some (topic, h, body)) :
    topic.length ≤ 255 ∧ h.WF ∧ body.length < 2 ^ 32 ∧ encEnv topic h body = b := by
  unfold decEnv at hd
  rcases e1 : rd1 b with _ | ⟨v, l1⟩
  · rw [e1] at hd; simp at hd
  rw [e1] at hd
  dsimp only at hd
  by_cases hv1 : v ≠ 1
  · simp [hv1] at hd
  rw [if_neg hv1] at hd
  rcases e2 : rd1 l1 with _ | ⟨k, l2⟩
  · rw [e2] at hd; simp at hd
  rw [e2] at hd
  dsimp only at hd
  by_cases hk : k ≠ 1
  · simp [hk] at hd
  rw [if_neg hk] at hd
  rcases e3 : rd 2 l2 with _ | ⟨tb, l3⟩
  · rw [e3] at hd; simp at hd
  rw [e3] at hd
  dsimp only at hd
  by_cases ht : 255 < beVal tb
  · simp [ht] at hd
  rw [if_neg ht] at hd
  rcases e4 : rd (beVal tb) l3 with _ | ⟨tp, l4⟩
  · rw [e4] at hd; simp at hd
  rw [e4] at hd
  dsimp only at hd
  rcases e5 : parse l4 with _ | ⟨h', body'⟩
  · rw [e5] at hd; simp at hd
  rw [e5] at hd
  dsimp only at hd
  simp only [Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨htp, hh, hbody⟩ := hd
  have hv1' : v = 1 := by simpa using hv1
  have hk' : k = 1 := by simpa using hk
  obtain ⟨c3, n3⟩ := rd_eq e3
  obtain ⟨c4, n4⟩ := rd_eq e4
  have r1 := rd1_eq e1
  have r2 := rd1_eq e2
  have hb : b = v :: k :: (tb ++ (tp ++ l4)) := by rw [r1, r2, c3, c4]
  have vtb : ValidBytes tb := fun x hx => hv x (by rw [hb]; simp [hx])
  have vl4 : ValidBytes l4 := fun x hx => hv x (by rw [hb]; simp [hx])
  obtain ⟨hwf, hlt, hw⟩ := parse_canonical vl4 e5
  rw [← htp, ← hh, ← hbody]
  refine ⟨by omega, hwf, hlt, ?_⟩
  unfold encEnv
  rw [n4, beBytes_beVal 2 tb n3 vtb, hb, ← hw]
  simp [hv1', hk']

/-- A version other than 1 is refused. -/
theorem env_version (v : Nat) (rest : List Nat) (hv : v ≠ 1) : decEnv (v :: rest) = none := by
  simp [decEnv, rd1, hv]

/-- A kind other than 1 is refused: the dispatch has one accepted case. -/
theorem env_kind (k : Nat) (rest : List Nat) (hk : k ≠ 1) : decEnv (1 :: k :: rest) = none := by
  simp [decEnv, rd1, hk]

/-- A topic length over 255 is refused. -/
theorem env_topic_bound (tl : Nat) (rest : List Nat) (h1 : 255 < tl) (h2 : tl < 65536) :
    decEnv ([1, 1] ++ beBytes 2 tl ++ rest) = none := by
  have e2 : beVal (beBytes 2 tl) = tl := beVal_of_lt (n := 2) (x := tl) (by show tl < 65536; exact h2)
  unfold decEnv
  simp only [List.append_assoc, List.cons_append, List.nil_append, rd1, ne_eq, not_true_eq_false, if_false]
  rw [rd_append _ (length_beBytes 2 tl)]
  simp [e2, h1]

/-- A cut is refused: no proper prefix of an encoding decodes. -/
theorem env_cut (topic : List Nat) (h : Head) (hw : h.WF) (body : List Nat) (ht : topic.length ≤ 255)
    (hb : body.length < 2 ^ 32) (hv : ValidBytes (encEnv topic h body)) (n : Nat)
    (hn : n < (encEnv topic h body).length) : decEnv ((encEnv topic h body).take n) = none := by
  cases hd : decEnv ((encEnv topic h body).take n) with
  | none => rfl
  | some X =>
    obtain ⟨tp, h', body'⟩ := X
    have vt : ValidBytes ((encEnv topic h body).take n) := fun x hx => hv x (List.mem_of_mem_take hx)
    obtain ⟨ht', hw', hb', he⟩ := env_canonical vt hd
    have hne : (encEnv topic h body).drop n ≠ [] := by
      intro hz
      have := congrArg List.length hz
      simp at this
      omega
    have key := env_trailing tp h' hw' body' _ ht' hb' hne
    rw [he, List.take_append_drop, env_roundtrip topic h hw body ht hb] at key
    simp at key

/-! ## Concrete checks of the real constants -/

/-- The shortest head is Ed25519's: no key, a 64-byte signature. -/
theorem headLen_ed25519 : 8 + 32 + 1 + Alg.ed25519.wirePk + Alg.ed25519.sigLen + 1 + 4 + 12 = 122 := by decide

/-- `MAX_HEAD`: the hybrid head, `8 + 32 + 1 + 1984 + 3373 + 1 + 4 + 12`. -/
theorem maxHead_hybrid : 8 + 32 + 1 + Alg.hybrid.wirePk + Alg.hybrid.sigLen + 1 + 4 + 12 = 5415 := by decide

/-- The four tags are 1 to 4 and round-trip. -/
theorem tags_concrete :
    [Alg.ed25519, .ecdsaP256, .mlDsa65, .hybrid].map Alg.tag = [1, 2, 3, 4] ∧
      ∀ a, Alg.fromTag a.tag = some a := ⟨by decide, Alg.fromTag_tag⟩

end Vinc.BroadcastWire
