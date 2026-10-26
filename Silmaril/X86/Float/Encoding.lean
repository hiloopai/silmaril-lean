module

public import Silmaril.X86.Float.Instr
public import Silmaril.X86.Encoding
public import Silmaril.Machine.Decoder

/-!
# Byte codec for the scalar SSE subset

A verified encoder and decoder for `Silmaril.X86.Float.Instr` in 64-bit mode,
written from the Intel SDM Volume 2A, Chapter 2 (instruction format) and the
opcode lines of the Volume 2 instruction pages. It has three layers.

1. **Operand bytes** (namespace `Silmaril.X86`, independent of the subset).
   ModRM, SIB and displacement for a register or a `Mem` operand
   (§2.1.3-§2.1.5, Tables 2-2 and 2-3; §2.2.1.2, Table 2-5): RSP and R12 bases
   need a SIB byte; RBP and R13 bases have no `mod = 00` form and use a zero
   8-bit displacement; displacements use the shortest form. RIP-relative
   (§2.2.1.6) and base-less SIB operands are rejected.
2. **Raw fields** (`Raw`, also independent of the subset apart from the
   immediate table `hasImm8`). Byte order is mandatory prefix (`66`, `F2` or
   `F3`), REX, `0F`, an optional `38`/`3A` escape, opcode, operand bytes and an
   optional imm8. REX immediately precedes the escape (§2.2.1) and is emitted
   only when one of W, R, X, B is set. `Raw.parse_bytes` and `Raw.parse_sound`
   are the round trip and canonicity of this layer.
3. **Instructions.** `toRaw` is the opcode table. `candidate` reads it
   backwards, and `ofRaw` keeps a candidate only if `toRaw` reproduces every
   field, so a field that the instruction ignores or fixes (REX.W on ADDSS,
   REX.R under `0F AE /2`) must have its canonical value.

The decoder accepts exactly the encoder's outputs followed by arbitrary bytes:

* `decode_encode_append`: `decode (encode i ++ rest) = some (i, (encode i).length)`;
* `decode_sound`: a successful decode consumed `encode i` for its result `i`;
* `decode_take_of_lt`: every proper prefix of an encoding is rejected;
* `encode_length_ge`, `encode_length_le`: encodings have 3 to 12 bytes, within
  the 15-byte limit;
* `byteDecoder`: the codec as a `Machine.Decoder`.

`none` means "outside this canonical subset", not "invalid on hardware".
Processors accept encodings that are rejected here, among them redundant or
reordered prefixes, a REX prefix with no bit set or with bits the instruction
ignores, the `0F 11` register form of MOVSS/MOVSD, redundant SIB bytes and
longer-than-needed displacements, and reserved immediate bits. The assembler
agreement checks are in `Examples.lean`; nothing here is proved against the
Sail, ACL2 or hardware decoders.
-/

@[expose] public section

namespace Silmaril.X86

/-! ## Byte fields -/

/-- A byte made of a two-bit and two three-bit fields, most significant first:
a ModRM byte `mod:reg:rm` or a SIB byte `scale:index:base` (SDM Vol. 2A,
§2.1.3, Figure 2-1). -/
def fieldByte (hi : BitVec 2) (mid lo : BitVec 3) : Byte := hi ++ mid ++ lo

/-- The top two bits (`mod` or `scale`). -/
def Byte.top (b : Byte) : BitVec 2 := b.extractLsb' 6 2
/-- Bits 5:3 (`reg` or `index`). -/
def Byte.mid (b : Byte) : BitVec 3 := b.extractLsb' 3 3
/-- Bits 2:0 (`rm` or `base`). -/
def Byte.low (b : Byte) : BitVec 3 := b.extractLsb' 0 3

@[simp] theorem fieldByte_top (a : BitVec 2) (b c : BitVec 3) : (fieldByte a b c).top = a := by
  revert a b c; decide

@[simp] theorem fieldByte_mid (a : BitVec 2) (b c : BitVec 3) : (fieldByte a b c).mid = b := by
  revert a b c; decide

@[simp] theorem fieldByte_low (a : BitVec 2) (b c : BitVec 3) : (fieldByte a b c).low = c := by
  revert a b c; decide

@[simp] theorem fieldByte_eta (m : Byte) : fieldByte m.top m.mid m.low = m := by
  revert m; decide

/-- The REX extension bit (bit 3) of a four-bit register number. -/
def nibbleHi (n : BitVec 4) : BitVec 1 := n.extractLsb' 3 1
/-- The low three bits of a four-bit register number. -/
def nibbleLo (n : BitVec 4) : BitVec 3 := n.extractLsb' 0 3

@[simp] theorem nibbleHi_append (h : BitVec 1) (l : BitVec 3) : nibbleHi (h ++ l) = h := by
  revert h l; decide

@[simp] theorem nibbleLo_append (h : BitVec 1) (l : BitVec 3) : nibbleLo (h ++ l) = l := by
  revert h l; decide

@[simp] theorem nibbleHi_append_nibbleLo (n : BitVec 4) : nibbleHi n ++ nibbleLo n = n := by
  revert n; decide

/-- A REX prefix `0100WRXB` carrying the given `WRXB` nibble (SDM Vol. 2A,
§2.2.1.1, Table 2-4). -/
def rexByte (n : BitVec 4) : Byte := 0x4#4 ++ n

/-- The REX prefix, omitted when all four bits are clear. -/
def rexBytes (n : BitVec 4) : List Byte := if n = 0#4 then [] else [rexByte n]

/-- The `WRXB` nibble from its four bits. -/
def rexNibble (w r x b : BitVec 1) : BitVec 4 := w ++ r ++ x ++ b

@[simp] theorem rexNibble_w (w r x b : BitVec 1) : (rexNibble w r x b).extractLsb' 3 1 = w := by
  revert w r x b; decide
@[simp] theorem rexNibble_r (w r x b : BitVec 1) : (rexNibble w r x b).extractLsb' 2 1 = r := by
  revert w r x b; decide
@[simp] theorem rexNibble_x (w r x b : BitVec 1) : (rexNibble w r x b).extractLsb' 1 1 = x := by
  revert w r x b; decide
@[simp] theorem rexNibble_b (w r x b : BitVec 1) : (rexNibble w r x b).extractLsb' 0 1 = b := by
  revert w r x b; decide

@[simp] theorem rexNibble_eta (n : BitVec 4) :
    rexNibble (n.extractLsb' 3 1) (n.extractLsb' 2 1) (n.extractLsb' 1 1) (n.extractLsb' 0 1) =
      n := by
  revert n; decide

/-- Read an optional REX prefix. A bare `40` (no bit set) is rejected as
non-canonical: the subset has no byte-register operand for which it matters. -/
def parseRex : List Byte → Option (BitVec 4 × List Byte)
  | [] => some (0, [])
  | p :: rest =>
    if p.extractLsb' 4 4 = 0x4#4 then
      if p.extractLsb' 0 4 = 0#4 then none else some (p.extractLsb' 0 4, rest)
    else some (0, p :: rest)

@[simp] theorem rexByte_high (n : BitVec 4) : (rexByte n).extractLsb' 4 4 = 0x4#4 := by
  revert n; decide

@[simp] theorem rexByte_low (n : BitVec 4) : (rexByte n).extractLsb' 0 4 = n := by
  revert n; decide

theorem rexByte_eta (p : Byte) (h : p.extractLsb' 4 4 = 0x4#4) :
    rexByte (p.extractLsb' 0 4) = p := by
  revert p; decide

theorem parseRex_rexBytes (n : BitVec 4) (next : Byte) (rest : List Byte)
    (hnext : next.extractLsb' 4 4 ≠ 0x4#4) :
    parseRex (rexBytes n ++ next :: rest) = some (n, next :: rest) := by
  unfold rexBytes
  by_cases hn : n = 0#4
  · subst hn; simp [parseRex, hnext]
  · simp [parseRex, hn]

theorem parseRex_sound {bytes rest : List Byte} {n : BitVec 4}
    (h : parseRex bytes = some (n, rest)) : bytes = rexBytes n ++ rest := by
  match bytes, h with
  | [], h =>
    simp only [parseRex, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [rexBytes]
  | p :: tail, h =>
    simp only [parseRex] at h
    split_ifs at h with h4 h0
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [rexBytes, h0, rexByte_eta p h4]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [rexBytes]

/-! ## Displacements

With a memory operand, `mod = 00` has no displacement, `01` a sign-extended
8-bit one and `10` a 32-bit one (SDM Vol. 2A, Table 2-2). A base whose low three
bits are `101` (RBP, R13) has no `mod = 00` form, since that encoding means
RIP-relative (without SIB) or no base (with SIB). The canonical choice is the
shortest available form, which is what assemblers emit. -/

/-- The displacement fits the sign-extended 8-bit form. -/
def fitsInt8 (d : BitVec 32) : Bool := decide ((d.setWidth 8).signExtend 32 = d)

/-- The `mod = 00` form is available: zero displacement and a base other than
RBP/R13. -/
def NoDisp (baseLo : BitVec 3) (d : BitVec 32) : Prop := d = 0#32 ∧ baseLo ≠ 5#3

instance (baseLo : BitVec 3) (d : BitVec 32) : Decidable (NoDisp baseLo d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The canonical `mod` field for base low bits `baseLo` and displacement `d`. -/
def dispMod (baseLo : BitVec 3) (d : BitVec 32) : BitVec 2 :=
  if NoDisp baseLo d then 0#2 else if fitsInt8 d then 1#2 else 2#2

/-- The canonical displacement bytes. -/
def dispBytes (baseLo : BitVec 3) (d : BitVec 32) : List Byte :=
  if NoDisp baseLo d then [] else if fitsInt8 d then [d.setWidth 8] else imm32Bytes d

/-- Read the displacement for `mod = md`, rejecting non-canonical forms and the
`mod = 00`, `101` forms (RIP-relative or base-less). -/
def parseDisp (md : BitVec 2) (baseLo : BitVec 3) (bytes : List Byte) :
    Option (BitVec 32 × List Byte) :=
  if md = 0#2 then
    if baseLo = 5#3 then none else some (0#32, bytes)
  else if md = 1#2 then
    match bytes with
    | d :: rest => if NoDisp baseLo (d.signExtend 32) then none else some (d.signExtend 32, rest)
    | [] => none
  else if md = 2#2 then
    match decodeImm32 bytes with
    | some d => if fitsInt8 d then none else some (d, bytes.drop 4)
    | none => none
  else none

private theorem fitsInt8_signExtend (d : Byte) : fitsInt8 (d.signExtend 32) = true := by
  revert d; decide

private theorem setWidth_signExtend (d : Byte) : (d.signExtend 32).setWidth 8 = d := by
  revert d; decide

theorem dispMod_ne_three (baseLo : BitVec 3) (d : BitVec 32) : dispMod baseLo d ≠ 3#2 := by
  unfold dispMod; split_ifs <;> decide

theorem parseDisp_dispBytes (baseLo : BitVec 3) (d : BitVec 32) (rest : List Byte) :
    parseDisp (dispMod baseLo d) baseLo (dispBytes baseLo d ++ rest) = some (d, rest) := by
  unfold dispMod dispBytes
  by_cases h0 : NoDisp baseLo d
  · obtain ⟨rfl, h5⟩ := h0
    simp [parseDisp, h5, NoDisp]
  · by_cases h8 : fitsInt8 d = true
    · have hd : (d.setWidth 8).signExtend 32 = d := by simpa [fitsInt8] using h8
      simp [parseDisp, h0, h8, hd]
    · simp [parseDisp, h0, h8, List.drop_left' (length_imm32Bytes d)]

theorem parseDisp_sound {md : BitVec 2} {baseLo : BitVec 3} {bytes rest : List Byte}
    {d : BitVec 32} (h : parseDisp md baseLo bytes = some (d, rest)) :
    md = dispMod baseLo d ∧ bytes = dispBytes baseLo d ++ rest := by
  unfold parseDisp at h
  by_cases hm0 : md = 0#2
  · subst hm0
    by_cases h5 : baseLo = 5#3
    · simp [h5] at h
    · simp only [h5, ite_false, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : NoDisp baseLo 0#32 := ⟨rfl, h5⟩
      simp [dispMod, dispBytes, this]
  by_cases hm1 : md = 1#2
  · subst hm1
    simp only [hm0, ite_false, ite_true] at h
    match bytes, h with
    | b :: tail, h =>
      simp only at h
      split_ifs at h with hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [dispMod, dispBytes, hb, fitsInt8_signExtend, setWidth_signExtend]
  by_cases hm2 : md = 2#2
  · subst hm2
    simp only [hm0, hm1, ite_false, ite_true] at h
    cases himm : decodeImm32 bytes with
    | none => simp [himm] at h
    | some e =>
      simp only [himm] at h
      split_ifs at h with hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : ¬ NoDisp baseLo e := by
        rintro ⟨rfl, -⟩; exact hf rfl
      simp [dispMod, dispBytes, hz, hf, imm32Bytes_of_decodeImm32 himm]
  · simp [hm0, hm1, hm2] at h

/-! ## Memory operands

The bytes after ModRM for a memory operand are an optional SIB byte and the
displacement (SDM Vol. 2A, §2.1.5, Tables 2-2 and 2-3, and §2.2.1.2, Table 2-5).
A SIB byte is emitted exactly when there is an index or the base is RSP or R12
(whose ModRM `rm` value `100` means "SIB follows"). Without an index the SIB
byte is `00 100 base`: index `100` with REX.X = 0 means "no index", and scale
`00` is what assemblers emit. -/

namespace Mem

/-- An index is present or the base is RSP/R12. -/
def NeedsSib (m : Mem) : Prop := m.index.isSome = true ∨ m.base.lo = 4#3

instance (m : Mem) : Decidable m.NeedsSib := inferInstanceAs (Decidable (_ ∨ _))

/-- The ModRM `rm` field: `100` (SIB follows) or the base's low bits. -/
def rmField (m : Mem) : BitVec 3 := if m.NeedsSib then 4#3 else m.base.lo

/-- The ModRM `mod` field, selecting the displacement size. -/
def modField (m : Mem) : BitVec 2 := dispMod m.base.lo m.disp

/-- REX.X: the extension bit of the index, if any. -/
def xBit (m : Mem) : BitVec 1 :=
  match m.index with
  | some (i, _) => i.1.hi
  | none => 0#1

/-- The SIB `scale` and `index` fields. -/
def sibScale (m : Mem) : BitVec 2 :=
  match m.index with
  | some (_, s) => s.toBitVec
  | none => 0#2

def sibIndex (m : Mem) : BitVec 3 :=
  match m.index with
  | some (i, _) => i.1.lo
  | none => 4#3

/-- The SIB byte, if any, followed by the displacement. -/
def tailBytes (m : Mem) : List Byte :=
  (if m.NeedsSib then [fieldByte m.sibScale m.sibIndex m.base.lo] else []) ++
    dispBytes m.base.lo m.disp

end Mem

theorem Reg.ofBitVec_ne_rsp {n : BitVec 4} (h : n ≠ 4#4) : Reg.ofBitVec n ≠ .rsp := by
  intro heq
  apply h
  have := congrArg Reg.toBitVec heq
  rw [Reg.toBitVec_ofBitVec] at this
  exact this

/-- Read the SIB `scale`/`index` fields, given REX.X. `none` rejects the
non-canonical index-free forms (nonzero scale, or a SIB byte that is not
required by the base). -/
def parseSibIndex (x : BitVec 1) (ss : BitVec 2) (idx base : BitVec 3) :
    Option (Option (IndexReg × Scale)) :=
  if h : x ++ idx = 4#4 then
    if ss = 0#2 ∧ base = 4#3 then some none else none
  else some (some (⟨Reg.ofBitVec (x ++ idx), Reg.ofBitVec_ne_rsp h⟩, Scale.ofBitVec ss))

theorem IndexReg.hi_append_lo_ne (i : IndexReg) : i.1.hi ++ i.1.lo ≠ 4#4 := by
  rw [Reg.hi_append_lo]
  intro h
  apply i.2
  apply Reg.toBitVec_injective
  simpa [Reg.toBitVec] using h

theorem parseSibIndex_some (i : IndexReg) (s : Scale) (base : BitVec 3) :
    parseSibIndex i.1.hi s.toBitVec i.1.lo base = some (some (i, s)) := by
  simp [parseSibIndex, IndexReg.hi_append_lo_ne i]

theorem parseSibIndex_sound {x : BitVec 1} {ss : BitVec 2} {idx base : BitVec 3}
    {index : Option (IndexReg × Scale)} (h : parseSibIndex x ss idx base = some index) :
    match index with
    | none => x = 0#1 ∧ ss = 0#2 ∧ idx = 4#3 ∧ base = 4#3
    | some (i, s) => x = i.1.hi ∧ ss = s.toBitVec ∧ idx = i.1.lo := by
  unfold parseSibIndex at h
  split at h
  next h4 =>
    split_ifs at h with hc
    cases h
    have hx : x = 0#1 ∧ idx = 4#3 := by
      have h1 := congrArg nibbleHi h4
      have h2 := congrArg nibbleLo h4
      simp only [nibbleHi_append, nibbleLo_append] at h1 h2
      exact ⟨h1.trans (by decide), h2.trans (by decide)⟩
    exact ⟨hx.1, hc.1, hx.2, hc.2⟩
  next h4 =>
    cases h
    simp

/-- Read the SIB byte (when ModRM `rm = 100`) and displacement of a memory
operand with ModRM `mod = md` and `rm = rmf`, given REX.X and REX.B. -/
def parseMem (md : BitVec 2) (rmf : BitVec 3) (x b : BitVec 1) (bytes : List Byte) :
    Option (Mem × List Byte) :=
  if rmf = 4#3 then
    match bytes with
    | s :: rest =>
      match parseSibIndex x s.top s.mid s.low with
      | some index =>
        (parseDisp md s.low rest).map fun (d, rest) =>
          ({ base := Reg.ofBitVec (b ++ s.low), index, disp := d }, rest)
      | none => none
    | [] => none
  else if x = 0#1 then
    (parseDisp md rmf bytes).map fun (d, rest) =>
      ({ base := Reg.ofBitVec (b ++ rmf), index := none, disp := d }, rest)
  else none

theorem parseMem_tailBytes (m : Mem) (rest : List Byte) :
    parseMem m.modField m.rmField m.xBit m.base.hi (m.tailBytes ++ rest) = some (m, rest) := by
  obtain ⟨base, index, disp⟩ := m
  cases index with
  | none =>
    by_cases hb : base.lo = 4#3
    · have hs : Mem.NeedsSib { base, index := none, disp } := Or.inr hb
      have hsib : parseSibIndex 0#1 0#2 4#3 base.lo = some none := by
        simp [parseSibIndex, hb]
      simp only [Mem.tailBytes, Mem.rmField, Mem.modField, Mem.xBit, Mem.sibScale, Mem.sibIndex,
        hs, ite_true, parseMem, List.cons_append, List.nil_append, fieldByte_top, fieldByte_mid,
        fieldByte_low, hsib, parseDisp_dispBytes, Option.map_some, Reg.ofBitVec_hi_append_lo]
    · have hs : ¬ Mem.NeedsSib { base, index := none, disp } := by
        simp [Mem.NeedsSib, hb]
      simp only [Mem.tailBytes, Mem.rmField, Mem.modField, Mem.xBit, hs, ite_false, parseMem, hb,
        ite_true, List.nil_append, parseDisp_dispBytes, Option.map_some,
        Reg.ofBitVec_hi_append_lo]
  | some p =>
    obtain ⟨i, s⟩ := p
    have hs : Mem.NeedsSib { base, index := some (i, s), disp } := Or.inl rfl
    simp only [Mem.tailBytes, Mem.rmField, Mem.modField, Mem.xBit, Mem.sibScale, Mem.sibIndex,
      hs, ite_true, parseMem, List.cons_append, List.nil_append, fieldByte_top, fieldByte_mid,
      fieldByte_low, parseSibIndex_some, parseDisp_dispBytes, Option.map_some,
      Reg.ofBitVec_hi_append_lo]

theorem parseMem_sound {md : BitVec 2} {rmf : BitVec 3} {x b : BitVec 1}
    {bytes rest : List Byte} {m : Mem} (h : parseMem md rmf x b bytes = some (m, rest)) :
    md = m.modField ∧ rmf = m.rmField ∧ x = m.xBit ∧ b = m.base.hi ∧
      bytes = m.tailBytes ++ rest := by
  unfold parseMem at h
  split_ifs at h with h4 hx
  · match bytes, h with
    | s :: tail, h =>
      simp only at h
      split at h
      next index hindex =>
        obtain ⟨⟨d, rest'⟩, hd, heq⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨hmd, htail⟩ := parseDisp_sound hd
        have hsib := parseSibIndex_sound hindex
        cases index with
        | none =>
          obtain ⟨rfl, hss, hidx, hbase⟩ := hsib
          have hs : Mem.NeedsSib { base := Reg.ofBitVec (b ++ s.low), index := none, disp := d } :=
            Or.inr (by simpa using hbase)
          refine ⟨by simpa [Mem.modField] using hmd, by simp [Mem.rmField, hs, h4],
            by simp [Mem.xBit], by simp, ?_⟩
          simp only [Mem.tailBytes, hs, ite_true, Mem.sibScale, Mem.sibIndex, Reg.lo_ofBitVec,
            List.cons_append, List.nil_append, ← htail, ← hss, ← hidx, fieldByte_eta]
        | some p =>
          obtain ⟨i, sc⟩ := p
          obtain ⟨rfl, hss, hidx⟩ := hsib
          have hs : Mem.NeedsSib ⟨Reg.ofBitVec (b ++ s.low), some (i, sc), d⟩ := Or.inl rfl
          refine ⟨by simpa [Mem.modField] using hmd, by simp [Mem.rmField, hs, h4],
            by simp [Mem.xBit], by simp, ?_⟩
          simp only [Mem.tailBytes, hs, ite_true, Mem.sibScale, Mem.sibIndex, Reg.lo_ofBitVec,
            List.cons_append, List.nil_append, ← htail, ← hss, ← hidx, fieldByte_eta]
      next => cases h
  · obtain ⟨⟨d, rest'⟩, hd, heq⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hmd, htail⟩ := parseDisp_sound hd
    have hs : ¬ Mem.NeedsSib { base := Reg.ofBitVec (b ++ rmf), index := none, disp := d } := by
      simp [Mem.NeedsSib, h4]
    refine ⟨by simpa [Mem.modField] using hmd, by simp [Mem.rmField, hs], by simp [Mem.xBit, hx],
      by simp, ?_⟩
    simpa [Mem.tailBytes, hs] using htail

/-! ## ModRM operands -/

/-- The ModRM `r/m` operand of an instruction: a register number or memory. -/
inductive Operand where
  | reg (n : BitVec 4)
  | mem (m : Mem)
  deriving DecidableEq, Repr

namespace Operand

/-- REX.X for the operand. -/
def xBit : Operand → BitVec 1
  | reg _ => 0#1
  | mem m => m.xBit

/-- REX.B for the operand. -/
def bBit : Operand → BitVec 1
  | reg n => nibbleHi n
  | mem m => m.base.hi

/-- The ModRM byte with `reg = regf`, then the SIB byte and displacement. -/
def bytes (regf : BitVec 3) : Operand → List Byte
  | reg n => [fieldByte 3#2 regf (nibbleLo n)]
  | mem m => fieldByte m.modField regf m.rmField :: m.tailBytes

end Operand

/-- Read a ModRM byte and the operand bytes that follow it, given REX.X and
REX.B; returns the ModRM `reg` field and the `r/m` operand. REX.X must be clear
for a register operand. -/
def parseOperand (x b : BitVec 1) : List Byte → Option ((BitVec 3 × Operand) × List Byte)
  | [] => none
  | mb :: rest =>
    if mb.top = 3#2 then
      if x = 0#1 then some ((mb.mid, .reg (b ++ mb.low)), rest) else none
    else (parseMem mb.top mb.low x b rest).map fun (m, rest) => ((mb.mid, .mem m), rest)

theorem parseOperand_bytes (regf : BitVec 3) (op : Operand) (rest : List Byte) :
    parseOperand op.xBit op.bBit (op.bytes regf ++ rest) = some ((regf, op), rest) := by
  cases op with
  | reg n => simp [parseOperand, Operand.xBit, Operand.bBit, Operand.bytes]
  | mem m =>
    have h3 : m.modField ≠ 3#2 := dispMod_ne_three _ _
    simp [parseOperand, Operand.xBit, Operand.bBit, Operand.bytes, h3, parseMem_tailBytes]

theorem parseOperand_sound {x b : BitVec 1} {bytes rest : List Byte} {regf : BitVec 3}
    {op : Operand} (h : parseOperand x b bytes = some ((regf, op), rest)) :
    x = op.xBit ∧ b = op.bBit ∧ bytes = op.bytes regf ++ rest := by
  match bytes, h with
  | mb :: tail, h =>
    simp only [parseOperand] at h
    split_ifs at h with h3 hx
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨hx, by simp [Operand.bBit], ?_⟩
      simp [Operand.bytes, ← h3]
    · obtain ⟨⟨m, rest'⟩, hm, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      obtain ⟨hmd, hrmf, hx, hb, htail⟩ := parseMem_sound hm
      refine ⟨hx, hb, ?_⟩
      simp [Operand.bytes, ← hmd, ← hrmf, ← htail]

/-! ## Raw legacy-encoded instructions

A `Raw` instruction is the field-level view of a legacy (non-VEX) encoding
with one ModRM byte (SDM Vol. 2A, §2.1 and §2.2.1): an optional mandatory
prefix `66`, `F2` or `F3`; an optional REX prefix, which must immediately
precede the opcode (§2.2.1); the escape `0F`, optionally followed by `38` or
`3A`; the opcode; ModRM with its SIB byte and displacement; and an optional
8-bit immediate. It is independent of the instruction subset except for
`hasImm8`, which lists the opcodes that take an immediate. -/

/-- A mandatory prefix. -/
inductive Prefix where
  | none | p66 | pF2 | pF3
  deriving DecidableEq, Repr

def Prefix.bytes : Prefix → List Byte
  | none => [] | p66 => [0x66#8] | pF2 => [0xF2#8] | pF3 => [0xF3#8]

/-- Read one of `66`, `F2`, `F3`, if present. -/
def parsePrefix : List Byte → Prefix × List Byte
  | [] => (.none, [])
  | p :: rest =>
    if p = 0x66#8 then (.p66, rest) else if p = 0xF2#8 then (.pF2, rest)
    else if p = 0xF3#8 then (.pF3, rest) else (.none, p :: rest)

/-- The opcode map selected after `0F`. -/
inductive OpMap where
  | m0F | m0F38 | m0F3A
  deriving DecidableEq, Repr

def OpMap.bytes : OpMap → List Byte
  | m0F => [] | m0F38 => [0x38#8] | m0F3A => [0x3A#8]

def parseMap : List Byte → OpMap × List Byte
  | [] => (.m0F, [])
  | p :: rest =>
    if p = 0x38#8 then (.m0F38, rest) else if p = 0x3A#8 then (.m0F3A, rest)
    else (.m0F, p :: rest)

/-- Whether an 8-bit immediate follows the operand bytes. The table covers the
modeled subset only: every `0F 3A` opcode, and `0F C2` (CMPPS/CMPSS/CMPSD). -/
def hasImm8 : OpMap → Byte → Bool
  | .m0F3A, _ => true
  | .m0F, opc => decide (opc = 0xC2#8)
  | .m0F38, _ => false

def parseImm8 (has : Bool) (bytes : List Byte) : Option (Option Byte × List Byte) :=
  if has then
    match bytes with
    | b :: rest => some (some b, rest)
    | [] => none
  else some (none, bytes)

/-- The fields of a legacy-encoded instruction. `reg` is the four-bit ModRM
`reg` field including REX.R. -/
structure Raw where
  pfx : Prefix
  w : BitVec 1
  map : OpMap
  opc : Byte
  reg : BitVec 4
  rm : Operand
  imm : Option Byte
  deriving DecidableEq, Repr

namespace Raw

/-- The `WRXB` bits of the REX prefix. -/
def rex (r : Raw) : BitVec 4 := rexNibble r.w (nibbleHi r.reg) r.rm.xBit r.rm.bBit

/-- The canonical byte string. REX is emitted only when one of its bits is
set. -/
def bytes (r : Raw) : List Byte :=
  r.pfx.bytes ++ (rexBytes r.rex ++ (0x0F#8 :: (r.map.bytes ++
    (r.opc :: (r.rm.bytes (nibbleLo r.reg) ++ r.imm.toList)))))

/-- The side conditions under which `parse` recovers the fields: an opcode in
the `0F` map is not an escape byte, and the immediate is present exactly when
the opcode takes one. -/
structure WellFormed (r : Raw) : Prop where
  not_escape : r.map = .m0F → r.opc ≠ 0x38#8 ∧ r.opc ≠ 0x3A#8
  imm : r.imm.isSome = hasImm8 r.map r.opc

/-- Read one legacy-encoded instruction, returning its fields and the bytes
after it. Non-canonical encodings (a bare `40` REX, a set REX.X without an
index, redundant SIB bytes, non-minimal displacements) and RIP-relative or
base-less memory operands are rejected. -/
def parse (bytes : List Byte) : Option (Raw × List Byte) :=
  match parsePrefix bytes with
  | (pfx, bytes) =>
  match parseRex bytes with
  | none => none
  | some (rex, bytes) =>
  match bytes with
  | [] => none
  | esc :: bytes =>
  if esc = 0x0F#8 then
    match parseMap bytes with
    | (map, bytes) =>
    match bytes with
    | [] => none
    | opc :: bytes =>
    match parseOperand (rex.extractLsb' 1 1) (rex.extractLsb' 0 1) bytes with
    | none => none
    | some ((regf, rm), bytes) =>
      (parseImm8 (hasImm8 map opc) bytes).map fun (imm, bytes) =>
        ({ pfx, w := rex.extractLsb' 3 1, map, opc, reg := rex.extractLsb' 2 1 ++ regf, rm, imm },
          bytes)
  else none

theorem bytes_length_le (r : Raw) : r.bytes.length ≤ 12 := by
  obtain ⟨pfx, w, map, opc, reg, rm, imm⟩ := r
  have hp : pfx.bytes.length ≤ 1 := by cases pfx <;> simp [Prefix.bytes]
  have hm : map.bytes.length ≤ 1 := by cases map <;> simp [OpMap.bytes]
  have hi : imm.toList.length ≤ 1 := by cases imm <;> simp
  have hx (n : BitVec 4) : (rexBytes n).length ≤ 1 := by unfold rexBytes; split <;> simp
  have hd (bl : BitVec 3) (d : BitVec 32) : (dispBytes bl d).length ≤ 4 := by
    unfold dispBytes; split_ifs <;> simp
  have ho (regf : BitVec 3) (op : Operand) : (op.bytes regf).length ≤ 6 := by
    cases op with
    | reg n => simp [Operand.bytes]
    | mem m =>
      simp only [Operand.bytes, Mem.tailBytes, List.length_cons, List.length_append]
      have := hd m.base.lo m.disp
      split_ifs <;> simp <;> omega
  have := hx (rexNibble w (nibbleHi reg) rm.xBit rm.bBit)
  have := ho (nibbleLo reg) rm
  simp only [bytes, rex, List.length_append, List.length_cons]
  omega

theorem bytes_length_ge (r : Raw) : 3 ≤ r.bytes.length := by
  simp only [bytes, List.length_append, List.length_cons]
  cases r.rm <;> simp [Operand.bytes] <;> omega

end Raw

theorem parsePrefix_bytes (p : Prefix) {bytes : List Byte}
    (h : parsePrefix bytes = (.none, bytes)) : parsePrefix (p.bytes ++ bytes) = (p, bytes) := by
  cases p <;> simp_all [Prefix.bytes, parsePrefix]

theorem parsePrefix_sound {bytes rest : List Byte} {p : Prefix}
    (h : parsePrefix bytes = (p, rest)) : bytes = p.bytes ++ rest := by
  match bytes, h with
  | [], h =>
    simp only [parsePrefix, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | b :: tail, h =>
    simp only [parsePrefix] at h
    split_ifs at h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
      simp_all [Prefix.bytes]

theorem parseMap_bytes (m : OpMap) {opc : Byte} (rest : List Byte)
    (h : m = .m0F → opc ≠ 0x38#8 ∧ opc ≠ 0x3A#8) :
    parseMap (m.bytes ++ opc :: rest) = (m, opc :: rest) := by
  cases m <;> simp_all [OpMap.bytes, parseMap]

theorem parseMap_sound {bytes rest : List Byte} {m : OpMap}
    (h : parseMap bytes = (m, rest)) : bytes = m.bytes ++ rest := by
  match bytes, h with
  | [], h =>
    simp only [parseMap, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | b :: tail, h =>
    simp only [parseMap] at h
    split_ifs at h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
      simp_all [OpMap.bytes]

theorem parseImm8_toList {has : Bool} {imm : Option Byte} (h : imm.isSome = has)
    (rest : List Byte) : parseImm8 has (imm.toList ++ rest) = some (imm, rest) := by
  subst h
  cases imm <;> simp [parseImm8]

theorem parseImm8_sound {has : Bool} {bytes rest : List Byte} {imm : Option Byte}
    (h : parseImm8 has bytes = some (imm, rest)) : bytes = imm.toList ++ rest := by
  unfold parseImm8 at h
  split at h
  · match bytes, h with
    | b :: tail, h =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

private theorem parsePrefix_rex (n : BitVec 4) (rest : List Byte) :
    parsePrefix (rexBytes n ++ 0x0F#8 :: rest) = (.none, rexBytes n ++ 0x0F#8 :: rest) := by
  unfold rexBytes
  split
  · simp [parsePrefix]
  · have h1 : rexByte n ≠ 0x66#8 := by revert n; decide
    have h2 : rexByte n ≠ 0xF2#8 := by revert n; decide
    have h3 : rexByte n ≠ 0xF3#8 := by revert n; decide
    simp [parsePrefix, h1, h2, h3]

namespace Raw

/-- The parser recovers every well-formed `Raw` from its bytes, whatever
follows them. -/
theorem parse_bytes (r : Raw) (wf : r.WellFormed) (rest : List Byte) :
    parse (r.bytes ++ rest) = some (r, rest) := by
  obtain ⟨pfx, w, map, opc, reg, rm, imm⟩ := r
  obtain ⟨hesc, himm⟩ := wf
  dsimp only at hesc himm
  simp only [bytes, List.append_assoc, List.cons_append]
  unfold parse
  rw [parsePrefix_bytes _ (parsePrefix_rex _ _)]
  simp only
  rw [parseRex_rexBytes _ _ _ (by decide)]
  simp only [ite_true, rex, rexNibble_x, rexNibble_b, rexNibble_w, rexNibble_r]
  rw [parseMap_bytes _ _ hesc]
  simp only
  rw [parseOperand_bytes]
  simp only
  rw [parseImm8_toList himm]
  simp

/-- Every successful parse consumed the canonical bytes of its result. -/
theorem parse_sound {bytes rest : List Byte} {r : Raw} (h : parse bytes = some (r, rest)) :
    bytes = r.bytes ++ rest := by
  unfold parse at h
  rcases hp : parsePrefix bytes with ⟨pfx, b1⟩
  rw [hp] at h
  simp only at h
  cases hr : parseRex b1 with
  | none => rw [hr] at h; cases h
  | some res =>
  obtain ⟨n, b2⟩ := res
  rw [hr] at h
  simp only at h
  match b2, h with
  | esc :: b3, h =>
  simp only at h
  split_ifs at h with hesc
  rcases hm : parseMap b3 with ⟨map, b4⟩
  rw [hm] at h
  simp only at h
  match b4, h with
  | opc :: b5, h =>
  simp only at h
  cases ho : parseOperand (n.extractLsb' 1 1) (n.extractLsb' 0 1) b5 with
  | none => rw [ho] at h; cases h
  | some res =>
  obtain ⟨⟨regf, rm⟩, b6⟩ := res
  rw [ho] at h
  simp only at h
  obtain ⟨⟨imm, b7⟩, hi, heq⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨hx, hb, h5⟩ := parseOperand_sound ho
  rw [parsePrefix_sound hp, parseRex_sound hr, parseMap_sound hm, h5, parseImm8_sound hi,
    hesc]
  have hrex : rexNibble (n.extractLsb' 3 1) (n.extractLsb' 2 1) rm.xBit rm.bBit = n := by
    rw [← hx, ← hb, rexNibble_eta]
  simp [Raw.bytes, rex, hrex]

end Raw

end Silmaril.X86

/-! ## Scalar SSE instructions -/

namespace Silmaril.X86.Float

/-- The mandatory prefix of the SS/SD forms: `F3` or `F2`. -/
def Precision.scalarPrefix : Precision → Prefix
  | .single => .pF3 | .double => .pF2

/-- The mandatory prefix of the PS/PD forms: none or `66`. -/
def Precision.packedPrefix : Precision → Prefix
  | .single => .none | .double => .p66

/-- REX.W for a general-purpose operand of this size. -/
def IntWidth.wBit : IntWidth → BitVec 1
  | .w32 => 0#1 | .w64 => 1#1

def IntWidth.ofBit (b : BitVec 1) : IntWidth := if b = 1#1 then .w64 else .w32

@[simp] theorem IntWidth.ofBit_wBit (w : IntWidth) : IntWidth.ofBit w.wBit = w := by
  cases w <;> rfl

def XRM.toOperand : XRM → Operand
  | .reg r => .reg r.toBitVec | .mem m => .mem m

def GRM.toOperand : GRM → Operand
  | .reg r => .reg r.toBitVec | .mem m => .mem m

def _root_.Silmaril.X86.Operand.toXRM : Operand → XRM
  | .reg n => .reg (XReg.ofBitVec n) | .mem m => .mem m

def _root_.Silmaril.X86.Operand.toGRM : Operand → GRM
  | .reg n => .reg (Reg.ofBitVec n) | .mem m => .mem m

@[simp] theorem XRM.toOperand_toXRM (x : XRM) : x.toOperand.toXRM = x := by
  cases x <;> simp [XRM.toOperand, Operand.toXRM]

@[simp] theorem GRM.toOperand_toGRM (x : GRM) : x.toOperand.toGRM = x := by
  cases x <;> simp [GRM.toOperand, Operand.toGRM]

/-- `0F 58` ADD, `59` MUL, `5C` SUB, `5D` MIN, `5E` DIV, `5F` MAX. -/
def ArithOp.opcode : ArithOp → Byte
  | .add => 0x58#8 | .mul => 0x59#8 | .sub => 0x5C#8 | .min => 0x5D#8 | .div => 0x5E#8
  | .max => 0x5F#8

/-- `0F 54` AND, `55` ANDN, `56` OR, `57` XOR. -/
def LogicOp.opcode : LogicOp → Byte
  | .and => 0x54#8 | .andn => 0x55#8 | .or => 0x56#8 | .xor => 0x57#8

/-- ROUNDSS is `66 0F 3A 0A`, ROUNDSD is `66 0F 3A 0B`. -/
def Precision.roundOpcode : Precision → Byte
  | .single => 0x0A#8 | .double => 0x0B#8

/-- `imm8 = 0000 P RS RC`. -/
def RoundImm.toByte (c : RoundImm) : Byte :=
  0#4 ++ BitVec.ofBool c.suppressInexact ++ BitVec.ofBool c.useMxcsr ++ c.rc

/-- Immediates with a reserved bit 7:4 set are outside the subset. -/
def RoundImm.ofByte? (b : Byte) : Option RoundImm :=
  if b.extractLsb' 4 4 = 0#4 then
    some { rc := b.extractLsb' 0 2, useMxcsr := b.getLsbD 2, suppressInexact := b.getLsbD 3 }
  else none

@[simp] theorem RoundImm.ofByte?_toByte (c : RoundImm) : RoundImm.ofByte? c.toByte = some c := by
  obtain ⟨rc, u, s⟩ := c
  revert rc u s
  decide

/-- The legacy predicate immediate `00000 ppp`. -/
def CmpPred.toByte (p : CmpPred) : Byte := 0#5 ++ p.toBitVec

/-- Immediates 8-255 (reserved bits 7:3 set) are outside the subset. -/
def CmpPred.ofByte? (b : Byte) : Option CmpPred :=
  if b.extractLsb' 3 5 = 0#5 then some (CmpPred.ofBitVec (b.extractLsb' 0 3)) else none

@[simp] theorem CmpPred.ofByte?_toByte (p : CmpPred) : CmpPred.ofByte? p.toByte = some p := by
  cases p <;> decide

/-- A `0F`-map instruction without an immediate. -/
def raw0F (pfx : Prefix) (w : BitVec 1) (opc : Byte) (reg : BitVec 4) (rm : Operand) : Raw :=
  { pfx, w, map := .m0F, opc, reg, rm, imm := none }

/-- The fields of each instruction (SDM Vol. 2, instruction pages). `/r`
forms put the first (destination) operand in ModRM `reg` except the stores
MOVSS/MOVSD `m, xmm` (`0F 11`) and MOVD/MOVQ `r/m, xmm` (`66 0F 7E`), whose
ModRM `r/m` is the destination. -/
def toRaw : Instr → Raw
  | .movs p dst src => raw0F p.scalarPrefix 0#1 0x10#8 dst.toBitVec (.reg src.toBitVec)
  | .load p dst m => raw0F p.scalarPrefix 0#1 0x10#8 dst.toBitVec (.mem m)
  | .store p m src => raw0F p.scalarPrefix 0#1 0x11#8 src.toBitVec (.mem m)
  | .movToX w dst src => raw0F .p66 w.wBit 0x6E#8 dst.toBitVec (.reg src.toBitVec)
  | .movFromX w dst src => raw0F .p66 w.wBit 0x7E#8 src.toBitVec (.reg dst.toBitVec)
  | .movap p dst src => raw0F p.packedPrefix 0#1 0x28#8 dst.toBitVec (.reg src.toBitVec)
  | .arith op p dst src => raw0F p.scalarPrefix 0#1 op.opcode dst.toBitVec src.toOperand
  | .sqrt p dst src => raw0F p.scalarPrefix 0#1 0x51#8 dst.toBitVec src.toOperand
  | .cvtFromInt p w dst src => raw0F p.scalarPrefix w.wBit 0x2A#8 dst.toBitVec src.toOperand
  | .cvtToIntTrunc p w dst src => raw0F p.scalarPrefix w.wBit 0x2C#8 dst.toBitVec src.toOperand
  | .cvtToInt p w dst src => raw0F p.scalarPrefix w.wBit 0x2D#8 dst.toBitVec src.toOperand
  | .cvtPrec p dst src => raw0F p.scalarPrefix 0#1 0x5A#8 dst.toBitVec src.toOperand
  | .ucomi p a b => raw0F p.packedPrefix 0#1 0x2E#8 a.toBitVec b.toOperand
  | .comi p a b => raw0F p.packedPrefix 0#1 0x2F#8 a.toBitVec b.toOperand
  | .logic op p dst src => raw0F p.packedPrefix 0#1 op.opcode dst.toBitVec src.toOperand
  | .round p dst src ctrl =>
    { pfx := .p66, w := 0#1, map := .m0F3A, opc := p.roundOpcode, reg := dst.toBitVec,
      rm := src.toOperand, imm := some ctrl.toByte }
  | .cmp p pred dst src =>
    { pfx := p.scalarPrefix, w := 0#1, map := .m0F, opc := 0xC2#8, reg := dst.toBitVec,
      rm := src.toOperand, imm := some pred.toByte }
  | .ldmxcsr m => raw0F .none 0#1 0xAE#8 2#4 (.mem m)
  | .stmxcsr m => raw0F .none 0#1 0xAE#8 3#4 (.mem m)

/-- The SS/SD opcode table (prefix `F3` or `F2`). -/
def scalarCandidate (p : Precision) (r : Raw) : Option Instr :=
  let x := XReg.ofBitVec r.reg
  let g := Reg.ofBitVec r.reg
  let w := IntWidth.ofBit r.w
  match r.opc.toNat with
  | 0x10 =>
    match r.rm with
    | .reg n => some (.movs p x (XReg.ofBitVec n))
    | .mem m => some (.load p x m)
  | 0x11 =>
    match r.rm with
    | .mem m => some (.store p m x)
    | .reg _ => none
  | 0x2A => some (.cvtFromInt p w x r.rm.toGRM)
  | 0x2C => some (.cvtToIntTrunc p w g r.rm.toXRM)
  | 0x2D => some (.cvtToInt p w g r.rm.toXRM)
  | 0x51 => some (.sqrt p x r.rm.toXRM)
  | 0x58 => some (.arith .add p x r.rm.toXRM)
  | 0x59 => some (.arith .mul p x r.rm.toXRM)
  | 0x5A => some (.cvtPrec p x r.rm.toXRM)
  | 0x5C => some (.arith .sub p x r.rm.toXRM)
  | 0x5D => some (.arith .min p x r.rm.toXRM)
  | 0x5E => some (.arith .div p x r.rm.toXRM)
  | 0x5F => some (.arith .max p x r.rm.toXRM)
  | 0xC2 =>
    match r.imm with
    | some b => (CmpPred.ofByte? b).map fun pred => .cmp p pred x r.rm.toXRM
    | none => none
  | _ => none

/-- The PS/PD opcode table (no prefix or `66`). -/
def packedCandidate (p : Precision) (r : Raw) : Option Instr :=
  let x := XReg.ofBitVec r.reg
  match r.opc.toNat with
  | 0x28 =>
    match r.rm with
    | .reg n => some (.movap p x (XReg.ofBitVec n))
    | .mem _ => none
  | 0x2E => some (.ucomi p x r.rm.toXRM)
  | 0x2F => some (.comi p x r.rm.toXRM)
  | 0x54 => some (.logic .and p x r.rm.toXRM)
  | 0x55 => some (.logic .andn p x r.rm.toXRM)
  | 0x56 => some (.logic .or p x r.rm.toXRM)
  | 0x57 => some (.logic .xor p x r.rm.toXRM)
  | _ => none

/-- Read the opcode tables. The result is only a candidate: `ofRaw` accepts it
when its encoding reproduces every field, which rejects, for example, a set
REX.W on an instruction that ignores it. -/
def candidate (r : Raw) : Option Instr :=
  match r.map, r.pfx with
  | .m0F, .pF3 => scalarCandidate .single r
  | .m0F, .pF2 => scalarCandidate .double r
  | .m0F, .p66 =>
    match r.opc.toNat, r.rm with
    | 0x6E, .reg n => some (.movToX (IntWidth.ofBit r.w) (XReg.ofBitVec r.reg) (Reg.ofBitVec n))
    | 0x7E, .reg n => some (.movFromX (IntWidth.ofBit r.w) (Reg.ofBitVec n) (XReg.ofBitVec r.reg))
    | _, _ => packedCandidate .double r
  | .m0F, .none =>
    match r.opc.toNat, r.rm with
    | 0xAE, .mem m =>
      if r.reg = 2#4 then some (.ldmxcsr m) else if r.reg = 3#4 then some (.stmxcsr m) else none
    | _, _ => packedCandidate .single r
  | .m0F3A, .p66 =>
    match r.opc.toNat, r.imm with
    | 0x0A, some b => (RoundImm.ofByte? b).map (.round .single (XReg.ofBitVec r.reg) r.rm.toXRM)
    | 0x0B, some b => (RoundImm.ofByte? b).map (.round .double (XReg.ofBitVec r.reg) r.rm.toXRM)
    | _, _ => none
  | _, _ => none

/-- The instruction with these fields, if any. -/
def ofRaw (r : Raw) : Option Instr :=
  match candidate r with
  | some i => if toRaw i = r then some i else none
  | none => none

theorem candidate_toRaw (i : Instr) : candidate (toRaw i) = some i := by
  cases i with
  | arith op p => cases op <;> cases p <;> simp [toRaw, raw0F, candidate, scalarCandidate,
      ArithOp.opcode, Precision.scalarPrefix]
  | logic op p => cases op <;> cases p <;> simp [toRaw, raw0F, candidate, packedCandidate,
      LogicOp.opcode, Precision.packedPrefix]
  | round p => cases p <;> simp [toRaw, candidate, Precision.roundOpcode]
  | cmp p => cases p <;> simp [toRaw, candidate, scalarCandidate, Precision.scalarPrefix]
  | movToX | movFromX | ldmxcsr | stmxcsr => simp [toRaw, raw0F, candidate]
  | movs p | load p | store p | sqrt p | cvtFromInt p | cvtToIntTrunc p | cvtToInt p
  | cvtPrec p =>
    cases p <;> simp [toRaw, raw0F, candidate, scalarCandidate, Precision.scalarPrefix]
  | movap p | ucomi p | comi p =>
    cases p <;> simp [toRaw, raw0F, candidate, packedCandidate, Precision.packedPrefix]

@[simp] theorem ofRaw_toRaw (i : Instr) : ofRaw (toRaw i) = some i := by
  simp [ofRaw, candidate_toRaw]

theorem toRaw_of_ofRaw {r : Raw} {i : Instr} (h : ofRaw r = some i) : toRaw i = r := by
  unfold ofRaw at h
  split at h
  · split_ifs at h with heq
    cases h
    exact heq
  · cases h

theorem toRaw_wellFormed (i : Instr) : (toRaw i).WellFormed := by
  cases i
  case arith op _ _ _ =>
    cases op <;> constructor <;> simp [toRaw, raw0F, ArithOp.opcode, hasImm8]
  case logic op _ _ _ =>
    cases op <;> constructor <;> simp [toRaw, raw0F, LogicOp.opcode, hasImm8]
  all_goals constructor <;> simp [toRaw, raw0F, hasImm8]

/-! ## Encoder and decoder -/

/-- The canonical encoding: the assembler's minimal form. -/
def encode (i : Instr) : List Byte := (toRaw i).bytes

/-- Decode one instruction from the start of `bytes`, returning it with the
number of bytes consumed. Only the bytes of the instruction are read. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match Raw.parse bytes with
  | some (r, rest) => (ofRaw r).map fun i => (i, bytes.length - rest.length)
  | none => none

/-- Decoding an encoding consumes exactly its bytes, whatever follows it. -/
@[simp] theorem decode_encode_append (i : Instr) (rest : List Byte) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  simp [decode, encode, Raw.parse_bytes _ (toRaw_wellFormed i)]

@[simp] theorem decode_encode (i : Instr) : decode (encode i) = some (i, (encode i).length) := by
  simpa using decode_encode_append i []

/-- A successful decode consumed the canonical encoding of its result, which
is a prefix of the input. -/
theorem decode_sound {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ n ≤ bytes.length ∧ bytes = encode i ++ bytes.drop n := by
  unfold decode at h
  split at h
  next r rest hp =>
    obtain ⟨j, hj, heq⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hb : bytes = encode j ++ rest := by
      rw [Raw.parse_sound hp, encode, toRaw_of_ofRaw hj]
    have hn : bytes.length - rest.length = (encode j).length := by
      rw [hb, List.length_append]; omega
    refine ⟨hn, by omega, ?_⟩
    rw [hn, hb, List.drop_left]
  next => cases h

theorem decode_eq_some_iff {bytes : List Byte} {i : Instr} {n : Nat} :
    decode bytes = some (i, n) ↔ n = (encode i).length ∧ encode i <+: bytes := by
  constructor
  · intro h
    obtain ⟨hn, -, hb⟩ := decode_sound h
    exact ⟨hn, ⟨_, hb.symm⟩⟩
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

/-- Canonicity: if `decode` succeeds then the input starts with the encoding of
its result, so at most one instruction decodes from any input. -/
theorem decode_unique {bytes : List Byte} {i j : Instr} (hi : encode i <+: bytes)
    (hj : encode j <+: bytes) : i = j := by
  obtain ⟨ri, rfl⟩ := hi
  obtain ⟨rj, hj⟩ := hj
  have h := decode_encode_append i ri
  rw [← hj, decode_encode_append] at h
  exact (Prod.mk.inj (Option.some.inj h)).1.symm

theorem encode_injective : Function.Injective encode := by
  intro i j h
  exact decode_unique (bytes := encode i) (List.prefix_refl _) (h ▸ List.prefix_refl _)

/-- Decoding reads no byte beyond the instruction. -/
theorem decode_append {bytes more : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes ++ more) = some (i, n) := by
  obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
  rw [List.append_assoc, decode_encode_append, hn]

/-- Every proper prefix of an encoding is rejected. -/
theorem decode_take_of_lt (i : Instr) {k : Nat} (hk : k < (encode i).length) :
    decode ((encode i).take k) = none := by
  cases hd : decode ((encode i).take k) with
  | none => rfl
  | some res =>
    obtain ⟨j, n⟩ := res
    obtain ⟨hn, hle, hb⟩ := decode_sound hd
    have hji : j = i := decode_unique (bytes := encode i)
      ⟨_, (by rw [← List.append_assoc, ← hb, List.take_append_drop] :
        encode j ++ (((encode i).take k).drop n ++ (encode i).drop k) = encode i)⟩
      (List.prefix_refl _)
    subst hji
    simp only [List.length_take] at hle
    omega

/-- Encodings are between 3 and 12 bytes long. -/
theorem encode_length_le (i : Instr) : (encode i).length ≤ 12 := Raw.bytes_length_le _

theorem encode_length_ge (i : Instr) : 3 ≤ (encode i).length := Raw.bytes_length_ge _

/-- Every encoding respects the 15-byte architectural instruction-length
limit (SDM Vol. 2A, §2.1). -/
theorem encode_length_le_fifteen (i : Instr) : (encode i).length ≤ 15 := by
  have := encode_length_le i
  omega

/-- The codec as an instance of the shared decoder contract. -/
def byteDecoder : Machine.Decoder Instr where
  decode := decode
  encode := encode
  decode_length_pos h := by
    obtain ⟨rfl, -⟩ := decode_sound h
    have := encode_length_ge ‹_›
    omega
  decode_length_le h := (decode_sound h).2.1
  decode_append extra h := decode_append h
  decode_take {bytes i n} h := by
    obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
    rw [hn, List.take_left]
    simp
  decode_encode_append := decode_encode_append

end Silmaril.X86.Float
