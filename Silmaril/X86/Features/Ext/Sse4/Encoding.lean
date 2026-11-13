module

public import Silmaril.X86.Features.Ext.Sse4.Syntax
public import Silmaril.X86.Ext.Encoding
public import Silmaril.X86.Float.Encoding
public import Silmaril.Machine.Decoder

/-!
# Encoding and decoding of the SSE3/SSSE3/SSE4 lane

Every instruction of the lane is a legacy-SSE encoding (SDM Vol. 2A, §2.1):

`[64] pfx [REX] 0F [38 | 3A] opcode ModRM [SIB] [disp] [imm8]`

with a mandatory prefix `pfx` (`66`, `F2` or `F3`), an optional FS override
for `fs:` operands, a REX prefix when one of its bits is set (or for the byte
registers SPL, BPL, SIL, DIL), and an imm8 exactly in the `0F 3A` map. `Raw`
holds these fields, `parse` reads them (`parse_bytes`), and the ModRM, SIB and
displacement are those of the integer machine (`Ext.pModrm`, `Ext.encodeRM`,
`Ext.decodeRM`), so the memory operands are `Ext.Mem` with RIP-relative,
base-less and `fs:` forms.

The opcode of an instruction is its `Key` (prefix, map, opcode byte, REX.W).
`Family.key` is the opcode table, written from the SDM opcode column of each
instruction page:

| Family | Encoding |
| --- | --- |
| ADDSUBPD/PS, HADDPD/PS, HSUBPD/PS | `66/F2 0F D0`, `66/F2 0F 7C`, `66/F2 0F 7D` |
| MOVDDUP, MOVSLDUP, MOVSHDUP, LDDQU | `F2 0F 12`, `F3 0F 12`, `F3 0F 16`, `F2 0F F0` |
| SSSE3 and SSE4.1 two-operand forms | `66 0F 38 00`-`41` |
| PCMPGTQ | `66 0F 38 37` |
| CRC32 | `F2 [REX.W] 0F 38 F0/F1` |
| `0F 3A` forms | `66 [REX.W] 0F 3A 08`-`63` |

`decode` parses, reads the fields through the table (`ofRaw`) and accepts only
if the input starts with the canonical encoding of the result; `canonical`
turns any such "parse then re-encode" decoder into a `Machine.Decoder`, so the
five decoder laws reduce to the round trip `ofRaw (toRaw i) = some i`.
Non-canonical encodings (a redundant REX or REX.W, a non-minimal
displacement, a segment override other than `fs:` without a base) are
rejected: `none` means outside the model.

`ext_decode_encode` shows that the integer decoder rejects every byte string
starting with an encoding of the lane (all of them start with a prefix and an
opcode the integer machine does not know), which `step_of_ext` needs.
`float_decode_disjoint` shows that `X86.Float`'s decoder and this one never
accept the same bytes.
-/

@[expose] public section

namespace Silmaril.X86.Features.Sse4

open Silmaril.X86 (XReg Reg Byte Prefix OpMap)
open Silmaril.X86.Ext (Rex ModRM SIB Disp ModrmPart RM Mem ByteParser PResult)
open Silmaril.X86.Ext.ByteParser

/-! ## A decoder from a canonical encoder -/

/-- A decoder that reads a candidate and accepts it when the input starts with
its encoding. The laws need only that the candidate of an encoding, with any
continuation, is the encoded instruction. -/
def canonicalDecode {α : Type} (cand : List Byte → Option α) (encode : α → List Byte)
    (bytes : List Byte) : Option (α × Nat) :=
  match cand bytes with
  | some i => if bytes.take (encode i).length = encode i then some (i, (encode i).length) else none
  | none => none

theorem canonicalDecode_sound {α : Type} {cand : List Byte → Option α} {encode : α → List Byte}
    {bytes : List Byte} {i : α} {n : Nat} (h : canonicalDecode cand encode bytes = some (i, n)) :
    n = (encode i).length ∧ bytes = encode i ++ bytes.drop n := by
  unfold canonicalDecode at h
  split at h
  · split at h
    · rename_i j _ ht
      cases h
      refine ⟨rfl, ?_⟩
      conv => lhs; rw [← List.take_append_drop (encode i).length bytes]
      rw [ht]
    · cases h
  · cases h

/-- The decoder laws of a canonical decoder. -/
def canonical {α : Type} (cand : List Byte → Option α) (encode : α → List Byte)
    (pos : ∀ i, 0 < (encode i).length)
    (roundtrip : ∀ i rest, cand (encode i ++ rest) = some i) : Machine.Decoder α where
  decode := canonicalDecode cand encode
  encode := encode
  decode_length_pos h := by
    obtain ⟨rfl, -⟩ := canonicalDecode_sound h
    exact pos _
  decode_length_le h := by
    obtain ⟨rfl, hb⟩ := canonicalDecode_sound h
    rw [hb, List.length_append]; omega
  decode_append extra h := by
    obtain ⟨rfl, hb⟩ := canonicalDecode_sound h
    rw [hb, List.append_assoc]
    simp [canonicalDecode, roundtrip]
  decode_take {bytes i n} h := by
    obtain ⟨rfl, hb⟩ := canonicalDecode_sound h
    rw [hb, List.take_left]
    have h0 := roundtrip i []
    simp only [List.append_nil] at h0
    simp [canonicalDecode, h0]
  decode_encode_append i rest := by
    simp [canonicalDecode, roundtrip]

/-! ## Opcode keys -/

/-- The opcode of an instruction: mandatory prefix, opcode map, opcode byte and
REX.W. -/
structure Key where
  pfx : Prefix
  map : OpMap
  opc : Byte
  w : Bool
  deriving DecidableEq, Repr

/-- `66 0F 38 opc`. -/
def k38 (opc : Byte) : Key := ⟨.p66, .m0F38, opc, false⟩

/-- `66 0F 3A opc`. -/
def k3A (opc : Byte) (w : Bool := false) : Key := ⟨.p66, .m0F3A, opc, w⟩

/-- The SDM opcode of each two-operand form. -/
def Op2.key : Op2 → Key
  | .addsubpd => ⟨.p66, .m0F, 0xD0, false⟩
  | .addsubps => ⟨.pF2, .m0F, 0xD0, false⟩
  | .haddpd => ⟨.p66, .m0F, 0x7C, false⟩
  | .haddps => ⟨.pF2, .m0F, 0x7C, false⟩
  | .hsubpd => ⟨.p66, .m0F, 0x7D, false⟩
  | .hsubps => ⟨.pF2, .m0F, 0x7D, false⟩
  | .movddup => ⟨.pF2, .m0F, 0x12, false⟩
  | .movshdup => ⟨.pF3, .m0F, 0x16, false⟩
  | .movsldup => ⟨.pF3, .m0F, 0x12, false⟩
  | .lddqu => ⟨.pF2, .m0F, 0xF0, false⟩
  | .pshufb => k38 0x00
  | .phaddw => k38 0x01
  | .phaddd => k38 0x02
  | .phaddsw => k38 0x03
  | .pmaddubsw => k38 0x04
  | .phsubw => k38 0x05
  | .phsubd => k38 0x06
  | .phsubsw => k38 0x07
  | .psignb => k38 0x08
  | .psignw => k38 0x09
  | .psignd => k38 0x0A
  | .pmulhrsw => k38 0x0B
  | .pblendvb => k38 0x10
  | .blendvps => k38 0x14
  | .blendvpd => k38 0x15
  | .ptest => k38 0x17
  | .pabsb => k38 0x1C
  | .pabsw => k38 0x1D
  | .pabsd => k38 0x1E
  | .pmovsxbw => k38 0x20
  | .pmovsxbd => k38 0x21
  | .pmovsxbq => k38 0x22
  | .pmovsxwd => k38 0x23
  | .pmovsxwq => k38 0x24
  | .pmovsxdq => k38 0x25
  | .pmuldq => k38 0x28
  | .pcmpeqq => k38 0x29
  | .movntdqa => k38 0x2A
  | .packusdw => k38 0x2B
  | .pmovzxbw => k38 0x30
  | .pmovzxbd => k38 0x31
  | .pmovzxbq => k38 0x32
  | .pmovzxwd => k38 0x33
  | .pmovzxwq => k38 0x34
  | .pmovzxdq => k38 0x35
  | .pcmpgtq => k38 0x37
  | .pminsb => k38 0x38
  | .pminsd => k38 0x39
  | .pminuw => k38 0x3A
  | .pminud => k38 0x3B
  | .pmaxsb => k38 0x3C
  | .pmaxsd => k38 0x3D
  | .pmaxuw => k38 0x3E
  | .pmaxud => k38 0x3F
  | .pmulld => k38 0x40
  | .phminposuw => k38 0x41

def OpI.key : OpI → Key
  | .roundps => k3A 0x08
  | .roundpd => k3A 0x09
  | .blendps => k3A 0x0C
  | .blendpd => k3A 0x0D
  | .pblendw => k3A 0x0E
  | .palignr => k3A 0x0F
  | .insertps => k3A 0x21
  | .dpps => k3A 0x40
  | .dppd => k3A 0x41
  | .mpsadbw => k3A 0x42
  | .pcmpestrm => k3A 0x60
  | .pcmpestri => k3A 0x61
  | .pcmpistrm => k3A 0x62
  | .pcmpistri => k3A 0x63
  | .pcmpestrm64 => k3A 0x60 true
  | .pcmpestri64 => k3A 0x61 true

def ExtrOp.key : ExtrOp → Key
  | .pextrb => k3A 0x14
  | .pextrw => k3A 0x15
  | .pextrd => k3A 0x16
  | .pextrq => k3A 0x16 true
  | .extractps => k3A 0x17

def InsOp.key : InsOp → Key
  | .pinsrb => k3A 0x20
  | .pinsrd => k3A 0x22
  | .pinsrq => k3A 0x22 true

def CrcSz.key : CrcSz → Key
  | .b => ⟨.pF2, .m0F38, 0xF0, false⟩
  | .bq => ⟨.pF2, .m0F38, 0xF0, true⟩
  | .d => ⟨.pF2, .m0F38, 0xF1, false⟩
  | .q => ⟨.pF2, .m0F38, 0xF1, true⟩

/-- The opcode families: one per key. -/
inductive Family where
  | op2 (o : Op2)
  | opI (o : OpI)
  | extr (o : ExtrOp)
  | ins (o : InsOp)
  | crc (s : CrcSz)
  deriving DecidableEq, Repr

def Family.key : Family → Key
  | .op2 o => o.key
  | .opI o => o.key
  | .extr o => o.key
  | .ins o => o.key
  | .crc s => s.key

def Op2.all : List Op2 :=
  [.addsubpd, .addsubps, .haddpd, .haddps, .hsubpd, .hsubps, .movddup, .movshdup, .movsldup,
    .lddqu, .pshufb, .phaddw, .phaddd, .phaddsw, .pmaddubsw, .phsubw, .phsubd, .phsubsw,
    .psignb, .psignw, .psignd, .pmulhrsw, .pblendvb, .blendvps, .blendvpd, .ptest, .pabsb,
    .pabsw, .pabsd, .pmovsxbw, .pmovsxbd, .pmovsxbq, .pmovsxwd, .pmovsxwq, .pmovsxdq,
    .pmuldq, .pcmpeqq, .movntdqa, .packusdw, .pmovzxbw, .pmovzxbd, .pmovzxbq, .pmovzxwd,
    .pmovzxwq, .pmovzxdq, .pcmpgtq, .pminsb, .pminsd, .pminuw, .pminud, .pmaxsb, .pmaxsd,
    .pmaxuw, .pmaxud, .pmulld, .phminposuw]

def OpI.all : List OpI :=
  [.roundps, .roundpd, .blendps, .blendpd, .pblendw, .palignr, .insertps, .dpps, .dppd,
    .mpsadbw, .pcmpestrm, .pcmpestri, .pcmpistrm, .pcmpistri, .pcmpestrm64, .pcmpestri64]

def ExtrOp.all : List ExtrOp := [.pextrb, .pextrw, .pextrd, .pextrq, .extractps]

def InsOp.all : List InsOp := [.pinsrb, .pinsrd, .pinsrq]

def CrcSz.all : List CrcSz := [.b, .bq, .d, .q]

def Family.all : List Family :=
  Op2.all.map .op2 ++ OpI.all.map .opI ++ ExtrOp.all.map .extr ++ InsOp.all.map .ins ++
    CrcSz.all.map .crc

theorem Family.mem_all (f : Family) : f ∈ Family.all := by
  cases f <;> rename_i o <;> cases o <;> decide

/-- The family with a given key. -/
def lookup (k : Key) : Option Family := Family.all.find? fun f => f.key == k

theorem lookup_key (f : Family) : lookup f.key = some f := by
  cases f <;> rename_i o <;> cases o <;> rfl

theorem lookup_eq_some {k : Key} {f : Family} (h : lookup k = some f) : f.key = k := by
  have := List.find?_some h
  simpa using this

/-- Facts about the table, checked on every entry: no opcode of the `0F` map is
an escape byte, the `0F 3A` map is exactly the one with an immediate, and
every key has a mandatory prefix. -/
def Family.wellFormed (f : Family) : Bool :=
  (f.key.map != .m0F || (f.key.opc != 0x38#8 && f.key.opc != 0x3A#8)) &&
    f.key.pfx != .none &&
    (match f with
      | .op2 _ | .crc _ => f.key.map != .m0F3A
      | _ => f.key.map == .m0F3A)

theorem Family.wellFormed_all : ∀ f ∈ Family.all, f.wellFormed = true := by decide

theorem Family.wellFormed_eq (f : Family) : f.wellFormed = true :=
  wellFormed_all f (mem_all f)

/-! ## Register fields -/

/-- REX.R/REX.B of an XMM register number. -/
def xHi (x : XReg) : Bool := x.toBitVec.getLsbD 3

/-- The three-bit ModRM field of an XMM register number. -/
def xLo (x : XReg) : BitVec 3 := x.toBitVec.extractLsb' 0 3

def mkX (hi : Bool) (lo : BitVec 3) : XReg := XReg.ofBitVec (BitVec.ofBool hi ++ lo)

@[simp] theorem mkX_xHi_xLo (x : XReg) : mkX (xHi x) (xLo x) = x := by cases x <;> rfl

/-- An `xmm/m` operand as an integer-machine `r/m` operand (same encoding). -/
def Src.toRM : Src → RM
  | .reg r => .reg (Reg.ofBitVec r.toBitVec)
  | .mem m => .mem m

def Src.ofRM : RM → Src
  | .reg r => .reg (XReg.ofBitVec r.toBitVec)
  | .mem m => .mem m

@[simp] theorem Src.ofRM_toRM (s : Src) : Src.ofRM s.toRM = s := by
  cases s <;> simp [Src.toRM, Src.ofRM]

/-! ## Raw fields -/

/-- The fields of one legacy-SSE encoding. -/
structure Raw where
  fs : Bool
  pfx : Prefix
  rex : Option Rex
  map : OpMap
  opc : Byte
  modrm : ModrmPart
  imm : Option Byte

/-- The bytes of the fields. -/
def Raw.bytes (r : Raw) : List Byte :=
  Ext.segBytes r.fs ++ (r.pfx.bytes ++ (Ext.rexBytes r.rex ++ (0x0F#8 :: (r.map.bytes ++
    (r.opc :: (Ext.modrmBytes (some r.modrm) ++ r.imm.toList))))))

theorem Raw.bytes_length_pos (r : Raw) : 0 < r.bytes.length := by
  simp [Raw.bytes]; omega

/-- The fields before the ModRM byte. -/
structure Head where
  fs : Bool
  pfx : Prefix
  rex : Option Rex
  map : OpMap
  opc : Byte

/-- The FS override. -/
def pSeg (b : Byte) : ByteParser (Bool × Byte) :=
  if b = 0x64#8 then map (fun c => (true, c)) byte else pure (false, b)

/-- A mandatory prefix. -/
def pPrefix (b : Byte) : ByteParser (Prefix × Byte) :=
  if b = 0x66#8 then map (fun c => (.p66, c)) byte
  else if b = 0xF2#8 then map (fun c => (.pF2, c)) byte
  else if b = 0xF3#8 then map (fun c => (.pF3, c)) byte
  else pure (.none, b)

/-- The opcode map after `0F`, and the opcode. -/
def pMap : ByteParser (OpMap × Byte) :=
  bind byte fun b =>
    if b = 0x38#8 then map (fun c => (.m0F38, c)) byte
    else if b = 0x3A#8 then map (fun c => (.m0F3A, c)) byte
    else pure (.m0F, b)

def pHead : ByteParser Head :=
  bind byte fun b0 =>
  bind (pSeg b0) fun sb =>
  bind (pPrefix sb.2) fun pb =>
  bind (Ext.pRex pb.2) fun rb =>
    if rb.2 = 0x0F#8 then map (fun mo => ⟨sb.1, pb.1, rb.1, mo.1, mo.2⟩) pMap else fail

def pImm8 (has : Bool) : ByteParser (Option Byte) :=
  if has then map some byte else pure none

/-- Read the fields of one instruction. -/
def parse : ByteParser Raw :=
  bind pHead fun h =>
  bind (Ext.pModrm true) fun mp =>
  match mp with
  | some part => map (fun imm => ⟨h.fs, h.pfx, h.rex, h.map, h.opc, part, imm⟩)
      (pImm8 (h.map == .m0F3A))
  | none => fail

private theorem Rex.byte_ne_F2 (x : Rex) : x.byte ≠ 0xF2#8 := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

private theorem Rex.byte_ne_0F (x : Rex) : x.byte ≠ 0x0F#8 := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

theorem pMap_bytes (m : OpMap) (opc : Byte) (h : m = .m0F → opc ≠ 0x38#8 ∧ opc ≠ 0x3A#8)
    (rest : List Byte) : pMap (m.bytes ++ opc :: rest) = .ok (m, opc) rest := by
  cases m <;> simp_all [pMap, OpMap.bytes, ByteParser.bind, ByteParser.map]

/-- The head is read back from its bytes. -/
theorem pHead_bytes (fs : Bool) (pfx : Prefix) (rex : Option Rex) (m : OpMap) (opc : Byte)
    (h : m = .m0F → opc ≠ 0x38#8 ∧ opc ≠ 0x3A#8) (rest : List Byte) :
    pHead (Ext.segBytes fs ++ (pfx.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 :: (m.bytes ++
      (opc :: rest)))))) = .ok ⟨fs, pfx, rex, m, opc⟩ rest := by
  have hm := pMap_bytes m opc h rest
  have h1 := Rex.byte_ne_F2
  have h2 := Rex.byte_ne_0F
  have h3 := Ext.Rex.byte_ne_66
  have h4 := Ext.Rex.byte_ne_F3
  have h5 := Ext.Rex.byte_ne_64
  cases fs <;> cases pfx <;> cases rex <;>
    simp_all [pHead, pSeg, pPrefix, Ext.pRex, Ext.segBytes, Prefix.bytes, Ext.rexBytes,
      ByteParser.bind, ByteParser.map]

theorem pImm8_bytes (imm : Option Byte) (rest : List Byte) :
    pImm8 imm.isSome (imm.toList ++ rest) = .ok imm rest := by
  cases imm <;> rfl

/-- The side conditions under which `parse` reads the fields back. -/
structure Raw.WF (r : Raw) : Prop where
  modrm : Ext.ModrmOk true (some r.modrm)
  esc : r.map = .m0F → r.opc ≠ 0x38#8 ∧ r.opc ≠ 0x3A#8
  imm : r.imm.isSome = (r.map == .m0F3A)

theorem parse_bytes {r : Raw} (wf : r.WF) (rest : List Byte) :
    parse (r.bytes ++ rest) = .ok r rest := by
  obtain ⟨fs, pfx, rex, m, opc, part, imm⟩ := r
  obtain ⟨hm, he, hi⟩ := wf
  simp only [Raw.bytes, List.append_assoc, List.cons_append]
  unfold parse
  rw [bind_ok (pHead_bytes fs pfx rex m opc he _)]
  rw [bind_ok (Ext.pModrm_bytes hm _)]
  simp only
  rw [← hi, map_ok (pImm8_bytes imm rest)]

/-! ## The canonical encoding -/

def Instr.family : Instr → Family
  | .rr op .. => .op2 op
  | .ri op .. => .opI op
  | .extr op .. => .extr op
  | .ins op .. => .ins op
  | .crc32 sz .. => .crc sz

/-- CRC32 with a byte register source SPL, BPL, SIL or DIL needs a REX prefix. -/
def forceRex : CrcSz → RM → Bool
  | .b, .reg r | .bq, .reg r => Ext.needsRexByte r
  | _, _ => false

/-- The ModRM `reg` field (with REX.R), the `r/m` operand, whether a REX prefix
is required, and the immediate. -/
def Instr.operands : Instr → Bool × BitVec 3 × RM × Bool × Option Byte
  | .rr _ dst src => (xHi dst, xLo dst, src.toRM, false, none)
  | .ri _ dst src imm => (xHi dst, xLo dst, src.toRM, false, some imm)
  | .extr _ dst src imm => (xHi src, xLo src, dst, false, some imm)
  | .ins _ dst src imm => (xHi dst, xLo dst, src, false, some imm)
  | .crc32 sz dst src => (Ext.hiBit dst, dst.lo, src, forceRex sz src, none)

def toRaw (i : Instr) : Raw :=
  let k := i.family.key
  let o := i.operands
  let e := Ext.encodeRM o.2.2.1
  { fs := o.2.2.1.isFs, pfx := k.pfx, rex := Ext.mkRex k.w o.1 e.x e.b o.2.2.2.1, map := k.map,
    opc := k.opc, modrm := (⟨e.mod, o.2.1, e.rm⟩, e.sib, e.disp), imm := o.2.2.2.2 }

/-- The instruction of a family with these operand fields. -/
def Family.build : Family → Bool → BitVec 3 → RM → Byte → Instr
  | .op2 o, hi, lo, rm, _ => .rr o (mkX hi lo) (Src.ofRM rm)
  | .opI o, hi, lo, rm, imm => .ri o (mkX hi lo) (Src.ofRM rm) imm
  | .extr o, hi, lo, rm, imm => .extr o rm (mkX hi lo) imm
  | .ins o, hi, lo, rm, imm => .ins o (mkX hi lo) rm imm
  | .crc s, hi, lo, rm, _ => .crc32 s (Ext.mkReg hi lo) rm

/-- The meaning of the fields, if their key is in the table. -/
def ofRaw (r : Raw) : Option Instr :=
  let rex := r.rex.getD Rex.zero
  (lookup ⟨r.pfx, r.map, r.opc, rex.w⟩).map fun f =>
    f.build rex.r r.modrm.1.reg
      (Ext.decodeRM r.fs rex.x rex.b r.modrm.1 r.modrm.2.1 r.modrm.2.2) (r.imm.getD 0)

theorem ofRaw_toRaw (i : Instr) : ofRaw (toRaw i) = some i := by
  have hd := Ext.decodeRM_encodeRM i.operands.2.2.1 i.operands.2.1
  simp only [ofRaw, toRaw, Ext.mkRex_getD]
  have hk : (⟨i.family.key.pfx, i.family.key.map, i.family.key.opc, i.family.key.w⟩ : Key) =
      i.family.key := rfl
  rw [hk, lookup_key, hd]
  cases i <;> simp [Instr.family, Instr.operands, Family.build]

private theorem family_imm (i : Instr) :
    i.operands.2.2.2.2.isSome = (i.family.key.map == .m0F3A) := by
  have h := Family.wellFormed_eq i.family
  cases i <;> simp_all [Instr.family, Instr.operands, Family.wellFormed]

theorem toRaw_wf (i : Instr) : (toRaw i).WF := by
  have h := Family.wellFormed_eq i.family
  refine ⟨Ext.encodeRM_ok _ _, ?_, family_imm i⟩
  intro hm
  simp only [Family.wellFormed, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1 | h1, -⟩, -⟩ := h
  · exact absurd hm h1
  · simpa [toRaw] using h1

/-- The canonical encoding: the assembler's form. -/
def encode (i : Instr) : List Byte := (toRaw i).bytes

/-- The candidate instruction at the front of the bytes. -/
def candidate (bytes : List Byte) : Option Instr :=
  match parse bytes with
  | .ok r _ => ofRaw r
  | _ => none

theorem candidate_encode (i : Instr) (rest : List Byte) : candidate (encode i ++ rest) = some i := by
  simp [candidate, encode, parse_bytes (toRaw_wf i), ofRaw_toRaw]

/-- The decoder of the lane. -/
def decoder : Machine.Decoder Instr :=
  canonical candidate encode (fun _ => Raw.bytes_length_pos _) candidate_encode

theorem decode_eq : decoder.decode = canonicalDecode candidate encode := rfl

@[simp] theorem decode_encode_append (i : Instr) (rest : List Byte) :
    decoder.decode (encode i ++ rest) = some (i, (encode i).length) :=
  decoder.decode_encode_append i rest

theorem decode_sound {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decoder.decode bytes = some (i, n)) :
    n = (encode i).length ∧ bytes = encode i ++ bytes.drop n :=
  canonicalDecode_sound h

/-! ## The integer decoder rejects the lane -/

/-- The integer machine's length decoder has no layout for the opcode after any
of the lane's prefixes: `66 0F 38/3A/7C/7D/D0`, `F3 0F 12/16` and `F2` are
unknown to `Ext.shape`. -/
def extRejects (k : Key) : Bool :=
  match k.pfx with
  | .none => false
  | .pF2 => true
  | .p66 => (Ext.shape .opsize false (.two (k.map.bytes.headD k.opc))).isNone &&
      (Ext.shape .opsize true (.two (k.map.bytes.headD k.opc))).isNone
  | .pF3 => (Ext.shape .rep false (.two (k.map.bytes.headD k.opc))).isNone &&
      (Ext.shape .rep true (.two (k.map.bytes.headD k.opc))).isNone

theorem extRejects_all : ∀ f ∈ Family.all, extRejects f.key = true := by decide

private theorem opcOk_two (b : Byte) : Ext.OpcOk (.two b) := trivial

private theorem opcOk_F2 : Ext.OpcOk (.one 0xF2#8) := by
  simp only [Ext.OpcOk]; decide

private theorem shape_none {p : Ext.Pfx} {b : Byte}
    (h : ((Ext.shape p false (.two b)).isNone && (Ext.shape p true (.two b)).isNone) = true)
    (w : Bool) : Ext.shape p w (.two b) = none := by
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  cases w
  · exact h.1
  · exact h.2

/-- The integer length decoder rejects every byte string that starts with a
head of the lane. -/
theorem ext_parseRaw_head (fs : Bool) (k : Key) (hk : extRejects k = true) (rex : Option Rex)
    (tail : List Byte) :
    Ext.parseRaw (Ext.segBytes fs ++ (k.pfx.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 :: (k.map.bytes ++
      (k.opc :: tail)))))) = .bad := by
  obtain ⟨pfx, m, opc, w⟩ := k
  simp only [extRejects] at hk
  unfold Ext.parseRaw
  cases pfx with
  | none => cases hk
  | pF2 =>
    have hh := Ext.pHead_bytes fs .none none opcOk_F2
      (Ext.rexBytes rex ++ (0x0F#8 :: (m.bytes ++ (opc :: tail))))
    have e : Ext.segBytes fs ++ (Prefix.pF2.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 :: (m.bytes ++
        (opc :: tail))))) = Ext.segBytes fs ++ Ext.Pfx.none.bytes ++ Ext.rexBytes none ++
        (Ext.Opc.one 0xF2#8).bytes ++ (Ext.rexBytes rex ++ (0x0F#8 :: (m.bytes ++ (opc :: tail)))) := by
      simp [Prefix.bytes, Ext.Pfx.bytes, Ext.rexBytes, Ext.Opc.bytes]
    rw [e, bind_ok hh]
    rfl
  | p66 =>
    cases m with
    | m0F =>
      have hh := Ext.pHead_bytes fs .opsize rex (opcOk_two opc) tail
      have e : Ext.segBytes fs ++ (Prefix.p66.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 ::
          (OpMap.m0F.bytes ++ (opc :: tail))))) = Ext.segBytes fs ++ Ext.Pfx.opsize.bytes ++
          Ext.rexBytes rex ++ (Ext.Opc.two opc).bytes ++ tail := by
        simp [Prefix.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, OpMap.bytes]
      rw [e, bind_ok hh]
      simp only [OpMap.bytes, List.headD] at hk
      simp only [shape_none hk]
      rfl
    | m0F38 =>
      have hh := Ext.pHead_bytes fs .opsize rex (opcOk_two 0x38#8) (opc :: tail)
      have e : Ext.segBytes fs ++ (Prefix.p66.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 ::
          (OpMap.m0F38.bytes ++ (opc :: tail))))) = Ext.segBytes fs ++ Ext.Pfx.opsize.bytes ++
          Ext.rexBytes rex ++ (Ext.Opc.two 0x38#8).bytes ++ (opc :: tail) := by
        simp [Prefix.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, OpMap.bytes]
      rw [e, bind_ok hh]
      simp only [OpMap.bytes, List.headD] at hk
      simp only [shape_none hk]
      rfl
    | m0F3A =>
      have hh := Ext.pHead_bytes fs .opsize rex (opcOk_two 0x3A#8) (opc :: tail)
      have e : Ext.segBytes fs ++ (Prefix.p66.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 ::
          (OpMap.m0F3A.bytes ++ (opc :: tail))))) = Ext.segBytes fs ++ Ext.Pfx.opsize.bytes ++
          Ext.rexBytes rex ++ (Ext.Opc.two 0x3A#8).bytes ++ (opc :: tail) := by
        simp [Prefix.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, OpMap.bytes]
      rw [e, bind_ok hh]
      simp only [OpMap.bytes, List.headD] at hk
      simp only [shape_none hk]
      rfl
  | pF3 =>
    cases m with
    | m0F =>
      have hh := Ext.pHead_bytes fs .rep rex (opcOk_two opc) tail
      have e : Ext.segBytes fs ++ (Prefix.pF3.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 ::
          (OpMap.m0F.bytes ++ (opc :: tail))))) = Ext.segBytes fs ++ Ext.Pfx.rep.bytes ++
          Ext.rexBytes rex ++ (Ext.Opc.two opc).bytes ++ tail := by
        simp [Prefix.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, OpMap.bytes]
      rw [e, bind_ok hh]
      simp only [OpMap.bytes, List.headD] at hk
      simp only [shape_none hk]
      rfl
    | m0F38 =>
      have hh := Ext.pHead_bytes fs .rep rex (opcOk_two 0x38#8) (opc :: tail)
      have e : Ext.segBytes fs ++ (Prefix.pF3.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 ::
          (OpMap.m0F38.bytes ++ (opc :: tail))))) = Ext.segBytes fs ++ Ext.Pfx.rep.bytes ++
          Ext.rexBytes rex ++ (Ext.Opc.two 0x38#8).bytes ++ (opc :: tail) := by
        simp [Prefix.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, OpMap.bytes]
      rw [e, bind_ok hh]
      simp only [OpMap.bytes, List.headD] at hk
      simp only [shape_none hk]
      rfl
    | m0F3A =>
      have hh := Ext.pHead_bytes fs .rep rex (opcOk_two 0x3A#8) (opc :: tail)
      have e : Ext.segBytes fs ++ (Prefix.pF3.bytes ++ (Ext.rexBytes rex ++ (0x0F#8 ::
          (OpMap.m0F3A.bytes ++ (opc :: tail))))) = Ext.segBytes fs ++ Ext.Pfx.rep.bytes ++
          Ext.rexBytes rex ++ (Ext.Opc.two 0x3A#8).bytes ++ (opc :: tail) := by
        simp [Prefix.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, OpMap.bytes]
      rw [e, bind_ok hh]
      simp only [OpMap.bytes, List.headD] at hk
      simp only [shape_none hk]
      rfl

/-- `Ext.parseRaw` rejects every byte string starting with an encoding of the
lane. -/
theorem ext_parseRaw_encode (i : Instr) (more : List Byte) :
    Ext.parseRaw (encode i ++ more) = .bad := by
  simp only [encode, toRaw, Raw.bytes, List.append_assoc, List.cons_append]
  exact ext_parseRaw_head _ _ (extRejects_all i.family (Family.mem_all _)) _ _

/-- The integer decoder rejects every byte string starting with an encoding of
the lane. -/
theorem ext_decode_encode (i : Instr) (more : List Byte) :
    Ext.decode (encode i ++ more) = none := by
  unfold Ext.decode
  rw [ext_parseRaw_encode]

/-! ## Disjointness from the scalar SSE decoder -/

theorem parse_head {bytes : List Byte} {h : Head} {tail : List Byte}
    (hh : pHead bytes = .ok h tail) {r : Raw} {rest : List Byte} (hp : parse bytes = .ok r rest) :
    r.pfx = h.pfx ∧ r.map = h.map ∧ r.opc = h.opc := by
  unfold parse at hp
  rw [bind_ok hh] at hp
  simp only [ByteParser.bind] at hp
  split at hp
  · rename_i mp rest' _
    cases mp with
    | none => simp at hp
    | some part =>
      simp only [ByteParser.map, ByteParser.bind] at hp
      split at hp <;> simp_all
      obtain ⟨rfl, -⟩ := hp
      exact ⟨rfl, rfl, rfl⟩
  · cases hp
  · cases hp

/-- The key of a scalar SSE instruction is not in the lane's table. -/
private theorem lookup_float (i : Float.Instr) (w : Bool) :
    lookup ⟨(Float.toRaw i).pfx, (Float.toRaw i).map, (Float.toRaw i).opc, w⟩ = none := by
  cases i <;> (try cases ‹Float.Precision›) <;> (try cases ‹Float.ArithOp›) <;>
    (try cases ‹Float.LogicOp›) <;> cases w <;> rfl

theorem float_rexBytes (n : BitVec 4) :
    X86.rexBytes n = Ext.rexBytes (if n = 0#4 then none else some (Rex.ofByte (X86.rexByte n))) := by
  unfold X86.rexBytes
  split
  · rfl
  · simp only [Ext.rexBytes, List.cons.injEq, and_true]
    revert n; decide

/-- `X86.Float`'s scalar SSE decoder and this one never accept the same bytes. -/
theorem float_decode_disjoint (bytes : List Byte) :
    Float.decode bytes = none ∨ decoder.decode bytes = none := by
  cases hf : Float.decode bytes with
  | none => exact .inl rfl
  | some res =>
    right
    obtain ⟨i, n⟩ := res
    obtain ⟨-, -, hb⟩ := Float.decode_sound hf
    have wf := Float.toRaw_wellFormed i
    have hh := pHead_bytes false (Float.toRaw i).pfx
      (if (Float.toRaw i).rex = 0#4 then none else some (Rex.ofByte (X86.rexByte (Float.toRaw i).rex)))
      (Float.toRaw i).map (Float.toRaw i).opc wf.not_escape
      (((Float.toRaw i).rm.bytes (X86.nibbleLo (Float.toRaw i).reg) ++ (Float.toRaw i).imm.toList) ++
        bytes.drop n)
    rw [← float_rexBytes] at hh
    have hbytes : bytes = Ext.segBytes false ++ ((Float.toRaw i).pfx.bytes ++
        (X86.rexBytes (Float.toRaw i).rex ++ (0x0F#8 :: ((Float.toRaw i).map.bytes ++
          ((Float.toRaw i).opc :: (((Float.toRaw i).rm.bytes (X86.nibbleLo (Float.toRaw i).reg) ++
            (Float.toRaw i).imm.toList) ++ bytes.drop n)))))) := by
      conv_lhs => rw [hb]
      simp [Float.encode, X86.Raw.bytes, Ext.segBytes]
    rw [← hbytes] at hh
    simp only [decode_eq, canonicalDecode, candidate]
    cases hp : parse bytes with
    | ok r rest =>
      obtain ⟨h1, h2, h3⟩ := parse_head hh hp
      simp only [ofRaw, h1, h2, h3, lookup_float, Option.map_none]
    | eof => rfl
    | bad => rfl

end Silmaril.X86.Features.Sse4
