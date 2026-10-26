module

public import Silmaril.X86.Ext.Encoding

/-!
# Byte-faithful instructions for the local x86 model

This codec retains consumed bytes, including redundant REX, the inert DS
prefix (`3E`) in long mode, alternate MOV direction and displacement widths.
It models no CET, shadow stack, high-byte registers or additional segmentation.
The canonical `Ext.decode` and its round-trip theorems remain unchanged.
-/

@[expose] public section

namespace Silmaril.X86.Ext.Wire

open Silmaril.X86 (Byte Reg)
open ByteParser

/-- Additional semantic operations used by the original Jitawa image. -/
inductive Instr where
  | canonical (i : Ext.Instr)
  | callRM (target : RM)
  | jmpRM (target : RM)
  | cmov (sz : Sz) (c : Cond) (dst : Reg) (src : RM)
  /-- Register exchange only. Memory XCHG's implicit atomicity is excluded. -/
  | xchg (sz : Sz) (dst src : Reg)
  | mul (sz : Sz) (src : RM)
  | cmp8 (dst : Reg) (src : RM)
  | testI (sz : Sz) (dst : RM) (imm : BitVec 32)
  | cpuid
  deriving DecidableEq, Repr

/-- Parsed fields plus the inert long-mode DS prefix. -/
structure Raw where
  ds : Bool
  fields : Ext.Raw
  deriving DecidableEq, Repr

def Raw.bytes (r : Raw) : List Byte :=
  (if r.ds then [0x3E#8] else []) ++ r.fields.bytes

/-- Existing shapes take priority; new shapes have no operand-size/REP prefix. -/
def shape (pfx : Pfx) (w : Bool) (opc : Opc) : Option Shape :=
  match Ext.shape pfx w opc with
  | some sh => some sh
  | none =>
    if pfx = .none then
      match opc with
      | .one b => if b = 0x87#8 ∨ b = 0x3A#8 then some ⟨true, .none⟩ else none
      | .two b => if b = 0xA2#8 then some ⟨false, .none⟩ else none
    else none

/-- One optional DS override before the existing supported prefix sequence. -/
def pHead : ByteParser (Bool × Bool × Pfx × Option Rex × Opc) :=
  bind byte fun b =>
    if b = 0x3E#8 then map (true, ·) Ext.pHead
    else map (false, ·) (if b = 0x64#8 then pHead0 true else pAfterSeg false b)

/-- Group F7 /0 TEST carries imm32; the older canonical subset has no such form. -/
def immKind (opc : Opc) (mp : Option ModrmPart) (fallback : ImmKind) : ImmKind :=
  match opc, mp with
  | .one b, some (m, _, _) => if b = 0xF7#8 ∧ m.reg = 0#3 then .i32 else fallback
  | _, _ => fallback

/-- Consume the actual byte layout; do not compute a canonical encoded length. -/
def parseRaw : ByteParser Raw :=
  bind pHead fun h =>
  match shape h.2.2.1 (h.2.2.2.1.getD Rex.zero).w h.2.2.2.2 with
  | none => fail
  | some sh =>
    bind (pModrm sh.modrm) fun mp =>
      map (fun imm => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, mp, imm⟩) (pImm (immKind h.2.2.2.2 mp sh.imm))

theorem good_pHead : Good pHead := by
  apply good_bind good_byte
  intro b
  split
  · exact good_map _ Ext.good_pHead
  · apply good_map
    split
    · exact good_pHead0 _
    · exact good_pAfterSeg _ _

theorem good_parseRaw : Good parseRaw := by
  apply good_bind good_pHead
  intro h
  split
  · exact good_fail
  · exact good_bind (good_pModrm _) fun _ => good_map _ (good_pImm _)

/-- Reject legacy high-byte register fields in instructions using bytes. -/
def byteFieldsOk (r : Ext.Raw) (m : ModRM) : Bool :=
  r.rex.isSome ||
    (if r.opc = .one 0x84 ∨ r.opc = .one 0x88 ∨ r.opc = .one 0x8A ∨ r.opc = .one 0x3A then
       decide (m.reg < 4#3) && (m.mod != 3#2 || decide (m.rm < 4#3))
     else if (r.opc == .one 0x80) || (r.opc == .one 0xC6) || (r.opc == .one 0xF6) ||
         (match r.opc with
          | .two b => decide (b.extractLsb' 4 4 = 9#4 ∨ b = 0xB6#8 ∨ b = 0xBE#8)
          | _ => false) then
       m.mod != 3#2 || decide (m.rm < 4#3)
     else true)

/-- Assign meaning while checking constraints previously enforced by canonical
re-encoding. Unsupported group digits and FS base-register forms are rejected. -/
def ofRaw (raw : Raw) : Option Instr :=
  let r := raw.fields
  let rex := r.rex.getD Rex.zero
  match r.modrm with
  | none =>
    if r.fs then none
    else if r.opc = .one 0x90 ∧ rex.b then none
    else if r.opc = .two 0xA2 then some .cpuid
    else (Ext.ofRaw r).map .canonical
  | some (m, sib, d) =>
    let op := decodeRM r.fs rex.x rex.b m sib d
    if !byteFieldsOk r m then none
    else if r.fs && (match op with | .mem a => a.base != .fs | _ => true) then none
    else if r.opc = .one 0xC7 ∧ m.reg ≠ 0#3 then none
    else if r.opc = .one 0x63 ∧ !rex.w then none
    else
      match Ext.ofRaw r with
      | some i => some (.canonical i)
      | none =>
        if r.pfx ≠ .none then none
        else if r.opc = .one 0xFF then
          if m.reg = 2#3 then some (.callRM op)
          else if m.reg = 4#3 then some (.jmpRM op) else none
        else if r.opc = .one 0x8B then
          match op with
          | .reg src => some (.canonical (.mov (Sz.ofW rex.w) (.reg (mkReg rex.r m.reg)) src))
          | _ => none
        else if r.opc = .one 0x87 then
          match op with
          | .reg dst => some (.xchg (Sz.ofW rex.w) dst (mkReg rex.r m.reg))
          | _ => none
        else if r.opc = .one 0xF7 then
          if m.reg = 0#3 then
            match r.imm with
            | .i32 v => some (.testI (Sz.ofW rex.w) op v)
            | _ => none
          else none
        else if r.opc = .one 0x3A then some (.cmp8 (mkReg rex.r m.reg) op)
        else none

/-- The semantic instruction and its exact consumed spelling. -/
structure Decoded where
  instr : Instr
  bytes : List Byte
  deriving DecidableEq, Repr

def Decoded.length (d : Decoded) : Nat := d.bytes.length

/-- Re-encode a decoded instruction without changing its spelling. -/
def encode (d : Decoded) : List Byte := d.bytes

/-- Decode with exact spelling and an explicit 1..15 byte bound. Canonical
encodings use the original codec; all other accepted encodings use raw fields. -/
def decodeCandidate (bytes : List Byte) : Option Decoded :=
  match Ext.decode bytes with
  | some (i, n) => some ⟨.canonical i, bytes.take n⟩
  | none =>
    match parseRaw bytes with
    | .ok raw _ =>
      match ofRaw raw with
      | some i =>
        if 0 < raw.bytes.length ∧ raw.bytes.length ≤ 15 ∧ bytes.take raw.bytes.length = raw.bytes
        then some ⟨i, raw.bytes⟩ else none
      | none => none
    | _ => none

/-- Accept only candidates that the codec also decodes from their retained
bytes alone. This checked invariant makes the lossless round trip explicit. -/
def decode (bytes : List Byte) : Option Decoded :=
  match decodeCandidate bytes with
  | none => none
  | some d => if decodeCandidate (encode d) = some d then some d else none

@[simp] theorem decodeCandidate_canonical_append (i : Ext.Instr) (rest : List Byte) :
    decodeCandidate (Ext.encode i ++ rest) = some ⟨.canonical i, Ext.encode i⟩ := by
  simp [decodeCandidate]

@[simp] theorem decodeCandidate_canonical (i : Ext.Instr) :
    decodeCandidate (Ext.encode i) = some ⟨.canonical i, Ext.encode i⟩ := by
  simpa using decodeCandidate_canonical_append i []

@[simp] theorem decode_canonical_append (i : Ext.Instr) (rest : List Byte) :
    decode (Ext.encode i ++ rest) = some ⟨.canonical i, Ext.encode i⟩ := by
  simp [decode, encode]

@[simp] theorem decode_canonical (i : Ext.Instr) :
    decode (Ext.encode i) = some ⟨.canonical i, Ext.encode i⟩ := by
  simpa using decode_canonical_append i []

/-- Successful decoding guarantees byte-for-byte re-encoding and re-decoding. -/
theorem decode_encode {bytes : List Byte} {d : Decoded} (h : decode bytes = some d) :
    decode (encode d) = some d := by
  unfold decode at h
  split at h
  · cases h
  · split at h
    · rename_i hself
      cases h
      simp [decode, hself]
    · cases h

/-- Every accepted instruction preserves its consumed prefix exactly. -/
theorem decodeCandidate_sound {bytes : List Byte} {d : Decoded} (h : decodeCandidate bytes = some d) :
    0 < d.length ∧ d.length ≤ 15 ∧ encode d = bytes.take d.length ∧
      bytes = encode d ++ bytes.drop d.length := by
  unfold decodeCandidate at h
  split at h
  · rename_i i n hc
    cases h
    obtain ⟨hn, hp, hl, hb⟩ := Ext.decode_length hc
    obtain ⟨_, ht⟩ := Ext.decode_sound hc
    have htaken : (bytes.take n).length = n := by simp [List.length_take, Nat.min_eq_left hb]
    simp only [Decoded.length, encode, htaken]
    exact ⟨hp, hl, True.intro, (List.take_append_drop n bytes).symm⟩
  · split at h
    · rename_i raw rest hr
      split at h
      · rename_i i hi
        split at h
        · rename_i hg
          cases h
          obtain ⟨hp, hl, hb⟩ := hg
          exact ⟨hp, hl, hb.symm, by
            change bytes = raw.bytes ++ bytes.drop raw.bytes.length
            have ht := List.take_append_drop raw.bytes.length bytes
            rw [hb] at ht
            exact ht.symm⟩
        · cases h
      · cases h
    · cases h

/-- The public decoder preserves a nonempty prefix of at most fifteen bytes. -/
theorem decode_sound {bytes : List Byte} {d : Decoded} (h : decode bytes = some d) :
    0 < d.length ∧ d.length ≤ 15 ∧ encode d = bytes.take d.length ∧
      bytes = encode d ++ bytes.drop d.length := by
  unfold decode at h
  split at h
  · cases h
  · rename_i candidate hc
    split at h
    · cases h
      exact decodeCandidate_sound hc
    · cases h

end Silmaril.X86.Ext.Wire
