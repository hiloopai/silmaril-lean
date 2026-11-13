module

public import Silmaril.X86.Features.Ext.BaseInt.Semantics
public import Silmaril.X86.Features.Embed

/-!
# The baseline-integer extension

`baseIntExt` packages the lane as a `Features.Extension`: the canonical
decoder of `Encoding.lean`, no required feature (every form is x86-64
baseline: CPUID reports nothing for ADC, SBB, SHLD, SHRD, BTx, PUSH imm or RET),
and `exec` of `Semantics.lean`.

## Lattice form

The sub-families are restrictions of `baseIntExt` (`Extension.restrict`):
`carryExt` (ADC/SBB at 32/64 bits), `alu16Ext` (16-bit ALU), `shdExt`
(SHLD/SHRD), `bitExt` (BTx) and `stackExt` (PUSH imm, `repz ret`). Each embeds
into `baseIntExt` (`Extension.Embeds.restrict`), and they are pairwise disjoint
(`subExts_pairwiseDisjoint`). So a run proved with any list of sub-families is
the same run with `baseIntExt` in their place, or with `baseIntExt` added to an
extension list (`run_baseInt`), provided the larger list is pairwise disjoint.

## Disjointness

* From the integer decoder: `Ext.decode` rejects every encoding of the lane
  (`ext_decode_encode_append`), so `step_of_ext` applies (`step_baseInt`).
* From `floatExt`: `disjoint_floatExt`. Every `Float.encode` begins with an
  optional `66`/`F2`/`F3`, an optional REX and `0F`; the byte after `0F` is an
  SSE opcode or a `38`/`3A` map byte (`floatKey_float_encode`). Every encoding
  of the lane either is not of that shape or has its opcode in
  `0F A3/A4/A5/AB/AC/AD/B3/BA/BB` (`floatKey_encode`), none of which is an SSE
  opcode of `X86.Float`.
-/

@[expose] public section

namespace Silmaril.X86.Features.BaseInt

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Pfx Opc Rex OpcOk rmRaw)
open Silmaril.Process (Memory)

/-- The baseline-integer lane. -/
def baseIntExt : Extension where
  name := "baseline integer: ADC/SBB, 16-bit ALU, SHLD/SHRD, BTx, PUSH imm, REPZ RET"
  Syntax := Instr
  decoder := decoder
  requires _ := []
  exec := exec

@[simp] theorem baseIntExt_decode : baseIntExt.decoder.decode = decode := rfl
@[simp] theorem baseIntExt_requires (i : Instr) : baseIntExt.requires i = [] := rfl
theorem baseIntExt_exec (i : Instr) (n : Nat) (s : State) (memory : Memory) :
    baseIntExt.exec i n s memory = exec i n s memory := rfl

/-! ## Sub-families -/

def carryExt : Extension := baseIntExt.restrict Instr.isCarry
def alu16Ext : Extension := baseIntExt.restrict Instr.isAlu16
def shdExt : Extension := baseIntExt.restrict Instr.isShd
def bitExt : Extension := baseIntExt.restrict Instr.isBit
def stackExt : Extension := baseIntExt.restrict Instr.isStack

/-- The sub-families, in the coverage inventory's priority order. -/
def subExts : List Extension := [carryExt, alu16Ext, shdExt, bitExt, stackExt]

theorem subExts_included : Included subExts [baseIntExt] := by
  intro e he
  simp only [subExts, List.mem_cons, List.mem_nil_iff, or_false] at he
  refine ⟨baseIntExt, List.mem_singleton_self _, ?_⟩
  rcases he with rfl | rfl | rfl | rfl | rfl <;> exact Extension.Embeds.restrict _ _

/-- The sub-family predicates are mutually exclusive. -/
private theorem excl {p q : Instr → Bool} (h : ∀ x, p x = true → q x = false) :
    (baseIntExt.restrict p).Disjoint (baseIntExt.restrict q) :=
  Extension.Disjoint.restrict baseIntExt h

theorem disjoint_carry_alu16 : carryExt.Disjoint alu16Ext :=
  excl (p := Instr.isCarry) (q := Instr.isAlu16) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_carry_shd : carryExt.Disjoint shdExt :=
  excl (p := Instr.isCarry) (q := Instr.isShd) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_carry_bit : carryExt.Disjoint bitExt :=
  excl (p := Instr.isCarry) (q := Instr.isBit) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_carry_stack : carryExt.Disjoint stackExt :=
  excl (p := Instr.isCarry) (q := Instr.isStack) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_alu16_shd : alu16Ext.Disjoint shdExt :=
  excl (p := Instr.isAlu16) (q := Instr.isShd) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_alu16_bit : alu16Ext.Disjoint bitExt :=
  excl (p := Instr.isAlu16) (q := Instr.isBit) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_alu16_stack : alu16Ext.Disjoint stackExt :=
  excl (p := Instr.isAlu16) (q := Instr.isStack) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_shd_bit : shdExt.Disjoint bitExt :=
  excl (p := Instr.isShd) (q := Instr.isBit) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_shd_stack : shdExt.Disjoint stackExt :=
  excl (p := Instr.isShd) (q := Instr.isStack) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem disjoint_bit_stack : bitExt.Disjoint stackExt :=
  excl (p := Instr.isBit) (q := Instr.isStack) fun x hx => by
    cases x <;> first | rfl | exact absurd hx Bool.false_ne_true

theorem subExts_pairwiseDisjoint : Extension.PairwiseDisjoint subExts := by
  simp only [Extension.PairwiseDisjoint, subExts, List.pairwise_cons, List.mem_cons,
    List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
    IsEmpty.forall_iff, implies_true]
  exact ⟨⟨disjoint_carry_alu16, disjoint_carry_shd, disjoint_carry_bit, disjoint_carry_stack⟩,
    ⟨disjoint_alu16_shd, disjoint_alu16_bit, disjoint_alu16_stack⟩,
    ⟨disjoint_shd_bit, disjoint_shd_stack⟩, disjoint_bit_stack⟩

/-! ## Disjointness from `floatExt` -/

/-- After an optional `66`/`F2`/`F3` and an optional REX byte: the byte after a
`0F` escape, if the next byte is `0F`. -/
def afterRex : List Byte → Option Byte
  | e :: rest => if e = 0x0F#8 then rest.head? else none
  | [] => none

def afterPfx : List Byte → Option Byte
  | p :: rest => if p.extractLsb' 4 4 = 4#4 then afterRex rest else afterRex (p :: rest)
  | [] => none

/-- The two-byte-opcode key of a legacy encoding. -/
def floatKey : List Byte → Option Byte
  | p :: rest =>
    if p = 0x66#8 ∨ p = 0xF2#8 ∨ p = 0xF3#8 then afterPfx rest else afterPfx (p :: rest)
  | [] => none

/-- The two-byte opcodes of the lane. -/
def laneTwoByte (b : Byte) : Bool :=
  b == 0xA3#8 || b == 0xA4#8 || b == 0xA5#8 || b == 0xAB#8 || b == 0xAC#8 || b == 0xAD#8 ||
    b == 0xB3#8 || b == 0xBA#8 || b == 0xBB#8

/-- A one-byte opcode that is not a legacy prefix, REX or `0F`. -/
def plainOne (b : Byte) : Bool :=
  b != 0x66#8 && b != 0xF2#8 && b != 0xF3#8 && b != 0x0F#8 && !(b.extractLsb' 4 4 == 4#4)

theorem floatKey_float_raw (r : X86.Raw) (t : List Byte) :
    floatKey (r.bytes ++ t) =
      some (match r.map with | .m0F => r.opc | .m0F38 => 0x38#8 | .m0F3A => 0x3A#8) := by
  obtain ⟨pfx, w, map, opc, reg, rm, imm⟩ := r
  simp only [X86.Raw.bytes]
  generalize X86.Raw.rex _ = n
  by_cases hn : n = 0#4 <;> cases pfx <;> cases map <;>
    simp [X86.rexBytes, hn, floatKey, afterPfx, afterRex, X86.Prefix.bytes,
      X86.OpMap.bytes, X86.rexByte_high]

theorem floatKey_float_encode (j : Float.Instr) (t : List Byte) :
    ∃ b, floatKey (Float.encode j ++ t) = some b ∧ laneTwoByte b = false := by
  refine ⟨_, floatKey_float_raw _ t, ?_⟩
  cases j with
  | arith op => cases op <;> simp [Float.toRaw, Float.raw0F, Float.ArithOp.opcode, laneTwoByte]
  | logic op => cases op <;> simp [Float.toRaw, Float.raw0F, Float.LogicOp.opcode, laneTwoByte]
  | _ => simp [Float.toRaw, Float.raw0F, laneTwoByte]

/-- The shape of the lane's raw fields that `floatKey` sees. -/
def KeyOk (r : Ext.Raw) : Prop :=
  (r.pfx = .none ∨ r.pfx = .opsize ∨ r.pfx = .rep) ∧
    match r.opc with
    | .one b => plainOne b = true
    | .two b => laneTwoByte b = true

theorem floatKey_raw {r : Ext.Raw} (h : KeyOk r) (t : List Byte) :
    floatKey (r.bytes ++ t) = none ∨ ∃ b, floatKey (r.bytes ++ t) = some b ∧ laneTwoByte b = true := by
  obtain ⟨fs, pfx, rex, opc, modrm, imm⟩ := r
  obtain ⟨hpfx, hopc⟩ := h
  simp only at hpfx hopc
  have hx : ∀ x : Rex, x.byte.extractLsb' 4 4 = 4#4 ∧ x.byte ≠ 0x66#8 ∧ x.byte ≠ 0xF2#8 ∧
      x.byte ≠ 0xF3#8 ∧ x.byte ≠ 0x0F#8 := by
    intro x
    have h := Ext.isRex_byte x
    simp only [Ext.isRex, beq_iff_eq] at h
    refine ⟨h, ?_, ?_, ?_, ?_⟩ <;> intro he <;> rw [he] at h <;> exact absurd h (by decide)
  cases fs
  · rcases hpfx with rfl | rfl | rfl <;> cases rex <;> cases opc <;>
    simp_all [Ext.Raw.bytes, Ext.segBytes, Pfx.bytes, Ext.rexBytes, Opc.bytes, floatKey, afterPfx,
      afterRex, plainOne]
  · left
    simp [Ext.Raw.bytes, Ext.segBytes, floatKey, afterPfx, afterRex]

set_option linter.unnecessarySeqFocus false in
theorem keyOk_toRaw (i : Instr) : KeyOk (toRaw i) := by
  cases i with
  | carry sz op form =>
    cases form <;> cases op <;>
      simp [toRaw, formRaw, rmRaw, accRaw, KeyOk, CarryOp.toOp, Op.opRM, Op.opR, Op.opA] <;> decide
  | alu16 op form =>
    cases form <;> cases op <;>
      simp [toRaw, formRaw, rmRaw, accRaw, KeyOk, Op.opRM, Op.opR, Op.opA] <;> decide
  | shd sz left dst src count =>
    cases left <;> cases count <;> cases sz <;>
      simp [toRaw, rmRaw, KeyOk, shdOpcode, Width.pfx] <;> decide
  | bit sz op dst src =>
    cases src <;> cases op <;> cases sz <;>
      simp [toRaw, rmRaw, KeyOk, BtOp.opcode, Width.pfx] <;> decide
  | pushI v => simp [toRaw, accRaw, KeyOk]; decide
  | pushI8 v => simp [toRaw, accRaw, KeyOk]; decide
  | repRet => simp [toRaw, accRaw, KeyOk]; decide

theorem floatKey_encode (i : Instr) (t : List Byte) :
    floatKey (encode i ++ t) = none ∨ ∃ b, floatKey (encode i ++ t) = some b ∧ laneTwoByte b = true :=
  floatKey_raw (keyOk_toRaw i) t

/-- No byte string is decoded both by the lane and by `X86.Float`. -/
theorem disjoint_floatExt : baseIntExt.Disjoint floatExt := by
  intro bytes
  cases hi : decode bytes with
  | none => exact .inl hi
  | some r =>
    right
    obtain ⟨i, n⟩ := r
    obtain ⟨-, rest, rfl⟩ := decode_eq_some_iff.mp hi
    cases hf : Float.decode (encode i ++ rest) with
    | none => exact hf
    | some r =>
      obtain ⟨j, k⟩ := r
      obtain ⟨-, -, hb⟩ := Float.decode_sound hf
      obtain ⟨b, hkey, hb'⟩ := floatKey_float_encode j ((encode i ++ rest).drop k)
      rw [← hb] at hkey
      rcases floatKey_encode i rest with h | ⟨c, hc, hc'⟩
      · rw [h] at hkey; cases hkey
      · rw [hc] at hkey; cases hkey; rw [hc'] at hb'; cases hb'

theorem disjoint_floatExt' : floatExt.Disjoint baseIntExt := disjoint_floatExt.symm

theorem pairwiseDisjoint_baseInt_float : Extension.PairwiseDisjoint [baseIntExt, floatExt] :=
  List.pairwise_pair.mpr disjoint_floatExt

/-! ## Transport -/

/-- Adding the lane in front of a pairwise-disjoint extension list changes no
run that only visits decoded states. -/
theorem run_baseInt {F : FeatureSet} {exts : List Extension} {exit : Word} {initial : MState}
    (hd : Extension.PairwiseDisjoint (baseIntExt :: exts))
    (hdec : ∀ n m, run F exts exit n initial = some m → Decodes exts m) (n : Nat) :
    run F (baseIntExt :: exts) exit n initial = run F exts exit n initial :=
  run_conservative hd (Included.of_subset (List.subset_cons_self _ _)) hdec n

/-- Runs proved with sub-families of the lane hold with the whole lane. -/
theorem run_subExts {F : FeatureSet} {exts : List Extension} {exit : Word} {initial : MState}
    (hsub : exts ⊆ subExts)
    (hdec : ∀ n m, run F exts exit n initial = some m → Decodes exts m) (n : Nat) :
    run F [baseIntExt] exit n initial = run F exts exit n initial :=
  run_conservative (List.pairwise_singleton _ _)
    ((Included.of_subset hsub).trans subExts_included) hdec n

/-- The lane needs no feature, so it never causes a feature fault. -/
theorem extStep_baseInt (F : FeatureSet) (i : Instr) (n : Nat) (m : MState) :
    extStep F baseIntExt i n m =
      match exec i n m.state m.memory with
      | .retired s memory => .retired ⟨s, memory⟩
      | .fault f => .fault f
      | .unmodeled => .unmodeled := by
  simp only [extStep, baseIntExt_requires, FeatureSet.missing, baseIntExt_exec]
  cases exec i n m.state m.memory <;> rfl

/-- A lane instruction at RIP: the integer decoder rejects it, so the machine
executes it with the lane. -/
theorem step_baseInt {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {i : Instr} {n : Nat}
    (hdec : decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = some (i, n))
    (hext : extDecode exts (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) =
      some ⟨baseIntExt, i, n⟩)
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F exts exit m = extStep F baseIntExt i n m :=
  step_of_ext (ext_decode_none hdec) hext hperm

/-- With the lane first in the list. -/
theorem step_baseInt_cons {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {i : Instr} {n : Nat}
    (hdec : decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = some (i, n))
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F (baseIntExt :: exts) exit m = extStep F baseIntExt i n m :=
  step_baseInt hdec (by simp [extDecode, hdec]) hperm

end Silmaril.X86.Features.BaseInt
