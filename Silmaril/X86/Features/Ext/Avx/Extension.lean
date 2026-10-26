module

public import Silmaril.X86.Features.Ext.Avx.Semantics
public import Silmaril.X86.Features.Transport

/-!
# The `avx` lane as an `Extension`

`ext` packages the VEX codec (`byteDecoder`), the CPUID rule of every form
(`Instr.requires`) and the semantics (`exec`).

## Features and XCR0

`Instr.requires` is the SDM CPUID column (`FeatClass.requires`): VEX.128
integer forms need AVX and VEX.256 ones AVX2; VBROADCASTSS/SD need AVX from
memory and AVX2 from a register; VEX AES/PCLMULQDQ need AES/PCLMULQDQ and AVX
at 128 bits and VAES/VPCLMULQDQ at 256 bits; GFNI needs GFNI and AVX.

Every instruction requires a feature whose instructions need the OS to enable
the SSE and AVX state components (`Feature.xcr0 = xcr0Avx`,
`requires_xcr0`). Hence on a processor described by CPUID and an XCR0 without
`XCR0[2:1] = 11b`, every instruction of the lane raises #UD
(`extStep_ofCpuid_noAvxState`), whatever CPUID reports, as SDM Vol. 1, §14.3
requires.

## The integer decoder

The integer decoder (`Ext.decode`) rejects every encoding of the lane, whatever
follows (`ext_decode_encode`): `Ext.parseRaw` fails on `C4`, `C5`, `64 C4` and
`64 C5`. `step_of_decode` is the machine step at an instruction of the lane.
-/

@[expose] public section

namespace Silmaril.X86.Features.Avx

open Silmaril.Process (Memory)
open Silmaril.X86 (Byte fetchWindow maxInstrLength)

/-- The features of a form's CPUID rule at a vector length, for a register
(`mem = false`) or memory ModRM.rm operand. -/
def FeatClass.requires : FeatClass → Bool → Bool → List Feature
  | .int, l, _ => if l then [.avx2] else [.avx]
  | .avx, _, _ => [.avx]
  | .avx2, _, _ => [.avx2]
  | .bcast, _, mem => if mem then [.avx] else [.avx2]
  | .aes, l, _ => if l then [.vaes] else [.aes, .avx]
  | .clmul, l, _ => if l then [.vpclmulqdq] else [.pclmulqdq, .avx]
  | .gfni, _, _ => [.gfni, .avx]
  | .fma, _, _ => [.fma]
  | .f16c, _, _ => [.f16c]

/-- Whether ModRM.rm is a memory operand. -/
def Opnd.isMem : Opnd → Bool
  | .reg _ => false
  | .mem _ => true

/-- The features an instruction requires. -/
def Instr.requires (i : Instr) : List Feature := i.op.info.feat.requires i.l i.rm.isMem

/-- The lane. -/
def ext : Extension where
  name := "avx"
  Syntax := Syntax
  decoder := byteDecoder
  requires i := i.1.requires
  exec := exec

@[simp] theorem ext_decode : ext.decoder.decode = decode := rfl

theorem ext_requires (i : Syntax) : ext.requires i = i.1.requires := rfl

theorem ext_exec (i : Syntax) (n : Nat) (s : State) (memory : Memory) :
    ext.exec i n s memory = exec i n s memory := rfl

/-! ## Features and XCR0 -/

/-- Every CPUID rule names a feature that needs the AVX state components. -/
theorem FeatClass.requires_xcr0 (c : FeatClass) (l mem : Bool) :
    ∃ f ∈ c.requires l mem, f.xcr0 = Feature.xcr0Avx := by
  cases c <;> cases l <;> cases mem <;> decide

theorem requires_xcr0 (i : Syntax) : ∃ f ∈ ext.requires i, f.xcr0 = Feature.xcr0Avx :=
  FeatClass.requires_xcr0 _ _ _

/-- Without the SSE and AVX state enabled in XCR0 some required feature is
missing, whatever CPUID reports. -/
theorem missing_ofCpuid_noAvxState {cpuid : BitVec 32 → BitVec 32 → Ext.Wire.CpuidReply}
    {xcr0 : BitVec 64} (hx : xcr0 &&& Feature.xcr0Avx ≠ Feature.xcr0Avx) (i : Syntax) :
    (FeatureSet.ofCpuid cpuid xcr0).missing (ext.requires i) ≠ none := by
  intro h
  obtain ⟨f, hf, hx0⟩ := requires_xcr0 i
  have hmem := FeatureSet.missing_eq_none_iff.mp h f hf
  refine FeatureSet.not_mem_ofCpuid_of_xcr0 (cpuid := cpuid) ?_ ?_ hmem
  · rw [hx0]; decide
  · rw [hx0]; exact hx

/-- On a processor whose OS has not enabled the AVX state, every instruction of
the lane raises #UD for a missing feature. -/
theorem extStep_ofCpuid_noAvxState {cpuid : BitVec 32 → BitVec 32 → Ext.Wire.CpuidReply}
    {xcr0 : BitVec 64} (hx : xcr0 &&& Feature.xcr0Avx ≠ Feature.xcr0Avx) (i : Syntax) (n : Nat)
    (m : MState) : ∃ f, extStep (FeatureSet.ofCpuid cpuid xcr0) ext i n m = .featureUD f := by
  unfold extStep
  cases h : (FeatureSet.ofCpuid cpuid xcr0).missing (ext.requires i) with
  | none => exact absurd h (missing_ofCpuid_noAvxState hx i)
  | some f => exact ⟨f, rfl⟩

/-! ## The integer decoder rejects the lane -/

def isBad {α : Type} : Ext.PResult α → Bool
  | .bad => true
  | _ => false

theorem isBad_iff {α : Type} {r : Ext.PResult α} : isBad r = true ↔ r = .bad := by
  cases r <;> simp [isBad]

/-- `Ext.parseRaw` rejects a VEX prefix byte, with or without an FS override. -/
theorem header_bad : ∀ fs : Bool, ∀ b ∈ [0xC5#8, 0xC4#8],
    isBad (Ext.parseRaw (Ext.segBytes fs ++ [b])) = true := by
  decide +kernel

theorem encode_eq_header (i : Syntax) :
    encode i = Ext.segBytes (toRaw i.1).fs ++ ([(toRaw i.1).vex.lead] ++
      ((toRaw i.1).vex.payload ++ ((toRaw i.1).opc :: (Ext.modrmBytes (toRaw i.1).modrm ++
        (toRaw i.1).imm.toList)))) := by
  simp [encode, VRaw.bytes, VRaw.vexBytes, Vex.Prefix.bytes]

/-- The integer decoder rejects every encoding of the lane, whatever follows. -/
theorem ext_decode_encode (i : Syntax) (more : List Byte) : Ext.decode (encode i ++ more) = none := by
  have hl : (toRaw i.1).vex.lead ∈ [0xC5#8, 0xC4#8] := by
    rcases (toRaw i.1).vex.lead_cases with h | h <;> simp [h]
  have h := isBad_iff.mp (header_bad (toRaw i.1).fs _ hl)
  have hb : encode i ++ more = (Ext.segBytes (toRaw i.1).fs ++ [(toRaw i.1).vex.lead]) ++
      ((toRaw i.1).vex.payload ++ ((toRaw i.1).opc :: (Ext.modrmBytes (toRaw i.1).modrm ++
        (toRaw i.1).imm.toList)) ++ more) := by
    rw [encode_eq_header]; simp
  unfold Ext.decode
  rw [hb, Ext.good_parseRaw.bad h]

theorem ext_decode_of_decode {bytes : List Byte} {i : Syntax} {n : Nat}
    (h : decode bytes = some (i, n)) : Ext.decode bytes = none := by
  obtain ⟨-, rest, rfl⟩ := decode_sound h
  exact ext_decode_encode i rest

/-- The machine step at an instruction of the lane, for any pairwise disjoint
extension list containing `ext`. -/
theorem step_of_decode {F : FeatureSet} {exts : List Extension} {exit : X86.Word} {m : MState}
    {i : Syntax} {n : Nat} (hd : Extension.PairwiseDisjoint exts) (he : ext ∈ exts)
    (hdec : decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = some (i, n))
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F exts exit m = extStep F ext i n m :=
  step_of_ext (ext_decode_of_decode hdec) (extDecode_of_mem hd he (x := (i : ext.Syntax)) hdec)
    hperm

/-! ## The opcode key -/

theorem toRaw_key (i : Instr) :
    (toRaw i).pp = i.op.info.pp ∧ (toRaw i).map = i.op.info.map ∧ (toRaw i).opc = i.op.info.opc := by
  unfold toRaw; dsimp only; split <;> exact ⟨rfl, rfl, rfl⟩

/-- A decoded instruction starts with an FS override or has its form's
(`pp`, map, opcode) key (`Vex.key`). -/
theorem decode_key {bytes : List Byte} {i : Syntax} {n : Nat} (h : decode bytes = some (i, n)) :
    (∃ t, bytes = 0x64#8 :: t) ∨
      Vex.key bytes = some (i.1.op.info.pp, i.1.op.info.map, i.1.op.info.opc) := by
  obtain ⟨-, rest, rfl⟩ := decode_sound h
  obtain ⟨hp, hm, ho⟩ := toRaw_key i.1
  cases hfs : (toRaw i.1).fs
  · right
    simp only [encode, VRaw.bytes, hfs, Ext.segBytes_false, List.nil_append, VRaw.vexBytes,
      List.append_assoc, List.cons_append]
    rw [Vex.key_bytes]
    simp [VRaw.vex, hp, hm, ho]
  · left
    simp [encode, VRaw.bytes, hfs]

/-! ## Pure register forms

A form whose sources are registers is a pure register instruction
(`Extension.Pure`): it retires, leaves memory alone and advances RIP by its
length. The hypotheses that the earlier dispatch tables do not claim the form
hold by `rfl` for a concrete form. -/

theorem rip_writeV (s : State) (l : Bool) (n : BitVec 4) (v : BitVec 256) :
    (writeV s l n v).rip = s.rip := by
  unfold writeV; split <;> rfl

theorem pure_intOp {i : Syntax} {f : BitVec 256 → BitVec 256 → BitVec 256}
    (h : intOp? i.1.op i.1.w = some f) {n : BitVec 4} (hrm : i.1.rm = .reg n) : ext.Pure i :=
  Extension.Pure.of_eq _ (fun s => writeV s i.1.l i.1.reg (f (s.ymm (vreg i.1.vvvv)) (s.ymm (vreg n))))
    (fun s => rip_writeV ..) (fun length s memory => by
      show exec i length s memory = _
      unfold exec
      simp only [h, hrm, readSrc, retireV]
      rfl)

theorem pure_intOpI {i : Syntax} {f : Byte → BitVec 256 → BitVec 256 → BitVec 256}
    (h0 : intOp? i.1.op i.1.w = none) (h : intOpI? i.1.op = some f) {n : BitVec 4}
    (hrm : i.1.rm = .reg n) : ext.Pure i :=
  Extension.Pure.of_eq _
    (fun s => writeV s i.1.l i.1.reg (f i.1.imm (s.ymm (vreg i.1.vvvv)) (s.ymm (vreg n))))
    (fun s => rip_writeV ..) (fun length s memory => by
      show exec i length s memory = _
      unfold exec
      simp only [h0, h, hrm, readSrc, retireV]
      rfl)

theorem pure_unOp {i : Syntax} {f : Byte → BitVec 256 → BitVec 256}
    (h0 : intOp? i.1.op i.1.w = none) (h1 : intOpI? i.1.op = none) (h : unOp? i.1.op = some f)
    {n : BitVec 4} (hrm : i.1.rm = .reg n) : ext.Pure i :=
  Extension.Pure.of_eq _ (fun s => writeV s i.1.l i.1.reg (f i.1.imm (s.ymm (vreg n))))
    (fun s => rip_writeV ..) (fun length s memory => by
      show exec i length s memory = _
      unfold exec
      simp only [h0, h1, h, hrm, readSrc, retireV]
      rfl)

theorem pure_shiftImm {i : Syntax} {f : Byte → BitVec 256 → BitVec 256}
    (h0 : intOp? i.1.op i.1.w = none) (h1 : intOpI? i.1.op = none) (h2 : unOp? i.1.op = none)
    (h : shiftImm? i.1.op = some f) {n : BitVec 4} (hrm : i.1.rm = .reg n) : ext.Pure i :=
  Extension.Pure.of_eq _ (fun s => writeV s i.1.l i.1.vvvv (f i.1.imm (s.ymm (vreg n))))
    (fun s => rip_writeV ..) (fun length s memory => by
      show exec i length s memory = _
      unfold exec
      simp only [h0, h1, h2, h, hrm, readSrc, retireV]
      rfl)

/-! ## Running AVX/AVX2 code after a CPUID check

Code that branches on CPUID typically checks CPUID.1:ECX.AVX[28],
CPUID.(7,0):EBX.AVX2[5], CPUID.1:ECX.OSXSAVE[27] and, with XGETBV, that
`XCR0[2:1] = 11b` before taking an AVX2 path. On such a processor no
integer, AVX, AVX2 or broadcast form of the lane raises #UD
(`missing_ofCpuid_avx2`). -/

/-- Membership of a feature that needs OS-managed state. -/
theorem mem_ofCpuid_iff {cpuid : BitVec 32 → BitVec 32 → Ext.Wire.CpuidReply} {xcr0 : BitVec 64}
    {f : Feature} (h : f.xcr0 ≠ 0) :
    f ∈ FeatureSet.ofCpuid cpuid xcr0 ↔
      FeatureSet.leafAvailable cpuid f.cpuid.leaf = true ∧
        (f.cpuid.reg.get (cpuid f.cpuid.leaf f.cpuid.subleaf)).getLsbD f.cpuid.bit = true ∧
        (cpuid 1 0).ecx.getLsbD 27 = true ∧ xcr0 &&& f.xcr0 = f.xcr0 := by
  have h' : ¬(f.xcr0 = 0#64) := h
  simp [FeatureSet.ofCpuid, FeatureSet.mem_iff, h', and_assoc]

/-- A basic leaf at most the maximum leaf is available. -/
theorem leafAvailable_of_le {cpuid : BitVec 32 → BitVec 32 → Ext.Wire.CpuidReply} {leaf : BitVec 32}
    (h : leaf < 0x80000000#32) (hle : leaf ≤ (cpuid 0 0).eax) :
    FeatureSet.leafAvailable cpuid leaf = true := by
  simp only [FeatureSet.leafAvailable, h, ↓reduceIte, decide_eq_true_eq]
  exact hle

/-- With AVX and AVX2 present, the integer, AVX, AVX2 and broadcast forms
need nothing else. -/
theorem missing_of_avx2 {F : FeatureSet} (h1 : Feature.avx ∈ F) (h2 : Feature.avx2 ∈ F)
    (i : Syntax) (hc : i.1.op.info.feat ∈ [FeatClass.int, .avx, .avx2, .bcast]) :
    F.missing (ext.requires i) = none := by
  rw [FeatureSet.missing_eq_none_iff]
  intro f hf
  simp only [ext_requires, Instr.requires] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc | hc | hc <;> rw [hc] at hf <;>
    simp only [FeatClass.requires] at hf <;> (try split at hf) <;>
    simp only [List.mem_singleton] at hf <;> subst hf <;> assumption

/-- The CPUID and XCR0 conditions an AVX2 dispatch checks make every integer,
AVX, AVX2 and broadcast form of the lane execute without #UD. -/
theorem missing_ofCpuid_avx2 {cpuid : BitVec 32 → BitVec 32 → Ext.Wire.CpuidReply}
    {xcr0 : BitVec 64} (hleaf : 7#32 ≤ (cpuid 0 0).eax) (havx : (cpuid 1 0).ecx.getLsbD 28 = true)
    (havx2 : (cpuid 7 0).ebx.getLsbD 5 = true) (hos : (cpuid 1 0).ecx.getLsbD 27 = true)
    (hx : xcr0 &&& Feature.xcr0Avx = Feature.xcr0Avx)
    (i : Syntax) (hc : i.1.op.info.feat ∈ [FeatClass.int, .avx, .avx2, .bcast]) :
    (FeatureSet.ofCpuid cpuid xcr0).missing (ext.requires i) = none := by
  have h1leaf : 1#32 ≤ (cpuid 0 0).eax := by bv_omega
  refine missing_of_avx2 ?_ ?_ i hc
  · refine (mem_ofCpuid_iff (by decide)).mpr ⟨?_, havx, hos, hx⟩
    exact leafAvailable_of_le (leaf := 1#32) (by decide) h1leaf
  · refine (mem_ofCpuid_iff (by decide)).mpr ⟨?_, havx2, hos, hx⟩
    exact leafAvailable_of_le (leaf := 7#32) (by decide) hleaf

end Silmaril.X86.Features.Avx
