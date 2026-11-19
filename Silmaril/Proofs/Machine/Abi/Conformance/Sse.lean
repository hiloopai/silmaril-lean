module

public import Silmaril.Machine.Abi.Conformance.Sse.Defs
public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Bytes.Thms
public import Silmaril.Proofs.Machine.Abi.Conformance.Sse.Bits

/-!
# `Mach.str9L`: what a completion fixes, and the scalar SSE read-back

Proofs for `Silmaril.Machine.Abi.Conformance.Sse.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.Sse

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Sse
open Silmaril.X86 (XReg)
open Silmaril.X86.Sep.Plan (ffiXState xregOfIdx)

variable {s : Ffi.State} {x : SState}

theorem models_eq_true {f : FfiField} :
    models f = true ↔
      f = .machine ∨ f = .vectors ∨ f = .x87 ∨ f = .direction ∨ f = .mxcsr ∨ f = .x87Control := by
  cases f <;> simp [models]

theorem models_eq_false {f : FfiField} : models f = false ↔ f = .x87Mode ∨ f = .fsBase := by
  cases f <;> simp [models]

/-- The low 128 bits of a vector register of a machine state are the tower's XMM register. -/
theorem vecOf_low (x : SState) (r : XReg) :
    (vecOf x r.toBitVec.toNat).setWidth 128 = x.l.xmm r := by
  simp only [vecOf, r.toBitVec.isLt, ↓reduceIte, xregOfIdx_toBitVec]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [hj, show j < 256 by omega]

theorem fills_xmm (h : Fills s x) (r : XReg) :
    x.l.xmm r = (s.vectors r.toBitVec.toNat).setWidth 128 := by
  rw [← vecOf_low x r]
  exact congrArg (fun v => (v r.toBitVec.toNat).setWidth 128) (h .vectors rfl)

/-- **A completion's integer state and XMM file are `Sep.Plan.ffiXState` of the FFI state.** -/
theorem fills_tower (h : Fills s x) : x.l.x.d.v.g.x = ffiXState s := by
  change (⟨x.l.x.d.v.g.x.m, x.l.x.d.v.g.x.xmm⟩ : Silmaril.X86.Sse9.XState) = ⟨s.machine, _⟩
  congr 1
  · exact h .machine rfl
  · exact funext (fills_xmm h)

theorem fills_mxcsr (h : Fills s x) : x.l.mxcsr = ⟨s.mxcsr⟩ := by
  rw [← (h .mxcsr rfl : x.l.mxcsr.bits = s.mxcsr)]; rfl

/-- An eight-byte value at the low bytes of vector register `i`. -/
theorem vector_chunk_iff (s : Ffi.State) {i : Nat} (hi : i < 32) (v : BitVec 64) :
    Ffi.ChunksAt s (Ffi.bytesOfNat v.toNat 0 8) [⟨0, 8, .vector i 0⟩] ↔
      (s.vectors i).setWidth 64 = v := by
  have wide : Ffi.bytesOfNat (s.vectors i).toNat 0 8 =
      Ffi.bytesOfNat ((s.vectors i).setWidth 64).toNat 0 8 := by
    rw [BitVec.toNat_setWidth]
    exact (Ffi.bytesOfNat_mod _ 8).symm
  simp only [Ffi.ChunksAt, List.mem_singleton, forall_eq, Ffi.locationBytes, Ffi.bytesOfNat_length,
    Nat.zero_add, le_refl, true_and, List.drop_zero,
    List.take_of_length_le (le_of_eq (Ffi.bytesOfNat_length _ _ _)), hi, decide_true,
    show (8 : Nat) ≤ 64 from by decide, Bool.and_self, ite_true, Option.some.injEq, wide]
  exact ⟨bytes8_inj, fun h => h ▸ rfl⟩

/-- **The scalar `double` result** of `sysvScalar` is the low eight bytes of vector register 0. -/
theorem resultAt_double_iff (args : List Silmaril.Machine.Abi.SystemV.Scalar.Arg)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s t : Ffi.State) (r : BitVec 64) :
    sysvScalar.conv.ResultAt ⟨args, some (.scalar .double), h⟩ s t r ↔
      (t.vectors 0).setWidth 64 = r := by
  refine (Silmaril.Machine.Abi.SystemV.Scalar.resultAt_some {} args .double h s t r).trans ?_
  rw [← vector_chunk_iff t (i := 0) (by decide) r]
  simp only [Ffi.ChunksAt, List.mem_singleton, forall_eq, Ffi.bytesOfNat_length, Nat.zero_add,
    le_refl, true_and, List.drop_zero,
    List.take_of_length_le (le_of_eq (Ffi.bytesOfNat_length _ _ _))]
  rfl

/-- **The result read back from a returned state** is the low eight bytes of its XMM0. -/
theorem resultAt_store_double {F : Silmaril.X86.Features.FeatureSet}
    {exts : List Silmaril.X86.Features.Extension}
    (args : List Silmaril.Machine.Abi.SystemV.Scalar.Arg)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s : Ffi.State) (y : SState)
    (r : BitVec 64) :
    sysvScalar.conv.ResultAt ⟨args, some (.scalar .double), h⟩ s
        ((Mach.str9L F exts).store s y) r ↔
      (y.l.xmm .xmm0).setWidth 64 = r := by
  rw [resultAt_double_iff, ← vecOf_low y .xmm0]
  have e : (vecOf y 0).setWidth 64 = ((vecOf y 0).setWidth 128).setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp [hj]
  exact e ▸ Iff.rfl

/-- **An SSE argument placed at `.vector i 0`** fixes the low eight bytes of XMM `i` in every
completion. -/
theorem entry_xmm {i : Nat} (hi : i < 16) {v : BitVec 64}
    (hc : Ffi.ChunksAt s (Ffi.bytesOfNat v.toNat 0 8) [⟨0, 8, .vector i 0⟩]) (h : Fills s x) :
    (x.l.xmm (xregOfIdx i)).setWidth 64 = v := by
  rw [fills_xmm h, xregOfIdx_toNat hi, ← (vector_chunk_iff s (by omega) v).1 hc]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

/-- On `baseline64`, `vpcmpeqb (%rdi), %ymm0, %ymm1` (AVX2) has no step. -/
theorem vpcmpeqb_none (exts : List Silmaril.X86.Features.Extension) {x : SState}
    {base : Silmaril.X86.Word}
    (hl : Silmaril.X86.Ext.Loaded x.l.memory base [0xC5, 0xFD, 0x74, 0x0F])
    (hrip : x.l.core.rip = base) :
    (Mach.str9L Silmaril.X86.Features.FeatureSet.baseline64 exts).isa.step x = none := by
  have hd := Silmaril.X86.Str9L.decodeL_vpcmpeqb
  rcases hdl : Silmaril.X86.Str9V.decodeL [0xC5, 0xFD, 0x74, 0x0F] with _ | ⟨i, n⟩
  · rw [hdl] at hd; cases hd
  rw [hdl] at hd
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨hr, rfl⟩ := hd
  have hm := Silmaril.X86.Str9L.towerMissing_of_listed_v
    (F := Silmaril.X86.Features.FeatureSet.baseline64) (s := x.l) (o := 0) (l := 4) hl
    (by rw [hrip]; simp) (by decide) hdl
  rw [hr, show Silmaril.X86.Features.FeatureSet.baseline64.missing [.avx2] = some .avx2 by decide]
    at hm
  simp only [Mach.str9L, isa, hm]

end Silmaril.Proofs.Machine.Abi.Conformance.Sse

end
