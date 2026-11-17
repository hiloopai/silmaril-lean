module

public import Silmaril.Machine.Abi.Conformance.Sse.Defs
public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.Sse

/-! # `Mach.str9L`: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Machine.Abi.Conformance.Sse`:

* **What the machine models and carries** (`str9L_models`, `str9L_carried`): it models the
  machine, the whole vector field, the whole x87 field, the direction flag, MXCSR and the x87
  control word; it carries x87 mode and the FFI thread pointer. A row on `Mach.str9L` proves
  `Return`'s obligations about the modelled fields from the machine's run, and holds the
  carried ones by the model (`Thms.Mach.store_carried`);
* **every completion** (`str9L_fillsAll`, `str9L_fill`): every machine state that agrees on the
  modelled fields completes the FFI state, whatever its time-stamp stream, CET flag and the
  hidden parts the modelled fields do not fix; `fill s tsc cetOff` is one for each stream and
  flag;
* `str9L_step`: where no tower form needs a missing feature, a step is a step of
  `Str9L.isa F exts` on the tower state, the hidden vector and x87 parts unchanged;
  `str9L_step_missing`: elsewhere there is no step;
* `str9L_vpcmpeqb_none`: **on `baseline64` the VEX form `vpcmpeqb (%rdi), %ymm0, %ymm1`
  (`C5 FD 74 0F`, AVX2) has no step**, where `Str9L.step` alone would run it;
* **the SSE argument and result bridges**: `fills_tower` (a completion's integer state and XMM
  file are `Sep.Plan.ffiXState s`), `entry_xmm` (an eight-byte SSE argument that `Ffi.Entry`
  places at `.vector i 0` is the low 64 bits of XMM `i` in every completion),
  `resultAt_store_double` (the `double` result `ResultAt` reads back from `.vector 0 0` of a
  returned state is the low 64 bits of its XMM0), `fills_mxcsr`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Sse

open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (Word XReg)
open Silmaril.X86.Sep.Plan (ffiXState xregOfIdx)

variable {F : Silmaril.X86.Features.FeatureSet} {exts : List Silmaril.X86.Features.Extension}
  {s : Ffi.State} {x : SState}

/-- **The fields `Mach.str9L` models.** -/
theorem str9L_models {f : FfiField} :
    (Mach.str9L F exts).models f = true ↔
      f = .machine ∨ f = .vectors ∨ f = .x87 ∨ f = .direction ∨ f = .mxcsr ∨ f = .x87Control :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.models_eq_true

/-- **The fields `Mach.str9L` carries**: x87 mode and the FFI thread pointer. -/
theorem str9L_carried {f : FfiField} :
    (Mach.str9L F exts).models f = false ↔ f = .x87Mode ∨ f = .fsBase :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.models_eq_false

/-- **Every state that fits completes**: any time-stamp stream, CET flag and hidden part. -/
theorem str9L_fillsAll : (Mach.str9L F exts).FillsAll := fun _ _ h => h

/-- The completion with time-stamp stream `tsc` and CET flag `cetOff`, for every stream and
flag. -/
theorem str9L_fill (s : Ffi.State) (tsc : Nat → Word) (cetOff : Bool) :
    (Mach.str9L F exts).Fills s (fill s tsc cetOff) :=
  fill_fills s tsc cetOff

/-- A step is a `Str9L` step of the tower state. -/
theorem str9L_step (x : SState) (h : Silmaril.X86.Str9L.towerMissing F x.l = none) :
    (Mach.str9L F exts).isa.step x =
      (Silmaril.X86.Str9L.step F exts x.l).map fun l => { x with l } := by
  simp only [Mach.str9L, isa, h]

/-- No step at a tower form that needs a feature `F` lacks. -/
theorem str9L_step_missing (x : SState) {f : Silmaril.X86.Features.Feature}
    (h : Silmaril.X86.Str9L.towerMissing F x.l = some f) : (Mach.str9L F exts).isa.step x = none := by
  simp only [Mach.str9L, isa, h]

/-- **On `baseline64` an AVX2 form of the tower has no step.** -/
theorem str9L_vpcmpeqb_none (exts : List Silmaril.X86.Features.Extension) {x : SState}
    {base : Word} (hl : Silmaril.X86.Ext.Loaded x.l.memory base [0xC5, 0xFD, 0x74, 0x0F])
    (hrip : x.l.core.rip = base) :
    (Mach.str9L Silmaril.X86.Features.FeatureSet.baseline64 exts).isa.step x = none :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.vpcmpeqb_none exts hl hrip

theorem fills_tower (h : Fills s x) : x.l.x.d.v.g.x = ffiXState s :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.fills_tower h

theorem fills_xmm (h : Fills s x) (r : XReg) :
    x.l.xmm r = (s.vectors r.toBitVec.toNat).setWidth 128 :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.fills_xmm h r

theorem fills_mxcsr (h : Fills s x) : x.l.mxcsr = ⟨s.mxcsr⟩ :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.fills_mxcsr h

theorem vector_chunk_iff (s : Ffi.State) {i : Nat} (hi : i < 32) (v : BitVec 64) :
    Ffi.ChunksAt s (Ffi.bytesOfNat v.toNat 0 8) [⟨0, 8, .vector i 0⟩] ↔
      (s.vectors i).setWidth 64 = v :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.vector_chunk_iff s hi v

/-- **An SSE argument at `.vector i 0`** is the low 64 bits of XMM `i` in every completion. -/
theorem entry_xmm {i : Nat} (hi : i < 16) {v : BitVec 64}
    (hc : Ffi.ChunksAt s (Ffi.bytesOfNat v.toNat 0 8) [⟨0, 8, .vector i 0⟩]) (h : Fills s x) :
    (x.l.xmm (xregOfIdx i)).setWidth 64 = v :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.entry_xmm hi hc h

theorem resultAt_double_iff (args : List Silmaril.Machine.Abi.SystemV.Scalar.Arg)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s t : Ffi.State) (r : BitVec 64) :
    sysvScalar.conv.ResultAt ⟨args, some (.scalar .double), h⟩ s t r ↔
      (t.vectors 0).setWidth 64 = r :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.resultAt_double_iff args h s t r

/-- **The `double` result of a returned state** is the low 64 bits of its XMM0. -/
theorem resultAt_store_double (args : List Silmaril.Machine.Abi.SystemV.Scalar.Arg)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s : Ffi.State) (y : SState)
    (r : BitVec 64) :
    sysvScalar.conv.ResultAt ⟨args, some (.scalar .double), h⟩ s
        ((Mach.str9L F exts).store s y) r ↔
      (y.l.xmm .xmm0).setWidth 64 = r :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.resultAt_store_double args h s y r

end Silmaril.Machine.Abi.Conformance.Sse

end
