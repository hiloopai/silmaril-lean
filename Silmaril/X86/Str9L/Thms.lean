module

public import Silmaril.Raw.X86.Str9L

/-!
# `Str9L`: the conservative extension of `Str9X`, the lane law, the machine

* `step_of_str9x`: **every `Str9X` step is a step** (lane forms are tried only where every
  decoder of `Str9X` rejects the bytes), so `extendsStr9X F exts : Str9X.isa.Extends (isa F
  exts)` (lens `s ↦ s.x`, MXCSR the frame), for every feature set and list of lanes; and
  `run_of_str9v`: every `Str9V` run from DF clear is a run here.
* `step_of_fetch_lane`: the law of a lane form, at the fetch window.
* `step_of_listed_lane_head`: **a form of the first lane at a listed offset**, whatever bytes
  follow it, where no decoder of `Str9X` claims the form's bytes (`laneBad`, by `decide`);
  `step_of_listed_float`: a committed scalar SSE form (`floatExt`, the first lane of `lanes` and
  of `Features.sseExts`) takes the core, the XMM file and MXCSR from its `X86.Float` result and
  keeps the upper YMM halves, DF, the x87 state and the ghost state (`back_withFloat`);
  `laneBad_addsd`: `addsd %xmm1, %xmm0` (`F2 0F 58 C1`) is such a form.
* `towerMissing_of_listed`, `towerMissing_of_listed_lane`, `towerMissing_of_listed_v`: **the
  feature gate of the tower's own forms** (`towerMissing`, from `vRequires`) is inactive at a
  listed integer instruction or lane form, and at a listed `Str9V` form is the first feature
  the form needs and `F` lacks; `decodeL_vpcmpeqb`: `vpcmpeqb (%rdi), %ymm0, %ymm1`
  (`C5 FD 74 0F`) is a four-byte `Str9V` form needing AVX2.

The proofs are in `Silmaril.Raw.X86.Str9L`, re-exported here. `Str9L/Vectors.lean` runs the
`avx` lane's and `roundss`/`roundsd`'s native vectors through `Str9L.step v3 lanes`.
-/

@[expose] public section

namespace Silmaril.X86.Str9L

open Silmaril.X86.Features (Extension FeatureSet)
open Silmaril.Machine.Execution (run Reaches)

/-- **`Str9L` as a segment-VC instance** over `Str9D`'s integer instructions. -/
@[reducible] def isa (F : FeatureSet) (exts : List Extension) : Silmaril.X86.SegVC.Isa LState where
  Instr := Silmaril.X86.Str9FsX.Instr
  instDecEq := inferInstance
  decode := Str9D.decode
  exec := Silmaril.X86.Str9FsX.exec
  core := fun s => s.core
  mem := fun s => s.memory
  upd := fun s c m => ⟨⟨s.x.d.upd c m, s.x.fpu⟩, s.mxcsr⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step F exts
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ =>
    step_of_str9x (Str9X.isa.step_of (s := _) trivial hl hrip hfit hdec hx trivial)

@[simp] theorem isa_step (F : FeatureSet) (exts : List Extension) :
    (isa F exts).step = step F exts := rfl

/-- **`Str9L` extends `Str9X`** along `s ↦ s.x` (MXCSR is the frame). -/
@[reducible] def extendsStr9X (F : FeatureSet) (exts : List Extension) :
    Str9X.isa.Extends (isa F exts) where
  view s := s.x
  put s x := ⟨x, s.mxcsr⟩
  view_put _ _ := rfl
  put_put _ _ _ := rfl
  put_view _ := rfl
  core _ := rfl
  mem _ := rfl
  upd _ _ _ := rfl
  live _ _ := trivial
  step h := step_of_str9x h

/-- **Every `Str9V` run from DF clear is a run**, with DF clear and the x87 state and MXCSR
kept. -/
theorem run_of_str9v (F : FeatureSet) (exts : List Extension) {n : Nat} {v v' : Str9V.VState}
    (fpu : Silmaril.X86.Features.X87) (mxcsr : Silmaril.X86.Float.MXCSR)
    (h : run Str9V.step n v = some v') :
    run (step F exts) n ⟨⟨⟨v, false⟩, fpu⟩, mxcsr⟩ = some ⟨⟨⟨v', false⟩, fpu⟩, mxcsr⟩ :=
  (extendsStr9X F exts).run n (x := ⟨⟨⟨v, false⟩, fpu⟩, mxcsr⟩) (Str9X.run_of_str9v fpu h)

/-- A `Str9V` run from DF clear reaches the same state here. -/
theorem reaches_of_str9v (F : FeatureSet) (exts : List Extension) {v v' : Str9V.VState}
    (fpu : Silmaril.X86.Features.X87) (mxcsr : Silmaril.X86.Float.MXCSR)
    (h : Reaches Str9V.step v v') :
    Reaches (step F exts) ⟨⟨⟨v, false⟩, fpu⟩, mxcsr⟩ ⟨⟨⟨v', false⟩, fpu⟩, mxcsr⟩ :=
  let ⟨n, hn⟩ := h; ⟨n, run_of_str9v F exts fpu mxcsr hn⟩

/-- `addsd %xmm1, %xmm0` (`F2 0F 58 C1`) is a four-byte `floatExt` form no decoder of `Str9X`
claims, whatever follows it. -/
theorem laneBad_addsd : laneBad [0xF2, 0x0F, 0x58, 0xC1] = true ∧
    Silmaril.X86.Float.decode [0xF2, 0x0F, 0x58, 0xC1] =
      some (.arith .add .double .xmm0 (.reg .xmm1), 4) := by decide

/-- `vpcmpeqb (%rdi), %ymm0, %ymm1` (`C5 FD 74 0F`) is a listed four-byte `Str9V` form that
needs AVX2. -/
theorem decodeL_vpcmpeqb :
    ((Str9V.decodeL [0xC5, 0xFD, 0x74, 0x0F]).map fun p => (vRequires p.1, p.2)) =
      some ([.avx2], 4) := by decide

/-- `v3` has no AVX-512 feature, so the view is exact for every lane on it. -/
theorem v3_noAvx512 : Silmaril.X86.Features.Feature.all.all
    (fun f => !(f.isAvx512 && v3.has f)) = true := by decide

end Silmaril.X86.Str9L
