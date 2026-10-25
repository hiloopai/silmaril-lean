module

public import Silmaril.Compile.PassAPI.Category
public import Silmaril.Wasm.Binaryen.PassAPI.ModuleModes
public import Silmaril.Wasm.Binaryen.Exe.Fold

@[expose] public section

/-! # Core and Binaryen IRs over an explicit optimization mode

This uses the shared category of IRs over a replacement relation. Its semantic
domain is the existing source-first `ExportCorrect`, including admission and
feasibility. Every mode has its own category; trap insertion is not identified
with ordinary subset refinement of raw export observations.

Existing Core and Binaryen mode passes become endomorphisms without changing
their executable functions. The syntax-preserving structured lift and lowering
give translations between the two IRs at every numerical profile and host.
Other IRs need their own denotation and translation proof; no Wasm-to-SSA or
open-context congruence theorem is supplied by this packaging.
-/

namespace Silmaril.Wasm.Binaryen.Modes

open CategoryTheory Execution.Core Numerics Validation
open Silmaril.Compile.PassAPI

variable {H : Type}

/-- Actual Core module correctness at the selected mode, rather than an
unrelated preorder or an assumed observation-subset relation. -/
def modeDomain (mode : Optimization.Mode) (P : Profile) (host : HostSemantics H) :
    Silmaril.Compile.PassAPI.Domain Module where
  Rel := ExportCorrect mode P host
  refl := ExportCorrect.refl mode P host
  trans := ExportCorrect.trans

abbrev coreIR (mode : Optimization.Mode) (P : Profile) (host : HostSemantics H) :
    Silmaril.Compile.PassAPI.IR (modeDomain mode P host) where
  Prog := Module
  den := id
  Inv := ModuleValid

abbrev binaryenIR (mode : Optimization.Mode) (P : Profile) (host : HostSemantics H) :
    Silmaril.Compile.PassAPI.IR (modeDomain mode P host) where
  Prog := BModule
  den := BModule.lower
  Inv := BModule.Ok

@[simp] theorem coreIR_contract (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) :
    (coreIR mode P host).contract = moduleContract mode P host := rfl

@[simp] theorem binaryenIR_contract (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) :
    (binaryenIR mode P host).contract = contract mode P host := rfl

/-- An existing Core mode pass is an endomorphism in the shared IR category. -/
def ofCoreModePass {mode : Optimization.Mode} {P : Profile} {host : HostSemantics H}
    (pass : Silmaril.Compile.PassAPI.Pass (moduleContract mode P host)) :
    coreIR mode P host ⟶ coreIR mode P host :=
  ⟨pass.run, pass.inv_run, pass.sound⟩

/-- An existing Binaryen mode pass is an endomorphism in the same category. -/
def ofModePass {mode : Optimization.Mode} {P : Profile} {host : HostSemantics H}
    (pass : Silmaril.Compile.PassAPI.Pass (contract mode P host)) :
    binaryenIR mode P host ⟶ binaryenIR mode P host :=
  ⟨pass.run, pass.inv_run, pass.sound⟩

@[simp] theorem ofCoreModePass_run {mode : Optimization.Mode} {P : Profile}
    {host : HostSemantics H}
    (pass : Silmaril.Compile.PassAPI.Pass (moduleContract mode P host)) (m : Module) :
    Translation.run (ofCoreModePass pass) m = pass.run m := rfl

@[simp] theorem ofModePass_run {mode : Optimization.Mode} {P : Profile}
    {host : HostSemantics H}
    (pass : Silmaril.Compile.PassAPI.Pass (contract mode P host)) (m : BModule) :
    Translation.run (ofModePass pass) m = pass.run m := rfl

@[simp] theorem ofCoreModePass_one (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) :
    ofCoreModePass (1 : Silmaril.Compile.PassAPI.Pass (moduleContract mode P host)) =
      𝟙 (coreIR mode P host) := rfl

@[simp] theorem ofModePass_one (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) :
    ofModePass (1 : Silmaril.Compile.PassAPI.Pass (contract mode P host)) =
      𝟙 (binaryenIR mode P host) := rfl

/-- Both APIs run the left factor first. -/
@[simp] theorem ofCoreModePass_mul {mode : Optimization.Mode} {P : Profile}
    {host : HostSemantics H}
    (first second : Silmaril.Compile.PassAPI.Pass (moduleContract mode P host)) :
    ofCoreModePass (first * second) = ofCoreModePass first ≫ ofCoreModePass second := rfl

@[simp] theorem ofModePass_mul {mode : Optimization.Mode} {P : Profile}
    {host : HostSemantics H}
    (first second : Silmaril.Compile.PassAPI.Pass (contract mode P host)) :
    ofModePass (first * second) = ofModePass first ≫ ofModePass second := rfl

/-- Lowering is the denotation itself and preserves the actual Core module. -/
def lower (mode : Optimization.Mode) (P : Profile) (host : HostSemantics H) :
    binaryenIR mode P host ⟶ coreIR mode P host where
  run := BModule.lower
  inv_run valid := valid
  sound {_} _ := ExportCorrect.refl mode P host _

/-- The existing structured lift is syntax-preserving after lowering. This
requires no numerical determinism or restriction on the host. -/
def lift (mode : Optimization.Mode) (P : Profile) (host : HostSemantics H) :
    coreIR mode P host ⟶ binaryenIR mode P host where
  run := Exe.structuredLift
  inv_run {x} valid := by
    change ModuleValid (Exe.structuredLift x).lower
    simpa only [Exe.structuredLift_lower] using valid
  sound {x} _ := by
    change ExportCorrect mode P host x (Exe.structuredLift x).lower
    rw [Exe.structuredLift_lower]
    exact ExportCorrect.refl mode P host x

@[simp] theorem lift_lower_run (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) (m : Module) :
    Translation.run (lift mode P host ≫ lower mode P host) m = m :=
  Exe.structuredLift_lower m

/-- Rebuilding Binaryen syntax need not return the same tree, but its Core
denotation is exactly unchanged. No inverse-on-syntax claim is made. -/
@[simp] theorem lower_lift_den (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) (m : BModule) :
    (binaryenIR mode P host).den
        (Translation.run (lower mode P host ≫ lift mode P host) m) = m.lower :=
  Exe.structuredLift_lower m.lower

theorem lower_lift_le_id (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) :
    HomLe (lower mode P host ≫ lift mode P host) (𝟙 (binaryenIR mode P host)) := by
  intro m _
  change ExportCorrect mode P host (Exe.structuredLift m.lower).lower m.lower
  rw [Exe.structuredLift_lower]
  exact ExportCorrect.refl mode P host m.lower

theorem id_le_lower_lift (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) :
    HomLe (𝟙 (binaryenIR mode P host)) (lower mode P host ≫ lift mode P host) := by
  intro m _
  change ExportCorrect mode P host m.lower (Exe.structuredLift m.lower).lower
  rw [Exe.structuredLift_lower]
  exact ExportCorrect.refl mode P host m.lower

end Silmaril.Wasm.Binaryen.Modes
