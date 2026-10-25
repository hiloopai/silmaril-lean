module

public import Silmaril.Wasm.Binaryen.ArbitraryProfileCompiler
public import Silmaril.Wasm.Binaryen.GrowZeroSuccessPass
public import Silmaril.Wasm.Binaryen.GrowOOMPass
public import Silmaril.Wasm.Binaryen.PassAPI.ModeCategory

@[expose] public section

/-! # Feasible refinement in the existing export-observation compiler category

The export language observes positive instantiation admission. Its ordinary
behavioural refinement therefore needs target admission to imply source admission,
whereas `Modes.ExportCorrect .refinement` explicitly supplies the other direction.
The adapter below requires this additional reflection obligation for the actual
pass output; it does not assume it follows from the mode contract or totality.

The existing language, stores, scripts and observations are unchanged. The full
mode certificate, including feasibility, remains available alongside the ordinary
compiler-category view. Trap insertion has a concrete counterexample to ordinary
identity-convention refinement below and is not assigned such an adapter.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile.Compiler

open Execution.Core Numerics Optimization
open Silmaril.Compile
open CategoryTheory

abbrev RefinementPass (P : Profile) (H : Type) :=
  Silmaril.Compile.PassAPI.Pass (Modes.contract .refinement P (closedHost (H := H)))

/-- Reflection of positive instantiation admission in every valid ambient store.
This is the direction not supplied by the source-first refinement mode. -/
def AdmissionReflects (P : Profile) (H : Type) (source target : BModule) : Prop :=
  ∀ s imports, StoreOk s →
    Modes.Instantiates P (closedHost (H := H)) s imports target.lower →
      Modes.Instantiates P (closedHost (H := H)) s imports source.lower

theorem AdmissionReflects.trans {P : Profile} {H : Type} {a b c : BModule}
    (hab : AdmissionReflects P H a b) (hbc : AdmissionReflects P H b c) :
    AdmissionReflects P H a c := fun s imports hs hc => hab s imports hs (hbc s imports hs hc)

/-- Session safety and admission reflection imply ordinary behavioural
refinement of the existing language. The feasibility obligation is retained
separately by the stronger mode certificate. -/
theorem refinement_beh_subset {P : Profile} {H : Type} {source target : BModule}
    (correct : Modes.ExportCorrect .refinement P (closedHost (H := H))
      source.lower target.lower)
    (reflects : AdmissionReflects P H source target) :
    (Exe.CompilerPass.exportLanguage P (closedHost (H := H))).beh target ⊆
      (Exe.CompilerPass.exportLanguage P (closedHost (H := H))).beh source := by
  intro observation observed
  cases observation with
  | instantiates s imports => exact ⟨observed.1, reflects s imports observed.1 observed.2⟩
  | session s imports script outcomes =>
    exact ⟨observed.1, (correct.observations s imports script observed.1).1 observed.2⟩

/-- Admission reflection for the actual execution of a shared refinement pass. -/
def PassAdmissionReflects {P : Profile} {H : Type} (pass : RefinementPass P H) : Prop :=
  ∀ {m : BModule}, m.Ok → AdmissionReflects P H m (pass.run m)

theorem passAdmissionReflects_mul {P : Profile} {H : Type}
    {first second : RefinementPass P H}
    (firstReflects : PassAdmissionReflects first)
    (secondReflects : PassAdmissionReflects second) : PassAdmissionReflects (first * second) := by
  intro m valid
  exact (firstReflects valid).trans (secondReflects (first.inv_run valid))

/-- The same shared pass, as an ordinary endomorphism, with its additional
admission-reflection premise explicit. Validity alone defines the program subtype. -/
def ofRefinementPass {P : Profile} {H : Type} (pass : RefinementPass P H)
    (reflects : PassAdmissionReflects pass) : Category.EndoPass (language P H) where
  run m := ⟨pass.run m.val, pass.inv_run m.property⟩
  refines m := ⟨rfl, refinement_beh_subset (pass.sound m.property) (reflects m.property)⟩

@[simp] theorem ofRefinementPass_run_val {P : Profile} {H : Type}
    (pass : RefinementPass P H) (reflects : PassAdmissionReflects pass)
    (m : (language P H).Prog) :
    ((ofRefinementPass pass reflects).run m).val = pass.run m.val := rfl

/-- The ordinary export-language adapter and the mode-indexed IR category
retain the same transformation. Only the former needs admission reflection. -/
theorem ofRefinementPass_mode_run {P : Profile} {H : Type}
    (pass : RefinementPass P H) (reflects : PassAdmissionReflects pass)
    (m : (language P H).Prog) :
    ((ofRefinementPass pass reflects).run m).val =
      Silmaril.Compile.PassAPI.Translation.run (Modes.ofModePass pass) m.val := rfl

/-- The original full mode certificate survives the compiler-category adapter. -/
theorem ofRefinementPass_correct {P : Profile} {H : Type}
    (pass : RefinementPass P H) (reflects : PassAdmissionReflects pass)
    (m : (language P H).Prog) :
    Modes.ExportCorrect .refinement P (closedHost (H := H)) m.val.lower
      ((ofRefinementPass pass reflects).run m).val.lower := pass.sound m.property

/-- Observation existence remains part of the guarantee, even though ordinary
set-inclusion refinement alone would permit an empty target behaviour set. -/
theorem ofRefinementPass_feasible {P : Profile} {H : Type}
    (pass : RefinementPass P H) (reflects : PassAdmissionReflects pass)
    (m : (language P H).Prog) (s : Store H) (imports : List ExternAddr)
    (script : List Call) (validStore : StoreOk s) :
    Feasible (moduleObs P closedHost s imports m.val.lower script)
      (moduleObs P closedHost s imports ((ofRefinementPass pass reflects).run m).val.lower script) :=
  ((ofRefinementPass_correct pass reflects m).observations s imports script validStore).2

/-- Ordinary specifications over the unchanged export observations transport
forwards. Refinement does not claim the converse satisfaction implication. -/
theorem ofRefinementPass_sat {P : Profile} {H : Type}
    (pass : RefinementPass P H) (reflects : PassAdmissionReflects pass)
    (m : (language P H).Prog) (specification : Set (language P H).Obs) :
    (language P H).Sat m specification →
      (language P H).Sat ((ofRefinementPass pass reflects).run m) specification :=
  Category.Language.Refines.sat ((ofRefinementPass pass reflects).refines m)

/-- Shared pass composition and compiler-category composition run the same
left-to-right functions, retaining both mode and reflection obligations. -/
theorem ofRefinementPass_mul {P : Profile} {H : Type}
    (first second : RefinementPass P H)
    (firstReflects : PassAdmissionReflects first)
    (secondReflects : PassAdmissionReflects second) :
    ofRefinementPass (first * second) (passAdmissionReflects_mul firstReflects secondReflects) =
      ofRefinementPass first firstReflects * ofRefinementPass second secondReflects := by
  apply Category.EndoPass.ext
  funext m
  apply Subtype.ext
  rfl

/-- The actual zero-growth recognizer retains admission in both directions.
This uses exact recognized modules and instantiation inversion, not progress or
the existence of a session in an arbitrary host environment. -/
theorem zeroGrowSuccess_admissionReflects (P : Profile) (H : Type) (m : BModule) :
    AdmissionReflects P H m (GrowZeroSuccess.optimize m) := by
  intro s imports _ ⟨c, instantiated⟩
  cases recognized : GrowZeroSuccess.recognize? m.lower with
  | none =>
    rw [GrowZeroSuccess.optimize_of_rejected recognized] at instantiated
    exact ⟨c, instantiated⟩
  | some a =>
    have actual : Instantiate P closedHost s (GrowZeroSuccess.mod a) imports c := by
      simpa [GrowZeroSuccess.optimize, recognized, lower_lift] using instantiated
    obtain ⟨rfl, _⟩ := GrowZeroSuccess.instantiate_inv actual
    rw [GrowZeroSuccess.recognize?_sound recognized]
    exact ⟨GrowOOM.initial s a, GrowOOM.instantiate s a⟩

/-- The actual optional-trap-removing selector as a compiler endomorphism.
The numerical profile need only permit successful zero growth; host state is arbitrary. -/
def zeroGrowSuccessEndo_of_success (P : Profile) (H : Type)
    (success : GrowZeroSuccess.ZeroGrowSuccess P) : Category.EndoPass (language P H) :=
  ofRefinementPass (GrowZeroSuccess.refinementP_of_success P success)
    (fun {_} _ => zeroGrowSuccess_admissionReflects P H _)

@[simp] theorem zeroGrowSuccessEndo_of_success_run_val (P : Profile) (H : Type)
    (success : GrowZeroSuccess.ZeroGrowSuccess P) (m : (language P H).Prog) :
    ((zeroGrowSuccessEndo_of_success P H success).run m).val = GrowZeroSuccess.optimize m.val := rfl

theorem zeroGrowSuccessEndo_of_success_correct (P : Profile) (H : Type)
    (success : GrowZeroSuccess.ZeroGrowSuccess P) (m : (language P H).Prog) :
    Modes.ExportCorrect .refinement P (closedHost (H := H)) m.val.lower
      ((zeroGrowSuccessEndo_of_success P H success).run m).val.lower :=
  ofRefinementPass_correct _ _ m

def zeroGrowSuccessEndo (H : Type) (nd : Bool := true) (r : RelaxedChoice := {}) :
    Category.EndoPass (language (Profile.spec nd r) H) :=
  zeroGrowSuccessEndo_of_success _ H (GrowZeroSuccess.zeroGrowSuccess_spec nd r)

def zeroGrowSuccessCompiler (H : Type) (nd : Bool := true) (r : RelaxedChoice := {}) :
    Category.Compiler (language (Profile.spec nd r) H) (language (Profile.spec nd r) H) :=
  (zeroGrowSuccessEndo H nd r).toPass.toCompiler

@[simp] theorem zeroGrowSuccessCompiler_conv (H : Type) (nd : Bool) (r : RelaxedChoice) :
    (zeroGrowSuccessCompiler H nd r).conv = 𝟙 (language (Profile.spec nd r) H) := rfl

theorem zeroGrowSuccessCompiler_run (H : Type) (nd : Bool) (r : RelaxedChoice)
    (m : (language (Profile.spec nd r) H).Prog) :
    ((zeroGrowSuccessCompiler H nd r).run m).map Subtype.val =
      some (GrowZeroSuccess.optimize m.val) := rfl

/-- This category instance changes a valid source with a genuine trapping run
into an output with an actual zero return and no corresponding trapping run. -/
theorem zeroGrowSuccessEndo_witness (H : Type) (nd : Bool) (r : RelaxedChoice) (a : AddrType) :
    ∃ m : (language (Profile.spec nd r) H).Prog,
      [.returns [], .traps] ∈ moduleObs (Profile.spec nd r) (closedHost (H := H)) {} [] m.val.lower
        [("grow", [])] ∧
      [.returns [], .traps] ∉ moduleObs (Profile.spec nd r) (closedHost (H := H)) {} []
        ((zeroGrowSuccessEndo H nd r).run m).val.lower [("grow", [])] ∧
      [.returns [], .returns [MemoryGrowFailure.addrVal a 0]] ∈
        moduleObs (Profile.spec nd r) (closedHost (H := H)) {} []
          ((zeroGrowSuccessEndo H nd r).run m).val.lower [("grow", [])] := by
  let m : (language (Profile.spec nd r) H).Prog :=
    ⟨BModule.lift (GrowOOM.mod a), by
      change ∃ t, Validation.ModuleOk (BModule.lift (GrowOOM.mod a)).lower t
      rw [lower_lift]
      exact ⟨_, GrowOOM.module_ok a⟩⟩
  have output : ((zeroGrowSuccessEndo H nd r).run m).val.lower = GrowZeroSuccess.mod a := by
    change (GrowZeroSuccess.optimize (BModule.lift (GrowOOM.mod a))).lower = _
    rw [GrowZeroSuccess.optimize_guarded_wrapper, lower_lift]
  refine ⟨m, ?_, ?_, ?_⟩
  · simpa only [m, lower_lift] using GrowZeroSuccess.failure_observation (H := H) a nd r
  · rw [output]
    exact GrowZeroSuccess.target_not_trap a _
  · rw [output]
    exact GrowZeroSuccess.success_observation a _

/-- Fatal-OOM insertion is certified in its own mode, but is not ordinary
refinement of the current raw export-observation language. -/
theorem trapInsertion_not_raw_refinement (H : Type) (a : AddrType) :
    Modes.ExportCorrect .trapInsertion (Profile.spec true {}) (closedHost (H := H))
        (GrowWrapper.mod a 0 false) (GrowOOM.mod a) ∧
      ¬ (Exe.CompilerPass.exportLanguage (Profile.spec true {}) (closedHost (H := H))).Refines
        (BModule.lift (GrowWrapper.mod a 0 false)) (BModule.lift (GrowOOM.mod a)) := by
  refine ⟨GrowOOM.exportCorrect a, ?_⟩
  intro refines
  have observed :
      (Exe.CompilerPass.Observation.session ({} : Store H) [] [("grow", [])]
        [.returns [], .traps]) ∈
          (Exe.CompilerPass.exportLanguage (Profile.spec true {}) closedHost).beh
            (BModule.lift (GrowOOM.mod a)) :=
    ⟨LoopCex.storeOk_empty, by simpa only [lower_lift] using GrowOOM.failure_observation (H := H) a⟩
  have original := refines.2 observed
  exact GrowOOM.source_not_trap a _ (by simpa only [lower_lift] using original.2)

end Silmaril.Wasm.Binaryen.ArbitraryProfile.Compiler
