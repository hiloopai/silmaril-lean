module

public import Silmaril.Wasm.Binaryen.Exe.CompilerPass
public import Silmaril.Wasm.Binaryen.ArbitraryProfileAllFunctions
public import Silmaril.Wasm.Binaryen.Exe.SelectedCleanupSound

@[expose] public section

/-! # Arbitrary-profile Wasm cleanup in the existing compiler category

The semantic language and observation type are the existing export-session
language, including instantiation admissibility and the initial environment.
Only the input invariant changes from the old executable profile to validity.
This adapter retains the exact source contract and executable function; it
does not identify an arbitrary preorder with behavioural refinement.

These are ordinary compiler-category endomorphisms and can compose with
certified translations to other languages. No Wasm-to-SSA translation or
game-semantics adequacy theorem is asserted by this packaging.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile.Compiler

open Execution.Core Numerics
open Silmaril.Compile
open CategoryTheory

/-- The existing actual Core export-observation language, restricted only to
valid modules, at the same arbitrary numerical profile and closed host. -/
abbrev language (P : Profile) (H : Type) : Category.Language :=
  (Exe.CompilerPass.exportLanguage P (closedHost (H := H))).onInvariant BModule.Ok

/-- An exact arbitrary-profile pass as an ordinary behavioural endomorphism.
The category exposes refinement, while the stronger equivalence stays available. -/
def ofEquivPass {P : Profile} {H : Type} (pass : EquivPass P (closedHost (H := H))) :
    Category.EndoPass (language P H) :=
  Category.EndoPass.ofInvariantPass
    (L := Exe.CompilerPass.exportLanguage P (closedHost (H := H))) pass
    (fun _ equivalent => ⟨rfl, (Exe.CompilerPass.exportEquiv_beh_eq equivalent).subset⟩)

@[simp] theorem ofEquivPass_run_val {P : Profile} {H : Type}
    (pass : EquivPass P (closedHost (H := H))) (m : (language P H).Prog) :
    ((ofEquivPass pass).run m).val = pass.run m.val := rfl

/-- Adapting to the compiler category preserves the complete source relation. -/
theorem ofEquivPass_exportEquiv {P : Profile} {H : Type}
    (pass : EquivPass P (closedHost (H := H))) (m : (language P H).Prog) :
    ExportEquiv (· = ·) P (closedHost (H := H))
      ((ofEquivPass pass).run m).val.lower m.val.lower :=
  pass.sound m.property

/-- Both APIs run their left factor first. -/
@[simp] theorem ofEquivPass_mul {P : Profile} {H : Type}
    (first second : EquivPass P (closedHost (H := H))) :
    ofEquivPass (first * second) = ofEquivPass first * ofEquivPass second := by
  apply Category.EndoPass.ext
  funext m
  apply Subtype.ext
  rfl

/-- All current guarded function stages plus RUME, repeated finitely. -/
def cleanupEndo (P : Profile) (H : Type) (rounds : Nat) :
    Category.EndoPass (language P H) :=
  ofEquivPass (cleanupAllFunctionsP (H := H) P ^ rounds)

/-- The invariant subtype adds no executable transformation. -/
@[simp] theorem cleanupEndo_run_val (P : Profile) (H : Type) (rounds : Nat)
    (m : (language P H).Prog) :
    ((cleanupEndo P H rounds).run m).val = Exe.profileCleanupAllFunctionRound^[rounds] m.val := by
  change ((cleanupAllFunctionsP (H := H) P ^ rounds).run m.val) = _
  rw [Silmaril.Compile.PassAPI.Pass.pow_run, cleanupAllFunctionsP_run]
  rfl

def cleanupPass (P : Profile) (H : Type) (rounds : Nat) :
    Category.Pass (𝟙 (language P H)) := (cleanupEndo P H rounds).toPass

def cleanupCompiler (P : Profile) (H : Type) (rounds : Nat) :
    Category.Compiler (language P H) (language P H) := (cleanupPass P H rounds).toCompiler

/-- Successful compilation is exactly the same finite runtime cleanup. -/
theorem cleanupPass_run (P : Profile) (H : Type) (rounds : Nat)
    (m : (language P H).Prog) :
    ((cleanupPass P H rounds).run m).map Subtype.val =
      some (Exe.profileCleanupAllFunctionRound^[rounds] m.val) := by
  change some (((cleanupEndo P H rounds).run m).val) = _
  exact congrArg some (cleanupEndo_run_val P H rounds m)

/-- No deterministic profile or numerical oracle is introduced by the adapter. -/
theorem cleanupEndo_exportEquiv (P : Profile) (H : Type) (rounds : Nat)
    (m : (language P H).Prog) :
    ExportEquiv (· = ·) P (closedHost (H := H))
      ((cleanupEndo P H rounds).run m).val.lower m.val.lower :=
  ofEquivPass_exportEquiv _ m

theorem cleanupEndo_beh_eq (P : Profile) (H : Type) (rounds : Nat)
    (m : (language P H).Prog) :
    (language P H).beh ((cleanupEndo P H rounds).run m) = (language P H).beh m :=
  Exe.CompilerPass.exportEquiv_beh_eq (cleanupEndo_exportEquiv P H rounds m)

/-- Every specification over the actual export observations is preserved in
both directions; the observation set includes admission and shared-state traces. -/
theorem cleanupEndo_sat_iff (P : Profile) (H : Type) (rounds : Nat)
    (m : (language P H).Prog) (specification : Set (language P H).Obs) :
    (language P H).Sat ((cleanupEndo P H rounds).run m) specification ↔
      (language P H).Sat m specification := by
  change (language P H).beh ((cleanupEndo P H rounds).run m) ⊆ specification ↔
    (language P H).beh m ⊆ specification
  rw [cleanupEndo_beh_eq]

/-- An arbitrary ordered selection, including repeated stages, in the same
compiler category. No extra pass order or profile hypothesis is introduced. -/
def selectedEndo (P : Profile) (H : Type) (stages : List Exe.CleanupStage) (rounds : Nat) :
    Category.EndoPass (language P H) :=
  ofEquivPass (selectedStagesP (H := H) P stages ^ rounds)

@[simp] theorem selectedEndo_run_val (P : Profile) (H : Type)
    (stages : List Exe.CleanupStage) (rounds : Nat) (m : (language P H).Prog) :
    ((selectedEndo P H stages rounds).run m).val =
      (Exe.cleanupSelectedRound stages)^[rounds] m.val := by
  change ((selectedStagesP (H := H) P stages ^ rounds).run m.val) = _
  rw [Silmaril.Compile.PassAPI.Pass.pow_run]
  have run : (selectedStagesP (H := H) P stages).run = Exe.cleanupSelectedRound stages :=
    funext (selectedStagesP_run P stages)
  rw [run]

def selectedCompiler (P : Profile) (H : Type) (stages : List Exe.CleanupStage) (rounds : Nat) :
    Category.Compiler (language P H) (language P H) :=
  (selectedEndo P H stages rounds).toPass.toCompiler

theorem selectedEndo_exportEquiv (P : Profile) (H : Type) (stages : List Exe.CleanupStage)
    (rounds : Nat) (m : (language P H).Prog) :
    ExportEquiv (· = ·) P (closedHost (H := H))
      ((selectedEndo P H stages rounds).run m).val.lower m.val.lower :=
  ofEquivPass_exportEquiv _ m

/-- The validity-only selected pipeline used by the selected byte frontend.
The older output-profile-guarded selected adapters remain available above. -/
def selectedValidEndo (P : Profile) (H : Type) (stages : List Exe.CleanupStage) (rounds : Nat) :
    Category.EndoPass (language P H) :=
  ofEquivPass (selectedValidStagesP (H := H) P stages ^ rounds)

@[simp] theorem selectedValidEndo_run_val (P : Profile) (H : Type)
    (stages : List Exe.CleanupStage) (rounds : Nat) (m : (language P H).Prog) :
    ((selectedValidEndo P H stages rounds).run m).val =
      (Exe.cleanupSelectedValidRound stages)^[rounds] m.val := by
  change ((selectedValidStagesP (H := H) P stages ^ rounds).run m.val) = _
  rw [Silmaril.Compile.PassAPI.Pass.pow_run]
  have run : (selectedValidStagesP (H := H) P stages).run = Exe.cleanupSelectedValidRound stages :=
    funext (selectedValidStagesP_run P stages)
  rw [run]

def selectedValidCompiler (P : Profile) (H : Type) (stages : List Exe.CleanupStage) (rounds : Nat) :
    Category.Compiler (language P H) (language P H) :=
  (selectedValidEndo P H stages rounds).toPass.toCompiler

theorem selectedValidEndo_exportEquiv (P : Profile) (H : Type) (stages : List Exe.CleanupStage)
    (rounds : Nat) (m : (language P H).Prog) :
    ExportEquiv (· = ·) P (closedHost (H := H))
      ((selectedValidEndo P H stages rounds).run m).val.lower m.val.lower :=
  ofEquivPass_exportEquiv _ m

end Silmaril.Wasm.Binaryen.ArbitraryProfile.Compiler
