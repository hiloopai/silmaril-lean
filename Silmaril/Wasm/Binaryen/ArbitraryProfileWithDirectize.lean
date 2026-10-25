module

public import Silmaril.Wasm.Binaryen.ArbitraryProfileWithGlobals
public import Silmaril.Wasm.Binaryen.PassAPI.DirectizeProfile

@[expose] public section

/-! # Twelve-pass cleanup at every numerical profile

The existing eleven-pass executable is followed by the full existing Directize
transformation, including ordinary and tail-call indirect-call sites. These are
eleven of the fifteen default transforms plus the separate RUME stage. The
invariant is module validity and the host is closed. Every stage retains its
existing filters and identity fallbacks. Earlier pipelines and the default
executable remain unchanged.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- Losslessly reuse the full profile-generic pass through the shared API. -/
def directizeP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  (PassAPI.directizeProfileP P H).toShared

@[simp] theorem directizeP_run (P : Profile) :
    (directizeP (H := H) P).run = directize := rfl

/-- The eleven existing stages followed by the complete existing Directize pass. -/
def cleanupWithDirectizeP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  cleanupWithGlobalsP P * directizeP P

def cleanupWithDirectize (m : BModule) : BModule := directize (cleanupWithGlobals m)

@[simp] theorem cleanupWithDirectizeP_run (P : Profile) :
    (cleanupWithDirectizeP (H := H) P).run = cleanupWithDirectize := by
  funext m
  change (cleanupWithGlobalsP P * directizeP P).run m = cleanupWithDirectize m
  rw [Silmaril.Compile.PassAPI.Pass.mul_run, cleanupWithGlobalsP_run, directizeP_run]
  rfl

/-- Exact closed-host export equivalence at the same arbitrary profile, with
validity retained. No numerical determinism premise is required. -/
theorem cleanupWithDirectize_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (cleanupWithDirectize m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithDirectize m).lower m.lower := by
  have hv : ((cleanupWithDirectizeP (H := H) P).run m).Ok :=
    (cleanupWithDirectizeP (H := H) P).inv_run hm
  have he : ExportEquiv (· = ·) P (closedHost (H := H))
      ((cleanupWithDirectizeP (H := H) P).run m).lower m.lower :=
    (cleanupWithDirectizeP (H := H) P).sound hm
  simpa only [cleanupWithDirectizeP_run] using And.intro hv he

/-- Any finite number of twelve-stage rounds retains the exact same numerical
profile and closed-host contract. -/
theorem cleanupWithDirectize_iterate_sound (P : Profile) (rounds : Nat)
    {m : BModule} (hm : m.Ok) :
    (cleanupWithDirectize^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        (cleanupWithDirectize^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (cleanupWithDirectizeP (H := H) P) rounds
  rw [cleanupWithDirectizeP_run] at hrun
  have result : ((cleanupWithDirectizeP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupWithDirectizeP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(cleanupWithDirectizeP (H := H) P ^ rounds).inv_run hm,
      (cleanupWithDirectizeP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
