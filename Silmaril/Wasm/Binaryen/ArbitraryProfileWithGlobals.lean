module

public import Silmaril.Wasm.Binaryen.ArbitraryProfileWithGuards
public import Silmaril.Wasm.Binaryen.PassAPI.SimplifyGlobalsProfile

@[expose] public section

/-! # Eleven-pass cleanup at every numerical profile

The existing ten-pass executable is followed by the full existing immutable
integer-global substitution pass. The invariant is module validity and the
host is closed. Every stage retains its existing filters and identity
fallbacks. Earlier pipelines and the default executable remain unchanged.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- Losslessly reuse the full profile-generic pass through the shared API. -/
def simplifyGlobalsP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  (PassAPI.simplifyGlobalsProfileP P H).toShared

@[simp] theorem simplifyGlobalsP_run (P : Profile) :
    (simplifyGlobalsP (H := H) P).run = simplifyGlobals := rfl

/-- The ten existing stages followed by full immutable integer-global substitution. -/
def cleanupWithGlobalsP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  cleanupWithGuardsP P * simplifyGlobalsP P

def cleanupWithGlobals (m : BModule) : BModule := simplifyGlobals (cleanupWithGuards m)

@[simp] theorem cleanupWithGlobalsP_run (P : Profile) :
    (cleanupWithGlobalsP (H := H) P).run = cleanupWithGlobals := by
  funext m
  change (cleanupWithGuardsP P * simplifyGlobalsP P).run m = cleanupWithGlobals m
  rw [Silmaril.Compile.PassAPI.Pass.mul_run, cleanupWithGuardsP_run, simplifyGlobalsP_run]
  rfl

/-- Exact closed-host export equivalence at the same arbitrary profile, with
validity retained. No numerical determinism premise is required. -/
theorem cleanupWithGlobals_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (cleanupWithGlobals m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithGlobals m).lower m.lower := by
  have hv : ((cleanupWithGlobalsP (H := H) P).run m).Ok :=
    (cleanupWithGlobalsP (H := H) P).inv_run hm
  have he : ExportEquiv (· = ·) P (closedHost (H := H))
      ((cleanupWithGlobalsP (H := H) P).run m).lower m.lower :=
    (cleanupWithGlobalsP (H := H) P).sound hm
  simpa only [cleanupWithGlobalsP_run] using And.intro hv he

/-- Any finite number of eleven-stage rounds retains the exact same numerical
profile and closed-host contract. -/
theorem cleanupWithGlobals_iterate_sound (P : Profile) (rounds : Nat)
    {m : BModule} (hm : m.Ok) :
    (cleanupWithGlobals^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        (cleanupWithGlobals^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (cleanupWithGlobalsP (H := H) P) rounds
  rw [cleanupWithGlobalsP_run] at hrun
  have result : ((cleanupWithGlobalsP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupWithGlobalsP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(cleanupWithGlobalsP (H := H) P ^ rounds).inv_run hm,
      (cleanupWithGlobalsP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
