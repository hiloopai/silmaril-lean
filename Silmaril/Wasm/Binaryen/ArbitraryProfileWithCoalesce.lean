module

public import Silmaril.Wasm.Binaryen.ArbitraryProfileWithDirectize
public import Silmaril.Wasm.Binaryen.PassAPI.CoalesceLocalsProfile

@[expose] public section

/-! # Thirteen-pass cleanup at every numerical profile

The existing twelve-stage pipeline is followed by the unchanged overwrite-anchored
CoalesceLocals-lite transform. These are twelve of the fifteen default function
transforms plus the separate RUME stage. The invariant is module validity and the
host is closed. Every stage retains its existing filters and identity fallbacks.
Earlier pipelines and the default executable remain unchanged.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- Losslessly reuse the full profile-generic pass through the shared API. -/
def coalesceLocalsP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  (PassAPI.coalesceLocalsProfileP P H).toShared

@[simp] theorem coalesceLocalsP_run (P : Profile) :
    (coalesceLocalsP (H := H) P).run = CoalesceLocalsLite.deadSetLite := rfl

/-- The twelve existing stages followed by the exact overwrite-anchored dead-store pass. -/
def cleanupWithCoalesceP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  cleanupWithDirectizeP P * coalesceLocalsP P

def cleanupWithCoalesce (m : BModule) : BModule := CoalesceLocalsLite.deadSetLite (cleanupWithDirectize m)

@[simp] theorem cleanupWithCoalesceP_run (P : Profile) :
    (cleanupWithCoalesceP (H := H) P).run = cleanupWithCoalesce := by
  funext m
  change (cleanupWithDirectizeP P * coalesceLocalsP P).run m = cleanupWithCoalesce m
  rw [Silmaril.Compile.PassAPI.Pass.mul_run, cleanupWithDirectizeP_run, coalesceLocalsP_run]
  rfl

/-- Exact closed-host export equivalence at the same arbitrary profile, with
validity retained. No numerical determinism premise is required. -/
theorem cleanupWithCoalesce_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (cleanupWithCoalesce m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithCoalesce m).lower m.lower := by
  have hv : ((cleanupWithCoalesceP (H := H) P).run m).Ok :=
    (cleanupWithCoalesceP (H := H) P).inv_run hm
  have he : ExportEquiv (· = ·) P (closedHost (H := H))
      ((cleanupWithCoalesceP (H := H) P).run m).lower m.lower :=
    (cleanupWithCoalesceP (H := H) P).sound hm
  simpa only [cleanupWithCoalesceP_run] using And.intro hv he

/-- Any finite number of thirteen-stage rounds retains the exact same numerical
profile and closed-host contract. -/
theorem cleanupWithCoalesce_iterate_sound (P : Profile) (rounds : Nat)
    {m : BModule} (hm : m.Ok) :
    (cleanupWithCoalesce^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        (cleanupWithCoalesce^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (cleanupWithCoalesceP (H := H) P) rounds
  rw [cleanupWithCoalesceP_run] at hrun
  have result : ((cleanupWithCoalesceP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupWithCoalesceP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(cleanupWithCoalesceP (H := H) P ^ rounds).inv_run hm,
      (cleanupWithCoalesceP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
