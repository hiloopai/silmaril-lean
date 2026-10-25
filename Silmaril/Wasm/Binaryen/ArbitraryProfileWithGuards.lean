module

public import Silmaril.Wasm.Binaryen.ArbitraryProfileWithSelect
public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardAny

@[expose] public section

/-! # Ten-pass cleanup at every numerical profile

Compose the exact existing nine-pass executable with checked recursive
guard inversion. All acceptance guards remain active. The old four/five/eight/nine-pass
APIs and the default executable/byte contract retain their definitions.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- The actual checked guard-inversion executable with its validator fallback. -/
def invertGuardsCheckedP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := invertGuardsChecked
  inv_run hm := (GuardSim.invertGuardsChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (GuardSim.invertGuardsChecked_sound_any hm).2

/-- The existing exact nine-pass run followed by checked guard inversion: ten
stages in total, including the separate RUME stage. -/
def cleanupWithGuardsP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  cleanupWithSelectP P * invertGuardsCheckedP P

def cleanupWithGuards (m : BModule) : BModule :=
  invertGuardsChecked (cleanupWithSelect m)

@[simp] theorem cleanupWithGuardsP_run (P : Profile) :
    (cleanupWithGuardsP (H := H) P).run = cleanupWithGuards := by
  funext m
  change (cleanupWithSelectP P * invertGuardsCheckedP P).run m = cleanupWithGuards m
  rw [Silmaril.Compile.PassAPI.Pass.mul_run, cleanupWithSelectP_run]
  rfl

/-- The ten-pass output is valid and exactly export-equivalent at the same
arbitrary numerical profile under the closed host. -/
theorem cleanupWithGuards_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (cleanupWithGuards m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithGuards m).lower m.lower :=
  by
    have hv : ((cleanupWithGuardsP (H := H) P).run m).Ok :=
      (cleanupWithGuardsP (H := H) P).inv_run hm
    have he : ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupWithGuardsP (H := H) P).run m).lower m.lower :=
      (cleanupWithGuardsP (H := H) P).sound hm
    simpa only [cleanupWithGuardsP_run] using And.intro hv he

/-- Any finite number of ten-pass rounds retains the exact same profile and host. -/
theorem cleanupWithGuards_iterate_sound (P : Profile) (rounds : Nat) {m : BModule} (hm : m.Ok) :
    (cleanupWithGuards^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithGuards^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (cleanupWithGuardsP (H := H) P) rounds
  rw [cleanupWithGuardsP_run] at hrun
  have result : ((cleanupWithGuardsP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupWithGuardsP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(cleanupWithGuardsP (H := H) P ^ rounds).inv_run hm,
      (cleanupWithGuardsP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
