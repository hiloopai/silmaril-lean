module

public import Silmaril.Wasm.Binaryen.ArbitraryProfilePipeline
public import Silmaril.Wasm.Binaryen.ConstSelectAny

@[expose] public section

/-! # Nine-pass cleanup at every numerical profile

Compose the exact existing eight-pass executable with checked recursive
ConstSelect. All acceptance guards remain active. The old four/five/eight-pass
APIs and the default executable/byte contract retain their definitions.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- The actual checked ConstSelect executable with its existing guards. -/
def constSelectCheckedP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := ConstSelect.constSelectChecked
  inv_run hm := (ConstSelect.constSelectChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (ConstSelect.constSelectChecked_sound_any hm).2

/-- The existing exact eight-pass run followed by checked ConstSelect: nine
stages in total, including the separate RUME stage. -/
def cleanupWithSelectP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  extendedCleanupP P * constSelectCheckedP P

def cleanupWithSelect (m : BModule) : BModule :=
  ConstSelect.constSelectChecked (extendedCleanup m)

@[simp] theorem cleanupWithSelectP_run (P : Profile) :
    (cleanupWithSelectP (H := H) P).run = cleanupWithSelect := rfl

/-- The nine-pass output is valid and exactly export-equivalent at the same
arbitrary numerical profile under the closed host. -/
theorem cleanupWithSelect_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (cleanupWithSelect m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithSelect m).lower m.lower :=
  by
    have hv : ((cleanupWithSelectP (H := H) P).run m).Ok :=
      (cleanupWithSelectP (H := H) P).inv_run hm
    have he : ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupWithSelectP (H := H) P).run m).lower m.lower :=
      (cleanupWithSelectP (H := H) P).sound hm
    simpa only [cleanupWithSelectP_run] using And.intro hv he

/-- Any finite number of nine-pass rounds retains the exact same profile and host. -/
theorem cleanupWithSelect_iterate_sound (P : Profile) (rounds : Nat) {m : BModule} (hm : m.Ok) :
    (cleanupWithSelect^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithSelect^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (cleanupWithSelectP (H := H) P) rounds
  rw [cleanupWithSelectP_run] at hrun
  have result : ((cleanupWithSelectP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupWithSelectP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(cleanupWithSelectP (H := H) P ^ rounds).inv_run hm,
      (cleanupWithSelectP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
