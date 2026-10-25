module

public import Silmaril.Wasm.Binaryen.ArbitraryProfile
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteAny

@[expose] public section

/-! # A five-pass arbitrary-profile cleanup including tee/drop

The separately named `cleanupWithTee` runs the existing three local cleanup
passes, full recursive tee/drop, then RUME. It preserves exact export equivalence
at the same arbitrary numerical profile under the closed host. Its four local
passes additionally compose under every code-parametric host. Existing
`ArbitraryProfile.cleanup` remains the original four-pass function.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- Full recursive tee/drop, preserving its existing scalar/SIMD-local filter. -/
def teeDropP (P : Profile) (host : HostSemantics H) (hhost : Sim.HostParametric host) :
    EquivPass P host where
  run := SimplifyLocalsLite.teeDrop
  inv_run := SimplifyLocalsLite.teeDrop_ok
  sound hm := SimplifyLocalsLite.teeDrop_sound_parametric hm host hhost

/-- DCE, anchored vacuum, anchored integer precomputation, then tee/drop. -/
def localCleanupWithTeeP (P : Profile) (host : HostSemantics H)
    (hhost : Sim.HostParametric host) : EquivPass P host :=
  localCleanupP P host hhost * teeDropP P host hhost

/-- The four local transformations as an executable function. -/
def localCleanupWithTee (m : BModule) : BModule :=
  SimplifyLocalsLite.teeDrop (localCleanup m)

@[simp] theorem localCleanupWithTeeP_run (P : Profile) (host : HostSemantics H)
    (hhost : Sim.HostParametric host) :
    (localCleanupWithTeeP P host hhost).run = localCleanupWithTee := rfl

/-- Four local passes preserve exact equivalence under any code-parametric host. -/
theorem localCleanupWithTee_sound (P : Profile) (host : HostSemantics H)
    (hhost : Sim.HostParametric host) {m : BModule} (hm : m.Ok) :
    (localCleanupWithTee m).Ok ∧
      ExportEquiv (· = ·) P host (localCleanupWithTee m).lower m.lower :=
  ⟨(localCleanupWithTeeP P host hhost).inv_run hm,
    (localCleanupWithTeeP P host hhost).sound hm⟩

/-- The five-pass cleanup retains RUME's closed-host contract and applicability test. -/
def cleanupWithTeeP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  localCleanupWithTeeP P closedHost closedHost_codeParametric * rumeP P

/-- A separately named five-pass executable; the existing four-pass `cleanup` is unchanged. -/
def cleanupWithTee (m : BModule) : BModule := rume (localCleanupWithTee m)

@[simp] theorem cleanupWithTeeP_run (P : Profile) :
    (cleanupWithTeeP (H := H) P).run = cleanupWithTee := rfl

/-- Five-pass cleanup is valid and exactly export-equivalent at every numerical profile. -/
theorem cleanupWithTee_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (cleanupWithTee m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithTee m).lower m.lower :=
  ⟨(cleanupWithTeeP (H := H) P).inv_run hm, (cleanupWithTeeP (H := H) P).sound hm⟩

/-- Any number of five-pass rounds retains the same exact profile and host contract. -/
theorem cleanupWithTee_iterate_sound (P : Profile) (rounds : Nat) {m : BModule} (hm : m.Ok) :
    (cleanupWithTee^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanupWithTee^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (cleanupWithTeeP (H := H) P) rounds
  rw [cleanupWithTeeP_run] at hrun
  have result : ((cleanupWithTeeP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupWithTeeP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(cleanupWithTeeP (H := H) P ^ rounds).inv_run hm,
      (cleanupWithTeeP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
