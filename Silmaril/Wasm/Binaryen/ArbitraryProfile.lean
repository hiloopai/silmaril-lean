module

public import Silmaril.Wasm.Binaryen.PassAPI.Instances
public import Silmaril.Wasm.Binaryen.PassAPI.Shared
public import Silmaril.Wasm.Binaryen.Pass.DCECheck
public import Silmaril.Wasm.Binaryen.VacuumLiteSim
public import Silmaril.Wasm.Binaryen.PrecomputeLiteSim
public import Silmaril.Wasm.Binaryen.Pass.RUME

@[expose] public section

/-!
# A cleanup pipeline with exact equivalence at every numerical profile

The existing DCE, anchored vacuum and anchored integer-addition precompute
proofs hold for arbitrary profiles and code-parametric hosts. RUME holds for
arbitrary profiles under the closed host. Package these results as shared
passes and compose them without imposing the executable pipeline's
deterministic numerical profile or its syntactic profile check.

The invariant is module validity alone. Individual transformations retain
their existing applicability tests and identity fallbacks. This is a
separate four-pass pipeline; it does not generalize the complete executable
pipeline, whose other stages have stronger semantic hypotheses.

Each result is exact export equivalence for the *same* profile on both
sides. It is not obtained by turning deterministic-profile correctness into
spec-profile correctness, nor by weakening equivalence to refinement.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type}

/-- Shared passes retaining the existing exact export-equivalence contract,
with module validity as their only invariant. -/
abbrev EquivPass (P : Profile) (host : HostSemantics H) :=
  Silmaril.Compile.PassAPI.Pass (PassAPI.equivContract P host).toShared

/-- Checked dead-suffix elimination, with no deterministic-profile assumption. -/
def dceP (P : Profile) (host : HostSemantics H) (hhost : Sim.HostParametric host) :
    EquivPass P host where
  run := dceChecked
  inv_run := dceChecked_ok
  sound hm := dceChecked_sound hm host hhost

/-- Anchored removal of `nop` and discarded constants at every profile. -/
def vacuumP (P : Profile) (host : HostSemantics H) (hhost : Sim.HostParametric host) :
    EquivPass P host where
  run := VacuumLite.vacuumLite
  inv_run := VacuumLite.vacuumLite_ok
  sound hm := VacuumLite.vacuumLite_sound hm host hhost

/-- Anchored integer-addition precomputation at every profile. This does not
claim equivalence for canonicalizing nondeterministic floating-point results. -/
def precomputeP (P : Profile) (host : HostSemantics H)
    (hhost : Sim.HostParametric host) : EquivPass P host where
  run := PrecomputeLite.precomputeLite
  inv_run := PrecomputeLite.precomputeLite_ok
  sound hm := PrecomputeLite.precomputeLite_sound hm host hhost

/-- RUME retains its existing syntactic applicability check; the numerical
profile may be arbitrary. Its host remains closed. -/
def rumeP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := rume
  inv_run := rume_valid
  sound hm := rume_sound hm P

/-- The three local passes, in execution order. -/
def localCleanupP (P : Profile) (host : HostSemantics H)
    (hhost : Sim.HostParametric host) : EquivPass P host :=
  dceP P host hhost * vacuumP P host hhost * precomputeP P host hhost

/-- The actual executable function of the three-pass pipeline. -/
def localCleanup (m : BModule) : BModule :=
  PrecomputeLite.precomputeLite (VacuumLite.vacuumLite (dceChecked m))

@[simp] theorem localCleanupP_run (P : Profile) (host : HostSemantics H)
    (hhost : Sim.HostParametric host) :
    (localCleanupP P host hhost).run = localCleanup := rfl

/-- The shared pass monoid supplies validity and exact equivalence for any
numerical profile and any code-parametric host. -/
theorem localCleanup_sound (P : Profile) (host : HostSemantics H)
    (hhost : Sim.HostParametric host) {m : BModule} (hm : m.Ok) :
    (localCleanup m).Ok ∧ ExportEquiv (· = ·) P host (localCleanup m).lower m.lower :=
  ⟨(localCleanupP P host hhost).inv_run hm, (localCleanupP P host hhost).sound hm⟩

/-- The local cleanup followed by RUME, with exact closed-host equivalence. -/
def cleanupP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  localCleanupP P closedHost closedHost_codeParametric * rumeP P

/-- A four-pass executable independent of any numerical-profile parameter. -/
def cleanup (m : BModule) : BModule := rume (localCleanup m)

@[simp] theorem cleanupP_run (P : Profile) :
    (cleanupP (H := H) P).run = cleanup := rfl

/-- The four-pass cleanup is valid and exactly export-equivalent at every
profile, including profiles with per-operation nondeterminism. -/
theorem cleanup_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (cleanup m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanup m).lower m.lower :=
  ⟨(cleanupP (H := H) P).inv_run hm, (cleanupP (H := H) P).sound hm⟩

/-- Any number of cleanup rounds is sound by the same pass monoid. -/
theorem cleanup_iterate_sound (P : Profile) (rounds : Nat) {m : BModule} (hm : m.Ok) :
    (cleanup^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (cleanup^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (cleanupP (H := H) P) rounds
  rw [cleanupP_run] at hrun
  have result : ((cleanupP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(cleanupP (H := H) P ^ rounds).inv_run hm,
      (cleanupP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
