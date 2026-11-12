module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Thms

/-!
# Round 7, memory SIMD: preservation of `NoMemSimd` by Core steps

`Round7.VInv.NoMSDom` asks for the absence of memory SIMD code in the configuration *and in every
Core successor*. The definitions below are what this topic adds to drop the second condition.

* `HostKeepsMS host`: every returning call of `host` from a store without memory SIMD function
  bodies returns a store without them. Core's host semantics is an arbitrary relation, and
  `HostOk`'s `Extend` lets a host append function instances, so this is a genuine extra
  hypothesis on the host (see `Thms`, `not_noMemSimd_preserved`).
* `RestMSC hn P host`: the per-rule obligations of `OpenRMRest.rest`, at round 6's builtins `BI`,
  at the `NoCastVM` configurations that themselves contain memory SIMD code. Under
  `HostKeepsMS` this is all that is left of `rest` (`Thms`, `restMS_of_restMSC`).
* `WholeStepValidRMNoMSH`: `Round7.MemSimd.WholeStepValidRMNoMS` with the successor condition
  `NoMemSimd c₁` dropped and `HostKeepsMS` assumed instead.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSPres

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round7.MemSimd (NoCastVM BackwardUpToDRestS BoundedSelM configVD)

variable {H : Type}

/-- **A host that adds no memory SIMD code**: from a store whose Wasm function bodies have no
memory SIMD instruction, every returning call yields such a store. -/
def HostKeepsMS (host : HostSemantics H) : Prop :=
  ∀ h s vs s' r, host h s vs (.returned s' r) → Round6.MemSimd.StoreMS s →
    Round6.MemSimd.StoreMS s'

/-- **What is left of `OpenRMRest.rest` for a host that adds no memory SIMD code**, at round 6's
builtins: the per-rule obligations at the `NoCastVM` configurations that contain memory SIMD code
(in their code or in a function body of their store). -/
def RestMSC (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  BackwardUpToDRestS (fun c => NoCastVM c ∧ ¬ Round6.MemSimd.NoMemSimd c)
    (simEnv (Prims.builtins P hn host)) hn P host

/-- **`Round7.MemSimd.WholeStepValidRMNoMS` with the successor condition replaced by a host
condition**: both halves of the round-7 target from memory-SIMD-free sources, at every finite
`HostOk` host that adds no memory SIMD code. -/
def WholeStepValidRMNoMSH : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostKeepsMS host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
          Round6.MemSimd.NoMemSimd c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelM c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧
              Round6.Int.backend.step B (configVD hn c) (configVD hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          BoundedSelM c → Round6.MemSimd.NoMemSimd c →
          Round6.Int.backend.step B (configVD hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round7.MSPres
