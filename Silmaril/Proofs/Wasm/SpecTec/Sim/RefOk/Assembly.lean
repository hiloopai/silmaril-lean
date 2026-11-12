module

public import Silmaril.Wasm.SpecTec.Sim.RefOk.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefOk.InstReftype
public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefOk.Grow
public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefOk.Bridge

/-!
# The round-2 bundles from what is left of them

`residue_builtins` and `extra_builtins` rebuild `Integrate.Residue` and `Integrate.Extra` for
the concrete `B` from `ResidueRest` and `ExtraRest`, supplying `instReftype` and `grow`.
`wholeStepBounded_of_refok` is `Integrate.wholeStepBounded_of_concrete` with those two fields
no longer among its premises.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefOk

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- **`Integrate.Residue` for the concrete `B`, from `ResidueRest`.** -/
theorem residue_builtins {prof : Profile} {hn : H → String} {host : HostSemantics H}
    (R : ResidueRest (simEnv (Prims.builtins prof hn host)) hn) :
    Integrate.Residue (simEnv (Prims.builtins prof hn host)) hn where
  types := R.types
  valtypes := R.valtypes
  result := R.result
  funcinst := R.funcinst
  refOk := R.refOk
  instReftype := instReftype_simEnv _

/-- **`Integrate.Extra` for the concrete `B`, from `ExtraRest`.** -/
theorem extra_builtins {prof : Profile} {hn : H → String} {host : HostSemantics H}
    (X : ExtraRest (simEnv (Prims.builtins prof hn host))) :
    Integrate.Extra (simEnv (Prims.builtins prof hn host)) where
  mem := X.mem
  grow := growFuns_builtins hn host
  inst := X.inst
  agg := X.agg

/-- **`Task.wholeStepBounded`, reduced to the bundles left after track refok**: as
`Integrate.wholeStepBounded_of_concrete`, with `ResidueRest` and `ExtraRest` in place of
`Residue` and `Extra`. -/
theorem wholeStepBounded_of_refok
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Prims.HostRespects hn host ∧
        ResidueRest (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn ∧
        ExtraRest (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
        Integrate.BwdOpen (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r)
          host ∧
        (∀ c c' : Config H, ¬ Integrate.Covered c → Integrate.StoreOk c.store →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c' →
          Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧
            SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c)
              (configV hn d'))) :
    Integrate.Task.wholeStepBounded :=
  Integrate.wholeStepBounded_of_concrete fun H hn hinj host hfin nd r =>
    let ⟨hr, R, X, Bo, hrest⟩ := h H hn hinj host hfin nd r
    ⟨hr, residue_builtins R, extra_builtins X, Bo, hrest⟩

end Silmaril.Wasm.SpecTec.Sim.RefOk
