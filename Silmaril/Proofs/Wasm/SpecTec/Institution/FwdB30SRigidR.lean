module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SExact

/-!
# `Step_read` facts at `Wasm30.builtins`, exactly

As `FwdB30SRigid`, for `Step_read`.

* `readB_rigid`: every `FwdB30X.ReadB` successor (`ref.func`, the table, memory and aggregate
  reads, with the instruction sequences of `fill`, `copy` and `init`) is rigid, so
  **`readB_exact`**: the `Step_read` fact of `stepModel builtins` exists at `adminsToV is'`.
* `readX_exact`: at every `ReadHeadX` redex whose successor is rigid. The block rules (one label
  or handler) and `throw_ref-handler-next` (one handler) are not rigid; there the fact is known
  only up to `CfgRel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30S

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdX30 (ReadHeadX)

variable {H : Type}

/-- **Every `ReadB` successor is rigid.** -/
theorem readB_rigid {P : Profile} {c : Config H} {is' : List Admin} (h : FwdB30X.ReadB P c is') :
    RigidV (adminsToV is') := by
  cases h with
  | refFunc => rigid_tac
  | table h =>
    obtain ⟨h, -⟩ := h
    generalize hc' : (⟨c.store, c.frame, is'⟩ : Config H) = c' at h
    have e : is' = c'.code := by rw [← hc']
    rw [e]
    cases h <;> rigid_tac
  | memory h =>
    obtain ⟨h, -⟩ := h
    generalize hc' : (⟨c.store, c.frame, is'⟩ : Config H) = c' at h
    have e : is' = c'.code := by rw [← hc']
    rw [e]
    cases h <;> rigid_tac
  | aggregate h =>
    obtain ⟨h, -⟩ := h
    generalize hc' : (⟨c.store, c.frame, is'⟩ : Config H) = c' at h
    have e : is' = c'.code := by rw [← hc']
    rw [e]
    cases h <;> rigid_tac

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- **At a `ReadHeadX` redex with a rigid successor, the `Step_read` fact at `builtins` is
exact.** -/
theorem readX_exact {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadHeadX (Profile.spec nd r) c is') (hrig : RigidV (adminsToV is')) :
    (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) :=
  exact_of_cfgRel
    (Q := fun js => (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]))
    (FwdB30X.readX_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hr) hrig

/-- **Every `ReadB` redex has its `Step_read` fact at `builtins`, exactly.** -/
theorem readB_exact {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : FwdB30X.ReadB (Profile.spec nd r) c is') :
    (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) :=
  readX_exact (hinj := hinj) (hf := hf) (hh := hh) hc hr.toX (readB_rigid hr)

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30S
