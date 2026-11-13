module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XHandler

/-!
# Existence at `Wasm30.builtins` for every classified `Step_read` redex

* `ctrlRead_cases`, `readHeadX_cases`: every `FwdX30.ReadHeadX` redex is a `FwdB30.ReadG`,
  `ReadB`, `ReadC` or `ReadH` redex.
* `readX_builtins`, `readX_two_sided`: so at **every** `ReadHeadX` redex, on `DomDet`, a
  `Step_read` fact of `stepModel builtins` exists to Core's successor up to `CfgRel`, and every
  such fact to typed code is that successor up to `CfgRel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdX30 (ReadHeadX CtrlRead)
open Silmaril.Wasm.SpecTec.Institution.FwdB30 (ReadG)

variable {H : Type}

/-- Every `CtrlRead` redex is a `ReadG`, `ReadC` or `ReadH` redex. -/
theorem ctrlRead_cases {c : Config H} {is' : List Admin} (h : CtrlRead c is') :
    ReadG c is' ∨ ReadC c is' ∨ ReadH c is' := by
  cases h with
  | block hbt hm => exact .inr (.inl (.block hbt hm))
  | loop hbt hm => exact .inr (.inl (.loop hbt hm))
  | call hx hf => exact .inl (.call hx hf)
  | returnCall hx hf => exact .inl (.returnCall hx hf)
  | returnCallRefLabel hc => exact .inl (.returnCallRefLabel hc)
  | returnCallRefHandler hc => exact .inl (.returnCallRefHandler hc)
  | returnCallRefFrameNull hc => exact .inl (.returnCallRefFrameNull hc)
  | throwRefNull => exact .inl .throwRefNull
  | throwRefInstrs hne => exact .inl (.throwRefInstrs hne)
  | throwRefLabel => exact .inl .throwRefLabel
  | throwRefFrame => exact .inl .throwRefFrame
  | throwRefHandlerEmpty => exact .inl .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .inr (.inr (.catch_ he ht))
  | throwRefHandlerCatchRef he ht => exact .inr (.inr (.catchRef he ht))
  | throwRefHandlerCatchAll => exact .inl .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .inl .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact .inr (.inr (.next h))
  | tryTable hbt hm => exact .inr (.inl (.tryTable hbt hm))

/-- Every `ReadHeadX` redex is a `ReadG`, `ReadB`, `ReadC` or `ReadH` redex. -/
theorem readHeadX_cases {P : Profile} {c : Config H} {is' : List Admin}
    (h : ReadHeadX P c is') : (ReadG c is' ∨ ReadB P c is') ∨ ReadC c is' ∨ ReadH c is' := by
  cases h with
  | refNull ht => exact .inl (.inl (.refNull ht))
  | refFunc h => exact .inl (.inr (.refFunc h))
  | table h => exact .inl (.inr (.table h))
  | memory h => exact .inl (.inr (.memory h))
  | aggregate h => exact .inl (.inr (.aggregate h))
  | ctrl h =>
    rcases ctrlRead_cases h with h | h | h
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inr (.inr h)

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- **Every `ReadHeadX` redex has its `Step_read` fact at `builtins`**, to Core's successor up
to `CfgRel`. -/
theorem readX_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadHeadX (Profile.spec nd r) c is') :
    ∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  rcases readHeadX_cases hr with h | h | h
  · exact readR_builtins (hinj := hinj) (hf := hf) (hh := hh) hc h
  · exact readC_builtins (hinj := hinj) (hf := hf) (hh := hh) hc h
  · exact readH_builtins (hinj := hinj) (hf := hf) (hh := hh) hc h

/-- **`Step_read` at `builtins` is two-sided at every `ReadHeadX` redex**: on `DomDet`, there
is a `Step_read` fact of `stepModel builtins` to Core's successor up to `CfgRel`, and every
`Step_read` fact from `c` to typed code is that successor up to `CfgRel`. -/
theorem readX_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hr : ReadHeadX (Profile.spec nd r) c is') :
    (∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js)) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
          (cfgV (stateV hn c.store c.frame) js) :=
  ⟨readX_builtins hc hr, fun _ hjs hq => FwdX30Fin.readFact_unique_builtins hc hr.step hjs hq⟩

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
