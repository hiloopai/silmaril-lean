module

public import Silmaril.Wasm.SpecTec.Sim20.PackValid.Thms
public import Silmaril.Wasm.Versions.Soundness.Thms

/-!
# `FuncsValid` from V2 instantiation

Round 7's `PackValid.invokeOkS_of_valid` derives `BodyTyp.InvokeOkS` from V2 validation, but
assumes `FuncsValid s`: every Wasm function of the store is valid in some context. This file
derives that hypothesis from the V2 soundness development (`Silmaril.Wasm.V2.Execution`):

* `funcsValid_of_storeOk`: `Store_ok` gives it, since `Funcinst_ok` checks the code of every
  Wasm function instance (`FuncInstOk.wasm`);
* `funcsValid_of_configOk`: so does `Config_ok`;
* **`funcsValid_instantiate`**: the store of the configuration `$instantiate` returns, from a
  valid store;
* **`funcsValid_instantiate_steps`**: the store of every configuration reachable from it, under
  a host satisfying `HostOk`, so in particular the store an export is invoked in after the
  start code has run;
* **`invokeOkS_of_instantiate_steps`**: `InvokeOkS` at every such store, from the three
  remaining fields (bounded types and typed names), with no `FuncsValid` and no `packOkI`
  hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.PackInst

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.PackValid (FuncsValid invokeOkS_of_valid)
open Silmaril.Wasm.SpecTec.Sim20.BodyTyp (InvokeOkS)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (FuncTypeSmall TypesSmall NamesTyped)

variable {H : Type}

/-- **`Store_ok` gives `FuncsValid`.** -/
theorem funcsValid_of_storeOk {s : Store H} (h : StoreOk s) : FuncsValid s := by
  intro fi hfi fn hc
  cases h.funcs fi hfi with
  | wasm _ _ hcode hf =>
    rw [hc] at hcode
    cases hcode
    exact ⟨_, _, hf⟩
  | host _ hcode =>
    rw [hc] at hcode
    cases hcode

/-- **`Config_ok` gives `FuncsValid` of the store.** -/
theorem funcsValid_of_configOk {c : Config H} {ts : List CValType} (h : ConfigOk c ts) :
    FuncsValid c.store :=
  let ⟨_, hs, _⟩ := h
  funcsValid_of_storeOk hs.1

/-- **Instantiation gives `FuncsValid`**: the store of the configuration `$instantiate`
returns from a valid store. -/
theorem funcsValid_instantiate {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {m : V2.Module} {xas : List ExternAddr} {c : Config H} (hs : StoreOk s)
    (h : Instantiate P host s m xas c) : FuncsValid c.store :=
  funcsValid_of_configOk (Instantiate.ok hhost hs h).1

/-- **And along every run from it.** -/
theorem funcsValid_instantiate_steps {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {m : V2.Module} {xas : List ExternAddr} {c c' : Config H} (hs : StoreOk s)
    (h : Instantiate P host s m xas c) (hsteps : Steps P host c c') : FuncsValid c'.store :=
  funcsValid_of_configOk (Instantiate.safe hhost hs h hsteps).1

/-- **`InvokeOkS` at a store reached from an instantiation**, with neither `FuncsValid` nor
`packOkI` assumed. -/
theorem invokeOkS_of_instantiate_steps {B : Silmaril.SpecTec.Sem.Builtins} {P : Profile}
    {host : HostSemantics H} (hhost : HostOk host) {s : Store H} {m : V2.Module}
    {xas : List ExternAddr} {c c' : Config H} {f : Frame} (hs : StoreOk s)
    (h : Instantiate P host s m xas c) (hsteps : Steps P host c c')
    (hT : TypesSmall f.module) (hN : NamesTyped B f.module)
    (hF : ∀ fi ∈ c'.store.funcs, FuncTypeSmall fi.type ∧ TypesSmall fi.module ∧
      NamesTyped B fi.module) : InvokeOkS B c'.store f :=
  invokeOkS_of_valid hT hN hF (funcsValid_instantiate_steps hhost hs h hsteps)

end Silmaril.Wasm.SpecTec.Sim20.PackInst
