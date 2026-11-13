module

public import Silmaril.Wasm.Versions.Once.Thms
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Typed.Prepare

/-!
# The component engine instantiates by single allocation

`prepareE?_once`: the instantiation `prepareE?` of the concrete Core 3.0 component engine
(`Silmaril.Wasm.Component.Engine.Core3.core3`) is a run of `CoreInstantiateOnce`, the relational
single-allocation instantiation that `Silmaril.Wasm.Models.V2CoreInst.coreInstOnce` observes: its
configuration is a `CoreInstantiateOnce` of the module, which runs the segment initialisation to
the store and module instance `prepareE?` returns, at every profile and host. So the instantiation
observations of `coreInstOnce` (which `v20InstEmbG` lands in, without `noGlobals`) are those of
the engine that the component model is parametrised by, not of the spec's double allocation.

New statement.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Once

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **The engine's instantiation is single-allocation instantiation.** -/
theorem prepareE?_once {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {m : Module} {xas : List ExternAddr} {i : ModuleInst} {st : Option Nat}
    (h : Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas = some (s', i, st)) :
    ∃ (C : Config H) (f' : Frame) (st₀ : Option FuncIdx),
      Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C ∧
      Steps P host C ⟨s', f', startCode st₀⟩ ∧ i = f'.module ∧
      ∀ a, st = some a → ∃ x, st₀ = some x ∧ f'.module.funcs[x.toNat]? = some a := by
  obtain ⟨⟨xtI, xtE⟩, f', st₀, hv, hx, hi, hmod, hst⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv h
  obtain ⟨C, hC, hS⟩ := Silmaril.Wasm.V2.Execution.Once.instantiateOnce?_once (P := P)
    (host := host) ⟨xtE, xtI, Validation.validate?_sound hv, externAddrsOk?_sound hx⟩ hi
  exact ⟨C, f', st₀, hC, hS, hmod, hst⟩

/--
info: 'Silmaril.Wasm.Component.Once.prepareE?_once' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prepareE?_once

end Silmaril.Wasm.Component.Once
