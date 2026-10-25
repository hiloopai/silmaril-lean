module

public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-! # End-to-end type safety headlines (relational)

Compose `Instantiate.ok` / `invoke_ok` with `Steps.safe`:

* `Instantiate.safe` — every configuration reachable from an instantiation in a
  valid store is typed (empty result type) and is terminal or can step;
* `invoke_safe` — every configuration reachable from a well-typed invocation is
  typed at the function's result type and is terminal or can step;
* `Module.safe` — the spec-shaped soundness statement starting from `ModuleOk` and
  typed imports.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Type safety of instantiation: reachable configurations never get stuck. -/
theorem Instantiate.safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {m : Module} {xas : List ExternAddr} {c c' : Config H} (hs : StoreOk s)
    (h : Instantiate P host s m xas c) (hsteps : Steps P host c c') :
    ConfigOk c' [] ∧ (c'.Terminal ∨ ∃ c'', Step P host c' c'') :=
  Steps.safe hhost (Instantiate.ok hhost hs h) hsteps

/-- Type safety of invocation: reachable configurations are typed at the function's
result type and never get stuck. -/
theorem invoke_safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {a : Nat} {vs : List Val} {c' : Config H} (hs : StoreOk s)
    (h : InvokeOk s a vs) (hsteps : Steps P host (invoke s a vs) c') :
    ∃ fi ps rs, s.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
      ConfigOk c' rs.toList ∧ (c'.Terminal ∨ ∃ c'', Step P host c' c'') := by
  obtain ⟨fi, ps, rs, hfi, hexp, hc⟩ := invoke_ok hs h
  exact ⟨fi, ps, rs, hfi, hexp, Steps.safe hhost hc hsteps⟩

/-- Soundness (spec shape): a valid module `m : xtI → xtE`, instantiated in a valid
store against imports of types `xtI`, never reaches a stuck configuration. -/
theorem Module.safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {m : Module} {xtI xtE : List CExternType} {xas : List ExternAddr}
    {c c' : Config H} (hs : StoreOk s) (hm : ModuleOk m ⟨xtI, xtE⟩)
    (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : Instantiate P host s m xas c) (hsteps : Steps P host c c') :
    ConfigOk c' [] ∧ (c'.Terminal ∨ ∃ c'', Step P host c' c'') :=
  Instantiate.safe hhost hs { h with valid := ⟨xtE, xtI, hm, hxas⟩ } hsteps

end Silmaril.Wasm.Execution.Core
