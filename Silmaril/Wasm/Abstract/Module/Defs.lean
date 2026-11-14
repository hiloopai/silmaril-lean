module

public import Silmaril.Games.Abstract.Module.Defs
public import Silmaril.Wasm.Abstract.Function.Defs

/-!
# Core 3.0 modules as closed abstract modules

A Core 3.0 module instance with `n` functions at addresses `addrs`, under a
numerics profile and host semantics, has the internal shape

* imports: none here, since host calls are resolved by `HostSemantics`, as in
  `wasmFun`;
* internal state: the store, with all memories, globals and tables;
* functions: `Fin n`, each taking values and returning values or an uncaught
  exception.

Its internal calls (`call`, `call_indirect`) are resolved by the store
semantics, so it is a closed module (`wasmModule`). It projects to an open
module that makes no internal call, which closes back to it
(`Silmaril.Wasm.Abstract.Module.Thms`). Exposing internal calls as `self`
calls, to compare function-by-function against a call graph, is a later
stage.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- The internal shape of a Core 3.0 module with `n` functions. -/
abbrev wasmShape (H : Type) (n : Nat) : Silmaril.Games.Abstract.Shape.{0} :=
  ⟨Sig.empty, Store H, Fin n, fun _ => List Val, fun _ => List Val ⊕ Nat⟩

/-- The module's functions at `addrs`, as a closed abstract module. -/
def wasmModule {H : Type} (P : Profile) (host : HostSemantics H) {n : Nat} (addrs : Fin n → Nat) :
    (wasmShape H n).ClosedMod := fun i => wasmFun P host (addrs i)

end Silmaril.Wasm.Abstract
