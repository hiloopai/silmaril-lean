module

public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.SingleThreaded.Soundness
import Silmaril.Proofs.Wasm.Game.Instantiate.Typed

/-!
# Instantiation against typed imports is typed: theorems

A small header for users outside the `Wasm.Game` topic (the linked WAST scripts,
`Silmaril.Project.Shapes.WasmWastLink`), kept separate from the widely imported
`Wasm.Game.Instantiate.Thms`:

* `instantiateOnce?_configOk`: a valid module `m : mt`, instantiated by `instantiateOnce?` in a
  well-typed store against external addresses of the import types of `mt` (`ExternAddrOk`),
  leaves a typed configuration `⟨s', f, startCode st⟩`: the store after segment initialisation,
  with the start call (if any) still to run. No restriction to function imports or to modules
  without a start function (unlike `IsInstance.ok`).
* `importStore_nil_ok`: the empty store `importStore []` is well typed.

Proofs: `Silmaril.Proofs.Wasm.Game.Instantiate.Typed`.
-/

@[expose] public section

namespace Silmaril.Wasm.Game

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-- The empty store `importStore []` is well typed. -/
theorem importStore_nil_ok : StoreOk (importStore []) :=
  Silmaril.Proofs.Wasm.Game.importStore_nil_ok

/-- **Instantiation against typed imports is typed.** -/
theorem instantiateOnce?_configOk {s : Store Nat} {m : Module} {xas : List ExternAddr}
    {mt : CModuleType} {s' : Store Nat} {f : Frame} {st : Option FuncIdx} (hs : StoreOk s)
    (hm : ModuleOk m mt) (hx : List.Forall₂ (ExternAddrOk s) xas mt.imports)
    (h : instantiateOnce? s m xas = some (s', f, st)) :
    ConfigOk ⟨s', f, startCode st⟩ [] :=
  Silmaril.Proofs.Wasm.Game.instantiateOnce?_configOk hs hm hx h

end Silmaril.Wasm.Game

end
