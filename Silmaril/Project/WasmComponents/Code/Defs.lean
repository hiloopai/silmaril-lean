module

public import Silmaril.Project.WasmComponents.Defs
public import Silmaril.Project.Shapes.Component.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Wit.Binary.Custom.Defs

/-!
# The code of a component: its sections other than custom sections

Custom sections (id 0: `producers`, `component-name`, `version`, `package-docs`, …) carry no
semantics in the Component Model; tools add and rewrite them freely, so one release can have
several digests that differ only there (the `wasi:io@0.2.12` finding of
`docs/projects/wasm-wasi.md`). This module names that equivalence on the component AST and the
denotations the pilot compares releases with:

* `stripCustom c`: `c` without its custom sections (top level; nested components keep theirs).
* `CodeEq a b`: `a` and `b` have the same non-custom sections, in order.
* `topSem`: the loosest core semantics (every core module may play any legal play), and
  `irDen C L c`: the WASI model (`Layout.compModel`) of the IR lowering of `c` (`Binary.lower`),
  the bottom model when lowering fails. Statements about `irDen topSem L` are about the
  component's wiring, not about its core code.

`Silmaril.Project.WasmComponents.Code.Thms` proves that the WIT projection (`projectX`,
`project`), index scoping (`wellScopedC`) and lowering (`lower`) ignore custom sections, and
states the open byte-level bridge from `codeSections` (the framing the pilot compares in the
kernel) to `CodeEq`.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents

open Silmaril.Wasm.Component.Binary (Ast Section)

/-- Whether a section is a custom section. -/
def isCustom : Section → Bool
  | .custom _ _ => true
  | _ => false

/-- A component without its (top-level) custom sections. -/
def stripCustom (c : Ast) : Ast := .mk (c.sections.filter fun s => !isCustom s)

/-- **The same code**: the same non-custom sections, in order. -/
def CodeEq (a b : Ast) : Prop := stripCustom a = stripCustom b

/-- The loosest semantics of core modules: each may play any legal play. -/
def topSem : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod := ⟨fun _ => ⊤⟩

/-- The WASI model of a binary component under the core semantics `C` and the names `L`: the
model of its IR lowering, or the bottom model (no plays but the empty one) when lowering
fails. -/
def irDen (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Silmaril.Wasi.Layout) (c : Ast) : L.world.Model :=
  match Silmaril.Wasm.Component.Binary.lower c with
  | .ok m => L.compModel C m
  | .error _ => ⊥

/-- The layout of a component importing one function `get` and exporting one function `run`
(at the top level, interface `""`), as `Binary.Example.compB` does. -/
def getRunLayout : Silmaril.Wasi.Layout := ⟨[⟨"", "get"⟩], [⟨"", "run"⟩]⟩

end Silmaril.Project.WasmComponents

end
