module

public import Silmaril.Wasm.Component.Reference.Validation.Check.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs

/-!
# The reference Component Model: syntax, types and validation only

The part of `Silmaril.Wasm.Component.Reference` that executables need: the index-based component
AST, the component types of the Core 3.0 profile, validity `Valid` and its executable checker
`check?`. It imports the copied validator's definition module (`Reference.Validation.Check.Defs`, split
out of `Silmaril.Raw.Wasm.Component`) and **not** the component machine (`Embedding`, the core engines,
the canonical ABI runtime), which `Reference` adds for the behaviours. Tools that only validate
(`wasm-tools validate` on components, `component new`'s reference check, wasm-jco's layout
certificates) import this header, so their runtime closure has no component machine.

The names live in `Silmaril.Wasm.Component.Reference` (they were declared in `Reference` first);
`Reference` re-exports this header. Theorems: `Silmaril.Wasm.Component.Reference.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component

/-! ## Syntax, types and validation -/

/-- A component over core modules `M` (the index-based AST of `Binary.md`). -/
abbrev CompAst (M : Type) : Type := Syntax.Component M

/-- A component whose core modules are Core 3.0 modules. -/
abbrev Core3Component : Type := CompAst Silmaril.Wasm.Module

/-- Component types of the Core 3.0 profile (core extern types are closed Core 3.0 extern
types valid in the empty context). -/
abbrev ComponentType : Type := Types.ComponentType Nat Validation.Core3Extern

/-- Validity of a Core 3.0 component at type `ct` under the feature gates `feat`. -/
abbrev Valid (feat : Features) (c : Core3Component) (ct : ComponentType) : Prop :=
  Validation.ValidComponentCore3 feat c ct

/-- The executable validator of Core 3.0 components. -/
abbrev check? (feat : Features) (c : Core3Component) :
    Except Validation.ValidationError ComponentType :=
  Validation.checkCore3? feat c

end Silmaril.Wasm.Component.Reference
