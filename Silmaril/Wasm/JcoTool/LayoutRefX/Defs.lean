module

public import Silmaril.Wasm.JcoTool.LayoutRef.Defs

/-!
# The reference translation with core module types

`LayoutRef.toRef` fails on six shapes. This module closes the one that valid components can
have, **core module types** (`(core type (module …))`, `Binary.md` `core:moduletype`), and states
why the others stay outside:

* `toRefX rd x`: `LayoutRef.toRef` with core module types translated to the reference's
  `CoreTypeDef.module_` (`moduleDeclTo`: core imports and exports with their extern types,
  function types as one-element recursion groups, outer type aliases). Every other section is
  translated as `LayoutRef.toRef` translates it.
* `ToolV.refCore3X`, `ToolV.refCheckX`: the bytes read with `toRefX`, and the reference validator
  on them (`wasm-jco validate` reports this verdict).

Theorems (`LayoutRefX.Thms`): `toRefX_of_toRef` (the translation extends `toRef`),
`spacesRef_toRefX` and `read_toRefX` (`Layout.read names x = readRef names c` whenever
`toRefX rd x = some c`: a core type is in none of the five index spaces either reading keeps),
and `refCheckX_valid`.

The remaining shapes `toRef` rejects are not valid components in the Component Model
(`Explainer.md`, `Binary.md` at component-model `a25fc0b`), and on each the two readings would
count differently, so `toRefX` rejects them too:

* `alias export i n (core func)` and `alias outer c i (core func)`: component instances export
  no core functions, and outer aliases are only of types, modules and components;
* a core-instance export alias of a component sort (`alias core export i n (func)`): a core
  instance exports only core items; the reference syntax cannot even write it;
* exports of core functions and core instances: a component exports only modules, functions,
  values, types, components and instances;
* resource representations other than `i32` (the reference also has `i64` for memory64): the
  Component Model requires `(rep i32)`; the reference syntax cannot write the others;
* a `canon` section read as `XSec.sec` (never an `xparse` result).

`tools/wasm-jco/tests/ref-gaps.sh` checks that wasm-tools rejects each of these and that a
component with a core module type is `reference-valid: yes` under `toRefX`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.LayoutRefX

open Silmaril.Wasm.JcoTool.LayoutRef
open Silmaril.Wasm.Component (Syntax.Definition Syntax.Component)

namespace B
export Silmaril.Wasm.Component.Binary (CoreImportDesc ModuleDecl CoreType CoreFuncType Limits
  CoreValType Section Ast)
end B

/-- An index of the 32-bit range. -/
def idx32? {k : Silmaril.Wasm.IndexKind} (n : Nat) : Option (Silmaril.Wasm.Idx k) :=
  if h : n < 2 ^ 32 then some ⟨⟨n, h⟩⟩ else none

/-- A bound of the 64-bit range. -/
def u64? (n : Nat) : Option (Fin (2 ^ 64)) :=
  if h : n < 2 ^ 64 then some ⟨n, h⟩ else none

/-- Limits of a 32-bit memory or table. -/
def limitsTo (l : B.Limits) : Option Silmaril.Wasm.Limits := do
  let mn ← u64? l.min
  let mx ← match l.max with
    | none => pure none
    | some m => some <$> u64? m
  pure ⟨mn, mx⟩

/-- A reference type of a table (`funcref`, `externref`). -/
def refTypeTo : B.CoreValType → Option Silmaril.Wasm.RefType
  | .funcref => some ⟨true, .abstract .func⟩
  | .externref => some ⟨true, .abstract .extern⟩
  | _ => none

/-- A core import or export description as a Core 3.0 extern type. -/
def externTo : B.CoreImportDesc → Option Silmaril.Wasm.ExternType
  | .func t => (idx32? t).map .func
  | .table e l => do pure (.table ⟨.i32, ← limitsTo l, ← refTypeTo e⟩)
  | .memory l => do pure (.memory ⟨.i32, ← limitsTo l⟩)
  | .global t m => some (.global ⟨if m then .var else .const, coreValTo t⟩)
  | .tag t => (idx32? t).map .tag

/-- A function type as a one-element recursion group (as `coreTypeTo` writes it). -/
def recOf (t : B.CoreFuncType) : Silmaril.Wasm.RecType :=
  ⟨[⟨true, [], .func ⟨t.params.map coreValTo, t.results.map coreValTo⟩⟩]⟩

/-- A declaration of a core module type. -/
def moduleDeclTo : B.ModuleDecl → Option Silmaril.Wasm.Component.Syntax.CoreModuleDecl
  | .import m n d => (externTo d).map (.import_ m n)
  | .type t => some (.type (recOf t))
  | .alias c i => some (.aliasOuter c i)
  | .export n d => (externTo d).map (.export_ n)

/-- A core type, module types included. -/
def coreTypeToX : B.CoreType → Option Silmaril.Wasm.Component.Syntax.CoreTypeDef
  | .func t => some (.rec_ (recOf t))
  | .module ds => (ds.mapM moduleDeclTo).map .module_

section
variable {M : Type} (rd : ByteArray → Option M)

mutual
/-- A section, as `LayoutRef.secTo`, with core module types. -/
def secToX : B.Section → Option (List (Syntax.Definition M))
  | .coreTypes xs => (xs.mapM coreTypeToX).map (·.map .coreType)
  | .component c => (astToX c).map fun ds => [.component ds]
  | .custom n d => secTo rd (.custom n d)
  | .coreModule b => secTo rd (.coreModule b)
  | .coreInstances xs => secTo rd (.coreInstances xs)
  | .instances xs => secTo rd (.instances xs)
  | .aliases xs => secTo rd (.aliases xs)
  | .types xs => secTo rd (.types xs)
  | .canons xs => secTo rd (.canons xs)
  | .start s => secTo rd (.start s)
  | .imports xs => secTo rd (.imports xs)
  | .exports xs => secTo rd (.exports xs)
  | .values xs => secTo rd (.values xs)
def secsToX : List B.Section → Option (List (Syntax.Definition M))
  | [] => some []
  | s :: ss => do pure ((← secToX s) ++ (← secsToX ss))
def astToX : B.Ast → Option (List (Syntax.Definition M))
  | .mk ss => secsToX ss
end

/-- A section of a parsed output. -/
def xsecToX : XSec → Option (List (Syntax.Definition M))
  | .sec (.canons _) => none
  | .sec s => secToX rd s
  | .canons xs => some (xs.map fun c => .canon (xcanonTo c))

/-- **A parsed output as a reference component, core module types included.** -/
def toRefX (x : XComp) : Option (Syntax.Component M) :=
  (x.sections.mapM (xsecToX rd)).map List.flatten

end

end Silmaril.Wasm.JcoTool.LayoutRefX

namespace Silmaril.Wasm.JcoTool.ToolV

/-- Bytes read as a Core 3.0 reference component with `toRefX`. -/
def refCore3X (b : ByteArray) : Except String Silmaril.Wasm.Component.Reference.Core3Component :=
  match xparse b with
  | .error _ => .error "the component does not parse (xparse)"
  | .ok x => match LayoutRefX.toRefX Silmaril.Wasm.Perf.CoreDecode.decodeF x with
    | some c => .ok c
    | none => .error "the component is outside the translation to the reference syntax (a shape the Component Model rejects, or a core module that does not decode)"

/-- **The reference validator on bytes**, with core module types translated. -/
def refCheckX (b : ByteArray) : Except String Silmaril.Wasm.Component.Reference.ComponentType := do
  let c ← refCore3X b
  match Silmaril.Wasm.Perf.ValidateR.checkCore3R Silmaril.Wasm.Component.Features.all c with
  | .ok ct => pure ct
  | .error e => throw s!"the reference validator rejects the component: {repr e}"

/-- The verdict line of `refCheckX`. -/
def refCheckXLine (b : ByteArray) : String :=
  match refCheckX b with
  | .ok _ => "reference-valid: yes (the bytes, read as a reference Core3Component with core module types, pass Reference.check? with Features.all; LayoutRefX.refCheckX_valid)"
  | .error e => s!"reference-valid: no ({e})"

end Silmaril.Wasm.JcoTool.ToolV
