module

public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Wit.Project.Valid.Defs

/-!
# Index scoping and WIT projection of components with async built-ins

`Silmaril.Wasm.Wit.Project` checks index scoping (`wellScopedC`) and projects a component to
its world (`projectX`) on the syntax of `Silmaril.Wasm.Component.Binary` (component-model
`8505ba7`, no async built-ins). This module lifts both to `BinaryP3.Ast` (`d095e2f`).

* `Ast.shadow c` is `c` with the built-ins the old syntax lacks removed (every `canon` other
  than `lift`, `lower` and `resource.*`, nested components included). Those built-ins define
  **core** functions only, which neither check counts: `cStep` and the projection's replay
  treat every `canon` other than `lift` as a no-op.
* `projectX3 c := projectX c.shadow`: the world of a component with async built-ins.
* `wellScopedC3 c`: the walk of `wellScopedC` (`cCheck3`), which on the built-ins of the old
  syntax is `cStep` and on the others **also checks their component type operands**: the
  `t` of `stream.*` and `future.*` and the result type of `task.return` must be bound
  (`canonTypeOk`). Their core operands (memories, tables, core types, callbacks) are not
  checked, as the old check does not check those of `lower` either.

Laws (`Silmaril.Wasm.Component.BinaryP3.Project.Thms`): on the embedding of the old syntax
both agree with the old functions (`projectX3_ofV0`, `wellScopedC3_ofV0`), and
`Ast.shadow (Ast.ofV0 c) = c` (`shadow_ofV0`). `topV0 c` (every built-in of `c`'s own `canon`
sections is one of the old syntax) holds of every embedded old component (`topV0_ofV0`); with
`BinaryP3.parse_ofV0` it refutes `Binary.parse b = .ok _` for a file whose new parse has an
async built-in at the top level (`not_parse_v0`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3

open Silmaril.Wasm.Wit.Project (CCount cStep cCheck valOk optValOk)

/-- The built-in of the old syntax, if it is one. -/
def Canon.toV0? : Canon → Option Binary.Canon
  | .lift f o t => some (.lift f o t)
  | .lower f o => some (.lower f o)
  | .resourceNew t => some (.resourceNew t)
  | .resourceDrop t => some (.resourceDrop t)
  | .resourceRep t => some (.resourceRep t)
  | _ => none

mutual
/-- A section without the built-ins the old syntax lacks. -/
def Section.shadow : Section → Binary.Section
  | .custom n d => .custom n d
  | .coreModule b => .coreModule b
  | .coreInstances xs => .coreInstances xs
  | .coreTypes xs => .coreTypes xs
  | .component c => .component (Ast.shadow c)
  | .instances xs => .instances xs
  | .aliases xs => .aliases xs
  | .types xs => .types xs
  | .canons xs => .canons (xs.filterMap Canon.toV0?)
  | .start s => .start s
  | .imports xs => .imports xs
  | .exports xs => .exports xs
  | .values xs => .values xs

def Section.listShadow : List Section → List Binary.Section
  | [] => []
  | s :: ss => Section.shadow s :: Section.listShadow ss

/-- **A component without the built-ins the old syntax lacks.** -/
def Ast.shadow : Ast → Binary.Ast
  | .mk ss => .mk (Section.listShadow ss)
end

/-- **The world of a component with async built-ins**: the projection of its shadow. -/
def projectX3 (c : Ast) : Option Silmaril.Wasm.Wit.Project.WorldType :=
  Silmaril.Wasm.Wit.Project.projectX c.shadow

/-- The component type operands of a built-in the old syntax lacks are bound (`t` types so
far). -/
def canonTypeOk (t : Nat) : Canon → Bool
  | .taskReturn r _ => optValOk t r
  | .streamNew i | .streamRead i _ | .streamWrite i _ | .streamCancelRead i _
  | .streamCancelWrite i _ | .streamDropReadable i | .streamDropWritable i
  | .streamForward i
  | .futureNew i | .futureRead i _ | .futureWrite i _ | .futureCancelRead i _
  | .futureCancelWrite i _ | .futureDropReadable i | .futureDropWritable i
  | .futureForward i => decide (i < t)
  | _ => true

/-- Split vector sections into sections of one element (`Wit.Project.splitSection`). -/
def splitSection3 : Section → List Section
  | .coreInstances xs => xs.map fun x => .coreInstances [x]
  | .coreTypes xs => xs.map fun x => .coreTypes [x]
  | .instances xs => xs.map fun x => .instances [x]
  | .aliases xs => xs.map fun x => .aliases [x]
  | .types xs => xs.map fun x => .types [x]
  | .canons xs => xs.map fun x => .canons [x]
  | .imports xs => xs.map fun x => .imports [x]
  | .exports xs => xs.map fun x => .exports [x]
  | .values xs => xs.map fun x => .values [x]
  | s => [s]

/-- One item, checked: `cStep` on the old syntax, `canonTypeOk` on the new built-ins. -/
def cStep3 (k : CCount) : Section → Option CCount
  | .canons [x] =>
    match x.toV0? with
    | some x' => cStep k (.canons [x'])
    | none => if canonTypeOk k.t x then some k else none
  | s => cStep k s.shadow

/-- Check the items of a component, each a section of one element. -/
def cCheck3 : CCount → List Section → Option CCount
  | k, [] => some k
  | k, x :: xs => (cStep3 k x).bind fun k' => cCheck3 k' xs

/-- **A well-scoped component with async built-ins.** -/
def wellScopedC3 (c : Ast) : Bool := (cCheck3 {} (c.sections.flatMap splitSection3)).isSome

/-- Every built-in of the component's own `canon` sections is one of the old syntax. An
embedded old component has this property (`topV0_ofV0`), so a component without it is not
`Ast.ofV0` of anything. -/
def topV0 (c : Ast) : Bool :=
  c.sections.all fun
    | .canons xs => xs.all fun x => x.toV0?.isSome
    | _ => true

end Silmaril.Wasm.Component.BinaryP3

end
