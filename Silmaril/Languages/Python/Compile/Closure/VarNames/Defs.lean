module

public import Silmaril.Languages.Python.Compile.Closure.Link.Defs

/-! # Fast-local tuple evidence for checked ordinary functions

The profile is CPython 3.13.5 in `exec` mode at optimization level zero.
Inspected functions have at most one checked fixed positional parameter
and have no owned cells or incoming captures. The declared parameter
prefix precedes the first emitted uses of the other fast locals. Slot
indices identify names within the checked layout.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.VarNames

open Core.Closure (CodeRef Layout Parameters)
open Source (Name Scope ScopeTree)
open Source.Closure.Frame (ordinaryNames)

def readSlots? {layout : Layout} : Body.Expr layout → Option (List (Fin layout.locals))
  | .read (.local slot) => some [slot]
  | .globalName name => if name == "__debug__" then none else some []
  | _ => none

def valueSlots? {layout : Layout} : Body.Expr layout → Option (List (Fin layout.locals))
  | .integer _ | .none => some []
  | value => readSlots? value

/-- Collect fast-local indices in emission order within one checked block.
A closure contributes its destination; its body has a separate code entry. -/
def emittedSlots? {layout : Layout} : Link.Code layout → Option (List (Fin layout.locals))
  | .ret value => valueSlots? value
  | .returnClosure .. => none
  | .assert (.eqInt receiver _) next
  | .assertCodeNames receiver _ next
  | .discardCall receiver next => do
    let reads ← readSlots? receiver
    return reads ++ (← emittedSlots? next)
  | .assign (.local slot) value next => do
    let reads ← valueSlots? value
    return reads ++ (slot :: (← emittedSlots? next))
  | .closure (.local slot) _ _ _ next => do
    return slot :: (← emittedSlots? next)
  | _ => none

def Profile (scope : Scope) : Prop :=
  scope.context.parameters.length ≤ 1 ∧ scope.cells = [] ∧ scope.captures = []

instance (scope : Scope) : Decidable (Profile scope) := by
  unfold Profile
  infer_instance

def linkedParameterNames (block : Link.Block) (scope : Scope)
    (layout : block.entry.layout = frameLayout scope) : List Name :=
  let parameters : Parameters (frameLayout scope) := layout ▸ block.entry.definition.parameters
  parameters.slots.map (parameterName scope)

structure Evidence (tree : ScopeTree) (blocks : List Link.Block) (ref : CodeRef) where
  block : Link.Block
  found : blocks[ref.key]? = some block
  layout : block.entry.layout = ref.layout
  scope : Scope
  located : tree.atPath block.path = some scope
  scopeLayout : block.entry.layout = frameLayout scope
  profile : Profile scope
  fixed : block.entry.definition.variadic.isNone = true
  parameterOrder : linkedParameterNames block scope scopeLayout = scope.context.parameters
  emittedSlots : List (Fin block.entry.layout.locals)
  emitted : emittedSlots? block.entry.definition.body = some emittedSlots

/-- Decode slot identities in emission order, then intern each name at its
first use. The executor's slot order only supplies the name of each slot. -/
def Evidence.emittedNames {tree : ScopeTree} {blocks : List Link.Block} {ref : CodeRef}
    (evidence : Evidence tree blocks ref) : List Name :=
  let same : evidence.block.entry.layout.locals = (ordinaryNames evidence.scope).length :=
    congrArg Layout.locals evidence.scopeLayout
  evidence.emittedSlots.map fun slot => (ordinaryNames evidence.scope)[Fin.cast same slot]

def Evidence.tuple {tree : ScopeTree} {blocks : List Link.Block} {ref : CodeRef}
    (evidence : Evidence tree blocks ref) : List Name :=
  let declared := evidence.scope.context.parameters
  declared ++ (evidence.emittedNames.filter fun name => !declared.contains name).eraseDups

/-- Bind this evidence to an ordinary lexical path and the exact linked code
key and layout. An empty tuple is represented by successful evidence. -/
def checked? (tree : ScopeTree) (blocks : List Link.Block) (ref : CodeRef) :
    Option (Evidence tree blocks ref) := do
  match found : blocks[ref.key]? with
  | none => none
  | some block =>
    if layout : block.entry.layout = ref.layout then
      let ⟨scope, located, scopeLayout⟩ ← Link.blockScope? tree block
      if profile : Profile scope ∧ block.entry.definition.variadic.isNone = true ∧
          linkedParameterNames block scope scopeLayout = scope.context.parameters then
        match emitted : emittedSlots? block.entry.definition.body with
        | none => none
        | some slots =>
          return ⟨block, found, layout, scope, located, scopeLayout, profile.1, profile.2.1, profile.2.2, slots, emitted⟩
      else none
    else none

/-- Attach the optional tuple to each checked row at its existing code key. -/
def attach (tree : ScopeTree) (blocks : List Link.Block) : List Link.Block :=
  blocks.zipIdx.map fun (block, key) =>
    { block with entry := { block.entry with definition := { block.entry.definition with
      varnames := (checked? tree blocks ⟨key, block.entry.layout⟩).map (·.tuple) } } }

end Silmaril.Languages.Python.Compile.Closure.VarNames
