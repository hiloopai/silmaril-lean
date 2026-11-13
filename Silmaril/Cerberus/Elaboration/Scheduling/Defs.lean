module

public import Silmaril.Cerberus.Elaboration.State.Defs

/-! Explicit construction and execution of source state computations. Pinned
`translation_effect.lem:63-74` allocates global symbols before returning an
Elab action; `state.lem:9-13,47-59` delays bind continuations but eagerly builds
map callbacks. The installed Lem2026-05-01 `list.lem:261-278` gives the exact
count_map/map_tr threshold schedule reproduced below. This is a compositional
model of those patterns, not a source adequacy theorem or AST translation. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Scheduling
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

abbrev Build := ExceptT State.Error (StateM Freshness.Context)
abbrev Computation (α : Type) := Build (State.ElabM α)

/-- Build against the current shared freshness state, preserving all other
context fields, then run the resulting action. Build failures retain consumed
freshness, as do ordinary explicit-state errors; no source failure-state
correspondence is asserted. -/
def execute {α : Type} (computation : Computation α) : State.ElabM α := do
  let context ← get
  let (result, freshness) := computation.run context.freshness
  set {context with freshness}
  match result with
  | .ok action => action
  | .error error => throw error

/-- Existing actions without an eager construction prefix remain reusable. -/
def defer {α : Type} (action : State.ElabM α) : Computation α :=
  (pure action : Build (State.ElabM α))

def returnValue {α : Type} (value : α) : Computation α := defer (pure value)

/-- Source bind constructs its first plan now. Its continuation is constructed
only after that plan executes and produces a value. This is distinct from the
ordinary Build bind used internally to construct several plans immediately. -/
def bind {α β : Type} (first : Computation α) (next : α → Computation β) : Computation β :=
  (do
    let action ← first
    return (do
      let value ← action
      execute (next value) : State.ElabM β) : Build (State.ElabM β))

def map {α β : Type} (transform : α → β) (computation : Computation α) : Computation β :=
  bind computation fun value => returnValue (transform value)

def freshDescription (description : SymbolDescription) : Build Sym := do
  let before ← get
  match Freshness.description description before with
  | .error error => throw (.freshness error)
  | .ok (symbol, after) =>
      set after
      return symbol

/-- The actual symbol is allocated during Build, before the returned pure
Elab action is run. Pattern and pure-expression construction is unchanged. -/
def wrappedFreshSymbolWith (description : SymbolDescription) (type : BaseType) :
    Computation State.WrappedSymbol :=
  (do
    let symbol ← freshDescription description
    return (pure ⟨symbol, symbolPattern symbol type, symbolPure symbol⟩ : State.ElabM State.WrappedSymbol)
    : Build (State.ElabM State.WrappedSymbol))

def wrappedFreshSymbol (type : BaseType) : Computation State.WrappedSymbol :=
  wrappedFreshSymbolWith .none type

/-- Source map_tr's left-to-right callback construction, with original result
order. Its accumulator reversal is expressed extensionally by this recursion. -/
def forwardBuild {α β : Type} (callback : α → Build β) : List α → Build (List β)
  | [] => pure []
  | first :: rest => do
      let value ← callback first
      let values ← forwardBuild callback rest
      return value :: values

/-- Exact target callback construction order of pinned count_map. OCaml builds
the cons tail before its head. At counter5000 the remaining tail uses map_tr,
then the current head is built. This is not unconditional reverse traversal. -/
def buildMapAt {α β : Type} (counter : Nat) (callback : α → Build β) :
    List α → Build (List β)
  | [] => pure []
  | first :: rest => do
      let values ← if counter < 5000 then buildMapAt (counter + 1) callback rest
        else forwardBuild callback rest
      let value ← callback first
      return value :: values

def sequenceActions {α : Type} : List (State.ElabM α) → State.ElabM (List α)
  | [] => pure []
  | first :: rest => do
      let value ← first
      let values ← sequenceActions rest
      return value :: values

/-- Construct all callback plans in pinned target map order; execute the
resulting plans in original left-to-right list order. -/
def mapM {α β : Type} (callback : α → Computation β) (inputs : List α) : Computation (List β) :=
  (do
    let actions ← buildMapAt 0 callback inputs
    return sequenceActions actions : Build (State.ElabM (List β)))

end Silmaril.Cerberus.Elaboration.Scheduling
