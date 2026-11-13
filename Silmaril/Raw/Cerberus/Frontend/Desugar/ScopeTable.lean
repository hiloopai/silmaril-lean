module

public import Std.Data.TreeMap

/-! # Symbol tables with stacked scopes

A port of Cerberus's `frontend/model/scope_table.lem` at `b3e11ea3`: a stack of scopes, the
innermost first, each with the map of the identifiers registered in it. A Lem map is a
`Std.TreeMap` under the comparison of its key type's `MapKeyType` instance; like OCaml's
`Map.add`, `insert` replaces the stored key of an equal binding. Lem's `error` on an empty
table is unreachable from the desugaring (the file scope is opened first); these functions
return a default there.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

/-- `Scope_table.t`: the scopes, innermost first. -/
abbrev ScopeTable (σ κ α : Type) (cmp : κ → κ → Ordering) := List (σ × Std.TreeMap κ α cmp)

namespace ScopeTable

variable {σ κ α : Type} {cmp : κ → κ → Ordering}

/-- `Scope_table.empty` (`scope_table.lem:9`). -/
def empty : ScopeTable σ κ α cmp := []

/-- `Scope_table.register` (`scope_table.lem:13`): bind `ident` in the innermost scope. -/
def register (ident : κ) (a : α) : ScopeTable σ κ α cmp → ScopeTable σ κ α cmp
  | (scope, m) :: ms => (scope, m.insert ident a) :: ms
  | [] => []

/-- `Scope_table.resolve` (`scope_table.lem:21`): the innermost binding of `ident`, with its
scope. -/
def resolve (ident : κ) : ScopeTable σ κ α cmp → Option (σ × α)
  | (scope, m) :: ms =>
    match m.get? ident with
    | some a => some (scope, a)
    | none => resolve ident ms
  | [] => none

/-- `Scope_table.is_in_scope` (`scope_table.lem:30`). -/
def isInScope (ident : κ) (t : ScopeTable σ κ α cmp) : Bool := (resolve ident t).isSome

/-- `Scope_table.is_in_current_scope` (`scope_table.lem:35`). -/
def isInCurrentScope (ident : κ) : ScopeTable σ κ α cmp → Bool
  | (_, m) :: _ => m.contains ident
  | [] => false

/-- `Scope_table.create_scope` (`scope_table.lem:70`). -/
def createScope (scope : σ) (t : ScopeTable σ κ α cmp) : ScopeTable σ κ α cmp :=
  (scope, ∅) :: t

/-- `Scope_table.destroy_scope` (`scope_table.lem:75`): the innermost map, and the table
without it. -/
def destroyScope : ScopeTable σ κ α cmp → Std.TreeMap κ α cmp × ScopeTable σ κ α cmp
  | (_, m) :: ms => (m, ms)
  | [] => (∅, [])

/-- `Scope_table.return_scope` (`scope_table.lem:83`): the innermost scope alone. -/
def returnScope : ScopeTable σ κ α cmp → ScopeTable σ κ α cmp
  | m :: _ => [m]
  | [] => []

/-- `Scope_table.push_table` (`scope_table.lem:91`). -/
def pushTable (t₁ t₂ : ScopeTable σ κ α cmp) : ScopeTable σ κ α cmp := t₁ ++ t₂

/-- `Scope_table.current_scope_is` (`scope_table.lem:96`): the innermost scope. -/
def currentScopeIs [Inhabited σ] : ScopeTable σ κ α cmp → σ
  | (scope, _) :: _ => scope
  | [] => default

/-- `Scope_table.scope_is_visible` (`scope_table.lem:104`). -/
def scopeIsVisible [BEq σ] (sc : σ) : ScopeTable σ κ α cmp → Bool
  | [] => false
  | (sc', _) :: tbl' => sc == sc' || scopeIsVisible sc tbl'

end ScopeTable

end Silmaril.Cerberus.Frontend.Desugar
