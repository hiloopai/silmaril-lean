module

public import Silmaril.Wasm.Jco.Resource.Basic.Defs

/-!
# Handle tables that record their history

`logTab` is the reference machine's `Table` (`refTab`) together with the history of its
successful operations (`Table.Event`s, oldest first): `add` records `added i e`, a use (`get`
through `touch`) records `got i e`, `remove` records `removed i e`. The invariant is `refTab`'s
together with `Table.Steps Silmaril.Wasm.Component.Runtime.Table.empty log t`: the log is a successful history from the empty
table that ends in the current table.

This is how the resource-protocol theorems of `Silmaril.Wasm.Resource` apply to the jco toolchain:
any state satisfying the invariant has a history accepted by the handle protocol
(`table_steps_accepts`), and the jco theorems keep the invariant.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Component.Runtime (Table)

/-- The canonical handle tables with their history. -/
abbrev logTab : HTab where
  T := Silmaril.Wasm.Component.Runtime.Table HEntry × List (Silmaril.Wasm.Component.Runtime.Table.Event HEntry)
  add? t e := (t.1.add? e).map fun p => (p.1, (p.2, t.2 ++ [.added p.1 e]))
  get? t i := t.1.get? i
  touch t i :=
    match t.1.get? i with
    | some e => (t.1, t.2 ++ [.got i e])
    | none => t
  remove? t i := (t.1.remove? i).map fun p => (p.1, (p.2, t.2 ++ [.removed i p.1]))
  cap t := refTab.cap t.1
  Inv t := refTab.Inv t.1 ∧ Silmaril.Wasm.Component.Runtime.Table.Steps Silmaril.Wasm.Component.Runtime.Table.empty t.2 t.1

/-- The empty table with the empty history. -/
def logEmpty : logTab.T := (Silmaril.Wasm.Component.Runtime.Table.empty, [])

end Silmaril.Wasm.Jco.Res
