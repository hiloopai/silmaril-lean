module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Resource.CompTable.Defs

/-!
# Early drops of borrowed handles and the ownership protocol: definitions

The ownership and borrowing protocol `obProto` (`Silmaril.Wasm.Resource.Handle`) has no event for
the end of one borrow: a borrowed handle is held until `endCall`, and `free`/`give` of it is a
violation. The Component Model lets a callee drop a borrowed handle early (REF
`canon_resource_drop` of a handle with `own = False`: the entry is removed and the borrow scope's
`num_borrows` is decremented). This module names the ownership reading of a handle table
history, so that the mismatch can be stated:

* `obEvOf μ`: a table event read as an ownership event, given the mode `μ e` of each entry
  (`owned`: `alloc` at an addition; `borrowed`: `lend`); a lookup is `use`, a removal `free`
  (`give` and `free` are treated alike by `obProto`);
* `modeOf s`: the mode of a resource entry read from the handle objects of store `s`
  (`own = false` is `borrowed`; every other entry is `owned`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.EarlyDrop

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Resource

/-- **The ownership reading of a table event**, given the mode of each entry. -/
def obEvOf (μ : HandleEntry → Mode) : Silmaril.Wasm.Component.Runtime.Table.Event HandleEntry → OEv ℕ
  | .added i e => match μ e with
    | .owned => .alloc i
    | .borrowed => .lend i
  | .got i _ => .use i
  | .removed i _ => .free i

/-- The mode of a table entry, read from the handle objects of `s`. -/
def modeOf {E : CoreEngine} (s : CStore E) : HandleEntry → Mode
  | .resource hid => match ArenaField.resHandles.get? s hid with
    | some r => if r.own then .owned else .borrowed
    | none => .owned
  | _ => .owned

end Silmaril.Wasm.Component.FXRes.EarlyDrop
