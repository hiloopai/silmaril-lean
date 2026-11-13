module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Component.Reference.Defs

@[expose] public section

/-!
# Handle tables of the component reference machine as handle protocols

The reference machine of the Component Model (`Silmaril.Wasm.Component.Reference`, built on the
canonical ABI transcription) keeps resource handles in **handle tables**
(`Silmaril.Wasm.Component.Runtime.Table`, REF `definitions.py` class `Table`): `resource.new`
adds an entry (`Table.add?`), `resource.rep` reads one (`Table.get?`), `resource.drop` removes one
(`Table.remove?`). The successful operations of a table form a history of `Table.Event`s
(`added i e`, `got i e`, `removed i e`; `Table.Steps t evs t'`).

This file reads such histories as handle events (`tableEv`: `added i` is `alloc i`, `got i` is
`use i`, `removed i` is `free i`), so that the handle protocols of `Silmaril.Wasm.Resource.Handle`
apply to them:

* `FreeOK t`: the representation invariant of a table needed here (free-stack entries are empty
  slots, without duplicates); it holds of `Table.empty`;
* `TabRel L t`: the protocol state `L` (live handles) lists exactly the valid indices of `t`,
  without duplicates.

The theorems (`Silmaril.Wasm.Resource.Table.Thms`) say that every successful table history is
accepted by the handle protocol **in both orientations**: `add` hands out a fresh index (the
provider sentence, "`resource.new` never returns a live handle"), and `get`/`remove` only touch live
indices (the client sentence, "no use or drop after drop"). This is the dynamic enforcement of
`noUseAfterDrop` by the reference machine: an operation on a dropped handle traps instead of
succeeding.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component.Runtime

/-- A successful table operation as a handle event. -/
def tableEv {α : Type} : Table.Event α → HEv ℕ
  | .added i _ => .alloc i
  | .got i _ => .use i
  | .removed i _ => .free i

/-- The representation invariant used here: free-stack entries are empty slots, without
duplicates. -/
def FreeOK {α : Type} (t : Silmaril.Wasm.Component.Runtime.Table α) : Prop :=
  (∀ j ∈ t.free, t.array[j]? = some none) ∧ t.free.Nodup

/-- The protocol state `L` lists exactly the valid indices of the table, without duplicates. -/
def TabRel {α : Type} (L : List ℕ) (t : Silmaril.Wasm.Component.Runtime.Table α) : Prop :=
  L.Nodup ∧ ∀ i, i ∈ L ↔ (t.get? i).isSome

end Silmaril.Wasm.Resource
