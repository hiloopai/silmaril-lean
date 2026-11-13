module

public import Silmaril.Wasm.Component.Streams.ACancel.Defs

/-!
# The store of `ACancel` and `Drop`'s store

`ofD` embeds a `Drop` store (no cancellation flags, no host-owned ends, no futures) into the
store of `Silmaril.Wasm.Component.Streams.ACancel`; `liftD` maps `Drop`'s built-ins to that
variant's. The theorems (`AStore.Thms`) say the variant answers them as `Cancel` and `Drop` do,
and where a `BLOCKED` cancel comes from.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.ACancel

open Silmaril.Wasm.Component.Streams.Drop

open Silmaril.Wasm.Component.Async (Obj Res Event upd blocked)
open Silmaril.Wasm.Component.Streams.Cancel

/-- A `Drop` store, with no flags and no futures. -/
def ofD (st : DStore) : AStore := { d := st }

/-- The built-ins of `Drop` as built-ins of this variant. -/
def liftD : DOp → AOp
  | .streamNew => .streamNew
  | .streamWrite w xs => .streamWrite w xs
  | .streamRead r n => .streamRead r n
  | .streamDropR r => .streamDropR r
  | .streamDropW w => .streamDropW w
  | .wsNew => .wsNew
  | .join h s => .join h s

/-- The store has no future handles. -/
def NoFut (st : DStore) : Prop := ∀ h s, st.tbl h ≠ some (.futureR s) ∧ st.tbl h ≠ some (.futureW s)

end Silmaril.Wasm.Component.Streams.ACancel

