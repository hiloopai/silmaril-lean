module

public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Effects
public import Silmaril.Raw.Wasm.Component.Features

/-!
# Handle lifting and lowering: resources, error contexts, stream/future ends

Specification programs `P E σ` transcribing the handle-valued lift/lower functions of REF
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>),
and the table-manipulating cores of the resource built-ins:

| Lean | REF (lines) |
| --- | --- |
| `liftOwn lim cx rt i` | `lift_own` (L1425-1431) |
| `liftBorrow lim cx rt i` | `lift_borrow` (L1433-1439), `Subtask.add_lender` (L848-851) |
| `liftErrorContext lim cx i` | `lift_error_context` (L1368-1371) |
| `liftAsyncValue lim kind cx t i` | `lift_async_value` (L1447-1457) |
| `liftStream`, `liftFuture` | `lift_stream` (L1441-1442), `lift_future` (L1444-1445) |
| `lowerOwn lim cx rt rep` | `lower_own` (L1736-1738) |
| `lowerBorrow lim cx rt rep` | `lower_borrow` (L1740-1746) |
| `lowerErrorContext lim cx x` | `lower_error_context` (L1677-1678) |
| `lowerAsyncValue lim kind cx e` | `lower_async_value` (L1754-1760) |
| `lowerStream`, `lowerFuture` | `lower_stream` (L1748-1749), `lower_future` (L1751-1752) |
| `resourceNewCore lim inst rt rep` | `canon_resource_new` (L2237-2242) after `may_leave` |
| `resourceDropCore lim inst rt i` | `canon_resource_drop` (L2246-2263) up to the destructor call |
| `resourceRepCore lim inst rt i` | `canon_resource_rep` (L2267-2271) |

The REF type argument `t` of `lift_own`/`lift_borrow`/`lower_own`/`lower_borrow` is only used
through `t.rt`, so these programs take the resource type id `rt : RtId` directly (REF compares
resource types by object identity, `h.rt is not t.rt`; here: equality of arena ids).

**Structure.** Handle-table accesses go through the `Effects.lean` helpers `handlesAdd`,
`handlesGet`, `handlesRemove` (REF `Table.add/get/remove`, L665-685, trapping `tableFull` and
`unknownHandle`). Every other store mutation is one `modifyStore` of a *named* pure function
of namespace `HandleSt` (one per REF multi-field update), or an arena allocation `allocObj`.
Each program has a `P.Inv` lemma (namespace `P.Inv`) whose hypotheses are exactly that these
named updates preserve the invariant.

**Convention.** Every program takes the numeric `Limits` as its explicit leading argument
(unused here: the handle-table bound is the fixed `Runtime.Table.maxLength`, see
`Effects.lean`); no program here has a quirk branch (the wasmtime quirk
`lendReleaseAtReturn` concerns the *release* of lends, `Subtask.deliver_resolve`, not
`add_lender`), so none takes `Quirks`.

**Trap reasons** (informative; the specification compares traps only as "some trap"): an
entry of the wrong kind traps `wrongHandleType`; a resource-type mismatch
`resourceTypeMismatch`; a lent own handle `ownLent`; a borrow where an own is required
`notOwnHandle`; a stream/future end of the wrong element type `wrongHandleType`; a non-idle
end `liftBusyEnd`; an end in a waitable set `endInSet`.

## Deviations and non-claims

* (D-f) REF `assert`s are preconditions, never traps: `lift_borrow`'s "scope is a Subtask",
  `lower_borrow`'s "scope is a Task", `add_lender`'s "not resolved, not delivered",
  `lift_async_value`'s `not contains_borrow(t)` and `end.owner is cx.inst and end.index == i`,
  `lower_async_value`'s kind/type/state assertions, and `canon_resource_drop`'s "an own handle
  has no borrow scope". Where the precondition fixes the shape of data the program must
  inspect (the borrow scope; the scope task of a dropped borrow), a violation reaches
  `internal` (unreachable in well-formed runs); the other assertions are not checked.
* `resourceDropCore` returns `Option (DtorRequest E)` rather than
  `Option (E.FuncAddr × Nat)`: REF calls `rt.dtor or (lambda rep: [])` through
  `store.lift`/`store.lower` even when there is no destructor, and the no-op call still lifts
  in the implementing instance (it registers a thread there, which can trap `tableFull`). So
  the request records the optional destructor, the implementing instance `rt.impl` (`none` for
  a host resource, which REF does not have and for which no call is made) and the resource
  type besides the `rep`. `none` means a borrow handle was dropped (no call). The call itself
  is made by `resourceDrop` (`Canon/Builtins/Resource.lean`) through `Canon.destructorCall`
  (`Canon/Lift.lean`).
* The `ResourceHandle` objects stay in their (append-only) arena after their table entry is
  removed; only the table entry is freed, as REF frees only the table slot.
* Nothing here is proved about the counters `numLends`/`numBorrows` along runs. No tests
  here (`Examples/Resources.lean` and the `run_tests.py` ports test these programs).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.AsyncRef

variable {E : CoreEngine} {σ : Type}

/-! ## Named store updates -/

namespace HandleSt

end HandleSt

/-! ## Handle objects -/

/-! ## Resources -/

/-! ## Error contexts -/

/-! ## Stream and future ends -/

/-! ## Cores of the resource built-ins (used by `Canon/Builtins/Resource.lean`) -/

/-! ## Invariant preservation -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

section Examples

/-- Lowering an own handle into the current instance and lifting it back out (REF
`lower_own` then `lift_own`): the round trip of a resource through a handle table. -/
example (lim : Limits) (rt : RtId) (rep : Nat) : P E σ Nat := do
  let inst ← currentInst
  let cx : LiftLowerContext E := { opts := {}, inst := inst }
  let i ← lowerOwn lim cx rt rep
  liftOwn lim cx rt i

/-- `resource.drop` core followed by the destructor decision. -/
example (lim : Limits) (rt : RtId) (i : Nat) : P E σ (List FlatValue) := do
  let inst ← currentInst
  match ← resourceDropCore lim inst rt i with
  | some _req => pure []
  | none => pure []

/-- Transferring the readable end of a stream from one instance to another. -/
example (lim : Limits) (src dst : LiftLowerContext E) (t : Option (WIT.ClosedType RtId))
    (i : Nat) : P E σ Nat := do
  let e ← liftStream lim src t i
  lowerStream lim dst e

/-- Programs issuing only lookups and traps preserve every invariant. -/
example (I : CStore E → Prop) (lim : Limits) (inst : InstId) (rt : RtId) (i : Nat) :
    P.Inv I (resourceRepCore lim inst rt i : P E σ Nat) :=
  P.Inv.resourceRepCore lim inst rt i

end Examples

end Silmaril.Wasm.Component.Canon
