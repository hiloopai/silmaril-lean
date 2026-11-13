module

public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs

/-!
# The resource built-ins `resource.new`, `resource.drop`, `resource.rep`

Specification programs `P E σ` transcribing the resource built-ins of REF
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>);
see also `CanonicalABI.md` §"`canon resource.new`", §"`canon resource.drop`" and §"`canon
resource.rep`".

| Lean | REF (lines) |
| --- | --- |
| `resourceNew lim rt rep` | `canon_resource_new` (L2237-2242) |
| `resourceDrop lim q dtorCall rt i` | `canon_resource_drop` (L2246-2263) |
| `resourceRep lim rt i` | `canon_resource_rep` (L2267-2271) |

The table-manipulating cores are `resourceNewCore`, `resourceDropCore` and `resourceRepCore`
of `Canon/Handles.lean`, reused here unchanged; this file adds the `may_leave` entry
checks, the destructor call of `resource.drop` and the flat results. Flat arguments arrive
already decoded (`rep`, `i : Nat`); the late-bound dispatcher decodes them.

**Destructor call.** REF `canon_resource_drop` performs, for an own handle,
`store.lower(store.lift(rt.dtor or (lambda rep: []), ft, opts, rt.impl), ft, opts, inst)`
applied to `[h.rep]`, with `ft = FuncType([U32Type()], [])` and synchronous empty options:
a real synchronous cross-component call (a `canon_lower` into a `canon_lift`), made even
when `rt.impl is inst` and even when there is no destructor: the no-op call is a synchronous
`canon_lift` in the implementing instance like any other, which registers a thread there (and
so traps `tableFull` when that instance's thread table is full, L677) but runs no core code
(`Canon.canonLiftNoop`). A host resource (`rt.impl` is `none`, which REF does not have) makes
no call.
Because the program building this call (`destructorCall`) lives in `Canon/Lift.lean`, which
this file does **not** import, `resourceDrop` takes it as the parameter
`dtorCall : InstId → DtorRequest E → P E σ Unit`, instantiated by the dispatcher
with a late-bound `call`. Its arguments are the calling instance `inst` (REF `lower(...,
inst)`) and the `DtorRequest` returned by `resourceDropCore` (the resource type, REF
`rt.impl`, REF `rt.dtor` with `none` = the no-op lambda, and `h.rep`).

**Flat results.** `resource.new` returns the new handle index as an `i32`. `resource.rep`
returns `h.rep` as a flat value of the resource type's representation width
(`ResourceType.rep`: `i32`, or `i64` under memory64 resources); `resource.drop` returns `[]`.

**Convention.** Programs take `(lim : Limits)` as their leading argument (unused: the handle
bound is the fixed `Runtime.Table.maxLength`); `resourceDrop` also takes `(q : Quirks)` for
uniformity with the other built-ins, but has no quirk branch (only `Quirks.none` is the
specification, and no wasmtime quirk concerns `resource.drop`).

## Deviations and non-claims

* The destructor-call hook has type `InstId → DtorRequest E → P E σ Unit` rather than `E.FuncAddr →
  Nat → InstId → P E σ Unit`: REF calls the no-op `lambda rep: []` when `rt.dtor is None`, and
  `rt.impl` may be the host (`none`), so neither a `FuncAddr` nor an implementing `InstId` always
  exists. The request carries both options.
* REF asserts (D-f) are preconditions: `resource.drop` of an own handle asserts
  `h.borrow_scope is None` (unchecked here; `Handles.lean`); the "current instance exists"
  assertion of `current_instance()` reaches `internal` when violated (`currentInst`).
* `resource.rep` performs no `may_leave` check, exactly as REF.
* No tests here (`Examples/Resources.lean` and `Examples/Linked.lean` test these built-ins
  end to end). Invariant
  preservation lemmas (`P.Inv`) are proved below under exactly the hypotheses of the cores
  plus, for `resourceDrop`, preservation by the supplied destructor-call program.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type}

/-- REF `inst = current_instance(); trap_if(not inst.may_leave)`, the entry check of
`canon_resource_new` (L2238-2239) and `canon_resource_drop` (L2247-2248): the current
instance, trapping `cannotLeave` when it may not currently leave. -/
def resourceEnter : P E σ InstId := do
  let inst ← currentInst
  trapIf (!(← getInst inst).mayLeave) .cannotLeave
  return inst

/-- REF `canon_resource_new(rt, rep)` (L2237-2242): trap `cannotLeave` unless the current
instance may leave, then add `ResourceHandle(rt, rep, own = True)` to its handle table (trap
`tableFull`; `resourceNewCore`) and return `[i]` as an `i32`. -/
def resourceNew (lim : Limits) (rt : RtId) (rep : Nat) : P E σ (List FlatValue) := do
  let inst ← resourceEnter
  let i ← resourceNewCore lim inst rt rep
  return [i32Flat i]

/-- REF `canon_resource_drop(rt, i)` (L2246-2263): trap `cannotLeave` unless the current
instance may leave; `h = inst.handles.remove(i)` (trap `unknownHandle`), trap unless a
resource handle (`wrongHandleType`) of type `rt` (`resourceTypeMismatch`) with
`num_lends == 0` (`ownLent`) (`resourceDropCore`). For an own handle, make the synchronous
destructor call `dtorCall inst req` (REF `store.lower(store.lift(rt.dtor or noop, ...,
rt.impl), ..., inst)([h.rep])`, L2253-2259; supplied by the dispatcher through a late-bound call,
see the module docstring); for a borrow handle `h.borrow_scope.num_borrows -= 1` (L2261-2262,
done inside `resourceDropCore`; the scope task may be another task than the current one).
Returns `[]`. The `Quirks` argument has no branch here. -/
def resourceDrop (lim : Limits) (_q : Quirks) (dtorCall : InstId → DtorRequest E → P E σ Unit)
    (rt : RtId) (i : Nat) : P E σ (List FlatValue) := do
  let inst ← resourceEnter
  match ← resourceDropCore lim inst rt i with
  | some req => dtorCall inst req
  | none => pure ()
  return []

/-- REF `canon_resource_rep(rt, i)` (L2267-2271): NO `may_leave` check;
`h = current_instance().handles.get(i)` (trap `unknownHandle`), trap unless a resource handle
(`wrongHandleType`) of type `rt` (`resourceTypeMismatch`) (`resourceRepCore`); return
`[h.rep]` at the representation width of `rt` (`ResourceType.rep`). -/
def resourceRep (lim : Limits) (rt : RtId) (i : Nat) : P E σ (List FlatValue) := do
  let inst ← currentInst
  let rep ← resourceRepCore lim inst rt i
  let rty ← getResourceType rt
  return [ptrFlat rty.rep rep]

/-! ## Invariant preservation -/

namespace Inv

variable {I : CStore E → Prop}

end Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon.Builtins
