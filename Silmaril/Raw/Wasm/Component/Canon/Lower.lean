module

public import Silmaril.Wasm.Component.Reference.Canon.Lower.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Lower.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Flat
public import Silmaril.Raw.Wasm.Component.Runtime.Waitable

/-!
# `canon lower` (sync and async) and the caller-side `on_start`/`on_resolve`

Transcribes REF `canon_lower` of `design/mvp/canonical-abi/definitions.py` at component-model
`a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
L2169-2233; `CanonicalABI.md` §"`canon lower`") as specification programs in `P E σ`:

| Lean | REF (lines) |
| --- | --- |
| `lowerLimits` | the `max_flat_params`/`max_flat_results` choice (L2177-2182) |
| `canonLower lim q callee ft opts inst flatArgs` | `canon_lower` (L2169-2233) |
| `lowerOnStart lim q c` | the `on_start` closure of `canon_lower` (L2188-2192) |
| `lowerOnResolve lim q c r` | the `on_resolve` closure of `canon_lower` (L2194-2206) |
| `maybeOnProgress s` | `maybe_on_progress()` (L2186, L2222-2229) |
| `LowerSt.*` | the named store updates these programs issue |

**Defunctionalization.** The pair `(on_start, on_resolve)` handed to the callee is the arena
record `Runtime.Caller.lower s cx flatArgs pos ft maxParams maxResults` (`Runtime/Objects.lean`)
allocated by `canonLower`; the dispatcher runs `Call.onStart c` / `Call.onResolve c r`
of such a record as `lowerOnStart lim q c` / `lowerOnResolve lim q c r`. The record holds the
SHARED REF `CoreValueIter` over the caller's flat arguments as the list `flatArgs` and the
position `pos`: `lowerOnStart` lifts the parameters from `⟨flatArgs, pos⟩` and writes the
advanced position back into the record (`LowerSt.setCallerPosSt`), and `lowerOnResolve` uses the
cursor at that position as the out-parameter of `lower_flat_values` (the trailing return
pointer). The borrow scope of `cx` is the subtask (`BorrowScope.subtask s`), so borrows lifted
by `lowerOnStart` make the caller's handles lenders of `s` (`Canon.liftBorrow`).

**`maybe_on_progress`.** REF rebinds the closure variable `maybe_on_progress` from a no-op to
`on_progress` once an async lower added the subtask to the caller's handle table
(L2221-2229). Here the mode is the recorded caller handle index `Subtask.index`: `none` (sync
lower, or async lower before the handle was added) is the no-op, `some i` sets the pending event
`PendingEvent.subtask s` (REF `subtask_event`, run at delivery by `Waitable.getPendingEvent`,
`Runtime/Waitable.lean`, which reads `index` as the captured `subtaski`). The index is set in
the same named update as `inst.handles.add(subtask)` (`LowerSt.addSubtaskSt`, issued by
`handlesAddSubtask`), i.e. AFTER the callee ran, as in REF, where `subtaski` is the value of
`handles.add` itself (L2223): a subtask is never in a handle table without its index.

**Async result.** The `i32` returned by an async lower is `AsyncRef.AsyncLowerResult.pack`:
`.returned` (REF `[Subtask.State.RETURNED]`) or `.pending state subtaski` (REF
`[subtask.state | (subtaski << 4)]`).

## Deviations and non-claims

* D-f: REF asserts are preconditions, not checked: `types_match_values(flat_ft.params,
  flat_args)` and the result shape of the sync branch; `ft.async_ or subtask.state ==
  RETURNED` after the callee returned; `STARTING` in `on_start`; `STARTED` (and, for `None`,
  `cancellation_requested`) in `on_resolve`; `flat_results == []` in the eager async branch;
  `0 < subtaski <= Table.MAX_LENGTH` and `state < 2^4` (facts about `handlesAdd` and
  `SubtaskState`, see `AsyncRef.AsyncLowerResult.WellFormed`).
* `Store.lower`'s `assert(inst is current_instance())` (L548) is checked, by the entry check
  `Canon.calloutEntry` of the only caller of `canonLower`, the dispatched callout program
  `Canon.hostCalloutProg`: a lowered callout from a thread of another instance, or from a host
  frame, traps `internal` before `canonLower` runs (REF asserts before `canon_lower` reads
  `may_leave`, L2171). So `canonLower` runs on a thread of the instance `inst` it takes, which
  is REF's `current_thread().task.inst`, and checks `may_leave` on it.
* A `Call.onStart`/`Call.onResolve` of a caller record that is not `Caller.lower` reaching
  `lowerOnStart`/`lowerOnResolve` is an `internal` trap (the dispatcher only routes
  `Caller.lower` records here).
* `Quirks.lendReleaseAtReturn` (wasmtime's `validate_scope_exit`; NOT the specification): when
  set, `lowerOnResolve` releases the subtask's lends at the callee's completion, i.e. on both
  `task.return` (after lowering the results) and `task.cancel` (`on_resolve(None)`, before
  resolving) (`LowerSt.releaseLendsSt`: every lender's `num_lends -= 1`, `lenders := []`, the
  subtask staying not-yet-delivered). This models wasmtime a7b4f29
  `crates/wasmtime/src/runtime/component/concurrent.rs` `task_complete`, shared by `task_return`
  and `task_cancel`, which calls `validate_scope_exit`; the later `deliver_resolve` then finds
  no lenders (for `CANCELLED_BEFORE_STARTED` there are none anyway, as `on_start` never ran).
  With `Quirks.none` the lends are released only by REF
  `deliver_resolve` (sync: before `canon_lower` returns; async: when the `SUBTASK` event of
  the resolution is delivered, or eagerly in the resolved-before-return branch).
* Proved here: `P.Inv` lemmas for every program under `LowerPres I` (the named updates issued
  preserve `I`). No conformance test is ported here (the end-to-end tests run through the
  machine in `Examples/` and `Tests/`); nothing is claimed about results.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI

variable {E : CoreEngine} {σ : Type}

/-! ## Named store updates -/

namespace LowerSt

/-- `addSubtaskSt` preserves every invariant that its two parts, the table insertion and the
index write, preserve. -/
theorem addSubtaskSt_pres {I : CStore E → Prop} {inst : InstId} {sub : SubtaskId} {i : Nat}
    (ha : ∀ s, I s →
      I (ArenaField.insts.modify s inst (InstState.addHandle (.waitable (.subtask sub)))))
    (hi : ∀ s, I s → I (setIndexSt sub i s)) {s : CStore E} (h : I s) :
    I (addSubtaskSt inst sub i s) := by
  unfold addSubtaskSt
  split
  · exact h
  · exact hi _ (ha _ h)

/-- After `addSubtaskSt inst s i`, subtask `s` carries the index `i` (and is otherwise
unchanged). -/
theorem subtask?_addSubtaskSt (inst : InstId) (s : SubtaskId) (i : Nat) (st : CStore E) :
    (addSubtaskSt inst s i st).subtask? s =
      (st.subtask? s).map fun x => { x with index := some i } := by
  unfold addSubtaskSt
  split
  · rename_i h; rw [h]; rfl
  · simp only [setIndexSt, CStore.subtask?, ArenaField.get?_modify_self]
    rfl

end LowerSt

/-! ## Programs -/

theorem lowerLimits_sync : lowerLimits false = (16, 1) := rfl
theorem lowerLimits_async : lowerLimits true = (4, 0) := rfl

/-! ## Program-logic lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

/-- The eager async result is `RETURNED = 2`. -/
example : AsyncRef.AsyncLowerResult.returned.pack = 2 := by decide

/-- A pending async lower of subtask index 3 in state `STARTED` returns `1 | (3 << 4)`. -/
example : (AsyncRef.AsyncLowerResult.pending .started 3).pack = 0x31 := by decide

/-- Setting the shared cursor position only touches `Caller.lower` records. -/
example (x : CallId) :
    LowerSt.Caller.withPos (E := E) (.host x [] 0) 5 = .host x [] 0 := rfl

end Silmaril.Wasm.Component.Canon
