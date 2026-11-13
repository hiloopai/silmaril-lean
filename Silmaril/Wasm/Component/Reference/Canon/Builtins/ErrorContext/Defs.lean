module

public import Silmaril.Wasm.Component.Reference.Canon.Strings.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs

/-!
# The `error-context` built-ins

Transcribes the 📝 built-ins of REF `design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
as specification programs in `P E σ` (`CanonicalABI.md` §"`canon error-context.new`" and the two
following sections):

| Lean | REF (line) |
| --- | --- |
| `errorContextNew lim q opts ptr units` | `canon_error_context_new` (L2667-2678) |
| `errorContextDebugMessage lim q opts i ptr` | `canon_error_context_debug_message` (L2681-2689) |
| `errorContextDrop i` | `canon_error_context_drop` (L2692-2697) |

Each built-in returns the flat core results (`List FlatValue`) the dispatcher hands
back to core code; `ptr`, `units` and `i` are the unsigned values of the flat arguments.
An `ErrorContext` object lives in the `errCtxs` arena of the store and is referenced from
`inst.handles` by `HandleEntry.errCtx`.

## Choices

* C6a (`choose .errCtxKeep`): REF `if DETERMINISTIC_PROFILE or random.randint(0,1)`. The answer
  `false` takes the REF discard branch: the message is `String(('', 'utf8', 0))`
  (`ErrorContext.empty`) and memory is NOT read (so an invalid `ptr` does not trap). The
  deterministic profile only admits `false` (`Allowed`). The answer `true` runs
  `load_string_from_range` (which may trap) and then
* C6b (`choose (.errCtxMessage s)`): REF `host_defined_transformation(s)`.

## Deviations and non-claims

* D-d: `errorContextDebugMessage` checks, before storing anything, that the two-pointer slot
  `[ptr, ptr + 2 * ptr_size)` is in bounds (`outOfBounds`) and aligned to `ptr_size`
  (`unalignedPointer`). The bounds check follows wasmtime (`error_context_debug_message`,
  `crates/wasmtime/src/runtime/component/concurrent/futures_and_streams.rs` at `a7b4f29`,
  L4347-4352), which rejects an out-of-bounds slot before lowering the string, but always
  checks a fixed 8 bytes (its FIXME #4311), even for memory64, where Silmaril checks
  `2 * ptr_size` = 16 bytes. Wasmtime does not trap on misalignment: `str::linear_lower_to_memory`
  (`crates/wasmtime/src/runtime/component/func/typed.rs` L1352) only `debug_assert!`s it. The
  `unalignedPointer` trap is therefore a Silmaril addition beyond both REF and wasmtime, made for
  uniformity with `storeU32`/`unpackEvent` (D-d). REF neither traps nor asserts here:
  `store_string` writes the slot with two `store_int`s, raw slice assignments into the memory
  `bytearray` (L1533-1536), so an out-of-bounds slot would silently grow the Python
  `bytearray`. A trap from these checks leaves memory unchanged and happens before any
  `realloc` call.
* D-a: the stored message is a `StrVal` (REF tuple plus source pointer width); storing it goes
  through `Canon.storeString`, which re-tags a UTF-16-tagged `latin1+utf16` count for the
  destination width (raw REF behaviour under `q.refUtf16TagBug`).
* D-f: `store_string`'s asserts (`StoreStringPre`: a consistent source string, and the
  `REALLOC_I32_MAX` bounds of `store_string_into_range`) are preconditions of
  `errorContextDebugMessage`, not traps. A C6b answer is `Allowed` only when consistent, but
  nothing bounds its length: `host_defined_transformation` may return a longer string than the
  one `load_string_from_range` read, and a large enough message violates the
  `REALLOC_I32_MAX` bounds. REF then fails the same assert, so this is no divergence; the
  precondition is not discharged by the oracle.
* The handle type test `trap_if(not isinstance(errctx, ErrorContext))` traps
  `wrongHandleType`.
* `errorContextNew` and `errorContextDebugMessage` take the leading `(lim : Limits)
  (q : Quirks)` of the calling convention because they call `loadStringFromRange lim q`
  resp. `storeString lim q` (the latter has the `refUtf16TagBug` quirk branch).
* Not modelled here: the dispatch of the core call, the late-bound `realloc`,
  and any test (the built-ins are tested end to end in `Examples/Misc.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-- REF `canon_error_context_new(opts, ptr, tagged_code_units)` (L2667-2678):
`trap_if(not inst.may_leave)`; C6a: on `false` (always under the deterministic profile) the
message is the empty REF string without reading memory; on `true`,
`load_string_from_range(LiftLowerContext(opts, inst), ptr, tagged_code_units)` (may trap)
followed by C6b `host_defined_transformation`; then `inst.handles.add(ErrorContext(s))`
(may trap `tableFull`) and return `[i]`. -/
def errorContextNew (lim : Limits) (q : Quirks) (opts : CanonOpts E) (ptr units : Nat) :
    P E σ (List FlatValue) := do
  let inst ← currentInst
  trapIf (!(← getInst inst).mayLeave) .cannotLeave
  let keep ← choose .errCtxKeep
  let msg ← (if keep then do
      let s ← loadStringFromRange lim q { opts := opts, inst := inst } ptr units
      choose (.errCtxMessage s)
    else pure ErrorContext.empty.message : P E σ StrVal)
  let x ← allocObj ArenaField.errCtxs ⟨msg⟩
  let i ← handlesAdd inst (.errCtx x)
  return [i32Flat i]

/-- The error context of a handle entry (REF `isinstance(errctx, ErrorContext)`), trapping
`wrongHandleType` for any other entry. -/
def expectErrCtx : HandleEntry → P E σ ErrCtxId
  | .errCtx x => pure x
  | _ => trap .wrongHandleType

/-- REF `canon_error_context_debug_message(opts, i, ptr)` (L2681-2689):
`trap_if(not inst.may_leave)`; `errctx = inst.handles.get(i)` (trap `unknownHandle`);
`trap_if(not isinstance(errctx, ErrorContext))`; then (D-d) check the alignment and bounds of
the two-pointer slot at `ptr`; then `store_string(LiftLowerContext(opts, inst),
errctx.debug_message, ptr)`; return `[]`.
Precondition (REF asserts in `store_string`, D-f): `StoreStringPre q opts.encoding dst msg`
for the destination pointer width `dst`. -/
def errorContextDebugMessage (lim : Limits) (q : Quirks) (opts : CanonOpts E) (i ptr : Nat) :
    P E σ (List FlatValue) := do
  let inst ← currentInst
  trapIf (!(← getInst inst).mayLeave) .cannotLeave
  let x ← expectErrCtx (← handlesGet inst i)
  let ec ← getObj ArenaField.errCtxs x
  let cx : LiftLowerContext E := { opts := opts, inst := inst }
  let sz ← ptrSize cx
  checkAligned ptr sz
  checkInBounds cx ptr (2 * sz)
  storeString lim q cx ec.message ptr
  return []

/-- REF `canon_error_context_drop(i)` (L2692-2697): `trap_if(not inst.may_leave)`;
`errctx = inst.handles.remove(i)` (trap `unknownHandle`);
`trap_if(not isinstance(errctx, ErrorContext))` (after the removal, as in REF; the trap locks
the store down); return `[]`. The `ErrorContext` object itself stays in its arena (REF
objects are garbage collected; arena ids are never freed). -/
def errorContextDrop (i : Nat) : P E σ (List FlatValue) := do
  let inst ← currentInst
  trapIf (!(← getInst inst).mayLeave) .cannotLeave
  let _ ← expectErrCtx (← handlesRemove inst i)
  return []

/-! ## Unfolding facts -/

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon.Builtins
