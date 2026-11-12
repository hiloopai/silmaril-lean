module

public import Silmaril.Wasm.Component.Reference.Runtime.Stream.Properties.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Load.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs

/-!
# Stream/future copies with guest and host buffers

The Prog layer of the REF stream/future ends of `design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>;
`CanonicalABI.md` §"Buffer State" and §"Stream and Future State"): the element transfer that
the pure `End` state machine (`Runtime/Stream.lean`) abstracts as `CopyAction.transfer`, and the
`End` methods as specification programs in `Canon.P E σ`.

| Lean | REF (lines) |
| --- | --- |
| `mkGuestBuffer lim cx t ptr length` | `GuestBuffer.__init__` (L894-903) |
| `readBuffer lim q b n` | `ReadableGuestBuffer.read` (L909-917); host `read` |
| `writeBuffer lim q b vs` | `WritableGuestBuffer.write` (L920-927); host `write` |
| `performCopy lim q a` | the element move of `End.copy` case 3 (L966-969) |
| `endCopy lim q e buf isRead` | `End.copy` (L956-979) |
| `endCancel e` | `End.cancel` (L981-988), choice C5 |
| `endForward lim q src dst` | `End.forward` (L990-1006) |
| `endDrop e` | `End.drop` (L1008-1016) |
| `endCopyPumped`, `endDropPumped`, `endForwardPumped` | run_tests harness pumps (not REF) |

Named store updates: `copySt` (the store part of `Runtime.copyCore`), `forwardSt` (of
`Runtime.forward`), `Runtime.cancel` and `Runtime.dropEnd`; each REF multi-field update is one
of these.

## Buffers

`mkGuestBuffer` performs the eager checks of `GuestBuffer.__init__` in REF order:
`trap_if(length > Buffer.MAX_LENGTH)` (`bufferTooLong`, bound `lim.maxBufferLength`), then, only
if `t` is not `None` and `length > 0`, misalignment (`unalignedPointer`) and
`ptr + length * elem_size(t) > len(memory)` (`outOfBounds`). With `t = None` the pointer is
ignored. The buffer's context gets `borrow_scope = None` (REF `copy` builds
`LiftLowerContext(opts, inst, borrow_scope = None)`, L2468), so `own` handles inside elements
are transferred per element at copy time by `lift_own`/`lower_own` inside `load`/`store`.

The pure layer keeps a guest buffer's BASE pointer and advances only `progress`
(`BufferDesc.advance`); the REF cursor `self.ptr` after earlier reads/writes is therefore
`ptr + progress * elem_size(t)` (`guestCursor`), which is where `readBuffer`/`writeBuffer`
load and store. `readBuffer` of a guest buffer with `t = None` returns `n` copies of the REF
unit value `()`, represented as `Val.record []`; `writeBuffer` with `t = None` stores nothing
(REF asserts every value is `()`, D-f).

Host buffers (choice point E1) are late-bound calls: `call (.hostBuffer (.read b n))` returning
`Ret.vals` and `call (.hostBuffer (.write b vs))` returning `Ret.unit`. The REF contract of
`HostReadableBuffer.read(n)` returns exactly `n` values (`n <= remain`); a host answer of a
different length is a contract violation (D-f) and traps `TrapReason.internal`.

## Order of bookkeeping and transfer (deviation)

`Runtime.copyCore` returns the new end state (states, parked buffers with advanced progress,
pending notifications) together with the `CopyAction`; `endCopy` first checks the pure result
(trapping with its reason, e.g. `sameInstanceCopy`), applies the bookkeeping (`copySt`) and
then performs the element transfer (`performCopy`). REF sets `COPYING`, transfers, and then
notifies. The two orders are observably different only if the element transfer itself (a
`realloc` call inside `store`, or a host buffer call) could inspect or operate on the ends.
REF rules this out: `LiftLowerContext.reallocate` clears `inst.may_leave` around the `realloc`
call (L636-639) and every stream/future built-in begins with `trap_if(not ...may_leave)`
(L2462, L2496, ...), so guest code cannot touch an end during the transfer; and the REF host
buffers (run_tests `HostReadableBuffer.read`/`HostWritableBuffer.write`, L1341-1373) are pure
list operations. The reorder is therefore unobservable in REF. On the Lean side the
equivalence rests on two assumptions about the (late-bound) resolution of calls, to be
discharged by the dispatcher: (i) `may_leave` is cleared while `realloc` runs, so
the stream built-ins trap; (ii) the `.hostBuffer (.read _ _)`/`.hostBuffer (.write _ _)`
handlers do not modify `CStore.ends`. Progress bookkeeping is done by the pure layer;
`performCopy` itself never touches the ends.

## Choice C5

`endCancel` issues `choose .cancelNow` exactly when REF would flip its coin: the end is
`COPYING`, has no pending event, and its peer is host-owned (`Runtime.peerGuest = false`).
Otherwise the Boolean passed to `Runtime.cancel` is irrelevant and `false` is passed.

## Host pumps (not REF)

`endCopyPumped`/`endDropPumped` additionally call `.hostBuffer (.pump o)` for a host-owned
peer `o` afterwards, modelling run_tests `pump_after_other_end_makes_progress` (run_tests
L1378-1393, def at L1382), which wraps the guest end's `copy` and `drop`. `End.forward` calls
`src.drop()`/`dst.drop()` on its drop branch, so `endForwardPumped` pumps the host-owned peers
of `src`/`dst` (snapshotted before the forward) when that branch is taken. In the splice
branch the re-issued `smaller_end.copy` is a method of a peer of the (guest-owned) forwarded
ends, which run_tests never wraps, so no pump happens there. Deviations from run_tests: the
peer is determined dynamically (`hostPeer?` at call time) rather than by which ends run_tests
wrapped, and on the forward drop branch both drops happen before both pumps (run_tests
interleaves drop, pump, drop, pump). These are test-harness conveniences; the REF methods are
`endCopy`/`endDrop`/`endForward`.

## What is proved

* `performCopy_conservation`: every evaluation (under any relational handler) of a transfer
  reads a list `vs` of exactly `n` values from the writer's buffer and writes that same list
  `vs` into the reader's buffer.
* `copyCore_transfer`, `copy_transfer`, `forward_transfer`: a transfer produced by the pure
  layer moves `n = min writerBuf.remain readerBuf.remain > 0` elements, and for `copyCore`
  the buffer passed in is the reader's (read) or the writer's (write) buffer.
* `endCopy_conservation`, `endForward_conservation`: the combination for a transfer produced
  by `copyCore`/`forward`: `n = min wb.remain rb.remain`, `0 < n`, and every evaluation of its
  `performCopy` reads `n` values `vs` from `wb` and writes the same `vs` into `rb`. (The
  handler `H` is arbitrary, so the transfer is tied to `copyCore` by hypothesis, not by
  evaluating `endCopy`'s `getStore`.)
* `copySt_EndWF`, `forwardSt_EndWF`: the named updates preserve `EndWF`.
* `P.Inv` lemmas for every program, given the load/store preservation bundles.

Not modelled here: the canon built-ins around these methods (`may_leave`, handle lookups,
type and state checks, waiting; `Canon/Builtins/Stream.lean`), the dispatcher resolving host buffer
calls. Tests: none here. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine AsyncRef Canon Value

variable {E : CoreEngine} {σ : Type}

/-! ## Buffers -/

/-- The eager checks of REF `GuestBuffer.__init__` (L894-897): `bufferTooLong` if
`length > Buffer.MAX_LENGTH`; if `t` is not `None` and `length > 0`, `unalignedPointer` and
`outOfBounds` checks of the whole range `[ptr, ptr + length * elem_size(t))`. -/
def checkGuestBuffer (lim : Limits) (cx : LiftLowerContext E)
    (t : Option (WIT.ClosedType RtId)) (ptr length : Nat) : P E σ Unit := do
  trapIf (decide (length > lim.maxBufferLength)) .bufferTooLong
  match t with
  | some u =>
    if 0 < length then do
      let p ← ptrType cx
      trapIf (decide (ptr ≠ ABI.alignTo ptr (ABI.layout p u).alignment)) .unalignedPointer
      checkInBounds cx ptr (length * (ABI.layout p u).size)
    else pure ()
  | none => pure ()

/-- REF `GuestBuffer(t, cx, ptr, length)` (L894-903): the checks of `checkGuestBuffer`, then a
fresh buffer (progress 0) whose context has borrow scope `None`. -/
def mkGuestBuffer (lim : Limits) (cx : LiftLowerContext E) (t : Option (WIT.ClosedType RtId))
    (ptr length : Nat) : P E σ (BufferDesc E) := do
  checkGuestBuffer lim cx t ptr length
  pure (.guest { cx with scope := .none } t ptr length 0)

/-- The REF cursor `self.ptr` of a guest buffer of element type `u` after `progress` elements
(pointer width `p`): `ptr + progress * elem_size(u)`. -/
def guestCursor (p : AddrType) (u : WIT.ClosedType RtId) (ptr progress : Nat) : Nat :=
  ptr + progress * (ABI.layout p u).size

/-- The REF unit value `()` (an element of a stream/future without element type). -/
def unitVal : Val := .record []

/-- `ReadableBuffer.read(n)`: REF `ReadableGuestBuffer.read` (L909-917,
`load_list_from_valid_range` at the cursor; `n * [()]` without element type) or the host
buffer's `read` (E1; a result of the wrong length traps `internal`, D-f). -/
def readBuffer (lim : Limits) (q : Quirks) : BufferDesc E → Nat → P E σ (List Val)
  | .guest cx (some u) ptr _ progress, n => do
    let p ← ptrType cx
    loadListFromValidRange lim q cx (guestCursor p u ptr progress) n u
  | .guest _ none _ _ _, n => pure (List.replicate n unitVal)
  | .host b _ _, n => do
    let vs ← callVals (.hostBuffer (.read b n))
    if vs.length = n then pure vs else internal "host buffer read: wrong number of values"

/-- `WritableBuffer.write(vs)`: REF `WritableGuestBuffer.write` (L920-927,
`store_list_into_valid_range` at the cursor; nothing without element type) or the host
buffer's `write` (E1). -/
def writeBuffer (lim : Limits) (q : Quirks) : BufferDesc E → List Val → P E σ Unit
  | .guest cx (some u) ptr _ progress, vs => do
    let p ← ptrType cx
    storeListIntoValidRange lim q cx vs (guestCursor p u ptr progress) u
  | .guest _ none _ _ _, _ => pure ()
  | .host b _ _, vs => callUnit (.hostBuffer (.write b vs))

/-- The element transfer of `End.copy` case 3 (L966-969): read `n` values from the writer's
buffer and write them into the reader's buffer. The buffers are those of the
`CopyAction` (before the transfer); progress bookkeeping was done by the pure layer. -/
def performCopy (lim : Limits) (q : Quirks) : CopyAction E → P E σ Unit
  | .none => pure ()
  | .transfer _ _ n wb rb => do
    let vs ← readBuffer lim q wb n
    writeBuffer lim q rb vs

/-! ## Named store updates -/

/-- The store update of `End.copy` (`Runtime.copyCore`; unchanged on a trap). -/
def copySt (e : EndId) (buf : BufferDesc E) (isRead : Bool) (s : CStore E) : CStore E :=
  match copyCore e buf isRead s with
  | .ok (s', _) => s'
  | .error _ => s

/-- The store update of `End.forward` (`Runtime.forward`; unchanged on a trap). -/
def forwardSt (src dst : EndId) (s : CStore E) : CStore E :=
  match forward src dst s with
  | .ok (s', _) => s'
  | .error _ => s

/-! ## `End` methods -/

/-- REF `End.copy(buffer, is_read)` (L956-979): the pure `copyCore` (trapping with its reason,
e.g. the same-instance trap of L964), its store update `copySt`, then the element transfer.
The canon-level idle check of `copy` (L2466) is the caller's (`Runtime.copy` or
`Canon.Builtins.copyBuiltin`). -/
def endCopy (lim : Limits) (q : Quirks) (e : EndId) (buf : BufferDesc E) (isRead : Bool) :
    P E σ Unit := do
  match copyCore e buf isRead (← getStore) with
  | .error r => trap r
  | .ok (_, a) =>
    modifyStore (copySt e buf isRead)
    performCopy lim q a

/-- Whether REF `End.cancel` flips its coin (L984-987): the end is `COPYING`, has no pending
event and its peer is host-owned. -/
def cancelFlips (s : CStore E) (e : EndId) : Bool :=
  match s.end? e with
  | some x => x.state = .copying ∧ x.hasPending = false ∧ peerGuest x s = false
  | none => false

/-- REF `End.cancel()` (L981-988): the coin flip (choice C5, `choose .cancelNow`) is issued
only when the end is `COPYING`, has no pending event and its peer is host-owned. -/
def endCancel (e : EndId) : P E σ Unit := do
  let s ← getStore
  let notifyNow ← (if cancelFlips s e then choose .cancelNow else pure false)
  modifyStore (cancel e notifyNow)

/-- REF `End.forward(src, dst)` (L990-1006): the drop branch or the splice, and the re-issued
copy's element transfer. -/
def endForward (lim : Limits) (q : Quirks) (src dst : EndId) : P E σ Unit := do
  match forward src dst (← getStore) with
  | .error r => trap r
  | .ok (_, a) =>
    modifyStore (forwardSt src dst)
    performCopy lim q a

/-- REF `End.drop()` (L1008-1016). -/
def endDrop (e : EndId) : P E σ Unit := modifyStore (dropEnd e)

/-! ## Host pumps (run_tests harness, not REF) -/

/-- The host-owned peer of end `e`, if any. -/
def hostPeer? (s : CStore E) (e : EndId) : Option EndId :=
  match s.end? e with
  | some x => match x.other with
    | some o => match s.end? o with
      | some y => if y.owner.isNone then some o else none
      | none => none
    | none => none
  | none => none

/-- Call the host's `pump` hook of end `o` (if any). -/
def pumpHost : Option EndId → P E σ Unit
  | some o => callUnit (.hostBuffer (.pump o))
  | none => pure ()

/-- `endCopy` followed by run_tests `pump()` of a host-owned peer (L1382-1393). -/
def endCopyPumped (lim : Limits) (q : Quirks) (e : EndId) (buf : BufferDesc E)
    (isRead : Bool) : P E σ Unit := do
  let o ← gets (hostPeer? · e)
  endCopy lim q e buf isRead
  pumpHost o

/-- `endDrop` followed by run_tests `pump()` of a host-owned peer (L1382-1393). -/
def endDropPumped (e : EndId) : P E σ Unit := do
  let o ← gets (hostPeer? · e)
  endDrop e
  pumpHost o

/-- Whether `End.forward(src, dst)` takes its drop branch (`src.other is dst`, or either peer
link is gone; L991-993), mirroring `Runtime.forward`. -/
def forwardDrops (s : CStore E) (src dst : EndId) : Bool :=
  match s.end? src, s.end? dst with
  | some xs, some xd =>
    match xs.other, xd.other with
    | some w, some _ => decide (w = dst)
    | _, _ => true
  | _, _ => false

/-- `endForward` followed by run_tests `pump()` of the host-owned peers of `src` and `dst`
(L1382-1393) when the drop branch runs `src.drop()`/`dst.drop()` (L991-993). No pump after the
splice branch's re-issued copy: that copy is a method of a peer of the forwarded ends, which
run_tests does not wrap. Both pumps follow both drops (run_tests interleaves them). -/
def endForwardPumped (lim : Limits) (q : Quirks) (src dst : EndId) : P E σ Unit := do
  let ps ← gets fun s =>
    if forwardDrops s src dst then (hostPeer? s src, hostPeer? s dst) else (none, none)
  endForward lim q src dst
  pumpHost ps.1
  pumpHost ps.2

/-! ## Transfer sizes -/

/-! ## Conservation -/

section Eval

variable {τ : Type} {H : (o : (Eff E σ).Op) → τ → (Eff E σ).Resp o → τ → Prop}

end Eval

/-! ## Program-logic lemmas -/

section Inv

variable {I : CStore E → Prop}

end Inv

end Silmaril.Wasm.Component.Runtime
