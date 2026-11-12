module

public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Stream.Properties
public import Silmaril.Raw.Wasm.Component.Canon.Load
public import Silmaril.Raw.Wasm.Component.Canon.Store

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

open Engine Async Canon Value

variable {E : CoreEngine} {σ : Type}

/-! ## Buffers -/

/-! ## Named store updates -/

theorem copySt_eq {e : EndId} {buf : BufferDesc E} {isRead : Bool} {s s' : CStore E}
    {a : CopyAction E} (h : copyCore e buf isRead s = .ok (s', a)) :
    copySt e buf isRead s = s' := by
  simp only [copySt, h]

theorem forwardSt_eq {src dst : EndId} {s s' : CStore E} {a : CopyAction E}
    (h : forward src dst s = .ok (s', a)) : forwardSt src dst s = s' := by
  simp only [forwardSt, h]

theorem copySt_EndWF {s : CStore E} (hw : EndWF s) (e : EndId) (buf : BufferDesc E)
    (isRead : Bool) : EndWF (copySt e buf isRead s) := by
  unfold copySt
  split
  · rename_i s' a h; exact copyCore_EndWF hw h
  · exact hw

theorem forwardSt_EndWF {s : CStore E} (hw : EndWF s) (src dst : EndId) :
    EndWF (forwardSt src dst s) := by
  unfold forwardSt
  split
  · rename_i s' a h; exact forward_EndWF hw h
  · exact hw

/-! ## `End` methods -/

/-! ## Host pumps (run_tests harness, not REF) -/

/-! ## Transfer sizes -/

/-- A transfer of `End.copy` moves `n = min(remains) > 0` elements; the given buffer is the
reader's buffer for a read and the writer's for a write. -/
theorem copyCore_transfer {e : EndId} {buf : BufferDesc E} {isRead : Bool} {s s' : CStore E}
    {w r : EndId} {n : Nat} {wb rb : BufferDesc E}
    (h : copyCore e buf isRead s = .ok (s', .transfer w r n wb rb)) :
    n = min wb.remain rb.remain ∧ 0 < n ∧
      (if isRead then r = e ∧ rb = buf else w = e ∧ wb = buf) := by
  unfold copyCore at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals
    rename_i hpos _ hr
    simp only [Except.ok.injEq, Prod.mk.injEq, CopyAction.transfer.injEq] at h
    obtain ⟨_, rfl, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by omega, by omega, ?_⟩
    simp [hr]

/-- `copy` (idle check, then `End.copy`) produces transfers of `min(remains) > 0` elements. -/
theorem copy_transfer {e : EndId} {buf : BufferDesc E} {isRead : Bool} {s s' : CStore E}
    {w r : EndId} {n : Nat} {wb rb : BufferDesc E}
    (h : copy e buf isRead s = .ok (s', .transfer w r n wb rb)) :
    n = min wb.remain rb.remain ∧ 0 < n ∧
      (if isRead then r = e ∧ rb = buf else w = e ∧ wb = buf) := by
  unfold copy at h
  split at h
  · cases h
  · split at h
    · exact copyCore_transfer h
    all_goals cases h

/-- The re-issued copy of `End.forward` moves `min(remains) > 0` elements. -/
theorem forward_transfer {src dst : EndId} {s s' : CStore E} {w r : EndId} {n : Nat}
    {wb rb : BufferDesc E} (h : forward src dst s = .ok (s', .transfer w r n wb rb)) :
    n = min wb.remain rb.remain ∧ 0 < n := by
  unfold forward at h
  repeat' split at h
  all_goals first
    | cases h
    | exact ⟨(copyCore_transfer h).1, (copyCore_transfer h).2.1⟩

/-! ## Conservation -/

section Eval

variable {τ : Type} {H : (o : (Eff E σ).Op) → τ → (Eff E σ).Resp o → τ → Prop}

/-- A program that traps has no evaluation. -/
theorem not_eval_trap {α : Type} {r : TrapReason} {s s' : τ} {a : α} :
    ¬ Prog.Eval H (trap r : P E σ α) s a s' := by
  intro h
  obtain ⟨x, _, _, _⟩ := Prog.Eval.op_inv h
  exact nomatch x

/-- `Prog.mapM` returns one result per element. -/
theorem eval_mapM_length {α β : Type} {f : α → P E σ β} :
    ∀ {xs : List α} {s s' : τ} {bs : List β},
      Prog.Eval H (Prog.mapM f xs) s bs s' → bs.length = xs.length
  | [], _, _, _, h => by
    simp only [Prog.mapM_nil, Prog.eval_pure_iff] at h
    rw [h.1]; rfl
  | a :: as, _, _, _, h => by
    rw [Prog.mapM_cons] at h
    obtain ⟨_, _, _, h2⟩ := Prog.Eval.bind_inv h
    obtain ⟨_, _, h3, h4⟩ := Prog.Eval.bind_inv h2
    simp only [Prog.eval_pure_iff] at h4
    rw [h4.1, List.length_cons, List.length_cons, eval_mapM_length h3]

/-- `ReadableBuffer.read(n)` returns exactly `n` values. -/
theorem readBuffer_length {lim : Limits} {q : Quirks} {b : BufferDesc E} {n : Nat} {s s' : τ}
    {vs : List Val} (h : Prog.Eval H (readBuffer (σ := σ) lim q b n) s vs s') :
    vs.length = n := by
  match b with
  | .guest cx (some u) ptr _ progress =>
    rw [readBuffer] at h
    obtain ⟨_, _, _, h2⟩ := Prog.Eval.bind_inv h
    unfold loadListFromValidRange at h2
    obtain ⟨_, _, _, h4⟩ := Prog.Eval.bind_inv h2
    unfold loadListFromValidRangeWith at h4
    rw [eval_mapM_length h4, List.length_range]
  | .guest _ none _ _ _ =>
    rw [readBuffer] at h
    simp only [Prog.pure_eq, Prog.eval_pure_iff] at h
    rw [h.1, List.length_replicate]
  | .host _ _ _ =>
    rw [readBuffer] at h
    obtain ⟨_, _, _, h2⟩ := Prog.Eval.bind_inv h
    split at h2
    · rename_i hl
      simp only [Prog.pure_eq, Prog.eval_pure_iff] at h2
      rw [h2.1]; exact hl
    · exact absurd h2 not_eval_trap

/-- **Conservation.** Every evaluation of the element transfer of a `CopyAction` reads a list
`vs` of exactly `n` values from the writer's buffer and writes that same list into the reader's
buffer. (With `copyCore_transfer`/`copy_transfer`/`forward_transfer`,
`n = min writerBuf.remain readerBuf.remain`.) -/
theorem performCopy_conservation {lim : Limits} {q : Quirks} {w r : EndId} {n : Nat}
    {wb rb : BufferDesc E} {s s' : τ} {u : Unit}
    (h : Prog.Eval H (performCopy (σ := σ) lim q (.transfer w r n wb rb)) s u s') :
    ∃ vs s₁, Prog.Eval H (readBuffer lim q wb n) s vs s₁ ∧ vs.length = n ∧
      Prog.Eval H (writeBuffer lim q rb vs) s₁ () s' := by
  rw [performCopy] at h
  obtain ⟨vs, s₁, h1, h2⟩ := Prog.Eval.bind_inv h
  exact ⟨vs, s₁, h1, readBuffer_length h1, h2⟩

/-- **Conservation of `End.copy`.** For a transfer produced by `copyCore`, `n` is
`min wb.remain rb.remain > 0`, the given buffer is the reader's (read) or writer's (write), and
every evaluation of its element move reads `n` values `vs` from `wb` and writes that same `vs`
into `rb`. -/
theorem endCopy_conservation {lim : Limits} {q : Quirks} {e : EndId} {buf : BufferDesc E}
    {isRead : Bool} {st st' : CStore E} {w r : EndId} {n : Nat} {wb rb : BufferDesc E}
    {s s' : τ} {u : Unit}
    (hc : copyCore e buf isRead st = .ok (st', .transfer w r n wb rb))
    (h : Prog.Eval H (performCopy (σ := σ) lim q (.transfer w r n wb rb)) s u s') :
    n = min wb.remain rb.remain ∧ 0 < n ∧
      (if isRead then r = e ∧ rb = buf else w = e ∧ wb = buf) ∧
      ∃ vs s₁, Prog.Eval H (readBuffer lim q wb n) s vs s₁ ∧ vs.length = n ∧
        Prog.Eval H (writeBuffer lim q rb vs) s₁ () s' :=
  let ⟨h1, h2, h3⟩ := copyCore_transfer hc
  ⟨h1, h2, h3, performCopy_conservation h⟩

/-- **Conservation of `End.forward`.** For the transfer re-issued by `forward`,
`n = min wb.remain rb.remain > 0`, and every evaluation of its element move reads `n` values
`vs` from `wb` and writes that same `vs` into `rb`. -/
theorem endForward_conservation {lim : Limits} {q : Quirks} {src dst : EndId}
    {st st' : CStore E} {w r : EndId} {n : Nat} {wb rb : BufferDesc E} {s s' : τ} {u : Unit}
    (hf : forward src dst st = .ok (st', .transfer w r n wb rb))
    (h : Prog.Eval H (performCopy (σ := σ) lim q (.transfer w r n wb rb)) s u s') :
    n = min wb.remain rb.remain ∧ 0 < n ∧
      ∃ vs s₁, Prog.Eval H (readBuffer lim q wb n) s vs s₁ ∧ vs.length = n ∧
        Prog.Eval H (writeBuffer lim q rb vs) s₁ () s' :=
  let ⟨h1, h2⟩ := forward_transfer hf
  ⟨h1, h2, performCopy_conservation h⟩

end Eval

/-! ## Program-logic lemmas -/

section Inv

variable {I : CStore E → Prop}

theorem pumpHost_inv (o : Option EndId) : P.Inv I (pumpHost o : P E σ Unit) := by
  cases o with
  | none => exact P.Inv.pure _
  | some _ => exact P.Inv.callUnit _

theorem endCopyPumped_inv (hl : P.Inv.LoadPres I) (hs : P.Inv.StorePres I) (lim : Limits)
    (q : Quirks) {e : EndId} {buf : BufferDesc E} {isRead : Bool}
    (hc : ∀ s, I s → I (copySt e buf isRead s)) :
    P.Inv I (endCopyPumped lim q e buf isRead : P E σ Unit) :=
  P.Inv.bind (P.Inv.gets _) fun _ =>
    P.Inv.bind (endCopy_inv hl hs lim q hc) fun _ => pumpHost_inv _

theorem endDropPumped_inv {e : EndId} (hd : ∀ s, I s → I (dropEnd e s)) :
    P.Inv I (endDropPumped e : P E σ Unit) :=
  P.Inv.bind (P.Inv.gets _) fun _ => P.Inv.bind (endDrop_inv hd) fun _ => pumpHost_inv _

theorem endForwardPumped_inv (hl : P.Inv.LoadPres I) (hs : P.Inv.StorePres I) (lim : Limits)
    (q : Quirks) {src dst : EndId} (hf : ∀ s, I s → I (forwardSt src dst s)) :
    P.Inv I (endForwardPumped lim q src dst : P E σ Unit) :=
  P.Inv.bind (P.Inv.gets _) fun _ =>
    P.Inv.bind (endForward_inv hl hs lim q hf) fun _ =>
      P.Inv.bind (pumpHost_inv _) fun _ => pumpHost_inv _

/-- The stream-end updates of `endCopy`, `endForward`, `endCancel` and `endDrop` preserve
`EndWF`. -/
theorem endOps_EndWF {s : CStore E} (hw : EndWF s) :
    (∀ e buf isRead, EndWF (copySt e buf isRead s)) ∧
    (∀ src dst, EndWF (forwardSt src dst s)) ∧
    (∀ e b, EndWF (cancel e b s)) ∧ (∀ e, EndWF (dropEnd e s)) :=
  ⟨fun e buf isRead => copySt_EndWF hw e buf isRead, fun src dst => forwardSt_EndWF hw src dst,
    fun e b => cancel_EndWF hw e b, fun e => dropEnd_EndWF hw e⟩

end Inv

end Silmaril.Wasm.Component.Runtime
