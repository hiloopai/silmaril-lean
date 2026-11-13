module

public import Silmaril.Wasi.Theory.Defs
public import Silmaril.Wasi.Versions.WitImport.Tables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.Resolve.Thms

@[expose] public section

/-!
# WASI 0.2: `wasi:io` (streams and pollables) as a theory

The interfaces `wasi:io/streams`, `wasi:io/poll` and `wasi:io/error` of WASI 0.2, checked against
the vendored WIT `specs/wasi/v0.2.9/io/{streams,poll,error}.wit` (WebAssembly/WASI tag `v0.2.9`,
commit `34c02589`; see `provenance/wasi-0.2.9-wit.json`). Interface names are written without
the `@0.2.9` version, as in `Silmaril.Wasi.Theory` (#856), whose `blocking-write-and-flush` and
`[resource-drop]output-stream` are reused here (`streamWrite`, `streamDrop`).

## Functions

`IoOp` classifies the functions: the ten `output-stream` methods (`check-write`, `write`,
`blocking-write-and-flush`, `flush`, `blocking-flush`, `subscribe`, `write-zeroes`,
`blocking-write-zeroes-and-flush`, `splice`, `blocking-splice`), the five `input-stream` methods
(`read`, `blocking-read`, `skip`, `blocking-skip`, `subscribe`), and `pollable.ready`,
`pollable.block`, `poll` and `[resource-drop]pollable` (which forgets the pollable's stream, so
that a reused handle index does not inherit it). Other resource drops and
`error.to-debug-string` are `other`.
Encodings are those of `Silmaril.Wasi.Theory`: a handle is its `u32` index, `list<u8>` a record of
`u8`, `result` the variant cases `0`/`1`, `stream-error` the cases
`last-operation-failed(own<error>)` (`0`) and `closed` (`1`).

## The theory `ioTh r` (a protocol on the host's answers)

The state `IoSt` records per handle whether the stream is closed, the permit of its last
`check-write`, whether a pollable of the output stream has been seen ready since, and the parent
output stream of each pollable. An answer is admissible (`ansOk`) when:

* it has the WIT result type;
* **closed is sticky**: after an error on a stream, every operation on it returns
  `error(closed)` ("After this, the stream will be closed. All future operations return
  `stream-error::closed`.");
* `write`/`write-zeroes` within the permit of the last `check-write` answer normally, and beyond
  it **trap** ("Calling `write` with more bytes than this function has permitted will trap");
  `blocking-write-and-flush` may trap only beyond 4096 bytes;
* `read`/`skip`/`splice` return at most `len` bytes ("it may return fewer than requested, but not
  more");
* `poll` answers a non-empty list of indices into its argument, and traps on an empty argument.

Two readings of `check-write` (`Reading`):

* **strict**: once a pollable of the stream has been seen ready (`ready` answered `true`, `block`
  returned, or `poll` listed it), or `blocking-flush` succeeded, the next `check-write` does not
  answer `ok(0)` ("When this pollable is ready, `check-write` will return `ok(n)` with n>0, or an
  error"); a `blocking-read` of `len > 0` returns at least one byte or an error ("after blocking
  until at least one byte can be read");
* **loose**: these two liveness clauses are dropped. `check-write` may report a conservative
  budget, `ok(0)` included, at any time.

## The guest's obligation

`permitG`: a guarantee on the component's events: every `write` (`write-zeroes`) request carries
at most the permit of the last `check-write` answer on its stream, and consumes it.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Function names -/

/-- `wasi:io/streams`. -/
def ioStreams : String := "wasi:io/streams"
/-- `wasi:io/poll`. -/
def ioPollI : String := "wasi:io/poll"

/-- `[method]output-stream.check-write`. -/
def osCheckWrite : FnName := ⟨ioStreams, "[method]output-stream.check-write"⟩
/-- `[method]output-stream.write`. -/
def osWrite : FnName := ⟨ioStreams, "[method]output-stream.write"⟩
/-- `[method]output-stream.blocking-write-and-flush` (#856's `streamWrite`). -/
abbrev osBwf : FnName := streamWrite
/-- `[method]output-stream.flush`. -/
def osFlush : FnName := ⟨ioStreams, "[method]output-stream.flush"⟩
/-- `[method]output-stream.blocking-flush`. -/
def osBflush : FnName := ⟨ioStreams, "[method]output-stream.blocking-flush"⟩
/-- `[method]output-stream.subscribe`. -/
def osSubscribe : FnName := ⟨ioStreams, "[method]output-stream.subscribe"⟩
/-- `[method]output-stream.write-zeroes`. -/
def osWriteZeroes : FnName := ⟨ioStreams, "[method]output-stream.write-zeroes"⟩
/-- `[method]output-stream.blocking-write-zeroes-and-flush`. -/
def osBwzf : FnName := ⟨ioStreams, "[method]output-stream.blocking-write-zeroes-and-flush"⟩
/-- `[method]output-stream.splice`. -/
def osSplice : FnName := ⟨ioStreams, "[method]output-stream.splice"⟩
/-- `[method]output-stream.blocking-splice`. -/
def osBsplice : FnName := ⟨ioStreams, "[method]output-stream.blocking-splice"⟩
/-- `[resource-drop]output-stream` (#856's `streamDrop`). -/
abbrev osDrop : FnName := streamDrop

/-- `[method]input-stream.read`. -/
def isRead : FnName := ⟨ioStreams, "[method]input-stream.read"⟩
/-- `[method]input-stream.blocking-read`. -/
def isBread : FnName := ⟨ioStreams, "[method]input-stream.blocking-read"⟩
/-- `[method]input-stream.skip`. -/
def isSkip : FnName := ⟨ioStreams, "[method]input-stream.skip"⟩
/-- `[method]input-stream.blocking-skip`. -/
def isBskip : FnName := ⟨ioStreams, "[method]input-stream.blocking-skip"⟩
/-- `[method]input-stream.subscribe`. -/
def isSubscribe : FnName := ⟨ioStreams, "[method]input-stream.subscribe"⟩
/-- `[resource-drop]input-stream`. -/
def isDrop : FnName := ⟨ioStreams, "[resource-drop]input-stream"⟩

/-- `[method]pollable.ready`. -/
def pollReady : FnName := ⟨ioPollI, "[method]pollable.ready"⟩
/-- `[method]pollable.block`. -/
def pollBlock : FnName := ⟨ioPollI, "[method]pollable.block"⟩
/-- `poll`. -/
def pollPoll : FnName := ⟨ioPollI, "poll"⟩
/-- `[resource-drop]pollable`. -/
def pollDrop : FnName := ⟨ioPollI, "[resource-drop]pollable"⟩

/-- `wasi:io/error.[method]error.to-debug-string`. -/
def errDebug : FnName := ⟨"wasi:io/error", "[method]error.to-debug-string"⟩
/-- `wasi:io/error.[resource-drop]error`. -/
def errDrop : FnName := ⟨"wasi:io/error", "[resource-drop]error"⟩

/-- The imports of the world `wasi:io/imports` (the functions of `wasi:io` 0.2 and the resource drops), **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `ioImports_eq`. -/
def ioImports : Set FnName := {f | f ∈ WitImport.names WitImport.io2T ++ WitImport.io2D}

/-- **The imported functions of `ioImports` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem ioImports_eq : ioImports = {osCheckWrite, osWrite, osBwf, osFlush, osBflush, osSubscribe, osWriteZeroes, osBwzf, osSplice, osBsplice, osDrop, isRead, isBread, isSkip, isBskip, isSubscribe, isDrop, pollReady, pollBlock, pollPoll, pollDrop, errDebug, errDrop} := by
  ext f
  show f ∈ WitImport.names WitImport.io2T ++ WitImport.io2D ↔ _
  rw [(show (WitImport.names WitImport.io2T ++ WitImport.io2D).Perm [osCheckWrite, osWrite, osBwf, osFlush, osBflush, osSubscribe, osWriteZeroes, osBwzf, osSplice, osBsplice, osDrop, isRead, isBread, isSkip, isBskip, isSubscribe, isDrop, pollReady, pollBlock, pollPoll, pollDrop, errDebug, errDrop] by decide +kernel).mem_iff]
  simp

/-! ## Classification -/

/-- The `wasi:io` functions the theory constrains. -/
inductive IoOp where
  | checkWrite | write | bwf | flush | bflush | oSubscribe | writeZeroes | bwzf | splice
  | bsplice | read | bread | skip | bskip | iSubscribe | ready | block | poll | pDrop | other
  deriving DecidableEq, Repr

/-- The class of a function. -/
def ioOp (f : FnName) : IoOp :=
  if f = osCheckWrite then .checkWrite else if f = osWrite then .write
  else if f = osBwf then .bwf else if f = osFlush then .flush
  else if f = osBflush then .bflush else if f = osSubscribe then .oSubscribe
  else if f = osWriteZeroes then .writeZeroes else if f = osBwzf then .bwzf
  else if f = osSplice then .splice else if f = osBsplice then .bsplice
  else if f = isRead then .read else if f = isBread then .bread
  else if f = isSkip then .skip else if f = isBskip then .bskip
  else if f = isSubscribe then .iSubscribe else if f = pollReady then .ready
  else if f = pollBlock then .block else if f = pollPoll then .poll
  else if f = pollDrop then .pDrop else .other

/-- Stream operations: methods of a stream other than `subscribe` (closed is sticky for them). -/
def IoOp.isStream : IoOp → Bool
  | .checkWrite | .write | .bwf | .flush | .bflush | .writeZeroes | .bwzf | .splice | .bsplice
  | .read | .bread | .skip | .bskip => true
  | _ => false

/-! ## Arguments and answers -/

/-- The `self` handle of a method call. -/
def selfOf : List Val → BitVec 32
  | .u32 h :: _ => h
  | _ => 0

/-- The bytes of the second argument (`contents: list<u8>`). -/
def contentsOf : List Val → List (BitVec 8)
  | _ :: c :: _ => bytesOf c
  | _ => []

/-- The `u64` second argument (`len`). -/
def lenOf : List Val → Nat
  | _ :: .u64 n :: _ => n.toNat
  | _ => 0

/-- The `u64` third argument (the `len` of `splice`). -/
def spliceLenOf : List Val → Nat
  | _ :: _ :: .u64 n :: _ => n.toNat
  | _ => 0

/-- The amount a write-like call consumes from the permit. -/
def writeLen (o : IoOp) (a : List Val) : Nat := if o = .write ∨ o = .bwf then (contentsOf a).length else lenOf a

/-- `error(closed)`. -/
def errClosed : Val := errV (some (.variant 1 none))

/-- A `stream-error`, as written by hand (`streamErrOk_eq_hand`: equal to `streamErrOk`). -/
def streamErrOkH : Val → Bool
  | .variant 0 (some (.u32 _)) => true
  | .variant 1 none => true
  | _ => false

/-- A `stream-error`: **the resolved WIT type `wasi:io/streams@0.2.12.stream-error`** of the
imported `specs/wasi/0.2.12/io` package (`variant { last-operation-failed(error), closed }`). -/
def streamErrOk : Val → Bool :=
  WitImport.tyOkR WitImport.io2P.2 WitImport.fuel ⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩
    (.ref ⟨.local, "stream-error"⟩)

/-- **The resolved `stream-error` is the hand-written check** (the definition is read in the
kernel from the imported type environment). -/
theorem streamErrOk_eq_hand : streamErrOk = streamErrOkH := by
  funext v
  have h : WitImport.findTy WitImport.io2P.2 ⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩
      ⟨.local, "stream-error"⟩ =
      some (⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩,
        .variant [⟨"last-operation-failed", some (.own ⟨.local, "error"⟩), none⟩,
          ⟨"closed", none, none⟩]) := by
    decide +kernel
  show WitImport.tyOkR _ (30 + 2) _ _ v = _
  rw [WitImport.tyOkR_ref h]
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | w⟩
  all_goals try rfl
  · cases w <;> rfl

/-- An `error(_)` answer. -/
def isErrAns : Option (List Val) → Bool
  | some [.variant 1 _] => true
  | _ => false

/-- The answer `error(closed)`. -/
def isClosedAns : Option (List Val) → Bool
  | some [.variant 1 (some (.variant 1 none))] => true
  | _ => false

/-- The answer `ok`. -/
def isOkUnit : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | _ => false

/-- The answer `ok(0)` of `check-write`. -/
def isOkZero : Option (List Val) → Bool
  | some [.variant 0 (some (.u64 n))] => n == 0
  | _ => false

/-- The number in an `ok(n)` answer (`0` otherwise). -/
def okNat : Option (List Val) → Nat
  | some [.variant 0 (some (.u64 n))] => n.toNat
  | _ => 0

/-- The resolved WIT result check of the `wasi:io` function `f`: its interface and signature
are looked up in the resolved imported package `WitImport.io2P` (a function missing from it
fails). -/
def ioResR (f : FnName) (r : Option (List Val)) : Bool :=
  match WitImport.io2P.1.lookup f with
  | some (i, s) => WitImport.resOkR WitImport.io2P.2 i s r
  | none => false

/-- `result<_, stream-error>`, as written by hand (`unitAns_eq_hand`). -/
def unitAnsH : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | some [.variant 1 (some e)] => streamErrOk e
  | _ => false

/-- `result<_, stream-error>`: **the resolved WIT result of `output-stream.flush`** in `io2P`.
`unitAns_eq_hand`: this is `unitAnsH`. -/
def unitAns : Option (List Val) → Bool := ioResR osFlush

/-- `stream-error` in the resolved `wasi:io` package. -/
theorem io2P_findTy_streamErr :
    WitImport.findTy WitImport.io2P.2 ⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩
      ⟨.local, "stream-error"⟩ =
      some (⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩,
        .variant [⟨"last-operation-failed", some (.own ⟨.local, "error"⟩), none⟩,
          ⟨"closed", none, none⟩]) := by
  decide +kernel

/-- `output-stream.flush` in the resolved package. -/
theorem io2P_lookup_flush :
    WitImport.io2P.1.lookup osFlush =
      some (⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩,
        ⟨false, [("self", .borrow ⟨.local, "output-stream"⟩)],
          some (.result none (some (.ref ⟨.local, "stream-error"⟩)))⟩) := by
  decide +kernel

/-- `stream-error` at any fuel above one is the hand-written check. -/
theorem tyOkR_streamErr (n : Nat) (v : Val) :
    WitImport.tyOkR WitImport.io2P.2 (n + 2) ⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩
      (.ref ⟨.local, "stream-error"⟩) v = streamErrOkH v := by
  rw [WitImport.tyOkR_ref io2P_findTy_streamErr]
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | w⟩
  all_goals try rfl
  · cases w <;> rfl

/-- **The resolved `result<_, stream-error>` is the hand-written check.** -/
theorem unitAns_eq_hand : unitAns = unitAnsH := by
  funext r
  show ioResR osFlush r = _
  rw [ioResR, io2P_lookup_flush]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩
  all_goals try (simp only [WitImport.resOkR, unitAnsH]; done)
  dsimp only [WitImport.resOkR]
  rw [show WitImport.fuel = 30 + 1 + 1 from rfl, WitImport.tyOkR_result]
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | e⟩
  all_goals simp only [unitAnsH, WitImport.resV, WitImport.optOk, streamErrOk_eq_hand]
  exact tyOkR_streamErr 29 e

/-- `result<u64, stream-error>` with the number at most `bound`. -/
def natAns (bound : Nat) : Option (List Val) → Bool
  | some [.variant 0 (some (.u64 n))] => decide (n.toNat ≤ bound)
  | some [.variant 1 (some e)] => streamErrOk e
  | _ => false

/-- A `u8` value. -/
def isU8 : Val → Bool
  | .u8 _ => true
  | _ => false

/-- `result<list<u8>, stream-error>` with at most `bound` bytes, and at least one when
`nonempty`. -/
def bytesAns (bound : Nat) (nonempty : Bool) : Option (List Val) → Bool
  | some [.variant 0 (some (.record vs))] =>
    vs.all isU8 && decide (vs.length ≤ bound) && (!nonempty || !vs.isEmpty)
  | some [.variant 1 (some e)] => streamErrOk e
  | _ => false

/-- A handle answer (`own<pollable>`), as written by hand (`handleAns_eq_hand`). -/
def handleAnsH : Option (List Val) → Bool
  | some [.u32 _] => true
  | _ => false

/-- A handle answer: **the resolved WIT result of `output-stream.subscribe`** (`own<pollable>`)
in `io2P`. `handleAns_eq_hand`: this is `handleAnsH`. -/
def handleAns : Option (List Val) → Bool := ioResR osSubscribe

/-- The answer of `pollable.ready`, as written by hand (`readyAns_eq_hand`). -/
def readyAnsH : Option (List Val) → Bool
  | some [.bool _] => true
  | _ => false

/-- The answer of `pollable.ready`: **its resolved WIT result** (`bool`) in `io2P`. -/
def readyAns : Option (List Val) → Bool := ioResR pollReady

/-- The answer of `pollable.block`, as written by hand (`blockAns_eq_hand`). -/
def blockAnsH : Option (List Val) → Bool
  | some [] => true
  | _ => false

/-- The answer of `pollable.block`: **its resolved WIT result** (none) in `io2P`. -/
def blockAns : Option (List Val) → Bool := ioResR pollBlock

/-- `osSubscribe`, `isSubscribe`, `pollReady` and `pollBlock` in the resolved package. -/
theorem io2P_lookups :
    WitImport.io2P.1.lookup osSubscribe =
      some (⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩,
        ⟨false, [("self", .borrow ⟨.local, "output-stream"⟩)], some (.own ⟨.local, "pollable"⟩)⟩) ∧
    WitImport.io2P.1.lookup isSubscribe =
      some (⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩,
        ⟨false, [("self", .borrow ⟨.local, "input-stream"⟩)], some (.own ⟨.local, "pollable"⟩)⟩) ∧
    WitImport.io2P.1.lookup pollReady =
      some (⟨⟨"wasi", "io", some "0.2.12"⟩, "poll"⟩,
        ⟨false, [("self", .borrow ⟨.local, "pollable"⟩)], some (.prim .bool)⟩) ∧
    WitImport.io2P.1.lookup pollBlock =
      some (⟨⟨"wasi", "io", some "0.2.12"⟩, "poll"⟩,
        ⟨false, [("self", .borrow ⟨.local, "pollable"⟩)], none⟩) := by
  decide +kernel

/-- **The resolved `own<pollable>` is the hand-written handle check.** -/
theorem handleAns_eq_hand : handleAns = handleAnsH := by
  funext r
  show ioResR osSubscribe r = _
  rw [ioResR, io2P_lookups.1]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  all_goals cases v <;> rfl

/-- `input-stream.subscribe` has the same resolved result check. -/
theorem ioResR_isSubscribe : ioResR isSubscribe = handleAns := by
  funext r
  show ioResR isSubscribe r = ioResR osSubscribe r
  rw [ioResR, ioResR, io2P_lookups.1, io2P_lookups.2.1]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> rfl

/-- **The resolved `bool` is the hand-written `ready` check.** -/
theorem readyAns_eq_hand : readyAns = readyAnsH := by
  funext r
  show ioResR pollReady r = _
  rw [ioResR, io2P_lookups.2.2.1]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  all_goals cases v <;> rfl

/-- **The resolved empty result is the hand-written `block` check.** -/
theorem blockAns_eq_hand : blockAns = blockAnsH := by
  funext r
  show ioResR pollBlock r = _
  rw [ioResR, io2P_lookups.2.2.2]
  rcases r with _ | ⟨_ | ⟨v, r⟩⟩ <;> rfl

/-- An index into a list of `n` pollables. -/
def idxOk (n : Nat) : Val → Bool
  | .u32 i => decide (i.toNat < n)
  | _ => false

/-- The answer of `poll(in)`: a non-empty list of indices into `in`; a trap on an empty `in`. -/
def pollAns : List Val → Option (List Val) → Bool
  | [.record ps], res =>
    if ps.isEmpty then res.isNone
    else match res with
      | some [.record is] => !is.isEmpty && is.all (idxOk ps.length)
      | _ => false
  | _, _ => true

/-! ## The theory -/

/-- The two readings of `check-write` and `blocking-read`. -/
inductive Reading where
  | strict | loose
  deriving DecidableEq, Repr

/-- The point update of a handle map. -/
def upd {α : Type} (m : BitVec 32 → α) (h : BitVec 32) (v : α) : BitVec 32 → α :=
  fun x => if x = h then v else m x

/-- The state of the `wasi:io` theory. -/
structure IoSt where
  /-- Streams that reported an error (then closed). -/
  closed : BitVec 32 → Bool
  /-- The remaining permit of the last `check-write` of an output stream. -/
  permit : BitVec 32 → Nat
  /-- A pollable of the output stream was seen ready since its last `check-write`. -/
  ready : BitVec 32 → Bool
  /-- The output stream of a pollable. -/
  parent : BitVec 32 → Option (BitVec 32)

/-- The initial state. -/
def ioInit : IoSt := ⟨fun _ => false, fun _ => 0, fun _ => false, fun _ => none⟩

/-- Closed is sticky: on a closed stream only `error(closed)`. -/
def stickyOk (s : IoSt) (h : BitVec 32) (res : Option (List Val)) : Bool :=
  !s.closed h || isClosedAns res

/-- **The admissible answers** of the `wasi:io` functions. -/
def ansOk (r : Reading) (s : IoSt) (o : IoOp) (a : List Val) (res : Option (List Val)) : Bool :=
  let h := selfOf a
  match o with
  | .checkWrite =>
    stickyOk s h res && natAns (2 ^ 64) res && (r == .loose || !s.ready h || !isOkZero res)
  | .write | .writeZeroes =>
    if writeLen o a ≤ s.permit h then stickyOk s h res && unitAns res else res.isNone
  | .bwf | .bwzf => stickyOk s h res && (unitAns res || (decide (4096 < writeLen o a) && res.isNone))
  | .flush | .bflush => stickyOk s h res && unitAns res
  | .splice | .bsplice => stickyOk s h res && natAns (spliceLenOf a) res
  | .read => stickyOk s h res && bytesAns (lenOf a) false res
  | .bread => stickyOk s h res && bytesAns (lenOf a) (r == .strict && decide (0 < lenOf a)) res
  | .skip | .bskip => stickyOk s h res && natAns (lenOf a) res
  | .oSubscribe | .iSubscribe => handleAns res
  | .ready => readyAns res
  | .block => blockAns res
  | .poll => pollAns a res
  | .pDrop | .other => true

/-- Mark the output stream of the pollable `p` as ready. -/
def markReady (s : IoSt) (p : BitVec 32) : IoSt :=
  match s.parent p with
  | some h => { s with ready := upd s.ready h true }
  | none => s

/-- The pollables of a `poll` call listed by its answer. -/
def polled : List Val → Option (List Val) → List (BitVec 32)
  | [.record ps], some [.record is] =>
    is.filterMap fun | .u32 i => (match ps[i.toNat]? with | some (.u32 p) => some p | _ => none)
                     | _ => none
  | _, _ => []

/-- The handle of a handle answer. -/
def handleOf : Option (List Val) → BitVec 32
  | some [.u32 p] => p
  | _ => 0

/-- Close the stream `h` on an error answer of a stream operation. -/
def closeOn (s : IoSt) (o : IoOp) (h : BitVec 32) (res : Option (List Val)) : IoSt :=
  if o.isStream && isErrAns res then { s with closed := upd s.closed h true } else s

/-- The state after an admissible answer. -/
def ioUpd (s0 : IoSt) (o : IoOp) (a : List Val) (res : Option (List Val)) : IoSt :=
  let h := selfOf a
  let s := closeOn s0 o h res
  match o with
  | .checkWrite => { s with permit := upd s.permit h (okNat res), ready := upd s.ready h false }
  | .write | .writeZeroes =>
    { s with permit := upd s.permit h (s.permit h - writeLen o a), ready := upd s.ready h false }
  | .bwf | .bwzf | .flush | .splice => { s with ready := upd s.ready h false }
  | .bflush => if isOkUnit res then { s with ready := upd s.ready h true } else s
  | .oSubscribe => { s with parent := upd s.parent (handleOf res) (some h) }
  | .iSubscribe => { s with parent := upd s.parent (handleOf res) none }
  | .ready => (match res with | some [.bool true] => markReady s h | _ => s)
  | .block => (match res with | some [] => markReady s h | _ => s)
  | .poll => (polled a res).foldl markReady s
  | .pDrop => { s with parent := upd s.parent h none }
  | _ => s

/-- The state after an event (non-answers leave it unchanged). -/
def ioNext (s : IoSt) : WEv → IoSt
  | .imp f a res => ioUpd s (ioOp f) a res
  | _ => s

/-- One step of the theory. -/
def ioStep (r : Reading) (s : IoSt) : WEv → Option IoSt
  | .imp f a res => if ansOk r s (ioOp f) a res then some (ioUpd s (ioOp f) a res) else none
  | _ => some s

/-- **The `wasi:io` theory** in the reading `r`. -/
def ioTh (r : Reading) : Protocol IoSt WEv := ⟨ioInit, ioStep r⟩

/-- The strict reading. -/
abbrev ioStrict : Protocol IoSt WEv := ioTh .strict

/-- The loose reading. -/
abbrev ioLoose : Protocol IoSt WEv := ioTh .loose

/-! ## The guest's permit discipline -/

/-- One step of the permit guarantee: `check-write` answers set the permit, write requests
must fit in it and consume it. -/
def permitStep (m : BitVec 32 → Nat) : WEv → Option (BitVec 32 → Nat)
  | .imp f a res =>
    if ioOp f = .checkWrite then some (upd m (selfOf a) (okNat res)) else some m
  | .req f a =>
    if ioOp f = .write ∨ ioOp f = .writeZeroes then
      if writeLen (ioOp f) a ≤ m (selfOf a) then
        some (upd m (selfOf a) (m (selfOf a) - writeLen (ioOp f) a))
      else none
    else some m
  | _ => some m

/-- **The guest writes within its permits.** -/
def permitG : Protocol (BitVec 32 → Nat) WEv := ⟨fun _ => 0, permitStep⟩

end Silmaril.Wasi.Versions.P2
