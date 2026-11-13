module

public import Silmaril.Wasm.JcoTool.StreamSem.Defs
public import Silmaril.Wasm.Component.Streams.Kernel.Defs

/-!
# Callback-ABI core modules generated from byte kernels, with a semantics

`Silmaril.Wasm.JcoTool.StreamSem` proves that every machine simulating the `Proc` transformer
`tStep T N` is correct in every pipeline (`impl_correct`), and leaves open whether the core
module's export of a `wasm-jco` stream component is such a machine. This module gives the
pieces to close that gap for the core modules generated from the byte kernels `KM` of
`Silmaril.Wasm.Component.Streams.Kernel`:

* **A fragment of WebAssembly** (`E`, `S`): `i32` expressions in folded form (`i32.const`,
  `local.get`, `global.get`, `i32.add`, `i32.sub`, `i32.eq`, `i32.ne`, `i32.lt_u`,
  `i32.ge_u`, `i32.div_u`, `i32.rem_u`, `i32.shl`, `i32.eqz`, `i32.load8_u`) and structured
  statements (`local.set`, `global.set`, `i32.store8`, `memory.copy`, `block`, `loop`, `br`,
  `br_if`, `if`, `return`, `unreachable`, and calls of the imported canonical built-ins).
  Its semantics `exec` is a big-step interpreter: values are `Nat`s below `2 ^ 32` with
  wrap-around arithmetic, memory is a map from addresses to bytes, `br k` leaves `k + 1`
  enclosing labels (`block`, `if`; a `loop` is re-entered by a branch to it); loops take fuel.
* **The canonical built-ins** (`callBI`), over the store of `Silmaril.Wasm.Component.Async`: the
  `[async-lower]` `stream.read` copies the items it receives into linear memory (one byte per
  `u8`) or records the pending read's buffer; `stream.write` lifts the bytes of its buffer as
  `u8` values; `stream.new`, the drops, `waitable-set.new`, `waitable.join`, `task.return`.
* **The callback runtime** (`rstep`): `canon lift … async (callback …)` after
  `definitions.py`: the callback's code `EXIT` ends the task, `YIELD` calls the callback
  again with no event, `WAIT | s << 4` waits on the waitable set `s` (`Async.step (.wait s)`)
  and calls the callback with the event's code, index and payload, after copying the items of
  a completed read into the pending read's buffer.
* **The generator** `gen k N`: the core module (`Prog`: the `[async-lift]` function and its
  callback) of a component exporting `async func(in: stream<u8>) -> stream<u8>` that runs the
  kernel `k`, reading up to `N` bytes at a time. Unlike `KM.coreWat` (the streams track's
  generator, tested only), it is written as a **state machine over the `TPc` counter of
  `Proc.tStep`**: the global `pc` holds the transformer's control state, and each callback
  invocation performs at most one built-in and returns `YIELD` (or `WAIT` after a blocked
  copy, `EXIT` at the end). The kernel's statements are compiled one to one (`cS`), with
  bounds checks that trap rather than overflow the output and line buffers.
* **The printer** `Prog.wat`: the module as WebAssembly text, with wit-component's core names.

The theorems (`Silmaril.Wasm.JcoTool.KCore.Thms`): the generated module, run by the callback
runtime, **is an implementation** of `tStep (trV k) N` in the sense of `StreamSem.Impl`
(`kimpl`), and it does everything `tStep` does (`kimpl_complete`, under the bounds of its
buffers). **Not proved**: that the printed text means, under the official WebAssembly
semantics, what `exec` says (the fragment is small and the printer is one line per
construct; `tools/wasm-jco/tests` runs the printed modules under wasmtime).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCore

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event EventCode blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

/-- `2 ^ 32`. -/
def M32 : Nat := 2 ^ 32

/-! ## The fragment -/

/-- `i32` binary operators. -/
inductive Bin where
  | add | sub | eq | ne | ltu | geu | divu | remu | shl
  deriving Repr, DecidableEq

/-- `i32` expressions, in folded form. -/
inductive E where
  /-- `i32.const n` (taken modulo `2 ^ 32`). -/
  | c (n : Nat)
  | l (i : Nat)
  | g (i : Nat)
  | bin (o : Bin) (a b : E)
  | eqz (a : E)
  /-- `i32.load8_u`. -/
  | ld8 (a : E)
  deriving Repr

/-- The canonical built-ins the generated modules import. -/
inductive BI where
  | streamNew | streamRead | streamWrite | dropR | dropW | wsNew | join | taskReturn
  deriving Repr, DecidableEq

/-- Statements. -/
inductive S where
  | nop
  | unreachable
  | lset (i : Nat) (e : E)
  | gset (i : Nat) (e : E)
  /-- `i32.store8`. -/
  | st8 (a v : E)
  /-- `memory.copy dst src len` (non-overlapping uses only). -/
  | mcopy (d s n : E)
  | seq (a b : S)
  | ite (c : E) (t f : S)
  | block (b : S)
  | loop (b : S)
  | br (k : Nat)
  | brIf (k : Nat) (c : E)
  | ret (e : E)
  /-- A call of a built-in with its arguments; its results go to the locals `dst`. -/
  | call (b : BI) (args : List E) (dst : List Nat)
  deriving Repr

/-- The state of an invocation: globals, memory, locals, the async store, the pending read
(handle and buffer), and the current task. -/
structure St where
  g : Nat → Nat
  m : Nat → Nat
  l : Nat → Nat
  st : Store
  rp : Option (Nat × Nat)
  task : Nat

/-- How a statement ends: normally, by a branch out of `k` more blocks, or by `return`. -/
inductive Out where
  | norm
  | br (k : Nat)
  | ret (v : Nat)
  deriving Repr, DecidableEq

/-- Point update. -/
def upd (f : Nat → Nat) (k v : Nat) : Nat → Nat := fun j => if j = k then v else f j

/-- The bytes `m a, …, m (a + n - 1)`. -/
def slice (m : Nat → Nat) (a n : Nat) : List Nat := (List.range n).map fun i => m (a + i)

/-- Write bytes at `a`. -/
def writeBytes (m : Nat → Nat) (a : Nat) (bs : List Nat) : Nat → Nat :=
  fun x => if a ≤ x ∧ x < a + bs.length then bs.getD (x - a) 0 else m x

/-- `memory.copy`. -/
def mcopy (m : Nat → Nat) (d s n : Nat) : Nat → Nat :=
  fun x => if d ≤ x ∧ x < d + n then m (s + (x - d)) else m x

def Bin.eval : Bin → Nat → Nat → Nat
  | .add, a, b => (a + b) % M32
  | .sub, a, b => (a + (M32 - b % M32)) % M32
  | .eq, a, b => if a = b then 1 else 0
  | .ne, a, b => if a = b then 0 else 1
  | .ltu, a, b => if a < b then 1 else 0
  | .geu, a, b => if b ≤ a then 1 else 0
  | .divu, a, b => a / b
  | .remu, a, b => a % b
  | .shl, a, b => (a * 2 ^ (b % 32)) % M32

def E.eval (s : St) : E → Nat
  | .c n => n % M32
  | .l i => s.l i
  | .g i => s.g i
  | .bin o a b => o.eval (a.eval s) (b.eval s)
  | .eqz a => if a.eval s = 0 then 1 else 0
  | .ld8 a => s.m (a.eval s)

/-- The byte of a `u8` value (the canonical ABI's store at type `u8`). -/
def byteOf : Val → Nat
  | .u8 x => x.toNat
  | _ => 0

/-- The `u8` value of a byte (the canonical ABI's load at type `u8`). -/
def u8v (b : Nat) : Val := .u8 (BitVec.ofNat 8 b)

/-- The `Val` of a handle given to `task.return`. -/
def hv (h : Nat) : Val := .u32 (BitVec.ofNat 32 h)

/-- **The canonical built-ins**, on evaluated arguments. -/
def callBI (b : BI) (as : List Nat) (dst : List Nat) (s : St) : Option (Out × St) :=
  match b, as, dst with
  | .streamNew, [], [d₁, d₂] =>
    match Silmaril.Wasm.Component.Async.step s.st .streamNew with
    | some (st', .ends r w) => some (.norm, { s with st := st', l := upd (upd s.l d₁ r) d₂ w })
    | _ => none
  | .streamRead, [h, p, n], [d] =>
    match Silmaril.Wasm.Component.Async.step s.st (.streamRead h n) with
    | some (st', .read code xs) =>
      if code < M32 then
        some (.norm, { s with st := st', m := writeBytes s.m p (xs.map byteOf), l := upd s.l d code })
      else none
    | some (st', .nat r) =>
      if r = blocked then some (.norm, { s with st := st', rp := some (h, p), l := upd s.l d r })
      else none
    | _ => none
  | .streamWrite, [h, p, n], [d] =>
    match Silmaril.Wasm.Component.Async.step s.st (.streamWrite h ((slice s.m p n).map u8v)) with
    | some (st', .nat r) => if r < M32 then some (.norm, { s with st := st', l := upd s.l d r }) else none
    | _ => none
  | .dropR, [h], [] =>
    (Silmaril.Wasm.Component.Async.step s.st (.streamDropR h)).map fun p => (.norm, { s with st := p.1 })
  | .dropW, [h], [] =>
    (Silmaril.Wasm.Component.Async.step s.st (.streamDropW h)).map fun p => (.norm, { s with st := p.1 })
  | .wsNew, [], [d] =>
    match Silmaril.Wasm.Component.Async.step s.st .wsNew with
    | some (st', .nat n) => some (.norm, { s with st := st', l := upd s.l d n })
    | _ => none
  | .join, [h, w], [] =>
    (Silmaril.Wasm.Component.Async.step s.st (.join h w)).map fun p => (.norm, { s with st := p.1 })
  | .taskReturn, [v], [] =>
    (Silmaril.Wasm.Component.Async.step s.st (.taskReturn s.task [hv v])).map fun p =>
      (.norm, { s with st := p.1 })
  | _, _, _ => none

/-- The end of a label (`block`, `if`): a branch to it ends it normally, a branch further out
leaves one label fewer. -/
def lab : Option (Out × St) → Option (Out × St)
  | some (.br 0, s') => some (.norm, s')
  | some (.br (k + 1), s') => some (.br k, s')
  | r => r

/-- A loop: run the body until it does not branch back to the loop (at most `n` times). -/
def loopN (body : St → Option (Out × St)) : Nat → St → Option (Out × St)
  | 0, _ => none
  | n + 1, s =>
    match body s with
    | some (.br 0, s') => loopN body n s'
    | some (.br (k + 1), s') => some (.br k, s')
    | r => r

/-- **The semantics of statements** (`f`: the fuel of every loop). -/
def exec : S → Nat → St → Option (Out × St)
  | .nop, _, s => some (.norm, s)
  | .unreachable, _, _ => none
  | .lset i e, _, s => some (.norm, { s with l := upd s.l i (e.eval s) })
  | .gset i e, _, s => some (.norm, { s with g := upd s.g i (e.eval s) })
  | .st8 a v, _, s => some (.norm, { s with m := upd s.m (a.eval s) (v.eval s % 256) })
  | .mcopy d src n, _, s => some (.norm, { s with m := mcopy s.m (d.eval s) (src.eval s) (n.eval s) })
  | .seq a b, f, s =>
    match exec a f s with
    | some (.norm, s') => exec b f s'
    | r => r
  | .ite c t e, f, s => lab (if c.eval s ≠ 0 then exec t f s else exec e f s)
  | .block b, f, s => lab (exec b f s)
  | .loop b, f, s => loopN (exec b f) f s
  | .br k, _, s => some (.br k, s)
  | .brIf k c, _, s => if c.eval s ≠ 0 then some (.br k, s) else some (.norm, s)
  | .ret e, _, s => some (.ret (e.eval s), s)
  | .call b args dst, _, s => callBI b (args.map (·.eval s)) dst s

/-- A sequence of statements. -/
def seqs : List S → S
  | [] => .nop
  | [a] => a
  | a :: as => .seq a (seqs as)

/-! ## The layout of the generated modules -/

/-- Globals. -/
def PC : Nat := 0
def GST : Nat := 1
def BLEN : Nat := 2
def OLEN : Nat := 3
def OOFF : Nat := 4
def NXT : Nat := 5
def INSR : Nat := 6
def OUTSW : Nat := 7
def WS : Nat := 8

/-- Locals: the callback's parameters `0..2`, the loop counter, the byte, a result, a count. -/
def LI : Nat := 3
def LB : Nat := 4
def LR : Nat := 5
def LN : Nat := 6

/-- Memory: the input buffer, the output buffer and the kernel's buffer, each of `CAP` bytes. -/
def IN : Nat := 0x100
def OUT : Nat := 0x1000
def KBUF : Nat := 0x10000
def CAP : Nat := 0x8000

/-- The values of `pc`: the constructors of `Proc.TPc`. -/
def pRD : Nat := 0
def pWTR : Nat := 1
def pEOI : Nat := 2
def pWR : Nat := 3
def pWTW : Nat := 4
def pCL : Nat := 5
def pFIN : Nat := 6
def pFAULT : Nat := 7

/-! ## The kernel, compiled -/

/-- A kernel expression: the byte is local `LB`, the state global `GST`, the buffer's length
global `BLEN`. -/
def cE : KExp → E
  | .x => .l LB
  | .st => .g GST
  | .blen => .g BLEN
  | .lit n => .c n
  | .add a b => .bin .add (cE a) (cE b)
  | .sub a b => .bin .sub (cE a) (cE b)
  | .eq a b => .bin .eq (cE a) (cE b)
  | .ltu a b => .bin .ltu (cE a) (cE b)
  | .eqz a => .eqz (cE a)

/-- Output the low byte of `v` (trap when the output buffer is full). -/
def emitS (v : E) : S :=
  seqs [.ite (.bin .geu (.g OLEN) (.c CAP)) .unreachable .nop,
    .st8 (.bin .add (.c OUT) (.g OLEN)) v,
    .gset OLEN (.bin .add (.g OLEN) (.c 1))]

/-- Append the low byte of `v` to the kernel's buffer (trap when it is full). -/
def pushS (v : E) : S :=
  seqs [.ite (.bin .geu (.g BLEN) (.c CAP)) .unreachable .nop,
    .st8 (.bin .add (.c KBUF) (.g BLEN)) v,
    .gset BLEN (.bin .add (.g BLEN) (.c 1))]

/-- Output the kernel's buffer (trap when it does not fit). -/
def emitBufS : S :=
  seqs [.ite (.bin .ltu (.c CAP) (.bin .add (.g OLEN) (.g BLEN))) .unreachable .nop,
    .mcopy (.bin .add (.c OUT) (.g OLEN)) (.c KBUF) (.g BLEN),
    .gset OLEN (.bin .add (.g OLEN) (.g BLEN))]

/-- A kernel statement. -/
def cS : KStmt → S
  | .skip => .nop
  | .seq p q => .seq (cS p) (cS q)
  | .emit e => emitS (cE e)
  | .set e => .gset GST (cE e)
  | .push e => pushS (cE e)
  | .emitBuf => emitBufS
  | .clear => .gset BLEN (.c 0)
  | .ite c p q => .ite (cE c) (cS p) (cS q)

/-- The bounds checks of the compiled statement pass on byte `b` from the kernel state `ks`
with `o` bytes in the output buffer: neither buffer grows beyond `CAP` bytes. -/
def fitsS (b : Nat) : KStmt → KSt → Nat → Bool
  | .skip, _, _ => true
  | .seq p q, ks, o => fitsS b p ks o && fitsS b q (p.exec b ks).1 (o + (p.exec b ks).2.length)
  | .emit _, _, o => decide (o < CAP)
  | .set _, _, _ => true
  | .push _, ks, _ => decide (ks.buf.length < CAP)
  | .emitBuf, ks, o => decide (o + ks.buf.length ≤ CAP)
  | .clear, _, _ => true
  | .ite c p q, ks, o => if c.eval ks b ≠ 0 then fitsS b p ks o else fitsS b q ks o

/-- The bounds checks pass while the kernel `k` is fed the bytes `bs` (as `Tr.feed` does). -/
def fitsF (k : KM) : KSt → List Nat → Nat → Bool
  | _, [], _ => true
  | ks, b :: bs, o =>
    if k.tr.done ks then true
    else fitsS b k.step ks o && fitsF k (k.step.exec b ks).1 bs (o + (k.step.exec b ks).2.length)

/-! ## The generated module -/

/-- `pc = n`. -/
def pcIs (n : Nat) : E := .bin .eq (.g PC) (.c n)

/-- The code `WAIT | ws << 4`. -/
def waitCode : E := .bin .add (.c 2) (.bin .shl (.g WS) (.c 4))

/-- Feed the `LN` bytes of the input buffer to the kernel, stopping when it is done. -/
def feedLoop (k : KM) : S :=
  .block (.loop (seqs [.brIf 1 (.bin .geu (.l LI) (.l LN)),
    .lset LB (.c 0), .brIf 1 (cE k.done),
    .lset LB (.ld8 (.bin .add (.c IN) (.l LI))), cS k.step,
    .lset LI (.bin .add (.l LI) (.c 1)), .br 0]))

/-- After a read with packed result `p`: on `COMPLETED`, feed the bytes received and write
the output; otherwise the input has ended (`TPc.onRead`). -/
def onRead (k : KM) (p : E) : S :=
  .ite (.bin .remu p (.c 16)) (.gset PC (.c pEOI))
    (seqs [.lset LN (.bin .divu p (.c 16)), .lset LI (.c 0), feedLoop k,
      .gset NXT (.c 1), .gset PC (.c pWR)])

/-- After a write with packed result `p` (`TPc.onWrite`). -/
def onWrite (p : E) : S :=
  .ite (.bin .remu p (.c 16)) (.gset PC (.c pFAULT))
    (seqs [.lset LN (.bin .divu p (.c 16)),
      .ite (.bin .geu (.l LN) (.bin .sub (.g OLEN) (.g OOFF))) (.gset OOFF (.g OLEN))
        (.gset OOFF (.bin .add (.g OOFF) (.l LN))),
      .gset PC (.c pWR)])

/-- Run the kernel's flush into the empty output buffer; close after writing it. -/
def flushOut (k : KM) : S :=
  seqs [.gset OOFF (.c 0), .gset OLEN (.c 0), .lset LB (.c 0), cS k.flush,
    .gset NXT (.c 0), .gset PC (.c pWR)]

/-- The case `pc = n` of the callback. -/
def case_ (n : Nat) (body : S) : S := .ite (pcIs n) body .nop

/-- `YIELD`. -/
def yield_ : S := .ret (.c 1)

/-- The `WTR` case: the event must be the read's completion. -/
def cbWTR (k : KM) : S :=
  seqs [.ite (.bin .eq (.l 0) (.c 2)) (.ite (.bin .eq (.l 1) (.g INSR)) .nop .unreachable) .unreachable,
    onRead k (.l 2), yield_]

/-- The `WTW` case: the event must be the write's completion. -/
def cbWTW : S :=
  seqs [.ite (.bin .eq (.l 0) (.c 3)) (.ite (.bin .eq (.l 1) (.g OUTSW)) .nop .unreachable) .unreachable,
    onWrite (.l 2), yield_]

/-- The `RD` case: stop when done, else read up to `N` bytes. -/
def cbRD (k : KM) (N : Nat) : S :=
  seqs [.lset LB (.c 0),
    .ite (cE k.done) (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) .nop,
    .call .streamRead [.g INSR, .c IN, .c N] [LR],
    .ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTR), .ret waitCode]) .nop,
    onRead k (.l LR), yield_]

/-- The `EOI` case. -/
def cbEOI (k : KM) : S := seqs [.call .dropR [.g INSR] [], flushOut k, yield_]

/-- The `WR` case: resume when the output is written, else write the rest. -/
def cbWR : S :=
  seqs [.ite (.bin .geu (.g OOFF) (.g OLEN))
      (seqs [.gset OOFF (.c 0), .gset OLEN (.c 0),
        .ite (.g NXT) (.gset PC (.c pRD)) (.gset PC (.c pCL)), yield_]) .nop,
    .call .streamWrite [.g OUTSW, .bin .add (.c OUT) (.g OOFF), .bin .sub (.g OLEN) (.g OOFF)] [LR],
    .ite (.bin .eq (.l LR) (.c blocked)) (seqs [.gset PC (.c pWTW), .ret waitCode]) .nop,
    onWrite (.l LR), yield_]

/-- The `CL` case. -/
def cbCL : S := seqs [.call .dropW [.g OUTSW] [], .gset PC (.c pFIN), .ret (.c 0)]

/-- **The callback** `[callback][async-lift]name (code, index, payload) -> code`. -/
def callback (k : KM) (N : Nat) : S :=
  seqs [case_ pWTR (cbWTR k), case_ pWTW cbWTW, case_ pRD (cbRD k N), case_ pEOI (cbEOI k),
    case_ pWR cbWR, case_ pCL cbCL, .unreachable]

/-- **The lift** `[async-lift]name (in) -> code`: the result stream, the waitable set,
`task.return` of the readable end, the joins; then `YIELD`. -/
def entry : S :=
  seqs [.call .streamNew [] [1, 2], .gset INSR (.l 0), .gset OUTSW (.l 2),
    .call .wsNew [] [3], .gset WS (.l 3),
    .call .taskReturn [.l 1] [],
    .call .join [.g INSR, .g WS] [], .call .join [.g OUTSW, .g WS] [],
    yield_]

/-- A generated module: the lift, the callback, the initial globals. -/
structure Prog where
  entry : S
  cb : S
  g0 : Nat → Nat

/-- The initial globals: `pc = RD`, the kernel's initial state. -/
def initG (k : KM) : Nat → Nat := upd (fun _ => 0) GST (k.init % M32)

/-- **The core module generated from the kernel `k`**, reading up to `N` bytes at a time. -/
def gen (k : KM) (N : Nat) : Prog := ⟨entry, callback k N, initG k⟩

/-! ## The callback runtime -/

/-- What the runtime does next with the task. -/
inductive Mode where
  /-- Call the callback with no event (after `YIELD`). -/
  | ready
  /-- Wait on the waitable set `s`, then call the callback with the event (after `WAIT`). -/
  | waiting (s : Nat)
  /-- The task has exited. -/
  | exited
  deriving Repr, DecidableEq

/-- The machine: the instance's globals and memory, the pending read, the runtime's mode. -/
structure MS where
  g : Nat → Nat
  m : Nat → Nat
  rp : Option (Nat × Nat)
  mode : Mode

/-- The fuel of loops (every loop of the generated code runs fewer than `2 ^ 32` times). -/
def FUEL : Nat := M32

/-- The locals of an invocation: the parameters, then zeros. -/
def locals (ps : List Nat) : Nat → Nat := fun i => ps.getD i 0

/-- The mode a callback code asks for (`none`: a code that traps). -/
def modeOf (code : Nat) : Option Mode :=
  if code = 0 then some .exited
  else if code = 1 then some .ready
  else if code % 16 = 2 then some (.waiting (code / 16))
  else none

/-- Run `body` with the parameters `ps`; it must `return` a callback code. -/
def invoke (body : S) (ps : List Nat) (st : Store) (ms : MS) : Option (Store × MS) :=
  match exec body FUEL ⟨ms.g, ms.m, locals ps, st, ms.rp, 0⟩ with
  | some (.ret code, s') => (modeOf code).map fun md => (s'.st, ⟨s'.g, s'.m, s'.rp, md⟩)
  | _ => none

/-- The events the runtime delivers: an `i32` payload and index, and a completed stream read
delivers as many items as its count says, at most `256`. -/
def wellFormed (e : Event) : Bool :=
  decide (e.payload < M32) && decide (e.index < M32) && decide (e.items.length ≤ 256) &&
    (e.code != .streamRead || e.payload % 16 != 0 || decide (e.payload / 16 = e.items.length))

/-- The runtime's copy of a completed read's items into the pending read's buffer. -/
def deliver (e : Event) (ms : MS) : MS :=
  match e.code, ms.rp with
  | .streamRead, some (h, p) =>
    if h = e.index then { ms with m := writeBytes ms.m p (e.items.map byteOf), rp := none } else ms
  | _, _ => ms

/-- **One step of the callback runtime**: call the callback after `YIELD`, or wait for an
event of the set and call the callback with it. -/
def rstep (P : Prog) (st : Store) (ms : MS) : Option (Store × MS) :=
  match ms.mode with
  | .exited => none
  | .ready => invoke P.cb [0, 0, 0] st ms
  | .waiting s =>
    match Silmaril.Wasm.Component.Async.step st (.wait s) with
    | some (st₁, .event e) =>
      if wellFormed e then invoke P.cb [e.code.toNat, e.index, e.payload] st₁ (deliver e ms)
      else none
    | _ => none

/-- The machine after the lift returned `YIELD` in the pipeline of `Proc`: the input's
readable end `1`, the output's writable end `4`, the waitable set `5` (`Proc.setupOps`). -/
def initMS (k : KM) : MS :=
  ⟨upd (upd (upd (initG k) INSR 1) OUTSW 4) WS 5, fun _ => 0, none, .ready⟩

/-! ## The correspondence with `Proc.tStep` -/

/-- The kernel state the machine holds: the state global and the buffer at `KBUF`. -/
def MS.kst (ms : MS) : KSt := ⟨ms.g GST, slice ms.m KBUF (ms.g BLEN)⟩

/-- The output the machine still has to write: bytes `OOFF..OLEN` of the output buffer. -/
def MS.pending (ms : MS) : List Val := ((slice ms.m OUT (ms.g OLEN)).drop (ms.g OOFF)).map u8v

/-- The handles of the pipeline (`Proc.setupOps`) and the bounds of the buffers. -/
def MS.ok (ms : MS) : Prop :=
  ms.g INSR = 1 ∧ ms.g OUTSW = 4 ∧ ms.g WS = 5 ∧ ms.g BLEN ≤ CAP ∧ ms.g OLEN ≤ CAP ∧
    ms.g OOFF ≤ ms.g OLEN

/-- Where a write continues: back to reading in the held state, or to closing. -/
def NextRel (ms : MS) : Option KSt → Prop
  | some s => ms.g NXT = 1 ∧ ms.kst = s
  | none => ms.g NXT = 0

/-- **The simulation relation**: the machine's `pc`, mode, kernel state and pending output
are those of the transformer's control state. -/
def Rel (ms : MS) : Silmaril.Wasm.Component.Streams.Proc.TPc KSt → Prop
  | .rd s => ms.ok ∧ ms.mode = .ready ∧ ms.g PC = pRD ∧ ms.kst = s ∧ ms.g OLEN = 0 ∧ ms.g OOFF = 0
  | .wtR s => ms.ok ∧ ms.mode = .waiting 5 ∧ ms.g PC = pWTR ∧ ms.kst = s ∧ ms.g OLEN = 0 ∧
      ms.g OOFF = 0 ∧ ms.rp = some (1, IN)
  | .eoi s => ms.ok ∧ ms.mode = .ready ∧ ms.g PC = pEOI ∧ ms.kst = s
  | .wr ys next => ms.ok ∧ ms.mode = .ready ∧ ms.g PC = pWR ∧ ms.pending = ys ∧ NextRel ms next
  | .wtW ys next => ms.ok ∧ ms.mode = .waiting 5 ∧ ms.g PC = pWTW ∧ ms.pending = ys ∧ NextRel ms next
  | .cl => ms.ok ∧ ms.mode = .ready ∧ ms.g PC = pCL
  | .fin => ms.mode = .exited
  | .fault => ms.ok ∧ ms.mode = .ready ∧ ms.g PC = pFAULT

/-- **The conditions of completeness** at a transformer state `t` with the store `st`: the
kernel's bounds hold for what it is fed or flushes in the step `tStep` takes (`fitsF`,
`fitsS`), and the event a wait takes is well formed and is the completion the module waits for
(a read's on the input, `1`; a write's on the output, `4`). -/
def Cond (k : KM) (N : Nat) (st : Store) : Silmaril.Wasm.Component.Streams.Proc.TPc KSt → Prop
  | .rd ks => (k.tr.done ks = true → fitsS 0 k.flush ks 0 = true) ∧
      ∀ st₁ p xs, Silmaril.Wasm.Component.Async.step st (.streamRead 1 N) = some (st₁, .read p xs) →
        p % 16 = 0 → fitsF k ks (xs.map byteOf) 0 = true
  | .wtR ks => ∀ st₁ e, Silmaril.Wasm.Component.Async.step st (.wait 5) = some (st₁, .event e) →
      wellFormed e = true ∧ e.code = .streamRead ∧ e.index = 1 ∧
        (e.payload % 16 = 0 → fitsF k ks (e.items.map byteOf) 0 = true)
  | .eoi ks => fitsS 0 k.flush ks 0 = true
  | .wtW _ _ => ∀ st₁ e, Silmaril.Wasm.Component.Async.step st (.wait 5) = some (st₁, .event e) →
      wellFormed e = true ∧ e.code = .streamWrite ∧ e.index = 4
  | _ => True

/-! ## The transformer over values -/

/-- The kernel over `u8` values: the transformer of the canonical ABI's view of the bytes. -/
def trV (k : KM) : Tr KSt Val Val where
  init := k.tr.init
  step s v := let r := k.tr.step s (byteOf v); (r.1, r.2.map u8v)
  flush s := (k.tr.flush s).map u8v
  done s := k.tr.done s

/-! ## The text of the module -/

def Bin.wat : Bin → String
  | .add => "i32.add" | .sub => "i32.sub" | .eq => "i32.eq" | .ne => "i32.ne"
  | .ltu => "i32.lt_u" | .geu => "i32.ge_u" | .divu => "i32.div_u" | .remu => "i32.rem_u"
  | .shl => "i32.shl"

def E.wat : E → String
  | .c n => s!"(i32.const {n % M32})"
  | .l i => s!"(local.get {i})"
  | .g i => s!"(global.get {i})"
  | .bin o a b => s!"({o.wat} {a.wat} {b.wat})"
  | .eqz a => s!"(i32.eqz {a.wat})"
  | .ld8 a => s!"(i32.load8_u {a.wat})"

/-- The local of type `i64` that receives `stream.new`'s result. -/
def L64 : Nat := 7

def callWat : BI → List String → List Nat → String
  | .streamNew, _, [d₁, d₂] =>
    s!"(local.set {L64} (call $stream.new)) (local.set {d₁} (i32.wrap_i64 (local.get {L64}))) " ++
      s!"(local.set {d₂} (i32.wrap_i64 (i64.shr_u (local.get {L64}) (i64.const 32))))"
  | .streamRead, as, [d] => s!"(local.set {d} (call $stream.read {" ".intercalate as}))"
  | .streamWrite, as, [d] => s!"(local.set {d} (call $stream.write {" ".intercalate as}))"
  | .dropR, as, _ => s!"(call $stream.drop-readable {" ".intercalate as})"
  | .dropW, as, _ => s!"(call $stream.drop-writable {" ".intercalate as})"
  | .wsNew, _, [d] => s!"(local.set {d} (call $waitable-set.new))"
  | .join, as, _ => s!"(call $waitable.join {" ".intercalate as})"
  | .taskReturn, as, _ => s!"(call $task.return {" ".intercalate as})"
  | _, _, _ => "(unreachable)"

def S.wat : S → String
  | .nop => "(nop)"
  | .unreachable => "(unreachable)"
  | .lset i e => s!"(local.set {i} {e.wat})"
  | .gset i e => s!"(global.set {i} {e.wat})"
  | .st8 a v => s!"(i32.store8 {a.wat} {v.wat})"
  | .mcopy d s n => s!"(memory.copy {d.wat} {s.wat} {n.wat})"
  | .seq a b => a.wat ++ "\n    " ++ b.wat
  | .ite c t f => s!"(if {c.wat} (then {t.wat}) (else {f.wat}))"
  | .block b => s!"(block {b.wat})"
  | .loop b => s!"(loop {b.wat})"
  | .br k => s!"(br {k})"
  | .brIf k c => s!"(br_if {k} {c.wat})"
  | .ret e => s!"(return {e.wat})"
  | .call b as d => callWat b (as.map E.wat) d

/-- **The module as WebAssembly text**, exporting `[async-lift]name` and its callback. -/
def Prog.wat (P : Prog) (name : String) : String :=
  let glob (i : Nat) := s!"  (global (mut i32) (i32.const {P.g0 i % M32}))\n"
  s!";; Generated by wasm-jco from the kernel IR (Silmaril.Wasm.JcoTool.KCore); see KCore.Thms.
(module
  (import \"[export]$root\" \"[task-return]{name}\" (func $task.return (param i32)))
  (import \"[export]$root\" \"[stream-new-0]{name}\" (func $stream.new (result i64)))
  (import \"[export]$root\" \"[async-lower][stream-read-0]{name}\" (func $stream.read (param i32 i32 i32) (result i32)))
  (import \"[export]$root\" \"[async-lower][stream-write-0]{name}\" (func $stream.write (param i32 i32 i32) (result i32)))
  (import \"[export]$root\" \"[stream-drop-readable-0]{name}\" (func $stream.drop-readable (param i32)))
  (import \"[export]$root\" \"[stream-drop-writable-0]{name}\" (func $stream.drop-writable (param i32)))
  (import \"$root\" \"[waitable-set-new]\" (func $waitable-set.new (result i32)))
  (import \"$root\" \"[waitable-join]\" (func $waitable.join (param i32 i32)))
  (memory (export \"memory\") 2)
  (func (export \"cabi_realloc\") (param i32 i32 i32 i32) (result i32) (i32.const 0x8000))
" ++ String.join ((List.range 9).map glob) ++
  s!"  (func (export \"[async-lift]{name}\") (param i32) (result i32) (local i32 i32 i32 i32 i32 i32) (local i64)
    {P.entry.wat}
    (unreachable))
  (func (export \"[callback][async-lift]{name}\") (param i32 i32 i32) (result i32) (local i32 i32 i32 i32) (local i64)
    {P.cb.wat}
    (unreachable)))
"

/-- The kernels of the tests, by the names of `wasm-streams-gen`: `map` (add one), `filter`
(drop the ASCII digits), `takeN`, `lines` (newline `10`), `rechunkN` (`1 ≤ N ≤ 255`). -/
def kernelByName (k : String) : Option KM :=
  open Silmaril.Wasm.Component.Streams.Kernel in
  if k == "map" then some kInc
  else if k == "filter" then some kNoDigit
  else if k == "lines" then some (kLines 10)
  else if k.startsWith "take" then (k.drop 4).toString.toNat?.map kTake
  else if k.startsWith "rechunk" then
    (k.drop 7).toString.toNat?.bind fun n => if 1 ≤ n ∧ n ≤ 255 then some (kRechunk n) else none
  else none

end Silmaril.Wasm.JcoTool.KCore
