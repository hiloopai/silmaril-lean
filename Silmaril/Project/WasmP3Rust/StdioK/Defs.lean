module

public import Silmaril.Project.WasmP3Rust.DenX.Defs

/-!
# Models of the core layers of `cat` and `echo`, at the canonical ABI boundary

`stdioK P : CoreExecX` is a transition system over the calls the core code of `cat` (and its
debug build) or `echo` makes to `canon`-defined functions, in the style of
`Silmaril.Project.WasmP3Rust.HelloDen.helloK`, with the core function indices of a `Plan`
(`Silmaril.Project.WasmP3Rust.CatX.Thms` reads them off the files: `catPlan`, `echoPlan`).

**`cat`** (`examples/wasip3-rust/cat/src/main.rs`):

1. `run` (the lifted core function `P.cf`): `stdin.read-via-stream` (sync `canon lower`, the
   two handles stored at the return pointer `retA`), `stream.new`, `stdout.write-via-stream(r)`,
   `waitable-set.new`;
2. the loop: `stream.read(stdin, buf = 0, 4096)` (async). `BLOCKED` joins the stream to the set
   and returns `WAIT`; the callback (`P.cb`) on `STREAM_READ` for it, or a direct answer, gives
   a copy result `(res, k)`: the chunk is the first `k` bytes stored at `buf`. A non-empty chunk
   is written with `write_all` (as `helloK` writes its message: `stream.write(w, off, len -
   off)`, `COMPLETED k` advances, `BLOCKED` waits for `STREAM_WRITE`; a `DROPPED` or
   `CANCELLED` write ends the run with `error`, the Rust code's `return false`). Then
   `COMPLETED` reads again; `DROPPED` and `CANCELLED` leave the loop;
3. `stream.drop-writable(w)`, then `future.read` of stdin's future and of stdout's future
   (each may block and complete through `FUTURE_READ`); `task.return` of `ok` when both are
   `ok`, else `error`; `EXIT`.

**`echo`** (`examples/wasip3-rust/echo/src/main.rs`): `environment.get-arguments` (sync
`canon lower`; `DenX.den` lowers the `list<string>` into memory through `alloc`), the line is
the arguments after the first joined by spaces with a newline, read back from memory as the
Canonical ABI laid it out (`argStrs`); then as `cat` with one chunk (the line) and no stdin;
a failed write traps (the Rust code's `assert!`).

**Abstractions.** As for `helloK`: the real code runs `wit-bindgen`'s async runtime, which
joins the stdout future's read with the loop (`futures::join!`) and polls; it also calls
`context.get/set`, `waitable-set.poll`, `waitable-set.drop`, `future.drop-readable`. The model
fixes one order of the calls (the future reads after the loop). Memory is modelled by what the
code reads: the read buffer at `0`, the return area at `retA`, the future result at `futA`, and
the blocks `realloc` handed out (from `heapA`, a bump allocator that fails at `2 ^ 32`).
Whether the core modules refine the model is the open target `Task.catCore`/`Task.echoCore`
(`CatX.Thms`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.StdioK

open Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Project.WasmP3Rust.Den (CoreExec le32)
open Silmaril.Project.WasmP3Rust.DenX
open Silmaril.Wasm.Component.Async (CopyResult blocked)

/-- Which program. -/
inductive Kind where
  | cat | echo
  deriving DecidableEq, Repr

/-- **A plan**: the program, and the core function indices of the lift of `run` and of the
`canon`-defined functions it calls. -/
structure Plan where
  kind : Kind
  cf : Nat
  cb : Nat
  /-- `cat`: `stdin.read-via-stream`; `echo`: `environment.get-arguments`. -/
  src : Nat
  streamNew : Nat
  wvs : Nat
  wsNew : Nat
  read : Nat
  write : Nat
  join : Nat
  dropW : Nat
  fread : Nat
  taskReturn : Nat

/-! ## Memory layout -/

/-- The return area of the sync lowers. -/
def retA : Nat := 8
/-- Where `future.read` stores its result. -/
def futA : Nat := 16
/-- The first address `realloc` hands out. -/
def heapA : Nat := 64
/-- The read buffer size. -/
def bufN : Nat := 4096

/-- The little-endian `u32` of four bytes (missing bytes are `0`). -/
def dec32 (bs : List (BitVec 8)) : Nat :=
  (bs.getD 0 0).toNat + 256 * (bs.getD 1 0).toNat + 65536 * (bs.getD 2 0).toNat +
    16777216 * (bs.getD 3 0).toNat

/-! ## Configurations -/

/-- Where the model is. `fread true`/`joinF true`/`waitF true` are for stdin's future,
`… false` for stdout's. -/
inductive Pc where
  | init | src | new | wvs | wsNew
  | read | joinR | waitR
  | write | joinW | waitW
  | dropW | fread (stdin : Bool) | joinF (stdin : Bool) | waitF (stdin : Bool)
  | ret (v : Nat) | exit | trapped
  deriving DecidableEq, Repr

/-- The model's configuration. -/
structure SConf where
  pc : Pc
  /-- stdout's stream ends, its future, the waitable set. -/
  r : Nat := 0
  w : Nat := 0
  f : Nat := 0
  s : Nat := 0
  /-- stdin's readable end and future. -/
  rin : Nat := 0
  fin : Nat := 0
  /-- The chunk being written, and how much of it is out. -/
  chunk : List (BitVec 8) := []
  off : Nat := 0
  /-- The last read reported `COMPLETED` (read again after the chunk). -/
  more : Bool := false
  /-- The bytes at the read buffer, at the return area, the future result byte. -/
  buf : List (BitVec 8) := []
  ret : List (BitVec 8) := []
  res : Nat := 0
  /-- stdin's future result (`0`: ok). -/
  ok1 : Nat := 0
  /-- Blocks stored elsewhere (newest first), and the next free address. -/
  mem : List (Nat × List (BitVec 8)) := []
  next : Nat := heapA

/-- The block stored at `p`. -/
def SConf.at (c : SConf) (p : Nat) : List (BitVec 8) :=
  ((c.mem.find? (·.1 = p)).map (·.2)).getD []

/-- **The arguments as the code reads them back**: the `(array, n)` pair at the return area,
the `(ptr, len)` pair of each element, the bytes of each string. -/
def argStrs (c : SConf) : List (List (BitVec 8)) :=
  let arr := dec32 (c.ret.take 4)
  let n := dec32 (c.ret.drop 4)
  (List.range n).map fun i =>
    let e := c.at (arr + 8 * i)
    (c.at (dec32 (e.take 4))).take (dec32 (e.drop 4))

/-- **`echo`'s line**: the arguments after the first, joined by spaces, and a newline. -/
def lineOf (ss : List (List (BitVec 8))) : List (BitVec 8) :=
  List.intercalate [32] (ss.drop 1) ++ [10]

variable (P : Plan)

/-- The future read at `fread b`. -/
def SConf.fut (c : SConf) (b : Bool) : Nat := if b then c.fin else c.f

/-- The call each program point makes. -/
def callOf (c : SConf) : Option (Nat × List Nat) :=
  match c.pc with
  | .src => some (P.src, [retA])
  | .new => some (P.streamNew, [])
  | .wvs => some (P.wvs, [c.r])
  | .wsNew => some (P.wsNew, [])
  | .read => some (P.read, [c.rin, 0, bufN])
  | .joinR => some (P.join, [c.rin, c.s])
  | .write => some (P.write, [c.w, c.off, c.chunk.length - c.off])
  | .joinW => some (P.join, [c.w, c.s])
  | .dropW => some (P.dropW, [c.w])
  | .fread b => some (P.fread, [c.fut b, futA])
  | .joinF b => some (P.join, [c.fut b, c.s])
  | .ret v => some (P.taskReturn, [v])
  | _ => none

/-- After a chunk is out: `cat` reads again after a `COMPLETED` read, otherwise the stream is
closed. -/
def afterChunk (c : SConf) : SConf :=
  if P.kind = .cat ∧ c.more then { c with pc := .read } else { c with pc := .dropW }

/-- Start writing a chunk (nothing to write: as after it). -/
def startChunk (c : SConf) : SConf :=
  if c.off < c.chunk.length then { c with pc := .write } else afterChunk P c

/-- A read delivered `k` items with the copy result `res`. -/
def gotChunk (c : SConf) (res : CopyResult) (k : Nat) : SConf :=
  startChunk P { c with chunk := c.buf.take k, off := 0, more := decide (res = .completed) }

/-- `k` more bytes of the chunk were written. -/
def advance (c : SConf) (k : Nat) : SConf :=
  if c.off + k < c.chunk.length then { c with off := c.off + k, pc := .write }
  else afterChunk P { c with off := c.chunk.length }

/-- A write that failed: `cat` returns `error`, `echo` traps. -/
def failWrite (c : SConf) : SConf :=
  if P.kind = .cat then { c with pc := .ret 1 } else { c with pc := .trapped }

/-- A future read gave `v` (`0`: ok). -/
def gotFuture (c : SConf) (b : Bool) (v : Nat) : SConf :=
  if b then { c with ok1 := v, pc := .fread false }
  else { c with pc := .ret (if c.ok1 = 0 ∧ v = 0 then 0 else 1) }

/-- After a read reported the packed copy result `code`. -/
def afterRead (c : SConf) (code : Nat) : SConf :=
  match copyOf code with
  | some none => { c with pc := .joinR }
  | some (some (res, k)) => gotChunk P c res k
  | none => { c with pc := .ret 1 }

/-- After a write reported the packed copy result `code`. -/
def afterWrite (c : SConf) (code : Nat) : SConf :=
  match copyOf code with
  | some none => { c with pc := .joinW }
  | some (some (.completed, k)) => advance P c k
  | _ => failWrite P c

/-- After a future read reported the packed copy result `code`. -/
def afterFut (c : SConf) (b : Bool) (code : Nat) : SConf :=
  match copyOf code with
  | some none => { c with pc := .joinF b }
  | some (some (.completed, _)) => gotFuture c b c.res
  | _ => gotFuture c b 1

/-- After the first call: `cat` has stdin's handles in the return area, `echo` its arguments
in memory. -/
def afterSrc (c : SConf) : SConf :=
  match P.kind with
  | .cat => { c with pc := .new, rin := dec32 (c.ret.take 4), fin := dec32 (c.ret.drop 4) }
  | .echo => { c with pc := .new, chunk := lineOf (argStrs c), off := 0 }

/-- The answer of a call. -/
def afterCall (c : SConf) (vs : List Nat) : SConf :=
  match c.pc, vs with
  | .src, [] => afterSrc P c
  | .new, [p] => { c with pc := .wvs, r := p % 2 ^ 32, w := p / 2 ^ 32 }
  | .wvs, [fv] => { c with pc := .wsNew, f := fv }
  | .wsNew, [sv] =>
    if P.kind = .cat then { c with pc := .read, s := sv } else startChunk P { c with s := sv }
  | .read, [code] => afterRead P c code
  | .joinR, [] => { c with pc := .waitR }
  | .write, [code] => afterWrite P c code
  | .joinW, [] => { c with pc := .waitW }
  | .dropW, [] => { c with pc := if P.kind = .cat then .fread true else .fread false }
  | .fread b, [code] => afterFut c b code
  | .joinF b, [] => { c with pc := .waitF b }
  | .ret _, [] => { c with pc := .exit }
  | _, _ => { c with pc := .trapped }

/-- The callback, on the event `(code, index, payload)`. -/
def onEvent (c : SConf) (ev : List Nat) : SConf :=
  match c.pc, ev with
  | .waitR, [2, i, p] =>
    if i = c.rin then
      match copyOf p with
      | some (some (res, k)) => gotChunk P c res k
      | _ => { c with pc := .ret 1 }
    else c
  | .waitW, [3, i, p] =>
    if i = c.w then
      match copyOf p with
      | some (some (.completed, k)) => advance P c k
      | _ => failWrite P c
    else c
  | .waitF b, [4, i, p] =>
    if i = c.fut b then
      match copyOf p with
      | some (some (.completed, _)) => gotFuture c b c.res
      | _ => gotFuture c b 1
    else c
  | _, _ => c

/-- The model is waiting for an event. -/
def waiting : Pc → Bool
  | .waitR | .waitW | .waitF _ => true
  | _ => false

/-- The packed code the model returns. -/
def retOf (c : SConf) : Option Nat :=
  if waiting c.pc then some (2 + 16 * c.s)
  else if c.pc = .exit then some 0
  else none

/-- Store bytes. -/
def store (c : SConf) (p : Nat) (bs : List (BitVec 8)) : SConf :=
  if p = 0 then { c with buf := bs }
  else if p = retA then { c with ret := bs }
  else if p = futA then { c with res := (bs.head?.map BitVec.toNat).getD 0 }
  else { c with mem := (p, bs) :: c.mem }

/-- **The model of `cat`'s or `echo`'s core layer.** -/
abbrev stdioK : CoreExecX where
  Conf := SConf
  init := { pc := .init }
  enter c k args :=
    if k = P.cf ∧ c.pc = .init ∧ args = [] then some { c with pc := .src }
    else if k = P.cb ∧ waiting c.pc then some (onEvent P c args)
    else none
  step _ _ := False
  callOut c k args := callOf P c = some (k, args)
  resume := afterCall P
  ret c vs := ∃ p, retOf c = some p ∧ vs = [p]
  trap c := c.pc = .trapped
  load c p n := some ((c.chunk.drop p).take n)
  store c p bs := some (store c p bs)
  alloc c size _ :=
    if c.next + size < 2 ^ 32 then some ({ c with next := c.next + size }, c.next) else none

/-! ## Wiring -/

/-- The built-in of the first call: `stdin.read-via-stream` for `cat`, `get-arguments` for
`echo`. -/
def srcB : Kind → BuiltinX
  | .cat => .base (.wasi ⟨stdinRead3, Den.stdinRead3_mem⟩)
  | .echo => .getArgs

/-- **The wiring of a plan** in a component's index spaces: the lift of `run` and the built-ins
the model calls. -/
structure Wiring (P : Plan) (S : Silmaril.Project.WasmP3Rust.Den.Spaces) : Prop where
  run : Silmaril.Project.WasmP3Rust.Den.runLift S = some (P.cf, P.cb)
  src : builtinX S P.src = srcB P.kind
  streamNew : builtinX S P.streamNew = .base .streamNew
  wvs : builtinX S P.wvs = .base (.wasi ⟨stdoutWrite3, Den.stdoutWrite3_mem⟩)
  wsNew : builtinX S P.wsNew = .base .wsNew
  read : builtinX S P.read = .base .streamRead
  write : builtinX S P.write = .base .streamWrite
  join : builtinX S P.join = .base .join
  dropW : builtinX S P.dropW = .base .streamDropW
  fread : builtinX S P.fread = .base .futureRead
  taskReturn : builtinX S P.taskReturn = .base .taskReturn

/-- The plan of `cat.wasm` (core function indices from its index spaces, `CatX.Thms`). -/
def catPlan : Plan :=
  { kind := .cat, cf := 31, cb := 32, src := 26, streamNew := 8, wvs := 22, wsNew := 3,
    read := 30, write := 29, join := 4, dropW := 20, fread := 28, taskReturn := 23 }

/-- The plan of `cat-debug.wasm`: the same calls at other indices. -/
def catDebugPlan : Plan :=
  { kind := .cat, cf := 31, cb := 32, src := 29, streamNew := 15, wvs := 1, wsNew := 18,
    read := 27, write := 28, join := 17, dropW := 14, fread := 25, taskReturn := 0 }

/-- The plan of `echo.wasm`. -/
def echoPlan : Plan :=
  { kind := .echo, cf := 31, cb := 32, src := 26, streamNew := 8, wvs := 22, wsNew := 3,
    read := 30, write := 29, join := 4, dropW := 20, fread := 28, taskReturn := 23 }

end Silmaril.Project.WasmP3Rust.StdioK

end
