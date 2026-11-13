module

public import Silmaril.Wasm.Component.Streams.Chunks.Defs

/-!
# Byte kernels: a small language for stream transformers, and core modules generated from it

A **kernel** (`KM`) is a byte transformer written in a tiny imperative language that maps
one-to-one onto WebAssembly: an `i32` state `st`, a byte buffer (in linear memory), the input byte
`x`, expressions (`KExp`: `i32` arithmetic and comparisons) and statements (`KStmt`: emit a byte,
set the state, push to the buffer, emit the buffer, clear it, `if`). Its meaning `KM.tr` is a
transformer `Tr KSt Nat Nat` of `Silmaril.Wasm.Component.Streams.Spec`.

The kernels `kMap`, `kFilter`, `kTake`, `kLines`, `kRechunk` are proved to be the transformers of
the specification (`Silmaril.Wasm.Component.Streams.Kernel.Thms`: `kMap_run`, …, by simulation):
`Tr.map`, `Tr.filter`, `Tr.take`, the line splitter `linesT` followed by an unsplitter, and the
uniform rechunker `rechunk` followed by a length-prefixed framing.

`KM.coreWat name k` **generates the core module** of a component exporting
`name: async func(in: stream<u8>) -> stream<u8>` in the callback ABI, with wit-component's core
names (`[async-lift]name`, `[callback][async-lift]name`, `[export]$root` built-ins), so that
`wasm-jco new` (or `wasm-tools component new`) turns it into a component. The step and flush of
the kernel are compiled statement by statement (`KStmt.wat`); the surrounding driver loop is fixed
text: it reads up to `batch` bytes, runs the kernel on each until it is done, writes the output,
and handles `DROPPED` (with a count) and events on idle ends as in the Component Model. The code
generator is **not verified** (no WebAssembly semantics is used here); it is tested by running
the components under wasmtime against `T.run` of the specification transformers
(`tools/wasm-streams/tests/jco.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Kernel

open Silmaril.Wasm.Component.Streams
open scoped Silmaril.Wasm.Component.Streams.Tr

/-- `2 ^ 32`. -/
def M32 : Nat := 2 ^ 32

/-- Expressions: `i32` values (as `Nat` below `2 ^ 32`). -/
inductive KExp where
  /-- The input byte. -/
  | x
  /-- The state. -/
  | st
  /-- The length of the buffer. -/
  | blen
  | lit (n : Nat)
  | add (a b : KExp)
  | sub (a b : KExp)
  | eq (a b : KExp)
  | ltu (a b : KExp)
  | eqz (a : KExp)

/-- Statements. -/
inductive KStmt where
  | skip
  | seq (a b : KStmt)
  /-- Output the low byte of `e`. -/
  | emit (e : KExp)
  /-- `st := e`. -/
  | set (e : KExp)
  /-- Append the low byte of `e` to the buffer. -/
  | push (e : KExp)
  /-- Output the buffer. -/
  | emitBuf
  /-- Empty the buffer. -/
  | clear
  /-- `if c ≠ 0 then t else f`. -/
  | ite (c : KExp) (t f : KStmt)

/-- The kernel's state: `st` and the buffer. -/
structure KSt where
  st : Nat
  buf : List Nat

/-- Evaluate an expression with input byte `b`. -/
def KExp.eval (s : KSt) (b : Nat) : KExp → Nat
  | .x => b
  | .st => s.st
  | .blen => s.buf.length
  | .lit n => n % M32
  | .add e f => (e.eval s b + f.eval s b) % M32
  | .sub e f => (e.eval s b + (M32 - f.eval s b % M32)) % M32
  | .eq e f => if e.eval s b = f.eval s b then 1 else 0
  | .ltu e f => if e.eval s b < f.eval s b then 1 else 0
  | .eqz e => if e.eval s b = 0 then 1 else 0

/-- Execute a statement with input byte `b`: the new state and the bytes output. -/
def KStmt.exec (b : Nat) : KStmt → KSt → KSt × List Nat
  | .skip, s => (s, [])
  | .seq p q, s =>
    let r := p.exec b s
    let r' := q.exec b r.1
    (r'.1, r.2 ++ r'.2)
  | .emit e, s => (s, [e.eval s b % 256])
  | .set e, s => ({ s with st := e.eval s b }, [])
  | .push e, s => ({ s with buf := s.buf ++ [e.eval s b % 256] }, [])
  | .emitBuf, s => (s, s.buf)
  | .clear, s => ({ s with buf := [] }, [])
  | .ite c p q, s => if c.eval s b ≠ 0 then p.exec b s else q.exec b s

/-- **A kernel**: initial state, step (on each input byte), flush (at the end), and the `done`
condition (nonzero: read no more). -/
structure KM where
  init : Nat
  step : KStmt
  flush : KStmt := .skip
  done : KExp := .lit 0

/-- **The meaning of a kernel**: a byte transformer. -/
def KM.tr (k : KM) : Tr KSt Nat Nat where
  init := ⟨k.init % M32, []⟩
  step s b := k.step.exec b s
  flush s := (k.flush.exec 0 s).2
  done s := k.done.eval s 0 != 0

/-! ## The kernels -/

/-- Map every byte through `e` (which reads `x`). -/
def kMap (e : KExp) : KM := ⟨0, .emit e, .skip, .lit 0⟩

/-- Keep the bytes with `c ≠ 0`. -/
def kFilter (c : KExp) : KM := ⟨0, .ite c (.emit .x) .skip, .skip, .lit 0⟩

/-- The first `n` bytes. -/
def kTake (n : Nat) : KM := ⟨n, .seq (.emit .x) (.set (.sub .st (.lit 1))), .skip, .eqz .st⟩

/-- Lines: buffer the current line; at a newline `nl` output it followed by `nl`; at the end
output the partial line, if any, followed by `nl`. -/
def kLines (nl : Nat) : KM where
  init := 0
  step := .ite (.eq .x (.lit nl)) (.seq .emitBuf (.seq (.emit (.lit nl)) .clear)) (.push .x)
  flush := .ite .blen (.seq .emitBuf (.emit (.lit nl))) .skip

/-- Uniform chunks of `n` bytes, each output after its length byte (the last one shorter). -/
def kRechunk (n : Nat) : KM where
  init := 0
  step := .seq (.push .x) (.ite (.eq .blen (.lit n)) (.seq (.emit .blen) (.seq .emitBuf .clear)) .skip)
  flush := .ite .blen (.seq (.emit .blen) .emitBuf) .skip

/-- The kernel of the tests: add one (mod 256). -/
def kInc : KM := kMap (.add .x (.lit 1))

/-- The kernel of the tests: drop the ASCII digits (`x - 48 < 10` unsigned). -/
def kNoDigit : KM := kFilter (.eqz (.ltu (.sub .x (.lit 48)) (.lit 10)))

/-! ## The specification transformers of the kernels -/

/-- Lines of a byte stream, each followed by `nl`: `linesT` then an unsplitter. -/
def linesU (nl : Nat) : Tr ((Unit × List Nat) × Unit) Nat Nat :=
  (Tr.map (fun b => [b]) ⟫ Tr.linesT (· == nl)) ⟫ Tr.flatMap (· ++ [nl])

/-- Uniform chunks of `n` bytes, each after its length: `rechunk` then a framing. -/
def rechunkU (n : Nat) : Tr ((Unit × List Nat) × Unit) Nat Nat :=
  (Tr.map (fun b => [b]) ⟫ Tr.rechunk n) ⟫ Tr.flatMap (fun c => c.length :: c)

/-! ## Code generation -/

/-- An `i32` expression. -/
def KExp.wat : KExp → String
  | .x => "(local.get $b)"
  | .st => "(global.get $st)"
  | .blen => "(global.get $blen)"
  | .lit n => s!"(i32.const {n % M32})"
  | .add e f => s!"(i32.add {e.wat} {f.wat})"
  | .sub e f => s!"(i32.sub {e.wat} {f.wat})"
  | .eq e f => s!"(i32.eq {e.wat} {f.wat})"
  | .ltu e f => s!"(i32.lt_u {e.wat} {f.wat})"
  | .eqz e => s!"(i32.eqz {e.wat})"

/-- A statement. -/
def KStmt.wat : KStmt → String
  | .skip => "(nop)"
  | .seq p q => p.wat ++ " " ++ q.wat
  | .emit e => s!"(call $emit {e.wat})"
  | .set e => s!"(global.set $st {e.wat})"
  | .push e => s!"(call $push {e.wat})"
  | .emitBuf => "(call $emitBuf)"
  | .clear => "(global.set $blen (i32.const 0))"
  | .ite c p q => s!"(if (i32.ne {c.wat} (i32.const 0)) (then {p.wat}) (else {q.wat}))"

/-- **The generated core module** of the component `name: async func(in: stream<u8>) ->
stream<u8>` running the kernel `k`, reading up to `batch` bytes at a time (`1..256`) and writing
up to `wmax` bytes per `stream.write` (`0`: all pending output). Memory: input buffer at `0x100`,
output at `0x1000`, kernel buffer at `0x10000`. -/
def KM.coreWat (name : String) (k : KM) (batch : Nat) (wmax : Nat := 0) : String :=
  let writeLen := if wmax = 0 then "(i32.sub (global.get $outlen) (global.get $outoff))"
    else s!"(select (i32.const {wmax}) (i32.sub (global.get $outlen) (global.get $outoff)) (i32.lt_u (i32.const {wmax}) (i32.sub (global.get $outlen) (global.get $outoff))))"
  s!";; Generated by wasm-streams from the kernel IR (Silmaril.Wasm.Component.Streams.Kernel).
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
  (global $ws (mut i32) (i32.const 0))
  (global $insr (mut i32) (i32.const 0))
  (global $outsw (mut i32) (i32.const 0))
  (global $outlen (mut i32) (i32.const 0))
  (global $outoff (mut i32) (i32.const 0))
  (global $eof (mut i32) (i32.const 0))
  (global $rdropped (mut i32) (i32.const 0))
  (global $flushed (mut i32) (i32.const 0))
  (global $dead (mut i32) (i32.const 0))
  (global $wpend (mut i32) (i32.const 0))
  (global $rpend (mut i32) (i32.const 0))
  (global $st (mut i32) (i32.const {k.init % M32}))
  (global $blen (mut i32) (i32.const 0))
  (func $emit (param $v i32)
    (i32.store8 (i32.add (i32.const 0x1000) (global.get $outlen)) (local.get $v))
    (global.set $outlen (i32.add (global.get $outlen) (i32.const 1))))
  (func $push (param $v i32)
    (i32.store8 (i32.add (i32.const 0x10000) (global.get $blen)) (local.get $v))
    (global.set $blen (i32.add (global.get $blen) (i32.const 1))))
  (func $emitBuf (local $i i32)
    (block $d (loop $l
      (br_if $d (i32.ge_u (local.get $i) (global.get $blen)))
      (call $emit (i32.load8_u (i32.add (i32.const 0x10000) (local.get $i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l))))
  (func $done (result i32) (local $b i32) (i32.ne {k.done.wat} (i32.const 0)))
  (func $k (param $b i32) {k.step.wat})
  (func $kflush (local $b i32) {k.flush.wat})
  ;; stop reading; the readable end is dropped once no read is in progress (a drop during a
  ;; copy traps)
  (func $stopReading
    (if (i32.and (i32.eqz (global.get $rdropped)) (i32.eqz (global.get $rpend)))
      (then (call $stream.drop-readable (global.get $insr)) (global.set $rdropped (i32.const 1))))
    (global.set $eof (i32.const 1)))
  (func $onread (param $p i32) (local $n i32) (local $i i32)
    (local.set $n (i32.shr_u (local.get $p) (i32.const 4)))
    (block $out (loop $l
      (br_if $out (i32.ge_u (local.get $i) (local.get $n)))
      (br_if $out (call $done))
      (call $k (i32.load8_u (i32.add (i32.const 0x100) (local.get $i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    ;; DROPPED may come with the items copied before the writer dropped
    (if (i32.ne (i32.and (local.get $p) (i32.const 0xf)) (i32.const 0)) (then (call $stopReading)))
    (if (call $done) (then (call $stopReading))))
  (func $onwrite (param $p i32)
    (global.set $outoff (i32.add (global.get $outoff) (i32.shr_u (local.get $p) (i32.const 4))))
    ;; DROPPED: the reader has gone; nothing more will be written
    (if (i32.ne (i32.and (local.get $p) (i32.const 0xf)) (i32.const 0))
      (then (global.set $dead (i32.const 1)) (call $stopReading))))
  (func $pump (result i32) (local $r i32)
    (loop $l
      ;; at most one copy per end: an event may also arrive on an idle end (DROPPED)
      (if (global.get $wpend)
        (then (return (i32.or (i32.const 2) (i32.shl (global.get $ws) (i32.const 4))))))
      (if (i32.and (i32.eqz (global.get $dead)) (i32.lt_u (global.get $outoff) (global.get $outlen)))
        (then
          (local.set $r (call $stream.write (global.get $outsw)
            (i32.add (i32.const 0x1000) (global.get $outoff)) {writeLen}))
          (if (i32.eq (local.get $r) (i32.const -1))
            (then (global.set $wpend (i32.const 1))
              (return (i32.or (i32.const 2) (i32.shl (global.get $ws) (i32.const 4))))))
          (call $onwrite (local.get $r))
          (br $l)))
      (global.set $outoff (i32.const 0))
      (global.set $outlen (i32.const 0))
      (if (global.get $eof)
        (then
          (if (i32.and (i32.eqz (global.get $flushed)) (i32.eqz (global.get $dead)))
            (then (global.set $flushed (i32.const 1)) (call $kflush) (br $l)))
          (if (global.get $rpend) (then (return (i32.or (i32.const 2) (i32.shl (global.get $ws) (i32.const 4))))))
          (call $stopReading)
          (call $stream.drop-writable (global.get $outsw))
          (return (i32.const 0))))
      (if (global.get $rpend)
        (then (return (i32.or (i32.const 2) (i32.shl (global.get $ws) (i32.const 4))))))
      (local.set $r (call $stream.read (global.get $insr) (i32.const 0x100) (i32.const {batch})))
      (if (i32.eq (local.get $r) (i32.const -1))
        (then (global.set $rpend (i32.const 1))
          (return (i32.or (i32.const 2) (i32.shl (global.get $ws) (i32.const 4))))))
      (call $onread (local.get $r))
      (br $l))
    unreachable)
  (func (export \"[async-lift]{name}\") (param i32) (result i32) (local $p i64)
    (global.set $insr (local.get 0))
    (local.set $p (call $stream.new))
    (global.set $outsw (i32.wrap_i64 (i64.shr_u (local.get $p) (i64.const 32))))
    (global.set $ws (call $waitable-set.new))
    (call $task.return (i32.wrap_i64 (local.get $p)))
    (call $waitable.join (global.get $insr) (global.get $ws))
    (call $waitable.join (global.get $outsw) (global.get $ws))
    (if (call $done) (then (call $stopReading)))
    (call $pump))
  (func (export \"[callback][async-lift]{name}\") (param $code i32) (param $idx i32) (param $p i32) (result i32)
    ;; dispatch on the event code and the handle
    (if (i32.and (i32.eq (local.get $code) (i32.const 2)) (i32.eq (local.get $idx) (global.get $insr)))
      (then
        (if (global.get $rpend)
          (then (global.set $rpend (i32.const 0)) (call $onread (local.get $p)))
          ;; an idle readable end: the writer dropped
          (else (call $stopReading)))))
    (if (i32.and (i32.eq (local.get $code) (i32.const 3)) (i32.eq (local.get $idx) (global.get $outsw)))
      (then
        (if (global.get $wpend)
          (then (global.set $wpend (i32.const 0)) (call $onwrite (local.get $p)))
          ;; an idle writable end: the reader dropped
          (else (global.set $dead (i32.const 1)) (call $stopReading)))))
    (call $pump)))
"

/-- The WIT world of the generated component. -/
def worldWit (name : String) : String :=
  s!"package silmaril:streams;\n\nworld {name} \{\n  export {name}: async func(in: stream<u8>) -> stream<u8>;\n}\n"

end Silmaril.Wasm.Component.Streams.Kernel
