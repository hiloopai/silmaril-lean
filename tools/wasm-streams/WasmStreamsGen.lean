import Silmaril.Wasm.Component.Streams.Kernel.Defs
import Silmaril.Wasm.Component.Streams.Spec.Defs
import Silmaril.Wasm.JcoTool.KTeeEmit.Defs
import Silmaril.Wasm.JcoTool.KFitBuf.Defs
import Silmaril.Wasm.JcoTool.KDropEmit.Defs
import Silmaril.Wasm.Validation.Check.Validate

/-!
# `wasm-streams-gen`: core modules of stream components generated from byte kernels

```
wasm-streams-gen core NAME KERNEL BATCH [WMAX] [-o OUT.wasm]
                                                  the core module of component NAME: the
                                                  GENERATED module `KDrop.genD K BATCH` of the
                                                  tools' kernel `KFitBuf.toolKernel KERNEL`
wasm-streams-gen wit NAME                        its WIT world
wasm-streams-gen tee NAME BATCH [-o OUT.wasm]    the GENERATED tee (`KTee.genT BATCH`): one
                                                  input, two outputs
wasm-streams-gen gtee NAME BATCH [-o OUT.wasm]   the same as `tee` (the name  an earlier step)
wasm-streams-gen teewit NAME                     the tee's WIT world
wasm-streams-gen valid NAME KERNEL BATCH         runs silmaril's validator `validate?` on the
wasm-streams-gen valid-tee NAME BATCH            module of `core` / `tee`: `silmaril-valid: yes`
                                                  is the hypothesis of `KCoreHost.genD_lift_valid`
                                                  / `KTeeCore.genT_lift_valid` (exit 1 if not)
wasm-streams-gen driver SEED KERNEL...           a driver component (WAT) piping a random input
                                                  through imports t0, t1, … and checking T.run
wasm-streams-gen teedriver SEED K1 K2            a driver: input → tee → (K1, K2), both checked
```

KERNEL: `map` (`x + 1 mod 256`), `filter` (drop ASCII digits), `takeN`, `lines` (newline `10`),
`rechunkN` (`1 ≤ N ≤ 255`, length-prefixed chunks). BATCH is the read size, clamped to `1..256`.

**What the core modules are** (an earlier step; before, `core` and `tee` printed text templates,
`KM.coreWat` and `KernelWat.teeWat`, with a byte certificate only):

* `core` prints `KCoreEmit.watOf (genD k N) NAME` (silmaril's proved printer,
  `KCoreEmit.watOf_encodes`); with `-o` it writes `KCoreEmit.wasmOf (genD k N) NAME` (silmaril's
  verified encoder, `wasmOf_encodes`). These are the bytes of `wasm-jco kcore NAME KERNEL N -o`
  and `wasm-wac-kbytes genD`: the module whose callback refines the kernel's node (`KDrop`), runs
  on Core 3.0 (`KCoreRun`, `KRead`), never traps and reads the kernel's whole run for every tool
  kernel (`KFitBuf.toolKernel_fits`, `KLive`). `lines` is generated as `kLinesS 10`, which has
  the same runs as `kLines 10` (`KFitBuf.linesS_run`) and no line-length bound; the template for
  `lines` trapped on a line longer than its buffer, and is no longer reachable from the tool.
  `WMAX` (the template's cap on the bytes of one `stream.write`) is accepted and ignored.
* `tee` prints `KTeeEmit.watOfT N NAME` or writes `KTeeEmit.wasmOfT N NAME`: the generated tee,
  which refines `Net`'s tee node (`KTee.step_sim`) and runs on Core 3.0 (`KTeeCore`).

The expected outputs of the drivers are computed with the **specification transformers**
(`Tr.map`, `Tr.filter`, `Tr.take`, `Kernel.linesU`, `Kernel.rechunkU`), which `Kernel.Thms`
proves equal to the kernels' meanings. See `docs/projects/wasm-wasi.md`,
`tools/wasm-streams/tests/jco.sh` and `tools/wasm-streams/tests/wat-cert.sh`.
-/

open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Kernel
open scoped Silmaril.Wasm.Component.Streams.Tr

namespace WasmStreamsGen

/-- The specification of a kernel (as a function on byte lists, through `Tr.run`). -/
def kernelOf (k : String) : Option (List Nat → List Nat) :=
  if k == "map" then
    some (Tr.map (fun b => (b + 1) % 256)).run
  else if k == "filter" then
    some (Tr.filter (fun b => !(48 ≤ b && b < 58))).run
  else if k == "lines" then some (linesU 10).run
  else if k.startsWith "take" then
    (k.drop 4).toString.toNat?.map fun n => (Tr.take n : Tr Nat Nat Nat).run
  else if k.startsWith "rechunk" then
    (k.drop 7).toString.toNat?.bind fun n =>
      if 1 ≤ n ∧ n ≤ 255 then some (rechunkU n).run else none
  else none

/-- The read size: `BATCH` clamped to `1..256`. -/
def clampBatch (b : Nat) : Nat := max 1 (min b 256)

/-- The generated module of a kernel: `KDrop.genD` of the tools' kernel. -/
def coreProg (k : String) (batch : Nat) : Option Silmaril.Wasm.JcoTool.KCore.Prog :=
  (Silmaril.Wasm.JcoTool.KFitBuf.toolKernel k).map fun km =>
    Silmaril.Wasm.JcoTool.KDropEmit.toolGen false km (clampBatch batch)

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def randoms (seed count bound : Nat) : List Nat × Nat := Id.run do
  let mut s := seed
  let mut out := #[]
  for _ in [0:count] do
    s := lcg s
    out := out.push ((s / 65536) % bound)
  return (out.toList, s)

/-- A WAT data string. -/
def dataStr (bs : List Nat) : String :=
  let hex (n : Nat) : String :=
    let d := "0123456789abcdef".toList
    String.ofList [d.getD (n / 16 % 16) '0', d.getD (n % 16) '0']
  "\"" ++ String.join (bs.map fun b => "\\" ++ hex b) ++ "\""

/-- Random input, write chunk sizes (`1..8`) and read sizes (`1..8`). -/
def scenario (seed : Nat) : List Nat × List Nat × List Nat :=
  let s0 := lcg (seed + 1)
  let (len, s1) := match randoms s0 1 120 with | (l :: _, s) => (l + 1, s) | ([], s) => (1, s)
  let alphabet : List Nat := [97, 98, 99, 10, 32, 48, 49, 50, 10, 97]
  let (rs, s2) := randoms s1 len alphabet.length
  let bytes := rs.map fun r => alphabet.getD r 97
  let (sizes, s3) := randoms s2 (len + 1) 8
  let chunks := Id.run do
    let mut out := #[]
    let mut left := len
    for z in sizes do
      if left == 0 then break
      let c := min (z + 1) left
      out := out.push c
      left := left - c
    return out.toList
  let (reads, _) := randoms s3 16 8
  (bytes, chunks, reads.map (· + 1))

/-- The WIT of a generated transformer. -/
def witOf (name : String) : String := worldWit name


def teeWit (name : String) : String :=
  s!"package silmaril:streams;\n\nworld {name} \{\n  export {name}: async func(in: stream<u8>) -> tuple<stream<u8>, stream<u8>>;\n}\n"

/-- The common head of a driver component's core module: memory, built-ins and the readers. -/
def driverCore (imports : String) (body : String) (data : String) : String :=
  s!"(component
  {imports}
  (core module $Memory (memory (export \"mem\") 1))
  (core instance $memory (instantiate $Memory))
  (core module $DM
    (import \"\" \"mem\" (memory 1))
    (import \"\" \"waitable.join\" (func $waitable.join (param i32 i32)))
    (import \"\" \"waitable-set.new\" (func $waitable-set.new (result i32)))
    (import \"\" \"waitable-set.wait\" (func $waitable-set.wait (param i32 i32) (result i32)))
    (import \"\" \"stream.new\" (func $stream.new (result i64)))
    (import \"\" \"stream.read\" (func $stream.read (param i32 i32 i32) (result i32)))
    (import \"\" \"stream.write\" (func $stream.write (param i32 i32 i32) (result i32)))
    (import \"\" \"stream.drop-readable\" (func $stream.drop-readable (param i32)))
    (import \"\" \"stream.drop-writable\" (func $stream.drop-writable (param i32)))
    (import \"\" \"t0\" (func $t0 (param i32 i32) (result i32)))
    (import \"\" \"t1\" (func $t1 (param i32 i32) (result i32)))
    (import \"\" \"t2\" (func $t2 (param i32 i32) (result i32)))
    {data}
    {body})
  (type $ST (stream u8))
  (canon waitable.join (core func $waitable.join))
  (canon waitable-set.new (core func $waitable-set.new))
  (canon waitable-set.wait (memory (core memory $memory \"mem\")) (core func $waitable-set.wait))
  (canon stream.new $ST (core func $stream.new))
  (canon stream.read $ST async (memory (core memory $memory \"mem\")) (core func $stream.read))
  (canon stream.write $ST async (memory (core memory $memory \"mem\")) (core func $stream.write))
  (canon stream.drop-readable $ST (core func $stream.drop-readable))
  (canon stream.drop-writable $ST (core func $stream.drop-writable))
  CANONS
  (core instance $dm (instantiate $DM (with \"\" (instance
    (export \"mem\" (memory $memory \"mem\"))
    (export \"waitable.join\" (func $waitable.join))
    (export \"waitable-set.new\" (func $waitable-set.new))
    (export \"waitable-set.wait\" (func $waitable-set.wait))
    (export \"stream.new\" (func $stream.new))
    (export \"stream.read\" (func $stream.read))
    (export \"stream.write\" (func $stream.write))
    (export \"stream.drop-readable\" (func $stream.drop-readable))
    (export \"stream.drop-writable\" (func $stream.drop-writable))
    (export \"t0\" (func $t0'))
    (export \"t1\" (func $t1'))
    (export \"t2\" (func $t2'))))))
  (func (export \"run\") async (result u32) (canon lift (core func $dm \"run\"))))
"

/-- The core functions of a driver: write the input in the given chunks to `$insw`, and read
`nout` outputs (handles in globals `$o0`, `$o1`) with the given read sizes, into `0x8000` and
`0xC000`; compare with the expected bytes at `0x4000` and `0x6000`. -/
def driverBody (setup : String) (nout : Nat) (exp0 exp1 : Nat) (nchunks nreads : Nat) : String :=
  s!"(global $insw (mut i32) (i32.const 0))
    (global $o0 (mut i32) (i32.const 0))
    (global $o1 (mut i32) (i32.const 0))
    (global $wpend (mut i32) (i32.const 0))
    (global $wdone (mut i32) (i32.const 0))
    (global $rp0 (mut i32) (i32.const 0))
    (global $rp1 (mut i32) (i32.const 0))
    (global $rd0 (mut i32) (i32.const {if nout ≥ 1 then 0 else 1}))
    (global $rd1 (mut i32) (i32.const {if nout ≥ 2 then 0 else 1}))
    (global $inoff (mut i32) (i32.const 0))
    (global $ci (mut i32) (i32.const 0))
    (global $ri (mut i32) (i32.const 0))
    (global $len0 (mut i32) (i32.const 0))
    (global $len1 (mut i32) (i32.const 0))
    (func $handleW (param $r i32) (local $rem i32)
      (if (i32.ne (i32.and (local.get $r) (i32.const 0xf)) (i32.const 0))
        (then (call $stream.drop-writable (global.get $insw)) (global.set $wdone (i32.const 1)) (return)))
      (global.set $inoff (i32.add (global.get $inoff) (i32.shr_u (local.get $r) (i32.const 4))))
      (local.set $rem (i32.sub (i32.load8_u (i32.add (i32.const 0x200) (global.get $ci)))
                               (i32.shr_u (local.get $r) (i32.const 4))))
      (i32.store8 (i32.add (i32.const 0x200) (global.get $ci)) (local.get $rem))
      (if (i32.eqz (local.get $rem)) (then (global.set $ci (i32.add (global.get $ci) (i32.const 1))))))
    (func $handleR0 (param $r i32)
      (global.set $len0 (i32.add (global.get $len0) (i32.shr_u (local.get $r) (i32.const 4))))
      (if (i32.ne (i32.and (local.get $r) (i32.const 0xf)) (i32.const 0))
        (then (call $stream.drop-readable (global.get $o0)) (global.set $rd0 (i32.const 1)))))
    (func $handleR1 (param $r i32)
      (global.set $len1 (i32.add (global.get $len1) (i32.shr_u (local.get $r) (i32.const 4))))
      (if (i32.ne (i32.and (local.get $r) (i32.const 0xf)) (i32.const 0))
        (then (call $stream.drop-readable (global.get $o1)) (global.set $rd1 (i32.const 1)))))
    (func $readsize (result i32)
      (global.set $ri (i32.add (global.get $ri) (i32.const 1)))
      (i32.load8_u (i32.add (i32.const 0x300) (i32.rem_u (global.get $ri) (i32.const {nreads})))))
    (func $cmp (param $got i32) (param $want i32) (param $n i32) (param $wn i32) (param $tag i32) (result i32) (local $i i32)
      (if (i32.ne (local.get $n) (local.get $wn))
        (then (return (i32.add (local.get $tag) (i32.add (i32.const 1000) (local.get $n))))))
      (block $done (loop $c
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (if (i32.ne (i32.load8_u (i32.add (local.get $got) (local.get $i)))
                    (i32.load8_u (i32.add (local.get $want) (local.get $i))))
          (then (return (i32.add (local.get $tag) (i32.add (i32.const 100000) (local.get $i))))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $c)))
      (i32.const 0))
    (func $run (export \"run\") (result i32)
      (local $p i64) (local $insr i32) (local $ws i32) (local $r i32) (local $code i32) (local $idx i32)
      (local.set $p (call $stream.new))
      (local.set $insr (i32.wrap_i64 (local.get $p)))
      (global.set $insw (i32.wrap_i64 (i64.shr_u (local.get $p) (i64.const 32))))
      {setup}
      (local.set $ws (call $waitable-set.new))
      (call $waitable.join (global.get $insw) (local.get $ws))
      (if (i32.eqz (global.get $rd0)) (then (call $waitable.join (global.get $o0) (local.get $ws))))
      (if (i32.eqz (global.get $rd1)) (then (call $waitable.join (global.get $o1) (local.get $ws))))
      (block $exit (loop $l
        (if (i32.and (i32.eqz (global.get $wpend)) (i32.eqz (global.get $wdone)))
          (then
            (if (i32.ge_u (global.get $ci) (i32.const {nchunks}))
              (then (call $stream.drop-writable (global.get $insw)) (global.set $wdone (i32.const 1)) (br $l)))
            (local.set $r (call $stream.write (global.get $insw)
              (i32.add (i32.const 0x2000) (global.get $inoff))
              (i32.load8_u (i32.add (i32.const 0x200) (global.get $ci)))))
            (if (i32.eq (local.get $r) (i32.const -1)) (then (global.set $wpend (i32.const 1)) (br $l)))
            (call $handleW (local.get $r))
            (br $l)))
        (if (i32.and (i32.eqz (global.get $rp0)) (i32.eqz (global.get $rd0)))
          (then
            (local.set $r (call $stream.read (global.get $o0)
              (i32.add (i32.const 0x8000) (global.get $len0)) (call $readsize)))
            (if (i32.eq (local.get $r) (i32.const -1)) (then (global.set $rp0 (i32.const 1)) (br $l)))
            (call $handleR0 (local.get $r))
            (br $l)))
        (if (i32.and (i32.eqz (global.get $rp1)) (i32.eqz (global.get $rd1)))
          (then
            (local.set $r (call $stream.read (global.get $o1)
              (i32.add (i32.const 0xC000) (global.get $len1)) (call $readsize)))
            (if (i32.eq (local.get $r) (i32.const -1)) (then (global.set $rp1 (i32.const 1)) (br $l)))
            (call $handleR1 (local.get $r))
            (br $l)))
        (br_if $exit (i32.and (global.get $wdone) (i32.and (global.get $rd0) (global.get $rd1))))
        (local.set $code (call $waitable-set.wait (local.get $ws) (i32.const 0)))
        (local.set $idx (i32.load (i32.const 0)))
        (if (i32.and (i32.eq (local.get $code) (i32.const 3)) (i32.eq (local.get $idx) (global.get $insw)))
          (then
            (if (global.get $wpend)
              (then (global.set $wpend (i32.const 0)) (call $handleW (i32.load (i32.const 4))))
              (else (call $stream.drop-writable (global.get $insw)) (global.set $wdone (i32.const 1))))))
        (if (i32.and (i32.eq (local.get $code) (i32.const 2)) (i32.eq (local.get $idx) (global.get $o0)))
          (then (global.set $rp0 (i32.const 0)) (call $handleR0 (i32.load (i32.const 4)))))
        (if (i32.and (i32.eq (local.get $code) (i32.const 2)) (i32.eq (local.get $idx) (global.get $o1)))
          (then (global.set $rp1 (i32.const 0)) (call $handleR1 (i32.load (i32.const 4)))))
        (br $l)))
      (local.set $r (call $cmp (i32.const 0x8000) (i32.const 0x4000) (global.get $len0) (i32.const {exp0}) (i32.const 0)))
      (if (local.get $r) (then (return (local.get $r))))
      (local.set $r (call $cmp (i32.const 0xC000) (i32.const 0x6000) (global.get $len1) (i32.const {exp1}) (i32.const 10000000)))
      (if (local.get $r) (then (return (local.get $r))))
      (i32.const 42))"

def importLine (i : Nat) : String :=
  s!"(import \"t{i}\" (func $t{i} async (param \"in\" (stream u8)) (result (stream u8))))"

def lowerLine (i : Nat) (present : Bool) : String :=
  if present then s!"(canon lower (func $t{i}) async (memory (core memory $memory \"mem\")) (core func $t{i}'))"
  else s!"(core module $Stub{i} (func (export \"f\") (param i32 i32) (result i32) unreachable))
  (core instance $stub{i} (instantiate $Stub{i}))
  (alias core export $stub{i} \"f\" (core func $t{i}'))"

def dataLines (bytes chunks reads exp0 exp1 : List Nat) : String :=
  s!"(data (i32.const 0x200) {dataStr chunks})
    (data (i32.const 0x300) {dataStr reads})
    (data (i32.const 0x2000) {dataStr bytes})
    (data (i32.const 0x4000) {dataStr exp0})
    (data (i32.const 0x6000) {dataStr exp1})"

/-- A chain driver: `in → t0 → … → t(k-1) → read`. -/
def chainDriver (seed : Nat) (specs : List (List Nat → List Nat)) : String :=
  let (bytes, chunks, reads) := scenario seed
  let expected := specs.foldl (fun acc f => f acc) bytes
  let k := specs.length
  let calls := String.intercalate "\n      " ((List.range k).map fun i =>
    let src := if i = 0 then "(local.get $insr)" else s!"(i32.load (i32.const {16 + 4 * (i - 1)}))"
    s!"(if (i32.ne (call $t{i} {src} (i32.const {16 + 4 * i})) (i32.const 2)) (then unreachable))")
  let setup := calls ++ s!"\n      (global.set $o0 (i32.load (i32.const {16 + 4 * (k - 1)})))"
  let imports := String.intercalate "\n  " ((List.range k).map importLine)
  let canons := String.intercalate "\n  " ((List.range 3).map fun i => lowerLine i (i < k))
  (driverCore imports (driverBody setup 1 expected.length 0 chunks.length reads.length)
    (dataLines bytes chunks reads expected [])).replace "CANONS" canons

/-- A tee driver: `in → tee (import t0) → (outputs through t1 and t2) → read both`. -/
def teeDriver (seed : Nat) (f1 f2 : List Nat → List Nat) : String :=
  let (bytes, chunks, reads) := scenario seed
  let e1 := f1 bytes
  let e2 := f2 bytes
  let imports := "(import \"t0\" (func $t0 async (param \"in\" (stream u8)) (result (tuple (stream u8) (stream u8)))))\n  " ++
    importLine 1 ++ "\n  " ++ importLine 2
  let setup := "(if (i32.ne (call $t0 (local.get $insr) (i32.const 16)) (i32.const 2)) (then unreachable))
      (if (i32.ne (call $t1 (i32.load (i32.const 16)) (i32.const 24)) (i32.const 2)) (then unreachable))
      (if (i32.ne (call $t2 (i32.load (i32.const 20)) (i32.const 28)) (i32.const 2)) (then unreachable))
      (global.set $o0 (i32.load (i32.const 24)))
      (global.set $o1 (i32.load (i32.const 28)))"
  let canons := String.intercalate "\n  " ((List.range 3).map fun i => lowerLine i true)
  (driverCore imports (driverBody setup 2 e1.length e2.length chunks.length reads.length)
    (dataLines bytes chunks reads e1 e2)).replace "CANONS" canons

/-- Print a certified text, or write its certified bytes. -/
def emitChecked (t : Except String String) (b : Except String ByteArray) (out : Option String) :
    IO UInt32 :=
  match out with
  | none => match t with
    | .ok t => do IO.print t; return 0
    | .error e => do IO.eprintln s!"wasm-streams-gen: {e}"; return 1
  | some f => match b with
    | .ok b => do IO.FS.writeBinFile f b; return 0
    | .error e => do IO.eprintln s!"wasm-streams-gen: {e}"; return 1

/-- Silmaril's validator on a module: the decidable hypothesis of `KCoreHost.genD_lift_valid`. -/
def validLine (m : Silmaril.Wasm.Module) : IO UInt32 :=
  if (Silmaril.Wasm.Validation.validate? m).isSome then do IO.println "silmaril-valid: yes"; return 0
  else do IO.println "silmaril-valid: no"; return 1

/-- `core NAME KERNEL BATCH [WMAX] [-o OUT]`: the positional arguments and the output file. -/
def coreArgs : List String → Option (String × String × String × Nat × Option String)
  | [name, k, batch] => some (name, k, batch, 0, none)
  | [name, k, batch, "-o", f] => some (name, k, batch, 0, some f)
  | [name, k, batch, w] => some (name, k, batch, w.toNat?.getD 0, none)
  | [name, k, batch, w, "-o", f] => some (name, k, batch, w.toNat?.getD 0, some f)
  | _ => none

end WasmStreamsGen

open WasmStreamsGen in
def main (args : List String) : IO UInt32 := do
  match args with
  | "core" :: rest =>
    match coreArgs rest with
    | some (name, k, batch, _, out) =>
      match coreProg k (batch.toNat?.getD 8) with
      | some P =>
        emitChecked (Silmaril.Wasm.JcoTool.KCoreEmit.watOf P name) (Silmaril.Wasm.JcoTool.KCoreEmit.wasmOf P name) out
      | none => IO.eprintln s!"wasm-streams-gen: unknown kernel {k}"; return 2
    | none => IO.eprintln "usage: see tools/wasm-streams/WasmStreamsGen.lean"; return 2
  | ["wit", name] => IO.print (witOf name); return 0
  | ["tee", name, batch] | ["gtee", name, batch] =>
    let b := clampBatch (batch.toNat?.getD 8)
    emitChecked (Silmaril.Wasm.JcoTool.KTeeEmit.watOfT b name) (Silmaril.Wasm.JcoTool.KTeeEmit.wasmOfT b name) none
  | ["tee", name, batch, "-o", f] | ["gtee", name, batch, "-o", f] =>
    let b := clampBatch (batch.toNat?.getD 8)
    emitChecked (Silmaril.Wasm.JcoTool.KTeeEmit.watOfT b name) (Silmaril.Wasm.JcoTool.KTeeEmit.wasmOfT b name) (some f)
  | ["teewit", name] => IO.print (teeWit name); return 0
  | ["valid", name, k, batch] =>
    match coreProg k (batch.toNat?.getD 8) with
    | some P => validLine (Silmaril.Wasm.JcoTool.KCoreEmit.toModule P name)
    | none => IO.eprintln s!"wasm-streams-gen: unknown kernel {k}"; return 2
  | ["valid-tee", name, batch] =>
    validLine (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT (clampBatch (batch.toNat?.getD 8)) name)
  | "driver" :: seed :: ks =>
    let specs := ks.filterMap kernelOf
    if specs.length ≠ ks.length ∨ ks.length = 0 ∨ ks.length > 3 then
      IO.eprintln "wasm-streams-gen: driver needs 1..3 known kernels"; return 2
    IO.print (chainDriver (seed.toNat?.getD 0) specs); return 0
  | ["teedriver", seed, k1, k2] =>
    match kernelOf k1, kernelOf k2 with
    | some f1, some f2 => IO.print (teeDriver (seed.toNat?.getD 0) f1 f2); return 0
    | _, _ => IO.eprintln "wasm-streams-gen: unknown kernel"; return 2
  | _ => IO.eprintln "usage: see tools/wasm-streams/WasmStreamsGen.lean"; return 2
