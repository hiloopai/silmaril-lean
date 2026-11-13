module

public import Silmaril.Wasi.Versions.P1.Theory.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# Preview1 over 0.2: the official adapter, as a stateful component

The wasmtime **preview1 adapter** (`specs/wasi/adapter/lib.rs`, wasmtime `v50.0.1`) is a core
module exporting the preview1 functions and importing WASI 0.2.12 (`wasi:cli/command`). This
module transcribes a slice of it as a stateful component of `Silmaril.Wasi.Versions.Stateful`
that imports a 0.2 world and exports the preview1 functions (`world`). Its body `body` follows
the adapter function by function; the comments name the Rust function mirrored.

## Imports (WASI 0.2.12, `specs/wasi/0.2.12`)

`wasi:cli/{stdin,stdout,stderr}.get-*`, `wasi:io/streams` (`blocking-write-and-flush`,
`blocking-read`, the stream drops), `wasi:io/error.[resource-drop]error`,
`wasi:filesystem/preopens.get-directories`, `wasi:filesystem/types` (`open-at`, `get-type`,
`write-via-stream`, `read-via-stream`, `filesystem-error-code`, `[resource-drop]descriptor`),
`wasi:clocks/{monotonic-clock,wall-clock}.{now,resolution}`,
`wasi:random/random.get-random-bytes`, `wasi:cli/environment.get-{arguments,environment}`,
`wasi:cli/exit.exit`. Value encodings are those of `Silmaril.Wasi.Theory`; WIT `flags` are
records of `bool`s, enums are payload-free variants, `option` is `none = 0`/`some = 1`.

## The 0.2 theory assumed (`p2Th`)

`p2Typed` (every answer of an import has its WIT type; `blocking-read(len)` returns at most
`len` bytes; `get-random-bytes(len)` returns `len` bytes; `get-directories` returns at most
`maxPreopens = 125` preopens, which is what fits in the adapter's table) and `Silmaril.Wasi.clockTh` (the
monotonic clock never decreases).

## State (`ASt`, mirroring `Descriptors` of `descriptors.rs`)

The descriptor table, created at the first call that needs it (`Descriptors::new`: stdin,
stdout, stderr at `0, 1, 2`, then the preopens), and the free list of closed descriptors
(`Descriptors::closed`, most recently closed first). A file descriptor holds its 0.2
descriptor, whether it is a directory, its position and its cached input and output streams.

## The slice

`fd_write`, `fd_read` (stdio and files), `fd_close`, `path_open`, `clock_time_get`,
`clock_res_get`, `random_get`, `args_get`, `args_sizes_get`, `environ_get`,
`environ_sizes_get`, `sched_yield`, `proc_exit`. Every other preview1 function answers
`errno::nosys` (a partial adapter: a *related variant* of the official one).

Deviations from `lib.rs` inside the slice, all on paths that do not change the answers to a
well-behaved host, except the last two:

* the adapter's allocation states (`get_allocation_state`) are not modelled: the state is always
  allocated;
* preopens are taken as directories without calling `get-type` (`open_preopens` calls it and
  traps on an error);
* writes in chunks of 4096 bytes by `blocking-write-and-flush` are modelled (`writeLoop`), but
  `path_open` with `fdflags` `append` or `nonblock` answers `errno::notsup` (the adapter supports
  them through `append-via-stream`, `stat` and `check-write`);
* an ill-typed answer of the host, which the canonical ABI turns into a trap, is a trap (`none`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## The 0.2 imports -/

/-- `wasi:cli/stdin.get-stdin`. -/
def getStdin : FnName := ⟨"wasi:cli/stdin", "get-stdin"⟩
/-- `wasi:cli/stderr.get-stderr`. -/
def getStderr : FnName := ⟨"wasi:cli/stderr", "get-stderr"⟩
/-- `wasi:io/streams.[method]input-stream.blocking-read`. -/
def inRead : FnName := ⟨"wasi:io/streams", "[method]input-stream.blocking-read"⟩
/-- `wasi:io/streams.[resource-drop]input-stream`. -/
def inDrop : FnName := ⟨"wasi:io/streams", "[resource-drop]input-stream"⟩
/-- `wasi:io/error.[resource-drop]error`. -/
def errDrop : FnName := ⟨"wasi:io/error", "[resource-drop]error"⟩
/-- `wasi:filesystem/types.filesystem-error-code`. -/
def fsErrCode : FnName := ⟨"wasi:filesystem/types", "filesystem-error-code"⟩
/-- `wasi:filesystem/types.[method]descriptor.get-type`. -/
def getType : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.get-type"⟩
/-- `wasi:filesystem/types.[method]descriptor.write-via-stream`. -/
def writeVia : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.write-via-stream"⟩
/-- `wasi:filesystem/types.[method]descriptor.read-via-stream`. -/
def readVia : FnName := ⟨"wasi:filesystem/types", "[method]descriptor.read-via-stream"⟩
/-- `wasi:clocks/monotonic-clock.resolution`. -/
def monoRes : FnName := ⟨"wasi:clocks/monotonic-clock", "resolution"⟩
/-- `wasi:clocks/wall-clock.now`. -/
def wallNow : FnName := ⟨"wasi:clocks/wall-clock", "now"⟩
/-- `wasi:clocks/wall-clock.resolution`. -/
def wallRes : FnName := ⟨"wasi:clocks/wall-clock", "resolution"⟩
/-- `wasi:random/random.get-random-bytes`. -/
def randBytes : FnName := ⟨"wasi:random/random", "get-random-bytes"⟩
/-- `wasi:cli/environment.get-arguments`. -/
def getArgs : FnName := ⟨"wasi:cli/environment", "get-arguments"⟩
/-- `wasi:cli/environment.get-environment`. -/
def getEnv : FnName := ⟨"wasi:cli/environment", "get-environment"⟩
/-- `wasi:cli/exit.exit`. -/
def exitFn : FnName := ⟨"wasi:cli/exit", "exit"⟩

/-- The imports of the adapter slice. -/
inductive Imp where
  | getStdin | getStdout | getStderr | write | outDrop | read | inDrop | errDrop | errCode
  | getDirs | openAt | getType | writeVia | readVia | fdDrop | now | monoRes | wallNow | wallRes
  | rand | getArgs | getEnv | exit
  deriving DecidableEq, Repr

/-- The WIT function of an import. -/
def Imp.name : Imp → FnName
  | .getStdin => Silmaril.Wasi.Versions.Adapter.getStdin
  | .getStdout => Silmaril.Wasi.getStdout
  | .getStderr => Silmaril.Wasi.Versions.Adapter.getStderr
  | .write => Silmaril.Wasi.streamWrite
  | .outDrop => Silmaril.Wasi.streamDrop
  | .read => Silmaril.Wasi.Versions.Adapter.inRead
  | .inDrop => Silmaril.Wasi.Versions.Adapter.inDrop
  | .errDrop => Silmaril.Wasi.Versions.Adapter.errDrop
  | .errCode => Silmaril.Wasi.Versions.Adapter.fsErrCode
  | .getDirs => Silmaril.Wasi.getDirs
  | .openAt => Silmaril.Wasi.openAt
  | .getType => Silmaril.Wasi.Versions.Adapter.getType
  | .writeVia => Silmaril.Wasi.Versions.Adapter.writeVia
  | .readVia => Silmaril.Wasi.Versions.Adapter.readVia
  | .fdDrop => Silmaril.Wasi.fdDrop
  | .now => Silmaril.Wasi.clockNow
  | .monoRes => Silmaril.Wasi.Versions.Adapter.monoRes
  | .wallNow => Silmaril.Wasi.Versions.Adapter.wallNow
  | .wallRes => Silmaril.Wasi.Versions.Adapter.wallRes
  | .rand => Silmaril.Wasi.Versions.Adapter.randBytes
  | .getArgs => Silmaril.Wasi.Versions.Adapter.getArgs
  | .getEnv => Silmaril.Wasi.Versions.Adapter.getEnv
  | .exit => Silmaril.Wasi.Versions.Adapter.exitFn

/-- All imports. -/
def Imp.all : List Imp :=
  [.getStdin, .getStdout, .getStderr, .write, .outDrop, .read, .inDrop, .errDrop, .errCode,
   .getDirs, .openAt, .getType, .writeVia, .readVia, .fdDrop, .now, .monoRes, .wallNow, .wallRes,
   .rand, .getArgs, .getEnv, .exit]

theorem Imp.mem_all (i : Imp) : i ∈ Imp.all := by cases i <;> decide

/-- The import named `f`, if any. -/
def Imp.ofName (f : FnName) : Option Imp := Imp.all.find? (·.name == f)

/-- The imports of the adapter slice, as functions. -/
def importList : List FnName := Imp.all.map Imp.name

/-- The imports of the adapter slice, as a set. -/
def imports : Set FnName := {f | f ∈ importList}

/-- **The adapter's world**: it imports 0.2 and exports preview1. -/
def world : World := ⟨imports, P1.imports⟩

/-- An import of the adapter. -/
abbrev AFn : Type := {f // f ∈ imports}

/-- An import, with its membership proof. -/
def Imp.fn (i : Imp) : AFn := ⟨i.name, List.mem_map_of_mem (Imp.mem_all i)⟩

/-! ## The 0.2 theory assumed -/

/-- A `stream-error`: `last-operation-failed(error)` or `closed`. -/
def isStreamErr : Val → Bool
  | .variant 0 (some (.u32 _)) => true
  | .variant 1 none => true
  | _ => false

/-- Every value is a `u8`. -/
def allU8 (vs : List Val) : Bool := vs.all fun | .u8 _ => true | _ => false

/-- An environment entry `tuple<string, string>`. -/
def isEnvPair : Val → Bool
  | .record [k, v] => P1.isStrV k && P1.isStrV v
  | _ => false

/-- A `result<own<…>, error-code>`. -/
def isHandleRes : Option (List Val) → Bool
  | some [.variant 0 (some (.u32 _))] => true
  | some [.variant 1 (some (.variant _ none))] => true
  | _ => false

/-- At most `MAX_DESCRIPTORS - 3 = 125` preopens fit in the adapter's table (`push` of a
further one fails, and `open_preopens` traps). -/
def maxPreopens : Nat := 125

/-- The typing of the answers of an import. -/
def Imp.ok : Imp → List Val → Option (List Val) → Bool
  | .getStdin, _, r | .getStdout, _, r | .getStderr, _, r =>
    (match r with | some [.u32 _] => true | _ => false)
  | .getDirs, _, r =>
    (match r with
     | some [.record ds] => ds.all preopenOk && decide (ds.length ≤ maxPreopens)
     | _ => false)
  | .write, _, r =>
    (match r with
     | some [.variant 0 none] => true
     | some [.variant 1 (some e)] => isStreamErr e
     | _ => false)
  | .read, a, r =>
    (match a, r with
     | [_, .u64 len], some [.variant 0 (some (.record bs))] =>
       allU8 bs && decide (bs.length ≤ len.toNat)
     | _, some [.variant 1 (some e)] => isStreamErr e
     | _, _ => false)
  | .outDrop, _, r | .inDrop, _, r | .errDrop, _, r | .fdDrop, _, r =>
    (match r with | some [] => true | _ => false)
  | .errCode, _, r =>
    (match r with
     | some [.variant 0 none] => true
     | some [.variant 1 (some (.variant _ none))] => true
     | _ => false)
  | .openAt, _, r | .writeVia, _, r | .readVia, _, r => isHandleRes r
  | .getType, _, r =>
    (match r with
     | some [.variant 0 (some (.variant _ none))] => true
     | some [.variant 1 (some (.variant _ none))] => true
     | _ => false)
  | .now, _, r | .monoRes, _, r => (match r with | some [.u64 _] => true | _ => false)
  | .wallNow, _, r | .wallRes, _, r =>
    (match r with | some [.record [.u64 _, .u32 _]] => true | _ => false)
  | .rand, a, r =>
    (match a, r with
     | [.u64 len], some [.record bs] => allU8 bs && decide (bs.length = len.toNat)
     | _, _ => false)
  | .getArgs, _, r => (match r with | some [.record ss] => ss.all P1.isStrV | _ => false)
  | .getEnv, _, r => (match r with | some [.record ps] => ps.all isEnvPair | _ => false)
  | .exit, _, _ => true

/-- The typing of the answers of the adapter's imports (other functions are unconstrained). -/
def p2Ok : WEv → Bool
  | .imp f a r =>
    match Imp.ofName f with
    | some i => i.ok a r
    | none => true
  | _ => true

/-- **The 0.2 typing theory** of the adapter's imports. -/
def p2Typed : Protocol Unit WEv := pointwise p2Ok

/-- **The 0.2 theory assumed by the adapter**: typing and the monotonic clock. -/
def p2Th : Protocol (Unit × Option (BitVec 64)) WEv := p2Typed.prod clockTh

/-! ## State -/

/-- A preview1 descriptor of the adapter. -/
inductive Desc where
  /-- A closed descriptor. -/
  | closed
  /-- Standard input, with its input stream. -/
  | stdin (i : BitVec 32)
  /-- Standard output, with its output stream. -/
  | stdout (o : BitVec 32)
  /-- Standard error, with its output stream. -/
  | stderr (o : BitVec 32)
  /-- A file or directory: its 0.2 descriptor, whether it is a directory, its position, and its
  cached input and output streams. -/
  | file (d : BitVec 32) (isDir : Bool) (pos : Nat) (inp out : Option (BitVec 32))

/-- The state of the adapter. -/
structure ASt where
  /-- The descriptor table, once created. -/
  table : Option (List Desc)
  /-- The free list: closed descriptors, most recently closed first. -/
  free : List Nat

/-- The initial state: no table yet. -/
def ASt.init : ASt := ⟨none, []⟩

/-- The descriptor at `fd` (closed when out of range). -/
def getD (t : List Desc) (fd : BitVec 32) : Desc := t.getD fd.toNat .closed

/-- Replace the descriptor at `fd`. -/
def setD (s : ASt) (t : List Desc) (fd : BitVec 32) (d : Desc) : ASt := ⟨some (t.set fd.toNat d), s.free⟩

/-! ## Programs -/

/-- A program of the adapter. -/
abbrev AProg : Type := SProg ASt imports

/-- Call an import. -/
def icall (i : Imp) (args : List Val) (k : Option (List Val) → AProg) : AProg :=
  .call (i.fn, args) k

/-- Return `r` in the state `s`. -/
def done (s : ASt) (r : Option (List Val)) : AProg := .pure (s, r)

/-- Return `ok(v)`. -/
def okR (s : ASt) (v : Option Val) : AProg := done s (P1.okAns v)

/-- Return `error(e)`. -/
def errR (s : ASt) (e : Nat) : AProg := done s (P1.errAns e)

/-- Trap. -/
def trapR (s : ASt) : AProg := done s none

/-- `impl From<filesystem::ErrorCode> for Errno`. -/
def codeErrno : Val → Nat
  | .variant k none => P1.Gen.errnoOfCode.getD k P1.eIo
  | _ => P1.eIo

/-- `stream_error_to_errno` of a `last-operation-failed(err)`: ask `filesystem-error-code`,
then drop the error. -/
def lastOpErrno (s : ASt) (err : BitVec 32) (k : Nat → AProg) : AProg :=
  icall .errCode [.u32 err] fun
    | some [.variant 1 (some c)] => icall .errDrop [.u32 err] fun _ => k (codeErrno c)
    | some [.variant 0 none] => icall .errDrop [.u32 err] fun _ => k P1.eIo
    | _ => trapR s

/-- **`BlockingMode::Blocking.write`**: `blocking-write-and-flush` in chunks of 4096 bytes. -/
def writeLoop (s : ASt) (h : BitVec 32) (onOk : AProg) (onErr : Nat → AProg)
    (bs : List (BitVec 8)) : AProg :=
  icall .write [.u32 h, bytesV (bs.take 4096)] fun r =>
    match r with
    | some [.variant 0 none] =>
      if _hb : bs.length ≤ 4096 then onOk else writeLoop s h onOk onErr (bs.drop 4096)
    | some [.variant 1 (some (.variant 1 none))] => onErr P1.eIo
    | some [.variant 1 (some (.variant 0 (some (.u32 err))))] => lastOpErrno s err onErr
    | _ => trapR s
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega

/-- **`BlockingMode::Blocking.read`**: one `blocking-read`; a closed stream reads nothing. -/
def readOnce (s : ASt) (h : BitVec 32) (n : Nat) (onOk : List Val → AProg)
    (onErr : Nat → AProg) : AProg :=
  icall .read [.u32 h, .u64 (BitVec.ofNat 64 n)] fun
    | some [.variant 0 (some (.record bs))] =>
      if allU8 bs ∧ bs.length ≤ n then onOk bs else trapR s
    | some [.variant 1 (some (.variant 1 none))] => onOk []
    | some [.variant 1 (some (.variant 0 (some (.u32 err))))] => lastOpErrno s err onErr
    | _ => trapR s

/-- The preopens of `get-directories`, as directory descriptors. -/
def preopens : List Val → Option (List Desc)
  | [] => some []
  | .record [.u32 d, _] :: t => (preopens t).map (.file d true 0 none none :: ·)
  | _ :: _ => none

/-- The end of `Descriptors::new`: `get-directories`, then the table of stdin `i`, stdout `o`,
stderr `e` and the preopens (`open_preopens`), and the continuation `k`. -/
def withPreopens (s : ASt) (k : ASt → List Desc → AProg) (i o e : BitVec 32) : AProg :=
  icall .getDirs [] fun
  | some [.record ps] =>
    (match preopens ps with
     | some l => if l.length ≤ maxPreopens then k ⟨some ([.stdin i, .stdout o, .stderr e] ++ l),
         s.free⟩ ([.stdin i, .stdout o, .stderr e] ++ l) else trapR s
     | none => trapR s)
  | _ => trapR s

/-- **`State::with` / `Descriptors::new`**: the table, created at the first use (stdin, stdout,
stderr, then the preopens). -/
def withTable (s : ASt) (k : ASt → List Desc → AProg) : AProg :=
  match s.table with
  | some t => k s t
  | none =>
    icall .getStdin [] fun
    | some [.u32 i] => icall .getStdout [] fun
      | some [.u32 o] => icall .getStderr [] fun
        | some [.u32 e] => withPreopens s k i o e
        | _ => trapR s
      | _ => trapR s
    | _ => trapR s

/-! ## The preview1 functions -/

/-- The first buffer of a ciovec list, after skipping empty ones while more than one is left;
`none` for an empty list (`fd_write`'s preamble). -/
def firstBuf : List Val → Option (List (BitVec 8))
  | [] => none
  | [b] => some (bytesOf b)
  | b :: t => if bytesOf b = [] then firstBuf t else some (bytesOf b)

/-- The length of an iovec. -/
def lenOf : Val → Nat
  | .u32 x => x.toNat
  | _ => 0

/-- The first iovec length, skipping empty ones while more than one is left (`fd_read`). -/
def firstLen : List Val → Option Nat
  | [] => none
  | [l] => some (lenOf l)
  | l :: t => if lenOf l = 0 then firstLen t else some (lenOf l)

/-- `nwritten`. -/
def sizeV (n : Nat) : Option Val := some (.u32 (BitVec.ofNat 32 n))

/-- `fd_write` to a file without a cached output stream: open one at the position
(`get_write_stream`). -/
def fdWriteFile (s : ASt) (t : List Desc) (fd d : BitVec 32) (pos : Nat) (inp : Option (BitVec 32))
    (bs : List (BitVec 8)) : AProg :=
  icall .writeVia [.u32 d, .u64 (BitVec.ofNat 64 pos)] fun
  | some [.variant 0 (some (.u32 o))] =>
    writeLoop (setD s t fd (.file d false pos inp (some o))) o
      (okR (setD s t fd (.file d false (pos + bs.length) inp (some o))) (sizeV bs.length))
      (errR (setD s t fd (.file d false pos inp (some o)))) bs
  | some [.variant 1 (some c)] => errR s (codeErrno c)
  | _ => trapR s

/-- `fd_write` of the bytes `bs` to the descriptor `fd` of the table `t`. -/
def fdWriteAt (s : ASt) (t : List Desc) (fd : BitVec 32) (bs : List (BitVec 8)) : AProg :=
  match getD t fd with
  | .stdout o => writeLoop s o (okR s (sizeV bs.length)) (errR s) bs
  | .stderr o => writeLoop s o (okR s (sizeV bs.length)) (errR s) bs
  | .file d false pos inp (some o) =>
    writeLoop s o (okR (setD s t fd (.file d false (pos + bs.length) inp (some o)))
      (sizeV bs.length)) (errR s) bs
  | .file d false pos inp none => fdWriteFile s t fd d pos inp bs
  | _ => errR s P1.eBadf

/-- **`fd_write`**. -/
def fdWrite (s : ASt) : List Val → AProg
  | [.u32 fd, .record bufs] =>
    match firstBuf bufs with
    | none => okR s (sizeV 0)
    | some bs => withTable s fun s t => fdWriteAt s t fd bs
  | _ => errR s P1.eInval

/-- `fd_read` from a file without a cached input stream: open one at the position
(`get_read_stream`). -/
def fdReadFile (s : ASt) (t : List Desc) (fd d : BitVec 32) (pos : Nat) (out : Option (BitVec 32))
    (n : Nat) : AProg :=
  icall .readVia [.u32 d, .u64 (BitVec.ofNat 64 pos)] fun
  | some [.variant 0 (some (.u32 i))] =>
    readOnce (setD s t fd (.file d false pos (some i) out)) i n
      (fun bs => okR (setD s t fd (.file d false (pos + bs.length) (some i) out))
        (some (.record bs)))
      (errR (setD s t fd (.file d false pos (some i) out)))
  | some [.variant 1 (some c)] => errR s (codeErrno c)
  | _ => trapR s

/-- `fd_read` of at most `n` bytes from the descriptor `fd` of the table `t`. -/
def fdReadAt (s : ASt) (t : List Desc) (fd : BitVec 32) (n : Nat) : AProg :=
  match getD t fd with
  | .stdin i => readOnce s i n (fun bs => okR s (some (.record bs))) (errR s)
  | .file d false pos (some i) out =>
    readOnce s i n
      (fun bs => okR (setD s t fd (.file d false (pos + bs.length) (some i) out))
        (some (.record bs))) (errR s)
  | .file d false pos none out => fdReadFile s t fd d pos out n
  | _ => errR s P1.eBadf

/-- **`fd_read`**. -/
def fdRead (s : ASt) : List Val → AProg
  | [.u32 fd, .record lens] =>
    match firstLen lens with
    | none => okR s (some (bytesV []))
    | some n => withTable s fun s t => fdReadAt s t fd n
  | _ => errR s P1.eInval

/-- Drop the 0.2 resources of a descriptor, in field order (`drop(prev)` in `close`). -/
def dropDesc (d : Desc) (k : AProg) : AProg :=
  match d with
  | .closed => k
  | .stdin i => icall .inDrop [.u32 i] fun _ => k
  | .stdout o => icall .outDrop [.u32 o] fun _ => k
  | .stderr o => icall .outDrop [.u32 o] fun _ => k
  | .file d _ _ inp out =>
    let k₂ : AProg := icall .fdDrop [.u32 d] fun _ => k
    let k₁ : AProg := match out with
      | some o => icall .outDrop [.u32 o] fun _ => k₂
      | none => k₂
    match inp with
    | some i => icall .inDrop [.u32 i] fun _ => k₁
    | none => k₁

/-- **`fd_close`** (`Descriptors::close`: the descriptor goes on the free list). -/
def fdClose (s : ASt) : List Val → AProg
  | [.u32 fd] => withTable s fun s t =>
    match getD t fd with
    | .closed => errR s P1.eBadf
    | d => dropDesc d (okR ⟨some (t.set fd.toNat .closed), fd.toNat :: s.free⟩ none)
  | _ => errR s P1.eInval

/-- A preview1 flag bit. -/
def bit (x : BitVec 32) (i : Nat) : Bool := x.getLsbD i

/-- A preview1 flag bit of a 64-bit `rights`. -/
def bit64 (x : BitVec 64) (i : Nat) : Bool := x.getLsbD i

/-- `at_flags_from_lookupflags`: `path-flags { symlink-follow }`. -/
def pathFlagsV (dirflags : BitVec 32) : Val := .record [.bool (bit dirflags 0)]

/-- `o_flags_from_oflags`: `open-flags { create, directory, exclusive, truncate }`. -/
def openFlagsV (oflags : BitVec 32) : Val :=
  .record [.bool (bit oflags 0), .bool (bit oflags 1), .bool (bit oflags 2), .bool (bit oflags 3)]

/-- `descriptor_flags_from_flags`: `descriptor-flags { read, write, file-integrity-sync,
data-integrity-sync, requested-write-sync, mutate-directory }` from the rights
`fd_read` (bit 1), `fd_write` (bit 6) and the `fdflags` `sync` (bit 4), `dsync` (bit 1),
`rsync` (bit 3). -/
def descFlagsV (rights : BitVec 64) (fdflags : BitVec 32) : Val :=
  .record [.bool (bit64 rights 1), .bool (bit64 rights 6), .bool (bit fdflags 4),
    .bool (bit fdflags 1), .bool (bit fdflags 3), .bool false]

/-- The adapter's descriptor-table bound `MAX_DESCRIPTORS`. -/
def maxDescriptors : Nat := 128

/-- Put a new descriptor in the table (`Descriptors::open`): the head of the free list, or a
new entry at the end. -/
def openDesc (s : ASt) (t : List Desc) (d : Desc) : Option (ASt × Nat) :=
  match s.free with
  | x :: rest => some (⟨some (t.set x d), rest⟩, x)
  | [] => if t.length < maxDescriptors then some (⟨some (t ++ [d]), []⟩, t.length) else none

/-- `path_open` after `open-at` returned the descriptor `d'`: ask its type, then put it in the
table. -/
def pathOpened (s : ASt) (t : List Desc) (d' : BitVec 32) : AProg :=
  icall .getType [.u32 d'] fun
  | some [.variant 0 (some (.variant ty none))] =>
    (match openDesc s t (.file d' (ty == 3) 0 none none) with
     | some (s', x) => okR s' (sizeV x)
     | none => icall .fdDrop [.u32 d'] fun _ => errR s P1.eNomem)
  | some [.variant 1 (some c)] => icall .fdDrop [.u32 d'] fun _ => errR s (codeErrno c)
  | _ => trapR s

/-- `path_open` relative to the descriptor `fd` of the table `t` (`get_dir`, then `open-at`). -/
def pathOpenAt (s : ASt) (t : List Desc) (fd : BitVec 32) (args : List Val) : AProg :=
  match getD t fd with
  | .file d true _ _ _ =>
    icall .openAt (.u32 d :: args) fun
    | some [.variant 0 (some (.u32 d'))] => pathOpened s t d'
    | some [.variant 1 (some c)] => errR s (codeErrno c)
    | _ => trapR s
  | .file _ false _ _ _ => errR s P1.eNotdir
  | _ => errR s P1.eBadf

/-- **`path_open`**. -/
def pathOpen (s : ASt) : List Val → AProg
  | [.u32 fd, .u32 dirflags, path, .u32 oflags, .u64 rights, .u64 _, .u32 fdflags] =>
    if bit fdflags 0 ∨ bit fdflags 2 then errR s P1.eNotsup
    else withTable s fun s t => pathOpenAt s t fd
      [pathFlagsV dirflags, path, openFlagsV oflags, descFlagsV rights fdflags]
  | _ => errR s P1.eInval

/-- A wall-clock `datetime` in nanoseconds, or `errno::overflow`. -/
def wallNs (s : ASt) (sec : BitVec 64) (ns : BitVec 32) : AProg :=
  if sec.toNat * 1000000000 + ns.toNat < 2 ^ 64 then
    okR s (some (.u64 (BitVec.ofNat 64 (sec.toNat * 1000000000 + ns.toNat))))
  else errR s P1.eOverflow

/-- **`clock_time_get`** (the precision is ignored). -/
def clockTimeGet (s : ASt) : List Val → AProg
  | [.u32 id, .u64 _] =>
    if id = P1.clockMonotonic then
      icall .now [] fun
      | some [.u64 x] => okR s (some (.u64 x))
      | _ => trapR s
    else if id = P1.clockRealtime then
      icall .wallNow [] fun
      | some [.record [.u64 sec, .u32 ns]] => wallNs s sec ns
      | _ => trapR s
    else errR s P1.eBadf
  | _ => errR s P1.eInval

/-- **`clock_res_get`**. -/
def clockResGet (s : ASt) : List Val → AProg
  | [.u32 id] =>
    if id = P1.clockMonotonic then
      icall .monoRes [] fun
      | some [.u64 x] => okR s (some (.u64 x))
      | _ => trapR s
    else if id = P1.clockRealtime then
      icall .wallRes [] fun
      | some [.record [.u64 sec, .u32 ns]] => wallNs s sec ns
      | _ => trapR s
    else errR s P1.eBadf
  | _ => errR s P1.eInval

/-- **`random_get`**: the bytes of `get-random-bytes`, written in place (at most `len`). -/
def randomGet (s : ASt) : List Val → AProg
  | [.u32 len] =>
    icall .rand [.u64 (BitVec.ofNat 64 len.toNat)] fun
    | some [.record bs] => if allU8 bs ∧ bs.length ≤ len.toNat then okR s (some (.record bs))
      else trapR s
    | _ => trapR s
  | _ => errR s P1.eInval

/-- The characters of an encoded string. -/
def charsOf : Val → List Char
  | .record vs => vs.filterMap fun | .char c => some c | _ => none
  | _ => []

/-- The UTF-8 size of an encoded string with its terminating NUL. -/
def cSize (v : Val) : Nat := ((charsOf v).map Char.utf8Size).sum + 1

/-- `key=value`. -/
def envStr : Val → Val
  | .record [k, v] => .record ((charsOf k ++ ['='] ++ charsOf v).map .char)
  | _ => .record []

/-- `(count, bytes)`. -/
def sizesV (ss : List Val) : Option Val :=
  some (.record [.u32 (BitVec.ofNat 32 ss.length), .u32 (BitVec.ofNat 32 (ss.map cSize).sum)])

/-- **`args_get`** (`sizes = false`) and **`args_sizes_get`** (`sizes = true`). -/
def argsGet (s : ASt) (sizes : Bool) : AProg :=
  icall .getArgs [] fun
  | some [.record ss] =>
    if ss.all P1.isStrV then okR s (if sizes then sizesV ss else some (.record ss)) else trapR s
  | _ => trapR s

/-- **`environ_get`** (`sizes = false`) and **`environ_sizes_get`** (`sizes = true`). -/
def environGet (s : ASt) (sizes : Bool) : AProg :=
  icall .getEnv [] fun
  | some [.record ps] =>
    if ps.all isEnvPair then
      okR s (if sizes then sizesV (ps.map envStr) else some (.record (ps.map envStr)))
    else trapR s
  | _ => trapR s

/-- **`proc_exit`**: `exit(ok)` for status `0`, `exit(err)` otherwise; it does not return. -/
def procExit (s : ASt) : List Val → AProg
  | .u32 code :: _ =>
    icall .exit [.variant (if code = 0 then 0 else 1) none] fun _ => trapR s
  | _ => trapR s

/-- **The adapter**: the preview1 functions of the slice; every other one answers
`errno::nosys`. -/
def body : SBody ASt imports P1.imports := fun s q =>
  let n := q.1.1.fn
  let a := q.2
  if n = "fd_write" then fdWrite s a
  else if n = "fd_read" then fdRead s a
  else if n = "fd_close" then fdClose s a
  else if n = "path_open" then pathOpen s a
  else if n = "clock_time_get" then clockTimeGet s a
  else if n = "clock_res_get" then clockResGet s a
  else if n = "random_get" then randomGet s a
  else if n = "args_get" then argsGet s false
  else if n = "args_sizes_get" then argsGet s true
  else if n = "environ_get" then environGet s false
  else if n = "environ_sizes_get" then environGet s true
  else if n = "sched_yield" then okR s none
  else if n = "proc_exit" then procExit s a
  else errR s P1.eNosys

/-- **The adapter component** (preview1 over 0.2). -/
def adapter : Strategy (nsig imports) (nsig P1.imports) := ofSBody body ASt.init

end Silmaril.Wasi.Versions.Adapter
