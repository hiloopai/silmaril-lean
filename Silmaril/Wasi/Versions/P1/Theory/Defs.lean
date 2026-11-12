module

public import Silmaril.Wasi.Versions.P1.Gen.Defs
public import Silmaril.Wasi.Theory.Defs

@[expose] public section

/-!
# WASI preview1 (`wasi_snapshot_preview1`) as a theory

WASI preview1 lives *below* the Component Model: a preview1 program is a core Wasm module that
imports the functions of the module `wasi_snapshot_preview1` (`specs/wasi/preview1/
wasi_snapshot_preview1.witx`, generated into `Silmaril.Wasi.Versions.P1.Gen`) and exports
`_start` (a command) and its `memory`. This module makes preview1 a theory in the WASI
institution of `Silmaril.Wasi.World`.

## The signature

* `fnNames`: the 46 functions of the witx file, in order; `imports` the corresponding
  `FnName`s with interface `wasi_snapshot_preview1`; `world` a command module (imports, the
  export `_start`).
* `coreParams`, `coreResults`: the **core** signature of each import, computed from the witx
  parameter types by the witx lowering (`i32`/`i64` scalars, `(ptr, len)` pairs for strings and
  lists, one `i32` out-pointer per result component, an `i32` errno). For example `fd_write` is
  `(i32 i32 i32 i32) → i32` and `path_open` is `(i32 i32 i32 i32 i32 i64 i64 i32 i32) → i32`
  (`Silmaril.Wasi.Versions.P1.Theory.Thms`).

## Lifted events

Events of `Silmaril.Wasi.World` carry component values, so a preview1 call is read at the witx
*interface* level: pointer arguments are replaced by the data the host reads from the caller's
memory, out-pointers are dropped and the data the host writes is part of the answer.

| function | lifted arguments | lifted `ok` payload |
|---|---|---|
| `fd_write` | `u32 fd`, `record [list<u8>…]` (the ciovecs) | `u32 nwritten` |
| `fd_read` | `u32 fd`, `record [u32 len…]` (the iovec lengths) | `list<u8>` (the bytes read) |
| `clock_time_get` | `u32 id`, `u64 precision` | `u64 timestamp` |
| `clock_res_get` | `u32 id` | `u64 resolution` |
| `random_get` | `u32 len` | `list<u8>` |
| `args_get`, `environ_get` | — | `record [string…]` |
| `args_sizes_get`, `environ_sizes_get` | — | `record [u32 count, u32 bytes]` |
| `path_open` | `u32 fd`, `u32 dirflags`, `string path`, `u32 oflags`, `u64 rights`, `u64 rights`, `u32 fdflags` | `u32 fd` |
| `fd_close`, `sched_yield` | `u32 fd` / — | none |
| `proc_exit` | `u32 code` | (no answer: `none`) |

Other functions take their core scalar arguments (`u32` for `i32`, `u64` for `i64`). Every
answer is `ok(payload)` (`variant 0`) or `error(u16 errno)` (`variant 1`), and `proc_exit`'s only
answer is `none` (it does not return).

## The theory `th`: loose sentences on the host's answers

* `typed`: every answer has the witx result type of its function (for the functions in the table
  above) and is never a trap, except `proc_exit`, whose only answer is `none`; error codes are
  nonzero `errno` tags.
* `bounds`: `fd_write` reports at most the bytes it was given; `fd_read` returns at most the room
  of the iovecs; `random_get(len)` returns exactly `len` bytes.
* `clock`: the answers of `clock_time_get(monotonic)` never decrease.
* `fds`: descriptors: `0`, `1`, `2` are open; an operation on a descriptor that succeeds marks it
  open; `fd_close` and `fd_renumber` close one; `path_open` returns a descriptor that is not
  open; and no operation succeeds on a closed descriptor. `fd_write`/`fd_read` with an empty
  iovec list are exempt and say nothing about the descriptor: the official adapter answers them
  `ok(0)` without looking at the descriptor (`fdsStrict`, without the exemption, is refuted for
  it in `Silmaril.Wasi.Versions.Adapter`).

`th = typed × clock × bounds × fds`. Loose and concrete hosts of `th` are those of
`Silmaril.Wasi.Host` (`loose th`, and the composites of `Silmaril.Wasi.Versions.Adapter`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P1

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## The signature -/

/-- The import module of preview1. -/
def module : String := "wasi_snapshot_preview1"

/-- The functions of `wasi_snapshot_preview1.witx`. -/
def fnNames : List String := Gen.fns.map (·.1)

/-- A preview1 function. -/
def fn (n : String) : FnName := ⟨module, n⟩

/-- The preview1 imports. -/
def imports : Set FnName := {f | f.iface = module ∧ f.fn ∈ fnNames}

/-- The export `_start` of a command module. -/
def start : FnName := ⟨"", "_start"⟩

/-- **The preview1 world** of a command module. -/
def world : World := ⟨imports, {start}⟩

/-- A core value type. -/
inductive CoreTy where
  | i32
  | i64
  deriving DecidableEq, Repr

/-- The core lowering of a witx parameter. -/
def lowCore : Gen.Low → List CoreTy
  | .i32 => [.i32]
  | .i64 => [.i64]
  | .ptrLen => [.i32, .i32]
  | .ptr => [.i32]

/-- The witx entry of a function. -/
def entry (n : String) : Option (String × List (String × Gen.Low) × Nat × Bool) :=
  Gen.fns.find? (·.1 == n)

/-- The core parameters of a function: its lowered parameters, then its out-pointers. -/
def coreParams (n : String) : List CoreTy :=
  match entry n with
  | some (_, ps, outs, _) => ps.flatMap (fun p => lowCore p.2) ++ List.replicate outs .i32
  | none => []

/-- The core results of a function: an `errno`, or nothing (`proc_exit`). -/
def coreResults (n : String) : List CoreTy :=
  match entry n with
  | some (_, _, _, true) => [.i32]
  | _ => []

/-- The functions whose first parameter is a descriptor `fd`. -/
def fdFns : List String := (Gen.fns.filter fun e => (e.2.1.head?.map (·.1)) == some "fd").map (·.1)

/-! ## Errors and answers -/

/-- The tag of an `errno` name. -/
def errno (n : String) : Nat := Gen.errnoNames.idxOf n

/-- `errno::badf`. -/
abbrev eBadf : Nat := 8
/-- `errno::inval`. -/
abbrev eInval : Nat := 28
/-- `errno::io`. -/
abbrev eIo : Nat := 29
/-- `errno::nomem`. -/
abbrev eNomem : Nat := 48
/-- `errno::nosys`. -/
abbrev eNosys : Nat := 52
/-- `errno::notdir`. -/
abbrev eNotdir : Nat := 54
/-- `errno::notsup`. -/
abbrev eNotsup : Nat := 58
/-- `errno::overflow`. -/
abbrev eOverflow : Nat := 61

/-- `clockid::realtime`. -/
abbrev clockRealtime : BitVec 32 := 0
/-- `clockid::monotonic`. -/
abbrev clockMonotonic : BitVec 32 := 1

/-- An `ok` answer. -/
def okAns (v : Option Val) : Option (List Val) := some [okV v]

/-- An `error(errno)` answer. -/
def errAns (e : Nat) : Option (List Val) := some [errV (some (.u16 (BitVec.ofNat 16 e)))]

/-! ## Typing -/

/-- A `u32` payload. -/
def isU32 : Option Val → Bool
  | some (.u32 _) => true
  | _ => false

/-- A `u64` payload. -/
def isU64 : Option Val → Bool
  | some (.u64 _) => true
  | _ => false

/-- No payload. -/
def isUnit : Option Val → Bool
  | none => true
  | _ => false

/-- An encoded `list<u8>`. -/
def isBytesV : Val → Bool
  | .record vs => vs.all fun | .u8 _ => true | _ => false
  | _ => false

/-- A `list<u8>` payload. -/
def isBytes : Option Val → Bool
  | some v => isBytesV v
  | none => false

/-- An encoded `string`. -/
def isStrV : Val → Bool
  | .record vs => vs.all fun | .char _ => true | _ => false
  | _ => false

/-- A list of strings. -/
def isStrs : Option Val → Bool
  | some (.record vs) => vs.all isStrV
  | _ => false

/-- A pair of sizes. -/
def isSizes : Option Val → Bool
  | some (.record [.u32 _, .u32 _]) => true
  | _ => false

/-- The `ok` payload type of a function (any payload outside the lifted slice). -/
def okShape : String → Option Val → Bool
  | "fd_write" => isU32
  | "fd_read" => isBytes
  | "clock_time_get" => isU64
  | "clock_res_get" => isU64
  | "random_get" => isBytes
  | "args_get" => isStrs
  | "environ_get" => isStrs
  | "args_sizes_get" => isSizes
  | "environ_sizes_get" => isSizes
  | "path_open" => isU32
  | "fd_close" => isUnit
  | "sched_yield" => isUnit
  | _ => fun _ => true

/-- An `error(errno)` answer with a nonzero `errno` tag. -/
def isErrno : Option (List Val) → Bool
  | some [.variant 1 (some (.u16 e))] => e != 0 && decide (e.toNat < Gen.errnoNames.length)
  | _ => false

/-- A well-typed answer of the function `n`. -/
def ansOk (n : String) (r : Option (List Val)) : Bool :=
  if n = "proc_exit" then r.isNone
  else isErrno r || (match r with | some [.variant 0 v] => okShape n v | _ => false)

/-- The typing of a preview1 answer. -/
def typedOk : WEv → Bool
  | .imp f _ r => if f.iface = module ∧ f.fn ∈ fnNames then ansOk f.fn r else true
  | _ => true

/-- **Typing**: answers have their witx types; only `proc_exit` does not return. -/
def typed : Protocol Unit WEv := pointwise typedOk

/-! ## Bounds -/

/-- The bytes of a ciovec list. -/
def bufTotal : Val → Nat
  | .record bs => (bs.map fun b => (bytesOf b).length).sum
  | _ => 0

/-- The room of an iovec list. -/
def lenTotal : Val → Nat
  | .record ls => (ls.map fun | .u32 x => x.toNat | _ => 0).sum
  | _ => 0

/-- The bounds of an answer. -/
def boundsOk : WEv → Bool
  | .imp f a r =>
    if f = fn "fd_write" then
      (match a, r with
       | _ :: bufs :: _, some [.variant 0 (some (.u32 n))] => decide (n.toNat ≤ bufTotal bufs)
       | _, _ => true)
    else if f = fn "fd_read" then
      (match a, r with
       | _ :: lens :: _, some [.variant 0 (some v)] => decide ((bytesOf v).length ≤ lenTotal lens)
       | _, _ => true)
    else if f = fn "random_get" then
      (match a, r with
       | .u32 len :: _, some [.variant 0 (some v)] => decide ((bytesOf v).length = len.toNat)
       | _, _ => true)
    else true
  | _ => true

/-- **Bounds** of reads, writes and random bytes. -/
def bounds : Protocol Unit WEv := pointwise boundsOk

/-! ## The monotonic clock -/

/-- One step of the monotonic clock: the last instant answered. -/
def clockStep (last : Option (BitVec 64)) : WEv → Option (Option (BitVec 64))
  | .imp f (.u32 id :: _) (some [.variant 0 (some (.u64 x))]) =>
    if f = fn "clock_time_get" ∧ id = clockMonotonic then
      (if last.all fun l => decide (l ≤ x) then some (some x) else none)
    else some last
  | _ => some last

/-- **The monotonic clock**: `clock_time_get(monotonic)` never decreases. -/
def clock : Protocol (Option (BitVec 64)) WEv := ⟨none, clockStep⟩

/-! ## Descriptors -/

/-- The descriptors known to be open, and those closed (and not reopened). -/
structure FdSt where
  /-- Open descriptors. -/
  live : List (BitVec 32)
  /-- Closed descriptors. -/
  dead : List (BitVec 32)

/-- An empty iovec list (`fd_write`/`fd_read` answer it without a descriptor lookup). -/
def emptyIovs : List Val → Bool
  | _ :: .record [] :: _ => true
  | _ => false

/-- The descriptors after a successful operation of `n` on `fd` (with the other arguments `a`
and the payload `v`); `none` rejects the answer. -/
def fdOk (q : FdSt) (n : String) (fd : BitVec 32) (a : List Val) (v : Option Val) :
    Option FdSt :=
  let q1 : FdSt := if fd ∈ q.live then q else ⟨fd :: q.live, q.dead⟩
  if n = "fd_close" then some ⟨q1.live.filter (· != fd), fd :: q1.dead⟩
  else if n = "path_open" then
    (match v with
     | some (.u32 fd') => if fd' ∈ q1.live then none
       else some ⟨fd' :: q1.live, q1.dead.filter (· != fd')⟩
     | _ => some q1)
  else if n = "fd_renumber" then
    (match a with
     | .u32 dst :: _ =>
       if dst = fd then some q1
       else some ⟨dst :: q1.live.filter (fun x => x != fd && x != dst),
         fd :: q1.dead.filter (· != dst)⟩
     | _ => some q1)
  else some q1

/-- One step of the descriptor theory. -/
def fdStep (q : FdSt) : WEv → Option FdSt
  | .imp f (.u32 fd :: a) (some [.variant 0 v]) =>
    if f.iface = module ∧ f.fn ∈ fdFns then
      if (f.fn = "fd_write" ∨ f.fn = "fd_read") ∧ emptyIovs (.u32 fd :: a) = true then some q
      else if fd ∈ q.dead then none
      else fdOk q f.fn fd a v
    else some q
  | _ => some q

/-- **Descriptors**: no success on a closed descriptor, `path_open` returns a fresh one. -/
def fds : Protocol FdSt WEv := ⟨⟨[0, 1, 2], []⟩, fdStep⟩

/-- The same without the exemption of empty iovec lists. -/
def fdStepStrict (q : FdSt) : WEv → Option FdSt
  | .imp f (.u32 fd :: a) (some [.variant 0 v]) =>
    if f.iface = module ∧ f.fn ∈ fdFns then
      if fd ∈ q.dead then none else fdOk q f.fn fd a v
    else some q
  | _ => some q

/-- **The strict descriptor theory**: no success at all on a closed descriptor. -/
def fdsStrict : Protocol FdSt WEv := ⟨⟨[0, 1, 2], []⟩, fdStepStrict⟩

/-! ## The theory -/

/-- **The preview1 theory.** -/
def th : Protocol (Unit × Option (BitVec 64) × Unit × FdSt) WEv :=
  typed.prod (clock.prod (bounds.prod fds))

end Silmaril.Wasi.Versions.P1
