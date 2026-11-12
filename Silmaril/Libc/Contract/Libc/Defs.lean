module

public import Silmaril.Libc.Contract.Sig.Defs
public import Silmaril.Libc.Formats.Defs

/-!
# The C library's API, and the catalogue of its signatures

The exported functions the instances speak about (`LFn`), with abstract argument and result types
(`LFn.Arg`, `LFn.Ret`): pointers and sizes as `Nat`, bytes as `BitVec 8`, a C string as its bytes
before the terminating zero, a `printf` argument as a value (`PVal`), a `scanf` result as the
count and the assigned values (`SVal` of `Silmaril.Libc.Formats`). This is the API `libcApi` of the
institution; the System V reading of the same calls (registers, memory) is a process-level
matter, not stated here.

| function | `Arg` | `Ret` |
|---|---|---|
| `malloc` | size | pointer |
| `free` | pointer | — |
| `calloc` | count, size | pointer |
| `realloc` | pointer, size | pointer |
| `aligned_alloc` | alignment, size | pointer |
| `posix_memalign` | alignment, size | error code, pointer (`*memptr`) |
| `malloc_usable_size` | pointer | size |
| `putchar` | byte | `int` |
| `puts` | string | `int` |
| `printf` | format, values | `int` |
| `scanf` | format | `int`, assigned values |
| `getchar` | — | `int` |

**The catalogue** lists the functions of each named signature (`allocList k`, `putsList`,
`outList`, `inList`, `stdioList`); the signatures of the instances are built from these lists
(`LFn.setOf`), and the contract diagram is generated from them
(`Silmaril.Libc.Contract.Diagram`).
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open Silmaril.Libc.Formats (SVal)

/-- A byte. -/
abbrev Byte := BitVec 8

/-- **A `printf` argument**, as a value: an integer (`%d %ld %lld %u %x`), a string (`%s`), a
character (`%c`). -/
inductive PVal where
  | int (v : Int)
  | str (s : List Byte)
  | chr (c : Byte)

/-- **The exported functions** of the C library the instances cover. -/
inductive LFn where
  | malloc | free | calloc | realloc | aligned_alloc | posix_memalign | malloc_usable_size
  | putchar | puts | printf | scanf | getchar
  deriving DecidableEq, Repr

namespace LFn

/-- The arguments of a call. -/
def Arg : LFn → Type
  | malloc => Nat
  | free => Nat
  | calloc => Nat × Nat
  | realloc => Nat × Nat
  | aligned_alloc => Nat × Nat
  | posix_memalign => Nat × Nat
  | malloc_usable_size => Nat
  | putchar => Byte
  | puts => List Byte
  | printf => List Byte × List PVal
  | scanf => List Byte
  | getchar => Unit

/-- The result of a call. -/
def Ret : LFn → Type
  | malloc => Nat
  | free => Unit
  | calloc => Nat
  | realloc => Nat
  | aligned_alloc => Nat
  | posix_memalign => Nat × Nat
  | malloc_usable_size => Nat
  | putchar => Int
  | puts => Int
  | printf => Int
  | scanf => Int × List SVal
  | getchar => Int

/-- The C name. -/
def name : LFn → String
  | malloc => "malloc"
  | free => "free"
  | calloc => "calloc"
  | realloc => "realloc"
  | aligned_alloc => "aligned_alloc"
  | posix_memalign => "posix_memalign"
  | malloc_usable_size => "malloc_usable_size"
  | putchar => "putchar"
  | puts => "puts"
  | printf => "printf"
  | scanf => "scanf"
  | getchar => "getchar"

/-- Every function, in order. -/
def all : List LFn :=
  [malloc, free, calloc, realloc, aligned_alloc, posix_memalign, malloc_usable_size,
    putchar, puts, printf, scanf, getchar]

/-- The allocator level of a function: `0` for a function that is not the allocator's. -/
def allocLevel : LFn → Nat
  | malloc | free => 1
  | calloc => 2
  | realloc => 3
  | aligned_alloc | posix_memalign | malloc_usable_size => 4
  | _ => 0

/-- The set of the functions of a list. -/
def setOf (l : List LFn) : Set LFn := {f | f ∈ l}

end LFn

/-- **The C library's API.** -/
def libcApi : Api := ⟨LFn, LFn.Arg, LFn.Ret⟩

/-! ## The catalogue -/

/-- **The allocator at level `k`**: the functions of allocator level `1 … k`
(`1`: `malloc`, `free`; `2`: `+calloc`; `3`: `+realloc`; `4`: `+aligned_alloc`, `posix_memalign`,
`malloc_usable_size`). -/
def allocList (k : Nat) : List LFn :=
  LFn.all.filter fun f => 0 < f.allocLevel && f.allocLevel ≤ k

/-- `putchar`, `puts`. -/
def putsList : List LFn := [.putchar, .puts]

/-- Output: `putchar`, `puts`, `printf`. -/
def outList : List LFn := [.putchar, .puts, .printf]

/-- Input: `getchar`, `scanf`. -/
def inList : List LFn := [.getchar, .scanf]

/-- All of `stdio` covered here. -/
def stdioList : List LFn := outList ++ inList

end Silmaril.Libc.Contracts
