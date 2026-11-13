module

public import Silmaril.Machine.X86.BlockCert.Store.Defs
public import Silmaril.Machine.X86.Sep.SysV.Defs

/-!
# Byte-loop stencils: `Copy`, `Fill`, `Scan` (IR-C)

A byte loop walks a byte range `[a, a + n)` one (or a few) bytes per iteration. This module
fixes, once, what such a function promises and how its loop invariant evolves; the proofs
that turn one compiled loop into a System V separation-logic spec are in
`Stencils/ByteLoop/Thms.lean`. A **stencil instance** (`LibMini`) then only proves the blocks
of its listing against the stencil's state-level contract.

Each stencil has three layers.

* **The separation-logic spec** (`copySpec`, `fillSpec`, `scanSpec`, all `FnSpec`s with no
  stack): `memcpy`-like copy of `n` readable bytes into `n` owned bytes, returning the
  destination; `memset`-like fill of `n` owned bytes with the low byte of the second argument,
  returning the destination; `strlen`-like scan of a readable NUL-terminated string without
  inner NULs, returning its length. The footprint is the destination block (copy, fill) or
  nothing (scan): everything else the caller owns is framed.
* **The state-level contract** (`copyContract`, `fillContract`, `scanContract`: a
  `FnContract.Spec` on machine states, arguments read from `rdi, rsi, rdx`). Its entry
  condition lists exactly the facts a loop proof needs (permissions, backing, the
  destination apart from the source, the code and the return slot); its post states the
  result in terms of the entry memory. The stencil theorems (`copy_sat`, …) read these facts
  off the separation-logic precondition, so an instance never touches fragments.
* **The loop invariant algebra**: `Prefix m0 mem d i val` (the memory is the entry memory
  with the `i` bytes from `d` set to `val 0, …, val (i-1)`), its one-byte store step `set1`,
  and the reading lemmas (a load from outside the written prefix sees the entry memory, the
  code image and the return slot stay put). `Copy` uses `val j = m0[s + j]`, `Fill` uses
  `val j = c`; `Scan` writes nothing and uses `CStr` (`k` non-NUL bytes then a NUL).
-/

@[expose] public section

namespace Silmaril.Machine.X86.Stencils.ByteLoop

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.X86.Sep

/-! ## Memory facts -/

/-- `n` bytes from `a` are below `2 ^ 64` and writable. -/
def Writable (mem : Memory) (a n : Nat) : Prop :=
  ∀ i < n, a + i < addressLimit ∧ mem.permits .write (a + i) = true

/-- `n` bytes from `a` are below `2 ^ 64`, readable and backed. -/
def Readable (mem : Memory) (a n : Nat) : Prop :=
  ∀ i < n, a + i < addressLimit ∧ mem.permits .read (a + i) = true ∧
    (mem.bytes.get? (a + i)).isSome = true

/-- The intervals `[a, a + n)` and `[b, b + k)` do not overlap. -/
def Apart (a n b k : Nat) : Prop := n = 0 ∨ k = 0 ∨ a + n ≤ b ∨ b + k ≤ a

/-- A NUL-terminated string of length `k` at `s`: `k + 1` readable bytes, the first `k`
non-zero and the last zero. -/
def CStr (mem : Memory) (s k : Nat) : Prop :=
  Readable mem s (k + 1) ∧ (∀ j < k, mem.bytes.get? (s + j) ≠ some 0) ∧
    mem.bytes.get? (s + k) = some 0

/-- One byte stored at `a` (what a successful one-byte `storeN` produces). -/
def set1 (mem : Memory) (a : Nat) (b : Byte) : Memory :=
  { mem with bytes := mem.bytes.insert a b }

/-- **The loop invariant of a writing byte loop**: `mem` is `m0` with the `i` bytes from `d`
set to `val 0, …, val (i - 1)`, the mappings unchanged. -/
structure Prefix (m0 mem : Memory) (d i : Nat) (val : Nat → Option Byte) : Prop where
  regions : mem.regions = m0.regions
  inside : ∀ j < i, mem.bytes.get? (d + j) = val j
  outside : ∀ a, a < d ∨ d + i ≤ a → mem.bytes.get? a = m0.bytes.get? a

/-- The System V frame of a leaf loop, from the entry state `m0` to the current state `m`:
the entry obligations held, and `rsp` and the callee-saved registers are as at entry. Unlike
`BlockCert.Frame`, the memory may have changed. -/
structure LoopFrame (m0 m : MState) : Prop where
  abi : FnContract.AbiEntry m0.core m0.memory
  rsp : m.core.read .rsp = m0.core.read .rsp
  saved : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, m.core.read r = m0.core.read r

/-! ## Register arguments -/

/-- The first three integer arguments, as naturals. -/
def arg0 (m : MState) : Nat := (m.core.read .rdi).toNat
def arg1 (m : MState) : Nat := (m.core.read .rsi).toNat
def arg2 (m : MState) : Nat := (m.core.read .rdx).toNat

/-- The entry stack pointer, as a natural. -/
def sp (m : MState) : Nat := (m.core.read .rsp).toNat

/-! ## State-level contracts -/

/-- **`Copy`** at `entry` in `code`: `n = rdx` bytes from `s = rsi` to `d = rdi`, returning
`d`. -/
def copyContract (code : List Byte) (entry : Word) : FnContract.Spec MState where
  entry m := m.core.rip = entry ∧ Loaded m.memory entry code ∧
    Writable m.memory (arg0 m) (arg2 m) ∧ Readable m.memory (arg1 m) (arg2 m) ∧
    Apart (arg0 m) (arg2 m) (arg1 m) (arg2 m) ∧
    Apart (arg0 m) (arg2 m) entry.toNat code.length ∧ Apart (arg0 m) (arg2 m) (sp m) 8
  footprint m a := arg0 m ≤ a ∧ a < arg0 m + arg2 m
  post m t := t.core.read .rax = m.core.read .rdi ∧
    m.memory.WritesWithin t.memory (fun a => arg0 m ≤ a ∧ a < arg0 m + arg2 m) ∧
    ∀ i < arg2 m, t.memory.bytes.get? (arg0 m + i) = m.memory.bytes.get? (arg1 m + i)

/-- **`Fill`** at `entry` in `code`: `n = rdx` bytes from `d = rdi` set to the low byte of
`rsi`, returning `d`. -/
def fillContract (code : List Byte) (entry : Word) : FnContract.Spec MState where
  entry m := m.core.rip = entry ∧ Loaded m.memory entry code ∧
    Writable m.memory (arg0 m) (arg2 m) ∧
    Apart (arg0 m) (arg2 m) entry.toNat code.length ∧ Apart (arg0 m) (arg2 m) (sp m) 8
  footprint m a := arg0 m ≤ a ∧ a < arg0 m + arg2 m
  post m t := t.core.read .rax = m.core.read .rdi ∧
    m.memory.WritesWithin t.memory (fun a => arg0 m ≤ a ∧ a < arg0 m + arg2 m) ∧
    ∀ i < arg2 m, t.memory.bytes.get? (arg0 m + i) = some ((m.core.read .rsi).setWidth 8)

/-- **`Scan`** at `entry` in `code`: the length of the NUL-terminated string at `s = rdi`. -/
def scanContract (code : List Byte) (entry : Word) : FnContract.Spec MState where
  entry m := m.core.rip = entry ∧ Loaded m.memory entry code ∧ ∃ k, CStr m.memory (arg0 m) k
  footprint _ _ := False
  post m t := (∀ k, CStr m.memory (arg0 m) k → t.core.read .rax = BitVec.ofNat 64 k) ∧
    m.memory.WritesWithin t.memory (fun _ => False)

/-! ## Separation-logic specs -/

/-- Logical arguments of `Copy`: destination, source, source bytes, old destination bytes. -/
structure CopyArg where
  d : Word
  s : Word
  src : List Byte
  old : List Byte

/-- **The `Copy` spec** (`memcpy`; `restrict`: the two blocks are separate). -/
def copySpec : FnSpec where
  Arg := CopyArg
  args x := [x.d, x.s, BitVec.ofNat 64 x.src.length]
  stack := 0
  pre x := ⌜x.old.length = x.src.length ∧ x.src.length < 2 ^ 64⌝ ∗
    (bytesPt x.d.toNat x.old ∗ bytesPtRO x.s.toNat x.src)
  post x v := ⌜v = x.d⌝ ∗ (bytesPt x.d.toNat x.src ∗ bytesPtRO x.s.toNat x.src)

/-- Logical arguments of `Fill`: destination, fill value (its low byte is stored), old bytes. -/
structure FillArg where
  d : Word
  c : Word
  old : List Byte

/-- **The `Fill` spec** (`memset`). -/
def fillSpec : FnSpec where
  Arg := FillArg
  args x := [x.d, x.c, BitVec.ofNat 64 x.old.length]
  stack := 0
  pre x := ⌜x.old.length < 2 ^ 64⌝ ∗ bytesPt x.d.toNat x.old
  post x v := ⌜v = x.d⌝ ∗ bytesPt x.d.toNat (List.replicate x.old.length (x.c.setWidth 8))

/-- Logical arguments of `Scan`: the string's address and its bytes before the NUL. -/
structure ScanArg where
  s : Word
  bs : List Byte

/-- **The `Scan` spec** (`strlen`): read-only. -/
def scanSpec : FnSpec where
  Arg := ScanArg
  args x := [x.s]
  stack := 0
  pre x := ⌜(0 : Byte) ∉ x.bs⌝ ∗ bytesPtRO x.s.toNat (x.bs ++ [0])
  post x v := ⌜v = BitVec.ofNat 64 x.bs.length⌝ ∗ bytesPtRO x.s.toNat (x.bs ++ [0])

end Silmaril.Machine.X86.Stencils.ByteLoop
