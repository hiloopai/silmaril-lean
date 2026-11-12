module

public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Live
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.Raw.Libc.X86Alloc.Whole
public import Silmaril.Raw.Libc.X86Alloc.Loop
public import Silmaril.Raw.Libc.X86Alloc.HdrSeg
public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree
public import Silmaril.Libc.X86Alloc.Ladder.Coalesce.Defs

/-!
# Proofs: rung 05 (first-fit) `malloc` — the listing and the loop invariant

The walk's loop head is `0x401352` (offset 34). `Inv need sp ret fl0 x` is the state there for the
index `x = (passed, b, rest)`: `rax` at the block `b` under inspection, `rsi` at the final link
slot of the walked segment `passed` (all too small for `need`), the free list unchanged as a whole
(`passed ++ b :: rest = fl0`), and the memory split into the open segment `plist freelist passed
b.addr` and the tail `hdrSeg (b :: rest) b.addr`. The measure is `rest.length`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.FirstFit
open Silmaril.Raw.Libc.X86Alloc.Frame

/-- `malloc`'s bytes: the first 128 bytes of the code region, shared verbatim by rungs 05 and 06
(`FirstFit.code.take 128 = Coalesce.code.take 128`). -/
def mcode : List Byte := code.take 128

theorem mcode_coalesce : Silmaril.Libc.X86Alloc.Ladder.Coalesce.code.take 128 = mcode := by
  decide +kernel

/-! ## The listing of `malloc`, decoded once -/

theorem d0 : Silmaril.X86.Ext.decode ((mcode.drop 0).take 7) = some (.aluI .q .cmp (.reg .rdi) 0x1000, 7) := by
  decide +kernel
theorem d7 : Silmaril.X86.Ext.decode ((mcode.drop 7).take 2) = some (.jcc8 .a 0x57, 2) := by
  decide +kernel
theorem d9 : Silmaril.X86.Ext.decode ((mcode.drop 9).take 7) = some (.load .q .rax (ripMem 0x1d60), 7) := by
  decide +kernel
theorem d16 : Silmaril.X86.Ext.decode ((mcode.drop 16).take 4) = some (.aluI8 .q .add (.reg .rdi) 0x0f, 4) := by
  decide +kernel
theorem d20 : Silmaril.X86.Ext.decode ((mcode.drop 20).take 4) = some (.aluI8 .q .and (.reg .rdi) 0xf0, 4) := by
  decide +kernel
theorem d24 : Silmaril.X86.Ext.decode ((mcode.drop 24).take 3) = some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem d27 : Silmaril.X86.Ext.decode ((mcode.drop 27).take 2) = some (.jcc8 .e 0x45, 2) := by
  decide +kernel
theorem d29 : Silmaril.X86.Ext.decode ((mcode.drop 29).take 5) = some (.movI32 .rsi 0x4030a0, 5) := by
  decide +kernel
theorem d34 : Silmaril.X86.Ext.decode ((mcode.drop 34).take 3) = some (.load .q .rdx (Silmaril.X86.Sep.Insn.memAt .rax 0), 3) := by
  decide +kernel
theorem d37 : Silmaril.X86.Ext.decode ((mcode.drop 37).take 4) = some (.load .q .rcx (Silmaril.X86.Sep.Insn.memAt .rax 8), 4) := by
  decide +kernel
theorem d41 : Silmaril.X86.Ext.decode ((mcode.drop 41).take 3) = some (.alu .q .cmp (.reg .rdx) .rdi, 3) := by
  decide +kernel
theorem d44 : Silmaril.X86.Ext.decode ((mcode.drop 44).take 2) = some (.jcc8 .b 0x3a, 2) := by
  decide +kernel
theorem d46 : Silmaril.X86.Ext.decode ((mcode.drop 46).take 4) = some (.lea .q .r8 (Silmaril.X86.Sep.Insn.memAt .rdi 0x20), 4) := by
  decide +kernel
theorem d50 : Silmaril.X86.Ext.decode ((mcode.drop 50).take 3) = some (.alu .q .cmp (.reg .rdx) .r8, 3) := by
  decide +kernel
theorem d53 : Silmaril.X86.Ext.decode ((mcode.drop 53).take 2) = some (.jcc8 .b 0x19, 2) := by
  decide +kernel
theorem d55 : Silmaril.X86.Ext.decode ((mcode.drop 55).take 3) = some (.alu .q .sub (.reg .rdx) .rdi, 3) := by
  decide +kernel
theorem d63 : Silmaril.X86.Ext.decode ((mcode.drop 63).take 4) = some (.aluI8 .q .sub (.reg .rdx) 0x10, 4) := by
  decide +kernel
theorem d67 : Silmaril.X86.Ext.decode ((mcode.drop 67).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .r8 8)) .rcx, 4) := by
  decide +kernel
theorem d71 : Silmaril.X86.Ext.decode ((mcode.drop 71).take 3) = some (.mov .q (.reg .rcx) .r8, 3) := by
  decide +kernel
theorem d74 : Silmaril.X86.Ext.decode ((mcode.drop 74).take 3) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .r8 0)) .rdx, 3) := by
  decide +kernel
theorem d77 : Silmaril.X86.Ext.decode ((mcode.drop 77).take 3) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rax 0)) .rdi, 3) := by
  decide +kernel
theorem d80 : Silmaril.X86.Ext.decode ((mcode.drop 80).take 3) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0)) .rcx, 3) := by
  decide +kernel
theorem d83 : Silmaril.X86.Ext.decode ((mcode.drop 83).take 4) = some (.aluI8 .q .add (.reg .rax) 0x10, 4) := by
  decide +kernel
theorem d96 : Silmaril.X86.Ext.decode ((mcode.drop 96).take 2) = some (.alu .d .xor (.reg .rax) .rax, 2) := by
  decide +kernel
theorem d104 : Silmaril.X86.Ext.decode ((mcode.drop 104).take 4) = some (.lea .q .rsi (Silmaril.X86.Sep.Insn.memAt .rax 8), 4) := by
  decide +kernel
theorem d108 : Silmaril.X86.Ext.decode ((mcode.drop 108).take 3) = some (.test .q (.reg .rcx) .rcx, 3) := by
  decide +kernel
theorem d111 : Silmaril.X86.Ext.decode ((mcode.drop 111).take 2) = some (.jcc8 .e 0xef, 2) := by
  decide +kernel
theorem d113 : Silmaril.X86.Ext.decode ((mcode.drop 113).take 3) = some (.mov .q (.reg .rax) .rcx, 3) := by
  decide +kernel
theorem d116 : Silmaril.X86.Ext.decode ((mcode.drop 116).take 2) = some (.jmp8 0xac, 2) := by
  decide +kernel
theorem r87 : (code.drop 87).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem r98 : (code.drop 98).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel

/-! ## The loop invariant -/

/-- A loop index: the walked blocks, the block under inspection, the rest. -/
structure Ix where
  passed : List Block
  b : Block
  rest : List Block

/-- **The state at the loop head.** -/
def Inv (need : Nat) (sp ret : Word) (fl0 : List Block) (x : Ix) : SProp :=
  sexists fun (f : Reg → Word) => sexists fun (fl : Flags) =>
    ⌜f .rax = x.b.addr ∧ f .rsi = lastSlot flAddr x.passed ∧ f .rdi = BitVec.ofNat 64 need ∧
      f .rsp = sp ∧ (∀ c ∈ x.passed, c.size < need) ∧ x.passed ++ x.b :: x.rest = fl0⌝ ∗
    St 0x401352 f fl (wordPt sp.toNat ret ∗ plist flAddr x.passed x.b.addr ∗
      hdrSeg (x.b :: x.rest) x.b.addr ∗ strue)

/-- The loop measure. -/
def μ (x : Ix) : Nat := x.rest.length

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc
