module

public import Silmaril.Machine.X86.Ladder.LibMini.Transcript
public import Silmaril.Machine.X86.Ladder.LibMini.StrlenTranscript
public import Silmaril.Machine.X86.Ladder.LibMini.Bir.memcpy
public import Silmaril.Machine.X86.Ladder.LibMini.Bir.memset
public import Silmaril.Machine.X86.Stencils.ByteLoop.Defs
public import Silmaril.Machine.SystemV.Defs

/-!
# libmini (ladder rung 02) at `-O2`: stencil instances

`examples/elf-ladder/common/libmini.c` is the memory and string library that all ten ladder
rungs link. This module certifies `memcpy`, `memset` and `strlen` from the `-O2` build of rung
02 (`mem-loops`, transcribed by `tools/x86-lift`: `Transcript`, `StrlenTranscript`) as
instances of the byte-loop stencils `Copy`, `Fill` and `Scan`
(`Silmaril.Machine.X86.Stencils.ByteLoop`).

* **Code.** `memcpyCode`, `memsetCode`, `strlenCode`: each function's bytes, cut out of the
  transcribed regions at its partition entry and size (`memcpy` 35 bytes at `0x401300`,
  `memset` 58 bytes at `0x401380`, `strlen` 35 bytes at `0x401400`). The code is
  position-independent (no relocations), so every result is stated for **every load address
  `entry`**.
* **Blocks.** Each function is cut into straight-line blocks with at most one memory write,
  as the last instruction (`BlockCert.listingAtW`). The generated Bir blocks of WP2 are used
  where they qualify; the loop bodies that store are split after the store
  (`memcpy`: `movzbl; store | add; cmp; jne`; `memset`: `store | add; store | cmp; jne`),
  and their Bir blocks are written by hand and checked by `liftBlock … = some …`
  (`decide +kernel`). `strlen`'s `cmpb $0, (reg)` is not liftable to Bir; its two blocks are
  checked raw (the VC unfolds `Ext.exec`).
* **Annotations and measures.** `memcpy`: the index `rcx = i` with `memcpy`'s prefix
  `d[0, i) = s[0, i)`, measure `2(n - i)`. `memset`: the pointer `rcx = d + k` with
  `d[0, k) = c`, `n - k` even (the loop is unrolled twice after a peeled odd byte), measure
  `2(n - k)`. `strlen`: the pointer `rax = s + t` with `t ≤ k` (`k` the string length),
  measure `2(k - t)`.

The `FunCert`s are `memcpyCert`, `memsetCert`, `strlenCert`; the proofs are in
`Silmaril/Proofs/Machine/X86/Ladder/LibMini/`, the results in `LibMini/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Ladder.LibMini

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Mem)
open Silmaril.X86.Lift.Bir (LInstr Block E F Stmt)
open Silmaril.Machine.X86.BlockCert
open Silmaril.Machine.X86.Stencils.ByteLoop

/-! ## Code -/

/-- `memcpy`'s 35 bytes (transcribed at `0x401300`). -/
def memcpyCode : List Byte := Transcript.bytes.take 35

/-- `memset`'s 58 bytes (transcribed at `0x401380`). -/
def memsetCode : List Byte := (Transcript.bytes.drop 0x80).take 58

/-- `strlen`'s 35 bytes (transcribed at `0x401400`). -/
def strlenCode : List Byte := StrlenTranscript.bytes

/-- The addresses of the transcribed binary. -/
def memcpyAddr : Word := 0x401300
def memsetAddr : Word := 0x401380
def strlenAddr : Word := 0x401400

/-! ## `memcpy` (`Copy`) -/

section Memcpy
open Silmaril.Machine.X86.Ladder.LibMini.Bir.memcpy

/-- `movzbl (%rsi,%rcx),%r8d; mov %r8b,(%rax,%rcx)`. -/
def cpyL10 : List (LInstr × Nat) := L_401310.take 2
/-- `add $1,%rcx; cmp %rcx,%rdx; jne 0x10`. -/
def cpyL19 : List (LInstr × Nat) := L_401310.drop 2

def cpyI10 : Block :=
  { stmts := [.load 1 (.add (.reg .rsi) (.reg .rcx)),
      .store 1 (.add (.reg .rax) (.reg .rcx)) (.zext 8 (.zext 32 (.zext 8 (.v 0))))],
    regs := [(.r8, .zext 32 (.zext 8 (.v 0)))], flags := .entry, rip := .add .rip (.imm 9) }

def cpyI19 : Block :=
  { stmts := [.cond .ne (.alu 64 .cmp (.reg .rdx) (.add (.reg .rcx) (.imm 1)))],
    regs := [(.rcx, .add (.reg .rcx) (.imm 1))],
    flags := .alu 64 .cmp (.reg .rdx) (.add (.reg .rcx) (.imm 1)),
    rip := .sel (.v 0) (.add .rip (.imm 0xfffffffffffffff7)) (.add .rip (.imm 9)) }

/-- The `memcpy` loop at index `i`: frame, registers, and the copied prefix. -/
structure CpyAt (m0 m : MState) (i : Nat) : Prop where
  frame : LoopFrame m0 m
  rax : m.core.read .rax = m0.core.read .rdi
  rsi : m.core.read .rsi = m0.core.read .rsi
  rdx : m.core.read .rdx = m0.core.read .rdx
  pre : Prefix m0.memory m.memory (arg0 m0) i fun j => m0.memory.bytes.get? (arg1 m0 + j)

def cpyAnn (entry : Word) : Nat → MState → MState → Prop
  | 0x00, m0, m => m = m0 ∧ FnContract.AbiEntry m.core m.memory ∧
      (copyContract memcpyCode entry).entry m0
  | 0x08, m0, m => (copyContract memcpyCode entry).entry m0 ∧ CpyAt m0 m 0 ∧ arg2 m0 ≠ 0
  | 0x10, m0, m => (copyContract memcpyCode entry).entry m0 ∧
      CpyAt m0 m (m.core.read .rcx).toNat ∧ (m.core.read .rcx).toNat < arg2 m0
  | 0x19, m0, m => (copyContract memcpyCode entry).entry m0 ∧
      CpyAt m0 m ((m.core.read .rcx).toNat + 1) ∧ (m.core.read .rcx).toNat < arg2 m0
  | 0x22, m0, m => (copyContract memcpyCode entry).entry m0 ∧ CpyAt m0 m (arg2 m0)
  | _, _, _ => False

def cpyMeasure : Nat → MState → MState → Nat
  | 0x00, m0, _ => 2 * arg2 m0 + 4
  | 0x08, m0, _ => 2 * arg2 m0 + 3
  | 0x10, m0, m => 2 * (arg2 m0 - (m.core.read .rcx).toNat) + 1
  | 0x19, m0, m => 2 * (arg2 m0 - (m.core.read .rcx).toNat)
  | _, _, _ => 0

def memcpyCert (entry : Word) : FunCert where
  code := memcpyCode
  base := entry
  blocks := [⟨0x00, L_401300⟩, ⟨0x08, L_401308⟩, ⟨0x10, cpyL10⟩, ⟨0x19, cpyL19⟩,
    ⟨0x22, L_401322⟩]
  ann := cpyAnn entry
  measure := cpyMeasure

end Memcpy

/-! ## `memset` (`Fill`) -/

section Memset
open Silmaril.Machine.X86.Ladder.LibMini.Bir.memset

/-- `lea 1(%rax),%rcx; mov %sil,(%rax)`. -/
def setL17 : List (LInstr × Nat) := L_401397.take 2
/-- `cmp %rdi,%rcx; je 0x39`. -/
def setL1e : List (LInstr × Nat) := L_401397.drop 2
/-- `mov %r8b,(%rcx)`. -/
def setL28 : List (LInstr × Nat) := L_4013a8.take 1
/-- `add $2,%rcx; mov %r8b,-1(%rcx)`. -/
def setL2b : List (LInstr × Nat) := (L_4013a8.drop 1).take 2
/-- `cmp %rdi,%rcx; jne 0x28`. -/
def setL33 : List (LInstr × Nat) := L_4013a8.drop 3

def setI17 : Block :=
  { stmts := [.store 1 (.reg .rax) (.zext 8 (.reg .rsi))],
    regs := [(.rcx, .add (.reg .rax) (.imm 1))], flags := .entry, rip := .add .rip (.imm 7) }

def setI1e : Block :=
  { stmts := [.cond .e (.alu 64 .cmp (.reg .rcx) (.reg .rdi))], regs := [],
    flags := .alu 64 .cmp (.reg .rcx) (.reg .rdi),
    rip := .sel (.v 0) (.add .rip (.imm 0x1b)) (.add .rip (.imm 5)) }

def setI28 : Block :=
  { stmts := [.store 1 (.reg .rcx) (.zext 8 (.reg .r8))], regs := [], flags := .entry,
    rip := .add .rip (.imm 3) }

def setI2b : Block :=
  { stmts := [.store 1 (.add (.reg .rcx) (.imm 1)) (.zext 8 (.reg .r8))],
    regs := [(.rcx, .add (.reg .rcx) (.imm 2))],
    flags := .alu 64 .add (.reg .rcx) (.imm 2), rip := .add .rip (.imm 8) }

def setI33 : Block :=
  { stmts := [.cond .ne (.alu 64 .cmp (.reg .rcx) (.reg .rdi))], regs := [],
    flags := .alu 64 .cmp (.reg .rcx) (.reg .rdi),
    rip := .sel (.v 0) (.add .rip (.imm 0xfffffffffffffff5)) (.add .rip (.imm 5)) }

/-- The fill value. -/
def fillByte (m0 : MState) : Byte := (m0.core.read .rsi).setWidth 8

/-- The `memset` loop with `k` bytes written and the store pointer at `d + p`. -/
structure SetAt (m0 m : MState) (k : Nat) : Prop where
  frame : LoopFrame m0 m
  rax : m.core.read .rax = m0.core.read .rdi
  rdi : m.core.read .rdi = m0.core.read .rdi + m0.core.read .rdx
  r8 : (m.core.read .r8).setWidth 8 = fillByte m0
  pre : Prefix m0.memory m.memory (arg0 m0) k fun _ => some (fillByte m0)

/-- `memset` done: frame, result register and the whole block filled. -/
structure SetDone (m0 m : MState) : Prop where
  frame : LoopFrame m0 m
  rax : m.core.read .rax = m0.core.read .rdi
  pre : Prefix m0.memory m.memory (arg0 m0) (arg2 m0) fun _ => some (fillByte m0)

/-- The store pointer is `d + p`. -/
def SetPtr (m0 m : MState) (p : Nat) : Prop :=
  m.core.read .rcx = m0.core.read .rdi + BitVec.ofNat 64 p

def setAnn (entry : Word) : Nat → MState → MState → Prop
  | 0x00, m0, m => m = m0 ∧ FnContract.AbiEntry m.core m.memory ∧
      (fillContract memsetCode entry).entry m0
  | 0x08, m0, m => (fillContract memsetCode entry).entry m0 ∧ LoopFrame m0 m ∧
      m.memory = m0.memory ∧ m.core.read .rax = m0.core.read .rdi ∧
      m.core.read .rdi = m0.core.read .rdi ∧ m.core.read .rsi = m0.core.read .rsi ∧
      m.core.read .rdx = m0.core.read .rdx ∧ arg2 m0 ≠ 0
  | 0x17, m0, m => (fillContract memsetCode entry).entry m0 ∧ SetAt m0 m 0 ∧
      m.core.read .rsi = m0.core.read .rsi ∧ arg2 m0 % 2 = 1
  | 0x1e, m0, m => (fillContract memsetCode entry).entry m0 ∧ SetAt m0 m 1 ∧ SetPtr m0 m 1 ∧
      arg2 m0 % 2 = 1
  | 0x23, m0, m => (fillContract memsetCode entry).entry m0 ∧ SetAt m0 m 1 ∧ SetPtr m0 m 1 ∧
      1 < arg2 m0 ∧ arg2 m0 % 2 = 1
  | 0x28, m0, m => (fillContract memsetCode entry).entry m0 ∧ ∃ k, SetAt m0 m k ∧
      SetPtr m0 m k ∧ k < arg2 m0 ∧ (arg2 m0 - k) % 2 = 0
  | 0x2b, m0, m => (fillContract memsetCode entry).entry m0 ∧ ∃ k, SetAt m0 m (k + 1) ∧
      SetPtr m0 m k ∧ k < arg2 m0 ∧ (arg2 m0 - k) % 2 = 0
  | 0x33, m0, m => (fillContract memsetCode entry).entry m0 ∧ ∃ k, SetAt m0 m k ∧
      SetPtr m0 m k ∧ 2 ≤ k ∧ k ≤ arg2 m0 ∧ (arg2 m0 - k) % 2 = 0
  | 0x38, m0, m => (fillContract memsetCode entry).entry m0 ∧ SetDone m0 m
  | 0x39, m0, m => (fillContract memsetCode entry).entry m0 ∧ SetDone m0 m
  | _, _, _ => False

/-- The store pointer's offset. -/
def setOff (m0 m : MState) : Nat := (m.core.read .rcx - m0.core.read .rdi).toNat

def setMeasure : Nat → MState → MState → Nat
  | 0x00, m0, _ => 2 * arg2 m0 + 10
  | 0x08, m0, _ => 2 * arg2 m0 + 9
  | 0x17, m0, _ => 2 * arg2 m0 + 8
  | 0x1e, m0, _ => 2 * arg2 m0 + 7
  | 0x23, m0, _ => 2 * arg2 m0 + 6
  | 0x28, m0, m => 2 * (arg2 m0 - setOff m0 m) + 2
  | 0x2b, m0, m => 2 * (arg2 m0 - setOff m0 m) + 1
  | 0x33, m0, m => 2 * (arg2 m0 - setOff m0 m) + 4
  | _, _, _ => 0

def memsetCert (entry : Word) : FunCert where
  code := memsetCode
  base := entry
  blocks := [⟨0x00, L_401380⟩, ⟨0x08, L_401388⟩, ⟨0x17, setL17⟩, ⟨0x1e, setL1e⟩,
    ⟨0x23, L_4013a3⟩, ⟨0x28, setL28⟩, ⟨0x2b, setL2b⟩, ⟨0x33, setL33⟩, ⟨0x38, L_4013b8⟩,
    ⟨0x39, L_4013b9⟩]
  ann := setAnn entry
  measure := setMeasure

end Memset

/-! ## `strlen` (`Scan`) -/

/-- `cmpb $0,(%rdi); je 0x20` (raw: `cmpb $imm,(reg)` is not liftable to Bir). -/
def lenL00 : List (LInstr × Nat) :=
  [(.ext (.cmpI8 (.mem (Mem.ofReg .rdi none 0x0)) 0x0), 3), (.ext (.jcc8 .e 0x1b), 2)]
/-- `mov %rdi,%rax; nopl`. -/
def lenL05 : List (LInstr × Nat) := [(.ext (.mov .q (.reg .rax) .rdi), 3), (.ext (.nop 7), 8)]
/-- `add $1,%rax`. -/
def lenL10 : List (LInstr × Nat) := [(.ext (.aluI8 .q .add (.reg .rax) 0x1), 4)]
/-- `cmpb $0,(%rax); jne 0x10` (raw). -/
def lenL14 : List (LInstr × Nat) :=
  [(.ext (.cmpI8 (.mem (Mem.ofReg .rax none 0x0)) 0x0), 3), (.ext (.jcc8 .ne 0xf7), 2)]
/-- `sub %rdi,%rax; ret`. -/
def lenL19 : List (LInstr × Nat) := [(.ext (.alu .q .sub (.reg .rax) .rdi), 3), (.ext .ret, 1)]
/-- `xor %eax,%eax; ret`. -/
def lenL20 : List (LInstr × Nat) := [(.ext (.alu .d .xor (.reg .rax) .rax), 2), (.ext .ret, 1)]

def lenI05 : Block :=
  { stmts := [], regs := [(.rax, .reg .rdi)], flags := .entry, rip := .add .rip (.imm 0xb) }

def lenI10 : Block :=
  { stmts := [], regs := [(.rax, .add (.reg .rax) (.imm 1))],
    flags := .alu 64 .add (.reg .rax) (.imm 1), rip := .add .rip (.imm 4) }

def lenI19 : Block :=
  { stmts := [.pop (.reg .rsp)],
    regs := [(.rax, .sub (.reg .rax) (.reg .rdi)), (.rsp, .add (.reg .rsp) (.imm 8))],
    flags := .alu 64 .sub (.reg .rax) (.reg .rdi), rip := .v 0 }

def lenI20 : Block :=
  { stmts := [.pop (.reg .rsp)],
    regs := [(.rax, .zext 32 (.alu 32 .xor (.reg .rax) (.reg .rax))),
      (.rsp, .add (.reg .rsp) (.imm 8))],
    flags := .alu 32 .xor (.reg .rax) (.reg .rax), rip := .v 0 }

open Classical in
/-- The length of the string at `rdi` (`0` if there is none). -/
noncomputable def strLen (m0 : MState) : Nat :=
  if h : ∃ k, CStr m0.memory (arg0 m0) k then Classical.choose h else 0

/-- The `strlen` scan at offset `t` from the string's start, before the NUL. -/
structure LenAt (m0 m : MState) (t : Nat) : Prop where
  frame : LoopFrame m0 m
  mem : m.memory = m0.memory
  rdi : m.core.read .rdi = m0.core.read .rdi
  rax : m.core.read .rax = m0.core.read .rdi + BitVec.ofNat 64 t
  le : t ≤ strLen m0

def lenAnn (entry : Word) : Nat → MState → MState → Prop
  | 0x00, m0, m => m = m0 ∧ FnContract.AbiEntry m.core m.memory ∧
      (scanContract strlenCode entry).entry m0
  | 0x05, m0, m => (scanContract strlenCode entry).entry m0 ∧ LoopFrame m0 m ∧
      m.memory = m0.memory ∧ m.core.read .rdi = m0.core.read .rdi ∧ 0 < strLen m0
  | 0x10, m0, m => (scanContract strlenCode entry).entry m0 ∧ ∃ t, LenAt m0 m t ∧ t < strLen m0
  | 0x14, m0, m => (scanContract strlenCode entry).entry m0 ∧ ∃ t, LenAt m0 m t
  | 0x19, m0, m => (scanContract strlenCode entry).entry m0 ∧ LenAt m0 m (strLen m0)
  | 0x20, m0, m => (scanContract strlenCode entry).entry m0 ∧ LoopFrame m0 m ∧
      m.memory = m0.memory ∧ strLen m0 = 0
  | _, _, _ => False

/-- The scan pointer's offset. -/
def lenOff (m0 m : MState) : Nat := (m.core.read .rax - m0.core.read .rdi).toNat

noncomputable def lenMeasure : Nat → MState → MState → Nat
  | 0x00, m0, _ => 2 * strLen m0 + 10
  | 0x05, m0, _ => 2 * strLen m0 + 9
  | 0x10, m0, m => 2 * (strLen m0 - lenOff m0 m) + 1
  | 0x14, m0, m => 2 * (strLen m0 - lenOff m0 m) + 2
  | _, _, _ => 0

noncomputable def strlenCert (entry : Word) : FunCert where
  code := strlenCode
  base := entry
  blocks := [⟨0x00, lenL00⟩, ⟨0x05, lenL05⟩, ⟨0x10, lenL10⟩, ⟨0x14, lenL14⟩, ⟨0x19, lenL19⟩,
    ⟨0x20, lenL20⟩]
  ann := lenAnn entry
  measure := lenMeasure

/-! ## C signatures (for the integer `SystemV.Realizes` certificates) -/

/-- `void *memcpy(void *, const void *, size_t)`. -/
def sigCopy : Silmaril.C.Api.Signature := ⟨[.pointer, .pointer, .uint64], some .pointer⟩
/-- `void *memset(void *, int, size_t)`. -/
def sigFill : Silmaril.C.Api.Signature := ⟨[.pointer, .int32, .uint64], some .pointer⟩
/-- `size_t strlen(const char *)`. -/
def sigScan : Silmaril.C.Api.Signature := ⟨[.pointer], some .uint64⟩

/-- `memcpy` and `memset` return their first argument. -/
def firstResult {k : List Silmaril.C.Api.Scalar} :
    Silmaril.C.Api.Arguments (.pointer :: k) → Silmaril.C.Api.ReturnValue (some .pointer)
  | .cons d _ => d

/-- `memcpy` and `memset` write `[d, d + n)`. -/
def blockWrites {k : Silmaril.C.Api.Scalar} :
    Silmaril.C.Api.Arguments [.pointer, k, .uint64] → Silmaril.Machine.SystemV.Footprint
  | .cons d (.cons _ (.cons n .nil)) => fun a => d.toNat ≤ a ∧ a < d.toNat + n.toNat

end Silmaril.Machine.X86.Ladder.LibMini
