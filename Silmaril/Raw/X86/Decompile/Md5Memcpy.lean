module

public import Silmaril.X86.Bench.Objects.Md5MemcpyClangO0.Defs
public import Silmaril.X86.CallingConvention
public import Silmaril.X86.Decompile.Cert
/-!
# `MD5_memcpy`, decompiled into logic

The loop case for `Silmaril/X86/Decompile/Cert.lean`. `MD5_memcpy` is

```c
static void MD5_memcpy(POINTER output, POINTER input, unsigned int len) {
  for (unsigned int i = 0; i < len; i++) output[i] = input[i];
}
```

compiled by `clang -O0` for `x86_64-linux-gnu`; its 70 bytes are at `.text`
offset `0x1c0` of the pinned object that
`Silmaril.X86.Bench.Objects.Md5MemcpyClangO0` ingests.

```
1c0: push   %rbp                    55
1c1: mov    %rsp,%rbp               48 89 e5
1c4: mov    %rdi,-0x8(%rbp)         48 89 7d f8
1c8: mov    %rsi,-0x10(%rbp)        48 89 75 f0
1cc: mov    %edx,-0x14(%rbp)        89 55 ec
1cf: movl   $0x0,-0x18(%rbp)        c7 45 e8 00 00 00 00
                                 -- loop head
1d6: mov    -0x18(%rbp),%eax        8b 45 e8
1d9: cmp    -0x14(%rbp),%eax        3b 45 ec
1dc: jae    204                     0f 83 22 00 00 00
                                 -- loop body
1e2: mov    -0x10(%rbp),%rax        48 8b 45 f0
1e6: mov    -0x18(%rbp),%ecx        8b 4d e8
1e9: mov    (%rax,%rcx,1),%dl       8a 14 08
1ec: mov    -0x8(%rbp),%rax         48 8b 45 f8
1f0: mov    -0x18(%rbp),%ecx        8b 4d e8
1f3: mov    %dl,(%rax,%rcx,1)       88 14 08
1f6: mov    -0x18(%rbp),%eax        8b 45 e8
1f9: add    $0x1,%eax               83 c0 01
1fc: mov    %eax,-0x18(%rbp)        89 45 e8
1ff: jmp    1d6                     e9 d2 ff ff ff
204: pop    %rbp                    5d
205: ret                            c3
```

## Why this is the interesting case

`right_rot` is straight-line: its certificate is fifteen `retires_instr`
applications in a row, and no rule beyond `Advances.trans` is needed. A loop is
where decompilation-into-logic earns its keep: the machine code becomes a
*tail-recursive Lean function* plus an induction, and the induction happens
once, in `Advances.loop` (`Cert.lean`), not per program.

`writtenBytes` below is that tail-recursive function. It is a plain Lean
function on `Nat → Word`: no `State`, no `Memory`, no `exec`.
`writtenBytes_eq` is the "and now reason about it normally" step — the
tail-recursive accumulation equals the obvious pointwise description, proved by
ordinary well-founded induction with nothing machine-related in sight.

## Status

Proved end to end and `sorry`-free: the ingestion, the decoder's reading of all
70 bytes, the tail-recursive decompiled function with its closed form, the
prologue / per-iteration / epilogue certificates, and `md5_memcpy_returns`
gluing them with `Advances.loop`.

The `Status` section at the end of this file records a prediction this file
made before the attempt — that indexed framing would be where the approach ran
out — which the attempt disproved. That note is kept deliberately.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.Md5Memcpy

open Silmaril.X86 (Byte Word State MState Reg AluOp)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-! ## The decompiled function -/

/-- **The decompilation of `MD5_memcpy`'s loop.** `src i` is the byte at
`input + i`; the function accumulates, one iteration at a time, the partial map
from output offset to the byte written there. It is tail-recursive and
terminates on `len - i`, which is exactly the loop's own decreasing measure.

No `State`, no `Memory`, no `exec`: this is the "logic" that the machine code
decompiles *into*. -/
def writtenBytes (src : Nat → Word) (len : Nat) :
    Nat → (Nat → Option Word) → (Nat → Option Word)
  | i, f =>
    if i < len then
      writtenBytes src len (i + 1) (fun j => if j = i then some (src i) else f j)
    else f
  termination_by i => len - i

/-- The empty accumulator the loop starts from. -/
def nothingWritten : Nat → Option Word := fun _ => none

/-- **The decompiled function in closed form.** Running the tail recursion from
`i` leaves the bytes `i, …, len-1` written and everything else as it was. This
is the step that a decompilation makes cheap: it is an ordinary induction on
`len - i` about a function with no machine in it. -/
theorem writtenBytes_le (src : Nat → Word) (len : Nat) :
    ∀ (k i : Nat), len - i ≤ k → ∀ (f : Nat → Option Word) j,
      writtenBytes src len i f j = if i ≤ j ∧ j < len then some (src j) else f j := by
  intro k
  induction k with
  | zero =>
    intro i hk f j
    rw [writtenBytes]
    have hi : ¬ i < len := by omega
    have hno : ¬ (i ≤ j ∧ j < len) := by rintro ⟨h1, h2⟩; omega
    simp [hi, hno]
  | succ k ih =>
    intro i hk f j
    rw [writtenBytes]
    by_cases hi : i < len
    · simp only [hi, ite_true]
      rw [ih (i + 1) (by omega) _ j]
      by_cases hj : j = i
      · subst hj; simp [hi]
      · by_cases hle : i + 1 ≤ j
        · have h2 : i ≤ j := by omega
          simp [hle, h2, hj]
        · have h1 : ¬ (i ≤ j) := by omega
          simp [hle, h1, hj]
    · have hno : ¬ (i ≤ j ∧ j < len) := by rintro ⟨h1, h2⟩; omega
      simp [hi, hno]

theorem writtenBytes_eq (src : Nat → Word) (len : Nat) (i : Nat) (f : Nat → Option Word)
    (j : Nat) : writtenBytes src len i f j = if i ≤ j ∧ j < len then some (src j) else f j :=
  writtenBytes_le src len (len - i) i (Nat.le_refl _) f j

/-- From the empty accumulator: exactly the first `len` bytes are written. -/
theorem writtenBytes_zero (src : Nat → Word) (len : Nat) (j : Nat) :
    writtenBytes src len 0 nothingWritten j = if j < len then some (src j) else none := by
  rw [writtenBytes_eq]
  by_cases h : j < len <;> simp [h, nothingWritten]

/-! ## The code -/

/-- `[rbp + disp]`. -/
def frame (disp : BitVec 32) : Mem := Mem.ofReg .rbp none disp

/-- `[base + index]`, the byte-indexed addressing the copy uses. -/
def atIndex (base index : Reg) (h : index ≠ .rsp) : Mem :=
  Mem.ofReg base (some ⟨index, 0, h⟩) 0

/-- The 70 bytes of `MD5_memcpy`. -/
def code : List Byte :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x89, 0x7D, 0xF8, 0x48, 0x89, 0x75, 0xF0, 0x89, 0x55, 0xEC,
   0xC7, 0x45, 0xE8, 0x00, 0x00, 0x00, 0x00,
   0x8B, 0x45, 0xE8, 0x3B, 0x45, 0xEC, 0x0F, 0x83, 0x22, 0x00, 0x00, 0x00,
   0x48, 0x8B, 0x45, 0xF0, 0x8B, 0x4D, 0xE8, 0x8A, 0x14, 0x08,
   0x48, 0x8B, 0x45, 0xF8, 0x8B, 0x4D, 0xE8, 0x88, 0x14, 0x08,
   0x8B, 0x45, 0xE8, 0x83, 0xC0, 0x01, 0x89, 0x45, 0xE8,
   0xE9, 0xD2, 0xFF, 0xFF, 0xFF, 0x5D, 0xC3]

/-- These are exactly the bytes the ELF reader selected for the `MD5_memcpy`
symbol of the pinned object. -/
theorem code_eq_functionBytes :
    code = Bench.Objects.Md5MemcpyClangO0.functionBytes.toList := by decide

/-- The decompiler's reading of `code`: twenty-one instructions. -/
def instrs : List Ext.Instr :=
  [.push .rbp,
   .mov .q (.reg .rbp) .rsp,
   .mov .q (.mem (frame 0xFFFFFFF8)) .rdi,
   .mov .q (.mem (frame 0xFFFFFFF0)) .rsi,
   .mov .d (.mem (frame 0xFFFFFFEC)) .rdx,
   .movI .d (.mem (frame 0xFFFFFFE8)) 0,
   -- loop head
   .load .d .rax (frame 0xFFFFFFE8),
   .aluR .d .cmp .rax (.mem (frame 0xFFFFFFEC)),
   .jcc .ae 0x22,
   -- loop body
   .load .q .rax (frame 0xFFFFFFF0),
   .load .d .rcx (frame 0xFFFFFFE8),
   .mov8 .rdx (.mem (atIndex .rax .rcx (by decide))),
   .load .q .rax (frame 0xFFFFFFF8),
   .load .d .rcx (frame 0xFFFFFFE8),
   .store .b (.mem (atIndex .rax .rcx (by decide))) .rdx,
   .load .d .rax (frame 0xFFFFFFE8),
   .aluI8 .d .add (.reg .rax) 1,
   .mov .d (.mem (frame 0xFFFFFFE8)) .rax,
   .jmp 0xFFFFFFD2,
   .pop .rbp,
   .ret]

/-- The model's decoder reads `code` as exactly `instrs`. -/
theorem code_decodeAll : decodeAll 70 code = some instrs := by decide

/-- The per-instruction lengths, checkable against the disassembly; their sum
is the 70 bytes `readelf` reports for the symbol. -/
theorem code_decodeLengths :
    decodeLengths 70 code =
      some [1, 3, 4, 4, 3, 7, 3, 3, 6, 4, 3, 3, 4, 3, 3, 3, 3, 3, 5, 1, 1] := by decide

/-- Every byte belongs to one instruction, each spelled the way `encode` spells
it. -/
theorem code_covered : Covered code := covered_of_decodeAll code_decodeAll

/-- The loop head is at offset 22 (`0x1d6`), the body at 34 (`0x1e2`), the exit
at 68 (`0x204`). The backward `jmp` at 63 has displacement `-0x2e`, which lands
exactly on the head; the forward `jae` at 28 has `+0x22`, which lands exactly on
the exit. -/
theorem loop_offsets :
    (63 + 5 : Int) + (-0x2e : Int) = 22 ∧ (28 + 6 : Int) + 0x22 = 68 := by decide

/-! ## Nonoverlapping

`MD5_memcpy` copies forward, one byte at a time, so it is only correct when the
buffers do not overlap — reading `input[i]` after writing `output[0..i)` must
see the original byte. This is the `nonoverlapping(output, input, len)`
precondition the C caller owes, and it is exactly s2n-bignum's
`nonoverlapping`. -/

/-- The two `len`-byte buffers do not overlap. -/
def Nonoverlapping (out inp : Word) (len : Nat) : Prop :=
  out.toNat + len ≤ inp.toNat ∨ inp.toNat + len ≤ out.toNat

/-! ## Instruction lengths and addresses -/

theorem M0  : (X86.Insn.push Reg.rbp).length = 1 := by decide
theorem M1  : (Ext.Instr.mov .q (.reg Reg.rbp) Reg.rsp).length = 3 := by decide
theorem M2  : (Ext.Instr.mov .q (.mem (frame 0xFFFFFFF8)) Reg.rdi).length = 4 := by decide
theorem M3  : (Ext.Instr.mov .q (.mem (frame 0xFFFFFFF0)) Reg.rsi).length = 4 := by decide
theorem M4  : (Ext.Instr.mov .d (.mem (frame 0xFFFFFFEC)) Reg.rdx).length = 3 := by decide
theorem M5  : (Ext.Instr.movI .d (.mem (frame 0xFFFFFFE8)) 0).length = 7 := by decide
theorem M6  : (Ext.Instr.load .d Reg.rax (frame 0xFFFFFFE8)).length = 3 := by decide
theorem M7  : (Ext.Instr.aluR .d .cmp Reg.rax (.mem (frame 0xFFFFFFEC))).length = 3 := by decide
theorem M8  : (Ext.Instr.jcc .ae 0x22).length = 6 := by decide
theorem M9  : (Ext.Instr.load .q Reg.rax (frame 0xFFFFFFF0)).length = 4 := by decide
theorem M10 : (Ext.Instr.load .d Reg.rcx (frame 0xFFFFFFE8)).length = 3 := by decide
theorem M11 : (Ext.Instr.mov8 Reg.rdx (.mem (atIndex .rax .rcx (by decide)))).length = 3 := by
  decide
theorem M12 : (Ext.Instr.load .q Reg.rax (frame 0xFFFFFFF8)).length = 4 := by decide
theorem M13 :
    (Ext.Instr.store .b (.mem (atIndex .rax .rcx (by decide))) Reg.rdx).length = 3 := by decide
theorem M14 : (Ext.Instr.aluI8 .d .add (.reg Reg.rax) 1).length = 3 := by decide
theorem M15 : (Ext.Instr.mov .d (.mem (frame 0xFFFFFFE8)) Reg.rax).length = 3 := by decide
theorem M16 : (Ext.Instr.jmp 0xFFFFFFD2).length = 5 := by decide
theorem M17 : (X86.Insn.pop Reg.rbp).length = 1 := by decide

/-- The effective address of `[rbp + disp]`. -/
theorem frame_addr (disp : BitVec 32) (t : State) (nxt : Word) :
    (frame disp).addr t nxt = t.read .rbp + disp.signExtend 64 := by
  simp [frame, Mem.addr, Mem.ofReg]

/-- The effective address of `[base + index]`, the byte-indexed form the copy
uses. The scale is zero, so this really is just the sum. -/
theorem index_addr (base idx : Reg) (h : idx ≠ .rsp) (t : State) (nxt : Word) :
    (atIndex base idx h).addr t nxt = t.read base + t.read idx := by
  simp [atIndex, Mem.addr, Mem.ofReg, Index.value]

theorem aF8 (sp : Word) :
    sp - 8#64 + ((0xFFFFFFF8 : BitVec 32).signExtend 64) = sp - 16#64 := by
  have hs : ((0xFFFFFFF8 : BitVec 32).signExtend 64) = -(8#64) := by decide
  have ha : -(8#64) + -(8#64) = -(16#64) := by decide
  rw [hs, BitVec.sub_eq_add_neg, BitVec.add_assoc, ha, ← BitVec.sub_eq_add_neg]

theorem aF0 (sp : Word) :
    sp - 8#64 + ((0xFFFFFFF0 : BitVec 32).signExtend 64) = sp - 24#64 := by
  have hs : ((0xFFFFFFF0 : BitVec 32).signExtend 64) = -(16#64) := by decide
  have ha : -(8#64) + -(16#64) = -(24#64) := by decide
  rw [hs, BitVec.sub_eq_add_neg, BitVec.add_assoc, ha, ← BitVec.sub_eq_add_neg]

theorem aEC (sp : Word) :
    sp - 8#64 + ((0xFFFFFFEC : BitVec 32).signExtend 64) = sp - 28#64 := by
  have hs : ((0xFFFFFFEC : BitVec 32).signExtend 64) = -(20#64) := by decide
  have ha : -(8#64) + -(20#64) = -(28#64) := by decide
  rw [hs, BitVec.sub_eq_add_neg, BitVec.add_assoc, ha, ← BitVec.sub_eq_add_neg]

theorem aE8 (sp : Word) :
    sp - 8#64 + ((0xFFFFFFE8 : BitVec 32).signExtend 64) = sp - 32#64 := by
  have hs : ((0xFFFFFFE8 : BitVec 32).signExtend 64) = -(24#64) := by decide
  have ha : -(8#64) + -(24#64) = -(32#64) := by decide
  rw [hs, BitVec.sub_eq_add_neg, BitVec.add_assoc, ha, ← BitVec.sub_eq_add_neg]

/-! ## ABI-conformant entry -/

/-- The System V arguments: output in `rdi`, input in `rsi`, length in `edx`. -/
def outOf (m : MState) : Word := m.core.read .rdi
def inOf (m : MState) : Word := m.core.read .rsi
def lenOf (m : MState) : Nat := (Sz.d.read m.core .rdx).toNat

/-- **An ABI-conformant System V entry state** for `MD5_memcpy`.

The frame is the 32 bytes below the entry `rsp`: eight for the pushed `rbp`,
then eight for `output`, eight for `input`, four for `len` and four for the
loop counter — 24 bytes of the 128-byte `sysv64.redZone`. -/
structure Entry (entry exit : Word) (m : MState) : Prop where
  rip : m.core.rip = entry
  image : Image code entry m.memory
  ret : m.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [exit])
  frameWrite : m.memory.Permitted .write ((m.core.read .rsp).toNat - 32) 32
  frameRead : m.memory.Permitted .read ((m.core.read .rsp).toNat - 32) 32
  spLow : 32 ≤ (m.core.read .rsp).toNat
  outWrite : m.memory.Permitted .write (outOf m).toNat (lenOf m)
  outRead : m.memory.Permitted .read (outOf m).toNat (lenOf m)
  inRead : m.memory.Permitted .read (inOf m).toNat (lenOf m)
  /-- The input bytes are present. -/
  inLoad : ∀ j, j < lenOf m → (Ext.loadN m.memory (inOf m + BitVec.ofNat 64 j) 1).isSome
  outBound : (outOf m).toNat + lenOf m ≤ 2 ^ 64
  inBound : (inOf m).toNat + lenOf m ≤ 2 ^ 64
  /-- The forward byte copy is only correct for non-overlapping buffers. -/
  apart : Nonoverlapping (outOf m) (inOf m) (lenOf m)
  outFrame : (outOf m).toNat + lenOf m ≤ (m.core.read .rsp).toNat - 32 ∨
    (m.core.read .rsp).toNat + 8 ≤ (outOf m).toNat
  inFrame : (inOf m).toNat + lenOf m ≤ (m.core.read .rsp).toNat - 32 ∨
    (m.core.read .rsp).toNat + 8 ≤ (inOf m).toNat
  outCode : entry.toNat + 70 ≤ (outOf m).toNat ∨ (outOf m).toNat + lenOf m ≤ entry.toNat
  frameCode : entry.toNat + 70 ≤ (m.core.read .rsp).toNat - 32 ∨
    (m.core.read .rsp).toNat + 8 ≤ entry.toNat

/-! ## The loop-head invariant -/

/-- The machine is at the loop head (`.text` offset 22) having copied `i`
bytes. `base` is the state just after the prologue, so `frame` says the loop
has touched nothing but the output buffer and its own counter slot; every other
fact the body needs — the code image, the `output`/`input`/`len` frame slots,
the saved `rbp`, the return address and the untouched input — is recovered from
`frame` together with the corresponding fact about `base`. -/
structure AtLoop (entry sp out inp : Word) (len : Nat) (base m : MState) (i : Nat) : Prop where
  rip : m.core.rip = entry + 22#64
  rbp : m.core.read .rbp = sp - 8#64
  rsp : m.core.read .rsp = sp - 8#64
  slotI : Ext.loadN m.memory (sp - 32#64) 4 = some (BitVec.ofNat 64 i)
  copied : ∀ j, j < i → Ext.loadN m.memory (out + BitVec.ofNat 64 j) 1 =
    Ext.loadN base.memory (inp + BitVec.ofNat 64 j) 1
  frame : WritesOnly₂ base.memory m.memory out.toNat len (sp.toNat - 32) 4
  ile : i ≤ len
  /-- The loop body touches only `rax`, `rcx` and `rdx`. -/
  other : ∀ r : Reg, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → m.core.read r = base.core.read r

/-! ## Numeric helpers -/

/-- Narrowing a 64-bit `ofNat` to 32 bits. -/
theorem narrow (i : Nat) : (BitVec.ofNat 64 i).setWidth Sz.d.bits = BitVec.ofNat Sz.d.bits i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd i (Nat.pow_dvd_pow 2 (by decide : Sz.d.bits ≤ 64))

/-- Widening a 32-bit `ofNat` back to 64 bits, when it fits. -/
theorem widen (i : Nat) (h : i < 2 ^ 32) :
    (BitVec.ofNat Sz.d.bits i).setWidth 64 = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2:Nat) ^ Sz.d.bits = 2 ^ 32 from rfl, Nat.mod_eq_of_lt h]

/-- A one-byte load is a byte: its value is below 256. -/
theorem loadN_one_lt {mem : Memory} {a : Word} {w : Word} (h : Ext.loadN mem a 1 = some w) :
    w.toNat < 256 := by
  simp only [Ext.loadN, Option.map_eq_some_iff] at h
  obtain ⟨bs, hbs, rfl⟩ := h
  have hlen : bs.length = 1 := Memory.readWith_length hbs
  match bs, hlen with
  | [b], _ =>
    show (BitVec.ofNat 64 (Ext.leValue [b])).toNat < 256
    have : Ext.leValue [b] = b.toNat := by simp [Ext.leValue]
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
    have := b.isLt
    omega

/-- Reconstructing a byte value from what `loadN_storeN` reports for a one-byte
store. -/
theorem byte_roundtrip {w : Word} (h : w.toNat < 256) :
    BitVec.ofNat 64 (w.toNat % 2 ^ (8 * 1)) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, show 8 * 1 = 8 from rfl, show (2:Nat) ^ 8 = 256 from rfl,
    Nat.mod_eq_of_lt h]
  exact Nat.mod_eq_of_lt w.isLt

/-- The backward jump at offset 63 lands exactly on the loop head at 22. -/
theorem jmpBack (e : Word) :
    e + 63#64 + 5#64 + ((0xFFFFFFD2 : BitVec 32).signExtend 64) = e + 22#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc,
    show 63#64 + (5#64 + ((0xFFFFFFD2 : BitVec 32).signExtend 64)) = 22#64 from by decide]

/-- The forward conditional jump at offset 28 lands exactly on the exit at 68. -/
theorem jmpExit (e : Word) :
    e + 28#64 + 6#64 + ((0x22 : BitVec 32).signExtend 64) = e + 68#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc,
    show 28#64 + (6#64 + ((0x22 : BitVec 32).signExtend 64)) = 68#64 from by decide]

/-! ## The static side conditions

Everything the loop body needs that does not change from iteration to
iteration: the geometry of the three buffers (output, input, frame), the frame
slots as the prologue left them, and the permissions. Bundling them keeps the
per-iteration certificate's signature readable. -/

structure Static (entry sp out inp : Word) (len : Nat) (base : MState) : Prop where
  image : Image code entry base.memory
  slotOut : Ext.loadN base.memory (sp - 16#64) 8 = some out
  slotIn : Ext.loadN base.memory (sp - 24#64) 8 = some inp
  slotLen : Ext.loadN base.memory (sp - 28#64) 4 = some (BitVec.ofNat 64 len)
  /-- The input bytes are present and readable. -/
  inLoad : ∀ j, j < len → (Ext.loadN base.memory (inp + BitVec.ofNat 64 j) 1).isSome
  spLow : 32 ≤ sp.toNat
  spHigh : sp.toNat + 8 ≤ 2 ^ 64
  outBound : out.toNat + len ≤ 2 ^ 64
  inBound : inp.toNat + len ≤ 2 ^ 64
  lenLt : len < 2 ^ 32
  apart : Nonoverlapping out inp len
  outFrame : out.toNat + len ≤ sp.toNat - 32 ∨ sp.toNat + 8 ≤ out.toNat
  inFrame : inp.toNat + len ≤ sp.toNat - 32 ∨ sp.toNat + 8 ≤ inp.toNat
  outCode : entry.toNat + 70 ≤ out.toNat ∨ out.toNat + len ≤ entry.toNat
  frameCode : entry.toNat + 70 ≤ sp.toNat - 32 ∨ sp.toNat + 8 ≤ entry.toNat
  ctrWrite : base.memory.Permitted .write (sp.toNat - 32) 4
  ctrRead : base.memory.Permitted .read (sp.toNat - 32) 4
  outWrite : base.memory.Permitted .write out.toNat len
  outRead : base.memory.Permitted .read out.toNat len

/-! ## More numeric helpers -/

/-- Two consecutive RIP advances by literals collapse. -/
theorem rip_add (e : Word) (a b : Nat) :
    e + BitVec.ofNat 64 a + BitVec.ofNat 64 b = e + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    ← Nat.add_mod]

/-- Incrementing the loop counter in its 32-bit register view. -/
theorem ofNat_succ (i : Nat) :
    (BitVec.ofNat Sz.d.bits i + (1 : BitVec Sz.d.bits)) = BitVec.ofNat Sz.d.bits (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show (i % 2 ^ 32 + (1 : BitVec 32).toNat) % 2 ^ 32 = (i + 1) % 2 ^ 32
  rw [show (1 : BitVec 32).toNat = 1 % 2 ^ 32 from rfl, ← Nat.add_mod]

/-- The 32-bit unsigned compare the loop head performs. -/
theorem ult_ofNat {a b : Nat} (hab : a < b) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).ult (BitVec.ofNat 32 b) = true := by
  rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb]
  exact decide_eq_true hab

/-- Reading back a 32-bit counter stored into four frame bytes. -/
theorem ctr_roundtrip {k : Nat} (h : k < 2 ^ 32) :
    BitVec.ofNat 64 ((BitVec.ofNat 64 k).toNat % 2 ^ (8 * 4)) = BitVec.ofNat 64 k := by
  have h64 : k < 2 ^ 64 := Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, show 8 * 4 = 32 from rfl, Nat.mod_eq_of_lt h]

/-- What a one-byte store of the byte-register `dl` puts in memory: the byte
that was loaded into it. -/
theorem stored_byte (s : State) (r : Reg) {w : Word} (hw : w.toNat < 256) :
    BitVec.ofNat 64 (((Ext.writeByte s r (w.setWidth 8)).read r).toNat % 2 ^ (8 * 1)) = w := by
  have h8 : ((Ext.writeByte s r (w.setWidth 8)).read r).setWidth 8 = w.setWidth 8 :=
    Ext.writeByte_read_low s r (w.setWidth 8)
  have e1 : ((Ext.writeByte s r (w.setWidth 8)).read r).toNat % 2 ^ 8 = w.toNat % 2 ^ 8 := by
    rw [← BitVec.toNat_setWidth, ← BitVec.toNat_setWidth, h8]
  have hlt : w.toNat % 2 ^ 8 = w.toNat := by
    rw [show (2:Nat) ^ 8 = 256 from rfl]; exact Nat.mod_eq_of_lt hw
  rw [show 8 * 1 = 8 from rfl, e1, hlt]
  exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt w.isLt)

/-! ## The per-iteration body certificate -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **One iteration of the copy loop.** From a loop-head state having copied
`i < len` bytes, the machine advances to a loop-head state having copied
`i + 1`. This is the `body` argument of `Advances.loop`. -/
theorem iteration {entry exit sp out inp : Word} {len : Nat} {base m : MState} {i : Nat}
    (hS : Static entry sp out inp len base)
    (h : AtLoop entry sp out inp len base m i) (hlt : i < len) :
    ∃ m', Advances exit m m' ∧ AtLoop entry sp out inp len base m' (i + 1) := by
  obtain ⟨hrip, hrbp, hrsp, hslotI, hcopied, hframe, hile, hother⟩ := h
  have hsplow := hS.spLow
  have hlenLt := hS.lenLt
  have hdb : Sz.d.bytes = 4 := rfl
  have hqb : Sz.q.bytes = 8 := rfl
  have hcl : code.length = 70 := by decide
  -- ### frame addresses as naturals
  have hsp16 : (sp - 16#64).toNat = sp.toNat - 16 := toNat_sub_lit (k := 16) (by omega) (by omega)
  have hsp24 : (sp - 24#64).toNat = sp.toNat - 24 := toNat_sub_lit (k := 24) (by omega) (by omega)
  have hsp28 : (sp - 28#64).toNat = sp.toNat - 28 := toNat_sub_lit (k := 28) (by omega) (by omega)
  have hsp32 : (sp - 32#64).toNat = sp.toNat - 32 := toNat_sub_lit (k := 32) (by omega) (by omega)
  have hbufOut : ∀ j, j < len → (out + BitVec.ofNat 64 j).toNat = out.toNat + j := by
    intro j hj; exact toNat_add_lit (by have := hS.outBound; omega)
  have hbufIn : ∀ j, j < len → (inp + BitVec.ofNat 64 j).toNat = inp.toNat + j := by
    intro j hj; exact toNat_add_lit (by have := hS.inBound; omega)
  -- ### the loop's two written regions miss the code and the fixed frame slots
  have hcodeD1 : entry.toNat + code.length ≤ out.toNat ∨ out.toNat + len ≤ entry.toNat := by
    rw [hcl]; exact hS.outCode
  have hcodeD2 :
      entry.toNat + code.length ≤ sp.toNat - 32 ∨ (sp.toNat - 32) + 4 ≤ entry.toNat := by
    rw [hcl]
    rcases hS.frameCode with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by omega)
  have himg : Image code entry m.memory := Image.of_writesOnly₂ hS.image hframe hcodeD1 hcodeD2
  have keepSlot : ∀ (addr : Word) (k : Nat), sp.toNat - 28 ≤ addr.toNat →
      addr.toNat + k ≤ sp.toNat →
      Ext.loadN m.memory addr k = Ext.loadN base.memory addr k := by
    intro addr k h1 h2
    refine loadN_writesOnly₂ hframe addr k ?_ (Or.inr (by omega))
    rcases hS.outFrame with ho | ho
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hslotOut : Ext.loadN m.memory (sp - 16#64) 8 = some out := by
    rw [keepSlot _ _ (by rw [hsp16]; omega) (by rw [hsp16]; omega)]; exact hS.slotOut
  have hslotIn : Ext.loadN m.memory (sp - 24#64) 8 = some inp := by
    rw [keepSlot _ _ (by rw [hsp24]; omega) (by rw [hsp24]; omega)]; exact hS.slotIn
  have hslotLen : Ext.loadN m.memory (sp - 28#64) 4 = some (BitVec.ofNat 64 len) := by
    rw [keepSlot _ _ (by rw [hsp28]) (by rw [hsp28]; omega)]; exact hS.slotLen
  -- ### the input byte this iteration copies
  have hinKeep : Ext.loadN m.memory (inp + BitVec.ofNat 64 i) 1 =
      Ext.loadN base.memory (inp + BitVec.ofNat 64 i) 1 := by
    refine loadN_writesOnly₂ hframe _ 1 ?_ ?_
    · rw [hbufIn i hlt]
      rcases hS.apart with ha | ha
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    · rw [hbufIn i hlt]
      rcases hS.inFrame with hf | hf
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  obtain ⟨bval, hbval⟩ : ∃ w, Ext.loadN m.memory (inp + BitVec.ofNat 64 i) 1 = some w := by
    rw [hinKeep]; exact Option.isSome_iff_exists.mp (hS.inLoad i hlt)
  -- ### the loop head: load the counter, compare, fall through
  have hr₀ : m.core.rip.toNat = entry.toNat + 22 := by
    rw [hrip]; exact rip_at himg (by decide)
  obtain ⟨c₁, hc₁⟩ : ∃ c : State, c =
      { Sz.d.write m.core .rax (BitVec.ofNat Sz.d.bits i) with
        rip := m.core.rip +
          BitVec.ofNat 64 (Ext.Instr.load .d Reg.rax (frame 0xFFFFFFE8)).length } := ⟨_, rfl⟩
  have e₁ : Ext.exec (.load .d .rax (frame 0xFFFFFFE8)) m.core m.memory = .ok c₁ m.memory := by
    rw [Ext.exec_load, frame_addr, hrbp, aE8, hdb, hslotI]
    simp only [hc₁, narrow]
  have s₁ : Ext.stepOpt exit m = some ⟨c₁, m.memory⟩ :=
    retires_instr himg 22 (.load .d .rax (frame 0xFFFFFFE8)) hr₀
      (by decide) (by decide) (by decide) e₁
  have hrip₁ : c₁.rip = entry + BitVec.ofNat 64 25 := by
    rw [hc₁]; rw [M6, hrip, rip_add]
  have hrbp₁ : c₁.read .rbp = sp - 8#64 := by
    rw [hc₁, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rbp ≠ Reg.rax)]
    exact hrbp
  have hrax₁ : Sz.d.read c₁ .rax = BitVec.ofNat Sz.d.bits i := by
    simp only [hc₁, szRead_setRip, Sz.read_write]
  -- 25: cmp %eax, -0x14(%rbp)
  have hrm₂ : ∀ nxt : Word, Ext.readRM .d (.mem (frame 0xFFFFFFEC)) c₁ m.memory nxt =
      some (BitVec.ofNat Sz.d.bits len) := by
    intro nxt
    simp only [Ext.readRM, frame_addr, hrbp₁, aEC, hdb, hslotLen, Option.map_some, narrow]
  obtain ⟨c₂, hc₂⟩ : ∃ c : State, c =
      { c₁ with
        flags := Ext.subFlagsN (Sz.d.read c₁ .rax) (BitVec.ofNat Sz.d.bits len)
        rip := c₁.rip +
          BitVec.ofNat 64 (Ext.Instr.aluR .d .cmp Reg.rax
            (.mem (frame 0xFFFFFFEC))).length } := ⟨_, rfl⟩
  have e₂ : Ext.exec (.aluR .d .cmp .rax (.mem (frame 0xFFFFFFEC))) c₁ m.memory =
      .ok c₂ m.memory := by
    rw [hc₂]; exact exec_cmpR_mem .d .rax (frame 0xFFFFFFEC) c₁ m.memory (hrm₂ _)
  have hr₁ : c₁.rip.toNat = entry.toNat + 25 := by
    rw [hrip₁]; exact rip_at himg (by decide)
  have s₂ : Ext.stepOpt exit ⟨c₁, m.memory⟩ = some ⟨c₂, m.memory⟩ :=
    retires_instr (m := ⟨c₁, m.memory⟩) himg 25
      (.aluR .d .cmp .rax (.mem (frame 0xFFFFFFEC))) hr₁
      (by decide) (by decide) (by decide) e₂
  have hrip₂ : c₂.rip = entry + BitVec.ofNat 64 28 := by
    rw [hc₂]; rw [M7, hrip₁, rip_add]
  have hrbp₂ : c₂.read .rbp = sp - 8#64 := by
    rw [hc₂, read_setFlagsRip]; exact hrbp₁
  -- 28: jae 68 (not taken, since i < len)
  have hcond : Cond.ae.eval c₂.flags = some false := by
    have hf : c₂.flags =
        Ext.subFlagsN (BitVec.ofNat Sz.d.bits i) (BitVec.ofNat Sz.d.bits len) := by
      rw [hc₂]
      show Ext.subFlagsN (Sz.d.read c₁ .rax) _ = _
      rw [hrax₁]
    rw [hf]
    show Cond.ae.eval (Ext.subFlagsN (BitVec.ofNat 32 i) (BitVec.ofNat 32 len)) = some false
    rw [Ext.eval_after_cmp_d,
      show Cond.afterCmp (w := 31) (BitVec.ofNat 32 i) (BitVec.ofNat 32 len) Cond.ae =
        !(BitVec.ofNat 32 i).ult (BitVec.ofNat 32 len) from rfl,
      ult_ofNat hlt hS.lenLt]
    rfl
  obtain ⟨c₃, hc₃⟩ : ∃ c : State, c =
      { c₂ with rip := c₂.rip + BitVec.ofNat 64 (Ext.Instr.jcc .ae 0x22).length } := ⟨_, rfl⟩
  have e₃ : Ext.exec (.jcc .ae 0x22) c₂ m.memory = .ok c₃ m.memory := by
    rw [Ext.exec_jcc c₂ m.memory .ae 0x22 false hcond, hc₃]
    simp only [Bool.false_eq_true, ite_false]
  have hr₂ : c₂.rip.toNat = entry.toNat + 28 := by
    rw [hrip₂]; exact rip_at himg (by decide)
  have s₃ : Ext.stepOpt exit ⟨c₂, m.memory⟩ = some ⟨c₃, m.memory⟩ :=
    retires_instr (m := ⟨c₂, m.memory⟩) himg 28 (.jcc .ae 0x22) hr₂
      (by decide) (by decide) (by decide) e₃
  have hrip₃ : c₃.rip = entry + BitVec.ofNat 64 34 := by
    rw [hc₃]; rw [M8, hrip₂, rip_add]
  have hrbp₃ : c₃.read .rbp = sp - 8#64 := by
    rw [hc₃, read_setRip]; exact hrbp₂
  -- permissions transport along the frame, which keeps the region list
  have permOf : ∀ {acc : Process.Access} {ad l : Nat},
      base.memory.Permitted acc ad l → m.memory.Permitted acc ad l := by
    intro acc ad l hp
    rw [Memory.Permitted, X86.Memory.checkSpan_congr hframe.1]
    exact hp
  -- 34: mov -0x10(%rbp),%rax  — rax := input
  obtain ⟨c₄, hc₄⟩ : ∃ c : State, c =
      { Sz.q.write c₃ .rax (inp.setWidth Sz.q.bits) with
        rip := c₃.rip +
          BitVec.ofNat 64 (Ext.Instr.load .q Reg.rax (frame 0xFFFFFFF0)).length } := ⟨_, rfl⟩
  have e₄ : Ext.exec (.load .q .rax (frame 0xFFFFFFF0)) c₃ m.memory = .ok c₄ m.memory := by
    rw [Ext.exec_load, frame_addr, hrbp₃, aF0, hqb, hslotIn, hc₄]
  have hr₃ : c₃.rip.toNat = entry.toNat + 34 := by
    rw [hrip₃]; exact rip_at himg (by decide)
  have s₄ : Ext.stepOpt exit ⟨c₃, m.memory⟩ = some ⟨c₄, m.memory⟩ :=
    retires_instr (m := ⟨c₃, m.memory⟩) himg 34 (.load .q .rax (frame 0xFFFFFFF0)) hr₃
      (by decide) (by decide) (by decide) e₄
  have hrip₄ : c₄.rip = entry + BitVec.ofNat 64 38 := by
    rw [hc₄]; rw [M9, hrip₃, rip_add]
  have hrbp₄ : c₄.read .rbp = sp - 8#64 := by
    rw [hc₄, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rbp ≠ Reg.rax)]
    exact hrbp₃
  have hrax₄ : c₄.read .rax = inp := by
    rw [hc₄, read_setRip, read_szWrite_same]; simp
  -- 38: mov -0x18(%rbp),%ecx  — rcx := i
  obtain ⟨c₅, hc₅⟩ : ∃ c : State, c =
      { Sz.d.write c₄ .rcx (BitVec.ofNat Sz.d.bits i) with
        rip := c₄.rip +
          BitVec.ofNat 64 (Ext.Instr.load .d Reg.rcx (frame 0xFFFFFFE8)).length } := ⟨_, rfl⟩
  have e₅ : Ext.exec (.load .d .rcx (frame 0xFFFFFFE8)) c₄ m.memory = .ok c₅ m.memory := by
    rw [Ext.exec_load, frame_addr, hrbp₄, aE8, hdb, hslotI]
    simp only [hc₅, narrow]
  have hr₄ : c₄.rip.toNat = entry.toNat + 38 := by
    rw [hrip₄]; exact rip_at himg (by decide)
  have s₅ : Ext.stepOpt exit ⟨c₄, m.memory⟩ = some ⟨c₅, m.memory⟩ :=
    retires_instr (m := ⟨c₄, m.memory⟩) himg 38 (.load .d .rcx (frame 0xFFFFFFE8)) hr₄
      (by decide) (by decide) (by decide) e₅
  have hrip₅ : c₅.rip = entry + BitVec.ofNat 64 41 := by
    rw [hc₅]; rw [M10, hrip₄, rip_add]
  have hrbp₅ : c₅.read .rbp = sp - 8#64 := by
    rw [hc₅, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rbp ≠ Reg.rcx)]
    exact hrbp₄
  have hrax₅ : c₅.read .rax = inp := by
    rw [hc₅, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rax ≠ Reg.rcx)]
    exact hrax₄
  have hrcx₅ : c₅.read .rcx = BitVec.ofNat 64 i := by
    rw [hc₅, read_setRip, read_szWrite_same, widen i (by omega : i < 2 ^ 32)]
  -- 41: mov (%rax,%rcx,1),%dl  — dl := input[i]
  obtain ⟨c₆, hc₆⟩ : ∃ c : State, c =
      { Ext.writeByte c₅ .rdx (bval.setWidth 8) with
        rip := c₅.rip +
          BitVec.ofNat 64 (Ext.Instr.mov8 Reg.rdx
            (.mem (atIndex .rax .rcx (by decide)))).length } := ⟨_, rfl⟩
  have e₆ : Ext.exec (.mov8 .rdx (.mem (atIndex .rax .rcx (by decide)))) c₅ m.memory =
      .ok c₆ m.memory := by
    rw [exec_mov8_mem, index_addr, hrax₅, hrcx₅, hbval, hc₆]
  have hr₅ : c₅.rip.toNat = entry.toNat + 41 := by
    rw [hrip₅]; exact rip_at himg (by decide)
  have s₆ : Ext.stepOpt exit ⟨c₅, m.memory⟩ = some ⟨c₆, m.memory⟩ :=
    retires_instr (m := ⟨c₅, m.memory⟩) himg 41
      (.mov8 .rdx (.mem (atIndex .rax .rcx (by decide)))) hr₅
      (by decide) (by decide) (by decide) e₆
  have hrip₆ : c₆.rip = entry + BitVec.ofNat 64 44 := by
    rw [hc₆]; rw [M11, hrip₅, rip_add]
  have hrbp₆ : c₆.read .rbp = sp - 8#64 := by
    rw [hc₆, read_setRip,
      Ext.writeByte_read_other _ _ _ _ (by decide : Reg.rbp ≠ Reg.rdx)]
    exact hrbp₅
  -- 44: mov -0x8(%rbp),%rax  — rax := output
  obtain ⟨c₇, hc₇⟩ : ∃ c : State, c =
      { Sz.q.write c₆ .rax (out.setWidth Sz.q.bits) with
        rip := c₆.rip +
          BitVec.ofNat 64 (Ext.Instr.load .q Reg.rax (frame 0xFFFFFFF8)).length } := ⟨_, rfl⟩
  have e₇ : Ext.exec (.load .q .rax (frame 0xFFFFFFF8)) c₆ m.memory = .ok c₇ m.memory := by
    rw [Ext.exec_load, frame_addr, hrbp₆, aF8, hqb, hslotOut, hc₇]
  have hr₆ : c₆.rip.toNat = entry.toNat + 44 := by
    rw [hrip₆]; exact rip_at himg (by decide)
  have s₇ : Ext.stepOpt exit ⟨c₆, m.memory⟩ = some ⟨c₇, m.memory⟩ :=
    retires_instr (m := ⟨c₆, m.memory⟩) himg 44 (.load .q .rax (frame 0xFFFFFFF8)) hr₆
      (by decide) (by decide) (by decide) e₇
  have hrip₇ : c₇.rip = entry + BitVec.ofNat 64 48 := by
    rw [hc₇]; rw [M12, hrip₆, rip_add]
  have hrbp₇ : c₇.read .rbp = sp - 8#64 := by
    rw [hc₇, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rbp ≠ Reg.rax)]
    exact hrbp₆
  have hrax₇ : c₇.read .rax = out := by
    rw [hc₇, read_setRip, read_szWrite_same]; simp
  have hrdx₇ : c₇.read .rdx = c₆.read .rdx := by
    rw [hc₇, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rdx ≠ Reg.rax)]
  -- 48: mov -0x18(%rbp),%ecx  — rcx := i again
  obtain ⟨c₈, hc₈⟩ : ∃ c : State, c =
      { Sz.d.write c₇ .rcx (BitVec.ofNat Sz.d.bits i) with
        rip := c₇.rip +
          BitVec.ofNat 64 (Ext.Instr.load .d Reg.rcx (frame 0xFFFFFFE8)).length } := ⟨_, rfl⟩
  have e₈ : Ext.exec (.load .d .rcx (frame 0xFFFFFFE8)) c₇ m.memory = .ok c₈ m.memory := by
    rw [Ext.exec_load, frame_addr, hrbp₇, aE8, hdb, hslotI]
    simp only [hc₈, narrow]
  have hr₇ : c₇.rip.toNat = entry.toNat + 48 := by
    rw [hrip₇]; exact rip_at himg (by decide)
  have s₈ : Ext.stepOpt exit ⟨c₇, m.memory⟩ = some ⟨c₈, m.memory⟩ :=
    retires_instr (m := ⟨c₇, m.memory⟩) himg 48 (.load .d .rcx (frame 0xFFFFFFE8)) hr₇
      (by decide) (by decide) (by decide) e₈
  have hrip₈ : c₈.rip = entry + BitVec.ofNat 64 51 := by
    rw [hc₈]; rw [M10, hrip₇, rip_add]
  have hrbp₈ : c₈.read .rbp = sp - 8#64 := by
    rw [hc₈, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rbp ≠ Reg.rcx)]
    exact hrbp₇
  have hrax₈ : c₈.read .rax = out := by
    rw [hc₈, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rax ≠ Reg.rcx)]
    exact hrax₇
  have hrcx₈ : c₈.read .rcx = BitVec.ofNat 64 i := by
    rw [hc₈, read_setRip, read_szWrite_same, widen i (by omega : i < 2 ^ 32)]
  have hrdx₈ : c₈.read .rdx = c₆.read .rdx := by
    rw [hc₈, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rdx ≠ Reg.rcx)]
    exact hrdx₇
  -- 51: mov %dl,(%rax,%rcx,1)  — output[i] := dl
  have hnb : (Ext.Narrow.b).bytes = 1 := rfl
  have hstW : m.memory.Permitted .write (out + BitVec.ofNat 64 i).toNat 1 := by
    rw [hbufOut i hlt]
    exact permOf (permitted_sub hS.outWrite (off := i) (count := 1) (by omega) (by omega))
  have hstR : m.memory.Permitted .read (out + BitVec.ofNat 64 i).toNat 1 := by
    rw [hbufOut i hlt]
    exact permOf (permitted_sub hS.outRead (off := i) (count := 1) (by omega) (by omega))
  obtain ⟨mm₁, hst₁⟩ := storeN_isSome (memory := m.memory)
    (address := out + BitVec.ofNat 64 i) (k := 1) (v := c₈.read .rdx) hstW
  obtain ⟨c₉, hc₉⟩ : ∃ c : State, c =
      { c₈ with rip := c₈.rip +
        BitVec.ofNat 64 (Ext.Instr.store .b (.mem (atIndex .rax .rcx (by decide)))
          Reg.rdx).length } := ⟨_, rfl⟩
  have e₉ : Ext.exec (.store .b (.mem (atIndex .rax .rcx (by decide))) .rdx) c₈ m.memory =
      .ok c₉ mm₁ := by
    rw [Ext.exec_storeNarrow, index_addr, hrax₈, hrcx₈, hnb, hst₁, hc₉]
  have hr₈ : c₈.rip.toNat = entry.toNat + 51 := by
    rw [hrip₈]; exact rip_at himg (by decide)
  have s₉ : Ext.stepOpt exit ⟨c₈, m.memory⟩ = some ⟨c₉, mm₁⟩ :=
    retires_instr (m := ⟨c₈, m.memory⟩) himg 51
      (.store .b (.mem (atIndex .rax .rcx (by decide))) .rdx) hr₈
      (by decide) (by decide) (by decide) e₉
  have hwo₁ : Memory.WritesOnly m.memory mm₁ (out + BitVec.ofNat 64 i).toNat 1 :=
    Ext.storeN_writesOnly hst₁
  have himg₁ : Image code entry mm₁ := by
    refine Image.of_writesOnly himg hwo₁ ?_
    rw [hcl, hbufOut i hlt]
    rcases hS.outCode with hc | hc
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  -- the counter slot is untouched by the byte store
  have hctrDisj : (sp - 32#64).toNat + 4 ≤ (out + BitVec.ofNat 64 i).toNat ∨
      (out + BitVec.ofNat 64 i).toNat + 1 ≤ (sp - 32#64).toNat := by
    rw [hsp32, hbufOut i hlt]
    rcases hS.outFrame with ho | ho
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hslotI₁ : Ext.loadN mm₁ (sp - 32#64) 4 = some (BitVec.ofNat 64 i) := by
    rw [Ext.loadN_storeN_disjoint hst₁ hctrDisj]; exact hslotI
  have hrip₉ : c₉.rip = entry + BitVec.ofNat 64 54 := by
    rw [hc₉]; rw [M13, hrip₈, rip_add]
  have hrbp₉ : c₉.read .rbp = sp - 8#64 := by rw [hc₉, read_setRip]; exact hrbp₈
  -- 54: mov -0x18(%rbp),%eax
  obtain ⟨c₁₀, hc₁₀⟩ : ∃ c : State, c =
      { Sz.d.write c₉ .rax (BitVec.ofNat Sz.d.bits i) with
        rip := c₉.rip +
          BitVec.ofNat 64 (Ext.Instr.load .d Reg.rax (frame 0xFFFFFFE8)).length } := ⟨_, rfl⟩
  have e₁₀ : Ext.exec (.load .d .rax (frame 0xFFFFFFE8)) c₉ mm₁ = .ok c₁₀ mm₁ := by
    rw [Ext.exec_load, frame_addr, hrbp₉, aE8, hdb, hslotI₁]
    simp only [hc₁₀, narrow]
  have hr₉ : c₉.rip.toNat = entry.toNat + 54 := by
    rw [hrip₉]; exact rip_at himg₁ (by decide)
  have s₁₀ : Ext.stepOpt exit ⟨c₉, mm₁⟩ = some ⟨c₁₀, mm₁⟩ :=
    retires_instr (m := ⟨c₉, mm₁⟩) himg₁ 54 (.load .d .rax (frame 0xFFFFFFE8)) hr₉
      (by decide) (by decide) (by decide) e₁₀
  have hrip₁₀ : c₁₀.rip = entry + BitVec.ofNat 64 57 := by
    rw [hc₁₀]; rw [M6, hrip₉, rip_add]
  have hrbp₁₀ : c₁₀.read .rbp = sp - 8#64 := by
    rw [hc₁₀, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rbp ≠ Reg.rax)]
    exact hrbp₉
  have hrax₁₀ : Sz.d.read c₁₀ .rax = BitVec.ofNat Sz.d.bits i := by
    simp only [hc₁₀, szRead_setRip, Sz.read_write]
  -- 57: add $0x1,%eax
  obtain ⟨c₁₁, hc₁₁⟩ : ∃ c : State, c =
      { Sz.d.write c₁₀ .rax
          (Ext.AluOp.resultN .add (Sz.d.read c₁₀ .rax)
            ((1 : BitVec 8).signExtend Sz.d.bits)) with
        flags := Ext.AluOp.flagsN .add (Sz.d.read c₁₀ .rax)
          ((1 : BitVec 8).signExtend Sz.d.bits)
        rip := c₁₀.rip +
          BitVec.ofNat 64 (Ext.Instr.aluI8 .d .add (.reg Reg.rax) 1).length } := ⟨_, rfl⟩
  have e₁₁ : Ext.exec (.aluI8 .d .add (.reg .rax) 1) c₁₀ mm₁ = .ok c₁₁ mm₁ := by
    rw [hc₁₁]; exact Ext.exec_aluI8_reg c₁₀ mm₁ .d .add .rax 1 (by decide)
  have hr₁₀ : c₁₀.rip.toNat = entry.toNat + 57 := by
    rw [hrip₁₀]; exact rip_at himg₁ (by decide)
  have s₁₁ : Ext.stepOpt exit ⟨c₁₀, mm₁⟩ = some ⟨c₁₁, mm₁⟩ :=
    retires_instr (m := ⟨c₁₀, mm₁⟩) himg₁ 57 (.aluI8 .d .add (.reg .rax) 1) hr₁₀
      (by decide) (by decide) (by decide) e₁₁
  have hrip₁₁ : c₁₁.rip = entry + BitVec.ofNat 64 60 := by
    rw [hc₁₁]; rw [M14, hrip₁₀, rip_add]
  have hrbp₁₁ : c₁₁.read .rbp = sp - 8#64 := by
    rw [hc₁₁, read_setFlagsRip,
      Sz.read_write_other _ _ _ _ _ (by decide : Reg.rbp ≠ Reg.rax)]
    exact hrbp₁₀
  have hrax₁₁ : Sz.d.read c₁₁ .rax = BitVec.ofNat Sz.d.bits (i + 1) := by
    rw [hc₁₁]
    show Sz.d.read (Sz.d.write c₁₀ .rax _) .rax = _
    rw [Sz.read_write, hrax₁₀,
      show ((1 : BitVec 8).signExtend Sz.d.bits) = (1 : BitVec Sz.d.bits) from rfl,
      show Ext.AluOp.resultN .add (BitVec.ofNat Sz.d.bits i) (1 : BitVec Sz.d.bits) =
        BitVec.ofNat Sz.d.bits i + (1 : BitVec Sz.d.bits) from rfl, ofNat_succ]
  -- 60: mov %eax,-0x18(%rbp)  — i := i + 1
  have permOf₁ : ∀ {acc : Process.Access} {ad l : Nat},
      m.memory.Permitted acc ad l → mm₁.Permitted acc ad l := by
    intro acc ad l hp
    rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₁.1]
    exact hp
  have hctrW₁ : mm₁.Permitted .write (sp - 32#64).toNat 4 := by
    rw [hsp32]; exact permOf₁ (permOf hS.ctrWrite)
  have hctrR₁ : mm₁.Permitted .read (sp - 32#64).toNat 4 := by
    rw [hsp32]; exact permOf₁ (permOf hS.ctrRead)
  obtain ⟨mm₂, hst₂⟩ := storeN_isSome (memory := mm₁) (address := sp - 32#64) (k := 4)
    (v := (Sz.d.read c₁₁ .rax).setWidth 64) hctrW₁
  obtain ⟨c₁₂, hc₁₂⟩ : ∃ c : State, c =
      { c₁₁ with rip := c₁₁.rip +
        BitVec.ofNat 64 (Ext.Instr.mov .d (.mem (frame 0xFFFFFFE8)) Reg.rax).length } :=
    ⟨_, rfl⟩
  have e₁₂ : Ext.exec (.mov .d (.mem (frame 0xFFFFFFE8)) .rax) c₁₁ mm₁ = .ok c₁₂ mm₂ := by
    rw [Ext.exec_store, frame_addr, hrbp₁₁, aE8, hdb, hst₂, hc₁₂]
  have hr₁₁ : c₁₁.rip.toNat = entry.toNat + 60 := by
    rw [hrip₁₁]; exact rip_at himg₁ (by decide)
  have s₁₂ : Ext.stepOpt exit ⟨c₁₁, mm₁⟩ = some ⟨c₁₂, mm₂⟩ :=
    retires_instr (m := ⟨c₁₁, mm₁⟩) himg₁ 60 (.mov .d (.mem (frame 0xFFFFFFE8)) .rax) hr₁₁
      (by decide) (by decide) (by decide) e₁₂
  have hwo₂ : Memory.WritesOnly mm₁ mm₂ (sp - 32#64).toNat 4 := Ext.storeN_writesOnly hst₂
  have himg₂ : Image code entry mm₂ := by
    refine Image.of_writesOnly himg₁ hwo₂ ?_
    rw [hcl, hsp32]
    rcases hS.frameCode with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by omega)
  have hrip₁₂ : c₁₂.rip = entry + BitVec.ofNat 64 63 := by
    rw [hc₁₂]; rw [M15, hrip₁₁, rip_add]
  -- 63: jmp back to the loop head
  obtain ⟨c₁₃, hc₁₃⟩ : ∃ c : State, c =
      { c₁₂ with rip := c₁₂.rip + BitVec.ofNat 64 (Ext.Instr.jmp 0xFFFFFFD2).length +
        ((0xFFFFFFD2 : BitVec 32).signExtend 64) } := ⟨_, rfl⟩
  have e₁₃ : Ext.exec (.jmp 0xFFFFFFD2) c₁₂ mm₂ = .ok c₁₃ mm₂ := by
    rw [hc₁₃]; exact Ext.exec_jmp c₁₂ mm₂ 0xFFFFFFD2
  have hr₁₂ : c₁₂.rip.toNat = entry.toNat + 63 := by
    rw [hrip₁₂]; exact rip_at himg₂ (by decide)
  have s₁₃ : Ext.stepOpt exit ⟨c₁₂, mm₂⟩ = some ⟨c₁₃, mm₂⟩ :=
    retires_instr (m := ⟨c₁₂, mm₂⟩) himg₂ 63 (.jmp 0xFFFFFFD2) hr₁₂
      (by decide) (by decide) (by decide) e₁₃
  have hrip₁₃ : c₁₃.rip = entry + 22#64 := by
    rw [hc₁₃]
    show c₁₂.rip + BitVec.ofNat 64 (Ext.Instr.jmp 0xFFFFFFD2).length + _ = _
    rw [M16, hrip₁₂]
    exact jmpBack entry
  -- ### the registers the loop body leaves alone
  have hpres : ∀ r : Reg, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → c₁₃.read r = m.core.read r := by
    intro r h1 h2 h3
    rw [hc₁₃, read_setRip, hc₁₂, read_setRip, hc₁₁, read_setFlagsRip,
      Sz.read_write_other _ _ _ _ _ h1, hc₁₀, read_setRip,
      Sz.read_write_other _ _ _ _ _ h1, hc₉, read_setRip, hc₈, read_setRip,
      Sz.read_write_other _ _ _ _ _ h2, hc₇, read_setRip,
      Sz.read_write_other _ _ _ _ _ h1, hc₆, read_setRip,
      Ext.writeByte_read_other _ _ _ _ h3, hc₅, read_setRip,
      Sz.read_write_other _ _ _ _ _ h2, hc₄, read_setRip,
      Sz.read_write_other _ _ _ _ _ h1, hc₃, read_setRip, hc₂, read_setFlagsRip,
      hc₁, read_setRip, Sz.read_write_other _ _ _ _ _ h1]
  -- ### sequencing
  have a0 : Advances exit m ⟨c₁, m.memory⟩ := Advances.one s₁
  have a1 := a0.step s₂
  have a2 := a1.step s₃
  have a3 := a2.step s₄
  have a4 := a3.step s₅
  have a5 := a4.step s₆
  have a6 := a5.step s₇
  have a7 := a6.step s₈
  have a8 := a7.step s₉
  have a9 := a8.step s₁₀
  have a10 := a9.step s₁₁
  have a11 := a10.step s₁₂
  have a12 := a11.step s₁₃
  refine ⟨⟨c₁₃, mm₂⟩, a12, hrip₁₃, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · exact (hpres _ (by decide) (by decide) (by decide)).trans hrbp
  · exact (hpres _ (by decide) (by decide) (by decide)).trans hrsp
  · -- the counter slot now holds `i + 1`
    show Ext.loadN mm₂ (sp - 32#64) 4 = _
    rw [Ext.loadN_storeN hst₂ hctrR₁, hrax₁₁, widen (i + 1) (by omega),
      ctr_roundtrip (by omega)]
  · -- the first `i + 1` output bytes hold the first `i + 1` input bytes
    intro j hj
    show Ext.loadN mm₂ (out + BitVec.ofNat 64 j) 1 = _
    have hjlen : j < len := by omega
    have hbufDisj : (out + BitVec.ofNat 64 j).toNat + 1 ≤ (sp - 32#64).toNat ∨
        (sp - 32#64).toNat + 4 ≤ (out + BitVec.ofNat 64 j).toNat := by
      rw [hsp32, hbufOut j hjlen]
      rcases hS.outFrame with ho | ho
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [Ext.loadN_storeN_disjoint hst₂ hbufDisj]
    rcases Nat.lt_or_ge j i with hji | hji
    · -- an earlier byte: untouched by this iteration's store
      rw [Ext.loadN_storeN_disjoint hst₁
        (Or.inl (by rw [hbufOut j hjlen, hbufOut i hlt]; omega))]
      exact hcopied j hji
    · -- this iteration's byte
      have hje : j = i := by omega
      subst hje
      rw [Ext.loadN_storeN hst₁ hstR, hrdx₈, hc₆, read_setRip,
        stored_byte c₅ Reg.rdx (loadN_one_lt hbval), ← hinKeep]
      exact hbval.symm
  · -- the footprint: the output buffer and the counter slot, nothing else
    have f1 : WritesOnly₂ m.memory mm₁ out.toNat len (sp.toNat - 32) 4 :=
      writesOnly₂_of_left (writesOnly_widen hwo₁
        (by rw [hbufOut i hlt]; omega) (by rw [hbufOut i hlt]; omega))
    have f2 : WritesOnly₂ mm₁ mm₂ out.toNat len (sp.toNat - 32) 4 := by
      rw [hsp32] at hwo₂
      exact writesOnly₂_of_right hwo₂
    exact writesOnly₂_trans hframe (writesOnly₂_trans f1 f2)
  · intro r h1 h2 h3
    exact (hpres r h1 h2 h3).trans (hother r h1 h2 h3)

/-! ## The prologue -/

/-- Widening a 32-bit register value to 64 bits is `ofNat` of its value. -/
theorem setWidth64_ofNat (x : BitVec Sz.d.bits) :
    x.setWidth 64 = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat < 2 ^ 32 := x.isLt
  have h64 : x.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **The prologue.** From an ABI-conformant entry state, the six prologue
instructions set up the frame and reach the loop head with the counter at zero,
establishing the static side conditions the loop body needs. -/
theorem prologue {entry exit : Word} {m : MState} (h : Entry entry exit m) :
    ∃ base : MState,
      Advances exit m base ∧
      Static entry (m.core.read .rsp) (outOf m) (inOf m) (lenOf m) base ∧
      base.memory.readBytes ((m.core.read .rsp) - 8#64).toNat 8 =
        some (encodeWords [m.core.read .rbp]) ∧
      base.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [exit]) ∧
      AtLoop entry (m.core.read .rsp) (outOf m) (inOf m) (lenOf m) base base 0 ∧
      Memory.WritesOnly m.memory base.memory ((m.core.read .rsp).toNat - 32) 32 ∧
      (∀ r : Reg, r ≠ .rsp → r ≠ .rbp → base.core.read r = m.core.read r) ∧
      (∀ j, j < lenOf m → Ext.loadN base.memory (inOf m + BitVec.ofNat 64 j) 1 =
        Ext.loadN m.memory (inOf m + BitVec.ofNat 64 j) 1) := by
  obtain ⟨hrip, himage, hret, hfw, hfr, hsplow, houtW, houtR, hinR, hinL, houtB, hinB,
    hapart, houtF, hinF, houtC, hframeC⟩ := h
  set sp : Word := m.core.read .rsp with hspdef
  set out : Word := outOf m with houtdef
  set inp : Word := inOf m with hinpdef
  set len : Nat := lenOf m with hlendef
  have hlenLt : len < 2 ^ 32 := (Sz.d.read m.core .rdx).isLt
  have hcl : code.length = 70 := by decide
  have hdb : Sz.d.bytes = 4 := rfl
  have hqb : Sz.q.bytes = 8 := rfl
  have hsp8 : (sp - 8#64).toNat = sp.toNat - 8 := toNat_sub_lit (k := 8) (by omega) (by omega)
  have hsp16 : (sp - 16#64).toNat = sp.toNat - 16 := toNat_sub_lit (k := 16) (by omega) (by omega)
  have hsp24 : (sp - 24#64).toNat = sp.toNat - 24 := toNat_sub_lit (k := 24) (by omega) (by omega)
  have hsp28 : (sp - 28#64).toNat = sp.toNat - 28 := toNat_sub_lit (k := 28) (by omega) (by omega)
  have hsp32 : (sp - 32#64).toNat = sp.toNat - 32 := toNat_sub_lit (k := 32) (by omega) (by omega)
  -- every prologue write lands inside the 32 frame bytes, hence misses the code
  have hdis : ∀ a l : Nat, sp.toNat - 32 ≤ a → a + l ≤ sp.toNat →
      entry.toNat + code.length ≤ a ∨ a + l ≤ entry.toNat := by
    intro a l h1 h2
    rw [hcl]
    rcases hframeC with hc | hc
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have permW : ∀ off cnt : Nat, 0 < cnt → off + cnt ≤ 32 →
      m.memory.Permitted .write ((sp.toNat - 32) + off) cnt :=
    fun off cnt hpos hb => permitted_sub hfw hpos hb
  have permR : ∀ off cnt : Nat, 0 < cnt → off + cnt ≤ 32 →
      m.memory.Permitted .read ((sp.toNat - 32) + off) cnt :=
    fun off cnt hpos hb => permitted_sub hfr hpos hb
  -- 0: push %rbp
  have hpushW : m.memory.Permitted .write (sp - 8#64).toNat 8 := by
    rw [hsp8]
    have hp := permW 24 8 (by omega) (by omega)
    rwa [show sp.toNat - 32 + 24 = sp.toNat - 8 by omega] at hp
  have hpushR : m.memory.Permitted .read (sp - 8#64).toNat 8 := by
    rw [hsp8]
    have hp := permR 24 8 (by omega) (by omega)
    rwa [show sp.toNat - 32 + 24 = sp.toNat - 8 by omega] at hp
  obtain ⟨mem₁, hmem₁⟩ : ∃ mm : Memory, X86.pushWord m.core m.memory (m.core.read .rbp) =
      some (m.core.write .rsp (sp - 8#64), mm) := ⟨_, X86.pushWord_eq_some hpushW⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c : State, c =
      { m.core.write .rsp (sp - 8#64) with
        rip := m.core.rip + BitVec.ofNat 64 (X86.Insn.push Reg.rbp).length } := ⟨_, rfl⟩
  have e₁ : Ext.exec (.push .rbp) m.core m.memory = .ok c₁ mem₁ := by
    rw [Ext.exec_push, hc₁]
    simp only [X86.Insn.exec, hmem₁, Option.map_some]
  have hr₀ : m.core.rip.toNat = entry.toNat + 0 := by rw [hrip]; omega
  have s₁ : Ext.stepOpt exit m = some ⟨c₁, mem₁⟩ :=
    retires_instr himage 0 (.push .rbp) hr₀ (by decide) (by decide) (by decide) e₁
  have hwo₁ : Memory.WritesOnly m.memory mem₁ (sp - 8#64).toNat 8 :=
    X86.pushWord_writesOnly hmem₁
  have himg₁ : Image code entry mem₁ :=
    Image.of_writesOnly himage hwo₁ (by rw [hsp8]; exact hdis _ 8 (by omega) (by omega))
  have hrip₁ : c₁.rip = entry + BitVec.ofNat 64 1 := by
    rw [hc₁]; rw [M0, hrip]
  have hrsp₁ : c₁.read .rsp = sp - 8#64 := by rw [hc₁, read_setRip, State.read_write_same]
  have hoth₁ : ∀ r : Reg, r ≠ .rsp → c₁.read r = m.core.read r := by
    intro r hr; rw [hc₁, read_setRip, State.read_write_other _ _ _ _ hr]
  -- 1: mov %rsp,%rbp
  obtain ⟨c₂, hc₂⟩ : ∃ c : State, c =
      { Sz.q.write c₁ .rbp (Sz.q.read c₁ .rsp) with
        rip := c₁.rip +
          BitVec.ofNat 64 (Ext.Instr.mov .q (.reg Reg.rbp) Reg.rsp).length } := ⟨_, rfl⟩
  have e₂ : Ext.exec (.mov .q (.reg .rbp) .rsp) c₁ mem₁ = .ok c₂ mem₁ := by
    rw [hc₂]; exact Ext.exec_mov_reg c₁ mem₁ .q .rbp .rsp
  have hr₁ : c₁.rip.toNat = entry.toNat + 1 := by
    rw [hrip₁]; exact rip_at himg₁ (by decide)
  have s₂ : Ext.stepOpt exit ⟨c₁, mem₁⟩ = some ⟨c₂, mem₁⟩ :=
    retires_instr (m := ⟨c₁, mem₁⟩) himg₁ 1 (.mov .q (.reg .rbp) .rsp) hr₁
      (by decide) (by decide) (by decide) e₂
  have hrip₂ : c₂.rip = entry + BitVec.ofNat 64 4 := by rw [hc₂]; rw [M1, hrip₁, rip_add]
  have hrbp₂ : c₂.read .rbp = sp - 8#64 := by
    rw [hc₂, read_setRip, read_szWrite_same]
    show (Sz.q.read c₁ .rsp).setWidth 64 = _
    rw [Sz.read_q, hrsp₁]; simp
  have hrsp₂ : c₂.read .rsp = sp - 8#64 := by
    rw [hc₂, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rsp ≠ Reg.rbp)]
    exact hrsp₁
  have hoth₂ : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₂.read r = m.core.read r := by
    intro r h1 h2
    rw [hc₂, read_setRip, Sz.read_write_other _ _ _ _ _ h2]
    exact hoth₁ r h1
  -- 4: mov %rdi,-0x8(%rbp)   — the output pointer
  have hstW : ∀ (k off : Nat) (a : Word), a.toNat = sp.toNat - 32 + off → 0 < k →
      off + k ≤ 32 → mem₁.Permitted .write a.toNat k := by
    intro k off a ha hpos hb
    rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₁.1, ha]
    exact permW off k hpos hb
  have hstR : ∀ (k off : Nat) (a : Word), a.toNat = sp.toNat - 32 + off → 0 < k →
      off + k ≤ 32 → mem₁.Permitted .read a.toNat k := by
    intro k off a ha hpos hb
    rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₁.1, ha]
    exact permR off k hpos hb
  obtain ⟨mem₂, hst₂⟩ := storeN_isSome (memory := mem₁) (address := sp - 16#64) (k := 8)
    (v := (Sz.q.read c₂ .rdi).setWidth 64)
    (hstW 8 16 _ (by rw [hsp16]; omega) (by omega) (by omega))
  obtain ⟨c₃, hc₃⟩ : ∃ c : State, c =
      { c₂ with rip := c₂.rip +
        BitVec.ofNat 64 (Ext.Instr.mov .q (.mem (frame 0xFFFFFFF8)) Reg.rdi).length }
    := ⟨_, rfl⟩
  have e₃ : Ext.exec (.mov .q (.mem (frame 0xFFFFFFF8)) .rdi) c₂ mem₁ = .ok c₃ mem₂ := by
    rw [Ext.exec_store, frame_addr, hrbp₂, aF8, hqb, hst₂, hc₃]
  have hr₂ : c₂.rip.toNat = entry.toNat + 4 := by
    rw [hrip₂]; exact rip_at himg₁ (by decide)
  have s₃ : Ext.stepOpt exit ⟨c₂, mem₁⟩ = some ⟨c₃, mem₂⟩ :=
    retires_instr (m := ⟨c₂, mem₁⟩) himg₁ 4 (.mov .q (.mem (frame 0xFFFFFFF8)) .rdi) hr₂
      (by decide) (by decide) (by decide) e₃
  have hwo₂ : Memory.WritesOnly mem₁ mem₂ (sp - 16#64).toNat 8 := Ext.storeN_writesOnly hst₂
  have himg₂ : Image code entry mem₂ :=
    Image.of_writesOnly himg₁ hwo₂ (by rw [hsp16]; exact hdis _ 8 (by omega) (by omega))
  have hrip₃ : c₃.rip = entry + BitVec.ofNat 64 8 := by rw [hc₃]; rw [M2, hrip₂, rip_add]
  have hrbp₃ : c₃.read .rbp = sp - 8#64 := by rw [hc₃, read_setRip]; exact hrbp₂
  have hrsp₃ : c₃.read .rsp = sp - 8#64 := by rw [hc₃, read_setRip]; exact hrsp₂
  have hoth₃ : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₃.read r = m.core.read r := by
    intro r h1 h2; rw [hc₃, read_setRip]; exact hoth₂ r h1 h2
  -- 8: mov %rsi,-0x10(%rbp)  — the input pointer
  obtain ⟨mem₃, hst₃⟩ := storeN_isSome (memory := mem₂) (address := sp - 24#64) (k := 8)
    (v := (Sz.q.read c₃ .rsi).setWidth 64)
    (by rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₂.1]
        exact hstW 8 8 _ (by rw [hsp24]; omega) (by omega) (by omega))
  obtain ⟨c₄, hc₄⟩ : ∃ c : State, c =
      { c₃ with rip := c₃.rip +
        BitVec.ofNat 64 (Ext.Instr.mov .q (.mem (frame 0xFFFFFFF0)) Reg.rsi).length }
    := ⟨_, rfl⟩
  have e₄ : Ext.exec (.mov .q (.mem (frame 0xFFFFFFF0)) .rsi) c₃ mem₂ = .ok c₄ mem₃ := by
    rw [Ext.exec_store, frame_addr, hrbp₃, aF0, hqb, hst₃, hc₄]
  have hr₃ : c₃.rip.toNat = entry.toNat + 8 := by
    rw [hrip₃]; exact rip_at himg₂ (by decide)
  have s₄ : Ext.stepOpt exit ⟨c₃, mem₂⟩ = some ⟨c₄, mem₃⟩ :=
    retires_instr (m := ⟨c₃, mem₂⟩) himg₂ 8 (.mov .q (.mem (frame 0xFFFFFFF0)) .rsi) hr₃
      (by decide) (by decide) (by decide) e₄
  have hwo₃ : Memory.WritesOnly mem₂ mem₃ (sp - 24#64).toNat 8 := Ext.storeN_writesOnly hst₃
  have himg₃ : Image code entry mem₃ :=
    Image.of_writesOnly himg₂ hwo₃ (by rw [hsp24]; exact hdis _ 8 (by omega) (by omega))
  have hrip₄ : c₄.rip = entry + BitVec.ofNat 64 12 := by rw [hc₄]; rw [M3, hrip₃, rip_add]
  have hrbp₄ : c₄.read .rbp = sp - 8#64 := by rw [hc₄, read_setRip]; exact hrbp₃
  have hrsp₄ : c₄.read .rsp = sp - 8#64 := by rw [hc₄, read_setRip]; exact hrsp₃
  have hoth₄ : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₄.read r = m.core.read r := by
    intro r h1 h2; rw [hc₄, read_setRip]; exact hoth₃ r h1 h2
  -- 12: mov %edx,-0x14(%rbp)  — the length
  obtain ⟨mem₄, hst₄⟩ := storeN_isSome (memory := mem₃) (address := sp - 28#64) (k := 4)
    (v := (Sz.d.read c₄ .rdx).setWidth 64)
    (by rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₃.1,
          X86.Memory.checkSpan_congr hwo₂.1]
        exact hstW 4 4 _ (by rw [hsp28]; omega) (by omega) (by omega))
  obtain ⟨c₅, hc₅⟩ : ∃ c : State, c =
      { c₄ with rip := c₄.rip +
        BitVec.ofNat 64 (Ext.Instr.mov .d (.mem (frame 0xFFFFFFEC)) Reg.rdx).length }
    := ⟨_, rfl⟩
  have e₅ : Ext.exec (.mov .d (.mem (frame 0xFFFFFFEC)) .rdx) c₄ mem₃ = .ok c₅ mem₄ := by
    rw [Ext.exec_store, frame_addr, hrbp₄, aEC, hdb, hst₄, hc₅]
  have hr₄ : c₄.rip.toNat = entry.toNat + 12 := by
    rw [hrip₄]; exact rip_at himg₃ (by decide)
  have s₅ : Ext.stepOpt exit ⟨c₄, mem₃⟩ = some ⟨c₅, mem₄⟩ :=
    retires_instr (m := ⟨c₄, mem₃⟩) himg₃ 12 (.mov .d (.mem (frame 0xFFFFFFEC)) .rdx) hr₄
      (by decide) (by decide) (by decide) e₅
  have hwo₄ : Memory.WritesOnly mem₃ mem₄ (sp - 28#64).toNat 4 := Ext.storeN_writesOnly hst₄
  have himg₄ : Image code entry mem₄ :=
    Image.of_writesOnly himg₃ hwo₄ (by rw [hsp28]; exact hdis _ 4 (by omega) (by omega))
  have hrip₅ : c₅.rip = entry + BitVec.ofNat 64 15 := by rw [hc₅]; rw [M4, hrip₄, rip_add]
  have hrbp₅ : c₅.read .rbp = sp - 8#64 := by rw [hc₅, read_setRip]; exact hrbp₄
  have hrsp₅ : c₅.read .rsp = sp - 8#64 := by rw [hc₅, read_setRip]; exact hrsp₄
  have hoth₅ : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₅.read r = m.core.read r := by
    intro r h1 h2; rw [hc₅, read_setRip]; exact hoth₄ r h1 h2
  -- 15: movl $0x0,-0x18(%rbp)  — the loop counter
  obtain ⟨mem₅, hst₅⟩ := storeN_isSome (memory := mem₄) (address := sp - 32#64) (k := 4)
    (v := (((0 : BitVec 32).signExtend Sz.d.bits).setWidth 64))
    (by rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₄.1,
          X86.Memory.checkSpan_congr hwo₃.1, X86.Memory.checkSpan_congr hwo₂.1]
        exact hstW 4 0 _ (by rw [hsp32]; omega) (by omega) (by omega))
  obtain ⟨c₆, hc₆⟩ : ∃ c : State, c =
      { c₅ with rip := c₅.rip +
        BitVec.ofNat 64 (Ext.Instr.movI .d (.mem (frame 0xFFFFFFE8)) 0).length } := ⟨_, rfl⟩
  have e₆ : Ext.exec (.movI .d (.mem (frame 0xFFFFFFE8)) 0) c₅ mem₄ = .ok c₆ mem₅ := by
    rw [exec_movI_mem, frame_addr, hrbp₅, aE8, hdb, hst₅, hc₆]
  have hr₅ : c₅.rip.toNat = entry.toNat + 15 := by
    rw [hrip₅]; exact rip_at himg₄ (by decide)
  have s₆ : Ext.stepOpt exit ⟨c₅, mem₄⟩ = some ⟨c₆, mem₅⟩ :=
    retires_instr (m := ⟨c₅, mem₄⟩) himg₄ 15 (.movI .d (.mem (frame 0xFFFFFFE8)) 0) hr₅
      (by decide) (by decide) (by decide) e₆
  have hwo₅ : Memory.WritesOnly mem₄ mem₅ (sp - 32#64).toNat 4 := Ext.storeN_writesOnly hst₅
  have himg₅ : Image code entry mem₅ :=
    Image.of_writesOnly himg₄ hwo₅ (by rw [hsp32]; exact hdis _ 4 (by omega) (by omega))
  have hrip₆ : c₆.rip = entry + BitVec.ofNat 64 22 := by rw [hc₆]; rw [M5, hrip₅, rip_add]
  have hrbp₆ : c₆.read .rbp = sp - 8#64 := by rw [hc₆, read_setRip]; exact hrbp₅
  have hrsp₆ : c₆.read .rsp = sp - 8#64 := by rw [hc₆, read_setRip]; exact hrsp₅
  have hoth₆ : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₆.read r = m.core.read r := by
    intro r h1 h2; rw [hc₆, read_setRip]; exact hoth₅ r h1 h2
  -- ### permissions and reads survive the five prologue writes
  have transp : ∀ {acc : Process.Access} {ad l : Nat},
      m.memory.Permitted acc ad l → mem₅.Permitted acc ad l := by
    intro acc ad l hp
    rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₅.1,
      X86.Memory.checkSpan_congr hwo₄.1, X86.Memory.checkSpan_congr hwo₃.1,
      X86.Memory.checkSpan_congr hwo₂.1, X86.Memory.checkSpan_congr hwo₁.1]
    exact hp
  have loadPush : ∀ (a : Word) (k : Nat),
      a.toNat + k ≤ (sp - 8#64).toNat ∨ (sp - 8#64).toNat + 8 ≤ a.toNat →
      Ext.loadN mem₁ a k = Ext.loadN m.memory a k := by
    intro a k hd
    simp only [Ext.loadN, Memory.readBytes,
      X86.Memory.readWith_writesOnly hwo₁ .read a.toNat k hd]
  have readKeep : ∀ (a k : Nat), sp.toNat ≤ a →
      mem₅.readWith .read a k = m.memory.readWith .read a k := by
    intro a k hd
    rw [X86.Memory.readWith_writesOnly hwo₅ .read a k (Or.inr (by rw [hsp32]; omega)),
      X86.Memory.readWith_writesOnly hwo₄ .read a k (Or.inr (by rw [hsp28]; omega)),
      X86.Memory.readWith_writesOnly hwo₃ .read a k (Or.inr (by rw [hsp24]; omega)),
      X86.Memory.readWith_writesOnly hwo₂ .read a k (Or.inr (by rw [hsp16]; omega)),
      X86.Memory.readWith_writesOnly hwo₁ .read a k (Or.inr (by rw [hsp8]; omega))]
  have hRet : mem₅.readBytes sp.toNat 8 = some (encodeWords [exit]) := by
    show mem₅.readWith .read _ 8 = _
    rw [readKeep _ _ (by omega)]; exact hret
  have hSaved : mem₅.readBytes (sp - 8#64).toNat 8 = some (encodeWords [m.core.read .rbp]) := by
    show mem₅.readWith .read _ 8 = _
    rw [X86.Memory.readWith_writesOnly hwo₅ .read _ 8 (Or.inr (by rw [hsp8, hsp32]; omega)),
      X86.Memory.readWith_writesOnly hwo₄ .read _ 8 (Or.inr (by rw [hsp8, hsp28]; omega)),
      X86.Memory.readWith_writesOnly hwo₃ .read _ 8 (Or.inr (by rw [hsp8, hsp24]; omega)),
      X86.Memory.readWith_writesOnly hwo₂ .read _ 8 (Or.inr (by rw [hsp8, hsp16]; omega))]
    exact X86.pushWord_readBytes hmem₁ hpushR
  -- ### the four frame slots, read back
  have hslotOut : Ext.loadN mem₅ (sp - 16#64) 8 = some out := by
    rw [Ext.loadN_storeN_disjoint hst₅ (Or.inr (by rw [hsp16, hsp32]; omega)),
      Ext.loadN_storeN_disjoint hst₄ (Or.inr (by rw [hsp16, hsp28]; omega)),
      Ext.loadN_storeN_disjoint hst₃ (Or.inr (by rw [hsp16, hsp24]; omega)),
      Ext.loadN_storeN_eight hst₂ (hstR 8 16 _ (by rw [hsp16]; omega) (by omega) (by omega))]
    rw [show Sz.q.read c₂ .rdi = c₂.read .rdi from Sz.read_q _ _, hoth₂ .rdi (by decide)
      (by decide)]
    simp [houtdef, outOf]
  have hslotIn : Ext.loadN mem₅ (sp - 24#64) 8 = some inp := by
    rw [Ext.loadN_storeN_disjoint hst₅ (Or.inr (by rw [hsp24, hsp32]; omega)),
      Ext.loadN_storeN_disjoint hst₄ (Or.inr (by rw [hsp24, hsp28]; omega)),
      Ext.loadN_storeN_eight hst₃
        (by rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₂.1]
            exact hstR 8 8 _ (by rw [hsp24]; omega) (by omega) (by omega))]
    rw [show Sz.q.read c₃ .rsi = c₃.read .rsi from Sz.read_q _ _, hoth₃ .rsi (by decide)
      (by decide)]
    simp [hinpdef, inOf]
  have hslotLen : Ext.loadN mem₅ (sp - 28#64) 4 = some (BitVec.ofNat 64 len) := by
    rw [Ext.loadN_storeN_disjoint hst₅ (Or.inr (by rw [hsp28, hsp32]; omega)),
      Ext.loadN_storeN hst₄
        (by rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₃.1,
              X86.Memory.checkSpan_congr hwo₂.1]
            exact hstR 4 4 _ (by rw [hsp28]; omega) (by omega) (by omega))]
    have hdx : Sz.d.read c₄ .rdx = Sz.d.read m.core .rdx := by
      simp only [Sz.read, hoth₄ .rdx (by decide) (by decide)]
    rw [hdx, setWidth64_ofNat, ctr_roundtrip (Sz.d.read m.core Reg.rdx).isLt]
    rfl
  have hslotI : Ext.loadN mem₅ (sp - 32#64) 4 = some (BitVec.ofNat 64 0) := by
    rw [Ext.loadN_storeN hst₅
      (by rw [Memory.Permitted, X86.Memory.checkSpan_congr hwo₄.1,
            X86.Memory.checkSpan_congr hwo₃.1, X86.Memory.checkSpan_congr hwo₂.1]
          exact hstR 4 0 _ (by rw [hsp32]; omega) (by omega) (by omega))]
    rfl
  -- ### the input bytes survive the prologue
  have hinEq : ∀ j, j < len → Ext.loadN mem₅ (inp + BitVec.ofNat 64 j) 1 =
      Ext.loadN m.memory (inp + BitVec.ofNat 64 j) 1 := by
    intro j hj
    have hjn : (inp + BitVec.ofNat 64 j).toNat = inp.toNat + j :=
      toNat_add_lit (by have := hinB; omega)
    have hd : ∀ (a : Word) (l : Nat), sp.toNat - 32 ≤ a.toNat → a.toNat + l ≤ sp.toNat →
        (inp + BitVec.ofNat 64 j).toNat + 1 ≤ a.toNat ∨
          a.toNat + l ≤ (inp + BitVec.ofNat 64 j).toNat := by
      intro a l h1 h2
      rw [hjn]
      rcases hinF with hf | hf
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [Ext.loadN_storeN_disjoint hst₅
        (hd (sp - 32#64) 4 (by rw [hsp32]) (by rw [hsp32]; omega)),
      Ext.loadN_storeN_disjoint hst₄
        (hd (sp - 28#64) 4 (by rw [hsp28]; omega) (by rw [hsp28]; omega)),
      Ext.loadN_storeN_disjoint hst₃
        (hd (sp - 24#64) 8 (by rw [hsp24]; omega) (by rw [hsp24]; omega)),
      Ext.loadN_storeN_disjoint hst₂
        (hd (sp - 16#64) 8 (by rw [hsp16]; omega) (by rw [hsp16]; omega)),
      loadPush _ 1 (hd (sp - 8#64) 8 (by rw [hsp8]; omega) (by rw [hsp8]; omega))]
  have hinLoad : ∀ j, j < len → (Ext.loadN mem₅ (inp + BitVec.ofNat 64 j) 1).isSome := by
    intro j hj; rw [hinEq j hj]; exact hinL j hj
  -- ### the prologue's own footprint
  have hpframe : Memory.WritesOnly m.memory mem₅ (sp.toNat - 32) 32 := by
    refine writesOnly_trans (writesOnly_trans (writesOnly_trans (writesOnly_trans
      (writesOnly_widen hwo₁ (by rw [hsp8]; omega) (by rw [hsp8]; omega))
      (writesOnly_widen hwo₂ (by rw [hsp16]; omega) (by rw [hsp16]; omega)))
      (writesOnly_widen hwo₃ (by rw [hsp24]; omega) (by rw [hsp24]; omega)))
      (writesOnly_widen hwo₄ (by rw [hsp28]; omega) (by rw [hsp28]; omega)))
      (writesOnly_widen hwo₅ (by rw [hsp32]) (by rw [hsp32]; omega))
  -- ### sequencing
  have a0 : Advances exit m ⟨c₁, mem₁⟩ := Advances.one s₁
  have a1 := a0.step s₂
  have a2 := a1.step s₃
  have a3 := a2.step s₄
  have a4 := a3.step s₅
  have a5 := a4.step s₆
  refine ⟨⟨c₆, mem₅⟩, a5, ⟨himg₅, hslotOut, hslotIn, hslotLen, hinLoad, hsplow, ?_, houtB,
    hinB, hlenLt, hapart, houtF, hinF, houtC, hframeC, ?_, ?_, transp houtW, transp houtR⟩,
    hSaved, hRet, ⟨hrip₆, hrbp₆, hrsp₆, ?_, by intro j hj; omega, ⟨rfl, fun _ _ _ => rfl⟩,
      by omega, fun _ _ _ _ => rfl⟩, hpframe, hoth₆, hinEq⟩
  · -- `sp.toNat + 8 ≤ 2 ^ 64`
    have := Memory.readWith_permitted hret
    rw [Memory.Permitted, Memory.checkSpan_iff] at this
    exact this.2.1
  · exact transp (by have := permW 0 4 (by omega) (by omega); rwa [Nat.add_zero] at this)
  · exact transp (by have := permR 0 4 (by omega) (by omega); rwa [Nat.add_zero] at this)
  · show Ext.loadN mem₅ (sp - 32#64) 4 = _
    exact hslotI

/-! ## The exit certificate -/

/-- Popping the saved `rbp` restores the entry stack pointer. -/
theorem sp_restore (x : Word) : x - 8#64 + 8#64 = x := by
  have hz : (-(8#64) : BitVec 64) + 8#64 = 0#64 := by decide
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, hz, BitVec.add_zero]

/-- At the loop head with `i = len`, the `jae` is taken. -/
theorem jae_taken (len : Nat) :
    Cond.ae.eval (Ext.subFlagsN (BitVec.ofNat 32 len) (BitVec.ofNat 32 len)) = some true := by
  rw [Ext.eval_after_cmp_d,
    show Cond.afterCmp (w := 31) (BitVec.ofNat 32 len) (BitVec.ofNat 32 len) Cond.ae =
      !(BitVec.ofNat 32 len).ult (BitVec.ofNat 32 len) from rfl,
    show (BitVec.ofNat 32 len).ult (BitVec.ofNat 32 len) = false from by
      rw [BitVec.ult_eq_decide]; exact decide_eq_false (by omega)]
  rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **The loop exits and the function returns.** From a loop-head state with the
counter at `len`, the compare takes the `jae`, the epilogue pops `rbp` and the
`ret` returns to the caller. -/
theorem epilogue {entry exit sp out inp bp0 : Word} {len : Nat} {base m : MState}
    (hS : Static entry sp out inp len base)
    (hbSaved : base.memory.readBytes (sp - 8#64).toNat 8 = some (encodeWords [bp0]))
    (hbRet : base.memory.readBytes sp.toNat 8 = some (encodeWords [exit]))
    (h : AtLoop entry sp out inp len base m len) :
    ∃ final, Ext.Returns exit m final ∧ final.core.rip = exit ∧
      final.core.read .rsp = sp + 8#64 ∧ final.core.read .rbp = bp0 ∧
      (∀ r : Reg, r ≠ .rax → r ≠ .rsp → r ≠ .rbp → final.core.read r = m.core.read r) ∧
      final.memory = m.memory := by
  obtain ⟨hrip, hrbp, hrsp, hslotI, hcopied, hframe, hile, hother⟩ := h
  have hsplow := hS.spLow
  have hlenLt := hS.lenLt
  have hdb : Sz.d.bytes = 4 := rfl
  have hcl : code.length = 70 := by decide
  have hsp8 : (sp - 8#64).toNat = sp.toNat - 8 := toNat_sub_lit (k := 8) (by omega) (by omega)
  have hsp28 : (sp - 28#64).toNat = sp.toNat - 28 := toNat_sub_lit (k := 28) (by omega) (by omega)
  have hsp32 : (sp - 32#64).toNat = sp.toNat - 32 := toNat_sub_lit (k := 32) (by omega) (by omega)
  have hcodeD1 : entry.toNat + code.length ≤ out.toNat ∨ out.toNat + len ≤ entry.toNat := by
    rw [hcl]; exact hS.outCode
  have hcodeD2 :
      entry.toNat + code.length ≤ sp.toNat - 32 ∨ (sp.toNat - 32) + 4 ≤ entry.toNat := by
    rw [hcl]
    rcases hS.frameCode with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by omega)
  have himg : Image code entry m.memory := Image.of_writesOnly₂ hS.image hframe hcodeD1 hcodeD2
  -- the `len` slot and the two stack words survive the loop
  have keepRead : ∀ (a k : Nat), sp.toNat - 28 ≤ a → a + k ≤ sp.toNat + 8 →
      m.memory.readWith .read a k = base.memory.readWith .read a k := by
    intro a k h1 h2
    refine readWith_writesOnly₂ hframe .read a k ?_ (Or.inr (by omega))
    rcases hS.outFrame with ho | ho
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hslotLen : Ext.loadN m.memory (sp - 28#64) 4 = some (BitVec.ofNat 64 len) := by
    refine (loadN_writesOnly₂ hframe (sp - 28#64) 4 ?_ (Or.inr (by rw [hsp28]; omega))).trans
      hS.slotLen
    rw [hsp28]
    rcases hS.outFrame with ho | ho
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hSaved : m.memory.readBytes (sp - 8#64).toNat 8 = some (encodeWords [bp0]) := by
    show m.memory.readWith .read _ 8 = _
    rw [keepRead _ _ (by rw [hsp8]; omega) (by rw [hsp8]; omega)]; exact hbSaved
  have hRet : m.memory.readBytes sp.toNat 8 = some (encodeWords [exit]) := by
    show m.memory.readWith .read _ 8 = _
    rw [keepRead _ _ (by omega) (by omega)]; exact hbRet
  -- 22: load the counter (now `len`)
  have hr₀ : m.core.rip.toNat = entry.toNat + 22 := by
    rw [hrip]; exact rip_at himg (by decide)
  obtain ⟨c₁, hc₁⟩ : ∃ c : State, c =
      { Sz.d.write m.core .rax (BitVec.ofNat Sz.d.bits len) with
        rip := m.core.rip +
          BitVec.ofNat 64 (Ext.Instr.load .d Reg.rax (frame 0xFFFFFFE8)).length } := ⟨_, rfl⟩
  have e₁ : Ext.exec (.load .d .rax (frame 0xFFFFFFE8)) m.core m.memory = .ok c₁ m.memory := by
    rw [Ext.exec_load, frame_addr, hrbp, aE8, hdb, hslotI]
    simp only [hc₁, narrow]
  have s₁ : Ext.stepOpt exit m = some ⟨c₁, m.memory⟩ :=
    retires_instr himg 22 (.load .d .rax (frame 0xFFFFFFE8)) hr₀
      (by decide) (by decide) (by decide) e₁
  have hrip₁ : c₁.rip = entry + BitVec.ofNat 64 25 := by rw [hc₁]; rw [M6, hrip, rip_add]
  have hrbp₁ : c₁.read .rbp = sp - 8#64 := by
    rw [hc₁, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rbp ≠ Reg.rax)]
    exact hrbp
  have hrsp₁ : c₁.read .rsp = sp - 8#64 := by
    rw [hc₁, read_setRip, Sz.read_write_other _ _ _ _ _ (by decide : Reg.rsp ≠ Reg.rax)]
    exact hrsp
  have hrax₁ : Sz.d.read c₁ .rax = BitVec.ofNat Sz.d.bits len := by
    simp only [hc₁, szRead_setRip, Sz.read_write]
  -- 25: compare it with `len`
  have hrm₂ : ∀ nxt : Word, Ext.readRM .d (.mem (frame 0xFFFFFFEC)) c₁ m.memory nxt =
      some (BitVec.ofNat Sz.d.bits len) := by
    intro nxt
    simp only [Ext.readRM, frame_addr, hrbp₁, aEC, hdb, hslotLen, Option.map_some, narrow]
  obtain ⟨c₂, hc₂⟩ : ∃ c : State, c =
      { c₁ with
        flags := Ext.subFlagsN (Sz.d.read c₁ .rax) (BitVec.ofNat Sz.d.bits len)
        rip := c₁.rip +
          BitVec.ofNat 64 (Ext.Instr.aluR .d .cmp Reg.rax
            (.mem (frame 0xFFFFFFEC))).length } := ⟨_, rfl⟩
  have e₂ : Ext.exec (.aluR .d .cmp .rax (.mem (frame 0xFFFFFFEC))) c₁ m.memory =
      .ok c₂ m.memory := by
    rw [hc₂]; exact exec_cmpR_mem .d .rax (frame 0xFFFFFFEC) c₁ m.memory (hrm₂ _)
  have hr₁ : c₁.rip.toNat = entry.toNat + 25 := by
    rw [hrip₁]; exact rip_at himg (by decide)
  have s₂ : Ext.stepOpt exit ⟨c₁, m.memory⟩ = some ⟨c₂, m.memory⟩ :=
    retires_instr (m := ⟨c₁, m.memory⟩) himg 25
      (.aluR .d .cmp .rax (.mem (frame 0xFFFFFFEC))) hr₁
      (by decide) (by decide) (by decide) e₂
  have hrip₂ : c₂.rip = entry + BitVec.ofNat 64 28 := by rw [hc₂]; rw [M7, hrip₁, rip_add]
  have hrbp₂ : c₂.read .rbp = sp - 8#64 := by rw [hc₂, read_setFlagsRip]; exact hrbp₁
  have hrsp₂ : c₂.read .rsp = sp - 8#64 := by rw [hc₂, read_setFlagsRip]; exact hrsp₁
  -- 28: the `jae` is taken, to 68
  have hcond : Cond.ae.eval c₂.flags = some true := by
    have hf : c₂.flags =
        Ext.subFlagsN (BitVec.ofNat Sz.d.bits len) (BitVec.ofNat Sz.d.bits len) := by
      rw [hc₂]
      show Ext.subFlagsN (Sz.d.read c₁ .rax) _ = _
      rw [hrax₁]
    rw [hf]
    show Cond.ae.eval (Ext.subFlagsN (BitVec.ofNat 32 len) (BitVec.ofNat 32 len)) = some true
    exact jae_taken len
  obtain ⟨c₃, hc₃⟩ : ∃ c : State, c =
      { c₂ with rip := c₂.rip + BitVec.ofNat 64 (Ext.Instr.jcc .ae 0x22).length +
        ((0x22 : BitVec 32).signExtend 64) } := ⟨_, rfl⟩
  have e₃ : Ext.exec (.jcc .ae 0x22) c₂ m.memory = .ok c₃ m.memory := by
    rw [Ext.exec_jcc c₂ m.memory .ae 0x22 true hcond, hc₃]
    simp only [ite_true]
  have hr₂ : c₂.rip.toNat = entry.toNat + 28 := by
    rw [hrip₂]; exact rip_at himg (by decide)
  have s₃ : Ext.stepOpt exit ⟨c₂, m.memory⟩ = some ⟨c₃, m.memory⟩ :=
    retires_instr (m := ⟨c₂, m.memory⟩) himg 28 (.jcc .ae 0x22) hr₂
      (by decide) (by decide) (by decide) e₃
  have hrip₃ : c₃.rip = entry + BitVec.ofNat 64 68 := by
    rw [hc₃]
    show c₂.rip + BitVec.ofNat 64 (Ext.Instr.jcc .ae 0x22).length + _ = _
    rw [M8, hrip₂]
    exact jmpExit entry
  have hrsp₃ : c₃.read .rsp = sp - 8#64 := by rw [hc₃, read_setRip]; exact hrsp₂
  -- 68: pop %rbp
  have hpop : X86.popWord c₃ m.memory =
      some (bp0, c₃.write .rsp (c₃.read .rsp + 8#64)) :=
    X86.popWord_of_readBytes (by rw [hrsp₃]; exact hSaved)
  obtain ⟨c₄, hc₄⟩ : ∃ c : State, c =
      { (c₃.write .rsp (c₃.read .rsp + 8#64)).write .rbp bp0 with
        rip := c₃.rip + BitVec.ofNat 64 (X86.Insn.pop Reg.rbp).length } := ⟨_, rfl⟩
  have e₄ : Ext.exec (.pop .rbp) c₃ m.memory = .ok c₄ m.memory := by
    rw [Ext.exec_pop, hc₄]
    simp only [X86.Insn.exec, hpop, Option.map_some]
  have hr₃ : c₃.rip.toNat = entry.toNat + 68 := by
    rw [hrip₃]; exact rip_at himg (by decide)
  have s₄ : Ext.stepOpt exit ⟨c₃, m.memory⟩ = some ⟨c₄, m.memory⟩ :=
    retires_instr (m := ⟨c₃, m.memory⟩) himg 68 (.pop .rbp) hr₃
      (by decide) (by decide) (by decide) e₄
  have hrip₄ : c₄.rip = entry + BitVec.ofNat 64 69 := by rw [hc₄]; rw [M17, hrip₃, rip_add]
  have hrbp₄ : c₄.read .rbp = bp0 := by rw [hc₄, read_setRip, State.read_write_same]
  have hrsp₄ : c₄.read .rsp = sp := by
    rw [hc₄, read_setRip,
      State.read_write_other _ _ _ _ (by decide : Reg.rsp ≠ Reg.rbp),
      State.read_write_same, hrsp₃]
    exact sp_restore sp
  -- 69: ret
  have hpop₂ : X86.popWord c₄ m.memory =
      some (exit, c₄.write .rsp (c₄.read .rsp + 8#64)) :=
    X86.popWord_of_readBytes (by rw [hrsp₄]; exact hRet)
  obtain ⟨c₅, hc₅⟩ : ∃ c : State, c =
      { c₄.write .rsp (c₄.read .rsp + 8#64) with rip := exit } := ⟨_, rfl⟩
  have e₅ : Ext.exec .ret c₄ m.memory = .ok c₅ m.memory := by
    rw [Ext.exec_ret, hc₅]
    simp only [X86.Insn.exec, hpop₂, Option.map_some]
  have hr₄ : c₄.rip.toNat = entry.toNat + 69 := by
    rw [hrip₄]; exact rip_at himg (by decide)
  have hreturn : Ext.step exit ⟨c₄, m.memory⟩ = .returned ⟨c₅, m.memory⟩ :=
    returns_ret (m := ⟨c₄, m.memory⟩) himg 69 hr₄ (by decide) (by decide) e₅
      (by rw [hc₅])
  have a0 : Advances exit m ⟨c₁, m.memory⟩ := Advances.one s₁
  have a1 := a0.step s₂
  have a2 := a1.step s₃
  have a3 := a2.step s₄
  refine ⟨⟨c₅, m.memory⟩, returns_of_advances a3 hreturn, by rw [hc₅], ?_, ?_, ?_, rfl⟩
  · rw [hc₅, read_setRip, State.read_write_same, hrsp₄]
  · rw [hc₅, read_setRip,
      State.read_write_other _ _ _ _ (by decide : Reg.rbp ≠ Reg.rsp)]
    exact hrbp₄
  · intro r h1 h2 h3
    rw [hc₅, read_setRip, State.read_write_other _ _ _ _ h2, hc₄, read_setRip,
      State.read_write_other _ _ _ _ h3, State.read_write_other _ _ _ _ h2,
      hc₃, read_setRip, hc₂, read_setFlagsRip, hc₁, read_setRip,
      Sz.read_write_other _ _ _ _ _ h1]

/-! ## The certificate -/

set_option maxHeartbeats 2000000 in
/-- **`MD5_memcpy` returns, having copied the buffer.** From any ABI-conformant
System V entry state with non-overlapping buffers, the real machine returns to
the caller with the first `len` bytes of `output` equal to the entry state's
first `len` bytes of `input`, `rsp` popped past the return address, every
`sysv64` callee-saved register restored, and memory changed only in the output
buffer and the 32 frame bytes below the entry `rsp`.

The proof is `prologue`, then `Advances.loop` with `iteration` as its body,
then `epilogue`. The induction over the loop lives entirely in
`Advances.loop`. -/
theorem md5_memcpy_returns {entry exit : Word} {m : MState} (h : Entry entry exit m) :
    ∃ final, Ext.Returns exit m final ∧ final.core.rip = exit ∧
      (∀ j, j < lenOf m → Ext.loadN final.memory (outOf m + BitVec.ofNat 64 j) 1 =
        Ext.loadN m.memory (inOf m + BitVec.ofNat 64 j) 1) ∧
      final.core.read .rsp = m.core.read .rsp + 8#64 ∧
      (∀ r ∈ X86.sysv64.calleeSaved, final.core.read r = m.core.read r) ∧
      WritesOnly₂ m.memory final.memory (outOf m).toNat (lenOf m)
        ((m.core.read .rsp).toNat - 32) 32 := by
  obtain ⟨base, hadv, hS, hSaved, hRet, hInv0, hpframe, hothP, hinEq⟩ := prologue h
  obtain ⟨mid, hadv2, hmid⟩ :=
    Advances.loop (exit := exit)
      (Inv := fun k mm => ∃ i, i + k = lenOf m ∧
        AtLoop entry (m.core.read .rsp) (outOf m) (inOf m) (lenOf m) base mm i)
      (fun n mm hmm => by
        obtain ⟨i, hik, hinv⟩ := hmm
        obtain ⟨mm', hadvb, hinv'⟩ := iteration hS hinv (by omega)
        exact ⟨mm', hadvb, i + 1, by omega, hinv'⟩)
      (lenOf m) base ⟨0, by omega, hInv0⟩
  obtain ⟨i, hi0, hinvLen⟩ := hmid
  have hieq : i = lenOf m := by omega
  subst hieq
  obtain ⟨final, hret, hrip, hrsp, hrbp, hothE, hmem⟩ := epilogue hS hSaved hRet hinvLen
  refine ⟨final, returns_prepend (hadv.trans hadv2) hret, hrip, ?_, hrsp, ?_, ?_⟩
  · intro j hj
    rw [hmem]
    exact (hinvLen.copied j hj).trans (hinEq j hj)
  · intro r hr
    have hcs : r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 :=
      (X86.sysv64_mem_calleeSaved r).mp hr
    rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hothE _ (by decide) (by decide) (by decide)).trans
        ((hinvLen.other _ (by decide) (by decide) (by decide)).trans
          (hothP _ (by decide) (by decide)))
    · exact hrbp
    · exact (hothE _ (by decide) (by decide) (by decide)).trans
        ((hinvLen.other _ (by decide) (by decide) (by decide)).trans
          (hothP _ (by decide) (by decide)))
    · exact (hothE _ (by decide) (by decide) (by decide)).trans
        ((hinvLen.other _ (by decide) (by decide) (by decide)).trans
          (hothP _ (by decide) (by decide)))
    · exact (hothE _ (by decide) (by decide) (by decide)).trans
        ((hinvLen.other _ (by decide) (by decide) (by decide)).trans
          (hothP _ (by decide) (by decide)))
    · exact (hothE _ (by decide) (by decide) (by decide)).trans
        ((hinvLen.other _ (by decide) (by decide) (by decide)).trans
          (hothP _ (by decide) (by decide)))
  · rw [hmem]
    exact writesOnly₂_trans (writesOnly₂_of_right hpframe)
      (writesOnly₂_widen_right hinvLen.frame (by omega) (by omega))

/-! ## Status, and a note on a prediction that was wrong

Everything in this file is proved and `sorry`-free: the ingestion
(`code_eq_functionBytes`), the decoder's reading of all 70 bytes as 21
instructions with both branch displacements landing exactly on the loop head
and the exit (`code_decodeAll`, `code_decodeLengths`, `loop_offsets`,
`code_covered`), the tail-recursive decompiled function and its closed form
(`writtenBytes`, `writtenBytes_eq`), the three certificates (`prologue`,
`iteration`, `epilogue`) and the end-to-end `md5_memcpy_returns`.

### The prediction, and what actually happened

An earlier revision of this file predicted — from design analysis, before the
attempt — that the per-iteration certificate would be where this approach's
framing vocabulary ran out. The reasoning was that `right_rot`'s disjointness
side conditions are fixed offsets that `decide` closes, whereas the loop's
`copied` invariant is a `∀ j < i` statement over a span the loop extends, so
its preservation would be an *indexed* obligation of a different character.

That prediction was tested and was wrong, and it seems more useful to record
that than to quietly delete it. Once `WritesOnly₂` existed — two
non-adjacent written regions, the output buffer and the loop's own counter
slot, which the single-interval `Memory.WritesOnly` cannot describe —
`loadN_writesOnly₂`, `loadN_storeN_disjoint` and `toNat_add_lit` reduced
*every* framing side condition, indexed ones included, to a single `omega`
goal over naturals. Re-establishing `copied` for `j < i + 1` is a two-case
split (an earlier byte, disjoint from this iteration's store; or this
iteration's byte, by `loadN_storeN` and a byte round-trip) and runs to about
fifteen lines.

Measured effort, for whatever it is worth: `right_rot`'s fifteen straight-line
instructions took roughly a dozen build-fix cycles; this thirteen-instruction
iteration took about five, of which three were ordinary Lean friction (a
diverging `congr 1`, a `BitVec Sz.d.bits` versus `BitVec 32` unification
mismatch, an implicit `MState` inferred wrongly) rather than anything to do
with loops or framing. The loop rule itself (`Advances.loop`) is ten lines and
the decompiled function with its closed form about twenty-five.

### What this does and does not say

It says that for a buffer loop the cost is **the first loop, not the loop** —
roughly sixty lines of indexed framing vocabulary added once to `Cert.lean`,
after which the per-iteration cost was comparable to straight-line code. It
does not say that no loop will be expensive: this one has a single
`Nat`-measured counter, no nesting, no aliasing between its two pointers
(`Nonoverlapping` is a precondition the caller owes), and a decreasing measure
that `Advances.loop` can take directly. A loop whose measure is not obvious,
or whose buffers may alias, would exercise parts of the design this benchmark
does not reach.

### Red zone and the ABI

`MD5_memcpy` is a leaf that never adjusts `rsp` beyond its own `push`. Of the
32 frame bytes it uses, the top eight hold the saved `rbp` (at the post-push
`rsp`) and the remaining 24 are System V red zone — `sysv64.redZone` is 128.
`Entry` asks for exactly those 32 bytes plus the output buffer, and the
certificate promises to change no others.

Everything here is a statement about the handwritten local model of
`Silmaril/X86/Ext`; it is not evidence about hardware.
-/

end Silmaril.X86.Decompile.Md5Memcpy
