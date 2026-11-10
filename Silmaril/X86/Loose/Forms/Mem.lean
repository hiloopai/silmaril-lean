module

public import Silmaril.X86.Loose.Defs
public import Silmaril.X86.Ext8.Basic

/-!
# Loose forms: one-read kernels, operand helpers, `load` and `store`

Every integer form of the `Int` group reads memory at most once and writes it at most once.
This file gives one way to build such a form, and the two pure memory forms:

* `Kernel`: a form given by the one memory read it makes (`rd`: address and length, as a
  function of the core and the next-instruction address, never of memory) and by its
  effect as a function of the bytes read (`body`). `Kernel.spec` is its `EffSpec`:
  - **unspecified** exactly where the read is not permitted or the writes are not
    permitted (`Kernel.bad`). `X86.Ext` reports `dataFault` there; the loose spec says
    nothing (hardware may fault or do anything);
  - `local_reads` and `writes_ok` hold by construction.
* operand helpers over `Ext.RM` (`rmRd`, `rmVal`, `szDst`, `narrowDst`) and over
  `Ext8.RM8` (`rm8Rd`, `rm8Val`, `rm8Dst`), which mirror `readRM`/`writeRM`,
  `readNarrow`/`writeNarrow` and `RM8.read`/`RM8.write` as effect lists;
* `FlagEff.loose f`: CF, ZF, SF and OF as in `f` (a `none` of `f`, undefined in the SDM, is
  any value), PF and AF undefined (`undef`). This is the looseness of the `Int` group: Ext
  defines PF and AF, the loose spec does not promise them;
* `loadS` (`mov reg, m`) and `storeS` (`mov r/m8, r8`, `mov r/m16, r16`).

Every byte read or written goes through `Process.Memory.readBytes`/`writeBytes`, which
check the read or write permission of the whole span; so a "permitted" access is exactly a
`some` result.
-/

@[expose] public section

namespace Silmaril.X86.Loose.Forms

open Silmaril.X86 (State Word Byte Flags Reg)
open Silmaril.X86.Ext (Sz Narrow RM leBytes leValue narrowMask)
open Silmaril.Process (Memory)
open Silmaril.X86.Loose

/-- The little-endian word of a byte list (`Ext.loadN`'s value). -/
def leWord (bs : List Byte) : Word := BitVec.ofNat 64 (leValue bs)

/-- The address of the next instruction, for an instruction of length `l`. -/
def nextOf (c : State) (l : Nat) : Word := c.rip + BitVec.ofNat 64 l

/-- **Loose flags**: CF, ZF, SF and OF as in `f`; PF and AF undefined. -/
def FlagEff.loose (f : Flags) : FlagEff where
  carry := .ofOpt f.carry
  parity := .undef
  adjust := .undef
  zero := .ofOpt f.zero
  sign := .ofOpt f.sign
  overflow := .ofOpt f.overflow

/-- A form that reads memory at most once (`rd`, independent of memory) and whose effect is a
function of the bytes read (`none` when there is no read, or it is not permitted). -/
structure Kernel where
  /-- The memory read `(address, length)`, from the core and the next-instruction address. -/
  rd : State → Word → Option (Nat × Nat)
  /-- The effect, from the core, the next-instruction address and the bytes read. Its
  `reads` field is ignored (`Kernel.eff` sets it to `rd`). -/
  body : State → Word → Option (List Byte) → Effect

namespace Kernel

/-- The bytes the kernel reads. -/
def input (K : Kernel) (c : State) (m : Memory) (l : Nat) : Option (List Byte) :=
  (K.rd c (nextOf c l)).bind fun p => m.readBytes p.1 p.2

/-- The effect: the body on the bytes read, with the read listed. -/
def eff (K : Kernel) (c : State) (m : Memory) (l : Nat) : Effect :=
  let e := K.body c (nextOf c l) (K.input c m l)
  ⟨e.rip, e.regs, e.havocRegs, e.flags, (K.rd c (nextOf c l)).toList, e.writes⟩

/-- The read is not permitted. -/
def readFails (K : Kernel) (c : State) (m : Memory) (l : Nat) : Bool :=
  match K.rd c (nextOf c l) with
  | some p => (m.readBytes p.1 p.2).isNone
  | none => false

/-- Where the kernel's form is unspecified: a read or a write is not permitted. -/
def bad (K : Kernel) (c : State) (m : Memory) (l : Nat) : Bool :=
  K.readFails c m l || (writeAll m (K.eff c m l).writes).isNone

theorem input_congr (K : Kernel) (c : State) (m m' : Memory) (l : Nat)
    (h : ∀ p ∈ (K.rd c (nextOf c l)).toList, m'.readBytes p.1 p.2 = m.readBytes p.1 p.2) :
    K.input c m' l = K.input c m l := by
  unfold input
  cases hr : K.rd c (nextOf c l) with
  | none => rfl
  | some p =>
    simp only [Option.bind_some]
    exact h p (by simp [hr])

/-- **The `EffSpec` of a kernel.** -/
def spec (K : Kernel) : EffSpec where
  unspecified c m l := K.bad c m l = true
  eff := K.eff
  local_reads c m m' l h := by
    have := K.input_congr c m m' l h
    simp only [eff] at h ⊢
    rw [this]
  writes_ok c m l h := by
    simp only [bad, Bool.or_eq_true, not_or] at h
    cases hw : writeAll m (K.eff c m l).writes with
    | none => simp [hw] at h
    | some _ => rfl

end Kernel

/-! ## Operands -/

/-- The memory read of an `r/m` operand of `k` bytes. -/
def rmRd (k : Nat) : RM → State → Word → Option (Nat × Nat)
  | .reg _, _, _ => none
  | .mem a, c, next => some ((a.addr c next).toNat, k)

/-- The value of an `r/m` operand at width `n`, from the bytes read (`readRM`,
`readNarrow`). -/
def rmVal (n : Nat) : RM → State → Option (List Byte) → BitVec n
  | .reg r, c, _ => (c.read r).setWidth n
  | .mem _, _, inp => (leWord (inp.getD [])).setWidth n

/-- The writes of `writeRM sz dst v`: registers and memory. -/
def szDst (sz : Sz) : RM → State → Word → BitVec sz.bits → List (Reg × Word) × List (Nat × List Byte)
  | .reg r, _, _, v => ([(r, v.setWidth 64)], [])
  | .mem a, c, next, v => ([], [((a.addr c next).toNat, leBytes (v.setWidth 64) sz.bytes)])

/-- The writes of `writeNarrow n dst v` (a register keeps the bits above). -/
def narrowDst (n : Narrow) : RM → State → Word → BitVec n.bits →
    List (Reg × Word) × List (Nat × List Byte)
  | .reg r, c, _, v => ([(r, (c.read r &&& ~~~(narrowMask n)) ||| v.setWidth 64)], [])
  | .mem a, c, next, v => ([], [((a.addr c next).toNat, leBytes (v.setWidth 64) n.bytes)])

/-- The memory read of a byte operand of `Ext8` (`RM8`). -/
def rm8Rd : Silmaril.X86.Ext8.RM8 → State → Word → Option (Nat × Nat)
  | .reg _, _, _ => none
  | .mem a, c, next => some ((a.addr c next).toNat, 1)

/-- The value of a byte operand of `Ext8` (`RM8.read`), from the bytes read. -/
def rm8Val : Silmaril.X86.Ext8.RM8 → State → Option (List Byte) → BitVec 8
  | .reg b, c, _ => b.read c
  | .mem _, _, inp => (leWord (inp.getD [])).setWidth 8

/-- The register write of a byte register of `Ext8` (`BReg.write`): a low byte replaces bits
7:0, a legacy high byte bits 15:8. -/
def bregDst (c : State) : Silmaril.X86.Ext8.BReg → BitVec 8 → Reg × Word
  | .low r, v => (r, (c.read r &&& ~~~(0xFF#64)) ||| v.setWidth 64)
  | .high r, v => (r, (c.read r &&& ~~~(0xFF00#64)) ||| (v.setWidth 64 <<< 8))

/-- The writes of `RM8.write dst v`. -/
def rm8Dst : Silmaril.X86.Ext8.RM8 → State → Word → BitVec 8 →
    List (Reg × Word) × List (Nat × List Byte)
  | .reg b, c, _, v => ([bregDst c b v], [])
  | .mem a, c, next, v => ([], [((a.addr c next).toNat, leBytes (v.setWidth 64) 1)])

/-- An effect that retires to `next` with the given writes and flags. -/
def Effect.ofWrites (next : Word) (d : List (Reg × Word) × List (Nat × List Byte))
    (flags : FlagEff := FlagEff.keepAll) : Effect :=
  { rip := next, regs := d.1, flags := flags, writes := d.2 }

/-! ## The `Mem` group -/

/-- **`mov reg, m`** (`load sz dst src`, `8B /r`): read `sz.bytes` bytes at the effective
address, write the register (32-bit writes zero-extend). -/
def loadK (sz : Sz) (dst : Reg) (src : Silmaril.X86.Ext.Mem) : Kernel where
  rd := rmRd sz.bytes (.mem src)
  body c next inp := Effect.ofWrites next ([(dst, (rmVal sz.bits (.mem src) c inp).setWidth 64)], [])

def loadS (sz : Sz) (dst : Reg) (src : Silmaril.X86.Ext.Mem) : EffSpec := (loadK sz dst src).spec

/-- **`mov r/m8, r8` and `mov r/m16, r16`** (`store n dst src`, `88 /r`, `66 89 /r`): write
the low `n.bits` bits of `src`. -/
def storeK (n : Narrow) (dst : RM) (src : Reg) : Kernel where
  rd _ _ := none
  body c next _ := Effect.ofWrites next (narrowDst n dst c next ((c.read src).setWidth n.bits))

def storeS (n : Narrow) (dst : RM) (src : Reg) : EffSpec := (storeK n dst src).spec

end Silmaril.X86.Loose.Forms
