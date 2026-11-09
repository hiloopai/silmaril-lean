module

public import Silmaril.X86.Loose.Defs
public import Silmaril.X86.Ext9.Defs

/-!
# Loose forms, group `MulDiv`: multiply, divide, carry arithmetic, bit test and bit scan

`EffSpec`s for the `Ext9` forms

| family | `Ext9` form | spec |
| --- | --- | --- |
| `mul` | `.ext8 (.base (.mul sz src))` | `mulSpec` |
| `imul` (two operand) | `.ext8 (.base (.imul sz dst src))` | `imulSpec` |
| `imul` (three operand) | `.new (.imulI sz dst src imm)` | `imulISpec` |
| `imul` (one operand) | `.new (.imul1 sz src)` | `imul1Spec` |
| `div`, `idiv` | `.ext8 (.base (.div sz signed src))` | `divSpec` |
| `adc`/`sbb r/m, r` | `.new (.adc sz sub dst src)` | `adcSpec` |
| `adc`/`sbb r, r/m` | `.new (.adcR sz sub dst src)` | `adcRSpec` |
| `adc`/`sbb r/m, imm` | `.new (.adcI sz sub dst imm)` | `adcISpec` |
| `bt r, r` | `.new (.bt sz dst src)` | `btSpec` |
| `bsf`, `bsr` | `.new (.bsf sz dst src)`, `.new (.bsr sz dst src)` | `bsfSpec`, `bsrSpec` |

`specOf` maps each of these forms to its spec and every other form to `none`.

What each spec promises, and where it is looser than `Ext9`:

* `mul`, `imul*`: the product registers; CF and OF (the `Ext`/`Ext9` formulas); SF, ZF, AF,
  PF undefined (any value).
* `div`/`idiv`: quotient and remainder; all six flags undefined. Division by zero or a
  quotient that does not fit is **`unspecified`** (`Ext`: `.divideError`).
* `adc`/`sbb`: the result; CF, ZF, SF, OF. **PF and AF are undefined** (looser than `Ext9`,
  which defines them; the same choice as the `Int` group). CF undefined on entry is
  `unspecified` (`Ext9`: `.undefinedCondition .b`).
* `bt`: CF; the other five flags undefined.
* `bsf`/`bsr`: on a nonzero source the bit index, ZF = 0, the rest undefined. **On a zero
  source the form is `unspecified`**: the SDM sets ZF and leaves the destination undefined,
  and `Ext9` stops there (`.undefinedCondition .e`), so no tighter promise would be met by
  `Ext9`.
* every form: a memory operand that cannot be read, and a memory destination that cannot be
  written, is `unspecified` (`Ext`: `.dataFault`).

The specs reuse the `Ext`/`Ext9` result and flag formulas (`mulFlags`, `imulFlags`,
`imul1Flags`, `carryResult`, `carryFlags`, `divide`, `bsfIndex`, `bsrIndex`) through
`FlagEff.ofFlags` (a `none` flag is undefined); the looseness is in what is left out
(undefined flags, `unspecified`), not in new formulas.

Builders: `EffSpec.guarded` (unspecified where a Boolean guard holds or the writes are not
permitted, so `writes_ok` is free) and `ofOperand` (an effect computed from one `r/m` operand
value, which lists the operand's bytes as read, so `local_reads` is free).
-/

@[expose] public section

namespace Silmaril.X86.Loose.Forms.MulDiv

open Silmaril.X86 (State Word Byte Reg Flags)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (RM Sz Cond readRM)
open Silmaril.X86.Loose

/-! ## Builders -/

/-- The address of the next instruction. -/
def nextIp (c : State) (l : Nat) : Word := c.rip + BitVec.ofNat 64 l

/-- The bytes an `r/m` operand reads at size `sz`: none for a register. -/
def rmReads (sz : Sz) (op : RM) (c : State) (l : Nat) : List (Nat × Nat) :=
  match op with
  | .reg _ => []
  | .mem mm => [((mm.addr c (nextIp c l)).toNat, sz.bytes)]

/-- The value of an `r/m` operand (`0` where it cannot be read; that case is
`unspecified`). -/
def rmVal (sz : Sz) (op : RM) (c : State) (m : Memory) (l : Nat) : BitVec sz.bits :=
  (readRM sz op c m (nextIp c l)).getD 0

/-- A spec from an effect that is local in memory: unspecified where `bad` holds or the
effect's writes are not permitted. -/
def EffSpec.guarded (bad : State → Memory → Nat → Bool) (eff : State → Memory → Nat → Effect)
    (hloc : ∀ c m m' l,
      (∀ p ∈ (eff c m l).reads, m'.readBytes p.1 p.2 = m.readBytes p.1 p.2) →
        eff c m' l = eff c m l) : EffSpec where
  unspecified c m l := bad c m l = true ∨ writeAll m (eff c m l).writes = none
  eff := eff
  local_reads := hloc
  writes_ok c m l h := by
    rw [not_or] at h
    exact Option.isSome_iff_ne_none.2 h.2

/-- The effect `E c l x` of a form on the value `x` of one `r/m` operand, with the operand's
bytes as its reads. -/
def operandEff (sz : Sz) (op : RM) (E : State → Nat → BitVec sz.bits → Effect)
    (c : State) (m : Memory) (l : Nat) : Effect :=
  { E c l (rmVal sz op c m l) with reads := rmReads sz op c l }

/-- An operand read depends only on the bytes it lists. -/
theorem readRM_congr {sz : Sz} {op : RM} {c : State} {m m' : Memory} {l : Nat}
    (h : ∀ p ∈ rmReads sz op c l, m'.readBytes p.1 p.2 = m.readBytes p.1 p.2) :
    readRM sz op c m' (nextIp c l) = readRM sz op c m (nextIp c l) := by
  cases op with
  | reg r => rfl
  | mem mm =>
    have := h _ (List.mem_singleton_self _)
    simp only [readRM, Silmaril.X86.Ext.loadN]
    rw [this]

/-- **A form computed from one `r/m` operand**: unspecified where the operand cannot be read,
where `bad` holds of its value, or where the writes are not permitted. -/
def ofOperand (sz : Sz) (op : RM) (bad : State → Nat → BitVec sz.bits → Bool)
    (E : State → Nat → BitVec sz.bits → Effect) : EffSpec :=
  EffSpec.guarded
    (fun c m l => (readRM sz op c m (nextIp c l)).isNone || bad c l (rmVal sz op c m l))
    (operandEff sz op E)
    (fun c m m' l h => by
      have h' : ∀ p ∈ rmReads sz op c l, m'.readBytes p.1 p.2 = m.readBytes p.1 p.2 := h
      simp only [operandEff, rmVal, readRM_congr h'])

/-! ## Multiply -/

/-- `mul r/m` (unsigned, `RDX:RAX := RAX * src`): CF = OF = the high half is nonzero. -/
def mulEff (sz : Sz) (c : State) (l : Nat) (y : BitVec sz.bits) : Effect :=
  let p := (sz.read c .rax).toNat * y.toNat
  let lo := BitVec.ofNat sz.bits p
  let hi := BitVec.ofNat sz.bits (p / 2 ^ sz.bits)
  { rip := nextIp c l
    regs := [(.rax, lo.setWidth 64), (.rdx, hi.setWidth 64)]
    flags := FlagEff.ofFlags (Silmaril.X86.Ext.mulFlags (hi != 0#sz.bits)) }

def mulSpec (sz : Sz) (src : RM) : EffSpec := ofOperand sz src (fun _ _ _ => false) (mulEff sz)

/-- `imul r, r/m` (`dst := dst * src`): CF = OF = signed overflow. -/
def imulEff (sz : Sz) (dst : Reg) (c : State) (l : Nat) (y : BitVec sz.bits) : Effect :=
  { rip := nextIp c l
    regs := [(dst, (sz.read c dst * y).setWidth 64)]
    flags := FlagEff.ofFlags (Silmaril.X86.Ext.imulFlags (sz.read c dst) y) }

def imulSpec (sz : Sz) (dst : Reg) (src : RM) : EffSpec :=
  ofOperand sz src (fun _ _ _ => false) (imulEff sz dst)

/-- `imul r, r/m, imm` (`dst := src * sext imm`): CF = OF = signed overflow. -/
def imulIEff (sz : Sz) (dst : Reg) (imm : BitVec 32) (c : State) (l : Nat)
    (y : BitVec sz.bits) : Effect :=
  { rip := nextIp c l
    regs := [(dst, (y * imm.signExtend sz.bits).setWidth 64)]
    flags := FlagEff.ofFlags (Silmaril.X86.Ext.imulFlags y (imm.signExtend sz.bits)) }

def imulISpec (sz : Sz) (dst : Reg) (src : RM) (imm : BitVec 32) : EffSpec :=
  ofOperand sz src (fun _ _ _ => false) (imulIEff sz dst imm)

/-- `imul r/m` (one operand, signed `RDX:RAX := RAX * src`). -/
def imul1Eff (sz : Sz) (c : State) (l : Nat) (y : BitVec sz.bits) : Effect :=
  let x := sz.read c .rax
  let p := Silmaril.X86.Ext9.imulWide x y
  { rip := nextIp c l
    regs := [(.rax, p.1.setWidth 64), (.rdx, p.2.setWidth 64)]
    flags := FlagEff.ofFlags (Silmaril.X86.Ext9.imul1Flags x y) }

def imul1Spec (sz : Sz) (src : RM) : EffSpec :=
  ofOperand sz src (fun _ _ _ => false) (imul1Eff sz)

/-! ## Divide -/

/-- The quotient and remainder of `RDX:RAX` by `y`, or `none` (`#DE`). -/
def divOf (sz : Sz) (signed : Bool) (c : State) (y : BitVec sz.bits) :
    Option (BitVec sz.bits × BitVec sz.bits) :=
  Silmaril.X86.Ext.divide sz signed (sz.read c .rdx) (sz.read c .rax) y

/-- `div`/`idiv r/m`: `RAX := quotient`, `RDX := remainder`, every flag undefined. -/
def divEff (sz : Sz) (signed : Bool) (c : State) (l : Nat) (y : BitVec sz.bits) : Effect :=
  { rip := nextIp c l
    regs := match divOf sz signed c y with
      | some (q, r) => [(.rax, q.setWidth 64), (.rdx, r.setWidth 64)]
      | none => []
    flags := FlagEff.ofFlags Silmaril.X86.Ext.undefinedFlags }

/-- Division by zero or an overflowing quotient is `unspecified`. -/
def divSpec (sz : Sz) (signed : Bool) (src : RM) : EffSpec :=
  ofOperand sz src (fun c _ y => (divOf sz signed c y).isNone) (divEff sz signed)

/-! ## Add and subtract with carry -/

/-- The ADC/SBB flags the loose spec promises: CF, ZF, SF, OF; PF and AF undefined. -/
def looseCarryFlags {n : Nat} (sub : Bool) (x y : BitVec n) (cf : Bool) : Flags :=
  { Silmaril.X86.Ext9.carryFlags sub x y cf with parity := none, adjust := none }

/-- The register writes and memory writes of storing `v` into an `r/m` operand. -/
def rmWriteRegs (sz : Sz) (op : RM) (v : BitVec sz.bits) : List (Reg × Word) :=
  match op with
  | .reg r => [(r, v.setWidth 64)]
  | .mem _ => []

def rmWriteMem (sz : Sz) (op : RM) (c : State) (l : Nat) (v : BitVec sz.bits) :
    List (Nat × List Byte) :=
  match op with
  | .reg _ => []
  | .mem mm => [((mm.addr c (nextIp c l)).toNat,
      Silmaril.X86.Ext.leBytes (v.setWidth 64) sz.bytes)]

/-- `dst := x ± (y + CF)` into the `r/m` operand `dst`. -/
def carryEff (sz : Sz) (sub : Bool) (dst : RM) (x y : BitVec sz.bits) (c : State) (l : Nat) :
    Effect :=
  let cf := c.flags.carry.getD false
  let r := Silmaril.X86.Ext9.carryResult sub x y cf
  { rip := nextIp c l
    regs := rmWriteRegs sz dst r
    writes := rmWriteMem sz dst c l r
    flags := FlagEff.ofFlags (looseCarryFlags sub x y cf) }

/-- CF undefined on entry. -/
def cfUndef (c : State) : Bool := c.flags.carry.isNone

/-- `adc`/`sbb r/m, r`. -/
def adcSpec (sz : Sz) (sub : Bool) (dst : RM) (src : Reg) : EffSpec :=
  ofOperand sz dst (fun c _ _ => cfUndef c) fun c l x => carryEff sz sub dst x (sz.read c src) c l

/-- `adc`/`sbb r, r/m`. -/
def adcRSpec (sz : Sz) (sub : Bool) (dst : Reg) (src : RM) : EffSpec :=
  ofOperand sz src (fun c _ _ => cfUndef c)
    fun c l y => carryEff sz sub (.reg dst) (sz.read c dst) y c l

/-- `adc`/`sbb r/m, imm`. -/
def adcISpec (sz : Sz) (sub : Bool) (dst : RM) (imm : BitVec 32) : EffSpec :=
  ofOperand sz dst (fun c _ _ => cfUndef c)
    fun c l x => carryEff sz sub dst x (imm.signExtend sz.bits) c l

/-! ## Bit test and bit scan -/

/-- `bt r, r`: CF is the selected bit; the other flags undefined. -/
def btSpec (sz : Sz) (dst src : Reg) : EffSpec :=
  EffSpec.ofCore (fun c l =>
    { rip := nextIp c l
      flags := FlagEff.ofFlags
        ⟨some ((sz.read c dst).getLsbD ((sz.read c src).toNat % sz.bits)),
          none, none, none, none, none⟩ }) (fun _ _ => rfl)

/-- `bsf`/`bsr` with bit index `idx`, on a nonzero source. -/
def scanEff (sz : Sz) (idx : BitVec sz.bits → Nat) (dst : Reg) (c : State) (l : Nat)
    (y : BitVec sz.bits) : Effect :=
  { rip := nextIp c l
    regs := [(dst, (BitVec.ofNat sz.bits (idx y)).setWidth 64)]
    flags := FlagEff.ofFlags Silmaril.X86.Ext9.scanFlags }

/-- `bsf`: unspecified on a zero source. -/
def bsfSpec (sz : Sz) (dst : Reg) (src : RM) : EffSpec :=
  ofOperand sz src (fun _ _ y => decide (y = 0#sz.bits)) (scanEff sz Silmaril.X86.Ext9.bsfIndex dst)

/-- `bsr`: unspecified on a zero source. -/
def bsrSpec (sz : Sz) (dst : Reg) (src : RM) : EffSpec :=
  ofOperand sz src (fun _ _ y => decide (y = 0#sz.bits)) (scanEff sz Silmaril.X86.Ext9.bsrIndex dst)

/-! ## The group's specification -/

/-- The `MulDiv` specs of `Ext9` forms; `none` for every other form. -/
def specOf : Silmaril.X86.Ext9.Instr → Option EffSpec
  | .ext8 (.base (.mul sz src)) => some (mulSpec sz src)
  | .ext8 (.base (.imul sz dst src)) => some (imulSpec sz dst src)
  | .ext8 (.base (.div sz signed src)) => some (divSpec sz signed src)
  | .new (.imulI sz dst src imm) => some (imulISpec sz dst src imm)
  | .new (.imul1 sz src) => some (imul1Spec sz src)
  | .new (.adc sz sub dst src) => some (adcSpec sz sub dst src)
  | .new (.adcR sz sub dst src) => some (adcRSpec sz sub dst src)
  | .new (.adcI sz sub dst imm) => some (adcISpec sz sub dst imm)
  | .new (.bt sz dst src) => some (btSpec sz dst src)
  | .new (.bsf sz dst src) => some (bsfSpec sz dst src)
  | .new (.bsr sz dst src) => some (bsrSpec sz dst src)
  | _ => none

end Silmaril.X86.Loose.Forms.MulDiv
