module

public import Silmaril.X86.Loose.Defs
public import Silmaril.X86.Ext9.Defs

/-!
# Loose forms, group `Ctl`: control flow, stack, `cmov`, `setcc`

One `EffSpec` per family:

| family | `Ext9.Instr` constructors | spec |
| --- | --- | --- |
| `jmp*` | `.ext8 (.base (.jmp _))`, `.ext8 (.base (.jmp8 _))` | `jmpSpec` |
| `jcc*` | `.ext8 (.base (.jcc _ _))`, `.ext8 (.base (.jcc8 _ _))` | `jccSpec` |
| `call` | `.ext8 (.base (.call _))` | `pushSpec` (`callVal`) |
| `callInd` | `.new (.callInd _)` | `pushSpec` (`callIndVal`) |
| `jmpInd` | `.new (.jmpInd _)` | `jmpIndSpec` |
| `ret` | `.ext8 (.base .ret)` | `popSpec` (`retPost`) |
| `push` | `.ext8 (.base (.push _))`, `.ext8 (.base (.pushRM _))`, `.new (.pushI _)` | `pushSpec` |
| `pop` | `.ext8 (.base (.pop _))` | `popSpec` (`popPost`) |
| `leave` | `.ext8 (.base .leave)` | `popSpec` (`leavePost`) |
| `cmov` | `.ext8 (.base (.cmov _ _ _ _))` | `cmovSpec` |
| `setcc` | `.ext8 (.base (.setcc _ _))`, `.ext8 (.new (.setcc _ _))` | `setccSpec` |
| `endbr64` | `.ext8 (.base .endbr64)` | `endbrSpec` |

What each spec promises: the successor `rip`, the stack pointer and the stack bytes (push,
call), the destination register or byte (pop, leave, cmov, setcc); flags are kept. Where a
spec is **unspecified**:

* a condition that depends on an undefined (`none`) flag (`jcc`, `cmov`, `setcc`; `Ext`:
  `undefinedCondition`);
* a memory read that `Memory.readBytes` refuses (permission or backing), a stack write that
  is not `Permitted .write`, a byte destination write that is not permitted (`Ext`:
  `dataFault`).

These are exactly the cases where `Ext9.exec` does not retire, and where it retires the spec
allows exactly its successor: no flag is undefined and no register is havoc'd
(`Silmaril.X86.Exact.ctlAllows`).

`ctlSpec : Ext9.Instr → Option EffSpec` collects the families. Operand semantics (effective
addresses, `readRM`, the little-endian stack word encoding) are Silmaril's `Ext` helpers;
the specs do not call `Ext.exec`.
-/

@[expose] public section

namespace Silmaril.X86.Loose.Ctl

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.X86.Ext (Mem RM Sz Cond readRM)
open Silmaril.Process (Memory)
open Silmaril.X86.Loose

/-- The address of the next instruction, at instruction length `l`. -/
def next (c : State) (l : Nat) : Word := c.rip + BitVec.ofNat 64 l

/-- The memory read of an `r/m` operand at size `sz` (none for a register). -/
def rmReads (sz : Sz) (op : RM) (c : State) (l : Nat) : List (Nat × Nat) :=
  match op with
  | .reg _ => []
  | .mem mm => [((mm.addr c (next c l)).toNat, sz.bytes)]

/-- The stack word at `a`: eight readable bytes, little-endian. -/
def wordAt (m : Memory) (a : Word) : Option Word :=
  (m.readBytes a.toNat 8).bind Silmaril.X86.wordOfBytes?

/-! ## Families -/

/-- `jmp rel` with the displacement `d` (already sign-extended to 64 bits). -/
def jmpSpec (d : Word) : EffSpec :=
  EffSpec.ofCore (fun c l => { rip := next c l + d }) (fun _ _ => rfl)

/-- `endbr64`: no indirect-branch tracking is modelled, so the next instruction. -/
def endbrSpec : EffSpec :=
  EffSpec.ofCore (fun c l => { rip := next c l }) (fun _ _ => rfl)

/-- `jcc rel` with the displacement `d`: unspecified on an undefined condition. -/
def jccSpec (cc : Cond) (d : Word) : EffSpec where
  unspecified c _ _ := cc.eval c.flags = none
  eff c _ l := { rip := if cc.eval c.flags = some true then next c l + d else next c l }
  local_reads _ _ _ _ _ := rfl
  writes_ok _ _ _ _ := rfl

/-- `jmp r/m64`: `rip` is the operand; unspecified if a memory operand is not readable. -/
def jmpIndSpec (src : RM) : EffSpec where
  unspecified c m l := readRM .q src c m (next c l) = none
  eff c m l := { rip := (readRM .q src c m (next c l)).getD 0, reads := rmReads .q src c l }
  local_reads c m m' l h := by
    cases src with
    | reg r => rfl
    | mem mm =>
      simp only [rmReads, List.mem_singleton, forall_eq] at h
      simp [readRM, Silmaril.X86.Ext.loadN, h]
  writes_ok _ _ _ _ := rfl

/-! ### Pushes (`push`, `push r/m`, `push imm`, `call`, `call r/m`)

A push form reads a pair `(value, target)`: the word pushed and the successor `rip`. It is
unspecified if the pair is not available (an unreadable operand) or the eight bytes below
`rsp` are not writable. -/

/-- The successor of a push: `rsp - 8`, the word written there, the target. -/
def pushEff (c : State) (vt : Word × Word) (reads : List (Nat × Nat)) : Effect where
  rip := vt.2
  regs := [(.rsp, c.read .rsp - 8#64)]
  reads := reads
  writes := [((c.read .rsp - 8#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [vt.1])]

/-- A push form from its operand reader `val` and its read footprint `rd`. -/
def pushSpec (val : State → Memory → Nat → Option (Word × Word))
    (rd : State → Nat → List (Nat × Nat))
    (hloc : ∀ c m m' l, (∀ p ∈ rd c l, m'.readBytes p.1 p.2 = m.readBytes p.1 p.2) →
      val c m' l = val c m l) : EffSpec where
  unspecified c m l :=
    val c m l = none ∨ ¬ m.Permitted .write (c.read .rsp - 8#64).toNat 8
  eff c m l := pushEff c ((val c m l).getD (0, 0)) (rd c l)
  local_reads c m m' l h := by
    simp only [pushEff] at h ⊢
    rw [hloc c m m' l h]
  writes_ok c m l h := by
    have hp : m.checkSpan .write (c.read .rsp - 8#64).toNat 8 = true := not_not.1 (not_or.1 h).2
    simp only [pushEff, writeAll, Memory.writeBytes, Silmaril.X86.length_encodeWords_singleton,
      hp, ite_true, Option.bind_some, Option.isSome_some]

/-- `push r64`. -/
def pushRegVal (r : Reg) (c : State) (_ : Memory) (l : Nat) : Option (Word × Word) :=
  some (c.read r, next c l)

/-- `push r/m64`. -/
def pushRMVal (src : RM) (c : State) (m : Memory) (l : Nat) : Option (Word × Word) :=
  (readRM .q src c m (next c l)).map fun v => (v, next c l)

/-- `push imm` (sign-extended to 64 bits). -/
def pushIVal (imm : BitVec 32) (c : State) (_ : Memory) (l : Nat) : Option (Word × Word) :=
  some (imm.signExtend 64, next c l)

/-- `call rel` with displacement `d`: push the next address, jump. -/
def callVal (d : Word) (c : State) (_ : Memory) (l : Nat) : Option (Word × Word) :=
  some (next c l, next c l + d)

/-- `call r/m64`: the target is read first (with the old `rsp`), then the next address is
pushed. -/
def callIndVal (src : RM) (c : State) (m : Memory) (l : Nat) : Option (Word × Word) :=
  (readRM .q src c m (next c l)).map fun v => (next c l, v)

theorem readRM_local (src : RM) (c : State) (m m' : Memory) (l : Nat)
    (h : ∀ p ∈ rmReads .q src c l, m'.readBytes p.1 p.2 = m.readBytes p.1 p.2) :
    readRM .q src c m' (next c l) = readRM .q src c m (next c l) := by
  cases src with
  | reg r => rfl
  | mem mm =>
    simp only [rmReads, List.mem_singleton, forall_eq] at h
    simp [readRM, Silmaril.X86.Ext.loadN, h]

/-- The push forms. -/
def pushRegSpec (r : Reg) : EffSpec :=
  pushSpec (pushRegVal r) (fun _ _ => []) (fun _ _ _ _ _ => rfl)

def pushRMSpec (src : RM) : EffSpec :=
  pushSpec (pushRMVal src) (rmReads .q src)
    (fun c m m' l h => by simp only [pushRMVal, readRM_local src c m m' l h])

def pushISpec (imm : BitVec 32) : EffSpec :=
  pushSpec (pushIVal imm) (fun _ _ => []) (fun _ _ _ _ _ => rfl)

def callSpec (d : Word) : EffSpec :=
  pushSpec (callVal d) (fun _ _ => []) (fun _ _ _ _ _ => rfl)

def callIndSpec (src : RM) : EffSpec :=
  pushSpec (callIndVal src) (rmReads .q src)
    (fun c m m' l h => by simp only [callIndVal, readRM_local src c m m' l h])

/-! ### Pops (`ret`, `pop`, `leave`)

A pop form reads the stack word at an address `a c` and is unspecified if it is not
readable. `post c l v` gives the successor `rip` and the register writes (in order, the
last one wins). -/

/-- A pop form. -/
def popSpec (a : State → Word) (post : State → Nat → Word → Word × List (Reg × Word)) :
    EffSpec where
  unspecified c m _ := wordAt m (a c) = none
  eff c m l :=
    let v := (wordAt m (a c)).getD 0
    { rip := (post c l v).1, regs := (post c l v).2, reads := [((a c).toNat, 8)] }
  local_reads c m m' l h := by
    simp only [List.mem_singleton, forall_eq] at h
    simp [wordAt, h]
  writes_ok _ _ _ _ := rfl

/-- `ret`: `rip` is the word at `rsp`, `rsp + 8`. -/
def retPost (c : State) (_ : Nat) (v : Word) : Word × List (Reg × Word) :=
  (v, [(.rsp, c.read .rsp + 8#64)])

/-- `pop r64`: `rsp + 8`, then `r` is the word (so `pop rsp` loads the word). -/
def popPost (r : Reg) (c : State) (l : Nat) (v : Word) : Word × List (Reg × Word) :=
  (next c l, [(.rsp, c.read .rsp + 8#64), (r, v)])

/-- `leave`: `rsp := rbp`, then `pop rbp`. -/
def leavePost (c : State) (l : Nat) (v : Word) : Word × List (Reg × Word) :=
  (next c l, [(.rsp, c.read .rbp + 8#64), (.rbp, v)])

def retSpec : EffSpec := popSpec (fun c => c.read .rsp) retPost
def popRegSpec (r : Reg) : EffSpec := popSpec (fun c => c.read .rsp) (popPost r)
def leaveSpec : EffSpec := popSpec (fun c => c.read .rbp) leavePost

/-! ### `cmov` -/

/-- `cmovcc r, r/m` at size `sz`: the source is read even if the condition is false; a
32-bit destination is zero-extended either way. Unspecified if the source is not readable or
the condition is undefined. -/
def cmovSpec (sz : Sz) (cc : Cond) (dst : Reg) (src : RM) : EffSpec where
  unspecified c m l := readRM sz src c m (next c l) = none ∨ cc.eval c.flags = none
  eff c m l :=
    { rip := next c l
      regs := [(dst, (if cc.eval c.flags = some true then
          (readRM sz src c m (next c l)).getD 0 else sz.read c dst).setWidth 64)]
      reads := rmReads sz src c l }
  local_reads c m m' l h := by
    have : readRM sz src c m' (next c l) = readRM sz src c m (next c l) := by
      cases src with
      | reg r => rfl
      | mem mm =>
        simp only [rmReads, List.mem_singleton, forall_eq] at h
        simp [readRM, Silmaril.X86.Ext.loadN, h]
    simp only [this]
  writes_ok _ _ _ _ := rfl

/-! ### `setcc` -/

/-- The register value after writing byte `v` to byte register `b`. -/
def bregValue (c : State) (b : Silmaril.X86.Ext8.BReg) (v : BitVec 8) : Reg × Word :=
  match b with
  | .low r => (r, (c.read r &&& ~~~(0xFF#64)) ||| v.setWidth 64)
  | .high r => (r, (c.read r &&& ~~~(0xFF00#64)) ||| (v.setWidth 64 <<< 8))

/-- The byte the condition gives (`0` if undefined, where the spec is unspecified). -/
def setccByte (cc : Cond) (c : State) : BitVec 8 :=
  if cc.eval c.flags = some true then 1#8 else 0#8

/-- `setcc r/m8` over every byte register (`Ext8.RM8`). Unspecified if the condition is
undefined, or the destination byte is not writable. -/
def setccSpec (cc : Cond) (dst : Silmaril.X86.Ext8.RM8) : EffSpec where
  unspecified c m l := cc.eval c.flags = none ∨
    (match dst with
     | .reg _ => False
     | .mem mm => ¬ m.Permitted .write (mm.addr c (next c l)).toNat 1)
  eff c _ l :=
    match dst with
    | .reg b => { rip := next c l, regs := [bregValue c b (setccByte cc c)] }
    | .mem mm =>
      { rip := next c l
        writes := [((mm.addr c (next c l)).toNat,
          Silmaril.X86.Ext.leBytes ((setccByte cc c).setWidth 64) 1)] }
  local_reads _ _ _ _ _ := rfl
  writes_ok c m l h := by
    cases dst with
    | reg b => rfl
    | mem mm =>
      have hp : m.checkSpan .write (mm.addr c (next c l)).toNat 1 = true := not_not.1 (not_or.1 h).2
      simp only [writeAll, Memory.writeBytes, Silmaril.X86.Ext.length_leBytes,
        hp, ite_true, Option.bind_some, Option.isSome_some]

/-- `Ext`'s `r/m` byte destination as an `Ext8` one (a register is its low byte). -/
def RM.toRM8 : RM → Silmaril.X86.Ext8.RM8
  | .reg r => .reg (.low r)
  | .mem mm => .mem mm

/-! ## The `Ctl` specification -/

/-- **The `Ctl` forms** of `Ext9`; `none` for every other form. -/
def ctlSpec : Silmaril.X86.Ext9.Instr → Option EffSpec
  | .ext8 (.base i) =>
    match i with
    | .jmp rel => some (jmpSpec (rel.signExtend 64))
    | .jmp8 rel => some (jmpSpec (rel.signExtend 64))
    | .jcc cc rel => some (jccSpec cc (rel.signExtend 64))
    | .jcc8 cc rel => some (jccSpec cc (rel.signExtend 64))
    | .call rel => some (callSpec (rel.signExtend 64))
    | .ret => some retSpec
    | .push r => some (pushRegSpec r)
    | .pushRM src => some (pushRMSpec src)
    | .pop r => some (popRegSpec r)
    | .leave => some leaveSpec
    | .cmov sz cc dst src => some (cmovSpec sz cc dst src)
    | .setcc cc dst => some (setccSpec cc (RM.toRM8 dst))
    | .endbr64 => some endbrSpec
    | _ => none
  | .ext8 (.new (.setcc cc dst)) => some (setccSpec cc dst)
  | .new (.callInd src) => some (callIndSpec src)
  | .new (.jmpInd src) => some (jmpIndSpec src)
  | .new (.pushI imm) => some (pushISpec imm)
  | _ => none

end Silmaril.X86.Loose.Ctl
