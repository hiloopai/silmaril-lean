module

public import Silmaril.Machine.RiscV.Ext.Defs
public import Silmaril.Machine.CBackend.Lir.Defs
/-!
# Register conventions of the Lir-to-RV64 backend

The backend uses the LP64 integer registers as follows.

| Register | Use |
| --- | --- |
| `x0` | zero |
| `ra` (`x1`) | return address; saved in every frame |
| `sp` (`x2`) | stack pointer, 16-byte aligned, frames of a fixed size |
| `gp`, `tp` (`x3`, `x4`) | not used |
| `t0`–`t2` (`x5`–`x7`) | scratch registers of instruction selection |
| `a0`–`a7` (`x10`–`x17`) | argument and result registers |
| `s10` (`x26`) | lowest usable stack address (the stack limit) |
| `s11` (`x27`) | base address of the linear memory |
| `s0`, `s1`, `s2`–`s9`, `t3`–`t6` | the 14 allocatable registers |

Lir physical registers are placed in the allocatable registers by an
injective map `Assign.idx : P → Fin 14`. All allocatable registers are
caller-saved: a call stores the 14 of them in the caller's frame and reloads
them after the callee returns, so a callee may use them freely.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

abbrev ra : Reg := 1#5
abbrev sp : Reg := 2#5
abbrev t0 : Reg := 5#5
abbrev t1 : Reg := 6#5
abbrev t2 : Reg := 7#5
abbrev s10 : Reg := 26#5
abbrev s11 : Reg := 27#5

/-- The argument and result registers `a0 … a7`. -/
def argReg (j : Fin 8) : Reg := BitVec.ofNat 5 (10 + j.val)

/-- The 14 allocatable registers: `s0 s1 s2 … s9 t3 … t6`. -/
def allocReg (i : Fin 14) : Reg :=
  if i.val < 2 then BitVec.ofNat 5 (8 + i.val)
  else if i.val < 10 then BitVec.ofNat 5 (16 + i.val)
  else BitVec.ofNat 5 (18 + i.val)

theorem allocReg_injective : Function.Injective allocReg := by
  intro i j h
  revert i j
  decide

theorem allocReg_ne_zero (i : Fin 14) : allocReg i ≠ 0#5 := by revert i; decide
theorem allocReg_ne_ra (i : Fin 14) : allocReg i ≠ ra := by revert i; decide
theorem allocReg_ne_sp (i : Fin 14) : allocReg i ≠ sp := by revert i; decide
theorem allocReg_ne_t0 (i : Fin 14) : allocReg i ≠ t0 := by revert i; decide
theorem allocReg_ne_t1 (i : Fin 14) : allocReg i ≠ t1 := by revert i; decide
theorem allocReg_ne_t2 (i : Fin 14) : allocReg i ≠ t2 := by revert i; decide
theorem allocReg_ne_s10 (i : Fin 14) : allocReg i ≠ s10 := by revert i; decide
theorem allocReg_ne_s11 (i : Fin 14) : allocReg i ≠ s11 := by revert i; decide
theorem allocReg_ne_arg (i : Fin 14) (j : Fin 8) : allocReg i ≠ argReg j := by
  revert i j; decide

theorem argReg_injective : Function.Injective argReg := by
  intro i j h
  revert i j
  decide

theorem argReg_ne_zero (j : Fin 8) : argReg j ≠ 0#5 := by revert j; decide
theorem argReg_ne_ra (j : Fin 8) : argReg j ≠ ra := by revert j; decide
theorem argReg_ne_sp (j : Fin 8) : argReg j ≠ sp := by revert j; decide
theorem argReg_ne_t0 (j : Fin 8) : argReg j ≠ t0 := by revert j; decide
theorem argReg_ne_t1 (j : Fin 8) : argReg j ≠ t1 := by revert j; decide
theorem argReg_ne_t2 (j : Fin 8) : argReg j ≠ t2 := by revert j; decide
theorem argReg_ne_s10 (j : Fin 8) : argReg j ≠ s10 := by revert j; decide
theorem argReg_ne_s11 (j : Fin 8) : argReg j ≠ s11 := by revert j; decide

/-- Registers whose value instruction selection never changes except as a
destination: every register other than the scratch registers `t0 t1 t2`. -/
def Scratch (r : Reg) : Prop := r = t0 ∨ r = t1 ∨ r = t2

instance (r : Reg) : Decidable (Scratch r) := inferInstanceAs (Decidable (_ ∨ _))

theorem not_scratch_alloc (i : Fin 14) : ¬ Scratch (allocReg i) := by
  revert i; decide

theorem not_scratch_arg (j : Fin 8) : ¬ Scratch (argReg j) := by
  revert j; decide

@[simp] theorem not_scratch_sp : ¬ Scratch sp := by decide
@[simp] theorem not_scratch_ra : ¬ Scratch ra := by decide
@[simp] theorem not_scratch_s10 : ¬ Scratch s10 := by decide
@[simp] theorem not_scratch_s11 : ¬ Scratch s11 := by decide

@[simp] theorem t0_ne_zero : t0 ≠ 0#5 := by decide
@[simp] theorem t1_ne_zero : t1 ≠ 0#5 := by decide
@[simp] theorem t2_ne_zero : t2 ≠ 0#5 := by decide
@[simp] theorem t0_ne_t1 : t0 ≠ t1 := by decide
@[simp] theorem t0_ne_t2 : t0 ≠ t2 := by decide
@[simp] theorem t1_ne_t0 : t1 ≠ t0 := by decide
@[simp] theorem t1_ne_t2 : t1 ≠ t2 := by decide
@[simp] theorem t2_ne_t0 : t2 ≠ t0 := by decide
@[simp] theorem t2_ne_t1 : t2 ≠ t1 := by decide
@[simp] theorem sp_ne_zero : sp ≠ 0#5 := by decide
@[simp] theorem ra_ne_sp : ra ≠ sp := by decide
@[simp] theorem sp_ne_ra : sp ≠ ra := by decide
@[simp] theorem ra_ne_zero : ra ≠ 0#5 := by decide

/-- An assignment of Lir physical registers to allocatable RV64 registers. -/
structure Assign (P : Type) where
  idx : P → Fin 14
  injective : Function.Injective idx

namespace Assign

variable {P : Type} (A : Assign P)

/-- The RV64 register holding Lir register `p`. -/
def reg (p : P) : Reg := allocReg (A.idx p)

theorem reg_injective : Function.Injective A.reg :=
  fun _ _ h => A.injective (allocReg_injective h)

theorem reg_ne_zero (p : P) : A.reg p ≠ 0#5 := allocReg_ne_zero _
theorem reg_ne_ra (p : P) : A.reg p ≠ ra := allocReg_ne_ra _
theorem reg_ne_sp (p : P) : A.reg p ≠ sp := allocReg_ne_sp _
theorem reg_ne_t0 (p : P) : A.reg p ≠ t0 := allocReg_ne_t0 _
theorem reg_ne_t1 (p : P) : A.reg p ≠ t1 := allocReg_ne_t1 _
theorem reg_ne_t2 (p : P) : A.reg p ≠ t2 := allocReg_ne_t2 _
theorem reg_ne_s10 (p : P) : A.reg p ≠ s10 := allocReg_ne_s10 _
theorem reg_ne_s11 (p : P) : A.reg p ≠ s11 := allocReg_ne_s11 _
theorem reg_ne_arg (p : P) (j : Fin 8) : A.reg p ≠ argReg j := allocReg_ne_arg _ _
theorem not_scratch (p : P) : ¬ Scratch (A.reg p) := not_scratch_alloc _

end Assign

/-- The canonical assignment of `Fin n` for `n ≤ 14`, for example the output
`Fin (k + 2)` of `Lir.Alloc.firstK k` with `k ≤ 12`. -/
def Assign.fin (n : Nat) (h : n ≤ 14) : Assign (Fin n) where
  idx := Fin.castLE h
  injective := Fin.castLE_injective h

end Silmaril.RiscV.Backend
