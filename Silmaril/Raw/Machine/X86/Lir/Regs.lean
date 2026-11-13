module

public import Silmaril.Machine.X86.Ext.Defs
public import Silmaril.Machine.CBackend.Lir.Defs

/-!
# Register conventions of the Lir-to-x86-64 backend

The backend uses the sixteen general-purpose registers as follows.

| Register | Use |
| --- | --- |
| `rsp` | stack pointer; the body of a function runs with a 16-byte aligned `rsp` |
| `r15` | base address of the linear memory (never written) |
| `r14` | lowest usable stack address, the stack limit (never written) |
| `rax`, `rcx`, `rdx`, `r11` | scratch registers of instruction selection |
| `rbx rbp rsi rdi r8 r9 r10 r12 r13` | the nine allocatable registers |

The scratch registers cover every fixed-register use of the selected
instructions: `rcx` holds shift counts (`CL`), `rdx:rax` is the dividend of
DIV/IDIV and receives quotient and remainder, `rax` also receives the byte
written by SETcc, and `r11` is the general scratch register (two-address
arithmetic, linear-memory addresses, the stack-limit check). Since none of them
is allocatable, no save/restore is needed around these instructions.

Calls follow the System V AMD64 register assignment for integer arguments
(`rdi rsi rdx rcx r8 r9`) and results (`rax rdx`). A call site stores all nine
allocatable registers in its frame and reloads them after the call, so they are
caller-saved between compiled functions; in addition every function's prologue
saves the four System V callee-saved registers among them (`rbx rbp r12 r13`)
and its epilogue restores them, and `r14`, `r15` are never written, so a
compiled function preserves all System V callee-saved registers for an external
caller. Lir physical registers are placed in the allocatable registers by an
injective map `Assign.idx : P → Fin 9`.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.X86 (Reg)

/-- The nine allocatable registers: `rbx rbp rsi rdi r8 r9 r10 r12 r13`. -/
def allocReg (i : Fin 9) : Reg :=
  [Reg.rbx, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13].get (i.cast rfl)

/-- The System V integer argument registers `rdi rsi rdx rcx r8 r9`. -/
def argReg (j : Fin 6) : Reg :=
  [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].get (j.cast rfl)

/-- The System V integer result registers `rax rdx`. -/
def resReg (j : Fin 2) : Reg :=
  [Reg.rax, .rdx].get (j.cast rfl)

/-- Registers instruction selection may change without a Lir-level write. -/
def Scratch (r : Reg) : Prop := r = .rax ∨ r = .rcx ∨ r = .rdx ∨ r = .r11

instance (r : Reg) : Decidable (Scratch r) := inferInstanceAs (Decidable (_ ∨ _))

theorem allocReg_injective : Function.Injective allocReg := by
  intro i j h
  revert i j
  decide

theorem allocReg_not_scratch (i : Fin 9) : ¬ Scratch (allocReg i) := by revert i; decide
theorem allocReg_ne_rsp (i : Fin 9) : allocReg i ≠ .rsp := by revert i; decide
theorem allocReg_ne_r14 (i : Fin 9) : allocReg i ≠ .r14 := by revert i; decide
theorem allocReg_ne_r15 (i : Fin 9) : allocReg i ≠ .r15 := by revert i; decide
theorem allocReg_ne_rax (i : Fin 9) : allocReg i ≠ .rax := by revert i; decide
theorem allocReg_ne_rcx (i : Fin 9) : allocReg i ≠ .rcx := by revert i; decide
theorem allocReg_ne_rdx (i : Fin 9) : allocReg i ≠ .rdx := by revert i; decide
theorem allocReg_ne_r11 (i : Fin 9) : allocReg i ≠ .r11 := by revert i; decide

theorem argReg_injective : Function.Injective argReg := by
  intro i j h
  revert i j
  decide

theorem argReg_ne_rsp (j : Fin 6) : argReg j ≠ .rsp := by revert j; decide
theorem argReg_ne_r14 (j : Fin 6) : argReg j ≠ .r14 := by revert j; decide
theorem argReg_ne_r15 (j : Fin 6) : argReg j ≠ .r15 := by revert j; decide

theorem resReg_injective : Function.Injective resReg := by
  intro i j h
  revert i j
  decide

theorem resReg_scratch (j : Fin 2) : Scratch (resReg j) := by revert j; decide
theorem resReg_ne_alloc (j : Fin 2) (i : Fin 9) : resReg j ≠ allocReg i := by
  revert i j; decide

@[simp] theorem not_scratch_rsp : ¬ Scratch .rsp := by decide
@[simp] theorem not_scratch_r14 : ¬ Scratch .r14 := by decide
@[simp] theorem not_scratch_r15 : ¬ Scratch .r15 := by decide
@[simp] theorem not_scratch_rbx : ¬ Scratch .rbx := by decide
@[simp] theorem not_scratch_rbp : ¬ Scratch .rbp := by decide
@[simp] theorem not_scratch_r12 : ¬ Scratch .r12 := by decide
@[simp] theorem not_scratch_r13 : ¬ Scratch .r13 := by decide

/-- An assignment of Lir physical registers to allocatable x86-64 registers. -/
structure Assign (P : Type) where
  idx : P → Fin 9
  injective : Function.Injective idx

namespace Assign

variable {P : Type} (A : Assign P)

/-- The x86-64 register holding Lir register `p`. -/
def reg (p : P) : Reg := allocReg (A.idx p)

theorem reg_injective : Function.Injective A.reg :=
  fun _ _ h => A.injective (allocReg_injective h)

theorem reg_ne_rsp (p : P) : A.reg p ≠ .rsp := allocReg_ne_rsp _
theorem reg_ne_r14 (p : P) : A.reg p ≠ .r14 := allocReg_ne_r14 _
theorem reg_ne_r15 (p : P) : A.reg p ≠ .r15 := allocReg_ne_r15 _
theorem reg_ne_rax (p : P) : A.reg p ≠ .rax := allocReg_ne_rax _
theorem reg_ne_rcx (p : P) : A.reg p ≠ .rcx := allocReg_ne_rcx _
theorem reg_ne_rdx (p : P) : A.reg p ≠ .rdx := allocReg_ne_rdx _
theorem reg_ne_r11 (p : P) : A.reg p ≠ .r11 := allocReg_ne_r11 _
theorem not_scratch (p : P) : ¬ Scratch (A.reg p) := allocReg_not_scratch _

end Assign

/-- The canonical assignment of `Fin n` for `n ≤ 9`, for example the output
`Fin (k + 2)` of `Lir.Alloc.firstK k` with `k ≤ 7`. -/
def Assign.fin (n : Nat) (h : n ≤ 9) : Assign (Fin n) where
  idx := Fin.castLE h
  injective := Fin.castLE_injective h

end Silmaril.X86.Backend
