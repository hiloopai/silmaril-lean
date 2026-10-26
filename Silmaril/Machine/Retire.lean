module

public import Silmaril.Machine.Block

/-!
# Straight-line retirement models

A `RetireModel` packages the facts about an already-decoded, straight-line
instruction fragment that block-level frame and PC arguments need: a register
observation, a 64-bit program counter, a total step function, a may-write
relation on registers, and a per-instruction sequential PC advance.

The model is an ordinary structure passed as an argument, not an ISA typeclass.
It does not describe fetch, decoding, branches, faults, memory, or registers that
the backend chooses not to expose through `read` (for example, x86 flags may be
kept outside `Reg`). `writes` is a may-write over-approximation: an instruction
may write no observed register, several, or a register it only conditionally
changes. The only laws are the sequential PC advance and preservation of every
register outside `writes`.
-/

@[expose] public section

namespace Silmaril.Machine

universe u v w x

/-- Laws for sequential retirement of decoded instructions. `pcDelta` is the
instruction's byte length in the backend's own encoding; PC arithmetic is
modulo `2^64`. -/
structure RetireModel (Instr : Type u) (State : Type v) (Reg : Type w) (Word : Type x) where
  /-- Architectural read of an observed register, including any aliasing policy. -/
  read : State → Reg → Word
  /-- The program counter. -/
  pc : State → BitVec 64
  /-- Retirement of one decoded instruction with sequential next PC. -/
  step : Instr → State → State
  /-- Registers the instruction may change; all others are preserved. -/
  writes : Instr → Reg → Prop
  /-- The sequential PC advance of one instruction, in bytes. -/
  pcDelta : Instr → Nat
  step_pc : ∀ instr state, pc (step instr state) = pc state + BitVec.ofNat 64 (pcDelta instr)
  step_read_other : ∀ instr state reg, ¬ writes instr reg →
    read (step instr state) reg = read state reg

namespace RetireModel

variable {Instr : Type u} {State : Type v} {Reg : Type w} {Word : Type x}
variable (model : RetireModel Instr State Reg Word)

/-- Total sequential PC advance of a block, as a natural number. -/
def size (code : List Instr) : Nat := (code.map model.pcDelta).sum

@[simp] theorem size_nil : model.size [] = 0 := rfl

@[simp] theorem size_cons (instr : Instr) (rest : List Instr) :
    model.size (instr :: rest) = model.pcDelta instr + model.size rest := by
  simp [size]

theorem size_append (first second : List Instr) :
    model.size (first ++ second) = model.size first + model.size second := by
  simp [size]

/-- Every instruction advancing the PC by `delta` bytes gives a block size of
`delta` times the instruction count. -/
theorem size_uniform (delta : Nat) (uniform : ∀ instr, model.pcDelta instr = delta)
    (code : List Instr) : model.size code = delta * code.length := by
  induction code with
  | nil => rfl
  | cons instr rest ih => rw [size_cons, ih, uniform, List.length_cons, Nat.mul_add, Nat.mul_one,
      Nat.add_comm]

/-- The PC after a straight-line block is the initial PC plus the block size,
modulo `2^64`. -/
theorem run_pc (code : List Instr) (state : State) :
    model.pc (Block.run model.step code state) = model.pc state + BitVec.ofNat 64 (model.size code) := by
  induction code generalizing state with
  | nil => simp
  | cons instr rest ih =>
    rw [Block.run_cons, ih, model.step_pc, size_cons, BitVec.ofNat_add, BitVec.add_assoc]

/-- The uniform-length case of `run_pc`, such as a fixed-width encoding. -/
theorem run_pc_uniform (delta : Nat) (uniform : ∀ instr, model.pcDelta instr = delta)
    (code : List Instr) (state : State) :
    model.pc (Block.run model.step code state) =
      model.pc state + BitVec.ofNat 64 (delta * code.length) := by
  rw [run_pc, size_uniform model delta uniform]

/-- A register that no instruction of the block may write keeps its value. -/
theorem run_read_frame (code : List Instr) (state : State) (reg : Reg)
    (h : ∀ instr ∈ code, ¬ model.writes instr reg) :
    model.read (Block.run model.step code state) reg = model.read state reg := by
  induction code generalizing state with
  | nil => rfl
  | cons instr rest ih =>
    rw [Block.run_cons, ih _ (fun next hn => h next (List.mem_cons_of_mem instr hn))]
    exact model.step_read_other instr state reg (h instr List.mem_cons_self)

end RetireModel
end Silmaril.Machine
