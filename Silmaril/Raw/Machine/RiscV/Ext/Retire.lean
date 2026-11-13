module

public import Silmaril.Machine.RiscV.Ext.Machine.Defs
/-!
# Consilience of the extended machine with the base RV64 model

For the 21 base instructions, the extended model agrees with the existing
local model `RiscV.step`:

* `Compute.step_base`: the decoded retirement function is `RiscV.step`;
* `step_of_base_decode`: whenever the fetched word is accepted by the base
  decoder `RiscV.decode`, one machine step retires with exactly
  `RiscV.step` on the registers and PC and leaves memory unchanged;
* `run_base_block`: a base block laid out with `RiscV.byteDecoder` in
  executable memory runs to `Block.run RiscV.step`.

`retireModel` instantiates the shared `RetireModel` contract for the
register-only part (`Compute`), and `retireModel_base` shows that it restricts
to `RiscV.retireModel`. Both models are local handwritten models.
-/

@[expose] public section

namespace Silmaril.RiscV.Ext

open Machine

/-- Register-only extended instructions as a sequential retirement model. -/
def retireModel : RetireModel Compute State Reg Word where
  read := State.read
  pc := State.pc
  step := Compute.step
  writes c reg := reg = c.dest
  pcDelta _ := 4
  step_pc c state := Compute.step_pc c state
  step_read_other c state reg h := Compute.step_read_other c state reg h

@[simp] theorem retireModel_step : retireModel.step = Compute.step := rfl
@[simp] theorem retireModel_pcDelta (c : Compute) : retireModel.pcDelta c = 4 := rfl

@[simp] theorem retireModel_writes (c : Compute) (reg : Reg) :
    retireModel.writes c reg ↔ reg = c.dest := Iff.rfl

/-- On base instructions the extended retirement model is the base one:
the same observation, PC, step, write set and PC advance. -/
theorem retireModel_base (instr : RiscV.Instr) :
    retireModel.step (.base instr) = RiscV.retireModel.step instr ∧
      (∀ reg, retireModel.writes (.base instr) reg ↔ RiscV.retireModel.writes instr reg) ∧
      retireModel.pcDelta (.base instr) = RiscV.retireModel.pcDelta instr ∧
      retireModel.read = RiscV.retireModel.read ∧ retireModel.pc = RiscV.retireModel.pc :=
  ⟨rfl, fun _ => Iff.rfl, rfl, rfl, rfl⟩

@[simp] theorem Block.run_compute_base (code : List RiscV.Instr) (s : State) :
    Block.run Compute.step (code.map .base) s = Block.run RiscV.step code s := by
  induction code generalizing s with
  | nil => rfl
  | cons instr rest ih => simp [ih]

/-- The four-byte-per-instruction PC law for register-only blocks. -/
theorem run_pc (code : List Compute) (s : State) :
    (Block.run Compute.step code s).pc = s.pc + BitVec.ofNat 64 (4 * code.length) :=
  retireModel.run_pc_uniform 4 (fun _ => rfl) code s

theorem run_read_frame (code : List Compute) (s : State) (r : Reg)
    (h : ∀ c ∈ code, r ≠ c.dest) :
    (Block.run Compute.step code s).read r = s.read r :=
  retireModel.run_read_frame code s r h

/-! ## One machine step on base instructions -/

theorem Instr.exec_ofBase (instr : RiscV.Instr) (m : MState) :
    (Instr.ofBase instr).exec m = .retired ⟨RiscV.step instr m.core, m.memory⟩ := rfl

/-- Any fetched word accepted by the base decoder retires with `RiscV.step`. -/
theorem MState.step_of_base_decode {m : MState} {word : BitVec 32} {instr : RiscV.Instr}
    (fetched : fetch m.memory m.core.pc = some word) (decoded : RiscV.decode word = some instr) :
    m.step = .retired ⟨RiscV.step instr m.core, m.memory⟩ := by
  simp [MState.step, fetched, decode_of_base decoded]

/-- Conversely, a step that decodes a base-form instruction used the base decoder. -/
theorem MState.base_decode_of_decode {word : BitVec 32} {instr : RiscV.Instr}
    (decoded : decode word = some (.ofBase instr)) : RiscV.decode word = some instr :=
  decode_ofBase_iff.mp decoded

theorem MState.step_base {m : MState} {instr : RiscV.Instr}
    (aligned : m.core.pc.toNat % 4 = 0)
    (bytes : m.memory.fetchBytes m.core.pc.toNat 4 = some (RiscV.encodeBytes instr)) :
    m.step = .retired ⟨RiscV.step instr m.core, m.memory⟩ := by
  rw [MState.step_of_fetchBytes (instr := .ofBase instr) aligned (by simpa using bytes)]
  rfl

theorem encodeBlock_base (code : List RiscV.Instr) :
    byteDecoder.encodeBlock ((code.map Compute.base).map Instr.compute) =
      RiscV.byteDecoder.encodeBlock code := by
  induction code with
  | nil => rfl
  | cons instr rest ih =>
    simp only [List.map_cons, Decoder.encodeBlock_cons, ih]
    rfl

/-- A base block, encoded by `RiscV.byteDecoder` and executable at an aligned
PC, runs in the extended machine exactly as `Block.run RiscV.step`. -/
theorem run_base_block (code : List RiscV.Instr) (m : MState)
    (aligned : m.core.pc.toNat % 4 = 0)
    (fetched : m.memory.fetchBytes m.core.pc.toNat (4 * code.length) =
      some (RiscV.byteDecoder.encodeBlock code)) :
    Execution.run MState.stepOpt code.length m =
      some ⟨Block.run RiscV.step code m.core, m.memory⟩ := by
  have := run_compute_block (code.map Compute.base) m aligned
    (by rw [encodeBlock_base]; simpa using fetched)
  simpa using this

end Silmaril.RiscV.Ext
