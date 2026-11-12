module

public import Silmaril.Compiler.Native.Optimize.Open.CSE.Defs
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.CSE

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics

theorem instruction (summaries : OpenCalls) (facts : Facts) {instruction : Mir.Instr}
    {source final : Lir.Frame Nat} {memory finalMemory : Lir.Memory}
    (held : Mir.CSE.Holds facts source)
    (executed : InstructionExec summaries instruction source memory final finalMemory) :
    InstructionExec summaries (Mir.CSE.rwInstr facts instruction).1 source memory final finalMemory ∧
      Mir.CSE.Holds (Mir.CSE.rwInstr facts instruction).2 final := by
  cases executed with
  | op executed =>
    obtain ⟨candidate, next⟩ := Mir.CSE.rwOp_correct held executed
    exact ⟨.op candidate, next⟩
  | @fop op dest a b source memory final executed =>
    show InstructionExec summaries (.fop op dest a b) source memory final memory ∧
      Mir.CSE.Holds (Mir.CSE.kill facts dest) final
    refine ⟨.fop executed, ?_⟩
    have values : ∃ left, source.get a = some left ∧ ∃ right, source.get b = some right ∧
        source.set dest (op.eval left right) = final := by
      simpa only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] using executed
    obtain ⟨left, _, right, _, written⟩ := values
    exact written ▸ Mir.CSE.holds_kill held dest (op.eval left right)
  | addr resolved => exact ⟨.addr resolved, Mir.CSE.holds_kill held _ _⟩
  | call read summary write => exact ⟨.call read summary write, by simp [Mir.CSE.rwInstr, Mir.CSE.Holds]⟩
  | indirect target read summary write => exact ⟨.indirect target read summary write, by simp [Mir.CSE.rwInstr, Mir.CSE.Holds]⟩

theorem instructions (summaries : OpenCalls) (facts : Facts) {instructions : List Mir.Instr}
    {source final : Lir.Frame Nat} {memory finalMemory : Lir.Memory}
    (held : Mir.CSE.Holds facts source)
    (executed : InstructionsExec summaries instructions source memory final finalMemory) :
    InstructionsExec summaries (Mir.CSE.rwList facts instructions).1 source memory final finalMemory ∧
      Mir.CSE.Holds (Mir.CSE.rwList facts instructions).2 final := by
  induction executed generalizing facts with
  | nil => exact ⟨.nil, held⟩
  | cons first rest ih =>
    obtain ⟨candidate, next⟩ := instruction summaries facts held first
    obtain ⟨candidateRest, last⟩ := ih _ next
    exact ⟨.cons candidate candidateRest, last⟩

theorem block (summaries : OpenCalls) {sourceBlock : Mir.Block}
    {source final : Lir.Frame Nat} {memory finalMemory : Lir.Memory} {exit : BlockExit}
    (executed : BlockExec summaries sourceBlock source memory exit final finalMemory) :
    BlockExec summaries (Mir.CSE.rwBlock sourceBlock) source memory exit final finalMemory := by
  obtain ⟨candidate, _⟩ := instructions summaries [] (by simp [Mir.CSE.Holds]) executed.1
  exact ⟨by simpa only [Mir.CSE.rwBlock, List.toList_toArray] using candidate, executed.2⟩

theorem block_found {function : Mir.Func} {label : Nat} {sourceBlock : Mir.Block}
    (found : function.blocks[label]? = some sourceBlock) :
    (Mir.CSE.rwFunc function).blocks[label]? = some (Mir.CSE.rwBlock sourceBlock) := by
  simp only [Mir.CSE.rwFunc, Array.getElem?_map, found, Option.map_some]

theorem jump (summaries : OpenCalls) {function : Mir.Func} {source target : OpenFrame.State}
    (executed : OpenFrame.Step summaries function source target) :
    OpenFrame.Step summaries (Mir.CSE.rwFunc function) source target := by
  cases executed with
  | jump found executed => exact .jump (block_found found) (block summaries executed)

theorem run (summaries : OpenCalls) {function : Mir.Func} {source : OpenFrame.State} {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck) :
    OpenFrame.Run summaries (Mir.CSE.rwFunc function) source behavior := by
  revert successful
  induction executed with
  | @stop source behavior stopped =>
    intro successful
    cases behavior with
    | returned values memory | trapped memory =>
      obtain ⟨sourceBlock, final, found, executed⟩ := stopped
      exact .stop ⟨_, final, block_found found, block summaries executed⟩
    | stuck => exact False.elim (successful rfl)
    | diverges => exact False.elim stopped
  | next step rest ih =>
    intro successful
    exact .next (jump summaries step) (ih successful)

theorem instruction_call_free (facts : Facts) {source : Mir.Instr} (free : OpenFrame.CallFree source) :
    OpenFrame.CallFree (Mir.CSE.rwInstr facts source).1 := by
  cases source <;> simp_all [Mir.CSE.rwInstr, OpenFrame.CallFree]

theorem instructions_call_free (facts : Facts) {source : List Mir.Instr}
    (free : ∀ instruction ∈ source, OpenFrame.CallFree instruction) :
    ∀ instruction ∈ (Mir.CSE.rwList facts source).1, OpenFrame.CallFree instruction := by
  induction source generalizing facts with
  | nil => simp [Mir.CSE.rwList]
  | cons first rest ih =>
    intro instruction member
    have located : instruction = (Mir.CSE.rwInstr facts first).1 ∨
        instruction ∈ (Mir.CSE.rwList (Mir.CSE.rwInstr facts first).2 rest).1 := by
      simpa only [Mir.CSE.rwList, List.mem_cons] using member
    cases located with
    | inl same => exact same.symm ▸ instruction_call_free facts (free first (by simp))
    | inr member => exact ih _ (fun instruction member => free instruction (by simp [member])) instruction member

theorem block_call_free {source : Mir.Block} (free : OpenFrame.BlockCallFree source) :
    OpenFrame.BlockCallFree (Mir.CSE.rwBlock source) := by
  simpa only [OpenFrame.BlockCallFree, Mir.CSE.rwBlock, List.toList_toArray] using
    instructions_call_free [] free

theorem function_call_free {source : Mir.Func} (free : OpenFrame.FunctionCallFree source) :
    OpenFrame.FunctionCallFree (Mir.CSE.rwFunc source) := by
  intro label candidate found
  have selected : ∃ block, source.blocks[label]? = some block ∧ Mir.CSE.rwBlock block = candidate := by
    simpa only [Mir.CSE.rwFunc, Array.getElem?_map, Option.map_eq_some_iff] using found
  obtain ⟨block, original, rfl⟩ := selected
  exact block_call_free (free label block original)

theorem observations_exact (summaries : OpenCalls) {function : Mir.Func}
    (free : OpenFrame.FunctionCallFree function) (source : OpenFrame.State) {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck)
    (other : Lir.Behavior) :
    OpenFrame.Behaves summaries (Mir.CSE.rwFunc function) source other ↔ other = behavior := by
  have candidate : OpenFrame.Run summaries (Mir.CSE.rwFunc function) source behavior := run summaries executed successful
  have candidateFree : OpenFrame.FunctionCallFree (Mir.CSE.rwFunc function) := function_call_free free
  constructor
  · intro observed
    cases other with
    | diverges => exact False.elim (OpenFrame.run_no_infinite candidateFree candidate observed)
    | returned values memory | trapped memory | stuck =>
      obtain ⟨final, steps, stopped⟩ := observed
      exact (OpenFrame.run_unique candidateFree candidate (OpenFrame.run_prepend steps (.stop stopped))).symm
  · rintro rfl
    exact OpenFrame.run_behaves candidate

end Silmaril.Compiler.Native.Optimize.Open.CSE
