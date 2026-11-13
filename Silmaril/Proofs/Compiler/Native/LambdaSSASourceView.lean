module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.SourceView.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.EntryCompletion.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.SourceView
open Silmaril.Compile Silmaril.Machine
open EntryCompletion InstructionSemantics
open Silmaril.Machine.RTL (CallOracle Opcode packValues)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The original side of the actual enter output map is exactly the output
list published by the actual accepted view. -/
theorem view_outputs {base : Nat} {block : Mir.Block} {result : View}
    (accepted : view base block = some result) :
    sourceOutputs base block = result.outputs.map Lir.Loc.reg := by
  obtain ⟨_, _, _, _, outputs, _⟩ := BlockSemantics.view_function accepted
  rw [outputs]
  rfl

/-- Pointwise successful pair reads give the same actual list of words on
both original and versioned register lists, preserving their actual order. -/
theorem paired_readAll (versions : List (Nat × Nat)) (source target : Lir.Frame Nat)
    (defined : ∀ pair ∈ versions, ∃ word,
      source.get pair.1 = some word ∧ target.get pair.2 = some word) :
    ∃ values, source.readAll ((versions.map Prod.fst).map Lir.Loc.reg) = some values ∧
      target.readAll ((versions.map Prod.snd).map Lir.Loc.reg) = some values := by
  induction versions with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons pair rest ih =>
    obtain ⟨word, original, versioned⟩ := defined pair (by simp)
    obtain ⟨words, originalRest, versionedRest⟩ := ih (fun pair member => defined pair (by simp [member]))
    refine ⟨word :: words, ?_, ?_⟩
    · have first : source.read (.reg pair.1) = some word := original
      have tail : ((rest.map Prod.fst).map Lir.Loc.reg).mapM source.read = some words := originalRest
      simp only [List.map_cons, Lir.Frame.readAll, List.mapM_cons, first, tail]
      rfl
    · have first : target.read (.reg pair.2) = some word := versioned
      have tail : ((rest.map Prod.snd).map Lir.Loc.reg).mapM target.read = some words := versionedRest
      simp only [List.map_cons, Lir.Frame.readAll, List.mapM_cons, first, tail]
      rfl

/-- Final real cursor invariants derive all output reads; no successful
output-read premise is supplied. -/
theorem versions_readAll {base : Nat} {cursor : Rename} {source target : Lir.Frame Nat}
    (valid : cursor.Valid base) (defined : cursor.Defined source)
    (agreed : cursor.Agrees base source target) :
    ∃ values, source.readAll ((cursor.versions.map Prod.fst).map Lir.Loc.reg) = some values ∧
      target.readAll ((cursor.versions.map Prod.snd).map Lir.Loc.reg) = some values := by
  apply paired_readAll
  intro pair member
  obtain ⟨word, original⟩ := defined pair member
  have bounds := valid.2 pair member
  have versioned : target.get pair.2 = source.get pair.1 := by
    simpa only [bounds.2.2] using agreed.2 pair.1 bounds.1
  exact ⟨word, original, versioned.trans original⟩

/-- Actual original source execution derives entered execution and matching
complete output-map values from real Valid, Defined and Agrees invariants. -/
theorem source_entered_outputs {base : Nat} {block : Mir.Block} {calls : OpenCalls}
    {source final : Lir.Frame Nat} {memory after : Lir.Memory}
    (usesBelow : ∀ instruction ∈ block.instrs.toList, ∀ register ∈ uses instruction, register < base)
    (defsBelow : ∀ instruction ∈ block.instrs.toList, ∀ register ∈ defs instruction, register < base)
    (executed : InstructionsExec calls block.instrs.toList source memory final after) :
    ∃ entered values,
      InstructionsExec calls (enter base block).body.instrs.toList source memory entered after ∧
      final.readAll (sourceOutputs base block) = some values ∧
      entered.readAll (enteredOutputs base block) = some values := by
  obtain ⟨entered, run, agreed⟩ := enter_body_exec usesBelow executed
  obtain ⟨valid, defined⟩ := renameInstrs_valid_defined (valid_initial base)
    (defined_initial base source) defsBelow executed
  obtain ⟨values, original, versioned⟩ := versions_readAll valid defined agreed
  have outputs : (enter base block).outputs =
      ((block.instrs.toList.mapM renameInstr).run {next := base}).2.versions := by
    simp only [enter, renameArray_run]
  exact ⟨entered, values, run, by simpa only [sourceOutputs, outputs] using original,
    by simpa only [enteredOutputs, outputs] using versioned⟩

/-- Original source success now derives completed-view evaluation. Entered
execution and every output read are conclusions of the actual source run. -/
theorem source_view_eval {base : Nat} {block : Mir.Block} {result : View}
    (accepted : view base block = some result)
    (usesBelow : ∀ instruction ∈ block.instrs.toList, ∀ register ∈ uses instruction, register < base)
    (defsBelow : ∀ instruction ∈ block.instrs.toList, ∀ register ∈ defs instruction, register < base)
    (calls : OpenCalls) (oracle : CallOracle)
    (signatures : Silmaril.Machine.RTL.SSA.CallOracle.MatchesSigs oracle [])
    (source final : Lir.Frame Nat) (memory after : Lir.Memory)
    (executed : InstructionsExec calls block.instrs.toList source memory final after)
    (environment : Silmaril.Isotope.LambdaSSA.Semantics.Env Lir.Word)
    (input : environment 0 = packValues (arguments (frame source) result.inputs))
    (before : Silmaril.Machine.Lir.Memory) :
    after = memory ∧ ∃ values, final.readAll (result.outputs.map Lir.Loc.reg) = some values ∧
      Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval (Opcode.step oracle)
        environment result.region before 0 (packValues values) before := by
  obtain ⟨entered, values, run, originalRead, enteredRead⟩ :=
    source_entered_outputs usesBelow defsBelow executed
  obtain ⟨converted, _, conversion, _⟩ := BlockSemantics.view_function accepted
  have preserved := native_instructions_preserve _ converted conversion calls run
  have enteredRun : InstructionsExec calls (enter base block).body.instrs.toList
      source memory entered memory := by simpa only [preserved.2] using run
  have sourceRead : final.readAll (result.outputs.map Lir.Loc.reg) = some values := by
    rw [← view_outputs accepted]
    exact originalRead
  exact ⟨preserved.2, values, sourceRead,
    view_completed_eval accepted calls oracle signatures source entered memory enteredRun values
      enteredRead environment input before⟩


/-- Actual membership in a real function bounds every source operand by its
actual freshBase, including operands that are later overwritten. -/
theorem freshBase_uses {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) {instruction : Mir.Instr}
    (inBlock : instruction ∈ block.instrs.toList) {register : Nat}
    (used : register ∈ uses instruction) : register < freshBase function := by
  apply RestoreAdmission.freshBase_input (base := freshBase function) member
  change register ∈ (block.instrs.toList.flatMap uses ++ Mir.DeadCode.termUses block.term).dedup
  exact List.mem_dedup.mpr (List.mem_append_left _ (List.mem_flatMap.mpr ⟨instruction, inBlock, used⟩))

/-- Actual freshBase also bounds every original destination mentioned by the
actual member block. This bound supplies rename Valid's original-name side. -/
theorem freshBase_defs {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) {instruction : Mir.Instr}
    (inBlock : instruction ∈ block.instrs.toList) {register : Nat}
    (written : register ∈ defs instruction) : register < freshBase function := by
  have included : register ∈ function.params ++ function.blocks.toList.flatMap (fun block =>
      Mir.DeadCode.termUses block.term ++ block.instrs.toList.flatMap (fun instruction =>
        uses instruction ++ defs instruction)) := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨block, member, List.mem_append_right _ ?_⟩
    exact List.mem_flatMap.mpr ⟨instruction, inBlock, List.mem_append_right _ written⟩
  exact Nat.lt_succ_of_le (RestoreAdmission.member_le_foldl_max included 0)

/-- Real-function specialization: actual block membership and actual freshBase
supply every source use/definition bound. The only execution premise is the
actual original source instruction list; entered execution and reads are derived. -/
theorem function_source_view_eval {function : Mir.Func} {block : Mir.Block} {result : View}
    (member : block ∈ function.blocks.toList)
    (accepted : view (freshBase function) block = some result)
    (calls : OpenCalls) (oracle : CallOracle)
    (signatures : Silmaril.Machine.RTL.SSA.CallOracle.MatchesSigs oracle [])
    (source final : Lir.Frame Nat) (memory after : Lir.Memory)
    (executed : InstructionsExec calls block.instrs.toList source memory final after)
    (environment : Silmaril.Isotope.LambdaSSA.Semantics.Env Lir.Word)
    (input : environment 0 = packValues (arguments (frame source) result.inputs))
    (before : Silmaril.Machine.Lir.Memory) :
    after = memory ∧ ∃ values,
      final.readAll (result.outputs.map Lir.Loc.reg) = some values ∧
      Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval (Opcode.step oracle)
        environment result.region before 0 (packValues values) before :=
  source_view_eval accepted (fun _ inBlock _ used => freshBase_uses member inBlock used)
    (fun _ inBlock _ written => freshBase_defs member inBlock written)
    calls oracle signatures source final memory after executed environment input before

end Silmaril.Compiler.Native.Optimize.LambdaSSA.SourceView
