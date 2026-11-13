module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.BoundaryExecution.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.CommitFreshness.Thms
/-! Exact restored body execution and returned-value output copies, with real
partial reads, original output uniqueness and independent old/native memory. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.BoundaryExecution
open Silmaril.Compile Silmaril.Machine
open Silmaril.Machine.RTL.SSA
open InstructionSemantics RenamingSemantics CommitFreshness

theorem pullback_readAll (register : Nat → Nat) (source : Lir.Frame Nat) (registers : List Nat) :
    (pullback register source).readAll registers =
      source.readAll (registers.map (fun index => Lir.Loc.reg (register index))) := by
  simp only [Silmaril.Machine.RTL.Frame.readAll, Lir.Frame.readAll, List.mapM_map]
  rfl

theorem native_readAll_set_ne (source : Lir.Frame Nat) (destination : Nat) (word : Lir.Word)
    (registers : List Nat) (different : ∀ register ∈ registers, register ≠ destination) :
    (source.set destination word).readAll (registers.map Lir.Loc.reg) = source.readAll (registers.map Lir.Loc.reg) := by
  rw [← BlockSemantics.frame_readAll (source.set destination word) registers,
    ← BlockSemantics.frame_readAll source registers]
  apply Silmaril.Machine.RTL.SSA.readAll_congr
  intro register member
  change (source.set destination word).get register = source.get register
  simp only [Lir.Frame.get_set, different register member, ↓reduceIte]

theorem native_writeAll_frame (source : Lir.Frame Nat) (registers : List Nat) (words : List Lir.Word) :
    (source.writeAll (registers.map Lir.Loc.reg) words).map frame =
      (frame source).writeAll registers words := by
  induction registers generalizing source words with
  | nil => cases words <;> rfl
  | cons register rest ih =>
    cases words with
    | nil => rfl
    | cons word words =>
      exact ih (source.set register word) words

theorem native_readAll_writeAll {source final : Lir.Frame Nat} {registers : List Nat} {words : List Lir.Word}
    (written : source.writeAll (registers.map Lir.Loc.reg) words = some final) (unique : registers.Nodup) :
    final.readAll (registers.map Lir.Loc.reg) = some words := by
  have projected : (frame source).writeAll registers words = some (frame final) :=
    (native_writeAll_frame source registers words).symm.trans (by rw [written]; rfl)
  exact (BlockSemantics.frame_readAll final registers).symm.trans
    (Silmaril.Machine.RTL.SSA.readAll_writeAll projected unique)

/-- Actual range-separated sequential moves implement a writeAll of the
values read from the original source frame, retaining real partial reads. -/
theorem commits_of_readAll (base : Nat) (versions : List (Nat × Nat))
    (bounds : ∀ pair ∈ versions, pair.1 < base ∧ base ≤ pair.2)
    (calls : OpenCalls) (source : Lir.Frame Nat) (memory : Lir.Memory) (words : List Lir.Word)
    (read : source.readAll ((versions.map Prod.snd).map Lir.Loc.reg) = some words) :
    ∃ final, InstructionsExec calls (commitInstrs versions) source memory final memory ∧
      source.writeAll ((versions.map Prod.fst).map Lir.Loc.reg) words = some final := by
  induction versions generalizing source words with
  | nil =>
    have empty : words = [] := (Option.some.inj read).symm
    exact ⟨source, .nil, empty ▸ rfl⟩
  | cons pair rest ih =>
    show ∃ final, InstructionsExec calls (commitInstrs (pair :: rest)) source memory final memory ∧
      source.writeAll (((pair :: rest).map Prod.fst).map Lir.Loc.reg) words = some final
    have original : (frame source).readAll (pair.2 :: rest.map Prod.snd) = some words := by
      rw [BlockSemantics.frame_readAll]
      exact read
    obtain ⟨word, tailWords, firstRead, tailRead, same⟩ := Silmaril.Machine.RTL.SSA.readAll_cons_eq_some.mp original
    have restRead : source.readAll ((rest.map Prod.snd).map Lir.Loc.reg) = some tailWords :=
      (BlockSemantics.frame_readAll source _).symm.trans tailRead
    have separated : ∀ register ∈ rest.map Prod.snd, register ≠ pair.1 := by
      intro register member
      obtain ⟨other, included, same⟩ := List.mem_map.mp member
      have low : pair.1 < base := (bounds pair (List.mem_cons_self)).1
      have high : base ≤ register := same ▸ (bounds other (List.mem_cons_of_mem _ included)).2
      omega
    have afterRead : (source.set pair.1 word).readAll ((rest.map Prod.snd).map Lir.Loc.reg) = some tailWords :=
      (native_readAll_set_ne source pair.1 word (rest.map Prod.snd) separated).trans restRead
    obtain ⟨final, native, written⟩ := ih (fun other member => bounds other (List.mem_cons_of_mem _ member))
      (source.set pair.1 word) tailWords afterRead
    refine ⟨final, .cons (.op ?_) native, ?_⟩
    · have selected : source.get pair.2 = some word := firstRead
      simp only [Lir.Op.exec, selected, Option.map_some]
    · simpa only [same, List.map_cons, Lir.Frame.writeAll, Lir.Frame.write] using written

theorem define_unique (state : Rename) (unique : (state.versions.map Prod.fst).Nodup) (original : Nat) :
    (((define original).run state).2.versions.map Prod.fst).Nodup := by
  change ((original, state.next) :: state.versions.filter (fun pair => pair.1 != original)).map Prod.fst |>.Nodup
  rw [List.map_cons, List.nodup_cons]
  constructor
  · intro member
    obtain ⟨pair, included, same⟩ := List.mem_map.mp member
    have different : pair.1 ≠ original := by simpa only [List.mem_filter, bne_iff_ne] using (List.mem_filter.mp included).2
    exact different same
  · exact List.Nodup.sublist (List.filter_sublist.map Prod.fst) unique

theorem defineResults_unique (state : Rename) (unique : (state.versions.map Prod.fst).Nodup) (registers : List Nat) :
    (((registers.mapM define).run state).2.versions.map Prod.fst).Nodup := by
  induction registers generalizing state with
  | nil => exact unique
  | cons register rest ih =>
    rw [defineResults_cons]
    exact ih ((define register).run state).2 (define_unique state unique register)

theorem renameOp_unique (state : Rename) (unique : (state.versions.map Prod.fst).Nodup) (operation : Lir.Op Nat) :
    (((renameOp operation).run state).2.versions.map Prod.fst).Nodup := by
  cases operation <;> first | exact unique | exact define_unique state unique _

theorem renameInstr_unique (state : Rename) (unique : (state.versions.map Prod.fst).Nodup) (instruction : Mir.Instr) :
    (((renameInstr instruction).run state).2.versions.map Prod.fst).Nodup := by
  cases instruction with
  | op operation => exact renameOp_unique state unique operation
  | fop operation destination left right => exact define_unique state unique destination
  | addr destination symbol offset => exact define_unique state unique destination
  | call symbol args results =>
    rw [renameInstr_call_run]
    exact defineResults_unique state unique results
  | callIndirect target args results =>
    rw [renameInstr_indirect_run]
    exact defineResults_unique state unique results

theorem renameList_unique (state : Rename) (unique : (state.versions.map Prod.fst).Nodup)
    (instructions : List Mir.Instr) :
    (((instructions.mapM renameInstr).run state).2.versions.map Prod.fst).Nodup := by
  induction instructions generalizing state with
  | nil => exact unique
  | cons instruction rest ih =>
    rw [renameInstrs_cons]
    exact ih ((renameInstr instruction).run state).2 (renameInstr_unique state unique instruction)

theorem enter_outputs_unique (base : Nat) (block : Mir.Block) :
    ((enter base block).outputs.map Prod.fst).Nodup := by
  have unique := renameList_unique ({next := base} : Rename) (by simp) block.instrs.toList
  simpa only [enter, renameArray_run] using unique

theorem view_outputs_unique {base : Nat} {block : Mir.Block} {result : View}
    (accepted : view base block = some result) : result.outputs.Nodup := by
  obtain ⟨_, _, _, outputs, _⟩ := view_shape accepted
  rw [outputs]
  exact enter_outputs_unique base block

theorem commits_readAll (base : Nat) (versions : List (Nat × Nat))
    (bounds : ∀ pair ∈ versions, pair.1 < base ∧ base ≤ pair.2)
    (unique : (versions.map Prod.fst).Nodup)
    (calls : OpenCalls) (source : Lir.Frame Nat) (memory : Lir.Memory) (words : List Lir.Word)
    (read : source.readAll ((versions.map Prod.snd).map Lir.Loc.reg) = some words) :
    ∃ final, InstructionsExec calls (commitInstrs versions) source memory final memory ∧
      final.readAll ((versions.map Prod.fst).map Lir.Loc.reg) = some words ∧
      source.writeAll ((versions.map Prod.fst).map Lir.Loc.reg) words = some final ∧
      final.slots = source.slots ∧
      ∀ register, base ≤ register → final.get register = source.get register := by
  obtain ⟨final, executed, written⟩ := commits_of_readAll base versions bounds calls source memory words read
  obtain ⟨_, slots, high⟩ := commitInstrs_preserves_fresh base versions
    (fun pair member => (bounds pair member).1) calls source final memory memory executed
  exact ⟨final, executed, native_readAll_writeAll written unique, written, slots, high⟩

theorem outputVersions_fst (outputs values : List Nat) (register : Nat → Nat)
    (width : values.length = outputs.length) :
    ((outputs.zip values).map (fun (original, value) => (original, register value))).map Prod.fst = outputs := by
  exact (List.map_map ..).trans (List.map_fst_zip (Nat.le_of_eq width.symm))

theorem outputVersions_snd (outputs values : List Nat) (register : Nat → Nat)
    (width : values.length = outputs.length) :
    ((outputs.zip values).map (fun (original, value) => (original, register value))).map Prod.snd = values.map register := by
  calc
    _ = ((outputs.zip values).map Prod.snd).map register := by simp only [List.map_map, Function.comp_def]
    _ = values.map register := congrArg (List.map register) (List.map_snd_zip (Nat.le_of_eq width))

/-- Restored execution on the original native pullback supplies the actual
flattened returns. Range-separated real commits then recover those words in
ordered, unique original output registers. No completed entry frame is used. -/
theorem restored_boundary_execution {function : Mir.Func} {block candidate : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (accepted : view (freshBase function) block = some result)
    (restored : restore (freshBase function) block result (foldRegion [.unknown] result.region).1 = some candidate) :
    ∃ flattened body values instructions versions,
      ofLambdaSSA? [] (foldRegion [.unknown] result.region).1 result.annotation
        result.inputs.length result.outputs.length = some flattened ∧
      flattened.entry = 0 ∧ flattened.blocks = [body] ∧
      body.params = List.range result.inputs.length ∧ body.term = .ret values ∧
      values.length = result.outputs.length ∧
      body.ops.mapM (newOp (RestoreAdmission.register (freshBase function) result.inputs)) = some instructions ∧
      versions = (result.outputs.zip values).map (fun (original, value) =>
        (original, RestoreAdmission.register (freshBase function) result.inputs value)) ∧
      candidate = ⟨(instructions ++ commitInstrs versions).toArray, block.term⟩ ∧
      (∀ pair ∈ versions, pair.1 < freshBase function ∧ freshBase function ≤ pair.2) ∧
      result.outputs.Nodup ∧
      ∀ (calls : OpenCalls) (oracle : Silmaril.Machine.RTL.CallOracle)
        (source : Lir.Frame Nat) (memory : Lir.Memory)
        (oldMemory oldAfter : Silmaril.Machine.Lir.Memory) (oldFinal : Silmaril.Machine.RTL.Frame Nat)
        (words : List Lir.Word),
        Silmaril.Machine.RTL.SSA.Ops.Exec oracle body.ops
            (pullback (RestoreAdmission.register (freshBase function) result.inputs) source)
            oldMemory oldFinal oldAfter →
        oldFinal.readAll values = some words →
        ∃ afterBody final,
          InstructionsExec calls instructions source memory afterBody memory ∧
          pullback (RestoreAdmission.register (freshBase function) result.inputs) afterBody = oldFinal ∧
          InstructionsExec calls (commitInstrs versions) afterBody memory final memory ∧
          InstructionsExec calls candidate.instrs.toList source memory final memory ∧
          final.readAll (result.outputs.map Lir.Loc.reg) = some words ∧
          afterBody.writeAll (result.outputs.map Lir.Loc.reg) words = some final ∧
          final.slots = source.slots ∧ oldAfter = oldMemory ∧
          ∀ register, freshBase function ≤ register → final.get register = afterBody.get register := by
  obtain ⟨flattened, body, values, instructions, compiled, entry, singleton, parameters,
    returned, width, converted, emitted, fresh, bounds⟩ := restored_commit_bounds member accepted restored
  let register := RestoreAdmission.register (freshBase function) result.inputs
  let versions := (result.outputs.zip values).map (fun (original, value) => (original, register value))
  have destinations : versions.map Prod.fst = result.outputs := outputVersions_fst _ _ register width
  have sources : versions.map Prod.snd = values.map register := outputVersions_snd _ _ register width
  have shape : candidate = ⟨(instructions ++ commitInstrs versions).toArray, block.term⟩ := by
    simpa only [versions, register, commitInstrs, List.map_map, Function.comp_def] using emitted
  have unique : result.outputs.Nodup := view_outputs_unique accepted
  refine ⟨flattened, body, values, instructions, versions, compiled, entry, singleton, parameters,
    returned, width, converted, rfl, shape, bounds, unique, ?_⟩
  intro calls oracle source memory oldMemory oldAfter oldFinal words oldExecuted returnedWords
  obtain ⟨afterBody, bodyExecuted, pulled, bodySlots, oldMemorySame⟩ :=
    (view_instructions_iff member accepted body.ops instructions converted calls oracle source memory
      oldMemory oldAfter oldFinal).mp oldExecuted
  have nativeRead : afterBody.readAll ((versions.map Prod.snd).map Lir.Loc.reg) = some words := by
    rw [sources]
    have selected := (pullback_readAll register afterBody values).symm.trans (pulled ▸ returnedWords)
    simpa only [List.map_map, Function.comp_def] using selected
  obtain ⟨final, copiesExecuted, outputs, written, copySlots, high⟩ := commits_readAll
    (freshBase function) versions bounds (destinations ▸ unique) calls afterBody memory words nativeRead
  refine ⟨afterBody, final, bodyExecuted, pulled, copiesExecuted, ?_, ?_, ?_,
    copySlots.trans bodySlots, oldMemorySame, high⟩
  · simpa only [shape, List.toList_toArray] using InstructionsExec.append bodyExecuted copiesExecuted
  · simpa only [destinations] using outputs
  · simpa only [destinations] using written

end Silmaril.Compiler.Native.Optimize.LambdaSSA.BoundaryExecution
