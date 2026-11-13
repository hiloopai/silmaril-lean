module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ViewTyping.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ScopeTyping.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Admission.Thms
public import Silmaril.Compiler.Native.Optimize.LocalSSA.Thms
/-! Source-derived static admission of the actual native arithmetic view into
existing `RootFits`, including actual array renaming, operand versions, prefix
scopes, the singleton dominator wrapper and exact flattening annotation. -/
@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.ViewTyping
open Silmaril.Machine.RTL.SSA (Scope)
open Silmaril.Machine

theorem allocates_refl (state : Rename) : Allocates state state [] :=
  fun _ member => .inl member

theorem allocates_trans {before middle after : Rename} {first rest : List Nat}
    (head : Allocates before middle first) (tail : Allocates middle after rest) :
    Allocates before after (first ++ rest) := by
  intro pair member
  obtain previous | emitted := tail pair member
  · obtain original | emitted := head pair previous
    · exact .inl original
    · exact .inr (List.mem_append_left _ emitted)
  · exact .inr (List.mem_append_right _ emitted)

theorem define_allocates (register : Nat) (state : Rename) :
    Allocates state ((define register).run state).2 [((define register).run state).1] := by
  change ∀ pair ∈ (register, state.next) :: state.versions.filter (fun pair => pair.1 != register),
    pair ∈ state.versions ∨ pair.2 ∈ [state.next]
  intro pair member
  obtain rfl | member := List.mem_cons.mp member
  · exact .inr List.mem_cons_self
  · exact .inl (List.mem_filter.mp member).1

theorem read_available {scope : Scope Nat} {state : Rename} (versions : Available scope state)
    {register : Nat} (original : scope.HasReg register) : scope.HasReg (state.read register) := by
  unfold Rename.read
  cases found : state.versions.find? (fun pair => pair.1 == register) with
  | none => exact original
  | some pair => exact versions pair (List.mem_of_find?_eq_some found)

theorem available_push {scope : Scope Nat} {state : Rename} (versions : Available scope state)
    (registers : List Nat) : Available (scope.push registers) state := by
  intro pair member
  exact (versions pair member).mono (by intro registers member; exact List.mem_cons_of_mem _ member)

theorem available_allocates {scope : Scope Nat} {before after : Rename} {emitted : List Nat}
    (versions : Available scope before) (allocated : Allocates before after emitted) :
    Available (scope.push emitted) after := by
  intro pair member
  obtain old | fresh := allocated pair member
  · exact available_push versions emitted pair old
  · exact ⟨emitted, List.mem_cons_self, fresh⟩

theorem defineMany_allocates (registers : List Nat) (state : Rename) :
    Allocates state ((registers.mapM define).run state).2 ((registers.mapM define).run state).1 := by
  induction registers generalizing state with
  | nil => exact allocates_refl state
  | cons register rest ih =>
    rw [List.mapM_cons]
    change Allocates state
      ((rest.mapM define).run ((define register).run state).2).2
      (((define register).run state).1 :: ((rest.mapM define).run ((define register).run state).2).1)
    exact allocates_trans (define_allocates register state) (ih ((define register).run state).2)

theorem renameOp_allocates (instruction : Lir.Op Nat) (state : Rename) :
    Allocates state ((renameOp instruction).run state).2
      (defs (.op ((renameOp instruction).run state).1)) := by
  cases instruction with
  | const register value => exact define_allocates register state
  | move register source => exact define_allocates register state
  | unary operation register source => exact define_allocates register state
  | binary operation register left right => exact define_allocates register state
  | load width extension register base offset => exact define_allocates register state
  | slotGet register slot => exact define_allocates register state
  | store | slotSet => exact allocates_refl state

theorem renameOp_uses (instruction : Lir.Op Nat) (state : Rename) :
    uses (.op ((renameOp instruction).run state).1) =
      (uses (.op instruction)).map state.read := by
  cases instruction <;> rfl

theorem renameInstr_allocates (instruction : Silmaril.Compile.Mir.Instr) (state : Rename) :
    Allocates state ((renameInstr instruction).run state).2
      (defs ((renameInstr instruction).run state).1) := by
  cases instruction with
  | op operation => exact renameOp_allocates operation state
  | fop _ register | addr register => exact define_allocates register state
  | call _ _ registers | callIndirect _ _ registers => exact defineMany_allocates registers state

theorem renameInstr_uses (instruction : Silmaril.Compile.Mir.Instr) (state : Rename) :
    uses ((renameInstr instruction).run state).1 = (uses instruction).map state.read := by
  cases instruction with
  | op operation => exact renameOp_uses operation state
  | fop | addr | call | callIndirect => rfl


theorem renameInstr_covers {scope : Scope Nat} {state : Rename}
    (versions : Available scope state) {instruction : Silmaril.Compile.Mir.Instr}
    (sources : scope.Covers (uses instruction)) :
    scope.Covers (uses ((renameInstr instruction).run state).1) := by
  rw [renameInstr_uses]
  intro register member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact read_available versions (sources original originalMember)

theorem oldOp_uses {instruction : Silmaril.Compile.Mir.Instr} {converted : Old.Op}
    (accepted : oldOp instruction = some converted) : converted.uses = uses instruction := by
  cases instruction with
  | op operation =>
    cases operation <;> simp only [oldOp] at accepted
    all_goals first
      | cases accepted; rfl
      | (obtain ⟨operation, _, rfl⟩ := Option.map_eq_some_iff.mp accepted; rfl)
      | contradiction
  | fop | addr | call | callIndirect => cases accepted

theorem oldOp_defs {instruction : Silmaril.Compile.Mir.Instr} {converted : Old.Op}
    (accepted : oldOp instruction = some converted) : converted.defs = defs instruction := by
  cases instruction with
  | op operation =>
    cases operation <;> simp only [oldOp] at accepted
    all_goals first
      | cases accepted; rfl
      | (obtain ⟨operation, _, rfl⟩ := Option.map_eq_some_iff.mp accepted; rfl)
      | contradiction
  | fop | addr | call | callIndirect => cases accepted

theorem prefixCovers_at {scope : Scope Nat} {instructions : List Old.Op}
    (covered : PrefixCovers scope instructions)
    (previous : List Old.Op) (instruction : Old.Op) (rest : List Old.Op)
    (same : instructions = previous ++ instruction :: rest) :
    (scope.afterOps previous).Covers instruction.uses := by
  subst instructions
  induction previous generalizing scope with
  | nil => exact covered.1
  | cons head tail ih => exact ih covered.2

theorem oldOps_cons {instruction : Silmaril.Compile.Mir.Instr}
    {rest : List Silmaril.Compile.Mir.Instr} {converted : List Old.Op}
    (accepted : (instruction :: rest).mapM oldOp = some converted) :
    ∃ head tail, oldOp instruction = some head ∧ rest.mapM oldOp = some tail ∧ converted = head :: tail := by
  have sequenced : (oldOp instruction).bind (fun head => (rest.mapM oldOp).bind
      (fun tail => some (head :: tail))) = some converted := by
    simpa [List.mapM_cons] using accepted
  obtain ⟨head, headAccepted, tailSequenced⟩ := Option.bind_eq_some_iff.mp sequenced
  obtain ⟨tail, tailAccepted, same⟩ := Option.bind_eq_some_iff.mp tailSequenced
  exact ⟨head, tail, headAccepted, tailAccepted, (Option.some.inj same).symm⟩

theorem renameList_scoped (instructions : List Silmaril.Compile.Mir.Instr)
    (scope : Scope Nat) (state : Rename) (converted : List Old.Op)
    (versions : Available scope state)
    (sources : ∀ instruction ∈ instructions, scope.Covers (uses instruction))
    (accepted : ((instructions.mapM renameInstr).run state).1.mapM oldOp = some converted) :
    PrefixCovers scope converted ∧
      Available (scope.afterOps converted) ((instructions.mapM renameInstr).run state).2 := by
  induction instructions generalizing scope state converted with
  | nil =>
    have same : converted = [] := Option.some.inj accepted.symm
    subst converted
    exact ⟨True.intro, versions⟩
  | cons instruction rest ih =>
    show PrefixCovers scope converted ∧ Available (scope.afterOps converted)
      ((((instruction :: rest).mapM renameInstr).run state).2)
    have renamed : (((instruction :: rest).mapM renameInstr).run state) =
        (((renameInstr instruction).run state).1 ::
          ((rest.mapM renameInstr).run ((renameInstr instruction).run state).2).1,
          ((rest.mapM renameInstr).run ((renameInstr instruction).run state).2).2) := by
      rw [List.mapM_cons]
      rfl
    have convertedCons : (((renameInstr instruction).run state).1 ::
        ((rest.mapM renameInstr).run ((renameInstr instruction).run state).2).1).mapM oldOp =
        some converted := by simpa only [renamed] using accepted
    obtain ⟨head, tail, headAccepted, tailAccepted, same⟩ := oldOps_cons convertedCons
    have headCovered : scope.Covers head.uses := by
      rw [oldOp_uses headAccepted]
      exact renameInstr_covers versions (sources instruction List.mem_cons_self)
    have nextAvailable : Available (scope.push head.defs) ((renameInstr instruction).run state).2 := by
      rw [oldOp_defs headAccepted]
      exact available_allocates versions (renameInstr_allocates instruction state)
    have nextSources : ∀ candidate ∈ rest, (scope.push head.defs).Covers (uses candidate) :=
      fun candidate member => (sources candidate (List.mem_cons_of_mem _ member)).push _
    obtain ⟨tailCovered, finalAvailable⟩ := ih (scope.push head.defs)
      ((renameInstr instruction).run state).2 tail nextAvailable nextSources tailAccepted
    have combined : PrefixCovers scope (head :: tail) ∧ Available (scope.afterOps (head :: tail))
        ((rest.mapM renameInstr).run ((renameInstr instruction).run state).2).2 :=
      ⟨⟨headCovered, tailCovered⟩, finalAvailable⟩
    simpa only [same, renamed] using combined

theorem enter_scoped (base : Nat) (source : Silmaril.Compile.Mir.Block)
    (converted : List Old.Op)
    (accepted : (enter base source).body.instrs.toList.mapM oldOp = some converted) :
    PrefixCovers (entryScope (enter base source).inputs) converted ∧
      (entryScope (enter base source).inputs |>.afterOps converted).Covers
        ((enter base source).outputs.map Prod.snd) := by
  have arrayRun : (source.instrs.mapM renameInstr).run ({next := base} : Rename) =
      (let result := (source.instrs.toList.mapM renameInstr).run ({next := base} : Rename)
       (result.1.toArray, result.2)) := renameArray_run source.instrs ({next := base} : Rename)
  have inputCovered : ∀ instruction ∈ source.instrs.toList,
      (entryScope (enter base source).inputs).Covers (uses instruction) := by
    intro instruction member register used
    refine ⟨(enter base source).inputs, List.mem_cons_self, ?_⟩
    change register ∈ (source.instrs.toList.flatMap uses ++
      Silmaril.Compile.Mir.DeadCode.termUses source.term).dedup
    exact List.mem_dedup.mpr (List.mem_append_left _ (List.mem_flatMap.mpr ⟨instruction, member, used⟩))
  have initialAvailable : Available (entryScope (enter base source).inputs) ({next := base} : Rename) :=
    fun pair member => by cases member
  have convertedList : ((source.instrs.toList.mapM renameInstr).run ({next := base} : Rename)).1.mapM
      oldOp = some converted := by
    simpa only [enter, arrayRun, List.toList_toArray] using accepted
  obtain ⟨prefixes, outputs⟩ := renameList_scoped source.instrs.toList
    (entryScope (enter base source).inputs) ({next := base} : Rename) converted
    initialAvailable inputCovered convertedList
  refine ⟨prefixes, ?_⟩
  have outputVersions : (enter base source).outputs =
      ((source.instrs.toList.mapM renameInstr).run ({next := base} : Rename)).2.versions := by
    simp only [enter, arrayRun]
  intro register member
  rw [outputVersions] at member
  obtain ⟨pair, memberPair, same⟩ := List.mem_map.mp member
  rw [← same]
  exact outputs pair memberPair

open Silmaril.Machine.OfLambdaSSA
open ScopeTyping
open Admission

theorem singleFunction_fits (inputs : List Nat) (instructions : List Old.Op) (outputs : List Nat)
    (admitted : ∀ instruction ∈ instructions, ArithmeticOp instruction)
    (prefixes : PrefixCovers (entryScope inputs) instructions)
    (returned : ((entryScope inputs).afterOps instructions).Covers outputs) :
    RootFits [] (Silmaril.Machine.RTL.SSA.toLambdaSSA [] (singleFunction inputs instructions outputs))
      (.cfg [inputs.length] .br
        [instructions.foldr (fun _ body => .let₁ body) (.cfg [] .br [])])
      inputs.length outputs.length := by
  change inputs.length = inputs.length ∧ _
  refine ⟨rfl, ?_⟩
  unfold Silmaril.Machine.RTL.SSA.blockRegion
  dsimp only [singleFunction, Silmaril.Machine.RTL.SSA.Func.block?, List.getElem?_cons_zero]
  have noChildren : (singleFunction inputs instructions outputs).domChildren (some 0) = [] := by rfl
  dsimp only [singleFunction] at noChildren
  simp only [noChildren, List.length_cons, List.length_nil]
  apply opsRegion_fits (entryScope inputs) instructions admitted
    (prefixCovers_at prefixes) (labels := [inputs.length, outputs.length, 0])
  apply RegionFits.cfg (ws := []) rfl
  · simp only [Silmaril.Machine.RTL.SSA.Scope.afterOps_labels, Silmaril.Machine.RTL.SSA.Scope.push_labels]
    exact ret_fits (singleFunction inputs instructions outputs)
      { (entryScope inputs).afterOps instructions with labels := [(some 0, 1), (none, 1)] }
      (labels := [inputs.length, outputs.length, 0]) returned rfl
  · intro impossible
    exact Fin.elim0 impossible

/-- Accepted actual views have the existing flattening shape and exact annotation.
No evaluation, frame-read, freshness or successful-restore premise is required. -/
theorem view_fits {base : Nat} {source : Silmaril.Compile.Mir.Block} {result : View}
    (accepted : view base source = some result) :
    RootFits [] result.region result.annotation result.inputs.length result.outputs.length := by
  unfold view at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · cases converted : (enter base source).body.instrs.toList.mapM oldOp with
    | none => simp [converted] at accepted
    | some instructions =>
      simp only [converted, bind, pure] at accepted
      obtain rfl := Option.some.inj accepted
      obtain ⟨prefixes, returned⟩ := enter_scoped base source instructions converted
      simpa only [singleFunction, List.length_map] using
        singleFunction_fits (enter base source).inputs instructions ((enter base source).outputs.map Prod.snd)
          (oldOps_admitted converted) prefixes returned

end Silmaril.Compiler.Native.Optimize.LambdaSSA.ViewTyping
