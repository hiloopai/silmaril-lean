module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.CommitFreshness.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RenamingSemantics.Thms
/-! Source-derived returned-register freshness through actual Op.toTm, folding,
Scope projections, flattening and restore. Actual emitted sequential commits
preserve every fresh source and retain partial-read execution requirements. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.CommitFreshness
open Silmaril.Compile Silmaril.Machine
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.RTL (Opcode)
open Silmaril.Machine.RTL.SSA

/-- The actual folded translation of an admitted source primitive still binds
an operator result; known moves become constant operators, not input aliases. -/
theorem folded_toTm_operator (known : List Abstract) (scope : Scope Nat)
    (operation : Old.Op) (admitted : Admission.ArithmeticOp operation) :
    ∃ (opcode : Old.Opcode) (argument : Old.Tm),
      (foldTm known (operation.toTm [] scope)).1 = .op opcode argument ∧
      opcode ≠ .test ∧ opcode.results = 1 := by
  cases operation with
  | const destination value => exact ⟨.const value, .unit, rfl, (by intro same; cases same), rfl⟩
  | move destination operand =>
    simp only [Op.toTm, foldTm]
    cases selected : constantOp .move (foldTm known (scope.pack [operand])).2.1 with
    | none => exact ⟨.move, _, rfl, (by intro same; cases same), rfl⟩
    | some value => exact ⟨.const value, .unit, rfl, (by intro same; cases same), rfl⟩
  | unary operation destination operand =>
    simp only [Op.toTm, foldTm]
    cases selected : constantOp (.unary operation) (foldTm known (scope.pack [operand])).2.1 with
    | none => exact ⟨.unary operation, _, rfl, (by intro same; cases same), rfl⟩
    | some value => exact ⟨.const value, .unit, rfl, (by intro same; cases same), rfl⟩
  | binary operation destination left right =>
    simp only [Op.toTm, foldTm]
    cases selected : constantOp (.binary operation) (foldTm known (scope.pack [left, right])).2.1 with
    | none => exact ⟨.binary operation, _, rfl, (by intro same; cases same), rfl⟩
    | some value => exact ⟨.const value, .unit, rfl, (by intro same; cases same), rfl⟩
  | _ => cases admitted

/-- Actual flattening of an operator allocates every returned register at or
above the entry allocation cursor, after compiling the real argument. -/
theorem tmRegs_operator_fresh {sigs : List Silmaril.Machine.RTL.Signature} (opcode : Opcode sigs)
    (notTest : opcode ≠ .test) (argument : Tm (Opcode sigs))
    (env : List (List Nat)) (before : Emit)
    (registers : List Nat) (operations : List (Op Nat)) (after : Emit)
    (compiled : tmRegs env (.op opcode argument) before = some (registers, operations, after)) :
    registers.length = opcode.results ∧ ∀ register ∈ registers, before.nextReg ≤ register := by
  have sequenced := (tmRegs_op notTest env argument before).symm.trans compiled
  obtain ⟨⟨args, argOps, middle⟩, arguments, generated⟩ := Option.bind_eq_some_iff.mp sequenced
  obtain ⟨emitted, _, same⟩ := Option.map_eq_some_iff.mp generated
  have resultRegisters : freshRegs middle.nextReg opcode.results = registers := congrArg Prod.fst same
  have grew : GrewTm before argOps middle := tmRegs_grew argument env before _ arguments
  rw [← resultRegisters]
  exact ⟨freshRegs_length _ _, fun register member => grew.2.2.1.trans (mem_freshRegs.mp member).1⟩

/-- This is the real source primitive to folded syntax to flattened register
path, with no assumed result freshness or successful source execution. -/
theorem folded_toTm_registers_fresh (known : List Abstract) (scope : Scope Nat)
    (operation : Old.Op) (admitted : Admission.ArithmeticOp operation)
    (env : List (List Nat)) (before : Emit)
    (registers : List Nat) (operations : List (Op Nat)) (after : Emit)
    (compiled : tmRegs env (foldTm known (operation.toTm [] scope)).1 before =
      some (registers, operations, after)) :
    registers.length = 1 ∧ ∀ register ∈ registers, before.nextReg ≤ register := by
  obtain ⟨opcode, argument, folded, notTest, width⟩ := folded_toTm_operator known scope operation admitted
  have compiledOperator : tmRegs env (.op opcode argument) before = some (registers, operations, after) :=
    folded ▸ compiled
  have result := tmRegs_operator_fresh opcode notTest argument env before registers operations after compiledOperator
  exact ⟨result.1.trans width, result.2⟩

theorem foldTm_proj (known : List Abstract) (index : Nat) (term : Old.Tm) :
    (foldTm known (proj index term)).1 = proj index (foldTm known term).1 := by
  induction index generalizing known term with
  | zero => rfl
  | succ index ih => simp only [proj, foldTm, ih]

theorem foldTm_ref (known : List Abstract) (scope : Scope Nat) (register : Nat) :
    (foldTm known (scope.ref register : Old.Tm)).1 = scope.ref register := by
  unfold Scope.ref
  cases found : Scope.findReg scope.vals register 0 with
  | none => rfl
  | some pair => exact foldTm_proj known pair.2 (.var pair.1)

theorem foldTm_pack (known : List Abstract) (scope : Scope Nat) (registers : List Nat) :
    (foldTm known (scope.pack registers : Old.Tm)).1 = scope.pack registers := by
  induction registers with
  | nil => rfl
  | cons register rest ih => simp only [Scope.pack, foldTm, foldTm_ref, ih]

/-- Actual projection-only flattening returns the selected concrete register
without emitting an operation or allocating a name. -/
theorem tmRegs_proj (env : List (List Nat)) (before : Emit) (index offset : Nat)
    (group : List Nat) (register : Nat) (found : env[index]? = some group)
    (selected : group[offset]? = some register) :
    tmRegs env (proj offset (.var index) : Old.Tm) before = some ([register], [], before) := by
  induction offset generalizing env index group with
  | zero =>
    cases group with
    | nil => cases selected
    | cons head tail =>
      have same : head = register := Option.some.inj selected
      simp only [proj, tmRegs, found, Option.map_some, Option.bind_some, List.getElem?_cons_succ,
        List.getElem?_cons_zero, List.nil_append, same]
  | succ offset ih =>
    cases group with
    | nil => cases selected
    | cons head tail =>
      have inTail : tail[offset]? = some register := selected
      have projected := ih (tail :: [head] :: env) 0 tail rfl inTail
      simp only [proj, tmRegs, found, Option.map_some, Option.bind_some, projected, List.nil_append]

theorem freshScope_push {bound : Nat} {needed : List Nat} {groups env : List (List Nat)}
    (fresh : FreshScope bound needed groups env) (sources targets : List Nat)
    (width : sources.length = targets.length)
    (allocated : ∀ target ∈ targets, bound ≤ target) :
    FreshScope bound needed (sources :: groups) (targets :: env) := by
  intro source neededSource base index offset found
  have selected : (match idxIn sources source with
      | some position => some (base, position)
      | none => Scope.findReg groups source (base + 1)) = some (index, offset) := found
  cases chosen : idxIn sources source with
  | some position =>
    have same : (base, position) = (index, offset) := Option.some.inj (by simpa only [chosen] using selected)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    have bounded : position < targets.length := width ▸ idxIn_lt chosen
    exact ⟨targets[position], by simp only [Nat.sub_self, List.getElem?_cons_zero,
      Option.bind_some, List.getElem?_eq_getElem bounded], allocated _ (List.getElem_mem _)⟩
  | none =>
    have previous : Scope.findReg groups source (base + 1) = some (index, offset) := by
      simpa only [chosen] using selected
    have lower : base + 1 ≤ index := (Scope.findReg_spec previous).1
    have difference : index - base = (index - (base + 1)) + 1 := by omega
    obtain ⟨target, atIndex, targetBound⟩ := fresh source neededSource (base + 1) index offset previous
    exact ⟨target, by simpa only [difference, List.getElem?_cons_succ] using atIndex, targetBound⟩

theorem tmRegs_ref_fresh (bound : Nat) (needed : List Nat) (scope : Scope Nat)
    (env : List (List Nat)) (before : Emit) (register : Nat)
    (fresh : FreshScope bound needed scope.vals env) (neededSource : register ∈ needed)
    (available : scope.HasReg register) :
    ∃ target, tmRegs env (scope.ref register : Old.Tm) before = some ([target], [], before) ∧ bound ≤ target := by
  obtain ⟨⟨index, offset⟩, located⟩ := Option.isSome_iff_exists.mp (Scope.findReg_isSome_of_hasReg available)
  obtain ⟨target, found, targetBound⟩ := fresh register neededSource 0 index offset located
  have selected : ∃ group, env[index]? = some group ∧ group[offset]? = some target := by
    simpa only [Nat.sub_zero, Option.bind_eq_some_iff] using found
  obtain ⟨group, atGroup, atRegister⟩ := selected
  refine ⟨target, ?_, targetBound⟩
  simp only [Scope.ref, located]
  exact tmRegs_proj env before index offset group target atGroup atRegister

theorem tmRegs_pack_fresh (bound : Nat) (needed : List Nat) (scope : Scope Nat)
    (env : List (List Nat)) (before : Emit) (registers : List Nat)
    (fresh : FreshScope bound needed scope.vals env) (included : ∀ register ∈ registers, register ∈ needed)
    (available : scope.Covers registers) :
    ∃ targets, tmRegs env (scope.pack registers : Old.Tm) before = some (targets, [], before) ∧
      targets.length = registers.length ∧ ∀ target ∈ targets, bound ≤ target := by
  induction registers with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons register rest ih =>
    obtain ⟨target, selected, targetBound⟩ := tmRegs_ref_fresh bound needed scope env before register fresh
      (included register (List.mem_cons_self)) (available register (List.mem_cons_self))
    obtain ⟨targets, compiled, width, bounded⟩ := ih (fun r member => included r (List.mem_cons_of_mem _ member))
      (fun r member => available r (List.mem_cons_of_mem _ member))
    refine ⟨target :: targets, ?_, congrArg Nat.succ width, ?_⟩
    · simp only [Scope.pack, tmRegs, selected, compiled, Option.bind_some, Option.map_some,
        List.singleton_append, List.nil_append]
    · intro value member
      exact (List.mem_cons.mp member).elim (fun same => same ▸ targetBound) (bounded value)

theorem arithmetic_defs_length (operation : Old.Op) (admitted : Admission.ArithmeticOp operation) :
    operation.defs.length = 1 := by
  cases operation <;> first | rfl | cases admitted

/-- Fresh actual operator bindings compose through the actual folded let-chain
and the final actual packed return projection. The initial FreshScope contains
only structural source/target lookups, not desired execution or return facts. -/
theorem folded_opsRegion_returns_fresh (bound : Nat) (operations : List Old.Op)
    (admitted : ∀ operation ∈ operations, Admission.ArithmeticOp operation)
    (known : List Abstract) (scope : Scope Nat) (env : List (List Nat)) (before : Emit)
    (outputs : List Nat) (fresh : FreshScope bound outputs scope.vals env)
    (cursor : bound ≤ before.nextReg) (available : (scope.afterOps operations).Covers outputs)
    (label : Nat) (labels : List (Target × Nat))
    (returnLabel : labels[label]? = some (.ret, outputs.length))
    (resultOps : List (Op Nat)) (values : List Nat) (after : Emit)
    (compiled : regionOps
      (foldRegion known (opsRegion [] scope operations
        (.br label ((scope.afterOps operations).pack outputs)))).1
      (operations.foldr (fun _ annotation => Ann.let₁ annotation) .br) env labels before =
        some (resultOps, .ret values, after)) :
    ∀ register ∈ values, bound ≤ register := by
  induction operations generalizing known scope env before resultOps after with
  | nil =>
    show ∀ register ∈ values, bound ≤ register
    obtain ⟨targets, packed, width, bounded⟩ := tmRegs_pack_fresh bound outputs scope env before outputs
      fresh (fun _ member => member) available
    have generated : regionOps (.br label (scope.pack outputs : Old.Tm)) .br env labels before =
        some ([], .ret targets, before) := by
      simp only [regionOps, returnLabel, Option.bind_some, packed, width, ↓reduceIte]
    have actual : regionOps (.br label (scope.pack outputs : Old.Tm)) .br env labels before =
        some (resultOps, .ret values, after) := by
      simpa only [opsRegion, Scope.afterOps, List.foldl_nil, List.foldr_nil, foldRegion, foldTm_pack] using compiled
    have same : targets = values := Term.ret.inj
      (congrArg (fun result => result.2.1) (Option.some.inj (generated.symm.trans actual)))
    exact same ▸ bounded
  | cons operation rest ih =>
    show ∀ register ∈ values, bound ≤ register
    let value := foldTm known (operation.toTm [] scope)
    let tail := foldRegion (value.2.1 :: known) (opsRegion [] (scope.push operation.defs) rest
      (.br label (((scope.push operation.defs).afterOps rest).pack outputs)))
    have sequenced : (tmRegs env value.1 before).bind (fun first =>
        (regionOps tail.1 (rest.foldr (fun _ annotation => Ann.let₁ annotation) .br)
          (first.1 :: env) labels first.2.2).map
          (fun result => (first.2.1 ++ result.1, result.2.1, result.2.2))) =
        some (resultOps, .ret values, after) := compiled
    obtain ⟨⟨registers, emitted, middle⟩, firstCompiled, lastCompiled⟩ := Option.bind_eq_some_iff.mp sequenced
    obtain ⟨⟨lastOps, lastTerm, lastState⟩, tailCompiled, same⟩ := Option.map_eq_some_iff.mp lastCompiled
    have term : lastTerm = .ret values := congrArg (fun result => result.2.1) same
    have returned : regionOps tail.1 (rest.foldr (fun _ annotation => Ann.let₁ annotation) .br)
        (registers :: env) labels middle = some (lastOps, .ret values, lastState) := term ▸ tailCompiled
    have sourceAdmitted : Admission.ArithmeticOp operation := admitted operation (List.mem_cons_self)
    have allocated : registers.length = 1 ∧ ∀ register ∈ registers, before.nextReg ≤ register :=
      folded_toTm_registers_fresh known scope operation sourceAdmitted
      env before registers emitted middle firstCompiled
    have width : operation.defs.length = registers.length :=
      (arithmetic_defs_length operation sourceAdmitted).trans allocated.1.symm
    have nextFresh : FreshScope bound outputs (scope.push operation.defs).vals (registers :: env) :=
      freshScope_push fresh operation.defs registers width
        (fun register member => cursor.trans (allocated.2 register member))
    have nextCursor : bound ≤ middle.nextReg :=
      cursor.trans (tmRegs_grew value.1 env before _ firstCompiled).2.2.1
    exact ih (fun other member => admitted other (List.mem_cons_of_mem _ member))
      (value.2.1 :: known) (scope.push operation.defs) (registers :: env) middle nextFresh nextCursor
      available lastOps lastState returned

theorem freshScope_of_disjoint (bound : Nat) (needed inputs : List Nat) (env : List (List Nat))
    (disjoint : ∀ register ∈ needed, register ∉ inputs) : FreshScope bound needed [inputs] env := by
  intro register neededSource base index offset found
  obtain ⟨_, group, atGroup, _, atRegister⟩ := Scope.findReg_spec found
  have same : group = inputs := List.mem_singleton.mp (List.mem_of_getElem? atGroup)
  exact False.elim (disjoint register neededSource (same ▸ List.mem_of_getElem? atRegister))

theorem regionOps_cfg_zero (entry : Old.Region) (blocks : Fin 0 → Old.Region)
    (annotation : Ann) (env : List (List Nat)) (labels : List (Target × Nat)) (before : Emit) :
    regionOps (.cfg entry 0 blocks) (.cfg [] annotation []) env labels before =
      regionOps entry annotation env labels before := by
  simp only [regionOps, List.length_nil, ↓reduceIte, List.finRange_zero, List.map_nil,
    List.nil_append, Nat.add_zero, List.foldl_nil]
  cases regionOps entry annotation env labels before <;> rfl

theorem folded_ops_cfg_zero (known : List Abstract) (scope : Scope Nat) (operations : List Old.Op)
    (entry : Old.Region) (blocks : Fin 0 → Old.Region) (annotation : Ann)
    (env : List (List Nat)) (labels : List (Target × Nat)) (before : Emit) :
    regionOps (foldRegion known (opsRegion [] scope operations (.cfg entry 0 blocks))).1
      (operations.foldr (fun _ body => Ann.let₁ body) (.cfg [] annotation [])) env labels before =
    regionOps (foldRegion known (opsRegion [] scope operations entry)).1
      (operations.foldr (fun _ body => Ann.let₁ body) annotation) env labels before := by
  induction operations generalizing known scope env before with
  | nil => exact regionOps_cfg_zero (foldRegion known entry).1 _ annotation env labels before
  | cons operation rest ih =>
    simp only [opsRegion, List.foldr_cons, foldRegion, regionOps, ih]

theorem renameList_valid (instructions : List Mir.Instr) (base : Nat) (state : Rename)
    (valid : state.Valid base) (bounds : ∀ instruction ∈ instructions, ∀ register ∈ defs instruction, register < base) :
    ((instructions.mapM renameInstr).run state).2.Valid base := by
  induction instructions generalizing state with
  | nil => exact valid
  | cons instruction rest ih =>
    rw [renameInstrs_cons]
    exact ih ((renameInstr instruction).run state).2
      (valid_renameInstr valid instruction (bounds instruction (List.mem_cons_self)))
      (fun other member => bounds other (List.mem_cons_of_mem _ member))

theorem freshBase_def {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) {instruction : Mir.Instr}
    (inBlock : instruction ∈ block.instrs.toList) {register : Nat} (defined : register ∈ defs instruction) :
    register < freshBase function := by
  have included : register ∈ function.params ++ function.blocks.toList.flatMap (fun block =>
      Mir.DeadCode.termUses block.term ++ block.instrs.toList.flatMap (fun instruction => uses instruction ++ defs instruction)) := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨block, member, List.mem_append_right _ ?_⟩
    exact List.mem_flatMap.mpr ⟨instruction, inBlock, List.mem_append_right _ defined⟩
  exact Nat.lt_succ_of_le (RestoreAdmission.member_le_foldl_max included 0)

/-- Actual freshBase and actual syntactic allocation give the two sides of the
mutable boundary range, without any source execution assumption. -/
theorem enter_outputs_bounds {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) :
    ∀ pair ∈ (enter (freshBase function) block).outputs,
      pair.1 < freshBase function ∧ freshBase function ≤ pair.2 := by
  have valid : ((block.instrs.toList.mapM renameInstr).run
      ({next := freshBase function} : Rename)).2.Valid (freshBase function) :=
    renameList_valid block.instrs.toList (freshBase function) _ (valid_initial _)
      (fun instruction inBlock register defined => freshBase_def member inBlock defined)
  have arrayRun := renameArray_run block.instrs ({next := freshBase function} : Rename)
  intro pair included
  have listed : pair ∈ ((block.instrs.toList.mapM renameInstr).run
      ({next := freshBase function} : Rename)).2.versions := by
    simpa only [enter, arrayRun] using included
  exact ⟨(valid.2 pair listed).1, (valid.2 pair listed).2.1⟩

theorem enter_output_scope_fresh {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) (bound : Nat) (env : List (List Nat)) :
    FreshScope bound ((enter (freshBase function) block).outputs.map Prod.snd)
      (ViewTyping.entryScope (enter (freshBase function) block).inputs).vals env := by
  apply freshScope_of_disjoint
  intro register output input
  obtain ⟨pair, included, same⟩ := List.mem_map.mp output
  have lower : freshBase function ≤ register := same ▸ (enter_outputs_bounds member pair included).2
  have upper : register < freshBase function := RestoreAdmission.freshBase_input member input
  omega

theorem pack_of_vals {first second : Scope Nat} (same : first.vals = second.vals) (registers : List Nat) :
    (first.pack registers : Old.Tm) = second.pack registers := by
  induction registers with
  | nil => rfl
  | cons register rest ih => simp only [Scope.pack, Scope.ref, same, ih]

/-- The exact singleton source translation is one wrapper and one straight-line
let-chain ending in the actual zero-child CFG return pack. -/
theorem singleFunction_region (inputs : List Nat) (operations : List Old.Op) (outputs : List Nat) :
    toLambdaSSA [] (ViewTyping.singleFunction inputs operations outputs) =
      .cfg (.br 0 (.var 0)) 1 (fun _ =>
        opsRegion [] (ViewTyping.entryScope inputs) operations
          (.cfg (.br 1 (((ViewTyping.entryScope inputs).afterOps operations).pack outputs))
            0 (fun _ => .br 0 .unit))) := by
  unfold toLambdaSSA
  congr 1
  funext index
  unfold blockRegion
  dsimp only [ViewTyping.singleFunction, Func.block?, List.getElem?_cons_zero]
  have noChildren : (ViewTyping.singleFunction inputs operations outputs).domChildren (some 0) = [] := rfl
  dsimp only [ViewTyping.singleFunction] at noChildren
  simp only [noChildren, List.length_cons, List.length_nil]
  simp only [Term.toRegion, Scope.depth, Scope.afterOps_labels, Scope.push_labels]
  change opsRegion [] (ViewTyping.entryScope inputs) operations
      (.cfg (.br 1 (({((ViewTyping.entryScope inputs).afterOps operations) with
        labels := [(some 0, 1), (none, 1)]} : Scope Nat).pack outputs)) 0 (fun _ => .br 0 .unit)) = _
  apply congrArg (fun term : Old.Tm => opsRegion [] (ViewTyping.entryScope inputs) operations
    (.cfg (.br 1 term) 0 (fun _ => .br 0 .unit)))
  exact pack_of_vals (first := {((ViewTyping.entryScope inputs).afterOps operations) with
    labels := [(some 0, 1), (none, 1)]}) (second := (ViewTyping.entryScope inputs).afterOps operations) rfl outputs

theorem folded_singleFunction_rootOps (known : List Abstract) (inputs : List Nat)
    (operations : List Old.Op) (outputs : List Nat) :
    rootOps [] (foldRegion known (toLambdaSSA [] (ViewTyping.singleFunction inputs operations outputs))).1
      (.cfg [inputs.length] .br [operations.foldr (fun _ body => Ann.let₁ body) (.cfg [] .br [])])
      inputs.length outputs.length =
    regionOps (foldRegion (.unknown :: known) (opsRegion [] (ViewTyping.entryScope inputs) operations
      (.br 1 (((ViewTyping.entryScope inputs).afterOps operations).pack outputs)))).1
      (operations.foldr (fun _ body => Ann.let₁ body) .br)
      [freshRegs 0 inputs.length] [(.block 0, inputs.length), (.ret, outputs.length), (.trap, 0)]
      {nextReg := inputs.length, nextLabel := 1, blocks := []} := by
  rw [singleFunction_region]
  simp only [foldRegion, foldTm, rootOps, ↓reduceIte]
  exact folded_ops_cfg_zero (.unknown :: known) (ViewTyping.entryScope inputs) operations
    (.br 1 (((ViewTyping.entryScope inputs).afterOps operations).pack outputs)) _ .br _ _ _

theorem entered_root_returns_fresh {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) (operations : List Old.Op)
    (accepted : (enter (freshBase function) block).body.instrs.toList.mapM oldOp = some operations)
    (known : List Abstract) (resultOps : List (Op Nat)) (values : List Nat) (after : Emit)
    (compiled : rootOps []
      (foldRegion known (toLambdaSSA [] (ViewTyping.singleFunction
        (enter (freshBase function) block).inputs operations
        ((enter (freshBase function) block).outputs.map Prod.snd)))).1
      (.cfg [(enter (freshBase function) block).inputs.length] .br
        [operations.foldr (fun _ body => Ann.let₁ body) (.cfg [] .br [])])
      (enter (freshBase function) block).inputs.length (enter (freshBase function) block).outputs.length =
        some (resultOps, .ret values, after)) :
    ∀ register ∈ values, (enter (freshBase function) block).inputs.length ≤ register := by
  have coverage := ViewTyping.enter_scoped (freshBase function) block operations accepted
  have actual : regionOps (foldRegion (.unknown :: known)
      (opsRegion [] (ViewTyping.entryScope (enter (freshBase function) block).inputs) operations
        (.br 1 (((ViewTyping.entryScope (enter (freshBase function) block).inputs).afterOps operations).pack
          ((enter (freshBase function) block).outputs.map Prod.snd))))).1
      (operations.foldr (fun _ body => Ann.let₁ body) .br)
      [freshRegs 0 (enter (freshBase function) block).inputs.length]
      [(.block 0, (enter (freshBase function) block).inputs.length),
        (.ret, (enter (freshBase function) block).outputs.length), (.trap, 0)]
      {nextReg := (enter (freshBase function) block).inputs.length, nextLabel := 1, blocks := []} =
        some (resultOps, .ret values, after) := by
    have normalized : rootOps []
        (foldRegion known (toLambdaSSA [] (ViewTyping.singleFunction
          (enter (freshBase function) block).inputs operations
          ((enter (freshBase function) block).outputs.map Prod.snd)))).1
        (.cfg [(enter (freshBase function) block).inputs.length] .br
          [operations.foldr (fun _ body => Ann.let₁ body) (.cfg [] .br [])])
        (enter (freshBase function) block).inputs.length
        ((enter (freshBase function) block).outputs.map Prod.snd).length =
          some (resultOps, .ret values, after) := by simpa only [List.length_map] using compiled
    rw [folded_singleFunction_rootOps] at normalized
    simpa only [List.length_map] using normalized
  exact folded_opsRegion_returns_fresh _ operations (Admission.oldOps_admitted accepted)
    (.unknown :: known) (ViewTyping.entryScope (enter (freshBase function) block).inputs)
    [freshRegs 0 (enter (freshBase function) block).inputs.length] _
    ((enter (freshBase function) block).outputs.map Prod.snd) (enter_output_scope_fresh member _ _) (Nat.le_refl _)
    coverage.2 1 _ (by simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_map])
    resultOps values after actual

theorem view_shape {base : Nat} {block : Mir.Block} {result : View}
    (accepted : view base block = some result) :
    ∃ converted, (enter base block).body.instrs.toList.mapM oldOp = some converted ∧
      result.inputs = (enter base block).inputs ∧
      result.outputs = (enter base block).outputs.map Prod.fst ∧
      result.region = toLambdaSSA [] (ViewTyping.singleFunction (enter base block).inputs converted
        ((enter base block).outputs.map Prod.snd)) ∧
      result.annotation = .cfg [(enter base block).inputs.length] .br
        [converted.foldr (fun _ body => Ann.let₁ body) (.cfg [] .br [])] := by
  unfold view at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · cases converted : (enter base block).body.instrs.toList.mapM oldOp with
    | none => simp [converted] at accepted
    | some instructions =>
      simp only [converted, bind, pure] at accepted
      obtain rfl := Option.some.inj accepted
      exact ⟨instructions, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual successful optional flattening of a real folded view, together with
its actual singleton/return checks, derives fresh returned indices. -/
theorem folded_view_returns_fresh {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (accepted : view (freshBase function) block = some result) (known : List Abstract)
    {flattened : Old.Func} {body : Silmaril.Machine.RTL.SSA.Block Nat} {values : List Nat}
    (compiled : ofLambdaSSA? [] (foldRegion known result.region).1 result.annotation
      result.inputs.length result.outputs.length = some flattened)
    (singleton : flattened.blocks = [body]) (returned : body.term = .ret values) :
    ∀ register ∈ values, result.inputs.length ≤ register := by
  obtain ⟨operations, converted, inputs, outputs, region, annotation⟩ := view_shape accepted
  have sourceCompiled : ofLambdaSSA? []
      (foldRegion known (toLambdaSSA [] (ViewTyping.singleFunction
        (enter (freshBase function) block).inputs operations
        ((enter (freshBase function) block).outputs.map Prod.snd)))).1
      (.cfg [(enter (freshBase function) block).inputs.length] .br
        [operations.foldr (fun _ body => Ann.let₁ body) (.cfg [] .br [])])
      (enter (freshBase function) block).inputs.length (enter (freshBase function) block).outputs.length =
        some flattened := by simpa only [inputs, outputs, region, annotation, List.length_map] using compiled
  obtain ⟨⟨rootInstructions, rootTerm, emitted⟩, rootCompiled, sameFunction⟩ :=
    Option.map_eq_some_iff.mp sourceCompiled
  have blocks : assemble emitted.nextLabel
      ((0, ⟨freshRegs 0 (enter (freshBase function) block).inputs.length, rootInstructions, rootTerm⟩) :: emitted.blocks) =
      [body] := (congrArg Func.blocks sameFunction).trans singleton
  have count : emitted.nextLabel = 1 := by
    have lengths := congrArg List.length blocks
    simpa only [assemble, List.length_map, List.length_range, List.length_cons, List.length_nil] using lengths
  have sameBody : (⟨freshRegs 0 (enter (freshBase function) block).inputs.length,
      rootInstructions, rootTerm⟩ : Silmaril.Machine.RTL.SSA.Block Nat) = body := by
    simpa [assemble, count, List.lookup] using blocks
  have term : rootTerm = .ret values := (congrArg Silmaril.Machine.RTL.SSA.Block.term sameBody).trans returned
  have finalCompiled : rootOps []
      (foldRegion known (toLambdaSSA [] (ViewTyping.singleFunction
        (enter (freshBase function) block).inputs operations
        ((enter (freshBase function) block).outputs.map Prod.snd)))).1
      (.cfg [(enter (freshBase function) block).inputs.length] .br
        [operations.foldr (fun _ body => Ann.let₁ body) (.cfg [] .br [])])
      (enter (freshBase function) block).inputs.length (enter (freshBase function) block).outputs.length =
        some (rootInstructions, .ret values, emitted) := term ▸ rootCompiled
  have fresh := entered_root_returns_fresh member operations converted known rootInstructions values emitted finalCompiled
  simpa only [inputs] using fresh

/-- The real view's original mutable output names are below the genuine
per-function fresh range, independently of source execution. -/
theorem view_outputs_below_freshBase {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (accepted : view (freshBase function) block = some result) :
    ∀ output ∈ result.outputs, output < freshBase function := by
  obtain ⟨_, _, _, outputs, _⟩ := view_shape accepted
  intro output included
  obtain ⟨pair, listed, same⟩ := List.mem_map.mp (outputs ▸ included)
  exact same ▸ (enter_outputs_bounds member pair listed).1

/-- The actual emitted commit pairs are separated by the genuine freshBase.
The result-source bounds come from real folded-view flattening, not map
injectivity or an assumed nonclobbering condition. -/
theorem restored_commit_bounds {function : Mir.Func} {block candidate : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (accepted : view (freshBase function) block = some result)
    (restored : restore (freshBase function) block result (foldRegion [.unknown] result.region).1 = some candidate) :
    ∃ flattened body values instructions,
      ofLambdaSSA? [] (foldRegion [.unknown] result.region).1 result.annotation
        result.inputs.length result.outputs.length = some flattened ∧
      flattened.entry = 0 ∧ flattened.blocks = [body] ∧
      body.params = List.range result.inputs.length ∧ body.term = .ret values ∧
      values.length = result.outputs.length ∧
      body.ops.mapM (newOp (RestoreAdmission.register (freshBase function) result.inputs)) = some instructions ∧
      candidate = ⟨(instructions ++ (result.outputs.zip values).map (fun (original, value) =>
        Mir.Instr.op (.move original (RestoreAdmission.register (freshBase function) result.inputs value)))).toArray,
        block.term⟩ ∧
      (∀ value ∈ values, result.inputs.length ≤ value) ∧
      ∀ pair ∈ (result.outputs.zip values).map (fun (original, value) =>
        (original, RestoreAdmission.register (freshBase function) result.inputs value)),
        pair.1 < freshBase function ∧ freshBase function ≤ pair.2 := by
  obtain ⟨flattened, body, values, instructions, compiled, entry, singleton, parameters,
    returned, width, converted, emitted⟩ := RestoreAdmission.restore_witness restored
  have fresh := folded_view_returns_fresh member accepted [.unknown] compiled singleton returned
  refine ⟨flattened, body, values, instructions, compiled, entry, singleton, parameters,
    returned, width, converted, emitted, fresh, ?_⟩
  intro pair included
  obtain ⟨⟨original, value⟩, zipped, same⟩ := List.mem_map.mp included
  obtain ⟨atOutput, atValue⟩ := List.of_mem_zip zipped
  have sourceFresh : freshBase function ≤ RestoreAdmission.register (freshBase function) result.inputs value := by
    rw [RestoreAdmission.register_fresh (fresh value atValue)]
    exact Nat.le_add_right _ _
  exact same ▸ ⟨view_outputs_below_freshBase member accepted original atOutput, sourceFresh⟩

theorem commitInstrs_exists_iff (base : Nat) (versions : List (Nat × Nat))
    (bounds : ∀ pair ∈ versions, pair.1 < base ∧ base ≤ pair.2)
    (calls : OpenCalls) (source : Lir.Frame Nat) (memory : Lir.Memory) :
    (∃ final, InstructionsExec calls (commitInstrs versions) source memory final memory) ↔
      ∀ pair ∈ versions, ∃ word, source.get pair.2 = some word := by
  induction versions generalizing source with
  | nil =>
    constructor
    · intro _ pair member
      cases member
    · intro _
      exact ⟨source, .nil⟩
  | cons pair rest ih =>
    show (∃ final, InstructionsExec calls (commitInstrs (pair :: rest)) source memory final memory) ↔
      ∀ other ∈ pair :: rest, ∃ word, source.get other.2 = some word
    have tailBounds : ∀ other ∈ rest, other.1 < base ∧ base ≤ other.2 :=
      fun other member => bounds other (List.mem_cons_of_mem _ member)
    constructor
    · show (∃ final, InstructionsExec calls (commitInstrs (pair :: rest)) source memory final memory) →
        ∀ other ∈ pair :: rest, ∃ word, source.get other.2 = some word
      rintro ⟨final, native⟩
      cases native with
      | cons first tail =>
        show ∀ other ∈ pair :: rest, ∃ word, source.get other.2 = some word
        cases first with
        | op primitive =>
          show ∀ other ∈ pair :: rest, ∃ word, source.get other.2 = some word
          obtain ⟨word, read, sameFrame, sameMemory⟩ : ∃ word, source.get pair.2 = some word ∧
              source.set pair.1 word = _ ∧ memory = _ := by
            simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using primitive
          have tailRun : ∃ final, InstructionsExec calls (commitInstrs rest)
              (source.set pair.1 word) memory final memory := ⟨final, sameFrame.symm ▸ (sameMemory.symm ▸ tail)⟩
          have tailReads : ∀ other ∈ rest, ∃ value, (source.set pair.1 word).get other.2 = some value := (ih tailBounds (source.set pair.1 word)).mp tailRun
          intro other member
          obtain rfl | listed := List.mem_cons.mp member
          · exact ⟨word, read⟩
          · obtain ⟨value, selected⟩ := tailReads other listed
            have different : other.2 ≠ pair.1 := by
              have firstBound : pair.1 < base := (bounds pair (List.mem_cons_self)).1
              have nextBound : base ≤ other.2 := (tailBounds other listed).2
              omega
            exact ⟨value, by simpa only [Lir.Frame.get_set, different, ↓reduceIte] using selected⟩
    · show (∀ other ∈ pair :: rest, ∃ word, source.get other.2 = some word) →
        ∃ final, InstructionsExec calls (commitInstrs (pair :: rest)) source memory final memory
      intro reads
      obtain ⟨word, read⟩ := reads pair (List.mem_cons_self)
      have tailReads : ∀ other ∈ rest, ∃ value, (source.set pair.1 word).get other.2 = some value := by
        intro other member
        obtain ⟨value, selected⟩ := reads other (List.mem_cons_of_mem _ member)
        have different : other.2 ≠ pair.1 := by
          have firstBound : pair.1 < base := (bounds pair (List.mem_cons_self)).1
          have nextBound : base ≤ other.2 := (tailBounds other member).2
          omega
        exact ⟨value, by simpa only [Lir.Frame.get_set, different, ↓reduceIte] using selected⟩
      obtain ⟨final, native⟩ := (ih tailBounds (source.set pair.1 word)).mpr tailReads
      exact ⟨final, .cons (.op (by simp only [Lir.Op.exec, read, Option.map_some])) native⟩

theorem commitInstrs_preserves_fresh (base : Nat) (versions : List (Nat × Nat))
    (bounds : ∀ pair ∈ versions, pair.1 < base) (calls : OpenCalls)
    (source final : Lir.Frame Nat) (memory after : Lir.Memory)
    (executed : InstructionsExec calls (commitInstrs versions) source memory final after) :
    after = memory ∧ final.slots = source.slots ∧ ∀ register, base ≤ register → final.get register = source.get register := by
  induction versions generalizing source memory with
  | nil => cases executed; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons pair rest ih =>
    show after = memory ∧ final.slots = source.slots ∧
      ∀ register, base ≤ register → final.get register = source.get register
    cases executed with
    | cons first tail =>
      show after = memory ∧ final.slots = source.slots ∧
        ∀ register, base ≤ register → final.get register = source.get register
      cases first with
      | op primitive =>
        show after = memory ∧ final.slots = source.slots ∧
          ∀ register, base ≤ register → final.get register = source.get register
        obtain ⟨word, read, sameFrame, sameMemory⟩ : ∃ word, source.get pair.2 = some word ∧
            source.set pair.1 word = _ ∧ memory = _ := by
          simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using primitive
        have restRun : InstructionsExec calls (commitInstrs rest) (source.set pair.1 word) memory final after :=
          sameFrame.symm ▸ (sameMemory.symm ▸ tail)
        obtain ⟨memorySame, slotsSame, registers⟩ := ih (fun other member => bounds other (List.mem_cons_of_mem _ member))
          (source.set pair.1 word) memory restRun
        refine ⟨memorySame, slotsSame, ?_⟩
        intro register high
        have different : register ≠ pair.1 := by
          have lower : pair.1 < base := bounds pair (List.mem_cons_self)
          omega
        exact (registers register high).trans (by simp only [Lir.Frame.get_set, different, ↓reduceIte])

/-- Actual restore's concrete commits execute exactly when their original
fresh-source reads are defined, and every successful sequential execution
preserves all of those sources, all slots and memory. -/
theorem restore_commits_safe {function : Mir.Func} {block candidate : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (accepted : view (freshBase function) block = some result)
    (restored : restore (freshBase function) block result (foldRegion [.unknown] result.region).1 = some candidate) :
    ∃ instructions versions,
      candidate = ⟨(instructions ++ commitInstrs versions).toArray, block.term⟩ ∧
      (∀ pair ∈ versions, pair.1 < freshBase function ∧ freshBase function ≤ pair.2) ∧
      (∀ (calls : OpenCalls) (source : Lir.Frame Nat) (memory : Lir.Memory),
        (∃ final, InstructionsExec calls (commitInstrs versions) source memory final memory) ↔
          ∀ pair ∈ versions, ∃ word, source.get pair.2 = some word) ∧
      ∀ (calls : OpenCalls) (source final : Lir.Frame Nat) (memory after : Lir.Memory),
        InstructionsExec calls (commitInstrs versions) source memory final after →
          after = memory ∧ final.slots = source.slots ∧
          ∀ register, freshBase function ≤ register → final.get register = source.get register := by
  obtain ⟨flattened, body, values, instructions, compiled, entry, singleton, parameters,
    returned, width, converted, emitted, fresh, bounds⟩ := restored_commit_bounds member accepted restored
  let versions := (result.outputs.zip values).map (fun (original, value) =>
    (original, RestoreAdmission.register (freshBase function) result.inputs value))
  have candidateShape : candidate = ⟨(instructions ++ commitInstrs versions).toArray, block.term⟩ := by
    simpa only [versions, commitInstrs, List.map_map, Function.comp_def] using emitted
  refine ⟨instructions, versions, candidateShape, bounds, ?_, ?_⟩
  · intro calls source memory
    exact commitInstrs_exists_iff (freshBase function) versions bounds calls source memory
  · intro calls source final memory after executed
    exact commitInstrs_preserves_fresh (freshBase function) versions
      (fun pair member => (bounds pair member).1) calls source final memory after executed

end Silmaril.Compiler.Native.Optimize.LambdaSSA.CommitFreshness
