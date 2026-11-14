module

public import Silmaril.Compiler.Native.Optimize.Validation.Candidate.Defs
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Candidate
open Silmaril.Machine
open Roots Total


theorem Prefix.refl (nodes : Array Expr) : Prefix nodes nodes := ⟨Nat.le_refl _, fun _ _ => rfl⟩
theorem Prefix.trans {first middle last : Array Expr} (a : Prefix first middle) (b : Prefix middle last) :
    Prefix first last :=
  ⟨a.grows.trans b.grows, fun index bound => (b.old index (Nat.lt_of_lt_of_le bound a.grows)).trans (a.old index bound)⟩


theorem growing_pure {α : Type} (value : α) : Growing (pure value) := fun state => .refl state.nodes

theorem growing_bind {α β : Type} (action : StateM State α) (next : α → StateM State β)
    (first : Growing action) (later : ∀ value, Growing (next value)) : Growing (action >>= next) := by
  intro state
  exact (first state).trans (later (action.run state).1 (action.run state).2)

theorem growing_intern (expression : Expr) : Growing (intern expression) := by
  intro state
  obtain ⟨suffix, equal, bound⟩ := Intern.nodes_prefix state expression
  refine ⟨?_, ?_⟩
  · rw [equal]; simp
  · intro index bounded
    rw [equal]
    exact Array.getElem?_append_left bounded

theorem readReg_run (state : State) (reg : Nat) :
    (readReg reg).run state = match state.regs.find? (·.1 == reg) with
      | some (_, index) => (index, state)
      | none => (intern (.input reg)).run state := by
  cases found : state.regs.find? (·.1 == reg) with
  | none =>
    simp [readReg, StateT.run, StateT.bind, StateT.get,
      MonadState.get, getThe, MonadStateOf.get, Bind.bind, Pure.pure, found]
  | some root =>
    cases root
    simp [readReg, StateT.run, StateT.bind, StateT.get, StateT.pure,
      MonadState.get, getThe, MonadStateOf.get, Bind.bind, Pure.pure, found]

theorem growing_readReg (reg : Nat) : Growing (readReg reg) := by
  intro state
  rw [readReg_run]
  cases found : state.regs.find? (·.1 == reg) with
  | none => exact growing_intern (.input reg) state
  | some root => exact .refl _

theorem readSlot_run (state : State) (slot : Nat) :
    (readSlot slot).run state = match state.slots.find? (·.1 == slot) with
      | some (_, index) => (index, state)
      | none => (intern (.slot slot)).run state := by
  cases found : state.slots.find? (·.1 == slot) with
  | none =>
    simp [readSlot, StateT.run, StateT.bind, StateT.get,
      MonadState.get, getThe, MonadStateOf.get, Bind.bind, Pure.pure, found]
  | some root =>
    cases root
    simp [readSlot, StateT.run, StateT.bind, StateT.get, StateT.pure,
      MonadState.get, getThe, MonadStateOf.get, Bind.bind, Pure.pure, found]

theorem growing_readSlot (slot : Nat) : Growing (readSlot slot) := by
  intro state
  rw [readSlot_run]
  cases found : state.slots.find? (·.1 == slot) with
  | none => exact growing_intern (.slot slot) state
  | some root => exact .refl _

theorem growing_writeReg (reg index : Nat) : Growing (writeReg reg index) := fun state => .refl state.nodes

theorem growing_evalOp (op : Lir.Op Nat) (admitted : Roots.Admitted op) : Growing (evalOp op) := by
  cases op with
  | const dest word =>
    exact growing_bind _ _ (growing_intern (.const word)) (fun index => growing_writeReg dest index)
  | move dest source =>
    exact growing_bind _ _ (growing_readReg source) (fun index => growing_writeReg dest index)
  | unary op dest source =>
    exact growing_bind _ _ (growing_readReg source) (fun index =>
      growing_bind _ _ (growing_intern (.unary op index)) (fun output => growing_writeReg dest output))
  | binary op dest left right =>
    change Silmaril.Compile.Mir.DeadCode.faults op = false at admitted
    simp only [evalOp, admitted, Bool.false_eq_true, ↓reduceIte]
    exact growing_bind _ _ (growing_readReg left) (fun a =>
      growing_bind _ _ (growing_readReg right) (fun b =>
        growing_bind _ _ (growing_intern (.binary op a b)) (fun output => growing_writeReg dest output)))
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot => cases admitted
  | slotSet slot source => cases admitted

theorem growing_evalInstr (instruction : Silmaril.Compile.Mir.Instr)
    (admitted : Lists.AdmittedInstr instruction) : Growing (evalInstr instruction) := by
  cases instruction with
  | op op => exact growing_evalOp op admitted
  | fop op dest left right => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem growing_forM (instructions : List Silmaril.Compile.Mir.Instr)
    (admitted : Lists.Admitted instructions) : Growing (instructions.forM evalInstr) := by
  induction instructions with
  | nil => exact growing_pure ()
  | cons instruction rest ih =>
    intro state
    rw [Lists.forM_cons_run]
    exact (growing_evalInstr instruction (admitted instruction (by simp)) state).trans
      (ih (fun i h => admitted i (by simp [h])) ((evalInstr instruction).run state).2)

theorem growing_mapM {α β : Type} (action : α → StateM State β) (items : List α)
    (growing : ∀ item, Growing (action item)) : Growing (items.mapM action) := by
  induction items with
  | nil => exact growing_pure []
  | cons item rest ih =>
    simp only [List.mapM_cons]
    exact growing_bind _ _ (growing item) (fun value =>
      growing_bind _ _ ih (fun values => growing_pure (value :: values)))

theorem growing_evalLoc (loc : Lir.Loc Nat) : Growing (evalLoc loc) := by
  cases loc with
  | reg reg => exact growing_readReg reg
  | slot slot => exact growing_readSlot slot

theorem growing_evalTerm (term : Lir.Term Nat) : Growing (evalTerm term) := by
  cases term with
  | jump label => exact growing_pure (Term.jump label)
  | branch reg yes no => exact growing_bind _ _ (growing_readReg reg) (fun index => growing_pure (Term.branch index yes no))
  | ret locs => exact growing_bind _ _ (growing_mapM evalLoc locs growing_evalLoc) (fun values => growing_pure (Term.ret values))
  | trap => exact growing_pure Term.trap

theorem growing_evalBlock (block : Silmaril.Compile.Mir.Block) (observed : List Nat)
    (admitted : Lists.Admitted block.instrs.toList) : Growing (evalBlock block observed) := by
  intro state
  rw [Lists.evalBlock_run]
  exact (growing_forM block.instrs.toList admitted state).trans
    ((growing_evalTerm block.term _).trans (growing_mapM readReg observed growing_readReg _))


theorem guarded_of_any (nodes : Array Expr) (sourceSize : Nat)
    (guarded : nodes.any Expr.isPartialLeaf sourceSize = false) : Guarded sourceSize nodes := by
  intro index expression found partialLeaf
  have bounded : index < nodes.size := (Array.getElem?_eq_some_iff.mp found).1
  have selected : nodes[index] = expression := (Array.getElem?_eq_some_iff.mp found).2
  by_contra outside
  have atOrAfter : sourceSize ≤ index := by omega
  have detected : nodes.any Expr.isPartialLeaf sourceSize = true :=
    Array.any_iff_exists.mpr ⟨index, bounded, atOrAfter, bounded, by simpa only [selected] using partialLeaf⟩
  rw [guarded] at detected
  cases detected

theorem Guarded.prefix {before after : Array Expr} {bound : Nat}
    (guarded : Guarded bound after) (contained : Prefix before after) : Guarded bound before := by
  intro index expression found partialLeaf
  have bounded : index < before.size := (Array.getElem?_eq_some_iff.mp found).1
  exact guarded index expression ((contained.old index bounded).trans found) partialLeaf

/-- A guarded symbolic register read cannot introduce a missing external input. -/
theorem readReg_defined (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size) (reg : Nat)
    (guarded : Guarded sourceSize ((readReg reg).run state).2.nodes) :
    ∃ word, frame.get reg = some word := by
  cases found : state.regs.find? (·.1 == reg) with
  | some root =>
    obtain ⟨word, defined⟩ := total root.2 (rooted.regsBounded root (List.mem_of_find?_eq_some found))
    have selected : meaning.value root.2 = frame.get reg := by simpa [Roots.regValue, found] using rooted.regs reg
    exact ⟨word, selected.symm.trans defined⟩
  | none =>
    have readRun : (readReg reg).run state = (intern (.input reg)).run state := by rw [readReg_run, found]
    have atIndex : ((intern (.input reg)).run state).2.nodes[((intern (.input reg)).run state).1]? = some (.input reg) :=
      (Intern.returned_index state (.input reg)).2
    have sourceBound : ((intern (.input reg)).run state).1 < sourceSize := by
      rw [readRun] at guarded
      exact guarded _ _ atIndex rfl
    have beforeBound : ((intern (.input reg)).run state).1 < state.nodes.size := Nat.lt_of_lt_of_le sourceBound old
    have oldNode : state.nodes[((intern (.input reg)).run state).1]? = some (.input reg) :=
      (Intern.old_node state (.input reg) beforeBound).symm.trans atIndex
    obtain ⟨word, defined⟩ := total _ beforeBound
    have external : meaning.input reg = some word := (rooted.coherent _ _ oldNode).symm.trans defined
    have selected : meaning.input reg = frame.get reg := by simpa [Roots.regValue, found] using rooted.regs reg
    exact ⟨word, selected.symm.trans external⟩


/-- Total arithmetic for precisely the nonfaulting integer fragment. -/
theorem nonfaulting_binary_total (operation : Lir.Binop)
    (nonfaulting : Silmaril.Compile.Mir.DeadCode.faults operation = false)
    (left right : Lir.Word) : ∃ word, operation.eval left right = some word := by
  cases operation <;> simp_all [Silmaril.Compile.Mir.DeadCode.faults, Lir.Binop.eval]

/-- Concrete primitive success is derived from the final symbolic suffix guard;
it is not an input to this theorem. -/
theorem evalOp_exists (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (sourceSize : Nat)
    (old : sourceSize ≤ state.nodes.size) (op : Lir.Op Nat) (admitted : Roots.Admitted op)
    (guarded : Guarded sourceSize ((evalOp op).run state).2.nodes) :
    ∃ frame', op.exec frame memory = some (frame', memory) := by
  cases op with
  | const dest word => exact ⟨frame.set dest word, rfl⟩
  | move dest source =>
    obtain ⟨word, read⟩ := readReg_defined state frame meaning rooted total sourceSize old source guarded
    exact ⟨frame.set dest word, by simp only [Lir.Op.exec, read, Option.map_some]⟩
  | unary operation dest source =>
    let first := (readReg source).run state
    have contained : Prefix first.2.nodes ((evalOp (.unary operation dest source)).run state).2.nodes :=
      growing_intern (.unary operation first.1) first.2
    obtain ⟨word, read⟩ := readReg_defined state frame meaning rooted total sourceSize old source
      (guarded.prefix contained)
    exact ⟨frame.set dest (operation.eval word), by simp only [Lir.Op.exec, read, Option.map_some]⟩
  | binary operation dest left right =>
    show ∃ frame', (Lir.Op.binary operation dest left right).exec frame memory = some (frame', memory)
    change Silmaril.Compile.Mir.DeadCode.faults operation = false at admitted
    let first := (readReg left).run state
    let second := (readReg right).run first.2
    have actual : (evalOp (.binary operation dest left right)).run state =
        (writeReg dest ((intern (.binary operation first.1 second.1)).run second.2).1).run
          ((intern (.binary operation first.1 second.1)).run second.2).2 := by
      simp only [evalOp, admitted, Bool.false_eq_true, ↓reduceIte]
      rfl
    have secondPrefix : Prefix second.2.nodes ((evalOp (.binary operation dest left right)).run state).2.nodes := by
      rw [actual]
      exact growing_intern (.binary operation first.1 second.1) second.2
    have firstPrefix : Prefix first.2.nodes ((evalOp (.binary operation dest left right)).run state).2.nodes :=
      (growing_readReg right first.2).trans secondPrefix
    obtain ⟨x, leftRead⟩ := readReg_defined state frame meaning rooted total sourceSize old left
      (guarded.prefix firstPrefix)
    obtain ⟨firstMeaning, firstRead, firstTotal⟩ :=
      Total.readReg_sound state frame meaning rooted total left x leftRead
    have oldFirst : sourceSize ≤ first.2.nodes.size := old.trans (growing_readReg left state).grows
    obtain ⟨y, rightRead⟩ := readReg_defined first.2 frame firstMeaning firstRead.rooted firstTotal
      sourceSize oldFirst right (guarded.prefix secondPrefix)
    obtain ⟨result, computed⟩ := nonfaulting_binary_total operation admitted x y
    exact ⟨frame.set dest result, by
      simp only [Lir.Op.exec, leftRead, rightRead, computed, Option.bind_some, Option.map_some]⟩
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot => cases admitted
  | slotSet slot source => cases admitted

theorem evalOp_success (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (sourceSize : Nat)
    (old : sourceSize ≤ state.nodes.size) (op : Lir.Op Nat) (admitted : Roots.Admitted op)
    (guarded : Guarded sourceSize ((evalOp op).run state).2.nodes) :
    ∃ frame' newMeaning, op.exec frame memory = some (frame', memory) ∧
      OpResult state ((evalOp op).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((evalOp op).run state).2.nodes newMeaning := by
  obtain ⟨frame', executed⟩ := evalOp_exists state frame memory meaning rooted total sourceSize old op admitted guarded
  obtain ⟨sameMemory, newMeaning, actual, afterTotal⟩ :=
    Total.evalOp_sound state frame frame' memory memory meaning rooted total op admitted executed
  exact ⟨frame', newMeaning, executed, actual, afterTotal⟩

/-- The real candidate list executes from the actual partial frame. The only
fragment restriction is the existing pure admitted instruction predicate. -/
theorem instructions_success (calls : OpenCalls) (instructions : List Silmaril.Compile.Mir.Instr)
    (admitted : Lists.Admitted instructions) (state : State) (frame : Lir.Frame Nat)
    (memory : Lir.Memory) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((instructions.forM evalInstr).run state).2.nodes) :
    ∃ frame' newMeaning, InstructionsExec calls instructions frame memory frame' memory ∧
      OpResult state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((instructions.forM evalInstr).run state).2.nodes newMeaning := by
  induction instructions generalizing state frame meaning with
  | nil => exact ⟨frame, meaning, .nil, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, total⟩
  | cons instruction rest ih =>
    show ∃ frame' newMeaning, InstructionsExec calls (instruction :: rest) frame memory frame' memory ∧
      OpResult state (((instruction :: rest).forM evalInstr).run state).2 frame' meaning newMeaning ∧
      TotalNodes (((instruction :: rest).forM evalInstr).run state).2.nodes newMeaning
    have headAdmitted : Lists.AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Lists.Admitted rest := fun i member => admitted i (by simp [member])
    have headGuard : Guarded sourceSize ((evalInstr instruction).run state).2.nodes := by
      have finalGuard : Guarded sourceSize ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.nodes := by
        simpa only [Lists.forM_cons_run] using guarded
      exact finalGuard.prefix (growing_forM rest tailAdmitted ((evalInstr instruction).run state).2)
    have step : ∃ middle middleMeaning,
        InstructionExec calls instruction frame memory middle memory ∧
        OpResult state ((evalInstr instruction).run state).2 middle meaning middleMeaning ∧
        TotalNodes ((evalInstr instruction).run state).2.nodes middleMeaning := by
      cases instruction with
      | op op =>
        obtain ⟨middle, middleMeaning, executed, actual, afterTotal⟩ :=
          evalOp_success state frame memory meaning rooted total sourceSize old op headAdmitted headGuard
        exact ⟨middle, middleMeaning, .op executed, actual, afterTotal⟩
      | fop op dest left right => cases headAdmitted
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect target args results => cases headAdmitted
    obtain ⟨middle, middleMeaning, headExecuted, headResult, headTotal⟩ := step
    have tailGuard : Guarded sourceSize ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.nodes := by
      simpa only [Lists.forM_cons_run] using guarded
    obtain ⟨frame', newMeaning, tailExecuted, tailResult, tailTotal⟩ :=
      ih tailAdmitted ((evalInstr instruction).run state).2 middle middleMeaning headResult.rooted headTotal
        (old.trans headResult.grows) tailGuard
    rw [Lists.forM_cons_run]
    exact ⟨frame', newMeaning, .cons headExecuted tailExecuted, Lists.result_trans headResult tailResult, tailTotal⟩


theorem readSlot_defined (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size) (slot : Nat)
    (guarded : Guarded sourceSize ((readSlot slot).run state).2.nodes) :
    ∃ word, frame.slots slot = some word := by
  cases found : state.slots.find? (·.1 == slot) with
  | some root =>
    obtain ⟨word, defined⟩ := total root.2 (rooted.slotsBounded root (List.mem_of_find?_eq_some found))
    have selected : meaning.value root.2 = frame.slots slot := by simpa [Roots.slotValue, found] using rooted.slots slot
    exact ⟨word, selected.symm.trans defined⟩
  | none =>
    have readRun : (readSlot slot).run state = (intern (.slot slot)).run state := by rw [readSlot_run, found]
    have atIndex : ((intern (.slot slot)).run state).2.nodes[((intern (.slot slot)).run state).1]? = some (.slot slot) :=
      (Intern.returned_index state (.slot slot)).2
    have sourceBound : ((intern (.slot slot)).run state).1 < sourceSize := by
      rw [readRun] at guarded
      exact guarded _ _ atIndex rfl
    have beforeBound : ((intern (.slot slot)).run state).1 < state.nodes.size := Nat.lt_of_lt_of_le sourceBound old
    have oldNode : state.nodes[((intern (.slot slot)).run state).1]? = some (.slot slot) :=
      (Intern.old_node state (.slot slot) beforeBound).symm.trans atIndex
    obtain ⟨word, defined⟩ := total _ beforeBound
    have external : meaning.slot slot = some word := (rooted.coherent _ _ oldNode).symm.trans defined
    have selected : meaning.slot slot = frame.slots slot := by simpa [Roots.slotValue, found] using rooted.slots slot
    exact ⟨word, selected.symm.trans external⟩

theorem readReg_success (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size) (reg : Nat)
    (guarded : Guarded sourceSize ((readReg reg).run state).2.nodes) :
    ∃ word newMeaning, frame.get reg = some word ∧
      ReadResult state ((readReg reg).run state).2 frame (some word)
        ((readReg reg).run state).1 meaning newMeaning ∧
      TotalNodes ((readReg reg).run state).2.nodes newMeaning := by
  obtain ⟨word, read⟩ := readReg_defined state frame meaning rooted total sourceSize old reg guarded
  obtain ⟨newMeaning, actual, afterTotal⟩ := Total.readReg_sound state frame meaning rooted total reg word read
  exact ⟨word, newMeaning, read, actual, afterTotal⟩

theorem readSlot_success (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size) (slot : Nat)
    (guarded : Guarded sourceSize ((readSlot slot).run state).2.nodes) :
    ∃ word newMeaning, frame.slots slot = some word ∧
      ReadResult state ((readSlot slot).run state).2 frame (some word)
        ((readSlot slot).run state).1 meaning newMeaning ∧
      TotalNodes ((readSlot slot).run state).2.nodes newMeaning := by
  obtain ⟨word, read⟩ := readSlot_defined state frame meaning rooted total sourceSize old slot guarded
  obtain ⟨newMeaning, actual, afterTotal⟩ := Observation.readSlot_sound state frame meaning rooted total slot word read
  exact ⟨word, newMeaning, read, actual, afterTotal⟩

theorem evalLoc_success (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size) (loc : Lir.Loc Nat)
    (guarded : Guarded sourceSize ((evalLoc loc).run state).2.nodes) :
    ∃ word newMeaning, frame.read loc = some word ∧
      ReadResult state ((evalLoc loc).run state).2 frame (some word)
        ((evalLoc loc).run state).1 meaning newMeaning ∧
      TotalNodes ((evalLoc loc).run state).2.nodes newMeaning := by
  cases loc with
  | reg reg => exact readReg_success state frame meaning rooted total sourceSize old reg guarded
  | slot slot => exact readSlot_success state frame meaning rooted total sourceSize old slot guarded

/-- Sequence actual guarded reads; every head value survives subsequent DAG
extensions and is decoded under the same final interpretation. -/
theorem mapM_success {α : Type} (action : α → StateM State Nat)
    (read : α → Option Lir.Word) (items : List α) (frame : Lir.Frame Nat) (sourceSize : Nat)
    (growing : ∀ item, Growing (action item))
    (step : ∀ state meaning, Rooted state frame meaning → TotalNodes state.nodes meaning →
      sourceSize ≤ state.nodes.size → ∀ item,
      Guarded sourceSize ((action item).run state).2.nodes →
      ∃ word newMeaning, read item = some word ∧
        ReadResult state ((action item).run state).2 frame (some word)
          ((action item).run state).1 meaning newMeaning ∧
        TotalNodes ((action item).run state).2.nodes newMeaning)
    (state : State) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((items.mapM action).run state).2.nodes) :
    ∃ values newMeaning, items.mapM read = some values ∧
      Observation.ReadValues state ((items.mapM action).run state).2 frame
        ((items.mapM action).run state).1 values meaning newMeaning := by
  induction items generalizing state meaning with
  | nil =>
    exact ⟨[], meaning, rfl, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩,
      total, (fun _ member => nomatch member), rfl⟩
  | cons item rest ih =>
    show ∃ values newMeaning, (item :: rest).mapM read = some values ∧
      Observation.ReadValues state (((item :: rest).mapM action).run state).2 frame
        (((item :: rest).mapM action).run state).1 values meaning newMeaning
    let first := (action item).run state
    let tail := (rest.mapM action).run first.2
    have afterFirst : Guarded sourceSize first.2.nodes := by
      have finalGuard : Guarded sourceSize tail.2.nodes := by
        simpa only [Observation.mapM_cons_run] using guarded
      exact finalGuard.prefix (growing_mapM action rest growing first.2)
    obtain ⟨word, middleMeaning, firstRead, actualRead, middleTotal⟩ :=
      step state meaning rooted total old item afterFirst
    have afterTail : Guarded sourceSize tail.2.nodes := by
      simpa only [Observation.mapM_cons_run] using guarded
    obtain ⟨tailValues, newMeaning, tailRead, actualTail⟩ :=
      ih first.2 middleMeaning actualRead.rooted middleTotal (old.trans actualRead.grows) afterTail
    have firstBound : first.1 < tail.2.nodes.size := Nat.lt_of_lt_of_le actualRead.bounded actualTail.result.grows
    have firstSelected : newMeaning.value first.1 = some word :=
      (actualTail.result.extension.values first.1 actualRead.bounded).trans actualRead.selected
    refine ⟨word :: tailValues, newMeaning, ?_, ?_⟩
    · simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, firstRead, Option.bind_some, tailRead]
    · show Observation.ReadValues state (((item :: rest).mapM action).run state).2 frame
        (((item :: rest).mapM action).run state).1 (word :: tailValues) meaning newMeaning
      rw [Observation.mapM_cons_run]
      refine ⟨Lists.result_trans (Observation.read_result actualRead) actualTail.result,
        actualTail.total, ?_, ?_⟩
      · intro index member
        rcases List.mem_cons.mp member with equal | later
        · subst index
          exact firstBound
        · exact actualTail.bounded index later
      · have tailSelected : tail.1.mapM newMeaning.value = some tailValues := actualTail.selected
        change (first.1 :: tail.1).mapM newMeaning.value = some (word :: tailValues)
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, firstSelected,
          Option.bind_some, tailSelected]

theorem readRegs_success (registers : List Nat) (frame : Lir.Frame Nat) (sourceSize : Nat)
    (state : State) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((registers.mapM readReg).run state).2.nodes) :
    ∃ values newMeaning, registers.mapM frame.get = some values ∧
      Observation.ReadValues state ((registers.mapM readReg).run state).2 frame
        ((registers.mapM readReg).run state).1 values meaning newMeaning :=
  mapM_success readReg frame.get registers frame sourceSize growing_readReg
    (fun s m r t b reg g => readReg_success s frame m r t sourceSize b reg g)
    state meaning rooted total old guarded

theorem evalLocs_success (locations : List (Lir.Loc Nat)) (frame : Lir.Frame Nat) (sourceSize : Nat)
    (state : State) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((locations.mapM evalLoc).run state).2.nodes) :
    ∃ values newMeaning, frame.readAll locations = some values ∧
      Observation.ReadValues state ((locations.mapM evalLoc).run state).2 frame
        ((locations.mapM evalLoc).run state).1 values meaning newMeaning :=
  mapM_success evalLoc frame.read locations frame sourceSize growing_evalLoc
    (fun s m r t b loc g => evalLoc_success s frame m r t sourceSize b loc g)
    state meaning rooted total old guarded


/-- The actual symbolic terminator's guarded reads imply concrete terminator
success, including slot returns and both branch decisions. -/
theorem evalTerm_exists (term : Lir.Term Nat) (frame : Lir.Frame Nat)
    (state : State) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((evalTerm term).run state).2.nodes) :
    ∃ exit, TermExec term frame exit := by
  cases term with
  | jump label => exact ⟨.jump label, .jump⟩
  | branch reg yes no =>
    obtain ⟨word, read⟩ := readReg_defined state frame meaning rooted total sourceSize old reg guarded
    by_cases zero : word = 0
    · exact ⟨.jump no, .zero (zero ▸ read)⟩
    · exact ⟨.jump yes, .nonzero read zero⟩
  | ret locations =>
    obtain ⟨values, newMeaning, read, actual⟩ :=
      evalLocs_success locations frame sourceSize state meaning rooted total old guarded
    exact ⟨.returned values, .ret read⟩
  | trap => exact ⟨.trapped, .trap⟩

theorem evalTerm_success (term : Lir.Term Nat) (frame : Lir.Frame Nat)
    (state : State) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((evalTerm term).run state).2.nodes) :
    ∃ exit newMeaning, TermExec term frame exit ∧
      Observation.TermResult state ((evalTerm term).run state).2 frame
        ((evalTerm term).run state).1 exit meaning newMeaning := by
  obtain ⟨exit, executed⟩ := evalTerm_exists term frame state meaning rooted total sourceSize old guarded
  obtain ⟨newMeaning, actual⟩ := Observation.evalTerm_sound term frame exit executed state meaning rooted total
  exact ⟨exit, newMeaning, executed, actual⟩

/-- Candidate execution and observed-read success are derived from the real
final guard, in the exact instruction → terminator → observation order. -/
theorem block_success (calls : OpenCalls) (block : Silmaril.Compile.Mir.Block)
    (admitted : Lists.Admitted block.instrs.toList) (observed : List Nat)
    (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size)
    (guarded : Guarded sourceSize ((evalBlock block observed).run state).2.nodes) :
    ∃ exit frame' values newMeaning,
      BlockExec calls block frame memory exit frame' memory ∧
      observed.mapM frame'.get = some values ∧
      Observation.BlockResult state ((evalBlock block observed).run state).2 frame'
        ((evalBlock block observed).run state).1.1 ((evalBlock block observed).run state).1.2
        exit values meaning newMeaning := by
  let body := (block.instrs.toList.forM evalInstr).run state
  let term := (evalTerm block.term).run body.2
  let observations := (observed.mapM readReg).run term.2
  have afterTerm : Guarded sourceSize term.2.nodes := by
    rw [Lists.evalBlock_run] at guarded
    exact guarded.prefix (growing_mapM readReg observed growing_readReg term.2)
  have afterBody : Guarded sourceSize body.2.nodes :=
    afterTerm.prefix (growing_evalTerm block.term body.2)
  obtain ⟨frame', bodyMeaning, bodyExecuted, bodyResult, bodyTotal⟩ :=
    instructions_success calls block.instrs.toList admitted state frame memory meaning rooted total sourceSize old afterBody
  obtain ⟨exit, termMeaning, termExecuted, termResult⟩ :=
    evalTerm_success block.term frame' body.2 bodyMeaning bodyResult.rooted bodyTotal sourceSize
      (old.trans bodyResult.grows) afterTerm
  have afterObservations : Guarded sourceSize observations.2.nodes := by
    simpa only [Lists.evalBlock_run] using guarded
  obtain ⟨values, newMeaning, read, observedResult⟩ :=
    readRegs_success observed frame' sourceSize term.2 termMeaning termResult.result.rooted termResult.total
      ((old.trans bodyResult.grows).trans termResult.result.grows) afterObservations
  have common : OpResult state observations.2 frame' meaning newMeaning :=
    Lists.result_trans bodyResult (Lists.result_trans termResult.result observedResult.result)
  have scopedTerm : Observation.TermScoped observations.2.nodes.size term.1 :=
    Observation.termScoped_mono term.1 observedResult.result.grows termResult.wellScoped
  have decoded : Observation.termExit newMeaning term.1 = some exit :=
    (Observation.termExit_preserved term.1 observedResult.result.extension termResult.wellScoped).trans termResult.selected
  rw [Lists.evalBlock_run]
  exact ⟨exit, frame', values, newMeaning, ⟨bodyExecuted, termExecuted⟩, read,
    ⟨common, observedResult.total, scopedTerm, decoded⟩, observedResult.bounded, observedResult.selected⟩

/-- Resetting symbolic root maps for the candidate preserves the actual initial
partial frame while retaining the complete successful source DAG. -/
theorem seed_rooted (frame sourceFrame : Lir.Frame Nat) (sourceState : State) (meaning : Interpretation)
    (source : OpResult {} sourceState sourceFrame (Total.initialMeaning frame) meaning) :
    Rooted { nodes := sourceState.nodes } frame meaning := by
  refine ⟨source.rooted.wellScoped, source.rooted.coherent, ?_, ?_, ?_, ?_⟩
  · intro root member
    cases member
  · intro root member
    cases member
  · intro reg
    change meaning.input reg = frame.get reg
    exact congrFun source.extension.input reg
  · intro slot
    change meaning.slot slot = frame.slots slot
    exact congrFun source.extension.slot slot

/-- Use the exact retained suffix guard and actual candidate start state from
Validation.check. Source success supplies the initial DAG denotation; candidate
execution and concrete candidate reads are conclusions. -/
theorem seeded_block_success (calls : OpenCalls) (block : Silmaril.Compile.Mir.Block)
    (admitted : Lists.Admitted block.instrs.toList) (observed : List Nat)
    (frame sourceFrame : Lir.Frame Nat) (memory : Lir.Memory) (sourceState : State) (meaning : Interpretation)
    (source : OpResult {} sourceState sourceFrame (Total.initialMeaning frame) meaning)
    (total : TotalNodes sourceState.nodes meaning)
    (guarded : ((evalBlock block observed).run { nodes := sourceState.nodes }).2.nodes.any
      Expr.isPartialLeaf sourceState.nodes.size = false) :
    ∃ exit frame' values newMeaning,
      BlockExec calls block frame memory exit frame' memory ∧
      observed.mapM frame'.get = some values ∧
      Observation.BlockResult { nodes := sourceState.nodes }
        ((evalBlock block observed).run { nodes := sourceState.nodes }).2 frame'
        ((evalBlock block observed).run { nodes := sourceState.nodes }).1.1
        ((evalBlock block observed).run { nodes := sourceState.nodes }).1.2
        exit values meaning newMeaning :=
  block_success calls block admitted observed { nodes := sourceState.nodes } frame memory meaning
    (seed_rooted frame sourceFrame sourceState meaning source) total sourceState.nodes.size (Nat.le_refl _)
    (guarded_of_any _ _ guarded)

end Silmaril.Compiler.Native.Optimize.Validation.Candidate
