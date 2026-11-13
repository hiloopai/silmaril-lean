module

public import Silmaril.Compiler.Native.Optimize.Validation.Total.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Total
open Silmaril.Machine
open Roots
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem empty_total (meaning : Interpretation) : TotalNodes #[] meaning := by
  intro index bounded
  simp at bounded

theorem initial_rooted (frame : Lir.Frame Nat) : Rooted {} frame (initialMeaning frame) := by
  constructor
  · intro index expression atIndex
    simp at atIndex
  · intro index expression atIndex
    simp at atIndex
  · intro root member
    cases member
  · intro root member
    cases member
  · intro reg
    rfl
  · intro slot
    rfl

/-- Real interning either reuses the old DAG or adds exactly its returned
index. Defined raw denotation therefore suffices to retain total node values. -/
theorem intern_result_total (state : State) (raw : Expr) (word : Lir.Word)
    (oldMeaning newMeaning : Interpretation) (total : TotalNodes state.nodes oldMeaning)
    (extension : Extends state.nodes.size oldMeaning newMeaning)
    (selected : newMeaning.value ((intern raw).run state).1 = some word) :
    TotalNodes ((intern raw).run state).2.nodes newMeaning := by
  rcases Intern.cases_actual state raw with ⟨index, found, actual⟩ | ⟨missing, actual⟩
  · rw [actual]
    intro other bounded
    obtain ⟨value, defined⟩ := total other bounded
    exact ⟨value, (extension.values other bounded).trans defined⟩
  · have appended : newMeaning.value state.nodes.size = some word := by simpa only [actual] using selected
    rw [actual]
    intro other bounded
    by_cases old : other < state.nodes.size
    · obtain ⟨value, defined⟩ := total other old
      exact ⟨value, (extension.values other old).trans defined⟩
    · have last : other = state.nodes.size := by simp only [Array.size_push] at bounded; omega
      exact ⟨word, last ▸ appended⟩

theorem intern_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (raw : Expr) (rawScoped : Intern.ReferencesBelow state.nodes.size raw) (word : Lir.Word)
    (computed : raw.eval meaning = some word) :
    ∃ newMeaning, ReadResult state ((intern raw).run state).2 frame (some word)
      ((intern raw).run state).1 meaning newMeaning ∧
      TotalNodes ((intern raw).run state).2.nodes newMeaning := by
  obtain ⟨newMeaning, actual⟩ := intern_rooted state frame meaning rooted raw rawScoped
  have selected : newMeaning.value ((intern raw).run state).1 = some word := actual.selected.trans computed
  exact ⟨newMeaning, { actual with selected },
    intern_result_total state raw word meaning newMeaning total actual.extension selected⟩

private theorem readReg_run (state : State) (reg : Nat) :
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

theorem readReg_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (reg : Nat) (word : Lir.Word) (read : frame.get reg = some word) :
    ∃ newMeaning, ReadResult state ((readReg reg).run state).2 frame (some word)
      ((readReg reg).run state).1 meaning newMeaning ∧
      TotalNodes ((readReg reg).run state).2.nodes newMeaning := by
  obtain ⟨newMeaning, actual⟩ := Roots.readReg_sound state frame meaning rooted reg
  have selected : newMeaning.value ((readReg reg).run state).1 = some word := actual.selected.trans read
  refine ⟨newMeaning, { actual with selected }, ?_⟩
  cases found : state.regs.find? (·.1 == reg) with
  | none =>
    have run : (readReg reg).run state = (intern (.input reg)).run state := by rw [readReg_run, found]
    rw [run] at selected ⊢
    exact intern_result_total state (.input reg) word meaning newMeaning total actual.extension selected
  | some root =>
    rw [readReg_run, found]
    intro index bounded
    obtain ⟨value, defined⟩ := total index bounded
    exact ⟨value, (actual.extension.values index bounded).trans defined⟩

private theorem write_result {before middle : State} {frame : Lir.Frame Nat}
    {oldMeaning newMeaning : Interpretation} {index : Nat} {word : Lir.Word}
    (actual : ReadResult before middle frame (some word) index oldMeaning newMeaning)
    (total : TotalNodes middle.nodes newMeaning) (dest : Nat) :
    OpResult before ((writeReg dest index).run middle).2 (frame.set dest word) oldMeaning newMeaning ∧
      TotalNodes ((writeReg dest index).run middle).2.nodes newMeaning :=
  ⟨⟨writeReg_rooted middle frame newMeaning actual.rooted dest index word actual.bounded actual.selected,
    actual.extension, actual.grows, actual.effects⟩, total⟩

theorem const_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (dest : Nat) (word : Lir.Word) :
    ∃ newMeaning, OpResult state ((evalOp (.const dest word)).run state).2
      (frame.set dest word) meaning newMeaning ∧ TotalNodes ((evalOp (.const dest word)).run state).2.nodes newMeaning := by
  obtain ⟨newMeaning, actual, totalAfter⟩ := intern_sound state frame meaning rooted total (.const word) trivial word rfl
  exact ⟨newMeaning, write_result actual totalAfter dest⟩

theorem move_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (dest source : Nat) (word : Lir.Word) (read : frame.get source = some word) :
    ∃ newMeaning, OpResult state ((evalOp (.move dest source)).run state).2
      (frame.set dest word) meaning newMeaning ∧ TotalNodes ((evalOp (.move dest source)).run state).2.nodes newMeaning := by
  obtain ⟨newMeaning, actual, totalAfter⟩ := readReg_sound state frame meaning rooted total source word read
  exact ⟨newMeaning, write_result actual totalAfter dest⟩

theorem unary_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (op : Lir.Unop) (dest source : Nat) (word : Lir.Word) (read : frame.get source = some word) :
    ∃ newMeaning, OpResult state ((evalOp (.unary op dest source)).run state).2
      (frame.set dest (op.eval word)) meaning newMeaning ∧
      TotalNodes ((evalOp (.unary op dest source)).run state).2.nodes newMeaning := by
  obtain ⟨readMeaning, actualRead, readTotal⟩ := readReg_sound state frame meaning rooted total source word read
  have computed : (Expr.unary op ((readReg source).run state).1).eval readMeaning = some (op.eval word) := by
    simp only [Expr.eval, actualRead.selected, Option.map_some]
  obtain ⟨newMeaning, actualIntern, totalAfter⟩ := intern_sound ((readReg source).run state).2 frame readMeaning
    actualRead.rooted readTotal (.unary op ((readReg source).run state).1) actualRead.bounded (op.eval word) computed
  exact ⟨newMeaning, write_result (actualRead.trans actualIntern) totalAfter dest⟩

theorem binary_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (op : Lir.Binop) (dest left right : Nat) (x y result : Lir.Word)
    (leftRead : frame.get left = some x) (rightRead : frame.get right = some y)
    (computed : op.eval x y = some result) (nonfaulting : Silmaril.Compile.Mir.DeadCode.faults op = false) :
    ∃ newMeaning, OpResult state ((evalOp (.binary op dest left right)).run state).2
      (frame.set dest result) meaning newMeaning ∧
      TotalNodes ((evalOp (.binary op dest left right)).run state).2.nodes newMeaning := by
  let first := (readReg left).run state
  let second := (readReg right).run first.2
  obtain ⟨firstMeaning, firstRead, firstTotal⟩ := readReg_sound state frame meaning rooted total left x leftRead
  obtain ⟨secondMeaning, secondRead, secondTotal⟩ :=
    readReg_sound first.2 frame firstMeaning firstRead.rooted firstTotal right y rightRead
  have firstBound : first.1 < second.2.nodes.size := Nat.lt_of_lt_of_le firstRead.bounded secondRead.grows
  have firstSelected : secondMeaning.value first.1 = some x :=
    (secondRead.extension.values first.1 firstRead.bounded).trans firstRead.selected
  have secondSelected : secondMeaning.value second.1 = some y := secondRead.selected
  have selected : (Expr.binary op first.1 second.1).eval secondMeaning = some result := by
    simp only [Expr.eval, firstSelected, secondSelected, Option.bind_some, computed]
  obtain ⟨newMeaning, actualIntern, totalAfter⟩ := intern_sound second.2 frame secondMeaning secondRead.rooted
    secondTotal (.binary op first.1 second.1) ⟨firstBound, secondRead.bounded⟩ result selected
  have actual : (evalOp (.binary op dest left right)).run state =
      (writeReg dest ((intern (.binary op first.1 second.1)).run second.2).1).run
        ((intern (.binary op first.1 second.1)).run second.2).2 := by
    simp only [evalOp, nonfaulting, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [actual]
  exact ⟨newMeaning, write_result (firstRead.trans (secondRead.trans actualIntern)) totalAfter dest⟩

theorem evalOp_sound (state : State) (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning)
    (op : Lir.Op Nat)
    (admitted : Admitted op) (executed : op.exec frame memory = some (frame', memory')) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((evalOp op).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((evalOp op).run state).2.nodes newMeaning := by
  cases op with
  | const dest word =>
    have output : frame.set dest word = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact const_sound state frame meaning rooted total dest word
  | move dest source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.set dest word = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact move_sound state frame meaning rooted total dest source word read
  | unary op dest source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.set dest (op.eval word) = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact unary_sound state frame meaning rooted total op dest source word read
  | binary op dest left right =>
    show memory' = memory ∧ ∃ newMeaning,
      OpResult state ((evalOp (.binary op dest left right)).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((evalOp (.binary op dest left right)).run state).2.nodes newMeaning
    obtain ⟨x, leftRead, y, rightRead, result, computed, output⟩ :
        ∃ x, frame.get left = some x ∧ ∃ y, frame.get right = some y ∧
          ∃ result, op.eval x y = some result ∧ (frame.set dest result = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact binary_sound state frame meaning rooted total op dest left right x y result
      leftRead rightRead computed admitted
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot => cases admitted
  | slotSet slot source => cases admitted

/-- The actual open-Mir instruction relation lifts the same primitive result.
No call, address, floating-point, load, store or faulting case is asserted. -/
theorem evalInstr_op_sound (calls : OpenCalls) (state : State) (frame frame' : Lir.Frame Nat)
    (memory memory' : Lir.Memory) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : TotalNodes state.nodes meaning) (op : Lir.Op Nat) (admitted : Admitted op)
    (executed : InstructionExec calls (.op op) frame memory frame' memory') :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((evalInstr (.op op)).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((evalInstr (.op op)).run state).2.nodes newMeaning := by
  cases executed with
  | op actual => exact evalOp_sound state frame frame' memory memory' meaning rooted total op admitted actual


/-- Total source DAG values follow along actual successful instruction-list
execution, retaining the complete rooted interpretation and effect trace. -/
theorem instructions_sound (calls : OpenCalls) (instructions : List Silmaril.Compile.Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (executed : InstructionsExec calls instructions frame memory frame' memory')
    (admitted : Lists.Admitted instructions) (state : State) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : TotalNodes state.nodes meaning) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning ∧
      TotalNodes ((instructions.forM evalInstr).run state).2.nodes newMeaning := by
  induction executed generalizing state meaning with
  | nil => exact ⟨rfl, meaning, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, total⟩
  | @cons instruction rest frame memory middle middleMem frame' memory' first tail ih =>
    show memory' = memory ∧ ∃ newMeaning,
      OpResult state (((instruction :: rest).forM evalInstr).run state).2 frame' meaning newMeaning ∧
      TotalNodes (((instruction :: rest).forM evalInstr).run state).2.nodes newMeaning
    have headAdmitted : Lists.AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Lists.Admitted rest := fun i member => admitted i (by simp [member])
    have step : middleMem = memory ∧ ∃ middleMeaning,
        OpResult state ((evalInstr instruction).run state).2 middle meaning middleMeaning ∧
        TotalNodes ((evalInstr instruction).run state).2.nodes middleMeaning := by
      cases instruction with
      | op op => exact evalInstr_op_sound calls state frame middle memory middleMem meaning rooted total op headAdmitted first
      | fop op dest left right => cases headAdmitted
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect target args results => cases headAdmitted
    obtain ⟨stepMemory, middleMeaning, stepResult, stepTotal⟩ := step
    obtain ⟨tailMemory, newMeaning, tailResult, finalTotal⟩ := ih tailAdmitted
      ((evalInstr instruction).run state).2 middleMeaning stepResult.rooted stepTotal
    rw [Lists.forM_cons_run]
    exact ⟨tailMemory.trans stepMemory, newMeaning, Lists.result_trans stepResult tailResult, finalTotal⟩

/-- Start from the genuine empty validator DAG and actual partial input frame.
Initial Rooted and total-DAG invariants are constructed, not supplied by a
successful checker or an abstract simulation premise. -/
theorem source_instructions_sound (calls : OpenCalls) (instructions : List Silmaril.Compile.Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (executed : InstructionsExec calls instructions frame memory frame' memory')
    (admitted : Lists.Admitted instructions) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult {} ((instructions.forM evalInstr).run {}).2 frame' (initialMeaning frame) newMeaning ∧
      TotalNodes ((instructions.forM evalInstr).run {}).2.nodes newMeaning :=
  instructions_sound calls instructions frame frame' memory memory' executed admitted {} (initialMeaning frame)
    (initial_rooted frame) (empty_total _)

end Silmaril.Compiler.Native.Optimize.Validation.Total
