module

public import Silmaril.Compiler.Native.Optimize.Validation.Roots.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Roots
open Silmaril.Machine
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem Extends.refl (meaning : Interpretation) (bound : Nat) : Extends bound meaning meaning :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Extends.trans {small large : Nat} {first middle last : Interpretation}
    (earlier : Extends small first middle) (later : Extends large middle last) (bound : small ≤ large) :
    Extends small first last :=
  ⟨fun index bounded => (later.values index (by omega)).trans (earlier.values index bounded),
    later.input.trans earlier.input, later.slot.trans earlier.slot,
    later.address.trans earlier.address, later.load.trans earlier.load, later.result.trans earlier.result⟩

theorem regValue_preserved {before after : State} {oldMeaning newMeaning : Interpretation}
    (same : after.regs = before.regs)
    (bounded : ∀ root ∈ before.regs, root.2 < before.nodes.size)
    (extension : Extends before.nodes.size oldMeaning newMeaning) (reg : Nat) :
    regValue after newMeaning reg = regValue before oldMeaning reg := by
  simp only [regValue, same]
  cases found : before.regs.find? (·.1 == reg) with
  | none => exact congrFun extension.input reg
  | some root => exact extension.values root.2 (bounded root (List.mem_of_find?_eq_some found))

theorem slotValue_preserved {before after : State} {oldMeaning newMeaning : Interpretation}
    (same : after.slots = before.slots)
    (bounded : ∀ root ∈ before.slots, root.2 < before.nodes.size)
    (extension : Extends before.nodes.size oldMeaning newMeaning) (slot : Nat) :
    slotValue after newMeaning slot = slotValue before oldMeaning slot := by
  simp only [slotValue, same]
  cases found : before.slots.find? (·.1 == slot) with
  | none => exact congrFun extension.slot slot
  | some root => exact extension.values root.2 (bounded root (List.mem_of_find?_eq_some found))

/-- Actual interning preserves valid root maps and their complete partial frame
meaning, whether the new expression denotes some word or none. -/
theorem intern_rooted (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (raw : Expr)
    (rawScoped : Intern.ReferencesBelow state.nodes.size raw) :
    ∃ newMeaning, ReadResult state ((intern raw).run state).2 frame (raw.eval meaning)
      ((intern raw).run state).1 meaning newMeaning := by
  obtain ⟨newMeaning, denotation⟩ := Intern.sound state raw meaning rooted.wellScoped rooted.coherent rawScoped
  obtain ⟨suffix, prefixEqual, suffixBound⟩ := Intern.nodes_prefix state raw
  have grows : state.nodes.size ≤ ((intern raw).run state).2.nodes.size := by
    rw [prefixEqual]
    simp
  have mapFrame := Intern.frame state raw
  have extension : Extends state.nodes.size meaning newMeaning :=
    ⟨denotation.oldValues, denotation.input, denotation.slot, denotation.address, denotation.load, denotation.result⟩
  have rootedAfter : Rooted ((intern raw).run state).2 frame newMeaning := by
    refine ⟨denotation.wellScoped, denotation.coherent, ?_, ?_, ?_, ?_⟩
    · intro root member
      have old : root ∈ state.regs := by simpa [mapFrame.1] using member
      exact Nat.lt_of_lt_of_le (rooted.regsBounded root old) grows
    · intro root member
      have old : root ∈ state.slots := by simpa [mapFrame.2.1] using member
      exact Nat.lt_of_lt_of_le (rooted.slotsBounded root old) grows
    · intro reg
      exact (regValue_preserved mapFrame.1 rooted.regsBounded extension reg).trans (rooted.regs reg)
    · intro slot
      exact (slotValue_preserved mapFrame.2.1 rooted.slotsBounded extension slot).trans (rooted.slots slot)
  exact ⟨newMeaning, rootedAfter, denotation.bounded, denotation.selected, extension, grows, mapFrame.2.2⟩

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

/-- Missing registers are retained as none by actual symbolic readReg;
no successful concrete read is needed for this theorem. -/
theorem readReg_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (reg : Nat) :
    ∃ newMeaning, ReadResult state ((readReg reg).run state).2 frame (frame.get reg)
      ((readReg reg).run state).1 meaning newMeaning := by
  cases found : state.regs.find? (·.1 == reg) with
  | none =>
    obtain ⟨newMeaning, actual⟩ := intern_rooted state frame meaning rooted (.input reg) trivial
    have valueAt : meaning.input reg = frame.get reg := by simpa [regValue, found] using rooted.regs reg
    rw [readReg_run, found]
    exact ⟨newMeaning, { actual with selected := actual.selected.trans valueAt }⟩
  | some root =>
    have bounded : root.2 < state.nodes.size := rooted.regsBounded root (List.mem_of_find?_eq_some found)
    have valueAt : meaning.value root.2 = frame.get reg := by simpa [regValue, found] using rooted.regs reg
    rw [readReg_run, found]
    exact ⟨meaning, rooted, bounded, valueAt, .refl _ _, Nat.le_refl _, rfl⟩

private theorem readSlot_run (state : State) (slot : Nat) :
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

theorem readSlot_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (slot : Nat) :
    ∃ newMeaning, ReadResult state ((readSlot slot).run state).2 frame (frame.slots slot)
      ((readSlot slot).run state).1 meaning newMeaning := by
  cases found : state.slots.find? (·.1 == slot) with
  | none =>
    obtain ⟨newMeaning, actual⟩ := intern_rooted state frame meaning rooted (.slot slot) trivial
    have valueAt : meaning.slot slot = frame.slots slot := by simpa [slotValue, found] using rooted.slots slot
    rw [readSlot_run, found]
    exact ⟨newMeaning, { actual with selected := actual.selected.trans valueAt }⟩
  | some root =>
    have bounded : root.2 < state.nodes.size := rooted.slotsBounded root (List.mem_of_find?_eq_some found)
    have valueAt : meaning.value root.2 = frame.slots slot := by simpa [slotValue, found] using rooted.slots slot
    rw [readSlot_run, found]
    exact ⟨meaning, rooted, bounded, valueAt, .refl _ _, Nat.le_refl _, rfl⟩

theorem readReg_missing (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (reg : Nat) (missing : frame.get reg = none) :
    ∃ newMeaning, ReadResult state ((readReg reg).run state).2 frame none
      ((readReg reg).run state).1 meaning newMeaning := by
  obtain ⟨newMeaning, actual⟩ := readReg_sound state frame meaning rooted reg
  exact ⟨newMeaning, { actual with selected := actual.selected.trans missing }⟩

theorem readSlot_missing (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (slot : Nat) (missing : frame.slots slot = none) :
    ∃ newMeaning, ReadResult state ((readSlot slot).run state).2 frame none
      ((readSlot slot).run state).1 meaning newMeaning := by
  obtain ⟨newMeaning, actual⟩ := readSlot_sound state frame meaning rooted slot
  exact ⟨newMeaning, { actual with selected := actual.selected.trans missing }⟩

private theorem find_updated (entries : List (Nat × Nat)) (dest index reg : Nat) :
    ((dest, index) :: entries.filter (·.1 != dest)).find? (·.1 == reg) =
      if reg = dest then some (dest, index) else entries.find? (·.1 == reg) := by
  by_cases same : reg = dest
  · subst reg
    simp
  · have filtered : (entries.filter (·.1 != dest)).find? (·.1 == reg) =
        entries.find? (·.1 == reg) := by
      induction entries with
      | nil => rfl
      | cons root rest ih =>
        obtain ⟨key, value⟩ := root
        by_cases removed : key = dest
        · subst key
          simp [Ne.symm same, ih]
        · simp [removed, List.find?_cons, ih]
    simp [same, Ne.symm same, filtered]

private theorem writeReg_run (state : State) (dest index : Nat) :
    (writeReg dest index).run state =
      ((), { state with regs := (dest, index) :: state.regs.filter (·.1 != dest) }) := rfl

/-- A bounded root denoting a concrete word updates exactly the corresponding
actual frame register. The destination may be fresh and previously missing. -/
theorem writeReg_rooted (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (dest index : Nat) (word : Lir.Word)
    (bounded : index < state.nodes.size) (selected : meaning.value index = some word) :
    Rooted ((writeReg dest index).run state).2 (frame.set dest word) meaning := by
  rw [writeReg_run]
  refine ⟨rooted.wellScoped, rooted.coherent, ?_, rooted.slotsBounded, ?_, rooted.slots⟩
  · intro root member
    change root ∈ (dest, index) :: state.regs.filter (·.1 != dest) at member
    rcases List.mem_cons.mp member with equal | filtered
    · subst root
      exact bounded
    · exact rooted.regsBounded root (List.mem_filter.mp filtered).1
  · intro reg
    simp only [regValue, find_updated, Lir.Frame.get_set]
    by_cases same : reg = dest
    · simp [same, selected]
    · simpa [same, regValue] using rooted.regs reg

theorem ReadResult.trans {before middle after : State} {frame : Lir.Frame Nat}
    {firstExpected lastExpected : Option Lir.Word} {firstIndex lastIndex : Nat}
    {first middleMeaning last : Interpretation}
    (earlier : ReadResult before middle frame firstExpected firstIndex first middleMeaning)
    (later : ReadResult middle after frame lastExpected lastIndex middleMeaning last) :
    ReadResult before after frame lastExpected lastIndex first last :=
  ⟨later.rooted, later.bounded, later.selected,
    earlier.extension.trans later.extension earlier.grows,
    earlier.grows.trans later.grows, later.effects.trans earlier.effects⟩

private theorem write_read_result {before middle : State} {frame : Lir.Frame Nat}
    {oldMeaning newMeaning : Interpretation} {index : Nat} {word : Lir.Word}
    (actual : ReadResult before middle frame (some word) index oldMeaning newMeaning) (dest : Nat) :
    OpResult before ((writeReg dest index).run middle).2 (frame.set dest word) oldMeaning newMeaning :=
  ⟨writeReg_rooted middle frame newMeaning actual.rooted dest index word actual.bounded actual.selected,
    actual.extension, actual.grows, actual.effects⟩

theorem const_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (dest : Nat) (word : Lir.Word) :
    ∃ newMeaning, OpResult state ((evalOp (.const dest word)).run state).2
      (frame.set dest word) meaning newMeaning := by
  obtain ⟨newMeaning, actual⟩ := intern_rooted state frame meaning rooted (.const word) trivial
  exact ⟨newMeaning, write_read_result actual dest⟩

theorem move_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (dest source : Nat) (word : Lir.Word)
    (read : frame.get source = some word) :
    ∃ newMeaning, OpResult state ((evalOp (.move dest source)).run state).2
      (frame.set dest word) meaning newMeaning := by
  obtain ⟨newMeaning, actual⟩ := readReg_sound state frame meaning rooted source
  exact ⟨newMeaning, write_read_result { actual with selected := actual.selected.trans read } dest⟩

theorem unary_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (op : Lir.Unop) (dest source : Nat) (word : Lir.Word)
    (read : frame.get source = some word) :
    ∃ newMeaning, OpResult state ((evalOp (.unary op dest source)).run state).2
      (frame.set dest (op.eval word)) meaning newMeaning := by
  obtain ⟨readMeaning, actualRead⟩ := readReg_sound state frame meaning rooted source
  obtain ⟨newMeaning, actualIntern⟩ := intern_rooted ((readReg source).run state).2 frame readMeaning
    actualRead.rooted (.unary op ((readReg source).run state).1) actualRead.bounded
  have selected : (Expr.unary op ((readReg source).run state).1).eval readMeaning = some (op.eval word) := by
    simp only [Expr.eval, actualRead.selected, read, Option.map_some]
  have combined := actualRead.trans { actualIntern with selected := actualIntern.selected.trans selected }
  exact ⟨newMeaning, write_read_result combined dest⟩

theorem binary_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (op : Lir.Binop) (dest left right : Nat)
    (x y result : Lir.Word) (leftRead : frame.get left = some x) (rightRead : frame.get right = some y)
    (computed : op.eval x y = some result) (nonfaulting : Silmaril.Compile.Mir.DeadCode.faults op = false) :
    ∃ newMeaning, OpResult state ((evalOp (.binary op dest left right)).run state).2
      (frame.set dest result) meaning newMeaning := by
  let first := (readReg left).run state
  let second := (readReg right).run first.2
  obtain ⟨firstMeaning, firstRead⟩ := readReg_sound state frame meaning rooted left
  obtain ⟨secondMeaning, secondRead⟩ := readReg_sound first.2 frame firstMeaning firstRead.rooted right
  have firstBound : first.1 < second.2.nodes.size := Nat.lt_of_lt_of_le firstRead.bounded secondRead.grows
  have firstSelected : secondMeaning.value first.1 = some x :=
    (secondRead.extension.values first.1 firstRead.bounded).trans (firstRead.selected.trans leftRead)
  have secondSelected : secondMeaning.value second.1 = some y := secondRead.selected.trans rightRead
  obtain ⟨newMeaning, actualIntern⟩ := intern_rooted second.2 frame secondMeaning secondRead.rooted
    (.binary op first.1 second.1) ⟨firstBound, secondRead.bounded⟩
  have selected : (Expr.binary op first.1 second.1).eval secondMeaning = some result := by
    simp only [Expr.eval, firstSelected, secondSelected, Option.bind_some, computed]
  have combined := firstRead.trans (secondRead.trans
    { actualIntern with selected := actualIntern.selected.trans selected })
  have actual : (evalOp (.binary op dest left right)).run state =
      (writeReg dest ((intern (.binary op first.1 second.1)).run second.2).1).run
        ((intern (.binary op first.1 second.1)).run second.2).2 := by
    simp only [evalOp, nonfaulting, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [actual]
  exact ⟨newMeaning, write_read_result combined dest⟩

/-- Successful execution of the admitted actual Lir primitive implies coherence
of the actual symbolic evalOp result. Memory is unchanged in this fragment. -/
theorem evalOp_sound (state : State) (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning) (op : Lir.Op Nat)
    (admitted : Admitted op) (executed : op.exec frame memory = some (frame', memory')) :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((evalOp op).run state).2 frame' meaning newMeaning := by
  cases op with
  | const dest word =>
    have output : frame.set dest word = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact const_sound state frame meaning rooted dest word
  | move dest source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.set dest word = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact move_sound state frame meaning rooted dest source word read
  | unary op dest source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.set dest (op.eval word) = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact unary_sound state frame meaning rooted op dest source word read
  | binary op dest left right =>
    show memory' = memory ∧ ∃ newMeaning,
      OpResult state ((evalOp (.binary op dest left right)).run state).2 frame' meaning newMeaning
    obtain ⟨x, leftRead, y, rightRead, result, computed, output⟩ :
        ∃ x, frame.get left = some x ∧ ∃ y, frame.get right = some y ∧
          ∃ result, op.eval x y = some result ∧ (frame.set dest result = frame' ∧ memory = memory') := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨output.2.symm, ?_⟩
    rw [← output.1]
    exact binary_sound state frame meaning rooted op dest left right x y result
      leftRead rightRead computed admitted
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot => cases admitted
  | slotSet slot source => cases admitted

/-- The actual open-Mir instruction relation lifts the same primitive result.
No call, address, floating-point, load, store or faulting case is asserted. -/
theorem evalInstr_op_sound (calls : OpenCalls) (state : State) (frame frame' : Lir.Frame Nat)
    (memory memory' : Lir.Memory) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (op : Lir.Op Nat) (admitted : Admitted op)
    (executed : InstructionExec calls (.op op) frame memory frame' memory') :
    memory' = memory ∧ ∃ newMeaning,
      OpResult state ((evalInstr (.op op)).run state).2 frame' meaning newMeaning := by
  cases executed with
  | op actual => exact evalOp_sound state frame frame' memory memory' meaning rooted op admitted actual

end Silmaril.Compiler.Native.Optimize.Validation.Roots
