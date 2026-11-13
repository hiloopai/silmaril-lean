module

public import Silmaril.Compiler.Native.Optimize.Validation.Observation.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Observation
open Silmaril.Machine
open Roots
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem read_result {before after : State} {frame : Lir.Frame Nat} {expected : Option Lir.Word}
    {index : Nat} {oldMeaning newMeaning : Interpretation}
    (actual : ReadResult before after frame expected index oldMeaning newMeaning) :
    OpResult before after frame oldMeaning newMeaning :=
  ⟨actual.rooted, actual.extension, actual.grows, actual.effects⟩

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
    (rooted : Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning)
    (slot : Nat) (word : Lir.Word) (read : frame.slots slot = some word) :
    ∃ newMeaning, ReadResult state ((readSlot slot).run state).2 frame (some word)
      ((readSlot slot).run state).1 meaning newMeaning ∧
      Total.TotalNodes ((readSlot slot).run state).2.nodes newMeaning := by
  obtain ⟨newMeaning, actual⟩ := Roots.readSlot_sound state frame meaning rooted slot
  have selected : newMeaning.value ((readSlot slot).run state).1 = some word := actual.selected.trans read
  refine ⟨newMeaning, { actual with selected }, ?_⟩
  cases found : state.slots.find? (·.1 == slot) with
  | none =>
    have run : (readSlot slot).run state = (intern (.slot slot)).run state := by rw [readSlot_run, found]
    rw [run] at selected ⊢
    exact Total.intern_result_total state (.slot slot) word meaning newMeaning total actual.extension selected
  | some root =>
    rw [readSlot_run, found]
    intro index bounded
    obtain ⟨value, defined⟩ := total index bounded
    exact ⟨value, (actual.extension.values index bounded).trans defined⟩

theorem evalLoc_sound (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning)
    (location : Lir.Loc Nat) (word : Lir.Word) (read : frame.read location = some word) :
    ∃ newMeaning, ReadResult state ((evalLoc location).run state).2 frame (some word)
      ((evalLoc location).run state).1 meaning newMeaning ∧
      Total.TotalNodes ((evalLoc location).run state).2.nodes newMeaning := by
  cases location with
  | reg reg => exact Total.readReg_sound state frame meaning rooted total reg word read
  | slot slot => exact readSlot_sound state frame meaning rooted total slot word read

theorem mapM_cons_run {α : Type} (action : α → StateM State Nat) (key : α) (rest : List α) (state : State) :
    ((key :: rest).mapM action).run state =
      let first := (action key).run state
      let tail := (rest.mapM action).run first.2
      (first.1 :: tail.1, tail.2) := by
  rw [List.mapM_cons]
  rfl

private theorem mapM_values_cons {α : Type} (get : α → Option Lir.Word) (key : α)
    (rest : List α) (values : List Lir.Word) (read : (key :: rest).mapM get = some values) :
    ∃ word tail, get key = some word ∧ rest.mapM get = some tail ∧ values = word :: tail := by
  have sequence : (get key).bind (fun word => (rest.mapM get).bind
      (fun tail => some (word :: tail))) = some values := by simpa only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] using read
  obtain ⟨word, firstRead, restRead⟩ := Option.bind_eq_some_iff.mp sequence
  obtain ⟨tail, tailRead, same⟩ := Option.bind_eq_some_iff.mp restRead
  exact ⟨word, tail, firstRead, tailRead, (Option.some.inj same).symm⟩

theorem readRegs_sound (registers : List Nat) (values : List Lir.Word)
    (frame : Lir.Frame Nat) (read : registers.mapM frame.get = some values)
    (state : State) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) :
    ∃ newMeaning, ReadValues state ((registers.mapM readReg).run state).2 frame
      ((registers.mapM readReg).run state).1 values meaning newMeaning := by
  induction registers generalizing values state meaning with
  | nil =>
    have empty : values = [] := (Option.some.inj read).symm
    rw [empty]
    exact ⟨meaning, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, total, (fun _ member => nomatch member), rfl⟩
  | cons reg rest ih =>
    show ∃ newMeaning, ReadValues state (((reg :: rest).mapM readReg).run state).2 frame
      (((reg :: rest).mapM readReg).run state).1 values meaning newMeaning
    obtain ⟨word, tailValues, firstRead, tailRead, same⟩ := mapM_values_cons frame.get reg rest values read
    let first := (readReg reg).run state
    let tail := (rest.mapM readReg).run first.2
    obtain ⟨middleMeaning, actualRead, middleTotal⟩ := Total.readReg_sound state frame meaning rooted total reg word firstRead
    obtain ⟨newMeaning, actualTail⟩ := ih tailValues tailRead first.2 middleMeaning actualRead.rooted middleTotal
    have firstBound : first.1 < tail.2.nodes.size := Nat.lt_of_lt_of_le actualRead.bounded actualTail.result.grows
    have firstSelected : newMeaning.value first.1 = some word :=
      (actualTail.result.extension.values first.1 actualRead.bounded).trans actualRead.selected
    rw [mapM_cons_run, same]
    refine ⟨newMeaning, Lists.result_trans (read_result actualRead) actualTail.result, actualTail.total, ?_, ?_⟩
    · intro index member
      rcases List.mem_cons.mp member with equal | later
      · subst index
        exact firstBound
      · exact actualTail.bounded index later
    · have tailSelected : tail.1.mapM newMeaning.value = some tailValues := actualTail.selected
      change (first.1 :: tail.1).mapM newMeaning.value = some (word :: tailValues)
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, firstSelected,
        Option.bind_some, tailSelected]

theorem evalLocs_sound (locations : List (Lir.Loc Nat)) (values : List Lir.Word)
    (frame : Lir.Frame Nat) (read : frame.readAll locations = some values)
    (state : State) (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) :
    ∃ newMeaning, ReadValues state ((locations.mapM evalLoc).run state).2 frame
      ((locations.mapM evalLoc).run state).1 values meaning newMeaning := by
  induction locations generalizing values state meaning with
  | nil =>
    have empty : values = [] := (Option.some.inj read).symm
    rw [empty]
    exact ⟨meaning, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, total, (fun _ member => nomatch member), rfl⟩
  | cons location rest ih =>
    show ∃ newMeaning, ReadValues state (((location :: rest).mapM evalLoc).run state).2 frame
      (((location :: rest).mapM evalLoc).run state).1 values meaning newMeaning
    obtain ⟨word, tailValues, firstRead, tailRead, same⟩ := mapM_values_cons frame.read location rest values read
    let first := (evalLoc location).run state
    let tail := (rest.mapM evalLoc).run first.2
    obtain ⟨middleMeaning, actualRead, middleTotal⟩ := evalLoc_sound state frame meaning rooted total location word firstRead
    obtain ⟨newMeaning, actualTail⟩ := ih tailValues tailRead first.2 middleMeaning actualRead.rooted middleTotal
    have firstBound : first.1 < tail.2.nodes.size := Nat.lt_of_lt_of_le actualRead.bounded actualTail.result.grows
    have firstSelected : newMeaning.value first.1 = some word :=
      (actualTail.result.extension.values first.1 actualRead.bounded).trans actualRead.selected
    rw [mapM_cons_run, same]
    refine ⟨newMeaning, Lists.result_trans (read_result actualRead) actualTail.result, actualTail.total, ?_, ?_⟩
    · intro index member
      rcases List.mem_cons.mp member with equal | later
      · subst index
        exact firstBound
      · exact actualTail.bounded index later
    · have tailSelected : tail.1.mapM newMeaning.value = some tailValues := actualTail.selected
      change (first.1 :: tail.1).mapM newMeaning.value = some (word :: tailValues)
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, firstSelected,
        Option.bind_some, tailSelected]

theorem values_preserved (indices : List Nat) {bound : Nat} {oldMeaning newMeaning : Interpretation}
    (extension : Extends bound oldMeaning newMeaning) (bounded : ∀ index ∈ indices, index < bound) :
    indices.mapM newMeaning.value = indices.mapM oldMeaning.value := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    have first : newMeaning.value index = oldMeaning.value index := extension.values index (bounded index (by simp))
    have tail : rest.mapM newMeaning.value = rest.mapM oldMeaning.value := ih (fun other member => bounded other (by simp [member]))
    simp only [List.mapM_cons, first, tail]

theorem termScoped_mono (term : Term) {small large : Nat} (growth : small ≤ large)
    (bounded : TermScoped small term) : TermScoped large term := by
  cases term with
  | branch condition yes no => exact Nat.lt_of_lt_of_le bounded growth
  | ret indices => exact fun index member => Nat.lt_of_lt_of_le (bounded index member) growth
  | jump | trap => trivial

theorem termExit_preserved (term : Term) {bound : Nat} {oldMeaning newMeaning : Interpretation}
    (extension : Extends bound oldMeaning newMeaning) (bounded : TermScoped bound term) :
    termExit newMeaning term = termExit oldMeaning term := by
  cases term with
  | branch condition yes no => simp only [termExit, extension.values condition bounded]
  | ret indices => simp only [termExit, values_preserved indices extension bounded]
  | jump | trap => rfl

/-- Actual successful concrete terminator execution gives the same exit under
the partial symbolic decoder, using the actual evalTerm StateM result. -/
theorem evalTerm_sound (term : Lir.Term Nat) (frame : Lir.Frame Nat) (exit : BlockExit)
    (executed : TermExec term frame exit) (state : State) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning) :
    ∃ newMeaning, TermResult state ((evalTerm term).run state).2 frame
      ((evalTerm term).run state).1 exit meaning newMeaning := by
  cases executed with
  | jump => exact ⟨meaning, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, total, trivial, rfl⟩
  | @zero reg yes no source read =>
    obtain ⟨newMeaning, actual, totalAfter⟩ := Total.readReg_sound state frame meaning rooted total reg 0 read
    refine ⟨newMeaning, read_result actual, totalAfter, actual.bounded, ?_⟩
    change termExit newMeaning (.branch ((readReg reg).run state).1 yes no) = some (.jump no)
    simp [termExit, actual.selected]
  | @nonzero reg yes no source word read nonzero =>
    obtain ⟨newMeaning, actual, totalAfter⟩ := Total.readReg_sound state frame meaning rooted total reg word read
    refine ⟨newMeaning, read_result actual, totalAfter, actual.bounded, ?_⟩
    change termExit newMeaning (.branch ((readReg reg).run state).1 yes no) = some (.jump yes)
    simp only [termExit, actual.selected, Option.map_some, ite_eq_right nonzero]
  | @ret locations source values read =>
    obtain ⟨newMeaning, actual⟩ := evalLocs_sound locations values frame read state meaning rooted total
    refine ⟨newMeaning, actual.result, actual.total, actual.bounded, ?_⟩
    change termExit newMeaning (.ret ((locations.mapM evalLoc).run state).1) = some (.returned values)
    simp only [termExit, actual.selected, Option.map_some]
  | trap => exact ⟨meaning, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, total, trivial, rfl⟩

/-- Preserve actual source block evaluation order: instruction prefix, actual
terminator reads, then actual observed-register reads. Observed concrete read
success is an explicit source premise, not a checker or candidate hypothesis. -/
theorem block_sound (calls : OpenCalls) (block : Silmaril.Compile.Mir.Block)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block frame memory exit frame' memory')
    (admitted : Lists.Admitted block.instrs.toList) (observed : List Nat) (values : List Lir.Word)
    (read : observed.mapM frame'.get = some values) (state : State) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning) :
    memory' = memory ∧ ∃ newMeaning,
      BlockResult state ((evalBlock block observed).run state).2 frame'
        ((evalBlock block observed).run state).1.1 ((evalBlock block observed).run state).1.2
        exit values meaning newMeaning := by
  let body := (block.instrs.toList.forM evalInstr).run state
  let term := (evalTerm block.term).run body.2
  let observations := (observed.mapM readReg).run term.2
  obtain ⟨memorySame, bodyMeaning, bodyResult, bodyTotal⟩ := Total.instructions_sound calls block.instrs.toList
    frame frame' memory memory' executed.1 admitted state meaning rooted total
  obtain ⟨termMeaning, termResult⟩ := evalTerm_sound block.term frame' exit executed.2 body.2 bodyMeaning
    bodyResult.rooted bodyTotal
  obtain ⟨newMeaning, observedResult⟩ := readRegs_sound observed values frame' read term.2 termMeaning
    termResult.result.rooted termResult.total
  have common : OpResult state observations.2 frame' meaning newMeaning :=
    Lists.result_trans bodyResult (Lists.result_trans termResult.result observedResult.result)
  have scopedTerm : TermScoped observations.2.nodes.size term.1 :=
    termScoped_mono term.1 observedResult.result.grows termResult.wellScoped
  have decoded : termExit newMeaning term.1 = some exit :=
    (termExit_preserved term.1 observedResult.result.extension termResult.wellScoped).trans termResult.selected
  rw [Lists.evalBlock_run]
  exact ⟨memorySame, newMeaning, ⟨common, observedResult.total, scopedTerm, decoded⟩,
    observedResult.bounded, observedResult.selected⟩

/-- Construct the initial rooted/total interpretation from the actual partial
source frame and the genuine empty symbolic DAG before evaluating the block. -/
theorem source_block_sound (calls : OpenCalls) (block : Silmaril.Compile.Mir.Block)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls block frame memory exit frame' memory')
    (admitted : Lists.Admitted block.instrs.toList) (observed : List Nat) (values : List Lir.Word)
    (read : observed.mapM frame'.get = some values) :
    memory' = memory ∧ ∃ newMeaning,
      BlockResult {} ((evalBlock block observed).run {}).2 frame'
        ((evalBlock block observed).run {}).1.1 ((evalBlock block observed).run {}).1.2
        exit values (Total.initialMeaning frame) newMeaning :=
  block_sound calls block frame frame' memory memory' exit executed admitted observed values read {} (Total.initialMeaning frame)
    (Total.initial_rooted frame) (Total.empty_total _)

end Silmaril.Compiler.Native.Optimize.Validation.Observation
