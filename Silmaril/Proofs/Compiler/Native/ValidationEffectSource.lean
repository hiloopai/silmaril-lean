module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Source.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Source
open Silmaril.Machine Silmaril.Compile
open Roots
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem safe_bind {α β : Type} (action : StateM State α) (next : α → StateM State β)
    (first : Safe action) (later : ∀ value, Safe (next value)) : Safe (action >>= next) := by
  intro state loads
  exact later (action.run state).1 (action.run state).2 (first state loads)

theorem safe_intern (raw : Expr) (nonload : ∀ events, EventReferencesBelow events raw) : Safe (intern raw) := by
  intro state loads
  rw [(Intern.frame state raw).2.2]
  exact intern_loadsScoped state raw state.effects.size loads (nonload _)

theorem safe_readReg (reg : Nat) : Safe (readReg reg) := by
  intro state loads
  rw [Candidate.readReg_run]
  split
  · exact loads
  · exact safe_intern (.input reg) (fun _ => trivial) state loads

theorem safe_readSlot (slot : Nat) : Safe (readSlot slot) := by
  intro state loads
  rw [Candidate.readSlot_run]
  split
  · exact loads
  · exact safe_intern (.slot slot) (fun _ => trivial) state loads

theorem safe_writeReg (dest index : Nat) : Safe (writeReg dest index) := fun _ loads => loads

theorem safe_writeSlot (slot index : Nat) : Safe (writeSlot slot index) := fun _ loads => loads

/-- Frozen pure/slot source steps retain load-event scoping syntactically;
this does not require all incoming partial frame values to be defined. -/
theorem safe_pure_op (operation : Lir.Op Nat) (admitted : Slots.AdmittedOp operation) : Safe (evalOp operation) := by
  cases operation with
  | const dest word => exact safe_bind _ _ (safe_intern (.const word) (fun _ => trivial)) (fun index => safe_writeReg dest index)
  | move dest source => exact safe_bind _ _ (safe_readReg source) (fun index => safe_writeReg dest index)
  | unary op dest source =>
    exact safe_bind _ _ (safe_readReg source) (fun index =>
      safe_bind _ _ (safe_intern (.unary op index) (fun _ => trivial)) (fun output => safe_writeReg dest output))
  | binary op dest left right =>
    change Mir.DeadCode.faults op = false at admitted
    simp only [evalOp, admitted, Bool.false_eq_true, ↓reduceIte]
    exact safe_bind _ _ (safe_readReg left) (fun a => safe_bind _ _ (safe_readReg right) (fun b =>
      safe_bind _ _ (safe_intern (.binary op a b) (fun _ => trivial)) (fun output => safe_writeReg dest output)))
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot => exact safe_bind _ _ (safe_readSlot slot) (fun index => safe_writeReg dest index)
  | slotSet slot source => exact safe_bind _ _ (safe_readReg source) (fun index => safe_writeSlot slot index)

theorem pure_op_result (state : State) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning)
    (loads : LoadsScoped state.nodes state.effects.size) (operation : Lir.Op Nat) (admitted : Slots.AdmittedOp operation)
    (executed : operation.exec frame memory = some (final, finalMemory)) :
    finalMemory = memory ∧ ∃ newMeaning,
      Result state ((evalOp operation).run state).2 final meaning newMeaning ∧
      ((evalOp operation).run state).2.effects = state.effects ∧
      newMeaning.load = meaning.load := by
  obtain ⟨sameMemory, newMeaning, actual, totalAfter⟩ := Slots.Source.evalOp_sound state frame final memory finalMemory
    meaning rooted total operation admitted executed
  exact ⟨sameMemory, newMeaning, ⟨actual.rooted, totalAfter, safe_pure_op operation admitted state loads,
    prefix_of_extends actual.extension _, actual.grows⟩, actual.effects, actual.extension.load⟩

/-- A source store reads actual partial operands, records its actual symbolic
event, and retains rooted total DAG meaning while actual memory changes. -/
theorem store_result (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning)
    (loads : LoadsScoped state.nodes state.effects.size) (width : Lir.Width) (base offset source : Nat)
    (address word : Lir.Word) (baseRead : frame.get base = some address) (sourceRead : frame.get source = some word)
    (memory finalMemory : Lir.Memory) (stored : memory.store width (address.toNat + offset) word = some finalMemory) :
    ∃ newMeaning event,
      Result state ((evalOp (.store width base offset source)).run state).2 frame meaning newMeaning ∧
      ((evalOp (.store width base offset source)).run state).2.effects = state.effects.push event ∧
      EffectReferencesBelow ((evalOp (.store width base offset source)).run state).2.nodes.size event ∧
      newMeaning.load = meaning.load ∧
      (∀ width ext base offset, event ≠ .load width ext base offset) ∧
      runEffects newMeaning [event] memory = some ([none], finalMemory) := by
  let first := (readReg base).run state
  let second := (readReg source).run first.2
  let event : Effect := .store width first.1 offset second.1
  obtain ⟨firstMeaning, firstRead, firstTotal⟩ := Total.readReg_sound state frame meaning rooted total base address baseRead
  obtain ⟨newMeaning, secondRead, finalTotal⟩ :=
    Total.readReg_sound first.2 frame firstMeaning firstRead.rooted firstTotal source word sourceRead
  have actual : (evalOp (.store width base offset source)).run state =
      ((), { second.2 with effects := second.2.effects.push event }) := rfl
  have firstBound : first.1 < second.2.nodes.size := Nat.lt_of_lt_of_le firstRead.bounded secondRead.grows
  have firstSelected : newMeaning.value first.1 = some address :=
    (secondRead.extension.values first.1 firstRead.bounded).trans firstRead.selected
  have secondSelected : newMeaning.value second.1 = some word := secondRead.selected
  have combined : ReadResult state second.2 frame (some word) second.1 meaning newMeaning := firstRead.trans secondRead
  have middleLoads : LoadsScoped second.2.nodes second.2.effects.size :=
    safe_readReg source first.2 (safe_readReg base state loads)
  refine ⟨newMeaning, event, ?_, ?_, ?_, combined.extension.load, ?_, ?_⟩
  · rw [actual]
    exact ⟨⟨secondRead.rooted.wellScoped, secondRead.rooted.coherent, secondRead.rooted.regsBounded,
        secondRead.rooted.slotsBounded, secondRead.rooted.regs, secondRead.rooted.slots⟩,
      finalTotal, loadsScoped_mono middleLoads (by simp), prefix_of_extends combined.extension _, combined.grows⟩
  · rw [actual, combined.effects]
  · rw [actual]
    exact ⟨firstBound, secondRead.bounded⟩
  · intro loadWidth loadExt loadBase loadOffset impossible
    have impossibleShape : Effect.store width first.1 offset second.1 = .load loadWidth loadExt loadBase loadOffset := impossible
    cases impossibleShape
  · change (([event].mapM (concreteEffect newMeaning)).bind fun events => runEvents events memory) = _
    have concrete : concreteEffect newMeaning event = some (.store width (address.toNat + offset) word) := by
      simp only [event, concreteEffect, firstSelected, secondSelected, Option.bind_some, Option.map_some]
    simp only [List.mapM_cons, List.mapM_nil, concrete]
    apply runEvents_singleton
    simp only [Event.exec, stored, Option.map_some]


/-- Successful source faulting arithmetic records the actual ordered event
before interning the actual successful binary result. -/
theorem faulting_result (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning)
    (loads : LoadsScoped state.nodes state.effects.size) (op : Lir.Binop) (dest left right : Nat)
    (x y word : Lir.Word) (leftRead : frame.get left = some x) (rightRead : frame.get right = some y)
    (computed : op.eval x y = some word) (faulting : Mir.DeadCode.faults op = true) (memory : Lir.Memory) :
    ∃ newMeaning event,
      Result state ((evalOp (.binary op dest left right)).run state).2 (frame.set dest word) meaning newMeaning ∧
      ((evalOp (.binary op dest left right)).run state).2.effects = state.effects.push event ∧
      EffectReferencesBelow ((evalOp (.binary op dest left right)).run state).2.nodes.size event ∧
      newMeaning.load = meaning.load ∧
      (∀ width ext base offset, event ≠ .load width ext base offset) ∧
      runEffects newMeaning [event] memory = some ([some word], memory) := by
  let first := (readReg left).run state
  let second := (readReg right).run first.2
  let event : Effect := .faulting op first.1 second.1
  let recorded := (effect event).run second.2
  obtain ⟨firstMeaning, firstRead, firstTotal⟩ := Total.readReg_sound state frame meaning rooted total left x leftRead
  obtain ⟨secondMeaning, secondRead, secondTotal⟩ :=
    Total.readReg_sound first.2 frame firstMeaning firstRead.rooted firstTotal right y rightRead
  have firstBound : first.1 < second.2.nodes.size := Nat.lt_of_lt_of_le firstRead.bounded secondRead.grows
  have firstSelected : secondMeaning.value first.1 = some x :=
    (secondRead.extension.values first.1 firstRead.bounded).trans firstRead.selected
  have secondSelected : secondMeaning.value second.1 = some y := secondRead.selected
  have recordedActual : recorded = (second.2.effects.size, { second.2 with effects := second.2.effects.push event }) := rfl
  have recordedRooted : Rooted recorded.2 frame secondMeaning :=
    ⟨secondRead.rooted.wellScoped, secondRead.rooted.coherent, secondRead.rooted.regsBounded,
      secondRead.rooted.slotsBounded, secondRead.rooted.regs, secondRead.rooted.slots⟩
  have rawComputed : (Expr.binary op first.1 second.1).eval secondMeaning = some word := by
    simp only [Expr.eval, firstSelected, secondSelected, Option.bind_some, computed]
  obtain ⟨newMeaning, actualIntern, finalTotal⟩ := Total.intern_sound recorded.2 frame secondMeaning recordedRooted
    secondTotal (.binary op first.1 second.1) ⟨firstBound, secondRead.bounded⟩ word rawComputed
  have actual : (evalOp (.binary op dest left right)).run state =
      (writeReg dest ((intern (.binary op first.1 second.1)).run recorded.2).1).run
        ((intern (.binary op first.1 second.1)).run recorded.2).2 := by
    simp only [evalOp, faulting, ↓reduceIte]
    rfl
  have combinedReads : ReadResult state second.2 frame (some y) second.1 meaning secondMeaning := firstRead.trans secondRead
  have extension : Extends state.nodes.size meaning newMeaning :=
    combinedReads.extension.trans actualIntern.extension combinedReads.grows
  have readLoads : LoadsScoped second.2.nodes second.2.effects.size :=
    safe_readReg right first.2 (safe_readReg left state loads)
  have recordedLoads : LoadsScoped recorded.2.nodes recorded.2.effects.size := by
    rw [recordedActual]
    exact loadsScoped_mono readLoads (by simp)
  have finalLoads := intern_loadsScoped recorded.2 (.binary op first.1 second.1) recorded.2.effects.size recordedLoads trivial
  have leftFinal : newMeaning.value first.1 = some x :=
    (actualIntern.extension.values first.1 firstBound).trans firstSelected
  have rightFinal : newMeaning.value second.1 = some y :=
    (actualIntern.extension.values second.1 secondRead.bounded).trans secondRead.selected
  refine ⟨newMeaning, event, ?_, ?_, ?_, extension.load, ?_, ?_⟩
  · rw [actual]
    refine ⟨writeReg_rooted _ frame newMeaning actualIntern.rooted dest _ word actualIntern.bounded actualIntern.selected,
      finalTotal, ?_, prefix_of_extends extension _, combinedReads.grows.trans actualIntern.grows⟩
    change LoadsScoped ((intern (.binary op first.1 second.1)).run recorded.2).2.nodes
      ((intern (.binary op first.1 second.1)).run recorded.2).2.effects.size
    rw [actualIntern.effects]
    exact finalLoads
  · rw [actual]
    change ((intern (.binary op first.1 second.1)).run recorded.2).2.effects = _
    rw [actualIntern.effects]
    change second.2.effects.push event = _
    rw [combinedReads.effects]
  · rw [actual]
    exact ⟨Nat.lt_of_lt_of_le firstBound actualIntern.grows,
      Nat.lt_of_lt_of_le secondRead.bounded actualIntern.grows⟩
  · intro loadWidth loadExt loadBase loadOffset impossible
    have impossibleShape : Effect.faulting op first.1 second.1 = .load loadWidth loadExt loadBase loadOffset := impossible
    cases impossibleShape
  · change (([event].mapM (concreteEffect newMeaning)).bind fun events => runEvents events memory) = _
    have concrete : concreteEffect newMeaning event = some (.faulting op x y) := by
      simp only [event, concreteEffect, leftFinal, rightFinal, Option.bind_some, Option.map_some]
    simp only [List.mapM_cons, List.mapM_nil, concrete]
    apply runEvents_singleton
    simp only [Event.exec, computed, Option.map_some]


/-- The frozen actual source load theorem supplies the same common result and
its actual effect operand bound for source trace composition. -/
theorem load_result (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (loads : LoadsScoped state.nodes state.effects.size)
    (width : Lir.Width) (ext : Lir.Ext) (dest base offset : Nat) (address word : Lir.Word)
    (baseRead : frame.get base = some address)
    (loaded : memory.load width ext (address.toNat + offset) = some word) :
    ∃ newMeaning event,
      Result state ((evalOp (.load width ext dest base offset)).run state).2
        (frame.set dest word) meaning newMeaning ∧
      ((evalOp (.load width ext dest base offset)).run state).2.effects = state.effects.push event ∧
      EffectReferencesBelow ((evalOp (.load width ext dest base offset)).run state).2.nodes.size event ∧
      newMeaning.load state.effects.size = some word ∧
      runEffects newMeaning [event] memory = some ([some word], memory) := by
  obtain ⟨newMeaning, actual, effects, currentLoad, replay⟩ := Effects.source_load state frame memory meaning rooted total loads
    width ext dest base offset address word baseRead loaded
  let read := (readReg base).run state
  let event : Effect := .load width ext read.1 offset
  let recorded := (effect event).run read.2
  obtain ⟨readMeaning, actualRead, readTotal⟩ := Total.readReg_sound state frame meaning rooted total base address baseRead
  have grows : read.2.nodes.size ≤ ((evalOp (.load width ext dest base offset)).run state).2.nodes.size :=
    (Candidate.growing_intern (.load recorded.1) recorded.2).grows
  exact ⟨newMeaning, event, ⟨actual.rooted, actual.total, actual.loads, actual.extension, actual.grows⟩,
    effects, Nat.lt_of_lt_of_le actualRead.bounded grows, currentLoad, replay⟩

theorem effectReferences_mono {small large : Nat} {event : Effect}
    (references : EffectReferencesBelow small event) (bound : small ≤ large) :
    EffectReferencesBelow large event := by
  cases event with
  | load width ext base offset => exact Nat.lt_of_lt_of_le references bound
  | store width base offset source => exact ⟨Nat.lt_of_lt_of_le references.1 bound, Nat.lt_of_lt_of_le references.2 bound⟩
  | faulting op left right => exact ⟨Nat.lt_of_lt_of_le references.1 bound, Nat.lt_of_lt_of_le references.2 bound⟩
  | call symbol args results => exact fun index member => Nat.lt_of_lt_of_le (references index member) bound
  | indirect target args results =>
    exact ⟨Nat.lt_of_lt_of_le references.1 bound, fun index member => Nat.lt_of_lt_of_le (references.2 index member) bound⟩

theorem runEffects_append (meaning : Interpretation) (first last : List Effect)
    (memory middle final : Lir.Memory) (firstWords lastWords : List (Option Lir.Word))
    (earlier : runEffects meaning first memory = some (firstWords, middle))
    (later : runEffects meaning last middle = some (lastWords, final)) :
    runEffects meaning (first ++ last) memory = some (firstWords ++ lastWords, final) := by
  obtain ⟨firstEvents, firstConcrete, firstExec⟩ := Option.bind_eq_some_iff.mp earlier
  obtain ⟨lastEvents, lastConcrete, lastExec⟩ := Option.bind_eq_some_iff.mp later
  have fullConcrete : (first ++ last).mapM (concreteEffect meaning) = some (firstEvents ++ lastEvents) := by
    rw [List.mapM_append, firstConcrete, lastConcrete]
    rfl
  change ((first ++ last).mapM (concreteEffect meaning)).bind _ = _
  rw [fullConcrete, Option.bind_some]
  exact runEvents_append firstEvents lastEvents memory middle final firstWords lastWords firstExec lastExec

theorem initial_invariant (frame : Lir.Frame Nat) (memory : Lir.Memory) :
    Invariant frame memory {} frame memory [] (Total.initialMeaning frame) := by
  refine ⟨Total.initial_rooted frame, Total.empty_total _, ?_, ?_, .refl _ _ _, rfl, rfl, ?_⟩
  · intro index expression found
    simp at found
  · intro event member
    cases member
  · intro event width ext base offset found
    simp at found

/-- A real initial partial frame supports an independently supplied fixed
address interpretation; the actual event trace starts empty. -/
theorem initial_invariant_with (address : String → Nat → Option Lir.Word)
    (frame : Lir.Frame Nat) (memory : Lir.Memory) :
    InvariantWith address frame memory {} frame memory [] (Leaf.initialMeaning frame address) := by
  refine ⟨Leaf.initial_rooted frame address, Total.empty_total _, ?_, ?_, .refl _ _ _, rfl, rfl, ?_⟩
  · intro index expression found
    simp at found
  · intro event member
    cases member
  · intro event width ext base offset found
    simp at found

/-- A real no-event source transition composes with the accumulated actual
source memory trace, preserving all earlier real load results. -/
theorem invariant_pure {address : String → Nat → Option Lir.Word} {initialFrame frame final : Lir.Frame Nat} {initialMemory memory : Lir.Memory}
    {before after : State} {words : List (Option Lir.Word)} {meaning newMeaning : Interpretation}
    (invariant : InvariantWith address initialFrame initialMemory before frame memory words meaning)
    (result : Result before after final meaning newMeaning) (effects : after.effects = before.effects)
    (loadSame : newMeaning.load = meaning.load) :
    InvariantWith address initialFrame initialMemory after final memory words newMeaning := by
  refine ⟨result.rooted, result.total, result.loads, ?_, ?_, ?_, ?_, ?_⟩
  · intro event member
    rw [effects] at member
    exact effectReferences_mono (invariant.effects event member) result.grows
  · exact invariant.inputs.trans result.extension (Nat.zero_le _) (Nat.zero_le _)
  · rw [effects, runEffects_preserved result.extension before.effects.toList invariant.effects]
    exact invariant.executed
  · rw [effects]
    exact invariant.count
  · intro event width ext base offset found
    rw [effects] at found
    rw [loadSame]
    exact invariant.loadResults event width ext base offset found

/-- Append one actual source event to the accumulated semantic trace. Event
results and exact memory are real execution facts, not checker hypotheses. -/
theorem invariant_event {address : String → Nat → Option Lir.Word} {initialFrame frame final : Lir.Frame Nat} {initialMemory memory finalMemory : Lir.Memory}
    {before after : State} {words : List (Option Lir.Word)} {meaning newMeaning : Interpretation}
    (invariant : InvariantWith address initialFrame initialMemory before frame memory words meaning)
    (result : Result before after final meaning newMeaning) (event : Effect) (word : Option Lir.Word)
    (effects : after.effects = before.effects.push event)
    (references : EffectReferencesBelow after.nodes.size event)
    (newLoad : ∀ width ext base offset, event = .load width ext base offset → newMeaning.load before.effects.size = word)
    (executed : runEffects newMeaning [event] memory = some ([word], finalMemory)) :
    InvariantWith address initialFrame initialMemory after final finalMemory (words ++ [word]) newMeaning := by
  refine ⟨result.rooted, result.total, result.loads, ?_, ?_, ?_, ?_, ?_⟩
  · intro other member
    have appendedMember : other ∈ before.effects.toList ++ [event] := by simpa only [effects, Array.toList_push] using member
    rcases List.mem_append.mp appendedMember with old | current
    · exact effectReferences_mono (invariant.effects other old) result.grows
    · have same : other = event := List.mem_singleton.mp current
      exact same ▸ references
  · exact invariant.inputs.trans result.extension (Nat.zero_le _) (Nat.zero_le _)
  · rw [effects, Array.toList_push]
    have earlier : runEffects newMeaning before.effects.toList initialMemory = some (words, memory) := by
      rw [runEffects_preserved result.extension before.effects.toList invariant.effects]
      exact invariant.executed
    exact runEffects_append newMeaning before.effects.toList [event] initialMemory memory finalMemory words [word] earlier executed
  · simp only [List.length_append, List.length_singleton, effects, Array.size_push, invariant.count]
  · show LoadResults after.effects (words ++ [word]) newMeaning
    intro index width ext base offset found
    have appendedAt : (before.effects.push event)[index]? = some (.load width ext base offset) := by
      simpa only [effects] using found
    by_cases last : index = before.effects.size
    · have same : event = .load width ext base offset := by simpa [last] using appendedAt
      rw [last, newLoad width ext base offset same]
      simp [invariant.count]
    · have old : before.effects[index]? = some (.load width ext base offset) := by
        simpa [Array.getElem?_push, last] using appendedAt
      have bounded : index < before.effects.size := (Array.getElem?_eq_some_iff.mp old).1
      rw [result.extension.load index bounded, invariant.loadResults index width ext base offset old]
      have wordBound : index < words.length := by rw [invariant.count]; exact bounded
      simp [List.getElem?_append, wordBound]


/-- Existing pure/slot source execution composes into the full source memory
trace without changing any prior real load result. -/
theorem pure_op_invariant {address : String → Nat → Option Lir.Word} (initialFrame frame final : Lir.Frame Nat) (initialMemory memory finalMemory : Lir.Memory)
    (state : State) (words : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : InvariantWith address initialFrame initialMemory state frame memory words meaning)
    (operation : Lir.Op Nat) (admitted : Slots.AdmittedOp operation)
    (executed : operation.exec frame memory = some (final, finalMemory)) :
    ∃ newMeaning newWords, InvariantWith address initialFrame initialMemory ((evalOp operation).run state).2 final finalMemory newWords newMeaning := by
  obtain ⟨sameMemory, newMeaning, result, effects, loadSame⟩ := pure_op_result state frame final memory finalMemory
    meaning invariant.rooted invariant.total invariant.loads operation admitted executed
  subst finalMemory
  exact ⟨newMeaning, words, invariant_pure invariant result effects loadSame⟩

/-- Every actual successful source primitive derives its symbolic state,
actual ordered effect results and exact final memory. Faulting arithmetic is
handled from its actual successful evaluation, never assumed total. -/
theorem evalOp_invariant {address : String → Nat → Option Lir.Word} (initialFrame frame final : Lir.Frame Nat) (initialMemory memory finalMemory : Lir.Memory)
    (state : State) (words : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : InvariantWith address initialFrame initialMemory state frame memory words meaning)
    (operation : Lir.Op Nat) (executed : operation.exec frame memory = some (final, finalMemory)) :
    ∃ newMeaning newWords, InvariantWith address initialFrame initialMemory ((evalOp operation).run state).2 final finalMemory newWords newMeaning := by
  cases operation with
  | const dest word => exact pure_op_invariant initialFrame frame final initialMemory memory finalMemory state words meaning invariant _ trivial executed
  | move dest source => exact pure_op_invariant initialFrame frame final initialMemory memory finalMemory state words meaning invariant _ trivial executed
  | unary op dest source => exact pure_op_invariant initialFrame frame final initialMemory memory finalMemory state words meaning invariant _ trivial executed
  | binary op dest left right =>
    show ∃ newMeaning newWords, InvariantWith address initialFrame initialMemory
      ((evalOp (.binary op dest left right)).run state).2 final finalMemory newWords newMeaning
    cases faulting : Mir.DeadCode.faults op with
    | false => exact pure_op_invariant initialFrame frame final initialMemory memory finalMemory state words meaning invariant _ faulting executed
    | true =>
      show ∃ newMeaning newWords, InvariantWith address initialFrame initialMemory
        ((evalOp (.binary op dest left right)).run state).2 final finalMemory newWords newMeaning
      obtain ⟨x, leftRead, y, rightRead, word, computed, output⟩ :
          ∃ x, frame.get left = some x ∧ ∃ y, frame.get right = some y ∧
            ∃ word, op.eval x y = some word ∧ (frame.set dest word = final ∧ memory = finalMemory) := by
        simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
      obtain ⟨newMeaning, event, result, effects, references, loadSame, noLoad, replay⟩ := faulting_result state frame meaning
        invariant.rooted invariant.total invariant.loads op dest left right x y word leftRead rightRead computed faulting memory
      rw [← output.1, ← output.2]
      refine ⟨newMeaning, words ++ [some word], invariant_event invariant result event (some word) effects references ?_ replay⟩
      intro width ext base offset impossible
      exact False.elim (noLoad width ext base offset impossible)
  | load width ext dest base offset =>
    show ∃ newMeaning newWords, InvariantWith address initialFrame initialMemory
      ((evalOp (.load width ext dest base offset)).run state).2 final finalMemory newWords newMeaning
    obtain ⟨address, read, word, loaded, output⟩ :
        ∃ address, frame.get base = some address ∧ ∃ word,
          memory.load width ext (address.toNat + offset) = some word ∧
          (frame.set dest word = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨newMeaning, event, result, effects, references, currentLoad, replay⟩ := load_result state frame memory meaning
      invariant.rooted invariant.total invariant.loads width ext dest base offset address word read loaded
    rw [← output.1, ← output.2]
    exact ⟨newMeaning, words ++ [some word], invariant_event invariant result event (some word) effects references
      (fun _ _ _ _ _ => currentLoad) replay⟩
  | store width base offset source =>
    show ∃ newMeaning newWords, InvariantWith address initialFrame initialMemory
      ((evalOp (.store width base offset source)).run state).2 final finalMemory newWords newMeaning
    obtain ⟨address, baseRead, word, sourceRead, after, stored, output⟩ :
        ∃ address, frame.get base = some address ∧ ∃ word, frame.get source = some word ∧
          ∃ after, memory.store width (address.toNat + offset) word = some after ∧
          (frame = final ∧ after = finalMemory) := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨newMeaning, event, result, effects, references, loadSame, noLoad, replay⟩ := store_result state frame meaning
      invariant.rooted invariant.total invariant.loads width base offset source address word baseRead sourceRead memory after stored
    rw [← output.1, ← output.2]
    refine ⟨newMeaning, words ++ [none], invariant_event invariant result event none effects references ?_ replay⟩
    intro width ext base offset impossible
    exact False.elim (noLoad width ext base offset impossible)
  | slotGet dest slot => exact pure_op_invariant initialFrame frame final initialMemory memory finalMemory state words meaning invariant _ trivial executed
  | slotSet slot source => exact pure_op_invariant initialFrame frame final initialMemory memory finalMemory state words meaning invariant _ trivial executed

/-- The full invariant composes along actual source instruction execution.
Only actual `.op` constructors are admitted; calls remain separate. -/
theorem instructions_invariant (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Effects.Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory final finalMemory)
    (initialFrame : Lir.Frame Nat) (initialMemory : Lir.Memory) (state : State)
    (words : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : Invariant initialFrame initialMemory state frame memory words meaning) :
    ∃ newMeaning newWords, Invariant initialFrame initialMemory ((instructions.forM evalInstr).run state).2
      final finalMemory newWords newMeaning := by
  induction executed generalizing state words meaning with
  | nil => exact ⟨meaning, words, invariant⟩
  | @cons instruction rest frame memory middle middleMemory final finalMemory first later ih =>
    show ∃ newMeaning newWords, Invariant initialFrame initialMemory
      (((instruction :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
    have headAdmitted : Effects.AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Effects.Admitted rest := fun i member => admitted i (by simp [member])
    cases instruction with
    | op operation =>
      show ∃ newMeaning newWords, Invariant initialFrame initialMemory
        (((Mir.Instr.op operation :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
      cases first with
      | op actual =>
        obtain ⟨middleMeaning, middleWords, actualResult⟩ := evalOp_invariant initialFrame frame middle
          initialMemory memory middleMemory state words meaning invariant operation actual
        obtain ⟨newMeaning, newWords, finalInvariant⟩ := ih tailAdmitted ((evalInstr (.op operation)).run state).2
          middleWords middleMeaning actualResult
        rw [Lists.forM_cons_run]
        exact ⟨newMeaning, newWords, finalInvariant⟩
    | fop op dest left right => cases headAdmitted
    | addr dest symbol offset => cases headAdmitted
    | call symbol args results => cases headAdmitted
    | callIndirect target args results => cases headAdmitted

/-- Start from the genuine empty checker state and actual partial input frame.
All real source load results, event operands and complete retained DAG values
are constructed from actual successful source execution. -/
theorem source_instructions_invariant (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Effects.Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory final finalMemory) :
    ∃ meaning words, Invariant frame memory ((instructions.forM evalInstr).run {}).2 final finalMemory words meaning :=
  instructions_invariant calls instructions frame final memory finalMemory admitted executed frame memory {} []
    (Total.initialMeaning frame) (initial_invariant frame memory)


theorem safe_pure {α : Type} (value : α) : Safe (pure value) := fun _ loads => loads

theorem safe_mapM {α β : Type} (action : α → StateM State β) (items : List α)
    (safe : ∀ item, Safe (action item)) : Safe (items.mapM action) := by
  induction items with
  | nil => exact safe_pure []
  | cons item rest ih =>
    simp only [List.mapM_cons]
    exact safe_bind _ _ (safe item) (fun value => safe_bind _ _ ih (fun values => safe_pure (value :: values)))

theorem safe_evalLoc (loc : Lir.Loc Nat) : Safe (evalLoc loc) := by
  cases loc with
  | reg reg => exact safe_readReg reg
  | slot slot => exact safe_readSlot slot

theorem safe_evalTerm (term : Lir.Term Nat) : Safe (evalTerm term) := by
  cases term with
  | jump label => exact safe_pure (Term.jump label)
  | branch reg yes no => exact safe_bind _ _ (safe_readReg reg) (fun index => safe_pure (Term.branch index yes no))
  | ret locs => exact safe_bind _ _ (safe_mapM evalLoc locs safe_evalLoc) (fun values => safe_pure (Term.ret values))
  | trap => exact safe_pure Term.trap

/-- Successful source primitive writes are defined even for loads and
faulting arithmetic. Memory stores retain the frame and define no register. -/
theorem op_written (operation : Lir.Op Nat) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (executed : operation.exec frame memory = some (final, finalMemory)) :
    SourceReads.Written frame final (Validation.defs (.op operation)) := by
  cases operation with
  | const dest word => exact Slots.Source.op_written _ frame final memory finalMemory trivial executed
  | move dest source => exact Slots.Source.op_written _ frame final memory finalMemory trivial executed
  | unary op dest source => exact Slots.Source.op_written _ frame final memory finalMemory trivial executed
  | binary op dest left right =>
    show SourceReads.Written frame final (Validation.defs (.op (.binary op dest left right)))
    obtain ⟨x, leftRead, y, rightRead, word, computed, output⟩ :
        ∃ x, frame.get left = some x ∧ ∃ y, frame.get right = some y ∧
          ∃ word, op.eval x y = some word ∧ (frame.set dest word = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    rw [← output.1]
    exact SourceReads.set_written frame dest word
  | load width ext dest base offset =>
    show SourceReads.Written frame final (Validation.defs (.op (.load width ext dest base offset)))
    obtain ⟨address, read, word, loaded, output⟩ :
        ∃ address, frame.get base = some address ∧ ∃ word,
          memory.load width ext (address.toNat + offset) = some word ∧
          (frame.set dest word = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    rw [← output.1]
    exact SourceReads.set_written frame dest word
  | store width base offset source =>
    show SourceReads.Written frame final (Validation.defs (.op (.store width base offset source)))
    obtain ⟨address, baseRead, word, sourceRead, after, stored, output⟩ :
        ∃ address, frame.get base = some address ∧ ∃ word, frame.get source = some word ∧
          ∃ after, memory.store width (address.toNat + offset) word = some after ∧
          (frame = final ∧ after = finalMemory) := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    rw [← output.1]
    exact ⟨fun _ prior => prior, fun _ member => nomatch member⟩
  | slotGet dest slot => exact Slots.Source.op_written _ frame final memory finalMemory trivial executed
  | slotSet slot source => exact Slots.Source.op_written _ frame final memory finalMemory trivial executed

theorem instruction_written (calls : OpenCalls) (instruction : Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Effects.AdmittedInstr instruction)
    (executed : InstructionExec calls instruction frame memory final finalMemory) :
    SourceReads.Written frame final (Validation.defs instruction) := by
  cases instruction with
  | op operation =>
    cases executed with
    | op actual => exact op_written operation frame final memory finalMemory actual
  | fop op dest left right => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem instructions_written (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Effects.Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory final finalMemory) :
    SourceReads.Written frame final (instructions.flatMap Validation.defs) := by
  induction executed with
  | nil => exact ⟨fun _ prior => prior, fun _ member => nomatch member⟩
  | @cons instruction rest frame memory middle middleMemory final finalMemory first later ih =>
    have firstWrite := instruction_written calls instruction frame middle memory middleMemory
      (admitted instruction (by simp)) first
    have laterWrite := ih (fun i member => admitted i (by simp [member]))
    exact SourceReads.written_trans firstWrite laterWrite

theorem observed_success (calls : OpenCalls) (block : Mir.Block)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Effects.Admitted block.instrs.toList)
    (executed : InstructionsExec calls block.instrs.toList frame memory final finalMemory) :
    ∃ values, (Acceptance.observedRegs block).mapM final.get = some values := by
  have written := instructions_written calls block.instrs.toList frame final memory finalMemory admitted executed
  apply SourceReads.defined_mapM
  intro reg member
  apply written.defined reg
  simpa only [Acceptance.observedRegs, List.mem_dedup] using member

/-- Finish any real source body invariant with its actual terminator and
observed reads. The external resolver is fixed throughout; the instruction
fragment and the construction of the body invariant are independent inputs. -/
theorem finish_block (address : String → Nat → Option Lir.Word)
    (block : Mir.Block) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (bodyMeaning : Interpretation) (bodyWords : List (Option Lir.Word))
    (bodyInvariant : InvariantWith address frame memory
      ((block.instrs.toList.forM evalInstr).run {}).2 final finalMemory bodyWords bodyMeaning)
    (executed : TermExec block.term final exit)
    (observed : List Nat) (values : List Lir.Word) (read : observed.mapM final.get = some values) :
    ∃ meaning, BlockResultWith address frame memory ((evalBlock block observed).run {}).2 final finalMemory bodyWords
      ((evalBlock block observed).run {}).1.1 ((evalBlock block observed).run {}).1.2 exit values meaning := by
  let body := (block.instrs.toList.forM evalInstr).run ({} : State)
  let term := (evalTerm block.term).run body.2
  let observations := (observed.mapM readReg).run term.2
  obtain ⟨termMeaning, termResult⟩ := Observation.evalTerm_sound block.term final exit executed body.2 bodyMeaning
    bodyInvariant.rooted bodyInvariant.total
  have termCommon : Result body.2 term.2 final bodyMeaning termMeaning :=
    ⟨termResult.result.rooted, termResult.total, safe_evalTerm block.term body.2 bodyInvariant.loads,
      prefix_of_extends termResult.result.extension _, termResult.result.grows⟩
  have termInvariant : InvariantWith address frame memory term.2 final finalMemory bodyWords termMeaning :=
    invariant_pure bodyInvariant termCommon termResult.result.effects termResult.result.extension.load
  obtain ⟨meaning, observedResult⟩ := Observation.readRegs_sound observed values final read term.2 termMeaning
    termResult.result.rooted termResult.total
  have observedCommon : Result term.2 observations.2 final termMeaning meaning :=
    ⟨observedResult.result.rooted, observedResult.total, safe_mapM readReg observed safe_readReg term.2 termInvariant.loads,
      prefix_of_extends observedResult.result.extension _, observedResult.result.grows⟩
  have finalInvariant : InvariantWith address frame memory observations.2 final finalMemory bodyWords meaning :=
    invariant_pure termInvariant observedCommon observedResult.result.effects observedResult.result.extension.load
  have termBounded : Observation.TermScoped observations.2.nodes.size term.1 :=
    Observation.termScoped_mono term.1 observedResult.result.grows termResult.wellScoped
  have decoded : Observation.termExit meaning term.1 = some exit :=
    (Observation.termExit_preserved term.1 observedResult.result.extension termResult.wellScoped).trans termResult.selected
  rw [Lists.evalBlock_run]
  exact ⟨meaning, finalInvariant, termBounded, decoded, observedResult.bounded, observedResult.selected⟩

/-- Actual source block execution constructs its complete effectful symbolic
meaning and real memory trace; term/observed evaluation adds no effects. -/
theorem block_with_reads (calls : OpenCalls) (block : Mir.Block) (frame final : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (admitted : Effects.Admitted block.instrs.toList)
    (executed : BlockExec calls block frame memory exit final finalMemory)
    (observed : List Nat) (values : List Lir.Word) (read : observed.mapM final.get = some values) :
    ∃ meaning words, BlockResult frame memory ((evalBlock block observed).run {}).2 final finalMemory words
      ((evalBlock block observed).run {}).1.1 ((evalBlock block observed).run {}).1.2 exit values meaning := by
  obtain ⟨bodyMeaning, bodyWords, bodyInvariant⟩ := source_instructions_invariant calls block.instrs.toList frame final
    memory finalMemory admitted executed.1
  obtain ⟨meaning, result⟩ := finish_block (fun _ _ => none) block frame final memory finalMemory exit
    bodyMeaning bodyWords bodyInvariant executed.2 observed values read
  exact ⟨meaning, bodyWords, result⟩

/-- No observed-read or abstract semantic premise: original register outputs
are defined by actual successful source writes, and the complete actual checker
source run obtains its real load map and exact ordered effect memory trace. -/
theorem source_block (calls : OpenCalls) (block : Mir.Block) (frame final : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (admitted : Effects.Admitted block.instrs.toList)
    (executed : BlockExec calls block frame memory exit final finalMemory) :
    ∃ meaning words values,
      (Acceptance.observedRegs block).mapM final.get = some values ∧
      BlockResult frame memory (Acceptance.sourceRun block).2 final finalMemory words
        (Acceptance.sourceRun block).1.1 (Acceptance.sourceRun block).1.2 exit values meaning := by
  obtain ⟨values, read⟩ := observed_success calls block frame final memory finalMemory admitted executed.1
  obtain ⟨meaning, words, result⟩ := block_with_reads calls block frame final memory finalMemory exit admitted executed
    (Acceptance.observedRegs block) values read
  exact ⟨meaning, words, values, read, result⟩

end Silmaril.Compiler.Native.Optimize.Validation.Effects.Source
