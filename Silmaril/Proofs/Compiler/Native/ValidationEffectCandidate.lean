module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Candidate.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Candidate
open Silmaril.Machine Silmaril.Compile
open Roots
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem EffectPrefix.refl (effects : Array Effect) : EffectPrefix effects effects := ⟨[], by simp⟩

theorem EffectPrefix.trans {first middle last : Array Effect}
    (earlier : EffectPrefix first middle) (later : EffectPrefix middle last) : EffectPrefix first last := by
  obtain ⟨earlierSuffix, earlierEqual⟩ := earlier
  obtain ⟨laterSuffix, laterEqual⟩ := later
  exact ⟨earlierSuffix ++ laterSuffix, by rw [laterEqual, earlierEqual, List.append_assoc]⟩

theorem EffectPrefix.grows {before after : Array Effect} (earlier : EffectPrefix before after) :
    before.size ≤ after.size := by
  obtain ⟨suffix, actual⟩ := earlier
  have length : after.size = before.size + suffix.length := by
    simpa only [List.length_append, Array.length_toList] using congrArg List.length actual
  omega

theorem EffectPrefix.old {before after : Array Effect} (earlier : EffectPrefix before after)
    (index : Nat) (bounded : index < before.size) : after[index]? = before[index]? := by
  obtain ⟨suffix, actual⟩ := earlier
  rw [← Array.getElem?_toList, actual, List.getElem?_append_left (by simpa using bounded), Array.getElem?_toList]

theorem growing_pure {α : Type} (value : α) : EffectGrowing (pure value) := fun state => .refl state.effects

theorem growing_bind {α β : Type} (action : StateM State α) (next : α → StateM State β)
    (first : EffectGrowing action) (later : ∀ value, EffectGrowing (next value)) : EffectGrowing (action >>= next) := by
  intro state
  exact (first state).trans (later (action.run state).1 (action.run state).2)

theorem growing_intern (expression : Expr) : EffectGrowing (intern expression) := by
  intro state
  rw [(Intern.frame state expression).2.2]
  exact .refl state.effects

theorem growing_readReg (reg : Nat) : EffectGrowing (readReg reg) := by
  intro state
  rw [Validation.Candidate.readReg_run]
  split
  · exact .refl _
  · exact growing_intern (.input reg) state

theorem growing_readSlot (slot : Nat) : EffectGrowing (readSlot slot) := by
  intro state
  rw [Validation.Candidate.readSlot_run]
  split
  · exact .refl _
  · exact growing_intern (.slot slot) state

theorem growing_writeReg (dest index : Nat) : EffectGrowing (writeReg dest index) := fun state => .refl state.effects

theorem growing_writeSlot (slot index : Nat) : EffectGrowing (writeSlot slot index) := fun state => .refl state.effects

theorem growing_effect (event : Effect) : EffectGrowing (effect event) :=
  fun state => ⟨[event], by exact Array.toList_push (xs := state.effects) (x := event)⟩

theorem growing_discard (event : Effect) : EffectGrowing (discard (effect event)) :=
  growing_bind _ _ (growing_effect event) (fun _ => growing_pure ())

/-- The unchanged actual checker only appends effects, including all load,
store and faulting cases. No actual candidate execution is assumed. -/
theorem growing_evalOp (operation : Lir.Op Nat) : EffectGrowing (evalOp operation) := by
  cases operation with
  | const dest word => exact growing_bind _ _ (growing_intern (.const word)) (fun index => growing_writeReg dest index)
  | move dest source => exact growing_bind _ _ (growing_readReg source) (fun index => growing_writeReg dest index)
  | unary op dest source => exact growing_bind _ _ (growing_readReg source) (fun index =>
      growing_bind _ _ (growing_intern (.unary op index)) (fun output => growing_writeReg dest output))
  | binary op dest left right =>
    show EffectGrowing (evalOp (.binary op dest left right))
    apply growing_bind _ _ (growing_readReg left)
    intro a
    apply growing_bind _ _ (growing_readReg right)
    intro b
    cases Mir.DeadCode.faults op <;> simp only [↓reduceIte]
    · exact growing_bind _ _ (growing_intern (.binary op a b)) (fun output => growing_writeReg dest output)
    · exact growing_bind _ _ (growing_discard (.faulting op a b)) (fun _ =>
        growing_bind _ _ (growing_intern (.binary op a b)) (fun output => growing_writeReg dest output))
  | load width ext dest base offset =>
    exact growing_bind _ _ (growing_readReg base) (fun address =>
      growing_bind _ _ (growing_effect (.load width ext address offset)) (fun index =>
        growing_bind _ _ (growing_intern (.load index)) (fun output => growing_writeReg dest output)))
  | store width base offset source =>
    exact growing_bind _ _ (growing_readReg base) (fun address =>
      growing_bind _ _ (growing_readReg source) (fun index => growing_discard (.store width address offset index)))
  | slotGet dest slot => exact growing_bind _ _ (growing_readSlot slot) (fun index => growing_writeReg dest index)
  | slotSet slot source => exact growing_bind _ _ (growing_readReg source) (fun index => growing_writeSlot slot index)

theorem growing_evalInstr (instruction : Mir.Instr) (admitted : Effects.AdmittedInstr instruction) :
    EffectGrowing (evalInstr instruction) := by
  cases instruction with
  | op operation => exact growing_evalOp operation
  | fop op dest left right => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem growing_forM (instructions : List Mir.Instr) (admitted : Effects.Admitted instructions) :
    EffectGrowing (instructions.forM evalInstr) := by
  induction instructions with
  | nil => exact growing_pure ()
  | cons instruction rest ih =>
    intro state
    rw [Lists.forM_cons_run]
    exact (growing_evalInstr instruction (admitted instruction (by simp)) state).trans
      (ih (fun i member => admitted i (by simp [member])) ((evalInstr instruction).run state).2)

theorem growing_mapM {α β : Type} (action : α → StateM State β) (items : List α)
    (growing : ∀ item, EffectGrowing (action item)) : EffectGrowing (items.mapM action) := by
  induction items with
  | nil => exact growing_pure []
  | cons item rest ih =>
    simp only [List.mapM_cons]
    exact growing_bind _ _ (growing item) (fun value => growing_bind _ _ ih (fun values => growing_pure (value :: values)))

theorem growing_evalLoc (loc : Lir.Loc Nat) : EffectGrowing (evalLoc loc) := by
  cases loc with
  | reg reg => exact growing_readReg reg
  | slot slot => exact growing_readSlot slot

theorem growing_evalTerm (term : Lir.Term Nat) : EffectGrowing (evalTerm term) := by
  cases term with
  | jump label => exact growing_pure (Term.jump label)
  | branch reg yes no => exact growing_bind _ _ (growing_readReg reg) (fun index => growing_pure (Term.branch index yes no))
  | ret locs => exact growing_bind _ _ (growing_mapM evalLoc locs growing_evalLoc) (fun values => growing_pure (Term.ret values))
  | trap => exact growing_pure Term.trap

theorem growing_evalBlock (block : Mir.Block) (observed : List Nat)
    (admitted : Effects.Admitted block.instrs.toList) : EffectGrowing (evalBlock block observed) := by
  intro state
  rw [Lists.evalBlock_run]
  exact (growing_forM block.instrs.toList admitted state).trans
    ((growing_evalTerm block.term _).trans (growing_mapM readReg observed growing_readReg _))

/-- Relational decomposition of the actual partial symbolic event evaluator. -/
theorem runEffects_cons (meaning : Interpretation) (effect : Effect) (rest : List Effect) (memory : Lir.Memory) :
    runEffects meaning (effect :: rest) memory =
      (concreteEffect meaning effect).bind fun event => (event.exec memory).bind fun head =>
        (runEffects meaning rest head.2).map fun tail => (head.1 :: tail.1, tail.2) := by
  cases head : concreteEffect meaning effect with
  | none => simp [runEffects, List.mapM_cons, head]
  | some event =>
    cases tail : rest.mapM (concreteEffect meaning) with
    | none =>
      cases event.exec memory <;> simp [runEffects, List.mapM_cons, head, tail]
    | some events =>
      cases executed : event.exec memory <;> simp [runEffects, List.mapM_cons, head, tail, runEvents, executed]

/-- No extra event semantics: Replay is exactly the existing runEffects. -/
theorem Replay.run {meaning : Interpretation} {effects : List Effect} {memory final : Lir.Memory}
    {words : List (Option Lir.Word)} (replay : Replay meaning effects memory words final) :
    runEffects meaning effects memory = some (words, final) := by
  induction replay with
  | nil => rfl
  | cons effect rest event word words memory middle final concrete executed later ih =>
    rw [runEffects_cons, concrete, Option.bind_some, executed, Option.bind_some, ih, Option.map_some]

theorem Replay.of_run (meaning : Interpretation) (effects : List Effect) (memory final : Lir.Memory)
    (words : List (Option Lir.Word)) (executed : runEffects meaning effects memory = some (words, final)) :
    Replay meaning effects memory words final := by
  induction effects generalizing memory words with
  | nil =>
    have same : ([], memory) = (words, final) := Option.some.inj executed
    cases same
    constructor
  | cons effect rest ih =>
    rw [runEffects_cons] at executed
    obtain ⟨event, concrete, head, headExec, tail, tailExec, output⟩ :
        ∃ event, concreteEffect meaning effect = some event ∧ ∃ head, event.exec memory = some head ∧
          ∃ tail, runEffects meaning rest head.2 = some tail ∧ (head.1 :: tail.1, tail.2) = (words, final) := by
      simpa only [Option.bind_eq_some_iff, Option.map_eq_some_iff] using executed
    obtain ⟨word, middle⟩ := head
    obtain ⟨tailWords, tailMemory⟩ := tail
    have sameWords : word :: tailWords = words := congrArg Prod.fst output
    have sameMemory : tailMemory = final := congrArg Prod.snd output
    subst words
    subst tailMemory
    exact .cons effect rest event word tailWords memory middle final concrete headExec (ih middle tailWords tailExec)

theorem Replay.length {meaning : Interpretation} {effects : List Effect} {memory final : Lir.Memory}
    {words : List (Option Lir.Word)} (replay : Replay meaning effects memory words final) : words.length = effects.length := by
  induction replay with
  | nil => rfl
  | cons effect rest event word words memory middle final concrete executed later ih => simp only [List.length_cons, ih]

theorem Replay.unique {meaning : Interpretation} {effects : List Effect} {memory first last : Lir.Memory}
    {firstWords lastWords : List (Option Lir.Word)}
    (earlier : Replay meaning effects memory firstWords first) (later : Replay meaning effects memory lastWords last) :
    firstWords = lastWords ∧ first = last :=
  Prod.mk.inj (Option.some.inj (earlier.run.symm.trans later.run))

theorem Replay.split (meaning : Interpretation) (first last : List Effect)
    (memory final : Lir.Memory) (words : List (Option Lir.Word))
    (replay : Replay meaning (first ++ last) memory words final) :
    ∃ firstWords middle lastWords,
      Replay meaning first memory firstWords middle ∧ Replay meaning last middle lastWords final ∧
      words = firstWords ++ lastWords := by
  induction first generalizing memory words with
  | nil => exact ⟨[], memory, words, .nil memory, replay, rfl⟩
  | cons effect rest ih =>
    cases replay with
    | cons _ _ event word words memory middle final concrete executed later =>
      obtain ⟨firstWords, afterFirst, lastWords, earlier, suffix, output⟩ := ih middle words later
      exact ⟨word :: firstWords, afterFirst, lastWords,
        .cons effect rest event word firstWords memory middle afterFirst concrete executed earlier,
        suffix, by simp only [List.cons_append, output]⟩

theorem EffectPrefix.references {before after : Array Effect} (earlier : EffectPrefix before after)
    (bound : Nat) (references : ∀ event ∈ after.toList, EffectReferencesBelow bound event) :
    ∀ event ∈ before.toList, EffectReferencesBelow bound event := by
  obtain ⟨suffix, actual⟩ := earlier
  intro event member
  apply references event
  rw [actual]
  exact List.mem_append_left suffix member

/-- Determinism identifies the real current memory at a candidate effect
frontier and extracts the next actual source event and its ordered result. -/
theorem Replay.next (meaning : Interpretation) (before after : Array Effect) (effect : Effect)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (afterPrefix : EffectPrefix (before.push effect) after)
    (sourceRun : runEffects meaning after.toList initialMemory = some (sourceWords, finalMemory))
    (currentRun : runEffects meaning before.toList initialMemory = some (words, memory)) :
    ∃ event word nextMemory,
      concreteEffect meaning effect = some event ∧ event.exec memory = some (word, nextMemory) ∧
      sourceWords[before.size]? = some word ∧
      runEffects meaning (before.push effect).toList initialMemory = some (words ++ [word], nextMemory) := by
  obtain ⟨suffix, actual⟩ := afterPrefix
  have actualList : after.toList = before.toList ++ (effect :: suffix) := by
    simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using actual
  have sourceReplay : Replay meaning (before.toList ++ (effect :: suffix)) initialMemory sourceWords finalMemory := by
    rw [← actualList]
    exact Replay.of_run meaning after.toList initialMemory finalMemory sourceWords sourceRun
  obtain ⟨firstWords, middle, lastWords, earlier, later, output⟩ :=
    Replay.split meaning before.toList (effect :: suffix) initialMemory finalMemory sourceWords sourceReplay
  have equal : firstWords = words ∧ middle = memory :=
    earlier.unique (Replay.of_run meaning before.toList initialMemory memory words currentRun)
  obtain ⟨sameWords, sameMemory⟩ := equal
  rw [← sameWords, ← sameMemory]
  cases later with
  | cons _ _ event word restWords _ nextMemory _ concrete executed rest =>
    show ∃ event word nextMemory,
      concreteEffect meaning effect = some event ∧ event.exec middle = some (word, nextMemory) ∧
      sourceWords[before.size]? = some word ∧
      runEffects meaning (before.push effect).toList initialMemory = some (firstWords ++ [word], nextMemory)
    refine ⟨event, word, nextMemory, concrete, executed, ?_, ?_⟩
    · rw [output]
      have count : firstWords.length = before.size := by simpa only [Array.length_toList] using earlier.length
      rw [← count, List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_cons_zero]
    · rw [Array.toList_push]
      exact Source.runEffects_append meaning before.toList [effect] initialMemory middle nextMemory firstWords [word]
        earlier.run (Replay.run (.cons effect [] event word [] middle nextMemory nextMemory concrete executed (.nil nextMemory)))

/-- A candidate DAG extension preserves both the full real source trace and
the already consumed prefix; the full ghost load map remains fixed. -/
theorem Trace.extend {source state : State} {meaning newMeaning : Interpretation}
    {initialMemory memory finalMemory : Lir.Memory} {sourceWords words : List (Option Lir.Word)}
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (extension : Extends source.nodes.size meaning newMeaning) :
    Trace source state newMeaning initialMemory memory finalMemory sourceWords words := by
  have sourceScoped : ∀ event ∈ source.effects.toList, EffectReferencesBelow source.nodes.size event := trace.references
  have currentScoped := trace.prefixEffects.references source.nodes.size sourceScoped
  refine ⟨trace.prefixEffects, trace.references, ?_, ?_, ?_⟩
  · exact (runEffects_preserved (prefix_of_extends extension 0) source.effects.toList sourceScoped initialMemory).trans trace.sourceRun
  · exact (runEffects_preserved (prefix_of_extends extension 0) state.effects.toList currentScoped initialMemory).trans trace.currentRun
  · intro event width ext base offset found
    rw [extension.load]
    exact trace.loadResults event width ext base offset found

/-- The next successful candidate memory event comes from the accepted final
effect array and the actual current prefix memory, without an execution premise. -/
theorem Trace.next {source state : State} {meaning : Interpretation}
    {initialMemory memory finalMemory : Lir.Memory} {sourceWords words : List (Option Lir.Word)}
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (effect : Effect) (afterPrefix : EffectPrefix (state.effects.push effect) source.effects) :
    ∃ event word nextMemory,
      concreteEffect meaning effect = some event ∧ event.exec memory = some (word, nextMemory) ∧
      sourceWords[state.effects.size]? = some word ∧
      runEffects meaning (state.effects.push effect).toList initialMemory = some (words ++ [word], nextMemory) :=
  Replay.next meaning state.effects source.effects effect initialMemory memory finalMemory sourceWords words
    afterPrefix trace.sourceRun trace.currentRun

theorem extends_restrict {small large : Nat} {meaning newMeaning : Interpretation}
    (extension : Extends large meaning newMeaning) (bound : small ≤ large) : Extends small meaning newMeaning :=
  ⟨fun index bounded => extension.values index (Nat.lt_of_lt_of_le bounded bound),
    extension.input, extension.slot, extension.address, extension.load, extension.result⟩

theorem Trace.restate {source before after : State} {meaning : Interpretation}
    {initialMemory memory finalMemory : Lir.Memory} {sourceWords words : List (Option Lir.Word)}
    (trace : Trace source before meaning initialMemory memory finalMemory sourceWords words)
    (same : after.effects = before.effects) :
    Trace source after meaning initialMemory memory finalMemory sourceWords words := by
  exact ⟨by rw [same]; exact trace.prefixEffects, trace.references, trace.sourceRun,
    by rw [same]; exact trace.currentRun, trace.loadResults⟩

namespace Nodes
open Validation.Candidate

theorem effect (event : Effect) : Growing (Validation.effect event) := fun state => .refl state.nodes

theorem discard_effect (event : Effect) : Growing (discard (Validation.effect event)) :=
  Validation.Candidate.growing_bind _ _ (effect event) (fun _ => Validation.Candidate.growing_pure ())

theorem evalOp (operation : Lir.Op Nat) : Growing (Validation.evalOp operation) := by
  cases operation with
  | const dest word => exact Validation.Candidate.growing_evalOp _ trivial
  | move dest source => exact Validation.Candidate.growing_evalOp _ trivial
  | unary op dest source => exact Validation.Candidate.growing_evalOp _ trivial
  | binary op dest left right =>
    show Growing (Validation.evalOp (.binary op dest left right))
    apply Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_readReg left)
    intro a
    apply Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_readReg right)
    intro b
    cases Mir.DeadCode.faults op <;> simp only [↓reduceIte]
    · exact Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_intern (.binary op a b)) (fun output => Validation.Candidate.growing_writeReg dest output)
    · exact Validation.Candidate.growing_bind _ _ (discard_effect (.faulting op a b)) (fun _ =>
        Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_intern (.binary op a b)) (fun output => Validation.Candidate.growing_writeReg dest output))
  | load width ext dest base offset =>
    exact Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_readReg base) (fun address =>
      Validation.Candidate.growing_bind _ _ (effect (.load width ext address offset)) (fun index =>
        Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_intern (.load index)) (fun output => Validation.Candidate.growing_writeReg dest output)))
  | store width base offset source =>
    exact Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_readReg base) (fun address =>
      Validation.Candidate.growing_bind _ _ (Validation.Candidate.growing_readReg source) (fun index => discard_effect (.store width address offset index)))
  | slotGet dest slot => exact Slots.Candidate.growing_evalOp _ trivial
  | slotSet slot source => exact Slots.Candidate.growing_evalOp _ trivial

theorem evalInstr (instruction : Mir.Instr) (admitted : Effects.AdmittedInstr instruction) :
    Growing (Validation.evalInstr instruction) := by
  cases instruction with
  | op operation => exact evalOp operation
  | fop op dest left right => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem forM (instructions : List Mir.Instr) (admitted : Effects.Admitted instructions) :
    Growing (instructions.forM Validation.evalInstr) := by
  induction instructions with
  | nil => exact Validation.Candidate.growing_pure ()
  | cons instruction rest ih =>
    intro state
    rw [Lists.forM_cons_run]
    exact (evalInstr instruction (admitted instruction (by simp)) state).trans
      (ih (fun i member => admitted i (by simp [member])) ((Validation.evalInstr instruction).run state).2)

theorem evalBlock (block : Mir.Block) (observed : List Nat)
    (admitted : Effects.Admitted block.instrs.toList) : Growing (Validation.evalBlock block observed) := by
  intro state
  rw [Lists.evalBlock_run]
  exact (forM block.instrs.toList admitted state).trans
    ((Validation.Candidate.growing_evalTerm block.term _).trans (Validation.Candidate.growing_mapM readReg observed Validation.Candidate.growing_readReg _))

end Nodes

/-- Actual successful next loads give the real memory word and exactly the
source-derived fixed ghost value, indexed at the candidate effect frontier. -/
theorem Trace.next_load {source state : State} {meaning : Interpretation}
    {initialMemory memory finalMemory : Lir.Memory} {sourceWords words : List (Option Lir.Word)}
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (width : Lir.Width) (ext : Lir.Ext) (base offset : Nat) (address : Lir.Word)
    (selected : meaning.value base = some address)
    (afterPrefix : EffectPrefix (state.effects.push (.load width ext base offset)) source.effects) :
    ∃ word, memory.load width ext (address.toNat + offset) = some word ∧
      meaning.load state.effects.size = some word ∧
      runEffects meaning (state.effects.push (.load width ext base offset)).toList initialMemory =
        some (words ++ [some word], memory) := by
  obtain ⟨event, result, nextMemory, concrete, executed, output, accumulated⟩ :=
    trace.next (.load width ext base offset) afterPrefix
  have actualEvent : event = .load width ext (address.toNat + offset) := by
    simpa only [concreteEffect, selected, Option.map_some, Option.some.injEq] using concrete.symm
  subst event
  change ((memory.load width ext (address.toNat + offset)).map fun word => (some word, memory)) = _ at executed
  obtain ⟨word, loaded, equal⟩ := Option.map_eq_some_iff.mp executed
  have sameResult : some word = result := congrArg Prod.fst equal
  have sameMemory : memory = nextMemory := congrArg Prod.snd equal
  rw [← sameResult, ← sameMemory] at accumulated
  refine ⟨word, loaded, ?_, accumulated⟩
  have atIndex : source.effects[state.effects.size]? = some (.load width ext base offset) := by
    rw [afterPrefix.old state.effects.size (by simp)]
    simp
  rw [trace.loadResults state.effects.size width ext base offset atIndex, output, Option.getD_some, ← sameResult]

/-- Install the already-derived successful candidate prefix. This is used only
after `Trace.next` has recovered the actual real memory transition. -/
theorem Trace.advance {source before after : State} {meaning : Interpretation}
    {initialMemory memory finalMemory nextMemory : Lir.Memory}
    {sourceWords words nextWords : List (Option Lir.Word)}
    (trace : Trace source before meaning initialMemory memory finalMemory sourceWords words)
    (afterPrefix : EffectPrefix after.effects source.effects)
    (accumulated : runEffects meaning after.effects.toList initialMemory = some (nextWords, nextMemory)) :
    Trace source after meaning initialMemory nextMemory finalMemory sourceWords nextWords :=
  ⟨afterPrefix, trace.references, trace.sourceRun, accumulated, trace.loadResults⟩

/-- A load of the actual candidate executes from its actual current memory.
Its result comes from the fixed final source interpretation; no candidate
load-execution premise and no chosen load oracle is accepted. -/
theorem load_success (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (width : Lir.Width) (ext : Lir.Ext) (dest base offset : Nat)
    (guarded : Validation.Candidate.Guarded source.nodes.size
      ((evalOp (.load width ext dest base offset)).run state).2.nodes)
    (afterPrefix : EffectPrefix ((evalOp (.load width ext dest base offset)).run state).2.effects source.effects) :
    ∃ word newMeaning,
      (Lir.Op.load width ext dest base offset).exec frame memory = some (frame.set dest word, memory) ∧
      Result state ((evalOp (.load width ext dest base offset)).run state).2 (frame.set dest word) meaning newMeaning ∧
      Trace source ((evalOp (.load width ext dest base offset)).run state).2 newMeaning
        initialMemory memory finalMemory sourceWords (words ++ [some word]) := by
  let read := (readReg base).run state
  let event : Effect := .load width ext read.1 offset
  let recorded := (effect event).run read.2
  have actual : (evalOp (.load width ext dest base offset)).run state =
      (writeReg dest ((intern (.load recorded.1)).run recorded.2).1).run
        ((intern (.load recorded.1)).run recorded.2).2 := rfl
  have readPrefix : Validation.Candidate.Prefix read.2.nodes
      ((evalOp (.load width ext dest base offset)).run state).2.nodes := by
    rw [actual]
    exact Validation.Candidate.growing_intern (.load recorded.1) recorded.2
  obtain ⟨address, baseRead⟩ := Validation.Candidate.readReg_defined state frame meaning rooted total
    source.nodes.size old base (guarded.prefix readPrefix)
  obtain ⟨readMeaning, actualRead, readTotal⟩ :=
    Total.readReg_sound state frame meaning rooted total base address baseRead
  have readTrace : Trace source read.2 readMeaning initialMemory memory finalMemory sourceWords words :=
    (trace.extend (extends_restrict actualRead.extension old)).restate actualRead.effects
  have internFrame := Intern.frame recorded.2 (.load recorded.1)
  have effects : ((evalOp (.load width ext dest base offset)).run state).2.effects = state.effects.push event := by
    rw [actual]
    change ((intern (.load recorded.1)).run recorded.2).2.effects = _
    rw [internFrame.2.2]
    change read.2.effects.push event = _
    rw [actualRead.effects]
  have recordedPrefix : EffectPrefix (read.2.effects.push event) source.effects := by
    rw [actualRead.effects]
    exact effects ▸ afterPrefix
  obtain ⟨word, loaded, ghost, accumulated⟩ :=
    readTrace.next_load width ext read.1 offset address actualRead.selected recordedPrefix
  have recordedRooted : Rooted recorded.2 frame readMeaning :=
    ⟨actualRead.rooted.wellScoped, actualRead.rooted.coherent, actualRead.rooted.regsBounded,
      actualRead.rooted.slotsBounded, actualRead.rooted.regs, actualRead.rooted.slots⟩
  have rawComputed : (Expr.load recorded.1).eval readMeaning = some word := ghost
  obtain ⟨newMeaning, actualIntern, finalTotal⟩ := Total.intern_sound recorded.2 frame readMeaning recordedRooted
    readTotal (.load recorded.1) trivial word rawComputed
  have combined : Extends state.nodes.size meaning newMeaning :=
    actualRead.extension.trans actualIntern.extension actualRead.grows
  have finalRooted : Rooted ((evalOp (.load width ext dest base offset)).run state).2
      (frame.set dest word) newMeaning := by
    rw [actual]
    exact writeReg_rooted _ frame newMeaning actualIntern.rooted dest _ word actualIntern.bounded actualIntern.selected
  have finalTrace : Trace source ((evalOp (.load width ext dest base offset)).run state).2 readMeaning
      initialMemory memory finalMemory sourceWords (words ++ [some word]) := by
    apply readTrace.advance afterPrefix
    rw [effects, ← actualRead.effects]
    exact accumulated
  refine ⟨word, newMeaning, ?_, ⟨finalRooted, ?_, combined, actualRead.grows.trans actualIntern.grows⟩, ?_⟩
  · simp only [Lir.Op.exec, baseRead, loaded, Option.bind_some, Option.map_some]
  · rw [actual]
    exact finalTotal
  · exact finalTrace.extend (extends_restrict actualIntern.extension (old.trans actualRead.grows))

/-- The actual candidate store succeeds because its next accepted source
trace event succeeds at the independently tracked current memory. -/
theorem store_success (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (width : Lir.Width) (base offset input : Nat)
    (guarded : Validation.Candidate.Guarded source.nodes.size
      ((evalOp (.store width base offset input)).run state).2.nodes)
    (afterPrefix : EffectPrefix ((evalOp (.store width base offset input)).run state).2.effects source.effects) :
    ∃ memory' newMeaning,
      (Lir.Op.store width base offset input).exec frame memory = some (frame, memory') ∧
      Result state ((evalOp (.store width base offset input)).run state).2 frame meaning newMeaning ∧
      Trace source ((evalOp (.store width base offset input)).run state).2 newMeaning
        initialMemory memory' finalMemory sourceWords (words ++ [none]) := by
  let first := (readReg base).run state
  let second := (readReg input).run first.2
  let event : Effect := .store width first.1 offset second.1
  have actual : (evalOp (.store width base offset input)).run state =
      ((), { second.2 with effects := second.2.effects.push event }) := rfl
  have firstPrefix : Validation.Candidate.Prefix first.2.nodes
      ((evalOp (.store width base offset input)).run state).2.nodes :=
    Validation.Candidate.growing_readReg input first.2
  have secondGuard : Validation.Candidate.Guarded source.nodes.size second.2.nodes := guarded
  obtain ⟨address, baseRead⟩ := Validation.Candidate.readReg_defined state frame meaning rooted total
    source.nodes.size old base (guarded.prefix firstPrefix)
  obtain ⟨firstMeaning, firstRead, firstTotal⟩ :=
    Total.readReg_sound state frame meaning rooted total base address baseRead
  obtain ⟨word, inputRead⟩ := Validation.Candidate.readReg_defined first.2 frame firstMeaning firstRead.rooted firstTotal
    source.nodes.size (old.trans firstRead.grows) input secondGuard
  obtain ⟨newMeaning, secondRead, finalTotal⟩ :=
    Total.readReg_sound first.2 frame firstMeaning firstRead.rooted firstTotal input word inputRead
  have combined : ReadResult state second.2 frame (some word) second.1 meaning newMeaning := firstRead.trans secondRead
  have secondTrace : Trace source second.2 newMeaning initialMemory memory finalMemory sourceWords words :=
    (trace.extend (extends_restrict combined.extension old)).restate combined.effects
  have firstBound : first.1 < second.2.nodes.size := Nat.lt_of_lt_of_le firstRead.bounded secondRead.grows
  have firstSelected : newMeaning.value first.1 = some address :=
    (secondRead.extension.values first.1 firstRead.bounded).trans firstRead.selected
  have secondSelected : newMeaning.value second.1 = some word := secondRead.selected
  have nextPrefix : EffectPrefix (second.2.effects.push event) source.effects := afterPrefix
  obtain ⟨actualEvent, result, nextMemory, concrete, executed, output, accumulated⟩ := secondTrace.next event nextPrefix
  have actualEventEqual : actualEvent = .store width (address.toNat + offset) word := by
    simpa only [event, concreteEffect, firstSelected, secondSelected, Option.bind_some,
      Option.map_some, Option.some.injEq] using concrete.symm
  subst actualEvent
  change ((memory.store width (address.toNat + offset) word).map fun memory => (none, memory)) = _ at executed
  obtain ⟨storedMemory, stored, same⟩ := Option.map_eq_some_iff.mp executed
  have sameResult : none = result := congrArg Prod.fst same
  have sameMemory : storedMemory = nextMemory := congrArg Prod.snd same
  have actualStored : memory.store width (address.toNat + offset) word = some nextMemory := by rw [stored, sameMemory]
  rw [← sameResult] at accumulated
  refine ⟨nextMemory, newMeaning, ?_, ?_, secondTrace.advance afterPrefix accumulated⟩
  · simp only [Lir.Op.exec, baseRead, inputRead, actualStored, Option.bind_some, Option.map_some]
  · rw [actual]
    exact ⟨⟨secondRead.rooted.wellScoped, secondRead.rooted.coherent, secondRead.rooted.regsBounded,
        secondRead.rooted.slotsBounded, secondRead.rooted.regs, secondRead.rooted.slots⟩,
      finalTotal, combined.extension, combined.grows⟩

/-- Faulting arithmetic derives its successful actual result from the next
accepted ordered real event, before interning the corresponding DAG node. -/
theorem faulting_success (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (op : Lir.Binop) (dest left right : Nat) (faulting : Mir.DeadCode.faults op = true)
    (guarded : Validation.Candidate.Guarded source.nodes.size
      ((evalOp (.binary op dest left right)).run state).2.nodes)
    (afterPrefix : EffectPrefix ((evalOp (.binary op dest left right)).run state).2.effects source.effects) :
    ∃ word newMeaning,
      (Lir.Op.binary op dest left right).exec frame memory = some (frame.set dest word, memory) ∧
      Result state ((evalOp (.binary op dest left right)).run state).2 (frame.set dest word) meaning newMeaning ∧
      Trace source ((evalOp (.binary op dest left right)).run state).2 newMeaning
        initialMemory memory finalMemory sourceWords (words ++ [some word]) := by
  let first := (readReg left).run state
  let second := (readReg right).run first.2
  let event : Effect := .faulting op first.1 second.1
  let recorded := (effect event).run second.2
  have actual : (evalOp (.binary op dest left right)).run state =
      (writeReg dest ((intern (.binary op first.1 second.1)).run recorded.2).1).run
        ((intern (.binary op first.1 second.1)).run recorded.2).2 := by
    simp only [evalOp, faulting, ↓reduceIte]
    rfl
  have secondPrefix : Validation.Candidate.Prefix second.2.nodes
      ((evalOp (.binary op dest left right)).run state).2.nodes := by
    rw [actual]
    exact Validation.Candidate.growing_intern (.binary op first.1 second.1) recorded.2
  have firstPrefix : Validation.Candidate.Prefix first.2.nodes
      ((evalOp (.binary op dest left right)).run state).2.nodes :=
    (Validation.Candidate.growing_readReg right first.2).trans secondPrefix
  obtain ⟨x, leftRead⟩ := Validation.Candidate.readReg_defined state frame meaning rooted total
    source.nodes.size old left (guarded.prefix firstPrefix)
  obtain ⟨firstMeaning, firstRead, firstTotal⟩ :=
    Total.readReg_sound state frame meaning rooted total left x leftRead
  obtain ⟨y, rightRead⟩ := Validation.Candidate.readReg_defined first.2 frame firstMeaning firstRead.rooted firstTotal
    source.nodes.size (old.trans firstRead.grows) right (guarded.prefix secondPrefix)
  obtain ⟨secondMeaning, secondRead, secondTotal⟩ :=
    Total.readReg_sound first.2 frame firstMeaning firstRead.rooted firstTotal right y rightRead
  have combined : ReadResult state second.2 frame (some y) second.1 meaning secondMeaning := firstRead.trans secondRead
  have secondTrace : Trace source second.2 secondMeaning initialMemory memory finalMemory sourceWords words :=
    (trace.extend (extends_restrict combined.extension old)).restate combined.effects
  have firstBound : first.1 < second.2.nodes.size := Nat.lt_of_lt_of_le firstRead.bounded secondRead.grows
  have firstSelected : secondMeaning.value first.1 = some x :=
    (secondRead.extension.values first.1 firstRead.bounded).trans firstRead.selected
  have secondSelected : secondMeaning.value second.1 = some y := secondRead.selected
  have effects : ((evalOp (.binary op dest left right)).run state).2.effects = second.2.effects.push event := by
    rw [actual]
    change ((intern (.binary op first.1 second.1)).run recorded.2).2.effects = _
    rw [(Intern.frame recorded.2 (.binary op first.1 second.1)).2.2]
    rfl
  have nextPrefix : EffectPrefix (second.2.effects.push event) source.effects := effects ▸ afterPrefix
  obtain ⟨actualEvent, result, nextMemory, concrete, executed, output, accumulated⟩ := secondTrace.next event nextPrefix
  have actualEventEqual : actualEvent = .faulting op x y := by
    simpa only [event, concreteEffect, firstSelected, secondSelected, Option.bind_some,
      Option.map_some, Option.some.injEq] using concrete.symm
  subst actualEvent
  change ((op.eval x y).map fun word => (some word, memory)) = _ at executed
  obtain ⟨word, computed, same⟩ := Option.map_eq_some_iff.mp executed
  have sameResult : some word = result := congrArg Prod.fst same
  have sameMemory : memory = nextMemory := congrArg Prod.snd same
  rw [← sameResult, ← sameMemory] at accumulated
  have recordedRooted : Rooted recorded.2 frame secondMeaning :=
    ⟨secondRead.rooted.wellScoped, secondRead.rooted.coherent, secondRead.rooted.regsBounded,
      secondRead.rooted.slotsBounded, secondRead.rooted.regs, secondRead.rooted.slots⟩
  have rawComputed : (Expr.binary op first.1 second.1).eval secondMeaning = some word := by
    simp only [Expr.eval, firstSelected, secondSelected, Option.bind_some, computed]
  obtain ⟨newMeaning, actualIntern, finalTotal⟩ := Total.intern_sound recorded.2 frame secondMeaning recordedRooted
    secondTotal (.binary op first.1 second.1) ⟨firstBound, secondRead.bounded⟩ word rawComputed
  have extension : Extends state.nodes.size meaning newMeaning :=
    combined.extension.trans actualIntern.extension combined.grows
  have finalTrace : Trace source ((evalOp (.binary op dest left right)).run state).2 secondMeaning
      initialMemory memory finalMemory sourceWords (words ++ [some word]) := by
    apply secondTrace.advance afterPrefix
    rw [effects]
    exact accumulated
  refine ⟨word, newMeaning, ?_, ?_, finalTrace.extend (extends_restrict actualIntern.extension (old.trans combined.grows))⟩
  · simp only [Lir.Op.exec, leftRead, rightRead, computed, Option.bind_some, Option.map_some]
  · rw [actual]
    exact ⟨writeReg_rooted _ frame newMeaning actualIntern.rooted dest _ word actualIntern.bounded actualIntern.selected,
      finalTotal, extension, combined.grows.trans actualIntern.grows⟩

/-- No-event pure/slot candidates use the existing retained-partial-leaf
success proof and preserve the real consumed memory trace. -/
theorem pure_success (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (operation : Lir.Op Nat) (admitted : Slots.AdmittedOp operation)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((evalOp operation).run state).2.nodes) :
    ∃ frame' newMeaning, operation.exec frame memory = some (frame', memory) ∧
      Result state ((evalOp operation).run state).2 frame' meaning newMeaning ∧
      Trace source ((evalOp operation).run state).2 newMeaning
        initialMemory memory finalMemory sourceWords words := by
  obtain ⟨frame', newMeaning, executed, actual, afterTotal⟩ :=
    Slots.Candidate.evalOp_success state frame memory meaning rooted total source.nodes.size old operation admitted guarded
  exact ⟨frame', newMeaning, executed, ⟨actual.rooted, afterTotal, actual.extension, actual.grows⟩,
    (trace.extend (extends_restrict actual.extension old)).restate actual.effects⟩

/-- Every real primitive candidate operation executes from its actual partial
frame and memory. Admission to this layer excludes only non-op Mir syntax. -/
theorem evalOp_success (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (operation : Lir.Op Nat)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((evalOp operation).run state).2.nodes)
    (afterPrefix : EffectPrefix ((evalOp operation).run state).2.effects source.effects) :
    ∃ frame' memory' newMeaning nextWords, operation.exec frame memory = some (frame', memory') ∧
      Result state ((evalOp operation).run state).2 frame' meaning newMeaning ∧
      Trace source ((evalOp operation).run state).2 newMeaning
        initialMemory memory' finalMemory sourceWords nextWords := by
  have pureStep (operation : Lir.Op Nat) (admitted : Slots.AdmittedOp operation)
      (guarded : Validation.Candidate.Guarded source.nodes.size ((evalOp operation).run state).2.nodes) :
      ∃ frame' memory' newMeaning nextWords, operation.exec frame memory = some (frame', memory') ∧
        Result state ((evalOp operation).run state).2 frame' meaning newMeaning ∧
        Trace source ((evalOp operation).run state).2 newMeaning
          initialMemory memory' finalMemory sourceWords nextWords := by
    obtain ⟨frame', newMeaning, executed, actual, afterTrace⟩ :=
      pure_success source state frame meaning rooted total old initialMemory memory finalMemory sourceWords words
        trace operation admitted guarded
    exact ⟨frame', memory, newMeaning, words, executed, actual, afterTrace⟩
  cases operation with
  | const dest word => exact pureStep _ trivial guarded
  | move dest input => exact pureStep _ trivial guarded
  | unary op dest input => exact pureStep _ trivial guarded
  | binary op dest left right =>
    cases faulting : Mir.DeadCode.faults op with
    | false => exact pureStep _ faulting guarded
    | true =>
      obtain ⟨word, newMeaning, executed, actual, afterTrace⟩ :=
        faulting_success source state frame meaning rooted total old initialMemory memory finalMemory sourceWords words
          trace op dest left right faulting guarded afterPrefix
      exact ⟨frame.set dest word, memory, newMeaning, words ++ [some word], executed, actual, afterTrace⟩
  | load width ext dest base offset =>
    obtain ⟨word, newMeaning, executed, actual, afterTrace⟩ :=
      load_success source state frame meaning rooted total old initialMemory memory finalMemory sourceWords words
        trace width ext dest base offset guarded afterPrefix
    exact ⟨frame.set dest word, memory, newMeaning, words ++ [some word], executed, actual, afterTrace⟩
  | store width base offset input =>
    obtain ⟨memory', newMeaning, executed, actual, afterTrace⟩ :=
      store_success source state frame meaning rooted total old initialMemory memory finalMemory sourceWords words
        trace width base offset input guarded afterPrefix
    exact ⟨frame, memory', newMeaning, words ++ [none], executed, actual, afterTrace⟩
  | slotGet dest slot => exact pureStep _ trivial guarded
  | slotSet slot input => exact pureStep _ trivial guarded

theorem Result.trans {before middle after : State} {frame middleFrame : Lir.Frame Nat}
    {firstMeaning middleMeaning lastMeaning : Interpretation}
    (earlier : Result before middle middleFrame firstMeaning middleMeaning)
    (later : Result middle after frame middleMeaning lastMeaning) :
    Result before after frame firstMeaning lastMeaning :=
  ⟨later.rooted, later.total, earlier.extension.trans later.extension earlier.grows, earlier.grows.trans later.grows⟩

/-- The complete actual primitive candidate list executes. The final accepted
symbolic effect prefix supplies each event, rather than any candidate-run
premise or abstract execution contract. -/
theorem instructions_success (calls : OpenCalls) (instructions : List Mir.Instr)
    (admitted : Effects.Admitted instructions) (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((instructions.forM evalInstr).run state).2.nodes)
    (afterPrefix : EffectPrefix ((instructions.forM evalInstr).run state).2.effects source.effects) :
    ∃ frame' memory' newMeaning nextWords,
      InstructionsExec calls instructions frame memory frame' memory' ∧
      Result state ((instructions.forM evalInstr).run state).2 frame' meaning newMeaning ∧
      Trace source ((instructions.forM evalInstr).run state).2 newMeaning
        initialMemory memory' finalMemory sourceWords nextWords := by
  induction instructions generalizing state frame meaning memory words with
  | nil => exact ⟨frame, memory, meaning, words, .nil, ⟨rooted, total, .refl _ _, Nat.le_refl _⟩, trace⟩
  | cons instruction rest ih =>
    show ∃ frame' memory' newMeaning nextWords,
      InstructionsExec calls (instruction :: rest) frame memory frame' memory' ∧
      Result state (((instruction :: rest).forM evalInstr).run state).2 frame' meaning newMeaning ∧
      Trace source (((instruction :: rest).forM evalInstr).run state).2 newMeaning
        initialMemory memory' finalMemory sourceWords nextWords
    have headAdmitted : Effects.AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Effects.Admitted rest := fun i member => admitted i (by simp [member])
    have tailGuard : Validation.Candidate.Guarded source.nodes.size
        ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.nodes := by
      simpa only [Lists.forM_cons_run] using guarded
    have headGuard : Validation.Candidate.Guarded source.nodes.size ((evalInstr instruction).run state).2.nodes :=
      tailGuard.prefix (Nodes.forM rest tailAdmitted ((evalInstr instruction).run state).2)
    have tailPrefix : EffectPrefix ((rest.forM evalInstr).run ((evalInstr instruction).run state).2).2.effects source.effects := by
      simpa only [Lists.forM_cons_run] using afterPrefix
    have headPrefix : EffectPrefix ((evalInstr instruction).run state).2.effects source.effects :=
      (growing_forM rest tailAdmitted ((evalInstr instruction).run state).2).trans tailPrefix
    have step : ∃ middle middleMemory middleMeaning middleWords,
        InstructionExec calls instruction frame memory middle middleMemory ∧
        Result state ((evalInstr instruction).run state).2 middle meaning middleMeaning ∧
        Trace source ((evalInstr instruction).run state).2 middleMeaning
          initialMemory middleMemory finalMemory sourceWords middleWords := by
      cases instruction with
      | op operation =>
        obtain ⟨middle, middleMemory, middleMeaning, middleWords, executed, actual, afterTrace⟩ :=
          evalOp_success source state frame meaning rooted total old initialMemory memory finalMemory sourceWords words
            trace operation headGuard headPrefix
        exact ⟨middle, middleMemory, middleMeaning, middleWords, .op executed, actual, afterTrace⟩
      | fop op dest left right => cases headAdmitted
      | addr dest symbol offset => cases headAdmitted
      | call symbol args results => cases headAdmitted
      | callIndirect target args results => cases headAdmitted
    obtain ⟨middle, middleMemory, middleMeaning, middleWords, headExecuted, headResult, headTrace⟩ := step
    obtain ⟨frame', memory', newMeaning, nextWords, tailExecuted, tailResult, tailTrace⟩ :=
      ih tailAdmitted ((evalInstr instruction).run state).2 middle middleMeaning headResult.rooted headResult.total
        (old.trans headResult.grows) middleMemory middleWords headTrace tailGuard tailPrefix
    rw [Lists.forM_cons_run]
    exact ⟨frame', memory', newMeaning, nextWords, .cons headExecuted tailExecuted, headResult.trans tailResult, tailTrace⟩

/-- Finish a genuinely executed symbolic body using the actual retained-node
check for its terminator and observed reads. Shared by all admitted fragments;
no body syntax, address map, target reads or target terminator run is assumed. -/
theorem finish_block (calls : OpenCalls) (block : Mir.Block) (observed : List Nat)
    (source state : State) (frame frame' : Lir.Frame Nat) (meaning bodyMeaning : Interpretation)
    (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory memory' finalMemory : Lir.Memory) (sourceWords bodyWords : List (Option Lir.Word))
    (guarded : Validation.Candidate.Guarded source.nodes.size ((evalBlock block observed).run state).2.nodes)
    (bodyExecuted : InstructionsExec calls block.instrs.toList frame memory frame' memory')
    (bodyResult : Result state ((block.instrs.toList.forM evalInstr).run state).2 frame' meaning bodyMeaning)
    (bodyTrace : Trace source ((block.instrs.toList.forM evalInstr).run state).2 bodyMeaning
      initialMemory memory' finalMemory sourceWords bodyWords) :
    ∃ exit values newMeaning,
      BlockExec calls block frame memory exit frame' memory' ∧ observed.mapM frame'.get = some values ∧
      BlockResult state ((evalBlock block observed).run state).2 frame'
        ((evalBlock block observed).run state).1.1 ((evalBlock block observed).run state).1.2
        exit values meaning newMeaning ∧
      Trace source ((evalBlock block observed).run state).2 newMeaning initialMemory memory' finalMemory sourceWords bodyWords := by
  let body := (block.instrs.toList.forM evalInstr).run state
  let term := (evalTerm block.term).run body.2
  let observations := (observed.mapM readReg).run term.2
  have observationsGuard : Validation.Candidate.Guarded source.nodes.size observations.2.nodes := by
    simpa only [Lists.evalBlock_run] using guarded
  have termGuard : Validation.Candidate.Guarded source.nodes.size term.2.nodes :=
    observationsGuard.prefix (Validation.Candidate.growing_mapM readReg observed Validation.Candidate.growing_readReg term.2)
  obtain ⟨exit, termMeaning, termExecuted, termResult⟩ :=
    Validation.Candidate.evalTerm_success block.term frame' body.2 bodyMeaning bodyResult.rooted bodyResult.total
      source.nodes.size (old.trans bodyResult.grows) termGuard
  have termTrace : Trace source term.2 termMeaning initialMemory memory' finalMemory sourceWords bodyWords :=
    (bodyTrace.extend (extends_restrict termResult.result.extension (old.trans bodyResult.grows))).restate termResult.result.effects
  obtain ⟨values, newMeaning, read, observedResult⟩ :=
    Validation.Candidate.readRegs_success observed frame' source.nodes.size term.2 termMeaning termResult.result.rooted termResult.total
      ((old.trans bodyResult.grows).trans termResult.result.grows) observationsGuard
  have finalTrace : Trace source observations.2 newMeaning initialMemory memory' finalMemory sourceWords bodyWords :=
    (termTrace.extend (extends_restrict observedResult.result.extension
      ((old.trans bodyResult.grows).trans termResult.result.grows))).restate observedResult.result.effects
  have termActual : Result body.2 term.2 frame' bodyMeaning termMeaning :=
    ⟨termResult.result.rooted, termResult.total, termResult.result.extension, termResult.result.grows⟩
  have observationsActual : Result term.2 observations.2 frame' termMeaning newMeaning :=
    ⟨observedResult.result.rooted, observedResult.total, observedResult.result.extension, observedResult.result.grows⟩
  have common : Result state observations.2 frame' meaning newMeaning := bodyResult.trans (termActual.trans observationsActual)
  have scopedTerm : Observation.TermScoped observations.2.nodes.size term.1 :=
    Observation.termScoped_mono term.1 observedResult.result.grows termResult.wellScoped
  have decoded : Observation.termExit newMeaning term.1 = some exit :=
    (Observation.termExit_preserved term.1 observedResult.result.extension termResult.wellScoped).trans termResult.selected
  rw [Lists.evalBlock_run]
  exact ⟨exit, values, newMeaning, ⟨bodyExecuted, termExecuted⟩, read,
    ⟨common, scopedTerm, decoded, observedResult.bounded, observedResult.selected⟩, finalTrace⟩

/-- Complete actual candidate execution, including its terminator and observed
register reads, with real final frame, memory and consumed effect trace. -/
theorem block_success (calls : OpenCalls) (block : Mir.Block)
    (admitted : Effects.Admitted block.instrs.toList) (observed : List Nat)
    (source state : State) (frame : Lir.Frame Nat)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (guarded : Validation.Candidate.Guarded source.nodes.size ((evalBlock block observed).run state).2.nodes)
    (afterPrefix : EffectPrefix ((evalBlock block observed).run state).2.effects source.effects) :
    ∃ exit frame' memory' values newMeaning nextWords,
      BlockExec calls block frame memory exit frame' memory' ∧
      observed.mapM frame'.get = some values ∧
      BlockResult state ((evalBlock block observed).run state).2 frame'
        ((evalBlock block observed).run state).1.1 ((evalBlock block observed).run state).1.2
        exit values meaning newMeaning ∧
      Trace source ((evalBlock block observed).run state).2 newMeaning
        initialMemory memory' finalMemory sourceWords nextWords := by
  let body := (block.instrs.toList.forM evalInstr).run state
  let term := (evalTerm block.term).run body.2
  let observations := (observed.mapM readReg).run term.2
  have observationsGuard : Validation.Candidate.Guarded source.nodes.size observations.2.nodes := by
    simpa only [Lists.evalBlock_run] using guarded
  have termGuard : Validation.Candidate.Guarded source.nodes.size term.2.nodes :=
    observationsGuard.prefix (Validation.Candidate.growing_mapM readReg observed Validation.Candidate.growing_readReg term.2)
  have bodyGuard : Validation.Candidate.Guarded source.nodes.size body.2.nodes :=
    termGuard.prefix (Validation.Candidate.growing_evalTerm block.term body.2)
  have bodyPrefix : EffectPrefix body.2.effects source.effects := by
    have observationsPrefix : EffectPrefix observations.2.effects source.effects := by
      simpa only [Lists.evalBlock_run] using afterPrefix
    exact (growing_evalTerm block.term body.2).trans
      ((growing_mapM readReg observed growing_readReg term.2).trans observationsPrefix)
  obtain ⟨frame', memory', bodyMeaning, bodyWords, bodyExecuted, bodyResult, bodyTrace⟩ :=
    instructions_success calls block.instrs.toList admitted source state frame meaning rooted total old
      initialMemory memory finalMemory sourceWords words trace bodyGuard bodyPrefix
  obtain ⟨exit, values, newMeaning, executed, read, actual, trace⟩ :=
    Effects.Candidate.finish_block calls block observed source state frame frame' meaning bodyMeaning old
      initialMemory memory memory' finalMemory sourceWords bodyWords guarded bodyExecuted bodyResult bodyTrace
  exact ⟨exit, frame', memory', values, newMeaning, bodyWords, executed, read, actual, trace⟩

/-- A completed candidate trace has the actual source final memory and all
ordered source effect results, by deterministic execution of the same array. -/
theorem Trace.complete {source state : State} {meaning : Interpretation}
    {initialMemory memory finalMemory : Lir.Memory} {sourceWords words : List (Option Lir.Word)}
    (trace : Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (same : state.effects = source.effects) : words = sourceWords ∧ memory = finalMemory := by
  have currentRun := trace.currentRun
  rw [same] at currentRun
  exact Prod.mk.inj (Option.some.inj (currentRun.symm.trans trace.sourceRun))

/-- The candidate starts from the independently successful complete source DAG,
while its concrete frame is the original actual partial input frame. -/
theorem seed_rooted {address : String → Nat → Option Lir.Word} (source : State) (frame sourceFrame : Lir.Frame Nat)
    (initialMemory finalMemory : Lir.Memory) (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : Source.InvariantWith address frame initialMemory source sourceFrame finalMemory sourceWords meaning) :
    Rooted { nodes := source.nodes } frame meaning := by
  refine ⟨invariant.rooted.wellScoped, invariant.rooted.coherent, ?_, ?_, ?_, ?_⟩
  · intro root member
    cases member
  · intro root member
    cases member
  · intro reg
    exact congrFun invariant.inputs.input reg
  · intro slot
    exact congrFun invariant.inputs.slot slot

/-- Empty candidate effects consume no memory events; the complete source
trace and source-derived ghost load map already exist independently. -/
theorem seed_trace {address : String → Nat → Option Lir.Word} (source : State) (frame sourceFrame : Lir.Frame Nat)
    (initialMemory finalMemory : Lir.Memory) (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : Source.InvariantWith address frame initialMemory source sourceFrame finalMemory sourceWords meaning) :
    Trace source { nodes := source.nodes } meaning initialMemory initialMemory finalMemory sourceWords [] :=
  ⟨⟨source.effects.toList, rfl⟩, invariant.effects, invariant.executed, rfl, invariant.loadResults⟩

/-- A seeded actual candidate with the complete accepted effect array executes
to precisely the independently established source final memory. -/
theorem seeded_block_success {address : String → Nat → Option Lir.Word} (calls : OpenCalls) (block : Mir.Block)
    (admitted : Effects.Admitted block.instrs.toList) (observed : List Nat)
    (source : State) (frame sourceFrame : Lir.Frame Nat)
    (initialMemory finalMemory : Lir.Memory) (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : Source.InvariantWith address frame initialMemory source sourceFrame finalMemory sourceWords meaning)
    (guarded : ((evalBlock block observed).run { nodes := source.nodes }).2.nodes.any Expr.isPartialLeaf source.nodes.size = false)
    (sameEffects : ((evalBlock block observed).run { nodes := source.nodes }).2.effects = source.effects) :
    ∃ exit frame' values newMeaning,
      BlockExec calls block frame initialMemory exit frame' finalMemory ∧
      observed.mapM frame'.get = some values ∧
      BlockResult { nodes := source.nodes } ((evalBlock block observed).run { nodes := source.nodes }).2 frame'
        ((evalBlock block observed).run { nodes := source.nodes }).1.1
        ((evalBlock block observed).run { nodes := source.nodes }).1.2 exit values meaning newMeaning := by
  have finalPrefix : EffectPrefix ((evalBlock block observed).run { nodes := source.nodes }).2.effects source.effects := by
    rw [sameEffects]
    exact .refl _
  obtain ⟨exit, frame', memory', values, newMeaning, nextWords, executed, read, actual, trace⟩ :=
    block_success calls block admitted observed source { nodes := source.nodes } frame meaning
      (seed_rooted source frame sourceFrame initialMemory finalMemory sourceWords meaning invariant)
      invariant.total (Nat.le_refl _) initialMemory initialMemory finalMemory sourceWords []
      (seed_trace source frame sourceFrame initialMemory finalMemory sourceWords meaning invariant)
      (Validation.Candidate.guarded_of_any _ _ guarded) finalPrefix
  have sameMemory : memory' = finalMemory := (trace.complete sameEffects).2
  exact ⟨exit, frame', values, newMeaning, sameMemory ▸ executed, read, actual⟩

/-- Match complete source and candidate symbolic results using the actual
checker's equal term/output/slot certificates. Independent of the instruction
fragment and fixed source address resolver; candidate execution is not assumed. -/
theorem accepted_results_match {address : String → Nat → Option Lir.Word}
    {base : Nat} {source candidate : Mir.Block}
    {frame sourceFrame candidateFrame : Lir.Frame Nat} {memory sourceMemory : Lir.Memory}
    {exit candidateExit : BlockExit} {sourceWords : List (Option Lir.Word)}
    {values candidateValues : List Lir.Word} {meaning newMeaning : Interpretation}
    (sourceResult : Source.BlockResultWith address frame memory (Acceptance.sourceRun source).2
      sourceFrame sourceMemory sourceWords (Acceptance.sourceRun source).1.1
      (Acceptance.sourceRun source).1.2 exit values meaning)
    (candidateResult : BlockResult { nodes := (Acceptance.sourceRun source).2.nodes }
      (Acceptance.candidateRun source candidate).2 candidateFrame
      (Acceptance.candidateRun source candidate).1.1 (Acceptance.candidateRun source candidate).1.2
      candidateExit candidateValues meaning newMeaning)
    (facts : Acceptance.Accepted base source candidate) :
    candidateExit = exit ∧ candidateValues = values ∧ candidateFrame.slots = sourceFrame.slots := by
  have sourceExit : Observation.termExit newMeaning (Acceptance.sourceRun source).1.1 = some exit :=
    (Observation.termExit_preserved _ candidateResult.result.extension sourceResult.termScoped).trans sourceResult.selected
  rw [facts.term] at sourceExit
  have sameExit : candidateExit = exit := Option.some.inj (candidateResult.selected.symm.trans sourceExit)
  have sourceValues : (Acceptance.sourceRun source).1.2.mapM newMeaning.value = some values :=
    (Observation.values_preserved _ candidateResult.result.extension sourceResult.observedBounded).trans sourceResult.observed
  rw [facts.observed] at sourceValues
  have sameValues : candidateValues = values := Option.some.inj (candidateResult.observed.symm.trans sourceValues)
  have slotsSame : candidateFrame.slots = sourceFrame.slots :=
    Slots.states_slots_agree (Acceptance.sourceRun source).2 (Acceptance.candidateRun source candidate).2
      sourceFrame candidateFrame meaning newMeaning sourceResult.invariant.rooted candidateResult.result.rooted
      candidateResult.result.extension candidateResult.result.grows facts.slots
  exact ⟨sameExit, sameValues, slotsSame⟩

/-- Actual checker acceptance derives the candidate's real execution, exact
source final memory, whole slot map and observed source outputs. The source
execution and independent all-primitive syntax are the only semantic inputs. -/
theorem accepted_block_success (calls : OpenCalls) (base : Nat) (source candidate : Mir.Block)
    (frame sourceFrame : Lir.Frame Nat) (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceAdmitted : Effects.Admitted source.instrs.toList)
    (candidateAdmitted : Effects.Admitted candidate.instrs.toList)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (accepted : check base source candidate = true) :
    ∃ candidateFrame values, BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (Acceptance.observedRegs source).mapM sourceFrame.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  have facts : Acceptance.Accepted base source candidate :=
    (Acceptance.check_eq_true_iff base source candidate).mp accepted
  obtain ⟨meaning, sourceWords, values, sourceRead, sourceResult⟩ :=
    Source.source_block calls source frame sourceFrame memory sourceMemory exit sourceAdmitted sourceExecuted
  obtain ⟨candidateExit, candidateFrame, candidateValues, newMeaning, candidateExecuted, candidateRead, candidateResult⟩ :=
    seeded_block_success calls candidate candidateAdmitted (Acceptance.observedRegs source)
      (Acceptance.sourceRun source).2 frame sourceFrame memory sourceMemory sourceWords meaning sourceResult.invariant
      facts.partialLeaves facts.effects.symm
  obtain ⟨sameExit, sameValues, slotsSame⟩ := accepted_results_match sourceResult candidateResult facts
  exact ⟨candidateFrame, values, sameExit ▸ candidateExecuted, slotsSame, sourceRead, sameValues ▸ candidateRead⟩

end Silmaril.Compiler.Native.Optimize.Validation.Effects.Candidate
