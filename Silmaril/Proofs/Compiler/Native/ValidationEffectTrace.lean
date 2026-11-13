module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Trace.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects
open Silmaril.Machine Silmaril.Compile

theorem runEvents_nil (memory : Lir.Memory) : runEvents [] memory = some ([], memory) := rfl

theorem runEvents_singleton (event : Event) (memory final : Lir.Memory) (word : Option Lir.Word)
    (executed : event.exec memory = some (word, final)) :
    runEvents [event] memory = some ([word], final) := by
  simp only [runEvents, executed, Option.bind_some, Option.map_some]

theorem runEvents_append (first last : List Event) (memory middle final : Lir.Memory)
    (firstWords lastWords : List (Option Lir.Word))
    (earlier : runEvents first memory = some (firstWords, middle))
    (later : runEvents last middle = some (lastWords, final)) :
    runEvents (first ++ last) memory = some (firstWords ++ lastWords, final) := by
  induction first generalizing memory firstWords with
  | nil =>
    have same : [] = firstWords ∧ memory = middle := by simpa only [runEvents, Option.some.injEq, Prod.mk.injEq] using earlier
    simpa [← same.1, ← same.2] using later
  | cons event rest ih =>
    obtain ⟨head, headExec, tail, tailExec, output⟩ :
        ∃ head, event.exec memory = some head ∧ ∃ tail,
          runEvents rest head.2 = some tail ∧ (head.1 :: tail.1, tail.2) = (firstWords, middle) := by
      simpa only [runEvents, Option.bind_eq_some_iff, Option.map_eq_some_iff] using earlier
    obtain ⟨word, afterHead⟩ := head
    obtain ⟨words, afterRest⟩ := tail
    have firstSame : word :: words = firstWords := congrArg Prod.fst output
    have lastSame : afterRest = middle := congrArg Prod.snd output
    subst firstWords
    subst afterRest
    have combined := ih afterHead words tailExec
    simp only [List.cons_append, runEvents, headExec, Option.bind_some, combined]
    rfl

/-- Successful actual source execution generates the real ordered event
outcomes and exactly its final memory. Missing inputs or failed memory/arithmetic
are not filled in by totality assumptions. -/
theorem source_operation_events (operation : Lir.Op Nat) (frame final : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory)
    (executed : operation.exec frame memory = some (final, finalMemory)) :
    ∃ events words, sourceEvents operation frame = some events ∧
      runEvents events memory = some (words, finalMemory) := by
  cases operation with
  | const dest word =>
    have output : frame.set dest word = final ∧ memory = finalMemory := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using executed
    exact ⟨[], [], rfl, output.2 ▸ rfl⟩
  | move dest source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.set dest word = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    exact ⟨[], [], rfl, output.2 ▸ rfl⟩
  | unary op dest source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.set dest (op.eval word) = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    exact ⟨[], [], rfl, output.2 ▸ rfl⟩
  | binary op dest left right =>
    show ∃ events words, sourceEvents (.binary op dest left right) frame = some events ∧
      runEvents events memory = some (words, finalMemory)
    obtain ⟨x, leftRead, y, rightRead, result, computed, output⟩ :
        ∃ x, frame.get left = some x ∧ ∃ y, frame.get right = some y ∧
          ∃ result, op.eval x y = some result ∧ (frame.set dest result = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    cases faulting : Mir.DeadCode.faults op with
    | false => exact ⟨[], [], by simp [sourceEvents, faulting], output.2 ▸ rfl⟩
    | true =>
      refine ⟨[.faulting op x y], [some result], ?_, ?_⟩
      · simp [sourceEvents, faulting, leftRead, rightRead]
      · apply runEvents_singleton
        simp only [Event.exec, computed, Option.map_some, output.2]
  | load width ext dest base offset =>
    show ∃ events words, sourceEvents (.load width ext dest base offset) frame = some events ∧
      runEvents events memory = some (words, finalMemory)
    obtain ⟨address, read, word, loaded, output⟩ :
        ∃ address, frame.get base = some address ∧ ∃ word,
          memory.load width ext (address.toNat + offset) = some word ∧
          (frame.set dest word = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨[.load width ext (address.toNat + offset)], [some word], ?_, ?_⟩
    · simp only [sourceEvents, read, Option.map_some]
    · apply runEvents_singleton
      rw [← output.2]
      simp only [Event.exec, loaded, Option.map_some]
  | store width base offset source =>
    show ∃ events words, sourceEvents (.store width base offset source) frame = some events ∧
      runEvents events memory = some (words, finalMemory)
    obtain ⟨address, baseRead, word, sourceRead, after, stored, output⟩ :
        ∃ address, frame.get base = some address ∧ ∃ word, frame.get source = some word ∧
          ∃ after, memory.store width (address.toNat + offset) word = some after ∧
          (frame = final ∧ after = finalMemory) := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    refine ⟨[.store width (address.toNat + offset) word], [none], ?_, ?_⟩
    · simp only [sourceEvents, baseRead, sourceRead, Option.bind_some, Option.map_some]
    · apply runEvents_singleton
      simp only [Event.exec, stored, Option.map_some, output.2]
  | slotGet dest slot =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.slots slot = some word ∧
        (frame.set dest word = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    exact ⟨[], [], rfl, output.2 ▸ rfl⟩
  | slotSet slot source =>
    obtain ⟨word, read, output⟩ : ∃ word, frame.get source = some word ∧
        (frame.setSlot slot word = final ∧ memory = finalMemory) := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    exact ⟨[], [], rfl, output.2 ▸ rfl⟩

/-- Generate the complete event trace by induction on actual successful source
execution, retaining exact source memory changes and event order. -/
theorem source_instructions_events (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory final finalMemory) :
    ∃ events words, SourceTrace calls instructions frame memory events final finalMemory ∧
      runEvents events memory = some (words, finalMemory) := by
  induction executed with
  | nil => exact ⟨[], [], .nil _ _, rfl⟩
  | @cons instruction rest frame memory middle middleMemory final finalMemory first later ih =>
    have headAdmitted := admitted instruction (by simp)
    have tailAdmitted : Admitted rest := fun i member => admitted i (by simp [member])
    obtain ⟨tail, tailWords, tailTrace, tailRun⟩ := ih tailAdmitted
    cases instruction with
    | op operation =>
      cases first with
      | op actual =>
        obtain ⟨head, headWords, headEvents, headRun⟩ := source_operation_events operation frame middle memory middleMemory actual
        exact ⟨head ++ tail, headWords ++ tailWords,
          .cons operation rest frame middle final memory middleMemory finalMemory head tail actual headEvents tailTrace,
          runEvents_append head tail memory middleMemory finalMemory headWords tailWords headRun tailRun⟩
    | fop op dest left right => cases headAdmitted
    | addr dest symbol offset => cases headAdmitted
    | call symbol args results => cases headAdmitted
    | callIndirect target args results => cases headAdmitted

/-- Replaying the same concrete ordered events retains all results and the
exact final memory, including byte writes. -/
theorem runEvents_unique (events : List Event) (memory first last : Lir.Memory)
    (firstWords lastWords : List (Option Lir.Word))
    (earlier : runEvents events memory = some (firstWords, first))
    (later : runEvents events memory = some (lastWords, last)) :
    firstWords = lastWords ∧ first = last :=
  Prod.mk.inj (Option.some.inj (earlier.symm.trans later))

/-- This is symbolic event replay only. Deriving the candidate primitive
execution from rooted DAG/event-prefix invariants is a subsequent proof. -/
theorem accepted_effects_replay (base : Nat) (source candidate : Mir.Block)
    (accepted : Acceptance.Accepted base source candidate) (meaning : Interpretation)
    (memory finalMemory : Lir.Memory) (words : List (Option Lir.Word))
    (sourceRun : runEffects meaning (Acceptance.sourceRun source).2.effects.toList memory =
      some (words, finalMemory)) :
    runEffects meaning (Acceptance.candidateRun source candidate).2.effects.toList memory =
      some (words, finalMemory) := by
  rw [← accepted.effects]
  exact sourceRun

end Silmaril.Compiler.Native.Optimize.Validation.Effects
