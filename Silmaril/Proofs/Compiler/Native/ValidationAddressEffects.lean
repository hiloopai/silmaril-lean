module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract
open Validation.Effects Validation.Effects.Source

/-- Ordinary address interning and register update add no memory event. -/
theorem safe_addr (dest : Nat) (symbol : String) (offset : Nat) :
    Safe (evalInstr (.addr dest symbol offset)) :=
  safe_bind _ _ (safe_intern (.addr symbol offset) (fun _ => trivial)) (fun index => safe_writeReg dest index)

/-- A real successfully resolved source address preserves the complete ordered
memory trace and every earlier source load result under the actual resolver. -/
theorem addr_invariant (units : Array Mir.Unit) (placement : MirSem.Placement)
    (initialFrame frame : Lir.Frame Nat) (initialMemory memory : Lir.Memory)
    (state : State) (words : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : InvariantWith (resolve units placement) initialFrame initialMemory state frame memory words meaning)
    (dest : Nat) (symbol : String) (offset : Nat) (word : Lir.Word)
    (resolved : resolve units placement symbol offset = some word) :
    ∃ newMeaning, InvariantWith (resolve units placement) initialFrame initialMemory
      ((evalInstr (.addr dest symbol offset)).run state).2 (frame.set dest word) memory words newMeaning := by
  have fixed : meaning.address = resolve units placement := invariant.inputs.address
  obtain ⟨newMeaning, actual, after⟩ := Address.evalInstr_sound units placement state frame meaning
    ⟨invariant.rooted, invariant.total, fixed⟩ dest symbol offset word resolved
  have common : Result state ((evalInstr (.addr dest symbol offset)).run state).2
      (frame.set dest word) meaning newMeaning :=
    ⟨actual.rooted, after.total, safe_addr dest symbol offset state invariant.loads,
      prefix_of_extends actual.extension _, actual.grows⟩
  exact ⟨newMeaning, invariant_pure invariant common actual.effects actual.extension.load⟩

/-- Actual mixed source execution constructs all retained DAG denotations and
real ordered event results, including addresses feeding later loads/stores. -/
theorem instructions_invariant (units : Array Mir.Unit) (placement : MirSem.Placement)
    (instructions : List Mir.Instr) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Admitted instructions)
    (executed : InstructionsExec (calls units placement) instructions frame memory final finalMemory)
    (initialFrame : Lir.Frame Nat) (initialMemory : Lir.Memory) (state : State)
    (words : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : InvariantWith (resolve units placement) initialFrame initialMemory state frame memory words meaning) :
    ∃ newMeaning newWords, InvariantWith (resolve units placement) initialFrame initialMemory
      ((instructions.forM evalInstr).run state).2 final finalMemory newWords newMeaning := by
  induction executed generalizing state words meaning with
  | nil => exact ⟨meaning, words, invariant⟩
  | @cons instruction rest frame memory middle middleMemory final finalMemory first later ih =>
    show ∃ newMeaning newWords, InvariantWith (resolve units placement) initialFrame initialMemory
      (((instruction :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
    have headAdmitted : AdmittedInstr instruction := admitted instruction (by simp)
    have tailAdmitted : Admitted rest := fun i member => admitted i (by simp [member])
    cases instruction with
    | op operation =>
      show ∃ newMeaning newWords, InvariantWith (resolve units placement) initialFrame initialMemory
        (((Mir.Instr.op operation :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
      cases first with
      | op actual =>
        obtain ⟨middleMeaning, middleWords, actualResult⟩ := evalOp_invariant initialFrame frame middle
          initialMemory memory middleMemory state words meaning invariant operation actual
        obtain ⟨newMeaning, newWords, finalInvariant⟩ := ih tailAdmitted ((evalInstr (.op operation)).run state).2
          middleWords middleMeaning actualResult
        rw [Lists.forM_cons_run]
        exact ⟨newMeaning, newWords, finalInvariant⟩
    | fop op dest left right =>
      show ∃ newMeaning newWords, InvariantWith (resolve units placement) initialFrame initialMemory
        (((Mir.Instr.fop op dest left right :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
      cases first with
      | fop actual =>
        obtain ⟨middleMeaning, actualResult⟩ := Floating.Source.fop_invariant initialFrame frame middle initialMemory memory
          state words meaning invariant op dest left right actual
        obtain ⟨newMeaning, newWords, finalInvariant⟩ := ih tailAdmitted ((evalInstr (.fop op dest left right)).run state).2
          words middleMeaning actualResult
        rw [Lists.forM_cons_run]
        exact ⟨newMeaning, newWords, finalInvariant⟩
    | addr dest symbol offset =>
      show ∃ newMeaning newWords, InvariantWith (resolve units placement) initialFrame initialMemory
        (((Mir.Instr.addr dest symbol offset :: rest).forM evalInstr).run state).2 final finalMemory newWords newMeaning
      cases first with
      | addr resolved =>
        obtain ⟨middleMeaning, actualResult⟩ := addr_invariant units placement initialFrame frame initialMemory memory
          state words meaning invariant dest symbol offset _ resolved
        obtain ⟨newMeaning, newWords, finalInvariant⟩ := ih tailAdmitted ((evalInstr (.addr dest symbol offset)).run state).2
          words middleMeaning actualResult
        rw [Lists.forM_cons_run]
        exact ⟨newMeaning, newWords, finalInvariant⟩
    | call symbol args results => cases headAdmitted
    | callIndirect target args results => cases headAdmitted

/-- Source startup keeps the real partial input frame and constructs the
address-aware ordered trace from actual successful mixed execution. -/
theorem source_instructions_invariant (units : Array Mir.Unit) (placement : MirSem.Placement)
    (instructions : List Mir.Instr) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (admitted : Admitted instructions)
    (executed : InstructionsExec (calls units placement) instructions frame memory final finalMemory) :
    ∃ meaning words, InvariantWith (resolve units placement) frame memory
      ((instructions.forM evalInstr).run {}).2 final finalMemory words meaning :=
  instructions_invariant units placement instructions frame final memory finalMemory admitted executed frame memory {} []
    (Leaf.initialMeaning frame (resolve units placement)) (initial_invariant_with _ frame memory)

/-- Successful actual source execution provides the retained full DAG and
complete load interpretation for a genuinely empty candidate event prefix. -/
theorem source_seed (units : Array Mir.Unit) (placement : MirSem.Placement)
    (source : State) (frame sourceFrame : Lir.Frame Nat)
    (initialMemory finalMemory : Lir.Memory) (words : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : InvariantWith (resolve units placement) frame initialMemory source sourceFrame finalMemory words meaning) :
    Address.Invariant units placement { nodes := source.nodes } frame meaning ∧
      Validation.Effects.Candidate.Trace source { nodes := source.nodes } meaning
        initialMemory initialMemory finalMemory words [] :=
  ⟨⟨Validation.Effects.Candidate.seed_rooted source frame sourceFrame initialMemory finalMemory words meaning invariant,
      invariant.total, invariant.inputs.address⟩,
    Validation.Effects.Candidate.seed_trace source frame sourceFrame initialMemory finalMemory words meaning invariant⟩

/-- Guarded address execution preserves the candidate's actual consumed memory
trace. Successful target resolution and execution are conclusions of retained
source-node totality, never supplied as replay assumptions. -/
theorem candidate_addr_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (source state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (invariant : Address.Invariant units placement state frame meaning)
    (old : source.nodes.size ≤ state.nodes.size)
    (initialMemory memory finalMemory : Lir.Memory) (sourceWords words : List (Option Lir.Word))
    (trace : Validation.Effects.Candidate.Trace source state meaning initialMemory memory finalMemory sourceWords words)
    (dest : Nat) (symbol : String) (offset : Nat)
    (guarded : Validation.Candidate.Guarded source.nodes.size
      ((evalInstr (.addr dest symbol offset)).run state).2.nodes) :
    ∃ word newMeaning, resolve units placement symbol offset = some word ∧
      InstructionExec (calls units placement) (.addr dest symbol offset) frame memory (frame.set dest word) memory ∧
      Validation.Effects.Candidate.Result state ((evalInstr (.addr dest symbol offset)).run state).2
        (frame.set dest word) meaning newMeaning ∧
      Validation.Effects.Candidate.Trace source ((evalInstr (.addr dest symbol offset)).run state).2 newMeaning
        initialMemory memory finalMemory sourceWords words ∧
      Address.Invariant units placement ((evalInstr (.addr dest symbol offset)).run state).2
        (frame.set dest word) newMeaning := by
  obtain ⟨word, newMeaning, resolved, executed, actual, after⟩ := Address.candidate_success units placement state frame memory
    meaning invariant source.nodes.size old dest symbol offset guarded
  exact ⟨word, newMeaning, resolved, executed, ⟨actual.rooted, after.total, actual.extension, actual.grows⟩,
    (trace.extend (Validation.Effects.Candidate.extends_restrict actual.extension old)).restate actual.effects, after⟩

/-- A completed real source invariant and its actual retained-leaf guard are
sufficient to derive a candidate address step from empty consumed effects. -/
theorem seeded_addr_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (source : State) (frame sourceFrame : Lir.Frame Nat)
    (initialMemory finalMemory : Lir.Memory) (sourceWords : List (Option Lir.Word)) (meaning : Interpretation)
    (invariant : InvariantWith (resolve units placement) frame initialMemory source sourceFrame finalMemory sourceWords meaning)
    (dest : Nat) (symbol : String) (offset : Nat)
    (guarded : Validation.Candidate.Guarded source.nodes.size
      ((evalInstr (.addr dest symbol offset)).run { nodes := source.nodes }).2.nodes) :
    ∃ word newMeaning, resolve units placement symbol offset = some word ∧
      InstructionExec (calls units placement) (.addr dest symbol offset) frame initialMemory (frame.set dest word) initialMemory ∧
      Validation.Effects.Candidate.Result { nodes := source.nodes }
        ((evalInstr (.addr dest symbol offset)).run { nodes := source.nodes }).2 (frame.set dest word) meaning newMeaning ∧
      Validation.Effects.Candidate.Trace source ((evalInstr (.addr dest symbol offset)).run { nodes := source.nodes }).2 newMeaning
        initialMemory initialMemory finalMemory sourceWords [] ∧
      Address.Invariant units placement ((evalInstr (.addr dest symbol offset)).run { nodes := source.nodes }).2
        (frame.set dest word) newMeaning := by
  obtain ⟨seeded, trace⟩ := source_seed units placement source frame sourceFrame initialMemory finalMemory sourceWords meaning invariant
  exact candidate_addr_success units placement source { nodes := source.nodes } frame meaning seeded (Nat.le_refl _)
    initialMemory initialMemory finalMemory sourceWords [] trace dest symbol offset guarded

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects
