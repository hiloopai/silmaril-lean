module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk

open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

public theorem step_wire {plan : Plan} {ceiling rep defn : Nat} {start : State} {slot : Slot}
    (accepted : step plan ceiling start rep defn = .ok slot) :
    slot.repetition = rep ∧ slot.definition = defn ∧ StepWire plan ceiling start slot := by
  unfold step at accepted
  split at accepted
  · rename_i pos position
    split at accepted
    · rename_i present definition
      split at accepted
      · contradiction
      · rename_i incoming
        split at accepted
        · contradiction
        · rename_i current
          dsimp only at accepted
          split at accepted
          · contradiction
          · rename_i cap
            cases Except.ok.inj accepted
            exact ⟨rfl, rfl, position, Plan.presence_iff.mp definition,
              by simpa using incoming, by simpa using current, Nat.le_of_not_gt cap⟩
    · contradiction
  · contradiction

private theorem classifyFrom_wire {plan : Plan} {ceiling : Nat} {reps defs : List Nat}
    {start : State} {reversed : List Slot} {out : Classified}
    (accepted : classifyFrom plan ceiling start reps defs reversed = .ok out) :
    ∃ tail, out.levels = reversed.reverse ++ tail ∧ SlotsWire plan ceiling start reps defs tail out.after := by
  induction reps generalizing defs start reversed out with
  | nil =>
    cases defs with
    | cons => simp [classifyFrom] at accepted
    | nil =>
      cases Except.ok.inj accepted
      exact ⟨[], by simp, .nil start⟩
  | cons rep reps ih =>
    cases defs with
    | nil => simp [classifyFrom] at accepted
    | cons defn defs =>
      cases first : step plan ceiling start rep defn with
      | error => simp [classifyFrom, first, Bind.bind, Except.bind] at accepted
      | ok slot =>
        have rest : classifyFrom plan ceiling (start.consume slot) reps defs (slot :: reversed) = .ok out := by
          simpa [classifyFrom, first, Bind.bind, Except.bind] using accepted
        obtain ⟨tail, levelEq, wire⟩ := ih rest
        obtain ⟨repetition, definition, valid⟩ := step_wire first
        refine ⟨slot :: tail, ?_, ?_⟩
        · simpa [List.reverse_cons, List.append_assoc] using levelEq
        · simpa only [repetition, definition] using SlotsWire.cons valid wire

public theorem classify_wire {plan : Plan} {ceiling : Nat} {reps defs : List Nat}
    {start : State} {out : Classified} (accepted : classify plan ceiling start reps defs = .ok out) :
    SlotsWire plan ceiling start reps defs out.levels out.after := by
  obtain ⟨_, eq, wire⟩ := classifyFrom_wire accepted
  simpa [eq] using wire

public theorem original_levels {plan : Plan} {ceiling : Nat} {reps defs : List Nat}
    {start stop : State} {slots : List Slot} (wire : SlotsWire plan ceiling start reps defs slots stop) :
    slots.map (·.repetition) = reps ∧ slots.map (·.definition) = defs := by
  induction wire with
  | nil => simp
  | cons _ _ ih => simp [ih.1, ih.2]

public theorem slot_counts {plan : Plan} {ceiling : Nat} {reps defs : List Nat}
    {start stop : State} {slots : List Slot} (wire : SlotsWire plan ceiling start reps defs slots stop) :
    start.slots + slots.length = stop.slots ∧ start.rows + slots.countP Slot.startsRow = stop.rows := by
  induction wire with
  | nil => simp
  | @cons start slot reps defs tail stop _ _ ih =>
    obtain ⟨slots, rows⟩ := ih
    cases begins : slot.startsRow <;>
      simp [State.consume, begins] at slots rows ⊢ <;> omega

public theorem next_live {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) :
    (start.consume slot).live =
      if plan.innerEmpty < slot.definition then .inner
      else if plan.outerEmpty < slot.definition then .outer else .closed := by
  have definition := wire.definition
  obtain ⟨outer, inner, maximum⟩ := plan.thresholds
  cases presence : slot.presence <;>
    simp [presence, DefinitionWire] at definition <;>
    simp only [State.consume, presence, Presence.live] <;>
    (repeat' split) <;> simp_all <;> omega

public theorem row_start {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) : slot.startsRow = true ↔ slot.repetition = 0 := by
  have position := wire.position
  match rep : slot.repetition with
  | 0 | 1 | 2 =>
    simp [rep, Position.ofRep] at position
    simp [position.symm, Slot.startsRow]
  | n + 3 => simp [rep, Position.ofRep] at position

public theorem inner_start {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) (rep : slot.repetition = 1) :
    slot.position = .innerStart ∧ start.live ≠ .closed ∧ (start.consume slot).live ≠ .closed := by
  have position : slot.position = .innerStart := by simpa [rep, Position.ofRep] using wire.position.symm
  exact ⟨position, by simpa [position, Position.admits] using wire.incoming,
    by simpa [State.consume, position, Position.admits] using wire.current⟩

public theorem inner_continue {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) (rep : slot.repetition = 2) :
    slot.position = .innerContinue ∧ start.live = .inner ∧ (start.consume slot).live = .inner := by
  have position : slot.position = .innerContinue := by simpa [rep, Position.ofRep] using wire.position.symm
  exact ⟨position, by simpa [position, Position.admits] using wire.incoming,
    by simpa [State.consume, position, Position.admits] using wire.current⟩

public theorem repetition_count {plan : Plan} {ceiling : Nat} {start stop : State}
    {reps defs : List Nat} {slots : List Slot}
    (wire : SlotsWire plan ceiling start reps defs slots stop) :
    reps.countP (· == 0) = slots.countP Slot.startsRow := by
  induction wire with
  | nil => rfl
  | @cons start slot reps defs tail stop first _ ih =>
    have same : (slot.repetition == 0) = slot.startsRow := by
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq] using (row_start first).symm
    simp only [List.countP_cons, same, ih]

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk
