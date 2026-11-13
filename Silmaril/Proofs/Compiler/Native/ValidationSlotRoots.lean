module

public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Defs
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Slots
open Silmaril.Machine Silmaril.Compile
open Validation.Roots

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

/-- Slot writes retain partiality of every other actual slot and every register. -/
theorem writeSlot_rooted (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (dest index : Nat) (word : Lir.Word)
    (bounded : index < state.nodes.size) (selected : meaning.value index = some word) :
    Rooted ((writeSlot dest index).run state).2 (frame.setSlot dest word) meaning := by
  change Rooted { state with slots := (dest, index) :: state.slots.filter (·.1 != dest) }
    (frame.setSlot dest word) meaning
  refine ⟨rooted.wellScoped, rooted.coherent, rooted.regsBounded, ?_, rooted.regs, ?_⟩
  · intro root member
    change root ∈ (dest, index) :: state.slots.filter (·.1 != dest) at member
    rcases List.mem_cons.mp member with equal | filtered
    · subst root
      exact bounded
    · exact rooted.slotsBounded root (List.mem_filter.mp filtered).1
  · intro slot
    simp only [slotValue, find_updated, Lir.Frame.setSlot]
    by_cases same : slot = dest
    · simp [same, selected]
    · simpa [same, slotValue] using rooted.slots slot

/-- A shared extended DAG reinterprets the same old partial root maps. -/
theorem rooted_replace_nodes (before after : State) (beforeFrame afterFrame : Lir.Frame Nat)
    (oldMeaning newMeaning : Interpretation) (beforeRooted : Rooted before beforeFrame oldMeaning)
    (afterRooted : Rooted after afterFrame newMeaning)
    (extension : Extends before.nodes.size oldMeaning newMeaning) (grows : before.nodes.size ≤ after.nodes.size) :
    Rooted { before with nodes := after.nodes } beforeFrame newMeaning := by
  refine ⟨afterRooted.wellScoped, afterRooted.coherent, ?_, ?_, ?_, ?_⟩
  · intro root member
    exact Nat.lt_of_lt_of_le (beforeRooted.regsBounded root member) grows
  · intro root member
    exact Nat.lt_of_lt_of_le (beforeRooted.slotsBounded root member) grows
  · intro reg
    exact (regValue_preserved rfl beforeRooted.regsBounded extension reg).trans (beforeRooted.regs reg)
  · intro slot
    exact (slotValue_preserved rfl beforeRooted.slotsBounded extension slot).trans (beforeRooted.slots slot)

/-- Slot comparison retains each option, including missing untouched slots;
there is no successful-concrete-slot-read premise. -/
theorem readSlots_partial (slots : List Nat) (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) :
    ∃ newMeaning, PartialSlotReads state ((slots.mapM readSlot).run state).2 frame slots
      ((slots.mapM readSlot).run state).1 meaning newMeaning := by
  induction slots generalizing state meaning with
  | nil =>
    exact ⟨meaning, ⟨rooted, .refl _ _, Nat.le_refl _, rfl⟩, (fun _ member => nomatch member), rfl⟩
  | cons slot rest ih =>
    show ∃ newMeaning, PartialSlotReads state (((slot :: rest).mapM readSlot).run state).2 frame (slot :: rest)
      (((slot :: rest).mapM readSlot).run state).1 meaning newMeaning
    let first := (readSlot slot).run state
    let tail := (rest.mapM readSlot).run first.2
    obtain ⟨middleMeaning, firstRead⟩ := Validation.Roots.readSlot_sound state frame meaning rooted slot
    obtain ⟨newMeaning, tailRead⟩ := ih first.2 middleMeaning firstRead.rooted
    have firstBound : first.1 < tail.2.nodes.size := Nat.lt_of_lt_of_le firstRead.bounded tailRead.result.grows
    have firstSelected : newMeaning.value first.1 = frame.slots slot :=
      (tailRead.result.extension.values first.1 firstRead.bounded).trans firstRead.selected
    refine ⟨newMeaning, ?_⟩
    rw [Observation.mapM_cons_run]
    refine ⟨Lists.result_trans (Observation.read_result firstRead) tailRead.result, ?_, ?_⟩
    · intro index member
      rcases List.mem_cons.mp member with equal | later
      · subst index
        exact firstBound
      · exact tailRead.bounded index later
    · change (first.1 :: tail.1).map newMeaning.value = (slot :: rest).map frame.slots
      have tailSelected : tail.1.map newMeaning.value = rest.map frame.slots := tailRead.selected
      simp only [List.map_cons, firstSelected, tailSelected]

private theorem find_slot_none (state : State) (slot : Nat) (outside : slot ∉ state.slots.map Prod.fst) :
    state.slots.find? (·.1 == slot) = none := by
  apply List.find?_eq_none.mpr
  intro root member
  have different : root.1 ≠ slot := by
    intro same
    exact outside (same ▸ List.mem_map.mpr ⟨root, member, rfl⟩)
  simpa only [beq_iff_eq] using different

/-- The actual checker's final symbolic slot-root comparison establishes
whole-slot agreement even when source and candidate have different write maps
and partial untouched slots. -/
theorem states_slots_agree (sourceState candidateState : State) (sourceFrame candidateFrame : Lir.Frame Nat)
    (sourceMeaning candidateMeaning : Interpretation)
    (sourceRooted : Rooted sourceState sourceFrame sourceMeaning)
    (candidateRooted : Rooted candidateState candidateFrame candidateMeaning)
    (extension : Extends sourceState.nodes.size sourceMeaning candidateMeaning)
    (grows : sourceState.nodes.size ≤ candidateState.nodes.size)
    (accepted :
      let slots := (sourceState.slots.map Prod.fst ++ candidateState.slots.map Prod.fst).dedup
      let sourceRead := (slots.mapM readSlot).run { sourceState with nodes := candidateState.nodes }
      let candidateRead := (slots.mapM readSlot).run { candidateState with nodes := sourceRead.2.nodes }
      sourceRead.1 = candidateRead.1) : candidateFrame.slots = sourceFrame.slots := by
  let slots := (sourceState.slots.map Prod.fst ++ candidateState.slots.map Prod.fst).dedup
  let sourceRead := (slots.mapM readSlot).run { sourceState with nodes := candidateState.nodes }
  let candidateRead := (slots.mapM readSlot).run { candidateState with nodes := sourceRead.2.nodes }
  have sourceLift : Rooted { sourceState with nodes := candidateState.nodes } sourceFrame candidateMeaning :=
    rooted_replace_nodes sourceState candidateState sourceFrame candidateFrame sourceMeaning candidateMeaning
      sourceRooted candidateRooted extension grows
  obtain ⟨middleMeaning, sourceReads⟩ := readSlots_partial slots _ sourceFrame candidateMeaning sourceLift
  have candidateLift : Rooted { candidateState with nodes := sourceRead.2.nodes } candidateFrame middleMeaning :=
    rooted_replace_nodes candidateState sourceRead.2 candidateFrame sourceFrame candidateMeaning middleMeaning
      candidateRooted sourceReads.result.rooted sourceReads.result.extension sourceReads.result.grows
  obtain ⟨finalMeaning, candidateReads⟩ := readSlots_partial slots _ candidateFrame middleMeaning candidateLift
  have retained : sourceRead.1.map finalMeaning.value = sourceRead.1.map middleMeaning.value := by
    apply List.map_congr_left
    intro index member
    exact candidateReads.result.extension.values index (sourceReads.bounded index member)
  have actualSame : sourceRead.1 = candidateRead.1 := accepted
  have maps : slots.map sourceFrame.slots = slots.map candidateFrame.slots := by
    calc
      slots.map sourceFrame.slots = sourceRead.1.map middleMeaning.value := sourceReads.selected.symm
      _ = sourceRead.1.map finalMeaning.value := retained.symm
      _ = candidateRead.1.map finalMeaning.value := congrArg (List.map finalMeaning.value) actualSame
      _ = slots.map candidateFrame.slots := candidateReads.selected
  funext slot
  by_cases tracked : slot ∈ slots
  · exact (List.map_inj_left.mp maps slot tracked).symm
  · have sourceOutside : slot ∉ sourceState.slots.map Prod.fst := by
      intro member
      exact tracked (by simp only [slots, List.mem_dedup, List.mem_append]; exact Or.inl member)
    have candidateOutside : slot ∉ candidateState.slots.map Prod.fst := by
      intro member
      exact tracked (by simp only [slots, List.mem_dedup, List.mem_append]; exact Or.inr member)
    have sourceValue : candidateMeaning.slot slot = sourceFrame.slots slot := by
      simpa only [slotValue, find_slot_none sourceState slot sourceOutside] using sourceLift.slots slot
    have candidateValue : candidateMeaning.slot slot = candidateFrame.slots slot := by
      simpa only [slotValue, find_slot_none candidateState slot candidateOutside] using candidateRooted.slots slot
    exact candidateValue.symm.trans sourceValue


end Silmaril.Compiler.Native.Optimize.Validation.Slots
