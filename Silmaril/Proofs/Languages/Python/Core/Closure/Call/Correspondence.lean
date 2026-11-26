module

public import Silmaril.Languages.Python.Core.Closure.Call.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Completion
public import Silmaril.Languages.Python.Core.Closure.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Call

open Silmaril.Languages.Python.Core.Closure Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout} {bindings : List (ParameterSlot layout × Value)}
  {before after : Environment layout}

theorem writes_sound (bound : writeArguments bindings before = .ok after) : Writes bindings before after := by
  induction bindings generalizing before after with
  | nil =>
    change Except.ok before = .ok after at bound
    cases bound
    exact .nil before
  | cons binding rest ih =>
    obtain ⟨slot, value⟩ := binding
    rw [writeArguments] at bound
    cases written : before.2.write before.1 slot.slot value with
    | error error => simp [written, Except.bind] at bound
    | ok middle =>
      rw [written] at bound
      exact .cons written (ih bound)

theorem writes_complete (bound : Writes bindings before after) : writeArguments bindings before = .ok after := by
  induction bound with
  | nil => rfl
  | cons step _ ih =>
    rw [writeArguments, step]
    exact ih

theorem bind_iff {parameters : Parameters layout} {arguments : List Value} :
    bindPositional parameters arguments before = .ok after ↔
      arguments.length = parameters.slots.length ∧ Writes (parameters.slots.zip arguments) before after := by
  by_cases arity : arguments.length = parameters.slots.length
  · simpa [bindPositional, arity] using
      (show writeArguments (parameters.slots.zip arguments) before = .ok after ↔
          Writes (parameters.slots.zip arguments) before after from ⟨writes_sound, writes_complete⟩)
  · simp [bindPositional, arity]

private theorem write_slots {slot : ParameterSlot layout} {value : Value}
    (write : before.2.write before.1 slot.slot value = .ok after) :
    after.2.owned = before.2.owned ∧ after.2.captures = before.2.captures := by
  cases slot with
  | «local» index =>
    change Except.ok (before.1,
      { before.2 with locals := fun i => if i = index then some value else before.2.locals i }) = .ok after at write
    cases write
    exact ⟨rfl, rfl⟩
  | owned index =>
    have same := (Frame.writeCell_spec
      (show before.2.writeCell before.1 (before.2.owned index) value = .ok after from write)).1
    exact ⟨congrArg Frame.owned same, congrArg Frame.captures same⟩

theorem writes_preserve_ids (bound : Writes bindings before after) :
    after.2.owned = before.2.owned ∧ after.2.captures = before.2.captures := by
  induction bound with
  | nil => exact ⟨rfl, rfl⟩
  | cons write _ tail =>
    have head := write_slots write
    exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

private theorem read_after_write {slot target : ParameterSlot layout} {value : Value}
    (write : before.2.write before.1 slot.slot value = .ok after)
    (unique : Function.Injective before.2.owned) :
    after.2.read after.1 target.slot =
      if target = slot then .ok value else before.2.read before.1 target.slot := by
  cases slot with
  | «local» index =>
    change Except.ok (before.1,
      { before.2 with locals := fun i => if i = index then some value else before.2.locals i }) =
        .ok after at write
    cases write
    cases target with
    | «local» other =>
      by_cases same : other = index
      · subst other
        simp [ParameterSlot.slot, Frame.read]
      · simp [ParameterSlot.slot, Frame.read, same]
    | owned other => simp [ParameterSlot.slot, Frame.read]
  | owned index =>
    obtain ⟨sameFrame, written⟩ := Frame.writeCell_spec
      (show before.2.writeCell before.1 (before.2.owned index) value = .ok (after.1, after.2) from write)
    obtain ⟨_, lookup, unchanged⟩ := Heap.write_spec written
    cases target with
    | «local» other => simp [ParameterSlot.slot, Frame.read, sameFrame]
    | owned other =>
      by_cases same : other = index
      · subst other
        simp [ParameterSlot.slot, Frame.read, Heap.read, sameFrame, lookup]
      · have different : before.2.owned other ≠ before.2.owned index := fun eq => same (unique eq)
        simp [ParameterSlot.slot, Frame.read, Heap.read, sameFrame, same, unchanged _ different]

private theorem writes_read_absent (bound : Writes bindings before after) (target : ParameterSlot layout)
    (absent : target ∉ bindings.map Prod.fst) (unique : Function.Injective before.2.owned) :
    after.2.read after.1 target.slot = before.2.read before.1 target.slot := by
  induction bound with
  | nil => rfl
  | @cons slot value rest before middle after write _ ih =>
    have different : target ≠ slot := fun eq => absent (List.mem_cons.mpr (.inl eq))
    have notInRest : target ∉ rest.map Prod.fst := fun mem => absent (List.mem_cons.mpr (.inr mem))
    have middleUnique : Function.Injective middle.2.owned := by rwa [(write_slots write).1]
    rw [ih notInRest middleUnique, read_after_write write unique, ite_eq_right different]

private theorem writes_read_bound (bound : Writes bindings before after)
    (distinct : (bindings.map Prod.fst).Nodup) (unique : Function.Injective before.2.owned)
    {slot : ParameterSlot layout} {value : Value} (member : (slot, value) ∈ bindings) :
    after.2.read after.1 slot.slot = .ok value := by
  induction bound with
  | nil => simp at member
  | @cons head arg rest before middle after write tail ih =>
    obtain ⟨notInRest, tailDistinct⟩ := List.nodup_cons.mp (by simpa only [List.map_cons] using distinct)
    have middleUnique : Function.Injective middle.2.owned := by rwa [(write_slots write).1]
    rcases List.mem_cons.mp member with equal | inRest
    · cases equal
      rw [writes_read_absent tail _ notInRest middleUnique, read_after_write write unique, ite_eq_left rfl]
    · exact ih tailDistinct middleUnique inRest

theorem bind_read {parameters : Parameters layout} {arguments : List Value}
    (bound : bindPositional parameters arguments before = .ok after)
    (unique : Function.Injective before.2.owned)
    {slot : ParameterSlot layout} {value : Value} (member : (slot, value) ∈ parameters.slots.zip arguments) :
    after.2.read after.1 slot.slot = .ok value := by
  obtain ⟨arity, writes⟩ := bind_iff.mp bound
  apply writes_read_bound writes _ unique member
  simpa [List.map_fst_zip, arity] using parameters.distinct

private theorem write_live (before : Environment layout) (slot : ParameterSlot layout) (value : Value)
    (live : ∀ index, (before.2.owned index).address < before.1.next) :
    ∃ after, before.2.write before.1 slot.slot value = .ok after ∧ after.1.next = before.1.next := by
  cases slot with
  | «local» index => exact ⟨_, rfl, rfl⟩
  | owned index =>
    simp only [ParameterSlot.slot, Frame.write, Frame.writeCell, Heap.write, ite_eq_left (live index)]
    exact ⟨_, rfl, rfl⟩

private theorem writes_live (bindings : List (ParameterSlot layout × Value)) (before : Environment layout)
    (live : ∀ index, (before.2.owned index).address < before.1.next) :
    ∃ after, Writes bindings before after := by
  induction bindings generalizing before with
  | nil => exact ⟨before, .nil before⟩
  | cons binding rest ih =>
    obtain ⟨slot, value⟩ := binding
    obtain ⟨middle, written, next⟩ := write_live before slot value live
    have stillLive : ∀ index, (middle.2.owned index).address < middle.1.next := by
      rwa [(write_slots written).1, next]
    obtain ⟨after, tail⟩ := ih middle stillLive
    exact ⟨after, .cons written tail⟩

private theorem write_preserves_lookup {slot : ParameterSlot layout} {value : Value} {identity : CellId}
    (write : before.2.write before.1 slot.slot value = .ok after)
    (outside : ∀ index, identity ≠ before.2.owned index) :
    after.1.lookup identity = before.1.lookup identity := by
  cases slot with
  | «local» index =>
    change Except.ok (before.1,
      { before.2 with locals := fun i => if i = index then some value else before.2.locals i }) =
        .ok after at write
    cases write
    rfl
  | owned index =>
    have written := (Frame.writeCell_spec
      (show before.2.writeCell before.1 (before.2.owned index) value = .ok (after.1, after.2) from write)).2
    exact (Heap.write_spec written).2.2 identity (outside index)

private theorem writes_preserve_lookup {identity : CellId} (bound : Writes bindings before after)
    (outside : ∀ index, identity ≠ before.2.owned index) :
    after.1.lookup identity = before.1.lookup identity := by
  induction bound with
  | nil => rfl
  | @cons slot value rest before middle after write tail ih =>
    have stillOutside : ∀ index, identity ≠ middle.2.owned index := by rwa [(write_slots write).1]
    exact (ih stillOutside).trans (write_preserves_lookup write outside)

variable {Continuation : Layout → Type} {fn : Function} {parameters : Parameters fn.code.layout}
  {arguments : List Value} {heap : Heap} {caller : Saved Continuation} {stack : List (Saved Continuation)}
  {callee : Entered Continuation fn.code.layout}

theorem enter_spec (entered : enter fn parameters arguments heap caller stack = .ok callee) :
    (∃ completed, completeArguments parameters fn.positionalDefaults arguments = .ok completed ∧
      bindPositional parameters completed (fn.freshFrame heap) = .ok callee.environment) ∧
      callee.stack = caller :: stack := by
  cases valid : firstDangling fn heap with
  | some identity => simp [enter, valid] at entered
  | none =>
    cases completion : completeArguments parameters fn.positionalDefaults arguments with
    | error error => simp [enter, valid, completion, Except.bind] at entered
    | ok completed =>
      cases binding : bindPositional parameters completed (fn.freshFrame heap) with
      | error error => simp [enter, valid, completion, binding, Except.bind, Except.map] at entered
      | ok initialized =>
        simp only [enter, valid, completion, binding, Except.bind, Except.map, Except.ok.injEq] at entered
        cases entered
        exact ⟨⟨completed, rfl, binding⟩, rfl⟩

theorem enter_captures_live (entered : enter fn parameters arguments heap caller stack = .ok callee)
    {identity : CellId} (captured : identity ∈ fn.captures.toList) : identity.address < heap.next := by
  have valid : firstDangling fn heap = none := by
    cases check : firstDangling fn heap with
    | none => rfl
    | some identity => simp [enter, check] at entered
  change fn.captures.toList.find? (fun cell => decide (heap.next ≤ cell.address)) = none at valid
  by_contra notLive
  have outside : heap.next ≤ identity.address := by omega
  exact (List.find?_eq_none.mp valid identity captured) (by simpa using outside)

theorem enter_complete {completed : List Value}
    (completion : completeArguments parameters fn.positionalDefaults arguments = .ok completed)
    (live : ∀ identity ∈ fn.captures.toList, identity.address < heap.next) :
    ∃ callee, enter fn parameters arguments heap caller stack = .ok callee := by
  have valid : firstDangling fn heap = none := by
    apply List.find?_eq_none.mpr
    intro identity member
    simp [Nat.not_le_of_lt (live identity member)]
  have freshlyAllocated (index : Fin fn.code.layout.owned) :
      ((fn.freshFrame heap).2.owned index).address < (fn.freshFrame heap).1.next := by
    change heap.next + index.val < heap.next + fn.code.layout.owned
    exact Nat.add_lt_add_left index.isLt _
  obtain ⟨initialized, writes⟩ := writes_live (parameters.slots.zip completed) _ freshlyAllocated
  have bound := bind_iff.mpr ⟨completeArguments_length completion, writes⟩
  exact ⟨⟨initialized, caller :: stack⟩, by simp [enter, valid, completion, bound, Except.bind, Except.map]⟩

theorem enter_preserves_cell (entered : enter fn parameters arguments heap caller stack = .ok callee)
    {identity : CellId} (live : identity.address < heap.next) :
    callee.environment.1.lookup identity = heap.lookup identity := by
  have outside (index : Fin fn.code.layout.owned) :
      identity ≠ (fn.freshFrame heap).2.owned index := by
    intro equal
    have address : identity.address = heap.next + index.val := congrArg CellId.address equal
    omega
  obtain ⟨_, _, bound⟩ := (enter_spec entered).1
  exact (writes_preserve_lookup (bind_iff.mp bound).2 outside).trans
    (Heap.lookup_reserve_old heap fn.code.layout.owned identity live)

end Silmaril.Proofs.Languages.Python.Core.Closure.Call
