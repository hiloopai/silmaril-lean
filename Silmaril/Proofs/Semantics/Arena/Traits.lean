module

public import Silmaril.Semantics.Arena.Traits.Defs
public import Silmaril.Semantics.Arena.Mutable.Thms
public import Silmaril.Semantics.Arena.Cas.Thms
public import Silmaril.Semantics.Naming.Admission.Thms

public section

open Silmaril.Semantics Silmaril.Semantics.Arena Silmaril.Semantics.Arena.Traits

namespace Silmaril.Proofs.Semantics.Arena.Traits

variable {Rep Model Key Name Obj Error Semantic Other Result Next : Type}

theorem ofModel_refines (edit : Mutable.Mutation Rep Semantic Result) :
    Step.Refines id (Step.ofModel (Error := Error) edit) edit := by
  intro state
  cases result : edit state with
  | error fault => simp [Step.ofModel, result, Except.mapError]
  | ok pair => cases pair; simp [Step.ofModel, result, Except.mapError]

theorem mapSemantic_refines {observe : Rep → Model} {edit : Step Rep Semantic Error Result}
    {spec : Mutable.Mutation Model Semantic Result} (refined : Step.Refines observe edit spec)
    (rename : Semantic → Other) :
    Step.Refines observe (Step.mapSemantic edit rename) (fun state => (spec state).mapError rename) := by
  intro state
  have law := refined state
  cases effect : edit state with
  | error fault =>
    cases fault <;> simp_all [Step.mapSemantic, Except.mapError]
  | ok pair =>
    obtain ⟨_, _⟩ := pair
    simp_all [Step.mapSemantic, Except.mapError]

theorem bind_refines {observe : Rep → Model} {edit : Step Rep Semantic Error Result}
    {spec : Mutable.Mutation Model Semantic Result} {next : Result → Step Rep Semantic Error Next}
    {specNext : Result → Mutable.Mutation Model Semantic Next} (first : Step.Refines observe edit spec)
    (second : ∀ result, Step.Refines observe (next result) (specNext result)) :
    Step.Refines observe (edit.bind next) (spec.bind specNext) := by
  intro state
  have law := first state
  cases effect : edit state with
  | error fault => cases fault <;> simp_all [Mutable.Mutation.bind, Except.bind]
  | ok pair =>
    obtain ⟨result, successor⟩ := pair
    simp only [effect] at law
    simpa [Mutable.Mutation.bind, effect, law, Except.bind] using second result successor

theorem dense_refines (limit : Nat) :
    (ArenaApi.dense (Name := Name) (Obj := Obj) limit).Refines (fun state => state.toBounded.val) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro key operation state
  by_cases inside : key < limit
  · have model := Mutable.Access.array_change_simulates state key operation inside
    cases effect : (Mutable.Access.array limit).change key operation state with
    | error fault => cases fault <;> simp_all [ArenaApi.dense, Except.map, Except.mapError]
    | ok pair =>
      obtain ⟨⟨⟩, _⟩ := pair
      simp_all [ArenaApi.dense, Except.map, Except.mapError]
  · have bounds := Mutable.Access.array_change_outside state key operation (Nat.le_of_not_gt inside)
    simp [ArenaApi.dense, bounds, Except.mapError]

theorem append_fresh : (Allocate.append (Name := Name) (Obj := Obj)).Fresh ArenaApi.growing := by
  intro payload state key next accepted
  obtain ⟨updated, step, size, vacant, resident, frame⟩ := Mutable.Growing.allocate_spec state payload
  rw [Allocate.append, step] at accepted
  simp only [Except.mapError, Except.ok.injEq, Prod.mk.injEq] at accepted
  obtain ⟨rfl, rfl⟩ := accepted
  refine ⟨vacant, resident, ?_⟩
  intro query different
  by_cases inside : query < state.1
  · exact frame query inside
  · have past : updated.1 ≤ query := by omega
    have oldPast : state.1 ≤ query := Nat.le_of_not_gt inside
    change (updated.2.toBounded.val query).map Slot.payload = (state.2.toBounded.val query).map Slot.payload
    rw [updated.2.toBounded.property query past, state.2.toBounded.property query oldPast]

theorem put_admitted [DecidableEq Name] {select? : ByteArray → Option Name} {bytes : ByteArray}
    {state next : Cas.State Key Name Obj} {name : Name} (accepted : putBytes select? bytes state = .ok (name, next)) :
    ∃ blocks, select? bytes = some name ∧ Naming.admit state.blocks [(name, bytes)] = .ok blocks ∧
      next = {state with blocks} := by
  cases selection : select? bytes with
  | none => simp [putBytes, selection] at accepted
  | some chosen =>
    cases admission : Naming.admit state.blocks [(chosen, bytes)] with
    | error conflict => simp [putBytes, selection, admission, Except.mapError] at accepted
    | ok blocks =>
      rw [show putBytes select? bytes state = .ok (chosen, {state with blocks}) by
        simp [putBytes, selection, admission, Except.mapError]] at accepted
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj accepted)
      exact ⟨blocks, rfl, admission, rfl⟩

theorem put_effect [DecidableEq Name] {select? : ByteArray → Option Name} {bytes : ByteArray}
    {state next : Cas.State Key Name Obj} {name : Name} (accepted : putBytes select? bytes state = .ok (name, next)) :
    select? bytes = some name ∧ next.slots = state.slots ∧ next.blocks name = some bytes ∧
      Naming.Subset (Naming.graph state.blocks) (Naming.graph next.blocks) := by
  obtain ⟨blocks, selected, admitted, rfl⟩ := put_admitted accepted
  have exactGraph := Naming.admit_eq_union admitted
  have written : Naming.graph blocks name bytes := exactGraph ▸ Or.inr (by simp [Naming.listed])
  exact ⟨selected, rfl, written, Naming.admit_preserves admitted⟩

theorem put_graph [DecidableEq Name] {select? : ByteArray → Option Name} {bytes : ByteArray}
    {state next : Cas.State Key Name Obj} {name : Name} (accepted : putBytes select? bytes state = .ok (name, next)) :
    Naming.graph next.blocks = Naming.union (Naming.graph state.blocks) (Naming.listed [(name, bytes)]) := by
  obtain ⟨_, _, admitted, rfl⟩ := put_admitted accepted
  exact Naming.admit_eq_union admitted

theorem put_valid [DecidableEq Name] {profile : Cas.Profile Name Obj} {bytes : ByteArray}
    {state next : Cas.State Key Name Obj} {name : Name} (valid : profile.Valid state)
    (accepted : putBytes profile.select? bytes state = .ok (name, next)) : profile.Valid next := by
  obtain ⟨_, slots, _, monotone⟩ := put_effect accepted
  intro key claimed obj attached
  obtain ⟨payload, certified, found⟩ := valid key claimed obj (slots ▸ attached)
  exact ⟨payload, certified, monotone found⟩

theorem put_collision [DecidableEq Name] (select? : ByteArray → Option Name) (bytes : ByteArray)
    (state : Cas.State Key Name Obj) (name : Name) : putBytes select? bytes state = .error (.collision name) ↔
      select? bytes = some name ∧ ∃ prior, state.blocks name = some prior ∧ prior ≠ bytes := by
  cases selection : select? bytes with
  | none => simp [putBytes, selection]
  | some chosen =>
    cases previous : state.blocks chosen with
    | none =>
      simp [putBytes, selection, Naming.admit, Naming.admitOne, previous, Except.mapError]
      rintro rfl
      simp [previous]
    | some prior =>
      by_cases same : prior = bytes
      · subst prior
        simp [putBytes, selection, Naming.admit, Naming.admitOne, previous, Except.mapError]
        rintro rfl
        simp [previous]
      · have actual : putBytes select? bytes state = .error (.collision chosen) := by
          simp [putBytes, selection, Naming.admit, Naming.admitOne, previous, same, Except.mapError]
        rw [actual]
        simp only [Except.error.injEq, PutFault.collision.injEq, Option.some.injEq]
        exact ⟨fun eq => ⟨eq, prior, eq ▸ previous, same⟩, And.left⟩

theorem plain_refines_slots [DecidableEq Key] [DecidableEq Name]
    {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) : arena.toArena.Refines (fun state => (observe state).slots) := by
  refine ⟨refined.read_eq, ?_⟩
  intro key operation state
  have slotLaw := Cas.State.plain_refines (observe state) key operation
  have fullLaw := refined.plain key operation state
  cases effect : arena.toArena.change key operation state with
  | error fault => cases fault <;> simp_all [Except.map]
  | ok pair => obtain ⟨⟨⟩, _⟩ := pair; simp_all [Except.map]

theorem replaceAndAttach_refines [DecidableEq Key] [DecidableEq Name]
    {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) (key : Key) (obj : Obj) (name : Name) :
    Step.Refines observe (arena.replaceAndAttach key obj name)
      (CasArena.replaceAndAttachReference arena.profile key obj name) :=
  bind_refines (mapSemantic_refines (refined.plain key (.replace obj)) Sum.inl)
    (fun _ => mapSemantic_refines (refined.attach_refines key name) Sum.inr)

theorem replace_reference_spec [DecidableEq Key] [DecidableEq Name] {profile : Cas.Profile Name Obj}
    {state next : Cas.State Key Name Obj} {key : Key} {obj : Obj} {name : Name}
    (valid : profile.Valid state)
    (accepted : CasArena.replaceAndAttachReference profile key obj name state = .ok ((), next)) :
    profile.Valid next ∧ Naming.Subset (Naming.graph state.blocks) (Naming.graph next.blocks) := by
  cases plain : Cas.State.plain.change key (.replace obj) state with
  | error fault =>
    simp [CasArena.replaceAndAttachReference, Mutable.Mutation.bind, plain, Except.mapError, Except.bind] at accepted
  | ok pair =>
    obtain ⟨⟨⟩, mid⟩ := pair
    obtain ⟨midValid, frame⟩ := Cas.State.plain_valid valid plain
    have attached : profile.attach key name mid = .ok ((), next) := by
      cases check : profile.attach key name mid <;>
        simp_all [CasArena.replaceAndAttachReference, Mutable.Mutation.bind, Except.mapError, Except.bind]
    have effect := Cas.Profile.attach_spec attached
    have nextValid := effect.valid midValid
    obtain ⟨_, _, _, _, _, graph⟩ := effect
    exact ⟨nextValid, fun query bytes found => graph ▸ Or.inl (frame ▸ found)⟩

end Silmaril.Proofs.Semantics.Arena.Traits
