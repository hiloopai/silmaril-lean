module

public import Silmaril.Semantics.Arena.Traits.Publish.Defs
public import Silmaril.Semantics.Arena.Traits.Parsed.Thms
public import Silmaril.Semantics.Arena.Mutable.Thms

public section

namespace Silmaril.Proofs.Semantics.Arena.Traits.Publish

open Silmaril.Semantics.Arena Silmaril.Semantics.Arena.Traits
open Silmaril.Semantics.Arena.Traits.Publish

variable {Rep Key Name Obj Error : Type} [DecidableEq Key] [DecidableEq Name]

theorem run_refines {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) (mode : Mode) (key : Key) (obj : Obj) (name : Name) :
    Step.Refines observe (run arena mode key obj name) (reference arena.profile mode key obj name) := by
  intro state
  unfold run reference
  rw [refined.read_eq, refined.name_eq]
  cases Mode.prepare mode (Cas.State.plain.read (observe state) key) ((observe state).slots.keyName key) obj name with
  | error fault => rfl
  | ok operation =>
    exact ((refined.plain key operation).mapSemantic Fault.slot |>.bind
      (fun _ => (refined.attach_refines key name).mapSemantic Fault.attachment)) state

private theorem prepare_operation {mode : Mode} {cell : Mutable.Cell Obj} {claim : Option Name}
    {obj : Obj} {name : Name} {operation : Mutable.Change Obj}
    (prepared : mode.prepare cell claim obj name = .ok operation) :
    operation = .insert obj ∨ operation = .replace obj := by
  cases mode with
  | insert => exact Or.inl (Except.ok.inj prepared).symm
  | fulfill =>
    cases cell with
    | none => simp [Mode.prepare] at prepared
    | some payload => cases payload <;> cases claim <;> simp [Mode.prepare] at prepared
                      split at prepared <;> simp_all

omit [DecidableEq Name] in
private theorem stage_slots {state mid : Cas.State Key Name Obj} {key : Key} {operation : Mutable.Change Obj}
    {obj : Obj} (prepared : operation = .insert obj ∨ operation = .replace obj)
    (staged : Cas.State.plain.change key operation state = .ok ((), mid)) :
    mid.slots = state.slots.replaceAt key (some ⟨none, some obj⟩) := by
  have projected := Cas.State.plain_refines state key operation
  rw [staged] at projected
  obtain ⟨localSlot, frame⟩ := Mutable.Access.raw_spec projected.symm
  have atKey : mid.slots key = some ⟨none, some obj⟩ := by
    rcases prepared with rfl | rfl <;> cases found : state.slots key <;>
      simp_all [Mutable.Change.apply, Edit.apply, Except.map]
  funext other
  by_cases same : key = other
  · subst other; simp [State.replaceAt, atKey]
  · simp [State.replaceAt, same, frame other same]

theorem reference_effect {profile : Cas.Profile Name Obj} {mode : Mode} {key : Key} {obj : Obj} {name : Name}
    {before after : Cas.State Key Name Obj}
    (accepted : reference profile mode key obj name before = .ok ((), after)) :
    Effect profile before after key obj name ∧ (profile.Valid before → profile.Valid after) := by
  unfold reference at accepted
  cases prepared : mode.prepare (Cas.State.plain.read before key) (before.slots.keyName key) obj name with
  | error fault => simp [prepared, Bind.bind, Except.bind] at accepted
  | ok operation =>
    cases staged : Cas.State.plain.change key operation before with
    | error fault => simp [prepared, staged, Mutable.Mutation.bind, Except.mapError, Bind.bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨⟨⟩, mid⟩ := pair
      have attached : profile.attach key name mid = .ok ((), after) := by
        cases check : profile.attach key name mid <;>
          simp_all [Mutable.Mutation.bind, Except.mapError, Bind.bind, Except.bind]
      have effect := Cas.Profile.attach_spec attached
      have fields := stage_slots (prepare_operation prepared) staged
      refine ⟨?_, fun valid => effect.valid (Cas.State.plain_valid valid staged).1⟩
      obtain ⟨resident, bytes, found, certifies, slots, graph⟩ := effect
      have same : obj = resident := by simpa [fields, State.replaceAt] using found
      have byteFrame : mid.blocks = before.blocks := by
        cases localEdit : Mutable.Access.raw.change key operation before.slots <;>
          simp [Cas.State.plain, Cas.State.change, localEdit, Except.map] at staged
        obtain ⟨⟨⟩, _⟩ := ‹Unit × State Key Name Obj›
        cases staged
        rfl
      subst resident
      refine ⟨bytes, certifies, ?_, byteFrame ▸ graph⟩
      rw [slots, fields]
      funext other
      by_cases same : key = other <;> simp [State.replaceAt, same]

omit [DecidableEq Name] in
theorem effect_readback {profile : Cas.Profile Name Obj} {before after : Cas.State Key Name Obj}
    {key : Key} {obj : Obj} {name : Name} {bytes : ByteArray} (effect : Effect profile before after key obj name)
    (encoded : profile.encode? obj = some bytes) :
    after.slots key = some ⟨some name, some obj⟩ ∧ after.blocks name = some bytes := by
  obtain ⟨actual, ⟨actualBytes, _⟩, slots, graph⟩ := effect
  obtain rfl := Option.some.inj (encoded.symm.trans actualBytes)
  refine ⟨by simp [slots, State.replaceAt], ?_⟩
  change Semantics.Naming.graph after.blocks name bytes
  rw [graph]
  exact Or.inr (by simp [Semantics.Naming.listed])

omit [DecidableEq Name] in
theorem reserve_effect {key : Key} {name : Name} {before after : Cas.State Key Name Obj}
    (accepted : reserveReference key name before = .ok ((), after)) :
    before.slots key = none ∧ after.slots = before.slots.replaceAt key (some ⟨some name, none⟩) ∧
      after.blocks = before.blocks := by
  cases prior : before.slots key <;>
    simp [reserveReference, State.step, Edit.apply, prior, Except.map] at accepted
  subst after
  exact ⟨rfl, rfl, rfl⟩

theorem verify_complete {profile : Cas.Profile Name Obj} {source : Parsed.Source Name Error}
    {obj : Obj} {name : Name} {bytes : ByteArray} (fact : ValueFact profile source obj name bytes) :
    verifyValue profile source obj name bytes = .ok ⟨fact⟩ := by
  obtain ⟨named, exactBytes⟩ := fact
  simp [verifyValue, Parsed.verify_complete named, Bind.bind, Except.bind, exactBytes]

theorem reattach_idempotent {profile : Cas.Profile Name Obj} {state : Cas.State Key Name Obj}
    {key : Key} {obj : Obj} {name : Name} {bytes : ByteArray}
    (slot : state.slots key = some ⟨some name, some obj⟩) (valid : profile.Certifies name obj bytes)
    (prior : state.blocks name = some bytes) : profile.attach key name state = .ok ((), state) := by
  obtain ⟨encoded, selected⟩ := valid
  have same : state.slots.replaceAt key (some ⟨some name, some obj⟩) = state.slots := by
    funext other
    by_cases eq : key = other
    · subst other; simp [State.replaceAt, slot]
    · simp [State.replaceAt, eq]
  simp [Cas.Profile.attach, Cas.Profile.validate, slot, encoded, selected, Bind.bind, Except.bind,
    Except.mapError, Semantics.Naming.admit, Semantics.Naming.admitOne, prior, same, Pure.pure, Except.pure]

end Silmaril.Proofs.Semantics.Arena.Traits.Publish
