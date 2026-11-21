module

public import Silmaril.Semantics.Arena.Traits.Parsed.Defs
public import Silmaril.Semantics.Arena.Traits.Thms

public section

namespace Silmaril.Proofs.Semantics.Arena.Traits.Parsed

open Silmaril.Semantics.Arena
open Silmaril.Semantics.Arena.Traits
open Silmaril.Semantics.Arena.Traits.Parsed
open Silmaril.Semantics

variable {Rep Key Name Obj Error Semantic Result : Type}

theorem probe_agrees [DecidableEq Key] [DecidableEq Name]
    {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) (state : Rep) :
    (Parsed.CasArena.probe arena state).Agrees (observe state).blocks := by
  intro name
  cases read : arena.get state name with
  | error reason => simp [Parsed.CasArena.probe, read]
  | ok result => cases result <;> simpa [Parsed.CasArena.probe, read] using (refined.get_eq _ _ _ read).symm

theorem insert_model [DecidableEq Key] [DecidableEq Name] (profile : Cas.Profile Name Obj)
    (state : Cas.State Key Name Obj) (key : Key) (obj : Obj) (vacant : state.slots key = none) :
    let next : Cas.State Key Name Obj := {state with slots := state.slots.replaceAt key (some ⟨none, some obj⟩)}
    (CasArena.model profile).toArena.insert key obj state = .ok ((), next) ∧
      (CasArena.model profile).toArena.read next key = some (some obj) ∧ next.slots.keyName key = none := by
  simp [ArenaApi.insert, CasArena.model, ArenaApi.ofAccess, Step.ofModel, Cas.State.plain, Cas.State.change,
    Mutable.Access.raw, Mutable.Access.ofSlots, Mutable.Change.run, State.step, Edit.apply, vacant,
    State.replaceAt, State.keyName, Except.bind, Except.map, Except.mapError]
  funext other
  by_cases eq : key = other <;> simp [State.replaceAt, eq]

theorem verify_complete [DecidableEq Name] {profile : Cas.Profile Name Obj} {source : Source Name Error}
    {name : Name} {bytes : ByteArray} (fact : Fact profile source name bytes) :
    verify profile source name bytes = .ok ⟨fact⟩ := by
  have observed := fact.observed
  have selected := fact.selected
  unfold verify
  split <;> simp_all only [Observation.present.injEq, reduceCtorEq]
  simp only [dite_true]
  split <;> simp_all

theorem verifyAttachment_complete [DecidableEq Name] {arena : CasArena Rep Key Name Obj Error}
    {source : Source Name Error} {state : Rep} {key : Key} {name : Name} {bytes : ByteArray}
    (fact : AttachmentFact arena source state key name bytes) :
    verifyAttachment arena source state key name bytes = .ok ⟨fact⟩ := by
  obtain ⟨obj, resident, encoded⟩ := fact.resident
  unfold verifyAttachment
  rw [verify_complete fact.fact]
  change (match seen : arena.toArena.read state key with
    | none => _
    | some none => _
    | some (some _) => _) = _
  split <;> simp_all
  split <;> try simp_all
  split <;> simp_all

theorem guard_ok {Evidence : Prop} {check : Except (Fault Name Error) (PLift Evidence)}
    {edit : Step Rep Semantic Error Result} {state next : Rep} {result : Result}
    (accepted : guard check edit state = .ok (result, next)) :
    Evidence ∧ edit state = .ok (result, next) := by
  cases check with
  | error fault => cases accepted
  | ok evidence =>
    refine ⟨evidence.down, ?_⟩
    cases outcome : edit state with
    | error fault => simp [Parsed.guard, outcome, Except.mapError] at accepted
    | ok value => simpa [Parsed.guard, outcome, Except.mapError] using accepted

theorem guard_rollback {Evidence : Prop} (check : Except (Fault Name Error) (PLift Evidence))
    (edit : Step Rep Semantic Error Result) (state : Rep) {fault : GateError Name Error Semantic}
    (failed : guard check edit state = .error fault) :
    Mutable.Mutation.commit (guard check edit) state = (.error fault, state) := by
  simp [Mutable.Mutation.commit, failed]

theorem put_exact [DecidableEq Key] [DecidableEq Name] {arena : CasArena Rep Key Name Obj Error}
    {observe : Rep → Cas.State Key Name Obj} (refined : arena.Refines observe) {source : Source Name Error}
    {state next : Rep} {name result : Name} {bytes : ByteArray}
    (accepted : put arena source name bytes state = .ok (result, next)) :
    Fact arena.profile source name bytes ∧ result = name ∧ (observe next).blocks name = some bytes := by
  obtain ⟨fact, committed⟩ := guard_ok accepted
  obtain ⟨selected, _, readback, _⟩ := refined.put_effect committed
  have equal := Option.some.inj (selected.symm.trans fact.selected)
  exact ⟨fact, equal, equal ▸ readback⟩

theorem attach_exact [DecidableEq Key] [DecidableEq Name] {arena : CasArena Rep Key Name Obj Error}
    {observe : Rep → Cas.State Key Name Obj} (refined : arena.Refines observe) {source : Source Name Error}
    {state next : Rep} {key : Key} {name : Name} {bytes : ByteArray}
    (accepted : attach arena source key name bytes state = .ok ((), next)) :
    AttachmentFact arena source state key name bytes ∧ (observe next).blocks name = some bytes := by
  obtain ⟨checked, committed⟩ := guard_ok accepted
  obtain ⟨obj, resident, encoded⟩ := checked.resident
  have attached := refined.attach_effect committed
  obtain ⟨old, prior, atKey, certified, _, graph⟩ := attached
  have same : old = obj := by
    rw [refined.read_eq] at resident
    exact Option.some.inj (Option.some.inj (atKey.symm.trans resident))
  have exactPrior : prior = bytes := Option.some.inj (certified.1.symm.trans (same ▸ encoded))
  refine ⟨checked, ?_⟩
  change Naming.graph (observe next).blocks name bytes
  rw [graph, exactPrior]
  exact Or.inr (by simp [Naming.listed])

end Silmaril.Proofs.Semantics.Arena.Traits.Parsed
