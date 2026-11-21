module

public import Silmaril.Semantics.Arena.Traits.Publish.Defs
public import Silmaril.Semantics.Arena.Traits.Parsed.Thms
import Silmaril.Proofs.Semantics.Arena.Traits.Publish

public section

namespace Silmaril.Semantics.Arena.Traits.Publish

variable {Rep Key Name Obj Error : Type}

theorem Reserve.model_refines [DecidableEq Key] (key : Key) (name : Name) :
    Step.Refines id (Reserve.model (Obj := Obj) (Error := Error) key name) (reserveReference key name) :=
  Step.ofModel_refines _

theorem reserve_effect [DecidableEq Key] {key : Key} {name : Name} {before after : Cas.State Key Name Obj}
    (accepted : reserveReference key name before = .ok ((), after)) :
    before.slots key = none ∧ after.slots = before.slots.replaceAt key (some ⟨some name, none⟩) ∧
      after.blocks = before.blocks := Proofs.Semantics.Arena.Traits.Publish.reserve_effect accepted

theorem run_refines [DecidableEq Key] [DecidableEq Name]
    {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) (mode : Mode) (key : Key) (obj : Obj) (name : Name) :
    Step.Refines observe (run arena mode key obj name) (reference arena.profile mode key obj name) :=
  Proofs.Semantics.Arena.Traits.Publish.run_refines refined mode key obj name

theorem reference_effect [DecidableEq Key] [DecidableEq Name] {profile : Cas.Profile Name Obj}
    {mode : Mode} {key : Key} {obj : Obj} {name : Name} {before after : Cas.State Key Name Obj}
    (accepted : reference profile mode key obj name before = .ok ((), after)) :
    Effect profile before after key obj name ∧ (profile.Valid before → profile.Valid after) :=
  Proofs.Semantics.Arena.Traits.Publish.reference_effect accepted

theorem run_effect [DecidableEq Key] [DecidableEq Name]
    {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) {mode : Mode} {key : Key} {obj : Obj} {name : Name} {state next : Rep}
    (accepted : run arena mode key obj name state = .ok ((), next)) :
    Effect arena.profile (observe state) (observe next) key obj name ∧
      (arena.profile.Valid (observe state) → arena.profile.Valid (observe next)) :=
  reference_effect ((run_refines refined mode key obj name).ok accepted)

theorem Effect.readback [DecidableEq Key] {profile : Cas.Profile Name Obj} {before after : Cas.State Key Name Obj}
    {key : Key} {obj : Obj} {name : Name} {bytes : ByteArray} (effect : Effect profile before after key obj name)
    (encoded : profile.encode? obj = some bytes) :
    after.slots key = some ⟨some name, some obj⟩ ∧ after.blocks name = some bytes :=
  Proofs.Semantics.Arena.Traits.Publish.effect_readback effect encoded

theorem Effect.preserves [DecidableEq Key] {profile : Cas.Profile Name Obj} {before after : Cas.State Key Name Obj}
    {key : Key} {obj : Obj} {name : Name} (effect : Effect profile before after key obj name) :
    Naming.Subset (Naming.graph before.blocks) (Naming.graph after.blocks) :=
  let ⟨_, _, _, graph⟩ := effect; graph ▸ fun _ _ hit => Or.inl hit

theorem verify_complete [DecidableEq Name] {profile : Cas.Profile Name Obj} {source : Parsed.Source Name Error}
    {obj : Obj} {name : Name} {bytes : ByteArray} (fact : ValueFact profile source obj name bytes) :
    verifyValue profile source obj name bytes = .ok ⟨fact⟩ :=
  Proofs.Semantics.Arena.Traits.Publish.verify_complete fact

theorem checked_agrees [DecidableEq Name] {arena : CasArena Rep Key Name Obj Error}
    {source : Parsed.Source Name Error} {obj : Obj} {name : Name} {bytes : ByteArray}
    (fact : ValueFact arena.profile source obj name bytes) (mode : Mode) (key : Key) (state : Rep) :
    checked arena source mode key obj name bytes state = (run arena mode key obj name state).mapError Sum.inr := by
  rw [checked, verify_complete fact]; rfl

theorem checked_readback [DecidableEq Key] [DecidableEq Name]
    {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) {source : Parsed.Source Name Error} {mode : Mode}
    {key : Key} {obj : Obj} {name : Name} {bytes : ByteArray} {state next : Rep}
    (accepted : checked arena source mode key obj name bytes state = .ok ((), next)) :
    ValueFact arena.profile source obj name bytes ∧ (observe next).blocks name = some bytes := by
  obtain ⟨fact, committed⟩ := Parsed.guard_ok accepted
  exact ⟨fact, ((run_effect refined committed).1.readback fact.2).2⟩

theorem checked_get [DecidableEq Key] [DecidableEq Name]
    {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) {source : Parsed.Source Name Error} {mode : Mode}
    {key : Key} {obj : Obj} {name : Name} {bytes : ByteArray} {state next : Rep} {found : Option ByteArray}
    (accepted : checked arena source mode key obj name bytes state = .ok ((), next))
    (read : arena.get next name = .ok found) : found = some bytes :=
  (refined.get_eq _ _ _ read).trans (checked_readback refined accepted).2

/-- A fact checked against a different profile or name cannot justify this
commit when the exact observations required by the receiving profile fail. -/
theorem checked_rejects [DecidableEq Name] {arena : CasArena Rep Key Name Obj Error}
    {source : Parsed.Source Name Error} {mode : Mode} {key : Key} {obj : Obj} {name : Name}
    {bytes : ByteArray} {state : Rep} (invalid : ¬ ValueFact arena.profile source obj name bytes) :
    ∃ fault, (checked arena source mode key obj name bytes).commit state = (.error fault, state) := by
  cases attempted : checked arena source mode key obj name bytes state with
  | error fault => exact ⟨fault, Mutable.Mutation.commit_error attempted⟩
  | ok result => obtain ⟨⟨⟩, _⟩ := result; exact False.elim (invalid (Parsed.guard_ok attempted).1)

theorem rollback {edit : Mutable.Mutation Rep Error Unit} {state : Rep} {fault : Error}
    (failed : edit state = .error fault) : edit.commit state = (.error fault, state) :=
  Mutable.Mutation.commit_error failed

theorem reattach_idempotent [DecidableEq Key] [DecidableEq Name] {profile : Cas.Profile Name Obj}
    {state : Cas.State Key Name Obj} {key : Key} {obj : Obj} {name : Name} {bytes : ByteArray}
    (slot : state.slots key = some ⟨some name, some obj⟩) (valid : profile.Certifies name obj bytes)
    (prior : state.blocks name = some bytes) : profile.attach key name state = .ok ((), state) :=
  Proofs.Semantics.Arena.Traits.Publish.reattach_idempotent slot valid prior

end Silmaril.Semantics.Arena.Traits.Publish
