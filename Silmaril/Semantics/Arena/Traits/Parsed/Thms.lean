module

public import Silmaril.Semantics.Arena.Traits.Parsed.Defs
public import Silmaril.Semantics.Arena.Traits.Thms
import Silmaril.Proofs.Semantics.Arena.Traits.Parsed

public section

namespace Silmaril.Semantics.Arena.Traits.Parsed

open Silmaril.Semantics

variable {Rep Key Name Obj Error Semantic Result : Type}

theorem trusted_model [DecidableEq Key] [DecidableEq Name] (profile : Cas.Profile Name Obj) :
    Trusted (Traits.CasArena.model (Key := Key) profile) id profile.Valid :=
  ⟨Traits.CasArena.model_refines profile, fun _ valid => valid⟩

theorem CasArena.probe_agrees [DecidableEq Key] [DecidableEq Name]
    {arena : Traits.CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}
    (refined : arena.Refines observe) (state : Rep) :
    (probe arena state).Agrees (observe state).blocks := Proofs.Semantics.Arena.Traits.Parsed.probe_agrees refined state

theorem Source.absent_sound {source : Source Name Error} {reference : Name → Option ByteArray}
    (agrees : source.Agrees reference) {name : Name} (absent : source name = .absent) : reference name = none := by
  simpa [absent] using agrees name

/-- The default model inserts any native value at a vacant key, with no
serialization or naming assumptions and no change to the byte table. -/
theorem insert_model [DecidableEq Key] [DecidableEq Name] (profile : Cas.Profile Name Obj)
    (state : Cas.State Key Name Obj) (key : Key) (obj : Obj) (vacant : state.slots key = none) :
    let next : Cas.State Key Name Obj := {state with slots := state.slots.replaceAt key (some ⟨none, some obj⟩)}
    (Traits.CasArena.model profile).toArena.insert key obj state = .ok ((), next) ∧
      (Traits.CasArena.model profile).toArena.read next key = some (some obj) ∧ next.slots.keyName key = none :=
  Proofs.Semantics.Arena.Traits.Parsed.insert_model profile state key obj vacant

theorem verify_complete [DecidableEq Name] {profile : Cas.Profile Name Obj} {source : Source Name Error}
    {name : Name} {bytes : ByteArray} (fact : Fact profile source name bytes) :
    verify profile source name bytes = .ok ⟨fact⟩ := Proofs.Semantics.Arena.Traits.Parsed.verify_complete fact

theorem verifyAttachment_complete [DecidableEq Name] {arena : Traits.CasArena Rep Key Name Obj Error}
    {source : Source Name Error} {state : Rep} {key : Key} {name : Name} {bytes : ByteArray}
    (fact : AttachmentFact arena source state key name bytes) :
    verifyAttachment arena source state key name bytes = .ok ⟨fact⟩ :=
  Proofs.Semantics.Arena.Traits.Parsed.verifyAttachment_complete fact

theorem guard_ok {Evidence : Prop} {check : Except (Fault Name Error) (PLift Evidence)}
    {edit : Step Rep Semantic Error Result} {state next : Rep} {result : Result}
    (accepted : Parsed.guard check edit state = .ok (result, next)) :
    Evidence ∧ edit state = .ok (result, next) := Proofs.Semantics.Arena.Traits.Parsed.guard_ok accepted

/-- Rollback covers rejection, deferred verification, backend error and
collision. It is a statement about the pure commit, not physical IO. -/
theorem guard_rollback {Evidence : Prop} (check : Except (Fault Name Error) (PLift Evidence))
    (edit : Step Rep Semantic Error Result) (state : Rep) {fault : GateError Name Error Semantic}
    (failed : Parsed.guard check edit state = .error fault) :
    Mutable.Mutation.commit (Parsed.guard check edit) state = (.error fault, state) :=
  Proofs.Semantics.Arena.Traits.Parsed.guard_rollback check edit state failed

theorem put_agrees [DecidableEq Name] {arena : Traits.CasArena Rep Key Name Obj Error}
    {source : Source Name Error} {name : Name} {bytes : ByteArray} (fact : Fact arena.profile source name bytes)
    (state : Rep) : put arena source name bytes state = (arena.put bytes state).mapError Sum.inr := by
  rw [put, verify_complete fact]; rfl

theorem attach_agrees [DecidableEq Name] {arena : Traits.CasArena Rep Key Name Obj Error}
    {source : Source Name Error} {state : Rep} {key : Key} {name : Name} {bytes : ByteArray}
    (fact : AttachmentFact arena source state key name bytes) :
    attach arena source key name bytes state = (arena.attach key name state).mapError Sum.inr := by
  rw [attach, verifyAttachment_complete fact]; rfl

theorem put_exact [DecidableEq Key] [DecidableEq Name] {arena : Traits.CasArena Rep Key Name Obj Error}
    {observe : Rep → Cas.State Key Name Obj} (refined : arena.Refines observe) {source : Source Name Error}
    {state next : Rep} {name result : Name} {bytes : ByteArray}
    (accepted : put arena source name bytes state = .ok (result, next)) :
    Fact arena.profile source name bytes ∧ result = name ∧ (observe next).blocks name = some bytes :=
  Proofs.Semantics.Arena.Traits.Parsed.put_exact refined accepted

theorem attach_exact [DecidableEq Key] [DecidableEq Name] {arena : Traits.CasArena Rep Key Name Obj Error}
    {observe : Rep → Cas.State Key Name Obj} (refined : arena.Refines observe) {source : Source Name Error}
    {state next : Rep} {key : Key} {name : Name} {bytes : ByteArray}
    (accepted : attach arena source key name bytes state = .ok ((), next)) :
    AttachmentFact arena source state key name bytes ∧ (observe next).blocks name = some bytes :=
  Proofs.Semantics.Arena.Traits.Parsed.attach_exact refined accepted

end Silmaril.Semantics.Arena.Traits.Parsed
