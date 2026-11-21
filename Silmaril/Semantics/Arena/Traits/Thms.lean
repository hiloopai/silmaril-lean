module

public import Silmaril.Semantics.Arena.Traits.Defs
public import Silmaril.Semantics.Arena.Cas.Thms
public import Silmaril.Semantics.Naming.Admission.Thms
import Silmaril.Proofs.Semantics.Arena.Traits

public section

namespace Silmaril.Semantics.Arena.Traits

variable {Rep Model Key Name Obj Error Semantic Other Result Next : Type}

theorem Step.ofModel_refines (edit : Mutable.Mutation Rep Semantic Result) :
    Refines id (ofModel (Error := Error) edit) edit := Proofs.Semantics.Arena.Traits.ofModel_refines edit

theorem Step.Refines.ok {observe : Rep → Model} {edit : Step Rep Semantic Error Result}
    {spec : Mutable.Mutation Model Semantic Result} (refined : Refines observe edit spec)
    {state next : Rep} {result : Result} (accepted : edit state = .ok (result, next)) :
    spec (observe state) = .ok (result, observe next) := by
  simpa only [accepted] using refined state

theorem Step.Refines.semantic_error {observe : Rep → Model} {edit : Step Rep Semantic Error Result}
    {spec : Mutable.Mutation Model Semantic Result} (refined : Refines observe edit spec)
    {state : Rep} {fault : Semantic} (failed : edit state = .error (.semantic fault)) :
    spec (observe state) = .error fault := by
  simpa only [failed] using refined state

theorem Step.Refines.mapSemantic {observe : Rep → Model} {edit : Step Rep Semantic Error Result}
    {spec : Mutable.Mutation Model Semantic Result} (refined : Refines observe edit spec)
    (rename : Semantic → Other) :
    Refines observe (Step.mapSemantic edit rename) (fun state => (spec state).mapError rename) :=
  Proofs.Semantics.Arena.Traits.mapSemantic_refines refined rename

theorem Step.Refines.bind {observe : Rep → Model} {edit : Step Rep Semantic Error Result}
    {spec : Mutable.Mutation Model Semantic Result} {next : Result → Step Rep Semantic Error Next}
    {specNext : Result → Mutable.Mutation Model Semantic Next} (first : Refines observe edit spec)
    (second : ∀ result, Refines observe (next result) (specNext result)) :
    Refines observe (edit.bind next) (spec.bind specNext) :=
  Proofs.Semantics.Arena.Traits.bind_refines first second

theorem Step.rollback {edit : Step Rep Semantic Error Result} {state : Rep} {failure : Failure Semantic Error}
    (failed : edit state = .error failure) : edit.commit state = (.error failure, state) :=
  Mutable.Mutation.commit_error failed

theorem ArenaApi.raw_refines [DecidableEq Key] : (raw (Key := Key) (Name := Name) (Obj := Obj)).Refines id :=
  ⟨fun _ _ => rfl, fun key operation => Step.ofModel_refines (Mutable.Access.raw.change key operation)⟩

theorem ArenaApi.dense_refines (limit : Nat) :
    (dense (Name := Name) (Obj := Obj) limit).Refines (fun state => state.toBounded.val) :=
  Proofs.Semantics.Arena.Traits.dense_refines limit

theorem Allocate.append_fresh : (append (Name := Name) (Obj := Obj)).Fresh ArenaApi.growing :=
  Proofs.Semantics.Arena.Traits.append_fresh

theorem putBytes.graph_eq [DecidableEq Name] {select? : ByteArray → Option Name} {bytes : ByteArray}
    {state next : Cas.State Key Name Obj} {name : Name} (accepted : putBytes select? bytes state = .ok (name, next)) :
    Naming.graph next.blocks = Naming.union (Naming.graph state.blocks) (Naming.listed [(name, bytes)]) :=
  Proofs.Semantics.Arena.Traits.put_graph accepted

theorem putBytes.effect [DecidableEq Name] {select? : ByteArray → Option Name} {bytes : ByteArray}
    {state next : Cas.State Key Name Obj} {name : Name} (accepted : putBytes select? bytes state = .ok (name, next)) :
    select? bytes = some name ∧ next.slots = state.slots ∧ next.blocks name = some bytes ∧
      Naming.Subset (Naming.graph state.blocks) (Naming.graph next.blocks) :=
  Proofs.Semantics.Arena.Traits.put_effect accepted

theorem putBytes.collision_iff [DecidableEq Name] (select? : ByteArray → Option Name) (bytes : ByteArray)
    (state : Cas.State Key Name Obj) (name : Name) : putBytes select? bytes state = .error (.collision name) ↔
    select? bytes = some name ∧ ∃ prior, state.blocks name = some prior ∧ prior ≠ bytes :=
  Proofs.Semantics.Arena.Traits.put_collision select? bytes state name

namespace CasArena

variable [DecidableEq Key] [DecidableEq Name]

theorem model_refines (profile : Cas.Profile Name Obj) : (model (Key := Key) profile).Refines id :=
  ⟨fun _ _ => Step.ofModel_refines _, fun _ _ => rfl, fun _ _ _ eq => (Except.ok.inj eq).symm,
    fun _ _ => rfl, fun _ _ => rfl, fun _ => Step.ofModel_refines _, fun _ _ => Step.ofModel_refines _⟩

variable {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}

theorem Refines.plain_slots (refined : arena.Refines observe) : arena.toArena.Refines (fun state => (observe state).slots) :=
  Proofs.Semantics.Arena.Traits.plain_refines_slots refined

theorem Refines.plain_valid (refined : arena.Refines observe) {state next : Rep} {key : Key}
    {operation : Mutable.Change Obj} (valid : arena.profile.Valid (observe state))
    (accepted : arena.toArena.change key operation state = .ok ((), next)) :
    arena.profile.Valid (observe next) ∧ (observe next).blocks = (observe state).blocks :=
  Cas.State.plain_valid valid ((refined.plain key operation).ok accepted)

theorem Refines.put_effect (refined : arena.Refines observe) {state next : Rep} {bytes : ByteArray} {name : Name}
    (accepted : arena.put bytes state = .ok (name, next)) :
    arena.profile.select? bytes = some name ∧ (observe next).slots = (observe state).slots ∧
      (observe next).blocks name = some bytes ∧ Naming.Subset (Naming.graph (observe state).blocks)
        (Naming.graph (observe next).blocks) :=
  putBytes.effect ((refined.put_refines bytes).ok accepted)

theorem Refines.put_readback (refined : arena.Refines observe) {state next : Rep} {bytes : ByteArray} {name : Name}
    (accepted : arena.put bytes state = .ok (name, next)) {found : Option ByteArray}
    (read : arena.get next name = .ok found) : found = some bytes :=
  (refined.get_eq _ _ _ read).trans (refined.put_effect accepted).2.2.1

theorem Refines.put_valid (refined : arena.Refines observe) {state next : Rep} {bytes : ByteArray} {name : Name}
    (valid : arena.profile.Valid (observe state)) (accepted : arena.put bytes state = .ok (name, next)) :
    arena.profile.Valid (observe next) :=
  Proofs.Semantics.Arena.Traits.put_valid valid ((refined.put_refines bytes).ok accepted)

theorem Refines.attach_effect (refined : arena.Refines observe) {state next : Rep} {key : Key} {name : Name}
    (accepted : arena.attach key name state = .ok ((), next)) :
    arena.profile.Attached (observe state) (observe next) key name :=
  Cas.Profile.attach_spec ((refined.attach_refines key name).ok accepted)

theorem Refines.attach_valid (refined : arena.Refines observe) {state next : Rep} {key : Key} {name : Name}
    (valid : arena.profile.Valid (observe state)) (accepted : arena.attach key name state = .ok ((), next)) :
    arena.profile.Valid (observe next) := (refined.attach_effect accepted).valid valid

theorem Refines.replaceAndAttach (refined : arena.Refines observe) (key : Key) (obj : Obj) (name : Name) :
    Step.Refines observe (arena.replaceAndAttach key obj name)
      (replaceAndAttachReference arena.profile key obj name) :=
  Proofs.Semantics.Arena.Traits.replaceAndAttach_refines refined key obj name

theorem Refines.replace_valid (refined : arena.Refines observe) {state next : Rep} {key : Key} {obj : Obj} {name : Name}
    (valid : arena.profile.Valid (observe state)) (accepted : arena.replaceAndAttach key obj name state = .ok ((), next)) :
    arena.profile.Valid (observe next) ∧ Naming.Subset (Naming.graph (observe state).blocks)
      (Naming.graph (observe next).blocks) :=
  Proofs.Semantics.Arena.Traits.replace_reference_spec valid ((refined.replaceAndAttach key obj name).ok accepted)

end CasArena

end Silmaril.Semantics.Arena.Traits
