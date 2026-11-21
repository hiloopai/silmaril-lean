module

public import Silmaril.Semantics.Arena.Traits.Cache.Defs
public import Silmaril.Semantics.Arena.Traits.Parsed.Thms

public section

namespace Silmaril.Proofs.Semantics.Arena.Traits.Cache

open Silmaril.Semantics
open Silmaril.Semantics.Arena.Traits
open Silmaril.Semantics.Arena.Traits.Cache

variable {Rep Model Key Name Obj Error Semantic Result : Type}
variable {bytes : Rep → Name → Option ByteArray}

theorem get_sound (getBacking : Rep → Name → Except Error (Option ByteArray))
    (sound : ∀ state name found, getBacking state name = .ok found → found = bytes state name)
    (layer : Layer bytes) (name : Name) (found : Option ByteArray) (read : layer.get getBacking name = .ok found) :
    found = bytes layer.backing name := by
  unfold Layer.get at read
  split at read
  · exact (Except.ok.inj read).symm.trans (layer.agrees _ _ ‹_›).symm
  · exact sound _ _ _ read

theorem get_exact (getBacking : Rep → Name → Except Error (Option ByteArray)) (layer : Layer bytes) (name : Name)
    (adequate : getBacking layer.backing name = .ok (bytes layer.backing name)) :
    layer.get getBacking name = getBacking layer.backing name := by
  unfold Layer.get
  split
  · rw [adequate, layer.agrees _ _ ‹_›]
  · rfl

theorem lift_refines {observe : Rep → Model} {edit : Step Rep Semantic Error Result}
    {spec : Arena.Mutable.Mutation Model Semantic Result} (refines : Step.Refines observe edit spec)
    (stable : ∀ state result next, edit state = .ok (result, next) →
      Naming.Subset (Naming.graph (bytes state)) (Naming.graph (bytes next))) :
    Step.Refines (fun layer : Layer bytes => observe layer.backing) (Layer.lift edit stable) spec := by
  intro layer
  have ref := refines layer.backing
  have projected : (Layer.lift edit stable layer).map (fun (result, next) => (result, next.backing)) = edit layer.backing := by
    unfold Layer.lift
    split <;> simp_all [Layer.advance, Except.map]
  rw [← projected] at ref
  cases compared : Layer.lift edit stable layer with
  | error fault => cases fault with
    | semantic fault => simpa [compared, Except.map] using ref
    | backend fault => trivial
  | ok result => simpa [compared, Except.map] using ref

variable [DecidableEq Key] [DecidableEq Name]
variable {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Arena.Cas.State Key Name Obj}

theorem plain_stable (refined : arena.Refines observe) (key : Key) (operation : Arena.Mutable.Change Obj)
    (state : Rep) (result : Unit) (next : Rep) (accepted : arena.toArena.change key operation state = .ok (result, next)) :
    Naming.Subset (Naming.graph (observe state).blocks) (Naming.graph (observe next).blocks) := by
  have raw := (refined.plain key operation).ok accepted
  unfold Arena.Cas.State.plain Arena.Cas.State.change at raw
  cases changed : Arena.Mutable.Access.raw.change key operation (observe state).slots with
  | error fault => simp [changed, Except.map] at raw
  | ok value =>
    have sameState : {observe state with slots := value.2} = observe next := by
      simpa [changed, Except.map] using raw
    have eq := congrArg Arena.Cas.State.blocks sameState
    rw [← eq]
    intro _ _ witness
    exact witness

theorem attach_stable (refined : arena.Refines observe) (key : Key) (name : Name)
    (state : Rep) (result : Unit) (next : Rep) (accepted : arena.attach key name state = .ok (result, next)) :
    Naming.Subset (Naming.graph (observe state).blocks) (Naming.graph (observe next).blocks) := by
  cases result
  obtain ⟨_, _, _, _, _, eq⟩ := refined.attach_effect accepted
  rw [eq]
  intro _ _ prior
  exact Or.inl prior

end Silmaril.Proofs.Semantics.Arena.Traits.Cache
