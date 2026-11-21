module

public import Silmaril.Semantics.Arena.Traits.Cache.Defs
public import Silmaril.Semantics.Arena.Traits.Parsed.Thms
import Silmaril.Proofs.Semantics.Arena.Traits.Cache

public section

namespace Silmaril.Semantics.Arena.Traits.Cache

open Silmaril.Semantics

variable {Rep Key Name Obj Error : Type} {bytes : Rep → Name → Option ByteArray}

theorem Layer.probe_agrees (layer : Layer bytes) : (layer.probe).Agrees (bytes layer.backing) := by
  intro name
  cases found : layer.hot name <;> simp [Layer.probe, found, layer.agrees]

theorem Layer.probe_evict [DecidableEq Name] (layer : Layer bytes) (name : Name) :
    (layer.evict name).probe name = .unavailable () := by simp [Layer.probe, Layer.evict]

theorem Layer.get_sound (getBacking : Rep → Name → Except Error (Option ByteArray))
    (sound : ∀ state name found, getBacking state name = .ok found → found = bytes state name)
    (layer : Layer bytes) (name : Name) (found : Option ByteArray) (read : layer.get getBacking name = .ok found) :
    found = bytes layer.backing name := Proofs.Semantics.Arena.Traits.Cache.get_sound getBacking sound layer name found read

theorem Layer.get_exact (getBacking : Rep → Name → Except Error (Option ByteArray)) (layer : Layer bytes) (name : Name)
    (adequate : getBacking layer.backing name = .ok (bytes layer.backing name)) :
    layer.get getBacking name = getBacking layer.backing name :=
  Proofs.Semantics.Arena.Traits.Cache.get_exact getBacking layer name adequate

theorem Layer.evict_get_exact [DecidableEq Name] (getBacking : Rep → Name → Except Error (Option ByteArray))
    (layer : Layer bytes) (evicted queried : Name)
    (adequate : getBacking layer.backing queried = .ok (bytes layer.backing queried)) :
    (layer.evict evicted).get getBacking queried = layer.get getBacking queried :=
  ((layer.evict evicted).get_exact getBacking queried adequate).trans (layer.get_exact getBacking queried adequate).symm

variable [DecidableEq Key] [DecidableEq Name]
variable {arena : CasArena Rep Key Name Obj Error} {observe : Rep → Cas.State Key Name Obj}

theorem plain_retains (refined : arena.Refines observe) (key : Key) (operation : Mutable.Change Obj)
    (state : Rep) (result : Unit) (next : Rep) (accepted : arena.toArena.change key operation state = .ok (result, next)) :
    Naming.Subset (Naming.graph (observe state).blocks) (Naming.graph (observe next).blocks) :=
  Proofs.Semantics.Arena.Traits.Cache.plain_stable refined key operation state result next accepted

theorem attach_retains (refined : arena.Refines observe) (key : Key) (name : Name)
    (state : Rep) (result : Unit) (next : Rep) (accepted : arena.attach key name state = .ok (result, next)) :
    Naming.Subset (Naming.graph (observe state).blocks) (Naming.graph (observe next).blocks) :=
  Proofs.Semantics.Arena.Traits.Cache.attach_stable refined key name state result next accepted

/-- An optional read-through implementation of the same `CasArena`.
Backing mutation is not delegated to the cache. By refinement, every
successful edit retains old byte bindings, so old hot hits stay exact. -/
@[expose] def withCache (refined : arena.Refines observe) :
    CasArena (Layer (fun state => (observe state).blocks)) Key Name Obj Error where
  toArena := ⟨fun layer => arena.toArena.read layer.backing,
    fun key operation => Layer.lift (arena.toArena.change key operation) (plain_retains refined key operation)⟩
  profile := arena.profile
  get := Layer.get arena.get
  keyName layer := arena.keyName layer.backing
  attachedKeys layer := arena.attachedKeys layer.backing
  put wire := Layer.lift (arena.put wire) fun _ _ _ accepted => (refined.put_effect accepted).2.2.2
  attach key name := Layer.lift (arena.attach key name) (attach_retains refined key name)

open Proofs.Semantics.Arena.Traits.Cache in
theorem withCache_refines (refined : arena.Refines observe) :
    (withCache refined).Refines (fun layer => observe layer.backing) :=
  ⟨fun key op => lift_refines (refined.plain key op) (plain_retains refined key op), fun layer => refined.read_eq layer.backing,
    Layer.get_sound arena.get refined.get_eq, fun layer => refined.name_eq layer.backing,
    fun layer => refined.keys_eq layer.backing,
    fun wire => lift_refines (refined.put_refines wire) fun _ _ _ accepted => (refined.put_effect accepted).2.2.2,
    fun key name => lift_refines (refined.attach_refines key name) (attach_retains refined key name)⟩

end Silmaril.Semantics.Arena.Traits.Cache
