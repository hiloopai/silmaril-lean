module

public import Silmaril.Proofs.Wasm.Models.V2Core.Host

/-!
# 2.0 behaviours are Core 3.0 behaviours

* `invoke_sim`: the 2.0 entry configuration of an allocated address is simulated by the Core
  entry configuration on the image store (`Sim` of the copied
  `Silmaril/Raw/Wasm/Versions/V2/ToCore/Runtime.lean`);
* `behavioursOf_sub`: along any `Sim`, the 2.0 behaviours read in Core values are Core
  behaviours (`Steps.toCore`, `Sim.result`, `Diverges.toCore`);
* `behaviours_sub`: the entry-point form at every profile.

New proofs over the copied simulation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Execution (StoreWF HostCompatible Sim)

variable {H : Type}

/-- A 2.0 result read as a Core result has the translated behaviour. -/
theorem result_toBehaviour (r : Silmaril.Wasm.V2.Execution.Result) :
    Behaviour.map Silmaril.Wasm.V2.Execution.Val.toCore r.toBehaviour =
      (Silmaril.Wasm.V2.Execution.Result.toCore r).toBehaviour := by
  cases r <;> rfl

/-- **Behaviours along a simulation.** -/
theorem behavioursOf_sub {P : Profile} {src : VHost H} {tgt : CHost H}
    (hosts : HostCompatible src tgt) {a : Silmaril.Wasm.V2.Execution.Config H}
    {c : Silmaril.Wasm.Execution.Core.Config H} (hs : Sim a c) :
    Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behavioursOf P src a) ⊆
      Silmaril.Wasm.Execution.Core.behavioursOf P tgt c := by
  rintro _ ⟨b, ⟨a', r, hrun, hres, rfl⟩ | ⟨rfl, hdiv⟩, rfl⟩
  · obtain ⟨c₁, hrun₁, hs₁⟩ := Silmaril.Wasm.V2.Execution.Steps.toCore hosts hrun hs
    obtain ⟨c₂, hrun₂, -, -, hcode⟩ :=
      Silmaril.Wasm.V2.Execution.Sim.result (P := P) (tgt := tgt) hs₁ hres
    have hmem := Silmaril.Wasm.Execution.Core.mem_behavioursOf (hrun₁.trans hrun₂) hcode
    rwa [result_toBehaviour]
  · exact Or.inr ⟨rfl, Silmaril.Wasm.V2.Execution.Diverges.toCore hosts hdiv hs⟩

/-- The empty 2.0 frame is the erased empty Core frame. -/
theorem frame_empty :
    Silmaril.Wasm.V2.Execution.Frame.toCore ({} : Silmaril.Wasm.V2.Execution.Frame) =
      Silmaril.Wasm.V2.Execution.ToCore.Frame.erase {} := rfl

/-- The function type recorded at `a` by the image store. -/
theorem funcDefType_image {s : VStore H} {X : CStore H}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) (a : Nat) :
    Silmaril.Wasm.V2.Execution.Store.funcDefType s a =
      ((X.funcs[a]?).map Silmaril.Wasm.Execution.Core.FuncInst.type).getD default := by
  have hst : Silmaril.Wasm.V2.Execution.Store.toCore s =
      some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase X) := by
    rw [erase_of_toCore hX, hX]
  have h := Silmaril.Wasm.V2.Execution.ToCoreSim.bridge_funcs_type hst a
  simp only [Silmaril.Wasm.V2.Execution.Store.funcDefType]
  rw [← h]

/-- The Core image of the 2.0 entry code. -/
theorem invoke_code {s : VStore H} {X : CStore H}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) (a : Nat) (vs : List VVal) :
    Silmaril.Wasm.V2.Execution.Admin.listToCore s (Silmaril.Wasm.V2.Execution.invoke s a vs).code =
      some (Silmaril.Wasm.V2.Execution.ToCore.Admin.normList {}
        (Silmaril.Wasm.Execution.Core.invoke X a
          (vs.map Silmaril.Wasm.V2.Execution.Val.toCore)).code) := by
  have hc := Silmaril.Wasm.V2.Execution.ToCoreSim.listToCore_vals_append s vs
    (rest := [.callAddr a]) (L := [.ref (.func a),
      .callRefType (Silmaril.Wasm.V2.Execution.Store.funcDefType s a)]) (by simp [
        Silmaril.Wasm.V2.Execution.Admin.toCore])
  simp only [Silmaril.Wasm.V2.Execution.invoke, Silmaril.Wasm.Execution.Core.invoke]
  rw [hc, Silmaril.Wasm.V2.Execution.ToCore.Admin.normList_eq_map, List.map_append,
    Silmaril.Wasm.V2.Execution.ToCoreSim.map_norm_cvals, funcDefType_image hX]
  rfl

/-- **The entry configurations are simulated.** -/
theorem invoke_sim {s : VStore H} {X : CStore H} (hwf : StoreWF s)
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) {a : Nat}
    (ha : a < s.funcs.length) (vs : List VVal) :
    Sim (Silmaril.Wasm.V2.Execution.invoke s a vs)
      (Silmaril.Wasm.Execution.Core.invoke X a (vs.map Silmaril.Wasm.V2.Execution.Val.toCore)) := by
  have hcode := invoke_code hX a vs
  have hmod : Silmaril.Wasm.V2.Execution.ModWF s
      (Silmaril.Wasm.V2.Execution.invoke s a vs).frame.module := fun _ h => nomatch h
  have hlist : Silmaril.Wasm.V2.Execution.Admin.listWF s
      (Silmaril.Wasm.V2.Execution.invoke s a vs).code := by
    simp [Silmaril.Wasm.V2.Execution.invoke, Silmaril.Wasm.V2.Execution.Admin.listWF, ha]
  have hwfc : Silmaril.Wasm.V2.Execution.ConfigWF (Silmaril.Wasm.V2.Execution.invoke s a vs) :=
    ⟨hwf, hmod, hlist⟩
  refine ⟨?_, hwfc⟩
  simp only [Silmaril.Wasm.V2.Execution.Config.toCore, Silmaril.Wasm.V2.Execution.ToCore.Config.norm]
  rw [show (Silmaril.Wasm.V2.Execution.invoke s a vs).store = s from rfl, hX, Option.bind_some,
    hcode, Option.map_some,
    show (Silmaril.Wasm.Execution.Core.invoke X a
      (vs.map Silmaril.Wasm.V2.Execution.Val.toCore)).store = X from rfl, erase_of_toCore hX]
  rfl

/-- **2.0 behaviours of an allocated address are Core behaviours** of the image point, at every
profile. -/
theorem behaviours_sub (P : Profile) {s : VStore H} {src : VHost H} {X : CStore H}
    (hwf : StoreWF s) (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X)
    (hp : Silmaril.Wasm.V2.Execution.HostPreserves src) (hk : HostKeepsV src) {a : Nat}
    (ha : a < s.funcs.length) (vs : List VVal) :
    Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behaviours P src s a vs) ⊆
      Silmaril.Wasm.Execution.Core.behaviours P (liftHost src) X a
        (vs.map Silmaril.Wasm.V2.Execution.Val.toCore) :=
  behavioursOf_sub (compatible hp hk) (invoke_sim hwf hX ha vs)

end Silmaril.Proofs.Wasm.Models.V2Core
