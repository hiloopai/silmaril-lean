module

public import Silmaril.Proofs.Wasm.Models.V10.Host

/-!
# 1.0 behaviours are 2.0 behaviours

* `invoke_sim`: the Lime1 image of the 1.0 entry configuration is simulated by the 2.0 entry
  configuration on the image store (`ToV2.Sim` of the copied `Lime1/ToV2/Execution.lean`);
* `behaviours_sub`: the 1.0 behaviours read in 2.0 values are 2.0 behaviours at
  `v2Profile = Profile.spec` (the copied `V1.Execution.{Steps,Diverges}.toV2`, `ToV2.Sim.result`);
* `ptV2_dom`: the 2.0 image of a 1.0 point of the domain lies in the domain of `v20own`.

New proofs over the copied simulation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V10
open Silmaril.Wasm.Models.V2Core (VStore VHost)
open Silmaril.Wasm.Lime1.Execution (v2Profile)

variable {H : Type}

/-- The 2.0 image of the Lime1 entry code is the 2.0 entry code. -/
theorem invoke_code (s : OStore H) (a : FuncAddr) (vs : List Value) :
    Silmaril.Wasm.Lime1.Execution.Admin.listToV2
        (Silmaril.Wasm.V1.Execution.invoke s a vs).toLime.code =
      Silmaril.Wasm.Lime1.Execution.ToV2.Admin.normList
        (Silmaril.Wasm.V2.Execution.invoke ((s.mapCode Silmaril.Wasm.V1.Func.toLime).toV2)
          a.value (vs.map Value.toV2)).code := by
  simp [Silmaril.Wasm.V1.Execution.invoke, Silmaril.Wasm.V2.Execution.invoke,
    Silmaril.Wasm.V1.Execution.Config.toLime, AdminInstr.map,
    Silmaril.Wasm.Lime1.Execution.ToV2.Admin.normList_eq_map]

/-- **The entry configurations are simulated.** -/
theorem invoke_sim {s : OStore H}
    (hwf : Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF (s.mapCode Silmaril.Wasm.V1.Func.toLime))
    (a : FuncAddr) (vs : List Value) :
    Silmaril.Wasm.Lime1.Execution.ToV2.Sim (Silmaril.Wasm.V1.Execution.invoke s a vs).toLime
      (Silmaril.Wasm.V2.Execution.invoke ((s.mapCode Silmaril.Wasm.V1.Func.toLime).toV2)
        a.value (vs.map Value.toV2)) := by
  refine ⟨?_, hwf⟩
  have hc := invoke_code s a vs
  simp only [Silmaril.Wasm.Lime1.Execution.ToV2.Config.norm,
    Silmaril.Wasm.Execution.Runtime.Config.toV2]
  rw [hc]
  simp only [Silmaril.Wasm.V2.Execution.invoke, Silmaril.Wasm.V1.Execution.invoke,
    Silmaril.Wasm.V1.Execution.Config.toLime, Silmaril.Wasm.Lime1.Execution.ToV2.Store.erase_toV2]
  rfl

/-- A 1.0 result read in 2.0 values. -/
theorem result_toBehaviour (r : Result) :
    Behaviour.map Value.toV2 r.toBehaviour = (Result.toV2 r).toBehaviour := by
  cases r <;> rfl

/-- **1.0 behaviours are 2.0 behaviours** of the image point with the induced host. -/
theorem behaviours_sub {s : OStore H} {src : OHost H}
    (hwf : Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF (s.mapCode Silmaril.Wasm.V1.Func.toLime))
    (hosts : Silmaril.Wasm.Lime1.Execution.ToV2.HostCompatible
      (src.mapCode Silmaril.Wasm.V1.Func.toLime) (liftHostL (src.mapCode Silmaril.Wasm.V1.Func.toLime)))
    (a : FuncAddr) (vs : List Value) :
    Behaviour.mapSet Value.toV2 (Silmaril.Wasm.V1.Execution.behaviours src s a vs) ⊆
      Silmaril.Wasm.V2.Execution.behaviours v2Profile
        (liftHostL (src.mapCode Silmaril.Wasm.V1.Func.toLime))
        ((s.mapCode Silmaril.Wasm.V1.Func.toLime).toV2) a.value (vs.map Value.toV2) := by
  rintro _ ⟨b, ⟨c', r, hrun, hres, rfl⟩ | ⟨rfl, hdiv⟩, rfl⟩
  · obtain ⟨c₁, hrun₁, hs₁⟩ :=
      Silmaril.Wasm.V1.Execution.Steps.toV2 hosts hrun (invoke_sim hwf a vs)
    have hres' : c'.toLime.code = Silmaril.Wasm.Lime1.Execution.result r := by
      simp [Silmaril.Wasm.V1.Execution.Config.toLime, hres]
    have hcode := Silmaril.Wasm.Lime1.Execution.ToV2.Sim.result hs₁ hres'
    have hmem := Silmaril.Wasm.V2.Execution.mem_behavioursOf hrun₁ hcode
    rwa [result_toBehaviour]
  · exact Or.inr ⟨rfl,
      Silmaril.Wasm.V1.Execution.Diverges.toV2 hosts hdiv (invoke_sim hwf a vs)⟩

end Silmaril.Proofs.Wasm.Models.V10

namespace Silmaril.Proofs.Wasm.Models.V10

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V10
open Silmaril.Wasm.Models.V2Core (VStore VHost)

variable {H : Type}

/-- The memories and tables of the 2.0 image of a well-formed Lime1 store. -/
theorem memTab_image {ls : LStore H} (h : Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF ls) :
    MemTabWF ls.toV2 := by
  refine ⟨fun i mi hi => ?_, fun i mi hi => ?_, fun i ti hi => ?_⟩
  · obtain ⟨m, hm, rfl⟩ : ∃ m, ls.memories[i]? = some m ∧ MemInst.toV2 m = mi := by
      simpa [Silmaril.Wasm.Execution.Runtime.Store.toV2] using hi
    exact h.memSize m (List.mem_of_getElem? hm)
  · obtain ⟨m, hm, rfl⟩ : ∃ m, ls.memories[i]? = some m ∧ MemInst.toV2 m = mi := by
      simpa [Silmaril.Wasm.Execution.Runtime.Store.toV2] using hi
    exact h.memAligned m (List.mem_of_getElem? hm)
  · obtain ⟨t, ht, rfl⟩ : ∃ t, ls.tables[i]? = some t ∧ TableInst.toV2 t = ti := by
      simpa [Silmaril.Wasm.Execution.Runtime.Store.toV2] using hi
    simpa [TableInst.toV2] using h.tableSize t (List.mem_of_getElem? ht)

/-- The modules of the 2.0 image name allocated functions. -/
theorem modWF_image {s : OStore H} (h : ModsWF s) (i : Nat)
    (fi : Silmaril.Wasm.V2.Execution.FuncInst H)
    (hi : (s.mapCode Silmaril.Wasm.V1.Func.toLime).toV2.funcs[i]? = some fi) :
    Silmaril.Wasm.V2.Execution.ModWF (s.mapCode Silmaril.Wasm.V1.Func.toLime).toV2 fi.module := by
  obtain ⟨f, hf, rfl⟩ : ∃ f, s.funcs[i]? = some f ∧
      FuncInst.toV2 (FuncInst.mapCode Silmaril.Wasm.V1.Func.toLime f) = fi := by
    simpa [Silmaril.Wasm.Execution.Runtime.Store.toV2, Store.mapCode] using hi
  intro a ha
  cases f with
  | wasm t m c =>
    obtain ⟨b, hb, rfl⟩ : ∃ b ∈ m.funcs, b.value = a := by
      simpa [FuncInst.mapCode, FuncInst.toV2, ModuleInst.toV2] using ha
    simpa [Silmaril.Wasm.Execution.Runtime.Store.toV2, Store.mapCode] using
      h _ (List.mem_of_getElem? hf) t m c rfl b hb
  | host t c => simp [FuncInst.mapCode, FuncInst.toV2] at ha

/-- `List.mapM` succeeds when every element succeeds. -/
theorem mapM_isSome {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome) → (l.mapM f).isSome
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (by simp))
    obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp (mapM_isSome (f := f) (l := l)
      fun z hz => h z (by simp [hz]))
    simp [List.mapM_cons, hy, hys]

/-- The 2.0 image of a Lime1 store has a Core image. -/
theorem toCore_isSome_image (ls : LStore H) :
    (Silmaril.Wasm.V2.Execution.Store.toCore ls.toV2).isSome := by
  have hall : ∀ fi ∈ ls.toV2.funcs,
      (Silmaril.Wasm.V2.Execution.FuncInst.toCore fi).isSome := by
    intro fi hfi
    obtain ⟨f, -, rfl⟩ : ∃ f ∈ ls.funcs, FuncInst.toV2 f = fi := by
      simpa [Silmaril.Wasm.Execution.Runtime.Store.toV2] using hfi
    cases f <;> simp [FuncInst.toV2, Silmaril.Wasm.V2.Execution.FuncInst.toCore]
  simpa [Silmaril.Wasm.V2.Execution.Store.toCore] using mapM_isSome hall

/-- **The 2.0 image of a 1.0 point of the domain lies in the domain of `v20own`.** -/
theorem ptV2_dom {p : Pt H} (hp : dom p) : V2Core.dom (ptV2 p) := by
  obtain ⟨hwf, -, -, -, hmods⟩ := hp
  exact ⟨⟨modWF_image hmods, memTab_image hwf⟩, toCore_isSome_image _, preservesV _, keepsV _⟩

end Silmaril.Proofs.Wasm.Models.V10
