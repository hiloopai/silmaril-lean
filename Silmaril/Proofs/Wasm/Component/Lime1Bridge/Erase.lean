module

public import Silmaril.Wasm.Component.Lime1Bridge.Defs
public import Silmaril.Wasm.Component.Lime1Ref.Thms

/-!
# Lime1 behaviours are Core 3.0 behaviours of every store erasing to the image

`Lime1Core.lime1_core_beh` reads Lime1 behaviours as Core behaviours of the image store
`s.toCore`. The copied relation `Lime1.Execution.Sim` is up to erasure, so the same holds in every
Core store `S` with `ToCore.Store.erase S = s.toCore` (for example the store of a Core 3.0
instance, which keeps segment instances and full module instances):

* `invoke_sim_erase`: the Lime1 entry configuration is simulated by Core's entry configuration on
  `S` (erasure keeps function types, so both entry codes agree);
* **`behaviours_sub_erase`**: Lime1 behaviours, in Core values, are Core behaviours in `S` at
  `Profile.spec`;
* `returned_core_erase`, `diverges_core_erase`: the Lime1 engine forms, under the empty host.

Then the engine-run half of `Lime1Ref.RefToSpecLime1` follows from the store-level bridge:

* **`specSub_of_instBridgeE`**: `InstBridgeE → SpecSubOn lime1 lime1G.emb Profile.spec
  Lime1Dom`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Bridge

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref Silmaril.Wasm.Component.Lime1Bridge
open Silmaril.Wasm.Models.Lime1Core (behavioursL liftHostC invokeL)
open Silmaril.Wasm.Models.V10 (LStore LHost)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps Diverges)
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- Erasure keeps the function types. -/
theorem funcType_erase {S : Silmaril.Wasm.Execution.Core.Store H} (a : Nat) :
    ((Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S).funcs[a]?.map
        Silmaril.Wasm.Execution.Core.FuncInst.type) =
      S.funcs[a]?.map Silmaril.Wasm.Execution.Core.FuncInst.type := by
  simp only [Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase, List.getElem?_map, Option.map_map]
  rfl

/-- **The entry configurations are simulated, in every store erasing to the image.** -/
theorem invoke_sim_erase {s : LStore H} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    {S : Silmaril.Wasm.Execution.Core.Store H}
    (hS : Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = s.toCore)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (vs : List Value) :
    Silmaril.Wasm.Lime1.Execution.Sim (invokeL s a vs)
      (Silmaril.Wasm.Execution.Core.invoke S a.value (vs.map Value.toCore)) := by
  obtain ⟨h1, h2, h3, h4⟩ := Silmaril.Proofs.Wasm.Models.Lime1Core.invoke_sim hwf ha vs
  have hty : S.funcs[a.value]?.map Silmaril.Wasm.Execution.Core.FuncInst.type =
      s.toCore.funcs[a.value]?.map Silmaril.Wasm.Execution.Core.FuncInst.type := by
    rw [← funcType_erase, hS]
  refine ⟨?_, h2, h3, h4⟩
  simp only [Silmaril.Wasm.Execution.Core.invoke] at h1 ⊢
  rw [Silmaril.Wasm.Lime1.Execution.ToCore.Config.norm_eq_toCore_iff] at h1 ⊢
  rw [hty]
  exact ⟨hS, h1.2⟩

/-- **Lime1 behaviours are Core 3.0 behaviours in every store erasing to the image.** -/
theorem behaviours_sub_erase {s : LStore H} {src : LHost H}
    (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    (hosts : Silmaril.Wasm.Lime1.Execution.HostCompatible src (liftHostC src))
    {S : Silmaril.Wasm.Execution.Core.Store H}
    (hS : Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = s.toCore)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (vs : List Value) :
    Behaviour.mapSet Value.toCore (behavioursL src s a vs) ⊆
      Silmaril.Wasm.Execution.Core.behaviours Profile.spec (liftHostC src) S a.value
        (vs.map Value.toCore) := by
  rintro _ ⟨b, ⟨c', r, hrun, hres, rfl⟩ | ⟨rfl, hdiv⟩, rfl⟩
  · obtain ⟨c₁, hrun₁, hs₁⟩ :=
      Silmaril.Wasm.Lime1.Execution.Steps.toCore hosts hrun (invoke_sim_erase hwf hS ha vs)
    have hcode := Silmaril.Wasm.Lime1.Execution.Sim.result hs₁ hres
    have hmem := Silmaril.Wasm.Execution.Core.mem_behavioursOf hrun₁ hcode
    rwa [Silmaril.Proofs.Wasm.Models.Lime1Core.result_toBehaviour]
  · exact Or.inr ⟨rfl,
      Silmaril.Wasm.Lime1.Execution.Diverges.toCore hosts hdiv (invoke_sim_erase hwf hS ha vs)⟩

theorem core_beh_erase {s : LStore Nat} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    {S : Silmaril.Wasm.Execution.Core.Store Nat}
    (hS : Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = s.toCore)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (xs : List Value) {b : Behaviour Value}
    (hb : b ∈ behavioursL noHostL s a xs) :
    b.map Value.toCore ∈ Silmaril.Wasm.Execution.Core.behaviours Profile.spec
      Silmaril.Wasm.SingleThreaded.Det.noHost S a.value (xs.map Value.toCore) := by
  rw [← Silmaril.Proofs.Wasm.Component.Lime1Ref.liftHostC_noHostL]
  exact behaviours_sub_erase hwf
    (Silmaril.Wasm.Models.Lime1Core.liftHostC_compatible (fun _ _ _ _ _ h => h.elim)
      (fun _ _ _ _ _ h => h.elim)) hS ha xs ⟨b, hb, rfl⟩

/-- A returned engine run is a Core 3.0 behaviour in every store erasing to the image. -/
theorem returned_core_erase {s : LStore Nat} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    {S : Silmaril.Wasm.Execution.Core.Store Nat}
    (hS : Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = s.toCore)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (xs : List Value) {s' : LStore Nat}
    {t' : lime1.Thread Nat} (run : Steps lime1 (s, lime1.invoke a xs) (s', t'))
    {r : Silmaril.Wasm.Component.Engine.CallResult} (hst : lime1.status s' t' = .returned r) :
    ((Silmaril.Wasm.Component.Engine.Lime1.toResult r).toBehaviour).map Value.toCore ∈
      Silmaril.Wasm.Execution.Core.behaviours Profile.spec
        Silmaril.Wasm.SingleThreaded.Det.noHost S a.value (xs.map Value.toCore) := by
  refine core_beh_erase hwf hS ha xs
    (Or.inl ⟨Silmaril.Wasm.Component.Engine.Lime1.toConfig (s', t'), _,
      Silmaril.Proofs.Wasm.Component.Lime1Ref.steps_exec run, ?_, rfl⟩)
  exact Silmaril.Wasm.Lime1.Execution.terminal?_sound
    (Silmaril.Wasm.Component.Engine.Lime1.status_eq_returned hst)

/-- A diverging engine run is a Core 3.0 divergence in every store erasing to the image. -/
theorem diverges_core_erase {s : LStore Nat} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    {S : Silmaril.Wasm.Execution.Core.Store Nat}
    (hS : Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = s.toCore)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (xs : List Value)
    (hd : Diverges lime1 (s, lime1.invoke a xs)) :
    Behaviour.diverges ∈ Silmaril.Wasm.Execution.Core.behaviours Profile.spec
      Silmaril.Wasm.SingleThreaded.Det.noHost S a.value (xs.map Value.toCore) :=
  core_beh_erase hwf hS ha xs (b := .diverges)
    (Or.inr ⟨rfl, Silmaril.Proofs.Wasm.Component.Lime1Ref.diverges_exec hd⟩)

/-- A returned or trapping engine run of export `k` is a Core 3.0 outcome of `I'`, under
`InstSim`. -/
theorem coreRun_of_engineE {I : EInstance lime1} {I' : Silmaril.Wasm.Game.ScalarInstance}
    (hsim : InstSim I I') {k : Nat} {a : FuncAddr} (ha : I.addrs[k]? = some a) (xs : List Value)
    {s' : LStore Nat} {t' : lime1.Thread Nat}
    (run : Steps lime1 (I.store, lime1.invoke a xs) (s', t')) {r : Option (List Value)}
    (hfin : (∃ ys, lime1.status s' t' = .returned (.values ys) ∧ r = some ys) ∨
      (lime1.status s' t' = .returned .trap ∧ r = none)) :
    ∃ (c' : Silmaril.Wasm.Execution.Core.Config Nat) (res : Silmaril.Wasm.Execution.Core.Result),
      Silmaril.Wasm.Execution.Core.Steps Profile.spec Silmaril.Wasm.SingleThreaded.Det.noHost
        (Silmaril.Wasm.Execution.Core.invoke I'.store (I'.addrs.getD k 0)
          (xs.map Silmaril.Wasm.SingleThreaded.ofFlat)) c' ∧
      c'.code = res.toAdmin ∧
      r = match res with
        | .values vs => vs.mapM Silmaril.Wasm.SingleThreaded.toFlat?
        | _ => none := by
  obtain ⟨hwf, hS, hk⟩ := hsim
  obtain ⟨hlt, heq⟩ := hk k a ha
  rw [heq]
  rcases hfin with ⟨ys, hst, rfl⟩ | ⟨hst, rfl⟩
  · obtain ⟨c', run', hc'⟩ :=
      Silmaril.Proofs.Wasm.Component.Lime1Ref.result_of_beh (res := .values (ys.map Value.toCore))
        (.inr ⟨_, rfl⟩) (returned_core_erase hwf hS hlt xs run hst)
    exact ⟨c', _, run', hc', (Silmaril.Proofs.Wasm.Component.Lime1Ref.mapM_toFlat ys).symm⟩
  · obtain ⟨c', run', hc'⟩ :=
      Silmaril.Proofs.Wasm.Component.Lime1Ref.result_of_beh (res := .trap) (.inl rfl)
        (returned_core_erase hwf hS hlt xs run hst)
    exact ⟨c', _, run', hc', rfl⟩

/-- **The engine-run half for Lime1, from the store-level instantiation bridge.** -/
theorem specSub_of_instBridgeE (hB : InstBridgeE) :
    SpecSubOn lime1 Lime1G.lime1G.emb Profile.spec Lime1Dom := by
  intro c hD hc hi x hx vs b hb
  cases hL : checkLower x.ty.params vs with
  | none =>
    simp only [exportSpecE, hL] at hb
    simpa only [exportSpec, hL] using hb
  | some xs =>
    simp only [exportSpecE, hL] at hb
    simp only [exportSpec, hL]
    rcases hb with ⟨I, hI, r, ⟨a, s', t', ha, run, hfin⟩, rfl⟩ | ⟨rfl, I, hI, a, ha, hdv⟩
    · obtain ⟨I', hI', hsim⟩ := hB c hD hc hi I hI
      exact Or.inl ⟨r, ⟨I', hI', coreRun_of_engineE hsim ha xs run hfin⟩, rfl⟩
    · obtain ⟨I', hI', hwf, hS, hk⟩ := hB c hD hc hi I hI
      obtain ⟨hlt, heq⟩ := hk x.core a ha
      refine Or.inr ⟨rfl, I', hI', ?_⟩
      rw [heq]
      exact Silmaril.Proofs.Wasm.Component.Lime1Ref.diverges_of_beh
        (diverges_core_erase hwf hS hlt xs hdv)

end Silmaril.Proofs.Wasm.Component.Lime1Bridge
