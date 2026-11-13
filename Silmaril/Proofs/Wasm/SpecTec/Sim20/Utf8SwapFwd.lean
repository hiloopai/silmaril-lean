module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapTypEx
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Leg3.Thms

/-!
# `Utf8Mono.Task.fwdU20` from the involution leaf

Take a V2 step `c → c'` from a `Good20BU` configuration. Let `S` be the export images of the
module instances of `c` and re-encode every module's exports by `encExp20 S` (empty names, a
length that records the index in `S`).

1. The re-encoded configuration is `Good20B` (`good20B_exp`) and steps to the re-encoded
   successor (`step_exp20`), so the round-6 forward theorem `StoreBulk.fwd_good20B` gives a step
   of `simEnv20T`, which `Utf8Else.sstepB_utf8_20T` moves to `utf8Env20T`.
2. `swapS S` is an involution (`swapS_swapS`) and keeps `exportinst*` typing up to a fixed amount
   of fuel (`swapS_fuel`): a re-encoding is typed (`typedV_rep_U`), and so are the exports of `c`'s
   modules (`typedV_exports_U`); there are finitely many of each (`uniform_fuel`).
3. The leaf `Task.swapStep20` maps the step to one between the `swapV (swapS S)` images, which are
   the images of `c` and `c'` (`swapV_configV_exp`): a step never makes a module instance, so the
   modules of `c'` are among those of `c` (`Utf8Strip.modsQ_step`).

The successor is `Good20BU` 's strip route (`Utf8Strip.good20BU_succ`).

* **`fwdU20_of_swapStep20`** : `Task.swapStep20 → Utf8Mono.Task.fwdU20`;
* **`unstripStep20_of_swapStep20`** : `Task.swapStep20 → Utf8Strip.Task.unstripStep20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (Good20B fwd_good20B)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (Good20BU utf8Env20T storeB_utf8)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Strip (ModsQ AdminMods AdminsMods ModOk modsQ_step
  noHost20_of_storeOkB)

variable {H : Type}

section
variable {Q : ModuleInst → Prop}

mutual
theorem mem_adminMods20 : ∀ (a : Admin), AdminMods Q a → ∀ m ∈ adminMods20 a, Q m
  | .label _ _ body, h, m, hm => mem_adminsMods20 body h m hm
  | .frame _ _ body, h, m, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h.1
    · exact mem_adminsMods20 body h.2 m hm
  | .plain _, _, _, hm | .refFuncAddr _, _, _, hm | .refHostAddr _, _, _, hm
  | .callAddr _, _, _, hm | .trap, _, _, hm => nomatch hm

theorem mem_adminsMods20 : ∀ (l : List Admin), AdminsMods Q l → ∀ m ∈ adminsMods20 l, Q m
  | [], _, _, hm => nomatch hm
  | a :: l, h, m, hm => by
    rcases List.mem_append.1 hm with hm | hm
    · exact mem_adminMods20 a h.1 m hm
    · exact mem_adminsMods20 l h.2 m hm
end

/-- **Every module instance in `mods20 c` has a property all module instances of `c` have.** -/
theorem mem_mods20 {c : Config H} (h : ModsQ Q c) : ∀ m ∈ mods20 c, Q m := by
  intro m hm
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hm
    exact h.funcs fi hfi
  · rcases List.mem_cons.1 hm with rfl | hm
    · exact h.frame
    · exact mem_adminsMods20 _ h.code m hm
end

/-- **The module instances of a `Good20BU` configuration are `moduleinst`s of `utf8Env20`.** -/
theorem modsQ_modOk {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile} {c : Config H}
    (hg : Good20BU hn P c) : ModsQ (ModOk (Whole.storeB P)) c := by
  have hst := Utf8Strip.modOk_of_state_u20 hg.typ.state
  refine ⟨fun fi hfi => hst.1 (StoreFn.eraseFI fi) (List.mem_map_of_mem hfi), hst.2, ?_⟩
  exact (Utf8Strip.adminsMods_map_eDA c.code).1 (Utf8Strip.adminsMods_of_u20 _ hg.typ.code)

/-- **`swapS (expsV20 c)` keeps `exportinst*` typing in `utf8Env20T (storeB P)`.** -/
theorem swapS_typed {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile} {c : Config H}
    (hg : Good20BU hn P c) (u : Value)
    (_hu : HasTyp (utf8Env20T (Whole.storeB P)) VarEnv.empty exportsT u) :
    HasTyp (utf8Env20T (Whole.storeB P)) VarEnv.empty exportsT (swapS (expsV20 c) u) := by
  by_cases hm : u ∈ expsV20 c
  · rw [swapS_of_mem hm]
    exact typedV_rep_U _ _ ⟨rfl, rfl, rfl⟩
  · cases h : (expsV20 c).find? (fun x => encV (expsV20 c) x == u) with
    | none =>
      have : swapS (expsV20 c) u = u := by simp only [swapS, hm, ite_false, h]
      rwa [this]
    | some u₀ =>
      have : swapS (expsV20 c) u = u₀ := by simp only [swapS, hm, ite_false, h]
      rw [this]
      obtain ⟨m, hmm, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some h)
      exact typedV_exports_U (mem_mods20 (modsQ_modOk hg) m hmm) _ ⟨rfl, rfl, rfl⟩

/-- **Finitely many typed values are typed at one fuel.** -/
theorem uniform_fuel {env : Env} {ρ : VarEnv} {t : IL.Typ} :
    ∀ T : List Value, (∀ x ∈ T, HasTyp env ρ t x) →
      ∃ K, ∀ x ∈ T, hasTyp K env ρ t x = .ok true
  | [], _ => ⟨0, fun _ h => nomatch h⟩
  | x :: T, h => by
    obtain ⟨m, hm⟩ := h x List.mem_cons_self
    obtain ⟨K, hK⟩ := uniform_fuel T fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨max m K, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ((monoTypAt_of_le (le_max_left m K)).typ _ _ _ _).ok hm
    · exact ((monoTypAt_of_le (le_max_right m K)).typ _ _ _ _).ok (hK y hy)

/-- The values `swapS (expsV20 c)` exchanges are `exportinst*`s of `utf8Env20T (storeB P)`. -/
theorem swapS_pairs_typed {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile} {c : Config H}
    (hg : Good20BU hn P c) : ∀ x ∈ expsV20 c ++ (expsV20 c).map (encV (expsV20 c)),
      HasTyp (utf8Env20T (Whole.storeB P)) VarEnv.empty exportsT x := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨m, hmm, rfl⟩ := List.mem_map.1 hx
    exact typedV_exports_U (mem_mods20 (modsQ_modOk hg) m hmm) _ ⟨rfl, rfl, rfl⟩
  · obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
    exact typedV_rep_U _ _ ⟨rfl, rfl, rfl⟩

/-- `swapS S` moves a value into the exchanged ones, or fixes it. -/
theorem swapS_cases (S : List Value) (u : Value) :
    swapS S u ∈ S ++ S.map (encV S) ∨ swapS S u = u := by
  by_cases hm : u ∈ S
  · rw [swapS_of_mem hm]
    exact Or.inl (List.mem_append_right _ (List.mem_map_of_mem hm))
  · cases h : S.find? (fun x => encV S x == u) with
    | none => exact Or.inr (by simp only [swapS, hm, ite_false, h])
    | some u₀ =>
      have : swapS S u = u₀ := by simp only [swapS, hm, ite_false, h]
      rw [this]
      exact Or.inl (List.mem_append_left _ (List.mem_of_find?_eq_some h))

/-- **`swapS (expsV20 c)` loses a bounded amount of fuel on `exportinst*`.** -/
theorem swapS_fuel {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile} {c : Config H}
    (hg : Good20BU hn P c) : ∃ K, ∀ n u,
      hasTyp n (utf8Env20T (Whole.storeB P)) VarEnv.empty exportsT u = .ok true →
      hasTyp (n + K) (utf8Env20T (Whole.storeB P)) VarEnv.empty exportsT
        (swapS (expsV20 c) u) = .ok true := by
  obtain ⟨K, hK⟩ := uniform_fuel _ (swapS_pairs_typed hg)
  refine ⟨K, fun n u hu => ?_⟩
  rcases swapS_cases (expsV20 c) u with hx | he
  · exact ((monoTypAt_of_le (Nat.le_add_left K n)).typ _ _ _ _).ok (hK _ hx)
  · rw [he]
    exact ((monoTypAt_of_le (Nat.le_add_right n K)).typ _ _ _ _).ok hu

/-- **`Utf8Mono.Task.fwdU20` from the involution leaf.** -/
theorem fwdU20_of_swapStep20 (hL : Task.swapStep20) : Utf8Mono.Task.fwdU20 := by
  intro H hn P host c c' hg hs
  have hnh := noHost20_of_storeOkB hg.store
  -- the successor, by the strip route
  obtain ⟨hg₀', -⟩ := fwd_good20B (Utf8Strip.good20B_strip hg) (Utf8Strip.step_strip20 hs hnh)
  refine ⟨Utf8Strip.good20BU_succ hg hs hg₀', ?_⟩
  -- the step, by the re-encoding
  let S := expsV20 c
  have hm : ModsQ (fun m => expV m.exports ∈ S) c :=
    modsQ_mono (fun m hm => List.mem_map_of_mem (f := fun m => expV m.exports) hm)
      (modsQ_mods20 c)
  have hm' : ModsQ (fun m => expV m.exports ∈ S) c' := modsQ_step hs hnh hm
  have hE : Step P host (expConfig20 (encExp20 S) c) (expConfig20 (encExp20 S) c') :=
    step_exp20 hs hnh
  have hGE : Good20B hn P (expConfig20 (encExp20 S) c) :=
    good20B_exp (fun _ => typedV_rep_sim _) hg
  obtain ⟨-, hT⟩ := fwd_good20B hGE hE
  have hU := Utf8Else.sstepB_utf8_20T (storeB_utf8 P) hT
  obtain ⟨K, hK⟩ := swapS_fuel hg
  have hS := hL P (swapS S) (swapS_swapS S) K hK _ _ hU
  rwa [swapV_configV_exp (modsQ_mono (fun _ h => swapS_expV_enc h) hm),
    swapV_configV_exp (modsQ_mono (fun _ h => swapS_expV_enc h) hm')] at hS

/-- **Leg 3 from the involution leaf.** -/
theorem unstripStep20_of_swapStep20 (hL : Task.swapStep20) : Utf8Strip.Task.unstripStep20 :=
  Utf8Leg3.unstripStep20_of_fwdU20 (fwdU20_of_swapStep20 hL)

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
