module

public import Silmaril.Proofs.Wasm.Models.FXLower.HandlerInv

/-!
# A handler frame around Core code is transparent: equal behaviours

At the host `noHost` and without FX functions:

* `result_stuck`, `escape_stuck`: a Core result, and Core code whose first non-value is an
  escaping `br`/`return`, do not step in CoreFX;
* `escape_not_result`: the latter is not a result;
* `runs_underH`, `diverges_underH`: runs and divergence of Core code under a handler frame are
  runs and divergence of the Core code;
* **`behaviours_underH`**: the CoreFX behaviours of Core code under a handler frame (with any
  continuation store) are its Core behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Proofs.Wasm.Models.FX (isCore map_core_inj all_isCore_map noFX_store)
open Silmaril.Wasm.SingleThreaded.Det (noHost Blocked not_step_vals not_step_trap
  not_step_throwing not_step_blocked fnv fnv_vals_append fnv_cons_of_none)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- An FX step from Core code with live continuations, at `noHost` and without FX functions, is
a Core step at `noHost`. -/
theorem core_of_stepK {K : List (Option ContFX)} {c : Config H} {y : ConfigFX H}
    (h : StepFX P noHost noFX (ofCoreK K c) y) : ∃ c', Step P noHost c c' := by
  obtain ⟨c', hst, -⟩ := step_ofCoreK h K c rfl (noFX_store _)
  exact ⟨c', (blockFX_noHost _) ▸ hst⟩

/-- **A Core result does not step.** -/
theorem result_stuck {K : List (Option ContFX)} {s : Store H} {f : Frame} (r : Result)
    {y : ConfigFX H} : ¬ StepFX P noHost noFX (ofCoreK K ⟨s, f, r.toAdmin⟩) y := by
  intro h
  obtain ⟨c', hst⟩ := core_of_stepK h
  cases r with
  | values vs => exact not_step_vals hst
  | trap => exact not_step_trap hst
  | throw a => exact not_step_throwing hst

theorem escapes_blocked {X : Admin} (hX : Escapes X) : Blocked X ∧ X.val? = none := by
  rcases hX with ⟨l, rfl⟩ | rfl
  · exact ⟨Or.inl ⟨l, rfl⟩, rfl⟩
  · exact ⟨Or.inr (Or.inl rfl), rfl⟩

/-- **Core code whose first non-value escapes does not step.** -/
theorem escape_stuck {K : List (Option ContFX)} {s : Store H} {f : Frame} {vs : List Val}
    {X : Admin} (hX : Escapes X) {y : ConfigFX H} :
    ¬ StepFX P noHost noFX (ofCoreK K ⟨s, f, vals vs ++ [X]⟩) y := by
  intro h
  obtain ⟨c', hst⟩ := core_of_stepK h
  have hb := escapes_blocked hX
  have hf : fnv (vals vs ++ [X]) = (vs, [X]) := by
    rw [fnv_vals_append, fnv_cons_of_none hb.2]
    simp
  exact not_step_blocked hst hf hb.1

/-- **Escaping code is not a result.** -/
theorem escape_not_result {vs : List Val} {X : Admin} (hX : Escapes X) (r : Result) :
    vals vs ++ [X] ≠ r.toAdmin := by
  intro h
  have hl : (r.toAdmin).getLast? = some X := by rw [← h]; simp
  cases r with
  | values ws =>
    simp only [Result.toAdmin, vals, List.getLast?_map, Option.map_eq_some_iff] at hl
    obtain ⟨w, -, hw⟩ := hl
    rcases hX with ⟨l, rfl⟩ | rfl <;> cases w <;> simp [Val.toAdmin] at hw <;> split at hw <;>
      simp at hw
  | trap =>
    simp only [Result.toAdmin, List.getLast?_singleton, Option.some.injEq] at hl
    rcases hX with ⟨l, rfl⟩ | rfl <;> cases hl
  | throw a =>
    simp only [Result.toAdmin, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hl
    rcases hX with ⟨l, rfl⟩ | rfl <;> cases hl

/-- Core code under a handler frame is not a result. -/
theorem underH_not_result {K : List (Option ContFX)} {hs : List HClause} {c : Config H}
    (r : Result) : (underH K hs c).code ≠ r.toAdmin.map .core := by
  intro h
  have h1 : (r.toAdmin.map AdminFX.core).all isCore = true := all_isCore_map _
  rw [← h] at h1
  simp [underH, onHandler, isCore] at h1

theorem underH_injective {K : List (Option ContFX)} {hs : List HClause} {c c' : Config H}
    (h : underH K hs c = underH K hs c') : c = c' := by
  obtain ⟨s, f, cs⟩ := c
  obtain ⟨s', f', cs'⟩ := c'
  simp only [underH, onHandler, ConfigFX.mk.injEq, List.cons.injEq, AdminFX.handler.injEq,
    true_and, and_true] at h
  obtain ⟨rfl, rfl, hc⟩ := h
  rw [map_core_inj hc]

/-- A configuration the handler frame leaves behind is stuck. -/
theorem left_stuck {K : List (Option ContFX)} {c : Config H} {y z : ConfigFX H}
    (hy : (∃ r : Result, c.code = r.toAdmin ∧ y = ofCoreK K c) ∨
      (∃ (vs : List Val) (X : Admin) (rest : List Admin), Escapes X ∧
        c.code = vals vs ++ [X] ++ rest ∧ y = ofCoreK K ⟨c.store, c.frame, vals vs ++ [X]⟩)) :
    ¬ StepFX P noHost noFX y z := by
  rcases hy with ⟨r, hc, rfl⟩ | ⟨vs, X, -, hX, -, rfl⟩
  · obtain ⟨s, f, cs⟩ := c
    simp only at hc
    rw [hc]
    exact result_stuck r
  · exact escape_stuck hX

/-- What the handler frame leaves behind is a result only if `c` is that result. -/
theorem left_result {K : List (Option ContFX)} {c : Config H} {y : ConfigFX H} {r : Result}
    (hy : (∃ r : Result, c.code = r.toAdmin ∧ y = ofCoreK K c) ∨
      (∃ (vs : List Val) (X : Admin) (rest : List Admin), Escapes X ∧
        c.code = vals vs ++ [X] ++ rest ∧ y = ofCoreK K ⟨c.store, c.frame, vals vs ++ [X]⟩))
    (hd : y.code = r.toAdmin.map .core) : c.code = r.toAdmin := by
  rcases hy with ⟨r₀, -, rfl⟩ | ⟨vs, X, -, hX, -, rfl⟩
  · exact map_core_inj hd
  · exact absurd (map_core_inj hd) (escape_not_result hX r)

/-- **Finite runs**: a run of Core code under a handler frame to a result is a Core run. -/
theorem runs_underH {K : List (Option ContFX)} {hs : List HClause} {d : ConfigFX H}
    {r : Result} (hd : d.code = r.toAdmin.map .core) {x : ConfigFX H}
    (hrun : StepsFX P noHost noFX x d) :
    ∀ c, x = underH K hs c → ∃ c', Steps P noHost c c' ∧ c'.code = r.toAdmin := by
  induction hrun using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro c hx
    exact absurd (hx ▸ hd) (underH_not_result r)
  | head hstep hrest ih =>
    intro c hx
    rw [hx] at hstep
    rcases step_underH hstep with ⟨c', hst, rfl⟩ | hy
    · obtain ⟨c'', hrun', hc''⟩ := ih c' rfl
      exact ⟨c'', Relation.ReflTransGen.head hst hrun', hc''⟩
    · rcases Relation.ReflTransGen.cases_head hrest with rfl | ⟨z, hz, -⟩
      · exact ⟨c, .refl, left_result hy hd⟩
      · exact absurd hz (left_stuck hy)

/-- A step of Core code under a handler frame that can be continued is a Core step. -/
theorem step_underH_live {K : List (Option ContFX)} {hs : List HClause} {c : Config H}
    {y z : ConfigFX H} (h : StepFX P noHost noFX (underH K hs c) y)
    (hz : StepFX P noHost noFX y z) : ∃ c', Step P noHost c c' ∧ y = underH K hs c' := by
  rcases step_underH h with h1 | hy
  · exact h1
  · exact absurd hz (left_stuck hy)

/-- **Divergence**: Core code that diverges under a handler frame diverges in Core. -/
theorem diverges_underH {K : List (Option ContFX)} {hs : List HClause} {c : Config H}
    (h : Silmaril.InfiniteTrace (StepFX P noHost noFX) (underH K hs c)) : Diverges P noHost c := by
  obtain ⟨T, h0, hT⟩ := h
  have hall : ∀ n, ∃ cn, T n = underH K hs cn := by
    intro n
    induction n with
    | zero => exact ⟨c, h0⟩
    | succ n ih =>
      obtain ⟨cn, hn⟩ := ih
      have hs₀ : StepFX P noHost noFX (underH K hs cn) (T (n + 1)) := hn ▸ hT n
      obtain ⟨c', -, he⟩ := step_underH_live hs₀ (hT (n + 1))
      exact ⟨c', he⟩
  choose g hg using hall
  refine ⟨g, underH_injective ((hg 0).symm.trans h0), fun n => ?_⟩
  have hs₀ : StepFX P noHost noFX (underH K hs (g n)) (T (n + 1)) := hg n ▸ hT n
  obtain ⟨c', hst, he⟩ := step_underH_live hs₀ (hT (n + 1))
  have hc' : g (n + 1) = c' := underH_injective ((hg (n + 1)).symm.trans he)
  exact hc' ▸ hst

/-- **A handler frame around Core code is transparent** (no host calls, no FX functions): the
CoreFX behaviours of Core code under a handler frame, with any continuation store, are its Core
behaviours. -/
theorem behaviours_underH (K : List (Option ContFX)) (hs : List HClause) (c : Config H) :
    behavioursFX P noHost noFX (underH K hs c) = behavioursOf P noHost c := by
  apply Set.Subset.antisymm
  · rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨c', hc, hcode⟩ := runs_underH hd hrun c rfl
      exact Or.inl ⟨c', r, hc, hcode, rfl⟩
    · exact Or.inr ⟨rfl, diverges_underH hdiv⟩
  · have h := behaviours_handler_sub (P := P) (host := noHost) (fx := noFX) K hs c
    rwa [blockFX_noHost] at h

end Silmaril.Proofs.Wasm.Models.FXLower
