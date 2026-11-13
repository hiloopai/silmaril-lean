module

public import Silmaril.Proofs.Wasm.Models.FXLower.CoreK
public import Silmaril.Proofs.Wasm.Models.FXLower.Handler
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck

/-!
# Inverting a step of Core code under a handler frame (no host calls, no FX functions)

At the host `noHost` (no host calls) and without FX functions:

* `no_step_nil`: empty FX code does not step;
* `plug_isCore`: if a plugged context is Core code, so is what fills its hole;
* **`step_underH`**: a step of Core code `c` under a handler frame is either a Core step of `c`
  under the same frame, or the frame returning a result of `c`, or a `br`/`return` that escapes
  the frame (leaving stuck Core code);
* `result_stuck`, `blocked_stuck`: the last two kinds of configuration do not step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Proofs.Wasm.Models.FX (isCore map_core_inj split3 all_isCore_map noFX_store)
open Silmaril.Wasm.SingleThreaded.Det (noHost Blocked not_step_vals not_step_trap
  not_step_throwing not_step_blocked fnv fnv_vals_append fnv_cons_of_none)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

theorem blockFX_noHost (fx : H → Option FuncFX) : blockFX (noHost (H := H)) fx = noHost := by
  funext h s vs out
  simp [blockFX]

/-- **Empty FX code does not step.** -/
theorem no_step_nil {fx : H → Option FuncFX} {x y : ConfigFX H}
    (h : StepFX P noHost fx x y) : x.code ≠ [] := by
  induction h with
  | @core s s' K f f' cs cs' h =>
    intro hc
    have hcs : cs = [] := List.map_eq_nil_iff.mp hc
    have h' : Step P noHost ⟨s, f, vals []⟩ ⟨s', f', cs'⟩ := by
      rw [← blockFX_noHost fx]
      rw [hcs] at h
      exact h
    exact not_step_vals h'
  | seq _ _ ih =>
    intro hc
    exact ih (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hc).1).2
  | _ => simp [cvals, cthrowing]

/-- If a plugged context is Core code, so is what fills its hole. -/
theorem plug_isCore (E : Ctx) (c : List AdminFX) (h : (E.plug c).all isCore = true) :
    c.all isCore = true := by
  induction E with
  | hole => exact h
  | seq vs E rest ih =>
    simp only [Ctx.plug, List.all_append, Bool.and_eq_true] at h
    exact ih h.1.2
  | label n k E ih => simp [Ctx.plug, isCore] at h
  | frame n f E ih => simp [Ctx.plug, isCore] at h
  | handler hs E ih => simp [Ctx.plug, isCore] at h

/-- A `suspend` or `switch` site is not Core code. -/
theorem plug_ne_core (E : Ctx) (pre : List AdminFX) (i : FXInstr) (cs : List Admin) :
    E.plug (pre ++ [.fx i]) ≠ cs.map .core := by
  intro h
  have h1 : (E.plug (pre ++ [.fx i])).all isCore = true := by rw [h]; exact all_isCore_map cs
  have h2 := plug_isCore E _ h1
  simp [isCore] at h2

/-- `cvals vs ++ es ++ rest` with a non-trivial context is not a single non-Core instruction
unless `es` is empty. -/
theorem seq_single {vs : List Val} {es rest : List AdminFX} {x : AdminFX}
    (hx : isCore x = false) (hne : vs ≠ [] ∨ rest ≠ []) (h : cvals vs ++ es ++ rest = [x]) :
    es = [] := by
  rcases hne with hv | hr
  · obtain ⟨v, vs', rfl⟩ := List.exists_cons_of_ne_nil hv
    simp only [cvals, vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    rw [← h.1] at hx
    simp [isCore] at hx
  · have h' : cvals vs ++ (es ++ rest) = [x] := by rw [← List.append_assoc]; exact h
    rcases List.append_eq_singleton_iff.mp h' with ⟨-, h2⟩ | ⟨-, h2⟩
    · rcases List.append_eq_singleton_iff.mp h2 with ⟨he, -⟩ | ⟨-, hr'⟩
      · exact he
      · exact absurd hr' hr
    · exact absurd (List.append_eq_nil_iff.mp h2).2 hr

/-- The escaping branch instructions. -/
def Escapes (X : Admin) : Prop := (∃ l, X = .plain (.br l)) ∨ X = .plain .return_

/-- What a step of Core code `c` under a handler frame can do. -/
abbrev UnderHStep (K : List (Option ContFX)) (hs : List HClause) (c : Config H)
    (y : ConfigFX H) : Prop :=
  (∃ c', Step P noHost c c' ∧ y = underH K hs c') ∨
  (∃ r : Result, c.code = r.toAdmin ∧ y = ofCoreK K c) ∨
  (∃ (vs : List Val) (X : Admin) (rest : List Admin), Escapes X ∧
    c.code = vals vs ++ [X] ++ rest ∧ y = ofCoreK K ⟨c.store, c.frame, vals vs ++ [X]⟩)

theorem underH_eq {K K₀ : List (Option ContFX)} {hs hs₀ : List HClause} {s s₀ : Store H}
    {f f₀ : Frame} {cs : List Admin} {es : List AdminFX}
    (hx : underH K hs ⟨s, f, cs⟩ = ⟨s₀, K₀, f₀, [.handler hs₀ es]⟩) :
    s = s₀ ∧ K = K₀ ∧ f = f₀ ∧ hs = hs₀ ∧ cs.map .core = es := by
  simp only [underH, onHandler, ConfigFX.mk.injEq, List.cons.injEq, AdminFX.handler.injEq,
    and_true] at hx
  exact hx

/-- The `ctxHandler` case: a Core step under the frame. -/
theorem case_ctxHandler {K K₀ K₀' : List (Option ContFX)} {hs hs₀ : List HClause}
    {s s₀ s₀' : Store H} {f f₀ f₀' : Frame} {cs : List Admin} {es es' : List AdminFX}
    (hx : underH K hs ⟨s, f, cs⟩ = ⟨s₀, K₀, f₀, [.handler hs₀ es]⟩)
    (h : StepFX P noHost noFX ⟨s₀, K₀, f₀, es⟩ ⟨s₀', K₀', f₀', es'⟩) :
    UnderHStep (P := P) K hs ⟨s, f, cs⟩ ⟨s₀', K₀', f₀', [.handler hs₀ es']⟩ := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := underH_eq hx
  obtain ⟨c', hst, hy⟩ := step_ofCoreK h K ⟨s, f, cs⟩ rfl (noFX_store _)
  obtain ⟨hs₁, hK₁, hf₁, hc₁⟩ := ofCoreK_eq hy
  refine Or.inl ⟨c', (blockFX_noHost _) ▸ hst, ?_⟩
  simp only [underH, onHandler, hs₁, hK₁, hf₁, hc₁]

/-- The `handlerVals`, `trapHandler` and `throwHandler` cases: the frame returns a result. -/
theorem case_result {K K₀ : List (Option ContFX)} {hs hs₀ : List HClause} {s s₀ : Store H}
    {f f₀ : Frame} {cs : List Admin} (r : Result)
    (hx : underH K hs ⟨s, f, cs⟩ = ⟨s₀, K₀, f₀, [.handler hs₀ (r.toAdmin.map .core)]⟩) :
    UnderHStep (P := P) K hs ⟨s, f, cs⟩ ⟨s₀, K₀, f₀, r.toAdmin.map .core⟩ := by
  obtain ⟨rfl, rfl, rfl, rfl, hc⟩ := underH_eq hx
  have hcs : cs = r.toAdmin := map_core_inj hc
  refine Or.inr (Or.inl ⟨r, hcs, ?_⟩)
  show (⟨s, K, f, r.toAdmin.map .core⟩ : ConfigFX H) = ⟨s, K, f, cs.map .core⟩
  rw [hcs]

/-- The `brHandler` and `returnHandler` cases: a branch escapes the frame. -/
theorem case_escape {K K₀ : List (Option ContFX)} {hs hs₀ : List HClause} {s s₀ : Store H}
    {f f₀ : Frame} {cs : List Admin} {vs : List Val} {X : Admin} {rest : List AdminFX}
    (hX : Escapes X)
    (hx : underH K hs ⟨s, f, cs⟩ = ⟨s₀, K₀, f₀, [.handler hs₀ (cvals vs ++ [.core X] ++ rest)]⟩) :
    UnderHStep (P := P) K hs ⟨s, f, cs⟩ ⟨s₀, K₀, f₀, cvals vs ++ [.core X]⟩ := by
  obtain ⟨rfl, rfl, rfl, rfl, hc⟩ := underH_eq hx
  obtain ⟨A, B, C, hcs, hA, hB, -⟩ := split3 hc.symm
  have hcs' : cs = vals vs ++ [X] ++ C := by
    rw [hcs, map_core_inj hA, map_core_inj (l' := [X]) hB]
  exact Or.inr (Or.inr ⟨vs, X, C, hX, hcs', by simp [ofCoreK, cvals]⟩)

/-- The `suspend` and `switch` cases cannot happen on Core code. -/
theorem case_plug {K K₀ : List (Option ContFX)} {hs hs₀ : List HClause} {s s₀ : Store H}
    {f f₀ : Frame} {cs : List Admin} {E : Ctx} {pre : List AdminFX} {i : FXInstr}
    (hx : underH K hs ⟨s, f, cs⟩ = ⟨s₀, K₀, f₀, [.handler hs₀ (E.plug (pre ++ [.fx i]))]⟩) :
    False :=
  plug_ne_core E pre i cs (underH_eq hx).2.2.2.2.symm

/-- The remaining rules have a left-hand side that is not a handler frame around Core code. -/
macro "underH_absurd" hx:ident : tactic => `(tactic| (
  exfalso
  simp only [underH, onHandler, ConfigFX.mk.injEq] at $hx:ident
  first
  | (have h1 := congrArg (List.all · isCore) ($hx).2.2.2
     simp [isCore, cvals, cthrowing] at h1; done)
  | (have h1 := congrArg List.getLast? ($hx).2.2.2; simp [cvals, cthrowing] at h1; done)
  | (simp [cvals, cthrowing, List.cons_eq_append_iff] at $hx:ident)))

/-- **Inversion of a step of Core code under a handler frame.** -/
theorem step_underH {K : List (Option ContFX)} {hs : List HClause} {c : Config H}
    {y : ConfigFX H} (h : StepFX P noHost noFX (underH K hs c) y) :
    UnderHStep (P := P) K hs c y := by
  obtain ⟨s, f, cs⟩ := c
  generalize hx : underH K hs ⟨s, f, cs⟩ = x at h
  cases h with
  | ctxHandler h' => exact case_ctxHandler hx h'
  | @seq _ _ _ _ _ _ vs es _ rest h' hne =>
    have hc : cvals vs ++ es ++ rest = [AdminFX.handler hs (cs.map .core)] := by
      simp only [underH, onHandler, ConfigFX.mk.injEq] at hx
      exact hx.2.2.2.symm
    exact (no_step_nil h' (seq_single rfl hne hc)).elim
  | @handlerVals _ _ _ _ vs => exact case_result (.values vs) hx
  | trapHandler => exact case_result .trap hx
  | @throwHandler _ _ _ _ a => exact case_result (.throw a) hx
  | @brHandler _ _ _ _ _ l _ => exact case_escape (Or.inl ⟨l, rfl⟩) hx
  | returnHandler => exact case_escape (Or.inr rfl) hx
  | suspend => exact (case_plug hx).elim
  | switch => exact (case_plug (pre := cvals _ ++ [.contRef _]) (by simpa using hx)).elim
  | _ => underH_absurd hx

end Silmaril.Proofs.Wasm.Models.FXLower
