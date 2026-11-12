module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Match

/-!
# Round 7, REH route 2: the matching members, one step, and `MatchAt` at every fuel
(unrefined)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {env : Env} {n : Nat} {S : Sig} {T : TSig} {Γ : List (String × AT)}

theorem bindVal_defs (ρ : VarEnv) (x : IL.Id) (v : Value) : (ρ.bindVal x v).defs = ρ.defs := rfl

theorem bindVal_typs (ρ : VarEnv) (x : IL.Id) (v : Value) : (ρ.bindVal x v).typs = ρ.typs := rfl

set_option maxHeartbeats 1000000 in
/-- **`matchExp`, one step.** -/
theorem step_mexp (ih : MatchAt env n) (ρ : VarEnv) (e : Exp) (a : AT) (v : Value)
    (ρ' : VarEnv) (hρ : ScopeVT S Γ ρ) (hp : patTy S T Γ a e = true) (hv : vtB S a v = true)
    (hm : matchExp (n + 1) env ρ e v = .ok ρ') : MatchOk S Γ ρ ρ' := by
  cases e with
  | varE x =>
    simp only [patTy, Bool.and_eq_true] at hp
    simp only [matchExp] at hm
    split at hm
    · split at hm
      · cases hm; exact MatchOk.refl hρ
      · cases hm
    · cases hm
      refine ⟨hρ.bindVal hp.1 fun b hb => ?_, rfl, rfl⟩
      rw [hb] at hp
      exact vtB_of_atLe S _ _ _ hp.2 v hv
  | boolE b =>
    simp only [matchExp, Res.assert_eq_ok, Except.ok.injEq] at hm
    obtain ⟨_, rfl⟩ := hm; exact MatchOk.refl hρ
  | numE m =>
    simp only [matchExp, Res.assert_eq_ok, Except.ok.injEq] at hm
    obtain ⟨_, rfl⟩ := hm; exact MatchOk.refl hρ
  | textE t =>
    simp only [matchExp, Res.assert_eq_ok, Except.ok.injEq] at hm
    obtain ⟨_, rfl⟩ := hm; exact MatchOk.refl hρ
  | unE op t e =>
    simp only [patTy, Bool.and_eq_true] at hp
    have hb : ∀ m, vtB S .base (Value.num m) = true := fun m => base_of_nxB (nxB_num m)
    cases op <;> cases v
    all_goals simp only [matchExp] at hm
    all_goals first
      | (rw [matchDefault_ok hm]; exact MatchOk.refl hρ)
      | (simp only [Res.assert_eq_ok] at hm
         exact ih.exp S T Γ ρ e .base _ ρ' hρ hp.1 (hb _) hm.2)
      | (simp only [Res.assert_eq_ok, Res.bind_eq_ok, Res.ofOption_eq_ok] at hm
         obtain ⟨_, m', _, hm⟩ := hm
         exact ih.exp S T Γ ρ e .base _ ρ' hρ hp.1 (hb _) hm)
  | tupE es =>
    simp only [patTy] at hp
    simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asTuple?_eq_some] at hm
    obtain ⟨vs, rfl, hm⟩ := hm
    refine ih.exps S T Γ ρ es vs ρ' hρ (fun i e w he hw => ⟨compOf S a i, ?_, ?_⟩) hm
    · simpa using patT_get hp i e he
    · exact vtB_compOf hv hw
  | projE e i =>
    simp only [matchExp] at hm
    simp only [patTy] at hp
    split at hm
    · rename_i hi0
      simp only [hi0, ite_true] at hp
      exact ih.exp S T Γ ρ e _ _ ρ' hρ hp (vtB_tup1 hv) hm
    · rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | caseE op e =>
    simp only [patTy] at hp
    simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hm
    obtain ⟨⟨op', w⟩, hc, hm⟩ := hm
    simp only [Res.assert_eq_ok] at hm
    obtain ⟨rfl, hm⟩ := hm
    rw [Value.asCase?_eq_some] at hc
    subst hc
    exact ih.exp S T Γ ρ e _ w ρ' hρ hp (vtB_caseOf' hv) hm
  | uncaseE e op =>
    simp only [patTy] at hp
    simp only [matchExp] at hm
    refine ih.exp S T Γ ρ e _ _ ρ' hρ hp ?_ hm
    split
    · rename_i hn
      exact base_of_nxB (by simp only [nxB]; exact nxB_of_vtB hn hv)
    · exact vtB_unk S _
  | optE eo =>
    cases eo with
    | none =>
      simp only [matchExp, Res.assert_eq_ok, Except.ok.injEq] at hm
      obtain ⟨_, rfl⟩ := hm; exact MatchOk.refl hρ
    | some e =>
      simp only [patTy] at hp
      simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asOpt?_eq_some] at hm
      obtain ⟨o, rfl, w, rfl, hm⟩ := hm
      exact ih.exp S T Γ ρ e _ w ρ' hρ hp (vtB_elemOpt hv) hm
  | theE e => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | strE fs =>
    simp only [patTy] at hp
    simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asStruct?_eq_some] at hm
    obtain ⟨gs, rfl, hm⟩ := hm
    exact ih.fields S T Γ ρ a fs gs ρ' hρ hp (vtB_fieldOf'_mem hv) hm
  | dotE e k => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | compE e₁ e₂ => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | listE es =>
    simp only [patTy] at hp
    simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?_eq_some] at hm
    obtain ⟨vs, rfl, hm⟩ := hm
    refine ih.exps S T Γ ρ es vs ρ' hρ (fun i e w he hw => ⟨elemOf S a, ?_, ?_⟩) hm
    · exact patL_mem hp e (List.mem_of_getElem? he)
    · exact vtB_elem hv w (List.mem_of_getElem? hw)
  | liftE e => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | memE e₁ e₂ => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | lenE e => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | catE e₁ e₂ =>
    simp only [patTy, Bool.and_eq_true] at hp
    simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?_eq_some] at hm
    obtain ⟨vs, rfl, hm⟩ := hm
    have hb : ∀ l : List Value, (∀ w ∈ l, w ∈ vs) →
        vtB S (if iterLike S a then a else .unk) (.list l) = true := by
      intro l hl
      split
      · exact vtB_sublist hv hl
      · exact vtB_unk S _
    have key : ∀ j ρ'', (do
        let ρ₁ ← matchExp n env ρ e₁ (.list (vs.take j))
        matchExp n env ρ₁ e₂ (.list (vs.drop j))) = Except.ok ρ'' → MatchOk S Γ ρ ρ'' := by
      intro j ρ'' h
      simp only [Res.bind_eq_ok] at h
      obtain ⟨ρ₁, h₁, h₂⟩ := h
      have m₁ := ih.exp S T Γ ρ e₁ _ _ ρ₁ hρ hp.1 (hb _ fun w hw => List.mem_of_mem_take hw) h₁
      exact m₁.trans (ih.exp S T Γ ρ₁ e₂ _ _ ρ'' m₁.1 hp.2
        (hb _ fun w hw => List.mem_of_mem_drop hw) h₂)
    rcases elimUndef_eq_ok hm with ⟨k, _, hk⟩ | ⟨_, hk⟩
    · simp only [Res.assert_eq_ok] at hk
      exact key k ρ' hk.2
    · rcases elimUndef_eq_ok hk with ⟨k, _, hk'⟩ | ⟨_, hk'⟩
      · simp only [Res.assert_eq_ok] at hk'
        exact key _ ρ' hk'.2
      · obtain ⟨j, _, _, hj⟩ := Res.scan_eq_ok _ _ hk'
        exact key j ρ' hj
  | idxE e₁ e₂ => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | sliceE e₁ e₂ e₃ =>
    simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | updE e₁ p e₂ => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | extE e₁ p e₂ => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | callE f xs => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | iterE e ie =>
    obtain ⟨it, ds⟩ := ie
    simp only [matchExp] at hm
    exact ih.iter S T Γ ρ e it ds a v ρ' hρ hp hv hm
  | cvtE e t₁ t₂ =>
    simp only [patTy, Bool.and_eq_true] at hp
    cases v
    all_goals simp only [matchExp] at hm
    all_goals first
      | (rw [matchDefault_ok hm]; exact MatchOk.refl hρ)
      | (simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at hm
         obtain ⟨m', _, hm⟩ := hm
         exact ih.exp S T Γ ρ e .base _ ρ' hρ hp.1 (base_of_nxB (nxB_num _)) hm)
  | subE e t₁ t₂ =>
    simp only [patTy] at hp
    simp only [matchExp] at hm
    exact ih.exp S T Γ ρ e a v ρ' hρ hp hv hm
  | binE op t e₁ e₂ => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ
  | cmpE op t e₁ e₂ => simp only [matchExp] at hm; rw [matchDefault_ok hm]; exact MatchOk.refl hρ

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
