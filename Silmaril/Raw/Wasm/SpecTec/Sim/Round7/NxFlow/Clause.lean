module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Entry2

/-!
# Round 7, REH route 2: premises and the body of a clause (unrefined)

`prems_ok`: premises keep the clause's scope conforming (only `let` binds). `clause_ok`: a clause
that passes the flow check and the side conditions returns a conforming value, given
`NxSound.DefsVT` below the current fuel.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## Premises -/

theorem premRounds_ok {env : Env} {k : Nat} {ρ ρ' : VarEnv} {pr : Prem}
    {xvs : List (IL.Id × Value)} {ido : Option IL.Id} {n : Nat}
    (h : premRounds k env ρ pr xvs ido n = .ok ρ') : ρ' = ρ := by
  cases k with
  | zero => simp [premRounds] at h
  | succ k =>
    simp only [premRounds, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok,
      Except.ok.injEq] at h
    obtain ⟨_, _, _, _, _, rfl⟩ := h
    rfl

theorem premIter_ok {env : Env} {k : Nat} {ρ ρ' : VarEnv} {pr : Prem} {it : Iter}
    {ds : List Dom} (h : premIter k env ρ pr it ds = .ok ρ') : ρ' = ρ := by
  cases k with
  | zero => simp [premIter] at h
  | succ k =>
    cases it with
    | opt =>
      simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      split at h
      · cases h; rfl
      · split at h
        · simp only [Res.bind_eq_ok, Except.ok.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          rfl
        · cases h
    | list =>
      simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      exact premRounds_ok h
    | list1 =>
      simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨_, _, _, _, _, _, h⟩ := h
      exact premRounds_ok h
    | listN eₙ ido =>
      simp only [premIter, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨_, _, _, _, _, _, h⟩ := h
      exact premRounds_ok h

/-- **One premise keeps the scope conforming.** -/
theorem prem_ok {env : Env} {S : Sig} {T : TSig} {Γ : List (String × AT)} {c : AuxCtx}
    {ρ₀ : VarEnv} {k : Nat}
    (hC : ∀ ρ : VarEnv, ρ.defs = ρ₀.defs → ρ.typs = ρ₀.typs → CallH S T c env ρ k) :
    ∀ (pr : Prem) (ρ ρ' : VarEnv), ScopeVT S Γ ρ → ρ.defs = ρ₀.defs → ρ.typs = ρ₀.typs →
      premTy S T Γ pr = true → premAux c pr = true → premHolds k env ρ pr = .ok ρ' →
      MatchOk S Γ ρ ρ'
  | pr, ρ, ρ', hρ, hd, ht, hp, ha, hm => by
    cases k with
    | zero => simp [premHolds] at hm
    | succ k =>
    cases pr with
    | ifPr e =>
      simp only [premHolds, Res.bind_eq_ok, Res.assert_eq_ok, Except.ok.injEq] at hm
      obtain ⟨_, _, _, rfl⟩ := hm
      exact MatchOk.refl hρ
    | elsePr =>
      simp only [premHolds, Except.ok.injEq] at hm
      subst hm; exact MatchOk.refl hρ
    | letPr e₁ e₂ =>
      simp only [premTy, Bool.and_eq_true] at hp
      simp only [premAux] at ha
      simp only [premHolds, Res.bind_eq_ok] at hm
      obtain ⟨v, hv, hm⟩ := hm
      have hcall := (hC ρ hd ht).mono (Nat.le_succ k)
      have he := (expAt env k).exp S T Γ c ρ e₂ v hρ hcall hp.1 ha hv
      exact (matchAt env k).exp S T Γ ρ e₁ _ v ρ' hρ hp.2 he.ty hm
    | rulePr x args op e =>
      simp only [premHolds, Res.bind_eq_ok] at hm
      obtain ⟨_, _, _, _, hm⟩ := hm
      split at hm
      · cases hm; exact MatchOk.refl hρ
      · cases hm
    | iterPr pr ie =>
      obtain ⟨it, ds⟩ := ie
      simp only [premHolds] at hm
      rw [premIter_ok hm]
      exact MatchOk.refl hρ

theorem foldlM_prems_ok {env : Env} {S : Sig} {T : TSig} {Γ : List (String × AT)} {c : AuxCtx}
    {ρ₀ : VarEnv} {k : Nat}
    (hC : ∀ ρ : VarEnv, ρ.defs = ρ₀.defs → ρ.typs = ρ₀.typs → CallH S T c env ρ k) :
    ∀ (prems : List Prem) (ρ ρ' : VarEnv), ScopeVT S Γ ρ → ρ.defs = ρ₀.defs →
      ρ.typs = ρ₀.typs → (∀ pr ∈ prems, premTy S T Γ pr = true ∧ premAux c pr = true) →
      prems.foldlM (fun ρ' pr => premHolds k env ρ' pr) ρ = .ok ρ' → MatchOk S Γ ρ ρ'
  | [], ρ, ρ', hρ, _, _, _, hm => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hm
    subst hm; exact MatchOk.refl hρ
  | pr :: prems, ρ, ρ', hρ, hd, ht, hp, hm => by
    simp only [List.foldlM_cons, Res.bind_eq_ok] at hm
    obtain ⟨ρ₁, h₁, h₂⟩ := hm
    have hp0 := hp pr (List.mem_cons_self ..)
    have m₁ := prem_ok hC pr ρ ρ₁ hρ hd ht hp0.1 hp0.2 h₁
    exact m₁.trans (foldlM_prems_ok hC prems ρ₁ ρ' m₁.1 (m₁.2.1.trans hd) (m₁.2.2.trans ht)
      (fun q hq => hp q (List.mem_cons_of_mem _ hq)) h₂)

/-- **Premises keep the scope conforming.** -/
theorem prems_ok {env : Env} {S : Sig} {T : TSig} {Γ : List (String × AT)} {c : AuxCtx}
    {ρ₀ : VarEnv} {k : Nat}
    (hC : ∀ ρ : VarEnv, ρ.defs = ρ₀.defs → ρ.typs = ρ₀.typs → CallH S T c env ρ k)
    (prems : List Prem) (ρ' : VarEnv) (hρ : ScopeVT S Γ ρ₀)
    (hp : ∀ pr ∈ prems, premTy S T Γ pr = true ∧ premAux c pr = true)
    (hm : premsHold k env ρ₀ prems = .ok ρ') : MatchOk S Γ ρ₀ ρ' := by
  cases k with
  | zero => simp [premsHold] at hm
  | succ k =>
    simp only [premsHold] at hm
    exact foldlM_prems_ok (fun ρ hd ht => (hC ρ hd ht).mono (Nat.le_succ k)) prems ρ₀ ρ' hρ rfl
      rfl hp hm

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
