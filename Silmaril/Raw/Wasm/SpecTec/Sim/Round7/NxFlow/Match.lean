module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.StepIter

/-!
# Round 7, REH route 2: matching keeps scopes conforming (unrefined)

`matchAt : ∀ k, MatchAt env k`: a pattern that passes `NxTyped.patTy` at a type its value
conforms to binds conforming values, at every fuel. Forms the matcher only evaluates and
compares (`matchDefault`) bind nothing.
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

/-! ## Helpers -/

theorem MatchOk.refl {ρ : VarEnv} (h : ScopeVT S Γ ρ) : MatchOk S Γ ρ ρ := ⟨h, rfl, rfl⟩

theorem MatchOk.trans {ρ ρ₁ ρ₂ : VarEnv} (h₁ : MatchOk S Γ ρ ρ₁) (h₂ : MatchOk S Γ ρ₁ ρ₂) :
    MatchOk S Γ ρ ρ₂ := ⟨h₂.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem matchDefault_ok {k : Nat} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h : matchDefault k env ρ e v = .ok ρ') : ρ' = ρ := by
  cases k with
  | zero => simp [matchDefault] at h
  | succ k =>
    simp only [matchDefault, Res.bind_eq_ok, Res.assert_eq_ok, Except.ok.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h
    rfl

theorem elimUndef_eq_ok {α β : Type} {r : Res α} {f : α → Res β} {g : Unit → Res β} {b : β}
    (h : Res.elimUndef r f g = .ok b) :
    (∃ a, r = .ok a ∧ f a = .ok b) ∨ (r = .error .undef ∧ g () = .ok b) := by
  cases r with
  | ok a => exact .inl ⟨a, rfl, h⟩
  | error e =>
    cases e with
    | undef => exact .inr ⟨rfl, h⟩
    | outOfFuel => cases h

theorem vtB_compOf {a : AT} {vs : List Value} {i : Nat} {w : Value}
    (h : vtB S a (.tuple vs) = true) (hi : vs[i]? = some w) : vtB S (compOf S a i) w = true := by
  cases hn : nxAT S.good a
  · have hc : compOf S a i = compTy S a i := by
      unfold compOf compTy; simp only [hn, Bool.false_eq_true, ite_false]
      generalize unf S a = u; cases u <;> rfl
    rw [hc]; exact vtB_proj h hi
  · simp only [compOf, hn, ite_true]
    have := nxB_of_vtB hn h
    simp only [nxB] at this
    exact base_of_nxB ((nxBs_iff vs).1 this w (List.mem_of_getElem? hi))

theorem vtB_tup1 {a : AT} {v : Value} (h : vtB S a v = true) :
    vtB S (.tup [a]) (.tuple [v]) = true := by
  cases hn : nxAT S.good a
  · have hn' : nxAT S.good (.tup [a]) = false := by simp [nxAT, nxATs, hn]
    rw [vtB_tup hn' (unf_tup S [a])]
    simp [vtT, h]
  · have hn' : nxAT S.good (.tup [a]) = true := by simp [nxAT, nxATs, hn]
    exact vtB_of_nxB' (by simp [nxB, nxBs, nxB_of_vtB hn h])

theorem vtB_caseOf' {a : AT} {op : MixopS} {w : Value} (h : vtB S a (.case op w) = true) :
    vtB S (caseOf' S a op) w = true := by
  cases hn : nxAT S.good a
  · have hc : caseOf' S a op = caseTy S a op := by
      unfold caseOf' caseTy; simp only [hn, Bool.false_eq_true, ite_false]
      generalize unf S a = u; cases u <;> rfl
    rw [hc]; exact vtB_payload h
  · simp only [caseOf', hn, ite_true]
    have := nxB_of_vtB hn h
    simp only [nxB] at this
    exact base_of_nxB this

theorem vtF_mem {n : String} : ∀ {gs : List (AtomS × Value)}, vtF S n gs = true →
    ∀ g ∈ gs, vtB S (fieldAT S n g.1) g.2 = true
  | [], _, g, hg => by simp at hg
  | (k, v) :: gs, h, g, hg => by
    simp only [vtF, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact h.1
    · exact vtF_mem h.2 g hg

theorem nxBf_mem : ∀ {gs : List (AtomS × Value)}, nxBf gs = true → ∀ g ∈ gs, nxB g.2 = true
  | [], _, g, hg => by simp at hg
  | (k, v) :: gs, h, g, hg => by
    simp only [nxBf, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact h.1.1
    · exact nxBf_mem h.2 g hg

theorem vtB_fieldOf'_mem {a : AT} {gs : List (AtomS × Value)}
    (h : vtB S a (.struct gs) = true) : ∀ g ∈ gs, vtB S (fieldOf' S a g.1) g.2 = true := by
  intro g hg
  cases hn : nxAT S.good a
  · rw [fieldOf'_eq hn]
    unfold fieldTy
    split
    · rename_i m xs hu
      rw [vtB_struct_name hn hu] at h
      exact vtF_mem h g hg
    · exact vtB_unk S _
  · simp only [fieldOf', hn, ite_true]
    have := nxB_of_vtB hn h
    simp only [nxB] at this
    exact base_of_nxB (nxBf_mem this g hg)

theorem patL_mem {b : AT} : ∀ {es : List Exp}, patL S T Γ b es = true →
    ∀ e ∈ es, patTy S T Γ b e = true
  | [], _, e, he => by simp at he
  | e' :: es, h, e, he => by
    simp only [patL, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact patL_mem h.2 e he

theorem patT_get {a : AT} : ∀ {i : Nat} {es : List Exp}, patT S T Γ a i es = true →
    ∀ (j : Nat) e, es[j]? = some e → patTy S T Γ (compOf S a (i + j)) e = true
  | _, [], _, j, e, he => by simp at he
  | i, e' :: es, h, j, e, he => by
    simp only [patT, Bool.and_eq_true] at h
    cases j with
    | zero => simp at he; subst he; simpa using h.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at he
      have := patT_get h.2 j e he
      rwa [show i + 1 + j = i + (j + 1) by omega] at this

theorem patD_get {Γi : List (String × AT)} : ∀ {ds : List Dom}, patD S T Γ Γi ds = true →
    ∀ d ∈ ds, patTy S T Γ (.iter ((Γi.lookup (domVar d)).getD .unk)) (domSrc d) = true
  | [], _, d, hd => by simp at hd
  | .mk x e :: ds, h, d, hd => by
    simp only [patD, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact patD_get h.2 d hd

/-- The variables an iteration pattern binds in its body are not bound in a conforming scope. -/
theorem fresh_of {ρ : VarEnv} (hρ : ScopeVT S Γ ρ) {it : Iter} {ds : List Dom}
    (hf : freshDoms Γ it ds = true) :
    ∀ x, ((domsΓ S Γ ds ++ counterΓ it).lookup x).isSome = true → ρ.findVal? x = none := by
  intro x hx
  simp only [freshDoms, Bool.and_eq_true, List.all_eq_true] at hf
  have hΓ : Γ.lookup x = none := by
    rw [lookup_append] at hx
    split at hx
    · rename_i a ha
      obtain ⟨d, hd, rfl⟩ := domsΓ_lookup_some ha
      have := hf.1 d hd
      cases d with
      | mk y e => simpa [domVar] using this
    · rcases counterΓ_cases it with hc | ⟨y, hc⟩
      · rw [hc] at hx; simp [List.lookup] at hx
      · rw [hc] at hx
        simp only [List.lookup] at hx
        split at hx
        · rename_i hy
          have : x = y := beq_iff_eq.1 hy
          subst this
          have h2 := hf.2
          revert hc h2
          unfold counterΓ
          split
          · intro hc h2; simp at hc; obtain ⟨rfl, -⟩ := hc; simpa using h2
          · intro hc; simp at hc
        · simp at hx
  cases hv : ρ.findVal? x with
  | none => rfl
  | some v => have := hρ.dom x v hv; rw [hΓ] at this; cases this

theorem scope_iter {ρ : VarEnv} (hρ : ScopeVT S Γ ρ) {it : Iter} {ds : List Dom}
    (hf : freshDoms Γ it ds = true) : ScopeVT S (iterΓ S Γ it ds) ρ := by
  have he : iterΓ S Γ it ds = (domsΓ S Γ ds ++ counterΓ it) ++ Γ := by
    simp [iterΓ, List.append_assoc]
  rw [he]
  exact hρ.prepend (fresh_of hρ hf)

theorem vtB_getD {Γi : List (String × AT)} {ρ : VarEnv} (h : ScopeVT S Γi ρ) {x : IL.Id}
    {w : Value} (hw : ρ.findVal? x = some w) : vtB S ((Γi.lookup x).getD .unk) w = true := by
  cases hx : Γi.lookup x with
  | none => exact vtB_unk S w
  | some a => exact h.val x a w hx hw

theorem findVals?_get {ρ : VarEnv} : ∀ {xs : List IL.Id} {ws : List Value},
    ρ.findVals? xs = some ws → ∀ (j : Nat) x w, xs[j]? = some x → ws[j]? = some w →
      ρ.findVal? x = some w := by
  intro xs ws h j x w hx hw
  have h2 := mapM_option_forall₂ (f := ρ.findVal?) h
  obtain ⟨hl, hall⟩ := List.forall₂_iff_get.1 h2
  have hj : j < xs.length := (List.getElem?_eq_some_iff.1 hx).1
  have hx' := (List.getElem?_eq_some_iff.1 hx).2
  have hw' := (List.getElem?_eq_some_iff.1 hw).2
  have := hall j hj (by omega)
  simp only [List.get_eq_getElem] at this
  rw [hx', hw'] at this
  exact this

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
