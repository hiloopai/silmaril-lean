module

public import Silmaril.Logic.Metamath.Grammar.Derivation
public import Silmaril.Logic.Metatheory.InferenceMorphism

@[expose] public section

/-!
# Trees and strings

The tree layer and the string layer of a grammatical system agree.

* A well-sorted tree has a syntax proof of its flattening from the syntax
  axioms (`syntax_derivation`).
* Flattening a tree derivation gives a string derivation from the syntax
  axioms and the flattened logical axioms (`TDerivation.nonempty_flatten`,
  `TDerivable.flatten`, `flattenMorphism`).
* A string derivation of an expression at a syntax typecode is a parse: it
  yields a well-sorted tree with that flattening (`exists_tree_of_derivation`).
* For an unambiguous grammar and well-formed axioms, every string derivation of
  the flattening of a well-typed tree expression comes from a tree derivation
  (`nonempty_tderivation_of_derivation`). Hence a well-formed tree assertion is
  a tree theorem exactly when its flattening is a string theorem
  (`tderivable_iff_derivable`).

The last equivalence relies on each dummy variable of a string proof having a
single floating hypothesis (the `nodup` field of `Dummies`), as the Metamath
specification requires. A dummy variable with floating hypotheses at two
typecodes has no well-defined sort, and without that field the equivalence
fails: `Silmaril.Logic.Metamath.Grammar.DualSort` gives an unambiguous grammar
and well-formed axioms with such a string proof of a formula that has no tree
proof.
-/

namespace Silmaril.Logic.Metamath

open Cslib.Logic Silmaril.Logic.Metatheory

universe u

variable {C V : Type u}

namespace Grammar

variable {L : Type u} [DecidableEq V] {G : Grammar L C V}

/-- The variable context of the floating hypotheses of a string assertion. -/
def floatCtx (A : Assertion C V) (v : V) (s : C) : Prop := Hyp.float s v ∈ A.hyps

/-- A well-sorted tree has a syntax proof of its flattening. -/
theorem syntax_derivation {Δ : Set (Assertion C V)} (hΔ : G.syntaxAxioms ⊆ Δ)
    {A : Assertion C V} {t : Tree L V} {s : C} (h : G.HasSort (floatCtx A) t s) :
    Nonempty (Derivation Δ A ⟨s, G.flatten t⟩) := by
  induction h with
  | @var v s hv =>
    refine ⟨.hyp ?_⟩
    simp only [Assertion.hypExprs, List.mem_map]
    exact ⟨_, hv, by simp⟩
  | @node l args hlen hargs ih =>
    let σ := G.argSubst l (args.map G.flatten)
    have hR : (G.rule l).toAssertion ∈ Δ := hΔ ⟨l, rfl⟩
    have premises : ∀ e ∈ (G.rule l).toAssertion.hypExprs,
        Nonempty (Derivation Δ A (e.subst σ)) := by
      intro e he
      simp only [Assertion.hypExprs, SyntaxRule.toAssertion, List.map_map, List.mem_map,
        Function.comp_apply, Hyp.expr_float] at he
      obtain ⟨p, hp, rfl⟩ := he
      obtain ⟨c, hc⟩ := exists_mem_zip_of_mem_right hlen hp
      have hσ : σ p.2 = G.flatten c := argSubst_flatten hc
      have := ih (c, p) hc
      simpa [Expr.subst, Str.subst, hσ] using this
    have d := Derivation.app _ hR σ (fun e he => Classical.choice (premises e he))
      (by simp [Assertion.DVSafe, SyntaxRule.toAssertion])
    rw [flatten_node]
    exact ⟨d⟩

namespace TDerivation

variable {Γ : Set (TAssertion L C V)}

theorem floatCtx_flatten {A : TAssertion L C V} {v : V} {s : C} :
    floatCtx (A.flatten G) v s ↔ A.ctx v s :=
  TAssertion.float_mem_flatten

/-- Flattening a tree derivation gives a string derivation. -/
theorem nonempty_flatten {A : TAssertion L C V} {e : TExpr L C V}
    (d : TDerivation G Γ A e) : Nonempty (Derivation (G.axioms Γ) (A.flatten G) (e.flatten G)) := by
  induction d with
  | hyp h => exact ⟨.hyp (TAssertion.mem_hypExprs_flatten.2 (Or.inr ⟨_, h, rfl⟩))⟩
  | app B hB τ sorted premises dv ih =>
    let σ : Subst C V := fun v => G.flatten (τ v)
    have prem : ∀ e ∈ (B.flatten G).hypExprs,
        Nonempty (Derivation (G.axioms Γ) (A.flatten G) (e.subst σ)) := by
      intro e he
      rcases TAssertion.mem_hypExprs_flatten.1 he with ⟨s, v, hv, rfl⟩ | ⟨e', he', rfl⟩
      · have h := syntax_derivation (Δ := G.axioms Γ) (A := A.flatten G) Set.subset_union_left
          ((sorted v s hv).mono fun _ _ h => (floatCtx_flatten (A := A)).2 h)
        simpa [Expr.subst, Str.subst, σ] using h
      · rw [← TExpr.flatten_subst]
        exact ih e' he'
    have d := Derivation.app (B.flatten G) (Or.inr ⟨B, hB, rfl⟩) σ
      (fun e he => Classical.choice (prem e he))
      (fun x y hxy a ha b hb =>
        dv x y hxy a (mem_vars_of_mem_vars_flatten ha) b (mem_vars_of_mem_vars_flatten hb))
    rw [TExpr.flatten_subst]
    exact ⟨d⟩

end TDerivation

/-- A tree theorem flattens to a string theorem of the syntax axioms and the
flattened logical axioms. -/
theorem TDerivable.flatten {Γ : Set (TAssertion L C V)} {A : TAssertion L C V}
    (h : TDerivable G Γ A) : Derivable (G.axioms Γ) (A.flatten G) := by
  obtain ⟨⟨D, d⟩⟩ := h
  obtain ⟨d'⟩ := d.nonempty_flatten
  rw [TAssertion.flatten_extend] at d'
  exact derivable_iff.2 ⟨D.flatten, ⟨d'⟩⟩

/-- Flattening as a morphism of inference systems. -/
noncomputable def flattenMorphism (G : Grammar L C V) (Γ : Set (TAssertion L C V)) :
    InferenceMorphism (TSystem G Γ) (System (G.axioms Γ)) (TAssertion L C V) (Assertion C V) where
  map := TAssertion.flatten G
  mapDerivation := fun {A} p =>
    ⟨p.1.flatten, (TAssertion.flatten_extend (A := A) p.1) ▸
      Classical.choice p.2.nonempty_flatten⟩

/-- A string derivation at a syntax typecode is a parse: it yields a
well-sorted tree with the derived string as flattening. The axioms at syntax
typecodes must be syntax axioms, and the essential hypotheses of the frame must
not be at syntax typecodes. -/
theorem exists_tree_of_derivation {Δ : Set (Assertion C V)}
    (hΔ : ∀ B ∈ Δ, B.concl.tc ∈ G.sorts → B ∈ G.syntaxAxioms) {A : Assertion C V}
    (hA : ∀ e ∈ A.essentials, e.tc ∉ G.sorts) {e : Expr C V} (d : Derivation Δ A e)
    (he : e.tc ∈ G.sorts) : ∃ t, G.HasSort (floatCtx A) t e.tc ∧ G.flatten t = e.body := by
  induction d with
  | hyp h =>
    simp only [Assertion.hypExprs, List.mem_map] at h
    obtain ⟨hh, hmem, rfl⟩ := h
    cases hh with
    | float s v => exact ⟨.var v, .var hmem, by simp⟩
    | ess e' =>
      have he' : e' ∈ A.essentials := by
        simp only [Assertion.essentials, List.mem_filterMap]
        exact ⟨_, hmem, rfl⟩
      exact absurd he (hA e' he')
  | app B hB σ premises dv ih =>
    obtain ⟨l, rfl⟩ := hΔ B hB he
    have hargs : ∀ p ∈ (G.rule l).args,
        ∃ t, G.HasSort (floatCtx A) t p.1 ∧ G.flatten t = σ p.2 := by
      intro p hp
      have hmem : (⟨p.1, [.var p.2]⟩ : Expr C V) ∈ (G.rule l).toAssertion.hypExprs := by
        simp only [Assertion.hypExprs, SyntaxRule.toAssertion, List.map_map, List.mem_map]
        exact ⟨p, hp, rfl⟩
      simpa [Expr.subst, Str.subst] using ih _ hmem (G.rule_args l p hp)
    obtain ⟨ts, hts⟩ := exists_forall₂_of_forall hargs
    obtain ⟨hlen, hzip⟩ := List.forall₂_iff_zip.1 hts
    refine ⟨.node l ts, .node hlen fun p hp => (hzip hp).1, ?_⟩
    exact flatten_node_of_forall₂ (hts.imp fun _ _ h => h.2)

/-- Parses in the frame of a flattened tree assertion. -/
theorem exists_tree_of_derivation_flatten {Γ : Set (TAssertion L C V)}
    (hΓ : ∀ B ∈ Γ, B.WellFormed G) {A : TAssertion L C V}
    (hA : ∀ e ∈ A.essentials, e.WellTyped G A.ctx) {e : Expr C V}
    (d : Derivation (G.axioms Γ) (A.flatten G) e) (he : e.tc ∈ G.sorts) :
    ∃ t, G.HasSort A.ctx t e.tc ∧ G.flatten t = e.body := by
  have hΔ : ∀ B ∈ G.axioms Γ, B.concl.tc ∈ G.sorts → B ∈ G.syntaxAxioms := by
    rintro B (hB | ⟨B', hB', rfl⟩) hs
    · exact hB
    · obtain ⟨s, hs', -⟩ := (hΓ B' hB').concl_wellTyped
      exact absurd hs (G.prov_not_sort hs')
  have hA' : ∀ e ∈ (A.flatten G).essentials, e.tc ∉ G.sorts := by
    intro e he
    obtain ⟨e', he', rfl⟩ := TAssertion.mem_essentials_flatten.1 he
    obtain ⟨s, hs, -⟩ := hA e' he'
    exact G.prov_not_sort hs
  obtain ⟨t, ht, hf⟩ := exists_tree_of_derivation hΔ hA' d he
  exact ⟨t, ht.mono fun _ _ h => TDerivation.floatCtx_flatten.1 h, hf⟩

omit [DecidableEq V] in
theorem TAssertion.WellFormed.sort_unique {B : TAssertion L C V} (hB : B.WellFormed G)
    {v : V} {s s' : C} (h : B.ctx v s) (h' : B.ctx v s') : s = s' :=
  TAssertion.functional_ctx hB.floats_nodup v s s' h h'

/-- For an unambiguous grammar and well-formed axioms, a string derivation of
the flattening of a well-sorted tree at a provable typecode comes from a tree
derivation. The frame must have a functional context and well-typed essential
hypotheses. -/
theorem nonempty_tderivation_of_derivation (hG : G.Unambiguous)
    {Γ : Set (TAssertion L C V)} (hΓ : ∀ B ∈ Γ, B.WellFormed G) {A : TAssertion L C V}
    (hfun : Functional A.ctx) (hA : ∀ e ∈ A.essentials, e.WellTyped G A.ctx) {e : Expr C V}
    (d : Derivation (G.axioms Γ) (A.flatten G) e) {s : C} (hs : G.prov e.tc = some s)
    {t : Tree L V} (ht : G.HasSort A.ctx t s) (hflat : G.flatten t = e.body) :
    Nonempty (TDerivation G Γ A ⟨e.tc, t⟩) := by
  induction d generalizing s t with
  | hyp h =>
    rcases TAssertion.mem_hypExprs_flatten.1 h with ⟨s', v, hv, rfl⟩ | ⟨e', he', rfl⟩
    · exfalso
      have hvt : v ∈ t.vars := mem_vars_of_mem_vars_flatten (G := G) (by
        rw [hflat]; simp [Str.vars])
      obtain ⟨s'', hs'', hv''⟩ := ht.sort_of_mem_vars (G.prov_sort hs) hvt
      rw [hfun v s' s'' hv hv''] at hs
      exact G.prov_not_sort hs hs''
    · obtain ⟨s0, hs0, ht0⟩ := hA e' he'
      simp only [TExpr.flatten_tc] at hs
      rw [hs] at hs0
      cases hs0
      have : t = e'.tree := hG _ hfun _ _ _ ht ht0 hflat
      subst this
      exact ⟨.hyp he'⟩
  | app B hB σ premises dv ih =>
    rcases hB with ⟨l, rfl⟩ | ⟨B, hB, rfl⟩
    · exact absurd (G.rule_tc l) (G.prov_not_sort hs)
    have wf := hΓ B hB
    -- Parse the substituted floating variables.
    have hτ : ∀ v s', B.ctx v s' → ∃ tv, G.HasSort A.ctx tv s' ∧ G.flatten tv = σ v := by
      intro v s' hv
      have hmem : (⟨s', [.var v]⟩ : Expr C V) ∈ (B.flatten G).hypExprs :=
        TAssertion.mem_hypExprs_flatten.2 (Or.inl ⟨s', v, hv, rfl⟩)
      simpa [Expr.subst, Str.subst] using
        exists_tree_of_derivation_flatten hΓ hA (premises _ hmem) (wf.float_sort v s' hv)
    classical
    let τ : V → Tree L V := fun v =>
      if h : ∃ tv s', B.ctx v s' ∧ G.HasSort A.ctx tv s' ∧ G.flatten tv = σ v then
        Classical.choose h
      else .var v
    have hτs : ∀ v s', B.ctx v s' → G.HasSort A.ctx (τ v) s' ∧ G.flatten (τ v) = σ v := by
      intro v s' hv
      have h : ∃ tv s', B.ctx v s' ∧ G.HasSort A.ctx tv s' ∧ G.flatten tv = σ v :=
        let ⟨tv, htv⟩ := hτ v s' hv
        ⟨tv, s', hv, htv⟩
      obtain ⟨s'', hv'', hs'', hf''⟩ := Classical.choose_spec h
      simp only [τ, h, ↓reduceDIte]
      rw [wf.sort_unique hv'' hv] at hs''
      exact ⟨hs'', hf''⟩
    have sorted : ∀ v s', B.ctx v s' → G.HasSort A.ctx (τ v) s' := fun v s' h => (hτs v s' h).1
    -- Substitution commutes with flattening on well-typed expressions of `B`.
    have hsub : ∀ (e' : TExpr L C V), e'.WellTyped G B.ctx →
        ∃ s', G.prov e'.tc = some s' ∧ G.HasSort A.ctx (e'.tree.subst τ) s' ∧
          G.flatten (e'.tree.subst τ) = Str.subst σ (G.flatten e'.tree) := by
      rintro e' ⟨s', hs', ht'⟩
      refine ⟨s', hs', ht'.subst sorted, ?_⟩
      rw [flatten_subst]
      apply Str.subst_congr
      intro v hv
      obtain ⟨s'', -, hv''⟩ := ht'.sort_of_mem_vars (G.prov_sort hs')
        (mem_vars_of_mem_vars_flatten hv)
      exact (hτs v s'' hv'').2
    have prem : ∀ e' ∈ B.essentials, Nonempty (TDerivation G Γ A (e'.subst τ)) := by
      intro e' he'
      obtain ⟨s', hs', ht', hf'⟩ := hsub e' (wf.ess_wellTyped e' he')
      have hmem : e'.flatten G ∈ (B.flatten G).hypExprs :=
        TAssertion.mem_hypExprs_flatten.2 (Or.inr ⟨e', he', rfl⟩)
      exact ih _ hmem hs' ht' hf'
    have dv' : B.DVSafe τ A.Disjoint := by
      intro x y hxy a ha b hb
      obtain ⟨⟨sx, hx⟩, ⟨sy, hy⟩⟩ := wf.dv_float x y hxy
      have ha' : a ∈ Str.vars (σ x) := by
        rw [← (hτs x sx hx).2]; exact (sorted x sx hx).mem_vars_flatten.2 ha
      have hb' : b ∈ Str.vars (σ y) := by
        rw [← (hτs y sy hy).2]; exact (sorted y sy hy).mem_vars_flatten.2 hb
      exact dv x y hxy a ha' b hb'
    have d := TDerivation.app B hB τ sorted (fun e' he' => Classical.choice (prem e' he')) dv'
    obtain ⟨sc, hsc, htc, hfc⟩ := hsub B.concl wf.concl_wellTyped
    simp only [Expr.subst_tc, TAssertion.flatten_concl, TExpr.flatten_tc] at hs
    rw [hs] at hsc
    cases hsc
    have : t = B.concl.tree.subst τ := hG _ hfun _ _ _ ht htc (by rw [hflat, hfc]; rfl)
    subst this
    exact ⟨d⟩

/-- For an unambiguous grammar and well-formed axioms, a well-formed tree
assertion is a tree theorem exactly when its flattening is a string theorem of
the syntax axioms and the flattened logical axioms. -/
theorem tderivable_iff_derivable (hG : G.Unambiguous) {Γ : Set (TAssertion L C V)}
    (hΓ : ∀ B ∈ Γ, B.WellFormed G) {A : TAssertion L C V} (hA : A.WellFormed G) :
    TDerivable G Γ A ↔ Derivable (G.axioms Γ) (A.flatten G) := by
  refine ⟨TDerivable.flatten, fun h => ?_⟩
  obtain ⟨D, ⟨d⟩⟩ := derivable_iff.1 h
  let D' : TDummies A :=
    { floats := D.floats
      dv := D.dv
      fresh := fun p hp h => D.fresh p hp (TAssertion.mem_allVars_flatten hA h)
      dv_dummy := D.dv_dummy
      nodup := D.nodup }
  have hD : D'.flatten (G := G) = D := rfl
  rw [← hD, ← TAssertion.flatten_extend] at d
  obtain ⟨s, hs, ht⟩ := hA.concl_wellTyped
  have hA' : ∀ e ∈ (A.extend D').essentials, e.WellTyped G (A.extend D').ctx := by
    intro e he
    rw [TAssertion.essentials_extend] at he
    exact (hA.ess_wellTyped e he).mono (TAssertion.ctx_le_extend D')
  exact tderivable_iff.2 ⟨D', nonempty_tderivation_of_derivation hG hΓ
    (TAssertion.functional_ctx_extend hA.floats_nodup D') hA' d hs
    (ht.mono (TAssertion.ctx_le_extend D')) rfl⟩

end Grammar

end Silmaril.Logic.Metamath
