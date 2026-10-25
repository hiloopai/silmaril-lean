module

public import Silmaril.Logic.SetTheory.Inductive.MetamathHilbert

@[expose] public section

/-!
# Exact ZF schema instances as actual native inferences

Every independent finite named schema compiles to an application of its actual
native ZF0 assertion. Sorting uses only occurring set-variable names. The
frame declares the disjoint pairs of its occurring distinct names; separation
freshness is checked syntactically, including binder occurrences.
-/

namespace Silmaril.Logic.SetTheory.Inductive.MetamathZF

open Silmaril.Logic.Metamath Grammar

set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 1500000

/-- Substitution of set names and a finite predicate into native ZF templates. -/
def schemaSubst (a b c d : Native.V) (p : Named.Formula Native.V) :
    Native.V → Tree Native.L Native.V
  | .x => .var a
  | .y => .var b
  | .z => .var c
  | .w => .var d
  | .ph => encode p
  | v => .var v

/-- The exact nine native nonlogical ZF0 assertions. -/
def setAxioms : Set (TAssertion Native.L Native.C Native.V) :=
  {B | B = Peano.ZF.axExt ∨ B = Peano.ZF.axRep ∨ B = Peano.ZF.axSep ∨ B = Peano.ZF.axNul ∨ B = Peano.ZF.axPow ∨ B = Peano.ZF.axPr ∨ B = Peano.ZF.axUn ∨ B = Peano.ZF.axReg ∨ B = Peano.ZF.axInf}

/-- Compile each exact independent ZF schema to the real native ZF0 rule. -/
theorem schema_native {Δ : Set (TAssertion Native.L Native.C Native.V)}
    (hset : setAxioms ⊆ Δ) {A : TAssertion Native.L Native.C Native.V} {p : Named.Formula Native.V} (hs : ZF.Schema p)
    (hctx : ∀ v ∈ p.vars, A.ctx v .setvar)
    (hd : ∀ a ∈ p.vars, ∀ b ∈ p.vars, a ≠ b → A.Disjoint a b) :
    Nonempty (TDerivation Native.grammar Δ A (T.pf (encode p))) := by
  cases hs with
  | ext a b c hn =>
    let τ := schemaSubst a b c c (.eq a a)
    have hB : Peano.ZF.axExt ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axExt hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axExt, TAssertion.ctx, Peano.ZF.fs] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .var (hctx a (by simp [ZF.Axioms.ext, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.ext, Named.Formula.vars]))
        · exact .var (hctx c (by simp [ZF.Axioms.ext, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axExt, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axExt, Peano.ZF.dvs] at hxy
        rcases hxy with hxy | hxy | hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.ext, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axExt, TExpr.subst, τ, schemaSubst, ZF.Axioms.ext, encode] using d⟩
  | rep a b c d p hn =>
    let τ := schemaSubst a b c d p
    have hB : Peano.ZF.axRep ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axRep hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axRep, TAssertion.ctx, Peano.ZF.fs, Peano.ZF.fw] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · apply encode_sorted_on_vars p
          intro v hv
          exact hctx v (by simp [ZF.Axioms.rep, Named.Formula.vars, hv])
        · exact .var (hctx a (by simp [ZF.Axioms.rep, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.rep, Named.Formula.vars]))
        · exact .var (hctx c (by simp [ZF.Axioms.rep, Named.Formula.vars]))
        · exact .var (hctx d (by simp [ZF.Axioms.rep, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axRep, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axRep, Peano.ZF.dvs] at hxy
        rcases hxy with hxy | hxy | hxy | hxy | hxy | hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.rep, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axRep, TExpr.subst, τ, schemaSubst, ZF.Axioms.rep, encode] using d⟩
  | sep a b c p hn hf hi =>
    let τ := schemaSubst a b c c p
    have hB : Peano.ZF.axSep ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axSep hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axSep, TAssertion.ctx, Peano.ZF.fs, Peano.ZF.fw] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · apply encode_sorted_on_vars p
          intro v hv
          exact hctx v (by simp [ZF.Axioms.sep, Named.Formula.vars, hv])
        · exact .var (hctx a (by simp [ZF.Axioms.sep, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.sep, Named.Formula.vars]))
        · exact .var (hctx c (by simp [ZF.Axioms.sep, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axSep, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axSep, Peano.ZF.dvs] at hxy
        rcases hxy with hxy | hxy | hxy | hxy | hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.sep, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axSep, TExpr.subst, τ, schemaSubst, ZF.Axioms.sep, encode] using d⟩
  | nul a b hn =>
    let τ := schemaSubst a b b b (.eq a a)
    have hB : Peano.ZF.axNul ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axNul hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axNul, TAssertion.ctx, Peano.ZF.fs] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .var (hctx a (by simp [ZF.Axioms.nul, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.nul, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axNul, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axNul, Peano.ZF.dvs] at hxy
        rcases hxy with hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.nul, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axNul, TExpr.subst, τ, schemaSubst, ZF.Axioms.nul, encode] using d⟩
  | pow a b c d hn =>
    let τ := schemaSubst a b c d (.eq a a)
    have hB : Peano.ZF.axPow ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axPow hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axPow, TAssertion.ctx, Peano.ZF.fs] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .var (hctx a (by simp [ZF.Axioms.pow, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.pow, Named.Formula.vars]))
        · exact .var (hctx c (by simp [ZF.Axioms.pow, Named.Formula.vars]))
        · exact .var (hctx d (by simp [ZF.Axioms.pow, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axPow, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axPow, Peano.ZF.dvs] at hxy
        rcases hxy with hxy | hxy | hxy | hxy | hxy | hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.pow, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axPow, TExpr.subst, τ, schemaSubst, ZF.Axioms.pow, encode] using d⟩
  | pair a b c d hn hm =>
    let τ := schemaSubst a b c d (.eq a a)
    have hB : Peano.ZF.axPr ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axPr hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axPr, TAssertion.ctx, Peano.ZF.fs] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .var (hctx a (by simp [ZF.Axioms.pair, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.pair, Named.Formula.vars]))
        · exact .var (hctx c (by simp [ZF.Axioms.pair, Named.Formula.vars]))
        · exact .var (hctx d (by simp [ZF.Axioms.pair, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axPr, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axPr, Peano.ZF.dvs] at hxy
        rcases hxy with hxy | hxy | hxy | hxy | hxy | hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.pair, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axPr, TExpr.subst, τ, schemaSubst, ZF.Axioms.pair, encode] using d⟩
  | union a b c d hn =>
    let τ := schemaSubst a b c d (.eq a a)
    have hB : Peano.ZF.axUn ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axUn hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axUn, TAssertion.ctx, Peano.ZF.fs] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .var (hctx a (by simp [ZF.Axioms.union, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.union, Named.Formula.vars]))
        · exact .var (hctx c (by simp [ZF.Axioms.union, Named.Formula.vars]))
        · exact .var (hctx d (by simp [ZF.Axioms.union, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axUn, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axUn, Peano.ZF.dvs] at hxy
        rcases hxy with hxy | hxy | hxy | hxy | hxy | hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.union, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axUn, TExpr.subst, τ, schemaSubst, ZF.Axioms.union, encode] using d⟩
  | reg a b c hn =>
    let τ := schemaSubst a b c c (.eq a a)
    have hB : Peano.ZF.axReg ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axReg hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axReg, TAssertion.ctx, Peano.ZF.fs] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .var (hctx a (by simp [ZF.Axioms.reg, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.reg, Named.Formula.vars]))
        · exact .var (hctx c (by simp [ZF.Axioms.reg, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axReg, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axReg, Peano.ZF.dvs] at hxy
        rcases hxy with hxy | hxy | hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.reg, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axReg, TExpr.subst, τ, schemaSubst, ZF.Axioms.reg, encode] using d⟩
  | inf a b c d hn =>
    let τ := schemaSubst a b c d (.eq a a)
    have hB : Peano.ZF.axInf ∈ Δ := hset (by simp [setAxioms])
    have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axInf hB τ
      (by
        intro v s hv
        simp [Peano.ZF.axInf, TAssertion.ctx, Peano.ZF.fs] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .var (hctx a (by simp [ZF.Axioms.inf, Named.Formula.vars]))
        · exact .var (hctx b (by simp [ZF.Axioms.inf, Named.Formula.vars]))
        · exact .var (hctx c (by simp [ZF.Axioms.inf, Named.Formula.vars]))
        · exact .var (hctx d (by simp [ZF.Axioms.inf, Named.Formula.vars]))
      )
      (by intro e he; simp [Peano.ZF.axInf, TAssertion.essentials] at he)
      (by
        intro x y hxy u hu v hv
        simp [Peano.ZF.axInf, Peano.ZF.dvs] at hxy
        rcases hxy with hxy | hxy | hxy | hxy | hxy | hxy
        all_goals cases hxy
        all_goals simp [τ, schemaSubst] at hu hv
        all_goals have hne : u ≠ v := by intro he; simp_all
        all_goals refine ⟨hne, hd u ?_ v ?_ hne⟩
        all_goals simp_all [ZF.Axioms.inf, Named.Formula.vars])
    exact ⟨by simpa [Peano.ZF.axInf, TExpr.subst, τ, schemaSubst, ZF.Axioms.inf, encode] using d⟩

/-- Native DV safety implies distinctness of substituted set-variable names. -/
theorem dv_distinct {B A : TAssertion Native.L Native.C Native.V}
    {τ : Native.V → Tree Native.L Native.V} (h : B.DVSafe τ A.Disjoint)
    {x y a b : Native.V} (hxy : (x, y) ∈ B.dv ∨ (y, x) ∈ B.dv)
    (hx : τ x = .var a) (hy : τ y = .var b) : a ≠ b := by
  rcases hxy with hxy | hxy
  · exact (h x y hxy a (by simp [hx]) b (by simp [hy])).1
  · exact (h y x hxy b (by simp [hy]) a (by simp [hx])).1.symm

/-- Reflect every native nonlogical ZF schema instance, including all its
substitution and disjoint-variable restrictions, into independent finite syntax. -/
theorem native_schema_instance {B A : TAssertion Native.L Native.C Native.V}
    (hB : B ∈ setAxioms) (τ : Native.V → Tree Native.L Native.V)
    (hpure : ∀ v s, A.ctx v s → s = .setvar)
    (hsort : ∀ v s, B.ctx v s → Native.grammar.HasSort A.ctx (τ v) s)
    (hdv : B.DVSafe τ A.Disjoint) :
    ∃ p : Named.Formula Native.V, ZF.Schema p ∧ B.concl.subst τ = T.pf (encode p) := by
  have scalar : ∀ v, B.ctx v .setvar → ∃ a, τ v = .var a := by
    intro v hv
    exact Peano.ZF.hasSort_setCtx_setvar ((hsort v .setvar hv).mono (fun v s hs => hpure v s hs))
  have predicate : ∀ v, B.ctx v .wff → ∃ p : Named.Formula Native.V, encode p = τ v := by
    intro v hv
    exact pure_exists_encode _ ((hsort v .wff hv).mono (fun v s hs => hpure v s hs))
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axExt, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axExt, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨c, hc⟩ := scalar .z (by simp [Peano.ZF.axExt, TAssertion.ctx, Peano.ZF.fs])
    have hab : a ≠ b := dv_distinct hdv (x := .x) (y := .y) (by decide) ha hb
    have hac : a ≠ c := dv_distinct hdv (x := .x) (y := .z) (by decide) ha hc
    have hbc : b ≠ c := dv_distinct hdv (x := .y) (y := .z) (by decide) hb hc
    have hn0 : [a, b, c].Nodup := by simp [hab, hac, hbc]
    refine ⟨ZF.Axioms.ext a b c, .ext a b c hn0, ?_⟩
    simp [Peano.ZF.axExt, TExpr.subst, ZF.Axioms.ext, encode, ha, hb, hc]
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axRep, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axRep, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨c, hc⟩ := scalar .z (by simp [Peano.ZF.axRep, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨d, hd⟩ := scalar .w (by simp [Peano.ZF.axRep, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨p, hp⟩ := predicate .ph (by simp [Peano.ZF.axRep, TAssertion.ctx, Peano.ZF.fw])
    have hab : a ≠ b := dv_distinct hdv (x := .x) (y := .y) (by decide) ha hb
    have hac : a ≠ c := dv_distinct hdv (x := .x) (y := .z) (by decide) ha hc
    have had : a ≠ d := dv_distinct hdv (x := .x) (y := .w) (by decide) ha hd
    have hbc : b ≠ c := dv_distinct hdv (x := .y) (y := .z) (by decide) hb hc
    have hbd : b ≠ d := dv_distinct hdv (x := .y) (y := .w) (by decide) hb hd
    have hcd : c ≠ d := dv_distinct hdv (x := .z) (y := .w) (by decide) hc hd
    have hn0 : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
    refine ⟨ZF.Axioms.rep a b c d p, .rep a b c d p hn0, ?_⟩
    simp [Peano.ZF.axRep, TExpr.subst, ZF.Axioms.rep, encode, ha, hb, hc, hd, ← hp]
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axSep, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axSep, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨c, hc⟩ := scalar .z (by simp [Peano.ZF.axSep, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨p, hp⟩ := predicate .ph (by simp [Peano.ZF.axSep, TAssertion.ctx, Peano.ZF.fw])
    have hab : a ≠ b := dv_distinct hdv (x := .x) (y := .y) (by decide) ha hb
    have hac : a ≠ c := dv_distinct hdv (x := .x) (y := .z) (by decide) ha hc
    have hbc : b ≠ c := dv_distinct hdv (x := .y) (y := .z) (by decide) hb hc
    have hn0 : [a, b, c].Nodup := by simp [hab, hac, hbc]
    have hfb : b ∉ p.vars := by
      intro hv
      exact (hdv .y .ph (by decide) b (by simp [hb]) b
        (by simpa [← hp] using hv)).1 rfl
    have hfc : c ∉ p.vars := by
      intro hv
      exact (hdv .z .ph (by decide) c (by simp [hc]) c
        (by simpa [← hp] using hv)).1 rfl
    refine ⟨ZF.Axioms.sep a b c p, .sep a b c p hn0 hfb hfc, ?_⟩
    simp [Peano.ZF.axSep, TExpr.subst, ZF.Axioms.sep, encode, ha, hb, hc, ← hp]
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axNul, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axNul, TAssertion.ctx, Peano.ZF.fs])
    have hab : a ≠ b := dv_distinct hdv (x := .x) (y := .y) (by decide) ha hb
    have hn0 : [a, b].Nodup := by simp [hab]
    refine ⟨ZF.Axioms.nul a b, .nul a b hn0, ?_⟩
    simp [Peano.ZF.axNul, TExpr.subst, ZF.Axioms.nul, encode, ha, hb]
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axPow, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axPow, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨c, hc⟩ := scalar .z (by simp [Peano.ZF.axPow, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨d, hd⟩ := scalar .w (by simp [Peano.ZF.axPow, TAssertion.ctx, Peano.ZF.fs])
    have hab : a ≠ b := dv_distinct hdv (x := .x) (y := .y) (by decide) ha hb
    have hac : a ≠ c := dv_distinct hdv (x := .x) (y := .z) (by decide) ha hc
    have had : a ≠ d := dv_distinct hdv (x := .x) (y := .w) (by decide) ha hd
    have hbc : b ≠ c := dv_distinct hdv (x := .y) (y := .z) (by decide) hb hc
    have hbd : b ≠ d := dv_distinct hdv (x := .y) (y := .w) (by decide) hb hd
    have hcd : c ≠ d := dv_distinct hdv (x := .z) (y := .w) (by decide) hc hd
    have hn0 : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
    refine ⟨ZF.Axioms.pow a b c d, .pow a b c d hn0, ?_⟩
    simp [Peano.ZF.axPow, TExpr.subst, ZF.Axioms.pow, encode, ha, hb, hc, hd]
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axPr, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axPr, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨c, hc⟩ := scalar .z (by simp [Peano.ZF.axPr, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨d, hd⟩ := scalar .w (by simp [Peano.ZF.axPr, TAssertion.ctx, Peano.ZF.fs])
    have hac : a ≠ c := dv_distinct hdv (x := .x) (y := .z) (by decide) ha hc
    have had : a ≠ d := dv_distinct hdv (x := .x) (y := .w) (by decide) ha hd
    have hcd : c ≠ d := dv_distinct hdv (x := .z) (y := .w) (by decide) hc hd
    have hbc : b ≠ c := dv_distinct hdv (x := .y) (y := .z) (by decide) hb hc
    have hbd : b ≠ d := dv_distinct hdv (x := .y) (y := .w) (by decide) hb hd
    have hn0 : [a, c, d].Nodup := by simp [hac, had, hcd]
    have hn1 : [b, c, d].Nodup := by simp [hcd, hbc, hbd]
    refine ⟨ZF.Axioms.pair a b c d, .pair a b c d hn0 hn1, ?_⟩
    simp [Peano.ZF.axPr, TExpr.subst, ZF.Axioms.pair, encode, ha, hb, hc, hd]
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axUn, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axUn, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨c, hc⟩ := scalar .z (by simp [Peano.ZF.axUn, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨d, hd⟩ := scalar .w (by simp [Peano.ZF.axUn, TAssertion.ctx, Peano.ZF.fs])
    have hab : a ≠ b := dv_distinct hdv (x := .x) (y := .y) (by decide) ha hb
    have hac : a ≠ c := dv_distinct hdv (x := .x) (y := .z) (by decide) ha hc
    have had : a ≠ d := dv_distinct hdv (x := .x) (y := .w) (by decide) ha hd
    have hbc : b ≠ c := dv_distinct hdv (x := .y) (y := .z) (by decide) hb hc
    have hbd : b ≠ d := dv_distinct hdv (x := .y) (y := .w) (by decide) hb hd
    have hcd : c ≠ d := dv_distinct hdv (x := .z) (y := .w) (by decide) hc hd
    have hn0 : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
    refine ⟨ZF.Axioms.union a b c d, .union a b c d hn0, ?_⟩
    simp [Peano.ZF.axUn, TExpr.subst, ZF.Axioms.union, encode, ha, hb, hc, hd]
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axReg, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axReg, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨c, hc⟩ := scalar .z (by simp [Peano.ZF.axReg, TAssertion.ctx, Peano.ZF.fs])
    have hab : a ≠ b := dv_distinct hdv (x := .x) (y := .y) (by decide) ha hb
    have hac : a ≠ c := dv_distinct hdv (x := .x) (y := .z) (by decide) ha hc
    have hbc : b ≠ c := dv_distinct hdv (x := .y) (y := .z) (by decide) hb hc
    have hn0 : [a, b, c].Nodup := by simp [hab, hac, hbc]
    refine ⟨ZF.Axioms.reg a b c, .reg a b c hn0, ?_⟩
    simp [Peano.ZF.axReg, TExpr.subst, ZF.Axioms.reg, encode, ha, hb, hc]
  · obtain ⟨a, ha⟩ := scalar .x (by simp [Peano.ZF.axInf, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨b, hb⟩ := scalar .y (by simp [Peano.ZF.axInf, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨c, hc⟩ := scalar .z (by simp [Peano.ZF.axInf, TAssertion.ctx, Peano.ZF.fs])
    obtain ⟨d, hd⟩ := scalar .w (by simp [Peano.ZF.axInf, TAssertion.ctx, Peano.ZF.fs])
    have hab : a ≠ b := dv_distinct hdv (x := .x) (y := .y) (by decide) ha hb
    have hac : a ≠ c := dv_distinct hdv (x := .x) (y := .z) (by decide) ha hc
    have had : a ≠ d := dv_distinct hdv (x := .x) (y := .w) (by decide) ha hd
    have hbc : b ≠ c := dv_distinct hdv (x := .y) (y := .z) (by decide) hb hc
    have hbd : b ≠ d := dv_distinct hdv (x := .y) (y := .w) (by decide) hb hd
    have hcd : c ≠ d := dv_distinct hdv (x := .z) (y := .w) (by decide) hc hd
    have hn0 : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
    refine ⟨ZF.Axioms.inf a b c d, .inf a b c d hn0, ?_⟩
    simp [Peano.ZF.axInf, TExpr.subst, ZF.Axioms.inf, encode, ha, hb, hc, hd]

/-- The native common fragment: four propositional rules and the nine ZF schemata. -/
def zfFragment : Set (TAssertion Native.L Native.C Native.V) := propAxioms ∪ setAxioms

/-- All fragment assertions are genuine axioms/rules of the existing native ZF0. -/
theorem zfFragment_subset_ZF0 : zfFragment ⊆ Peano.ZF.ZF0 := by
  intro B h
  rcases h with h | h
  · exact propAxioms_subset_ZF0 h
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨("ax-ext", _), by simp [Peano.ZF.axiomList, Peano.ZF.axExt], by decide, rfl⟩
    · exact ⟨("ax-rep", _), by simp [Peano.ZF.axiomList, Peano.ZF.axRep], by decide, rfl⟩
    · exact ⟨("ax-sep", _), by simp [Peano.ZF.axiomList, Peano.ZF.axSep], by decide, rfl⟩
    · exact ⟨("ax-nul", _), by simp [Peano.ZF.axiomList, Peano.ZF.axNul], by decide, rfl⟩
    · exact ⟨("ax-pow", _), by simp [Peano.ZF.axiomList, Peano.ZF.axPow], by decide, rfl⟩
    · exact ⟨("ax-pr", _), by simp [Peano.ZF.axiomList, Peano.ZF.axPr], by decide, rfl⟩
    · exact ⟨("ax-un", _), by simp [Peano.ZF.axiomList, Peano.ZF.axUn], by decide, rfl⟩
    · exact ⟨("ax-reg", _), by simp [Peano.ZF.axiomList, Peano.ZF.axReg], by decide, rfl⟩
    · exact ⟨("ax-inf", _), by simp [Peano.ZF.axiomList, Peano.ZF.axInf], by decide, rfl⟩

/-- Declare every unordered pair of distinct names of a finite native frame. -/
def zfFrame (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) : TAssertion Native.L Native.C Native.V :=
  { proofFrame S Γ p with dv := Peano.ZF.dvs S.dedup }

@[simp] theorem zfFrame_ctx (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) (v : Native.V) (s : Native.C) :
    (zfFrame S Γ p).ctx v s ↔ v ∈ S ∧ s = .setvar := proofFrame_ctx S Γ p v s

@[simp] theorem zfFrame_essentials (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) :
    (zfFrame S Γ p).essentials = Γ.map (fun q => T.pf (encode q)) := proofFrame_essentials S Γ p

/-- The expanded native `$d` list covers every distinct pair of its members. -/
theorem dvs_disjoint (S : List Native.V) {a b : Native.V} (ha : a ∈ S) (hb : b ∈ S)
    (hne : a ≠ b) : (a, b) ∈ Peano.ZF.dvs S ∨ (b, a) ∈ Peano.ZF.dvs S := by
  induction S with
  | nil => simp at ha
  | cons x S ih =>
    rcases List.mem_cons.mp ha with rfl | hta
    · have hb' : b ∈ S := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      exact Or.inl (by simp [Peano.ZF.dvs, hb'])
    · rcases List.mem_cons.mp hb with rfl | htb
      · exact Or.inr (by simp [Peano.ZF.dvs, hta])
      · rcases ih hta htb with h | h
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr (List.mem_append_right _ h)

/-- Native disjoint pairs mention only names from their generating list. -/
theorem dvs_members (S : List Native.V) {a b : Native.V} (h : (a, b) ∈ Peano.ZF.dvs S) :
    a ∈ S ∧ b ∈ S := by
  induction S with
  | nil => simp [Peano.ZF.dvs] at h
  | cons x S ih =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨z, hz, he⟩ := List.mem_map.mp h
      cases he
      exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hz⟩
    · obtain ⟨ha, hb⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩

/-- Expanding a duplicate-free `$d` list never creates a reflexive disjoint pair. -/
theorem dvs_irrefl (S : List Native.V) (hS : S.Nodup) {a b : Native.V}
    (h : (a, b) ∈ Peano.ZF.dvs S) : a ≠ b := by
  induction S with
  | nil => simp [Peano.ZF.dvs] at h
  | cons x S ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp hS
    rcases List.mem_append.mp h with h | h
    · obtain ⟨z, hz, he⟩ := List.mem_map.mp h
      cases he
      exact fun he => hx (he ▸ hz)
    · exact ih ht h

/-- The generated native frame is genuinely well formed, including finite floating
hypotheses, typed essentials/conclusion and nonreflexive disjoint declarations. -/
theorem zfFrame_wellFormed (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) (hp : ∀ v ∈ p.vars, v ∈ S)
    (hΓ : ∀ q ∈ Γ, ∀ v ∈ q.vars, v ∈ S) : (zfFrame S Γ p).WellFormed Native.grammar where
  floats_nodup := by
    simp [zfFrame, proofFrame, TAssertion.floats, List.filterMap_map, List.map_map]
    exact List.nodup_dedup S
  float_sort := by
    intro v s hs
    have he := ((zfFrame_ctx S Γ p v s).mp hs).2
    cases he
    rfl
  ess_wellTyped := by
    intro e he
    rw [zfFrame_essentials] at he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact ⟨.wff, rfl, encode_sorted_on_vars q (fun v hv =>
      (zfFrame_ctx S Γ p v .setvar).mpr ⟨hΓ q hq v hv, rfl⟩)⟩
  concl_wellTyped := ⟨.wff, rfl, encode_sorted_on_vars p (fun v hv =>
    (zfFrame_ctx S Γ p v .setvar).mpr ⟨hp v hv, rfl⟩)⟩
  dv_irrefl := fun _ _ h => dvs_irrefl S.dedup (List.nodup_dedup S) h
  dv_float := by
    intro a b hab
    obtain ⟨ha, hb⟩ := dvs_members S.dedup hab
    exact ⟨⟨.setvar, (zfFrame_ctx S Γ p a .setvar).mpr ⟨List.mem_dedup.mp ha, rfl⟩⟩,
      ⟨.setvar, (zfFrame_ctx S Γ p b .setvar).mpr ⟨List.mem_dedup.mp hb, rfl⟩⟩⟩

/-- Independent Hilbert ZF proofs compile to actual native fragment derivations. -/
noncomputable def zfToNative {Γ : List (Named.Formula Native.V)} {p : Named.Formula Native.V}
    (d : Named.Hilbert ZF.Schema Γ p) :
    TDerivation Native.grammar zfFragment
      (zfFrame (d.vars ++ Γ.flatMap Named.Formula.vars) Γ p) (T.pf (encode p)) := by
  let S := d.vars ++ Γ.flatMap Named.Formula.vars
  let A := zfFrame S Γ p
  apply hilbertToNative (A := A) (fun _ h => Or.inl h) ?_ ?_ d ?_
  · intro q hq
    rw [zfFrame_essentials]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  · intro q hq hctx
    apply _root_.Classical.choice
    apply schema_native (fun _ h => Or.inr h) hq hctx
    intro a ha b hb hne
    have ha' : a ∈ S.dedup := List.mem_dedup.mpr ((zfFrame_ctx S Γ p a .setvar).mp (hctx a ha)).1
    have hb' : b ∈ S.dedup := List.mem_dedup.mpr ((zfFrame_ctx S Γ p b .setvar).mp (hctx b hb)).1
    exact dvs_disjoint S.dedup ha' hb' hne
  · intro v hv
    exact (zfFrame_ctx S Γ p v .setvar).mpr ⟨List.mem_append_left _ hv, rfl⟩

/-- The compiler yields native proof objects with an explicit empty dummy extension.
Intermediate names are declared in the finite frame, rather than hidden in a
semantic agreement theorem. -/
noncomputable def zfToNativeProof {Γ : List (Named.Formula Native.V)} {p : Named.Formula Native.V}
    (d : Named.Hilbert ZF.Schema Γ p) :
    TProof Native.grammar zfFragment (zfFrame (d.vars ++ Γ.flatMap Named.Formula.vars) Γ p) := by
  refine ⟨TDummies.none _, ?_⟩
  rw [TAssertion.extend_none]
  exact zfToNative d

/-- The actual compiler's finite frame passes the native well-formedness specification. -/
theorem zfToNative_wellFormed {Γ : List (Named.Formula Native.V)} {p : Named.Formula Native.V}
    (d : Named.Hilbert ZF.Schema Γ p) :
    (zfFrame (d.vars ++ Γ.flatMap Named.Formula.vars) Γ p).WellFormed Native.grammar :=
  zfFrame_wellFormed _ Γ p (fun v hv => List.mem_append_left _ (d.conclusion_vars v hv))
    (fun q hq _v hv => List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hv⟩))

/-- Independent proofs yield theorems of native ZF0 with the same explicit finite frame. -/
theorem zfToNative_derivable {Γ : List (Named.Formula Native.V)} {p : Named.Formula Native.V}
    (d : Named.Hilbert ZF.Schema Γ p) :
    TDerivable Native.grammar Peano.ZF.ZF0 (zfFrame (d.vars ++ Γ.flatMap Named.Formula.vars) Γ p) := by
  refine ⟨⟨TDummies.none _, ?_⟩⟩
  rw [TAssertion.extend_none]
  exact (zfToNative d).mono zfFragment_subset_ZF0

/-- Reuse the existing certified tree-to-string inference morphism, rather than
identifying semantic agreement with a native database proof. -/
theorem zfToNative_stringDerivable {Γ : List (Named.Formula Native.V)} {p : Named.Formula Native.V}
    (d : Named.Hilbert ZF.Schema Γ p) :
    Silmaril.Logic.Metamath.Derivable (Native.grammar.axioms Peano.ZF.ZF0)
      ((zfFrame (d.vars ++ Γ.flatMap Named.Formula.vars) Γ p).flatten Native.grammar) :=
  (zfToNative_derivable d).flatten

/-- Actual native inference objects reflect to independent Hilbert ZF syntax. -/
theorem nativeToZF {Γ : List (Named.Formula Native.V)} {A : TAssertion Native.L Native.C Native.V}
    (hpure : ∀ v s, A.ctx v s → s = .setvar)
    (hΓ : ∀ e ∈ A.essentials, ∃ p ∈ Γ, e = T.pf (encode p))
    {e : TExpr Native.L Native.C Native.V} (d : TDerivation Native.grammar zfFragment A e) :
    ∃ p : Named.Formula Native.V, e = T.pf (encode p) ∧ Nonempty (Named.Hilbert ZF.Schema Γ p) := by
  apply nativeToHilbertWithAxioms hpure hΓ ?_ d
  intro B hB τ hs hdv
  rcases hB with hB | hB
  · exact Or.inl hB
  · obtain ⟨p, hp, he⟩ := native_schema_instance hB τ hpure hs hdv
    exact Or.inr ⟨p, hp, he⟩

/-- Bidirectional derivability over the explicit common ZF schema/propositional fragment.
Quantifier/equality inference rules and definition elimination are not included
in `zfFragment` and require separate correspondence/conservativity proofs. -/
theorem zf_fragment_correspondence (Γ : List (Named.Formula Native.V)) (p : Named.Formula Native.V) :
    Nonempty (Named.Hilbert ZF.Schema Γ p) ↔
    ∃ A : TAssertion Native.L Native.C Native.V,
      A.WellFormed Native.grammar ∧
      (∀ v s, A.ctx v s → s = .setvar) ∧
      (∀ e ∈ A.essentials, ∃ q ∈ Γ, e = T.pf (encode q)) ∧
      (∀ q ∈ Γ, T.pf (encode q) ∈ A.essentials) ∧
      Nonempty (TDerivation Native.grammar zfFragment A (T.pf (encode p))) := by
  constructor
  · rintro ⟨d⟩
    let S := d.vars ++ Γ.flatMap Named.Formula.vars
    refine ⟨zfFrame S Γ p, zfToNative_wellFormed d, ?_, ?_, ?_, ⟨zfToNative d⟩⟩
    · intro v s hs
      exact ((zfFrame_ctx S Γ p v s).mp hs).2
    · intro e he
      rw [zfFrame_essentials] at he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      exact ⟨q, hq, rfl⟩
    · intro q hq
      rw [zfFrame_essentials]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
  · rintro ⟨A, _, hpure, hΓ, _, ⟨d⟩⟩
    obtain ⟨q, he, hd⟩ := nativeToZF hpure hΓ d
    have hq : q = p := encode_injective (congrArg TExpr.tree he).symm
    exact hq ▸ hd

/-- A nontrivial independent ZF derivation: extensionality applied by modus ponens. -/
def extensionalityApplication {V : Type*} (a b c : V) (hn : [a, b, c].Nodup) :
    Named.Hilbert ZF.Schema [.all c (.iff (.mem c a) (.mem c b))] (.eq a b) :=
  .mp (.ax (.ext a b c hn)) (.hyp (by simp))

/-- Transport the multi-step extensionality proof into the actual native ZF system. -/
noncomputable def nativeExtensionalityApplication (a b c : Native.V) (hn : [a, b, c].Nodup) :=
  (zfToNative (extensionalityApplication a b c hn)).mono zfFragment_subset_ZF0

/-- Finite named Hilbert ZF derivations also produce scoped natural-deduction objects. -/
noncomputable def hilbertToScopedZF {n : Nat} {Γ : List (Named.Formula (Fin n))}
    {p : Named.Formula (Fin n)} (d : Named.Hilbert ZF.Schema Γ p) :
    ZF.Derivation (Γ.map (Named.Formula.lower id)) (p.lower id) :=
  d.toClassical id (fun q hq => .ax ⟨n, q, some ∘ id, hq, Named.Formula.scope_total q id⟩)

end Silmaril.Logic.SetTheory.Inductive.MetamathZF
