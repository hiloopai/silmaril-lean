module

public import Silmaril.Logic.SetTheory.Inductive.Hilbert
public import Silmaril.Logic.SetTheory.Inductive.MetamathZF

@[expose] public section

/-!
# Actual inference transport into native Metamath

The target is `Grammar.TDerivation`, including mandatory-hypothesis sorting
and disjointness checks. The independent Hilbert object supplies finite
syntactic support; all its names must be declared in the target frame. An
explicit extension map supplies native proofs of any additional nonlogical
axioms. No semantic truth premise is used by this transport.
-/

namespace Silmaril.Logic.SetTheory.Inductive.MetamathZF

open Silmaril.Logic.Metamath Grammar

set_option linter.constructorNameAsVariable false

/-- The actual four native propositional assertions, as a subtheory of ZF0. -/
def propAxioms : Set (TAssertion Native.L Native.C Native.V) :=
  {B | B = Peano.ZF.axMp ∨ B = Peano.ZF.ax1 ∨ B = Peano.ZF.ax2 ∨ B = Peano.ZF.ax3}

theorem propAxioms_subset_ZF0 : propAxioms ⊆ Peano.ZF.ZF0 := by
  intro B h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨("ax-mp", _), by simp [Peano.ZF.axiomList, Peano.ZF.axMp], by decide, rfl⟩
  · exact ⟨("ax-1", _), by simp [Peano.ZF.axiomList, Peano.ZF.ax1], by decide, rfl⟩
  · exact ⟨("ax-2", _), by simp [Peano.ZF.axiomList, Peano.ZF.ax2], by decide, rfl⟩
  · exact ⟨("ax-3", _), by simp [Peano.ZF.axiomList, Peano.ZF.ax3], by decide, rfl⟩

/-- Native substitution for the two formula metavariables of ax-1/ax-3/ax-mp. -/
def subst₂ (p q : Named.Formula Native.V) : Native.V → Tree Native.L Native.V
  | .ph => encode p
  | .ps => encode q
  | v => .var v

/-- Native substitution for ax-2's three formula metavariables. -/
def subst₃ (p q r : Named.Formula Native.V) : Native.V → Tree Native.L Native.V
  | .ph => encode p
  | .ps => encode q
  | .ch => encode r
  | v => .var v

variable {Δ : Set (TAssertion Native.L Native.C Native.V)}
  {A : TAssertion Native.L Native.C Native.V}

/-- Instantiate the actual native ax-1 assertion. -/
def nativeK (hB : Peano.ZF.ax1 ∈ Δ) (p q : Named.Formula Native.V)
    (hp : Native.grammar.HasSort A.ctx (encode p) .wff)
    (hq : Native.grammar.HasSort A.ctx (encode q) .wff) :
    TDerivation Native.grammar Δ A (T.pf (encode (.imp p (.imp q p)))) := by
  have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.ax1 hB (subst₂ p q)
    (by
      intro v s h
      simp [Peano.ZF.ax1, TAssertion.ctx, Peano.ZF.fw] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp
      · exact hq)
    (by intro e he; simp [Peano.ZF.ax1, TAssertion.essentials] at he)
    (by intro x y h; simp [Peano.ZF.ax1] at h)
  simpa [Peano.ZF.ax1, TExpr.subst, subst₂, encode] using d

/-- Instantiate the actual native ax-2 assertion. -/
def nativeS (hB : Peano.ZF.ax2 ∈ Δ) (p q r : Named.Formula Native.V)
    (hp : Native.grammar.HasSort A.ctx (encode p) .wff)
    (hq : Native.grammar.HasSort A.ctx (encode q) .wff)
    (hr : Native.grammar.HasSort A.ctx (encode r) .wff) :
    TDerivation Native.grammar Δ A
      (T.pf (encode (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r))))) := by
  have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.ax2 hB (subst₃ p q r)
    (by
      intro v s h
      simp [Peano.ZF.ax2, TAssertion.ctx, Peano.ZF.fw] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp
      · exact hq
      · exact hr)
    (by intro e he; simp [Peano.ZF.ax2, TAssertion.essentials] at he)
    (by intro x y h; simp [Peano.ZF.ax2] at h)
  simpa [Peano.ZF.ax2, TExpr.subst, subst₃, encode] using d

/-- Instantiate the actual native ax-3 assertion. -/
def nativeC (hB : Peano.ZF.ax3 ∈ Δ) (p q : Named.Formula Native.V)
    (hp : Native.grammar.HasSort A.ctx (encode p) .wff)
    (hq : Native.grammar.HasSort A.ctx (encode q) .wff) :
    TDerivation Native.grammar Δ A (T.pf (encode (.imp (.imp (.neg p) (.neg q)) (.imp q p)))) := by
  have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.ax3 hB (subst₂ p q)
    (by
      intro v s h
      simp [Peano.ZF.ax3, TAssertion.ctx, Peano.ZF.fw] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp
      · exact hq)
    (by intro e he; simp [Peano.ZF.ax3, TAssertion.essentials] at he)
    (by intro x y h; simp [Peano.ZF.ax3] at h)
  simpa [Peano.ZF.ax3, TExpr.subst, subst₂, encode] using d

/-- Apply native ax-mp, including its two mandatory essential hypotheses. -/
noncomputable def nativeMP (hB : Peano.ZF.axMp ∈ Δ) (p q : Named.Formula Native.V)
    (hp : Native.grammar.HasSort A.ctx (encode p) .wff)
    (hq : Native.grammar.HasSort A.ctx (encode q) .wff)
    (di : TDerivation Native.grammar Δ A (T.pf (encode (.imp p q))))
    (dp : TDerivation Native.grammar Δ A (T.pf (encode p))) :
    TDerivation Native.grammar Δ A (T.pf (encode q)) := by
  have d := TDerivation.app (G := Native.grammar) (A := A) Peano.ZF.axMp hB (subst₂ p q)
    (by
      intro v s h
      simp [Peano.ZF.axMp, TAssertion.ctx, Peano.ZF.fw] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp
      · exact hq)
    (by
      classical
      intro e he
      simp [Peano.ZF.axMp, TAssertion.essentials] at he
      by_cases h : e = T.pf (.var .ph)
      · subst e
        simpa [TExpr.subst, subst₂] using dp
      · have heq := he.resolve_left h
        subst e
        simpa [TExpr.subst, subst₂, encode] using di)
    (by intro x y h; simp [Peano.ZF.axMp] at h)
  simpa [Peano.ZF.axMp, TExpr.subst, subst₂] using d

/-- Proof-relevant inference transport with an explicit nonlogical extension map. -/
noncomputable def hilbertToNative {Ax : Set (Named.Formula Native.V)}
    {Γ : List (Named.Formula Native.V)}
    (hprop : propAxioms ⊆ Δ)
    (hΓ : ∀ p ∈ Γ, T.pf (encode p) ∈ A.essentials)
    (hAx : ∀ p ∈ Ax, (∀ v ∈ p.vars, A.ctx v .setvar) →
      TDerivation Native.grammar Δ A (T.pf (encode p)))
    {p : Named.Formula Native.V} (d : Named.Hilbert Ax Γ p)
    (hctx : ∀ v ∈ d.vars, A.ctx v .setvar) :
    TDerivation Native.grammar Δ A (T.pf (encode p)) := by
  induction d with
  | hyp hp => exact .hyp (hΓ _ hp)
  | ax hp => exact hAx _ hp hctx
  | k p q =>
    exact nativeK (hprop (Or.inr (Or.inl rfl))) p q
      (encode_sorted_on_vars p (fun v hv => hctx v (List.mem_append_left _ hv)))
      (encode_sorted_on_vars q (fun v hv => hctx v (List.mem_append_right _ hv)))
  | s p q r =>
    exact nativeS (hprop (Or.inr (Or.inr (Or.inl rfl)))) p q r
      (encode_sorted_on_vars p (fun v hv => hctx v (by simp [Named.Hilbert.vars, hv])))
      (encode_sorted_on_vars q (fun v hv => hctx v (by simp [Named.Hilbert.vars, hv])))
      (encode_sorted_on_vars r (fun v hv => hctx v (by simp [Named.Hilbert.vars, hv])))
  | c p q =>
    exact nativeC (hprop (Or.inr (Or.inr (Or.inr rfl)))) p q
      (encode_sorted_on_vars p (fun v hv => hctx v (List.mem_append_left _ hv)))
      (encode_sorted_on_vars q (fun v hv => hctx v (List.mem_append_right _ hv)))
  | @mp p q di dp ih ip =>
    have hi := fun v hv => hctx v (List.mem_append_left _ hv)
    have hp := fun v hv => hctx v (List.mem_append_right _ hv)
    exact nativeMP (hprop (Or.inl rfl)) p q
      (encode_sorted_on_vars p (fun v hv => hp v (dp.conclusion_vars v hv)))
      (encode_sorted_on_vars q (fun v hv => hi v (di.conclusion_vars v (List.mem_append_right _ hv))))
      (ih hi) (ip hp)

/-- Reflect every actual native propositional inference into independent syntax.
A pure frame assigns setvar sort to all its floating variables. The hypotheses
must be exactly represented finite formulas; there is no semantic premise. -/
theorem nativeToHilbertWithAxioms {Ax : Set (Named.Formula Native.V)} {Γ : List (Named.Formula Native.V)}
    (hpure : ∀ v s, A.ctx v s → s = .setvar)
    (hΓ : ∀ e ∈ A.essentials, ∃ p ∈ Γ, e = T.pf (encode p))
    (hLeaf : ∀ B ∈ Δ, ∀ τ : Native.V → Tree Native.L Native.V,
      (∀ v s, B.ctx v s → Native.grammar.HasSort A.ctx (τ v) s) →
      B.DVSafe τ A.Disjoint → B ∈ propAxioms ∨
        ∃ p ∈ Ax, B.concl.subst τ = T.pf (encode p))
    {e : TExpr Native.L Native.C Native.V}
    (d : TDerivation Native.grammar Δ A e) :
    ∃ p : Named.Formula Native.V, e = T.pf (encode p) ∧ Nonempty (Named.Hilbert Ax Γ p) := by
  induction d with
  | hyp he =>
    obtain ⟨p, hp, rfl⟩ := hΓ _ he
    exact ⟨p, rfl, ⟨.hyp hp⟩⟩
  | app B hB τ sorted premises dv ih =>
    have parse : ∀ v, B.ctx v .wff → ∃ p : Named.Formula Native.V, encode p = τ v := by
      intro v hv
      apply pure_exists_encode
      exact (sorted v .wff hv).mono (fun v s hs => hpure v s hs)
    rcases hLeaf B hB τ sorted dv with hprop | ⟨p, hp, he⟩
    ·
      rcases hprop with rfl | rfl | rfl | rfl
      · obtain ⟨p, hp⟩ := parse .ph (by simp [Peano.ZF.axMp, TAssertion.ctx, Peano.ZF.fw])
        obtain ⟨q, hq⟩ := parse .ps (by simp [Peano.ZF.axMp, TAssertion.ctx, Peano.ZF.fw])
        obtain ⟨r, er, ⟨dr⟩⟩ := ih (T.pf (.var .ph))
          (by simp [Peano.ZF.axMp, TAssertion.essentials])
        obtain ⟨u, eu, ⟨du⟩⟩ := ih (T.pf (T.wi (.var .ph) (.var .ps)))
          (by simp [Peano.ZF.axMp, TAssertion.essentials])
        have hr : r = p := encode_injective (by
          have he := congrArg TExpr.tree er
          simpa [TExpr.subst, ← hp] using he.symm)
        have hu : u = .imp p q := encode_injective (by
          have he := congrArg TExpr.tree eu
          simpa [TExpr.subst, encode, ← hp, ← hq] using he.symm)
        subst r u
        refine ⟨q, ?_, ⟨.mp du dr⟩⟩
        simp [Peano.ZF.axMp, TExpr.subst, ← hq]
      · obtain ⟨p, hp⟩ := parse .ph (by simp [Peano.ZF.ax1, TAssertion.ctx, Peano.ZF.fw])
        obtain ⟨q, hq⟩ := parse .ps (by simp [Peano.ZF.ax1, TAssertion.ctx, Peano.ZF.fw])
        refine ⟨.imp p (.imp q p), ?_, ⟨.k p q⟩⟩
        simp [Peano.ZF.ax1, TExpr.subst, encode, ← hp, ← hq]
      · obtain ⟨p, hp⟩ := parse .ph (by simp [Peano.ZF.ax2, TAssertion.ctx, Peano.ZF.fw])
        obtain ⟨q, hq⟩ := parse .ps (by simp [Peano.ZF.ax2, TAssertion.ctx, Peano.ZF.fw])
        obtain ⟨r, hr⟩ := parse .ch (by simp [Peano.ZF.ax2, TAssertion.ctx, Peano.ZF.fw])
        refine ⟨.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)), ?_, ⟨.s p q r⟩⟩
        simp [Peano.ZF.ax2, TExpr.subst, encode, ← hp, ← hq, ← hr]
      · obtain ⟨p, hp⟩ := parse .ph (by simp [Peano.ZF.ax3, TAssertion.ctx, Peano.ZF.fw])
        obtain ⟨q, hq⟩ := parse .ps (by simp [Peano.ZF.ax3, TAssertion.ctx, Peano.ZF.fw])
        refine ⟨.imp (.imp (.neg p) (.neg q)) (.imp q p), ?_, ⟨.c p q⟩⟩
        simp [Peano.ZF.ax3, TExpr.subst, encode, ← hp, ← hq]
    · exact ⟨p, he, ⟨.ax hp⟩⟩

/-- The unconditional reflector for the four-rule native propositional theory. -/
theorem nativeToHilbert {Γ : List (Named.Formula Native.V)}
    (hpure : ∀ v s, A.ctx v s → s = .setvar)
    (hΓ : ∀ e ∈ A.essentials, ∃ p ∈ Γ, e = T.pf (encode p))
    {e : TExpr Native.L Native.C Native.V}
    (d : TDerivation Native.grammar propAxioms A e) :
    ∃ p : Named.Formula Native.V, e = T.pf (encode p) ∧ Nonempty (Named.Hilbert ∅ Γ p) :=
  nativeToHilbertWithAxioms hpure hΓ (fun _ h _ _ _ => Or.inl h) d

/-- A finite native frame for an independent proof, with all intermediate names declared. -/
def proofFrame (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) : TAssertion Native.L Native.C Native.V where
  dv := []
  hyps := S.dedup.map Peano.ZF.fs ++ Γ.map (fun q => .ess (T.pf (encode q)))
  concl := T.pf (encode p)

@[simp] theorem proofFrame_ctx (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) (v : Native.V) (s : Native.C) :
    (proofFrame S Γ p).ctx v s ↔ v ∈ S ∧ s = .setvar := by
  simp [proofFrame, TAssertion.ctx, Peano.ZF.fs, eq_comm]

@[simp] theorem proofFrame_essentials (S : List Native.V) (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) :
    (proofFrame S Γ p).essentials = Γ.map (fun q => T.pf (encode q)) := by
  simp [proofFrame, TAssertion.essentials, List.filterMap_map]

/-- Bidirectional derivability for the precisely specified native propositional fragment.
The native proof is a real derivation in a finite pure frame. The theorem does
not identify proof fibers or assert equivalence of all predicate/ZF rules. -/
theorem propositional_correspondence (Γ : List (Named.Formula Native.V))
    (p : Named.Formula Native.V) : Nonempty (Named.Hilbert ∅ Γ p) ↔
    ∃ A : TAssertion Native.L Native.C Native.V,
      (∀ v s, A.ctx v s → s = .setvar) ∧
      (∀ e ∈ A.essentials, ∃ q ∈ Γ, e = T.pf (encode q)) ∧
      (∀ q ∈ Γ, T.pf (encode q) ∈ A.essentials) ∧
      Nonempty (TDerivation Native.grammar propAxioms A (T.pf (encode p))) := by
  constructor
  · rintro ⟨d⟩
    let S := d.vars ++ Γ.flatMap Named.Formula.vars
    let A := proofFrame S Γ p
    refine ⟨A, ?_, ?_, ?_, ?_⟩
    · intro v s hs
      exact ((proofFrame_ctx S Γ p v s).mp hs).2
    · intro e he
      rw [proofFrame_essentials] at he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      exact ⟨q, hq, rfl⟩
    · intro q hq
      rw [proofFrame_essentials]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    · refine ⟨hilbertToNative (A := A) (fun _ h => h) ?_ ?_ d ?_⟩
      · intro q hq
        rw [proofFrame_essentials]
        exact List.mem_map.mpr ⟨q, hq, rfl⟩
      · intro q hq
        exact hq.elim
      · intro v hv
        exact (proofFrame_ctx S Γ p v .setvar).mpr ⟨List.mem_append_left _ hv, rfl⟩
  · rintro ⟨A, hpure, hΓ, _, ⟨d⟩⟩
    obtain ⟨q, he, hd⟩ := nativeToHilbert hpure hΓ d
    have hq : q = p := encode_injective (congrArg TExpr.tree he).symm
    exact hq ▸ hd

end Silmaril.Logic.SetTheory.Inductive.MetamathZF
