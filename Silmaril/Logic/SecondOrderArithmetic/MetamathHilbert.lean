module

public import Silmaril.Logic.SecondOrderArithmetic.Hilbert
public import Silmaril.Logic.SecondOrderArithmetic.MetamathBase

@[expose] public section

/-! Bidirectional derivation correspondence for the classical Hilbert
fragment, in concrete name-only frames with no essential assumptions.
This theorem does not identify the full subsystem proof calculi. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open Silmaril.Logic.Metamath Grammar

/-- Only the three classical schemas and modus ponens. -/
def hilbertAxioms : Set (TAssertion SecondOrder.L SecondOrder.C SecondOrder.V) :=
  {SecondOrder.ax1, SecondOrder.ax2, SecondOrder.ax3, SecondOrder.axMp}

private theorem imp_sort {ctx : SecondOrder.V → SecondOrder.C → Prop}
    {a b : Tree SecondOrder.L SecondOrder.V}
    (ha : SecondOrder.grammar.HasSort ctx a .wff)
    (hb : SecondOrder.grammar.HasSort ctx b .wff) :
    SecondOrder.grammar.HasSort ctx (.node .wi [a, b]) .wff := by
  apply HasSort.node rfl
  simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule,
    List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl) <;> assumption

private theorem neg_sort {ctx : SecondOrder.V → SecondOrder.C → Prop}
    {a : Tree SecondOrder.L SecondOrder.V}
    (ha : SecondOrder.grammar.HasSort ctx a .wff) :
    SecondOrder.grammar.HasSort ctx (.node .wn [a]) .wff := by
  apply HasSort.node rfl
  simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule,
    List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
  rintro p rfl
  exact ha

/-- All leaf parameters must have their native formula sort in this frame. -/
def HilbertProof.Sorted (ctx : SecondOrder.V → SecondOrder.C → Prop)
    : {φ : Formula SecondOrder.V} → HilbertProof φ → Prop
  | _, .ax1 φ ψ | _, .ax3 φ ψ =>
      SecondOrder.grammar.HasSort ctx φ.toTree .wff ∧
      SecondOrder.grammar.HasSort ctx ψ.toTree .wff
  | _, .ax2 φ ψ χ =>
      SecondOrder.grammar.HasSort ctx φ.toTree .wff ∧
      SecondOrder.grammar.HasSort ctx ψ.toTree .wff ∧
      SecondOrder.grammar.HasSort ctx χ.toTree .wff
  | _, .mp p q => p.Sorted ctx ∧ q.Sorted ctx

theorem HilbertProof.hasSort {ctx : SecondOrder.V → SecondOrder.C → Prop}
    {φ : Formula SecondOrder.V} (p : HilbertProof φ) (h : p.Sorted ctx) :
    SecondOrder.grammar.HasSort ctx φ.toTree .wff := by
  induction p with
  | ax1 φ ψ => exact imp_sort h.1 (imp_sort h.2 h.1)
  | ax2 φ ψ χ =>
    exact imp_sort (imp_sort h.1 (imp_sort h.2.1 h.2.2))
      (imp_sort (imp_sort h.1 h.2.1) (imp_sort h.1 h.2.2))
  | ax3 φ ψ => exact imp_sort (imp_sort (neg_sort h.1) (neg_sort h.2)) (imp_sort h.2 h.1)
  | mp p q _ ih => exact SecondOrder.wi_1 (ih h.2)

/-- Typing of the concrete identity proof follows from typing of its parameter. -/
theorem HilbertProof.identity_sorted {ctx : SecondOrder.V → SecondOrder.C → Prop}
    {φ : Formula SecondOrder.V}
    (h : SecondOrder.grammar.HasSort ctx φ.toTree .wff) :
    (HilbertProof.identity φ).Sorted ctx :=
  ⟨⟨h, h⟩, ⟨⟨h, imp_sort h h⟩, ⟨h, imp_sort h h, h⟩⟩⟩

private theorem native_step {A B : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V}
    (hB : B ∈ hilbertAxioms) (τ : SecondOrder.V → Tree SecondOrder.L SecondOrder.V)
    (sorted : ∀ namev c, B.ctx namev c → SecondOrder.grammar.HasSort A.ctx (τ namev) c)
    (premises : ∀ e ∈ B.essentials, Nonempty (TDerivation SecondOrder.grammar hilbertAxioms A (e.subst τ)))
    (dv : B.DVSafe τ A.Disjoint) :
    Nonempty (TDerivation SecondOrder.grammar hilbertAxioms A (B.concl.subst τ)) :=
  ⟨.app B hB τ sorted (fun e he => Classical.choice (premises e he)) dv⟩

theorem HilbertProof.toNative {A : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V}
    {φ : Formula SecondOrder.V} (p : HilbertProof φ) (h : p.Sorted A.ctx) :
    Nonempty (TDerivation SecondOrder.grammar hilbertAxioms A ⟨.turnstile, φ.toTree⟩) := by
  induction p with
  | ax1 φ ψ =>
    let τ : SecondOrder.V → Tree SecondOrder.L SecondOrder.V := fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q
    have d := native_step (A := A) (B := SecondOrder.ax1)
      (by simp [hilbertAxioms]) τ (fun namev c hv => by
        simp only [TAssertion.ctx, SecondOrder.ax1, List.mem_cons, List.not_mem_nil,
          or_false, THyp.float.injEq] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h.1
        · exact h.2
      ) (fun e he => by simp [TAssertion.essentials, SecondOrder.ax1] at he)
      (fun namex namey hxy => by simp [SecondOrder.ax1] at hxy)
    simpa [τ, SecondOrder.ax1, TExpr.subst, Formula.toTree] using d
  | ax2 φ ψ χ =>
    let τ : SecondOrder.V → Tree SecondOrder.L SecondOrder.V := fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | .ch => χ.toTree
      | q => .var q
    have d := native_step (A := A) (B := SecondOrder.ax2)
      (by simp [hilbertAxioms]) τ (fun namev c hv => by
        simp only [TAssertion.ctx, SecondOrder.ax2, List.mem_cons, List.not_mem_nil,
          or_false, THyp.float.injEq] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h.1
        · exact h.2.1
        · exact h.2.2
      ) (fun e he => by simp [TAssertion.essentials, SecondOrder.ax2] at he)
      (fun namex namey hxy => by simp [SecondOrder.ax2] at hxy)
    simpa [τ, SecondOrder.ax2, TExpr.subst, Formula.toTree] using d
  | ax3 φ ψ =>
    let τ : SecondOrder.V → Tree SecondOrder.L SecondOrder.V := fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q
    have d := native_step (A := A) (B := SecondOrder.ax3)
      (by simp [hilbertAxioms]) τ (fun namev c hv => by
        simp only [TAssertion.ctx, SecondOrder.ax3, List.mem_cons, List.not_mem_nil,
          or_false, THyp.float.injEq] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h.1
        · exact h.2
      ) (fun e he => by simp [TAssertion.essentials, SecondOrder.ax3] at he)
      (fun namex namey hxy => by simp [SecondOrder.ax3] at hxy)
    simpa [τ, SecondOrder.ax3, TExpr.subst, Formula.toTree] using d
  | @mp φ ψ p q ih ih' =>
    let τ : SecondOrder.V → Tree SecondOrder.L SecondOrder.V := fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | namev => .var namev
    have d := native_step (A := A) (B := SecondOrder.axMp)
      (by simp [hilbertAxioms]) τ (fun namev c hv => by
        simp [TAssertion.ctx, SecondOrder.axMp] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact p.hasSort h.1
        · exact SecondOrder.wi_1 (q.hasSort h.2)
      ) (fun e he => by
        simp only [TAssertion.essentials, SecondOrder.axMp, List.filterMap_cons,
          List.filterMap_nil, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simpa [τ, TExpr.subst] using ih h.1
        · simpa [τ, TExpr.subst, Formula.toTree] using ih' h.2
      ) (fun namex namey hxy => by simp [SecondOrder.axMp] at hxy)
    simpa [τ, SecondOrder.axMp, TExpr.subst] using d



/-- Reconstruct an independent proof tree from every native derivation in
this fragment. Formula metavariables and essential hypotheses are excluded
explicitly; name variables of both sorts remain available. -/
theorem hilbert_fromNative {A : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V}
    (hc : NameContext A.ctx) (he : A.essentials = [])
    {e : TExpr SecondOrder.L SecondOrder.C SecondOrder.V}
    (d : TDerivation SecondOrder.grammar hilbertAxioms A e) :
    ∃ φ : Formula SecondOrder.V, φ.toTree = e.tree ∧
      ∃ p : HilbertProof φ, p.Sorted A.ctx := by
  induction d with
  | hyp h => simp [he] at h
  | app B hB τ sorted _ _ ih =>
    simp only [hilbertAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hB
    rcases hB with rfl | rfl | rfl | rfl
    · have hφ := sorted .ph .wff (by simp [TAssertion.ctx, SecondOrder.ax1])
      obtain ⟨φ, eqφ⟩ := Formula.toTree_surjective hc hφ
      have sφ : SecondOrder.grammar.HasSort A.ctx φ.toTree .wff := eqφ.symm ▸ hφ
      have hψ := sorted .ps .wff (by simp [TAssertion.ctx, SecondOrder.ax1])
      obtain ⟨ψ, eqψ⟩ := Formula.toTree_surjective hc hψ
      have sψ : SecondOrder.grammar.HasSort A.ctx ψ.toTree .wff := eqψ.symm ▸ hψ
      refine ⟨.imp φ (.imp ψ φ), ?_, .ax1 φ ψ, ⟨sφ, sψ⟩⟩
      simp [Formula.toTree, SecondOrder.ax1, TExpr.subst, eqφ, eqψ]
    · have hφ := sorted .ph .wff (by simp [TAssertion.ctx, SecondOrder.ax2])
      obtain ⟨φ, eqφ⟩ := Formula.toTree_surjective hc hφ
      have sφ : SecondOrder.grammar.HasSort A.ctx φ.toTree .wff := eqφ.symm ▸ hφ
      have hψ := sorted .ps .wff (by simp [TAssertion.ctx, SecondOrder.ax2])
      obtain ⟨ψ, eqψ⟩ := Formula.toTree_surjective hc hψ
      have sψ : SecondOrder.grammar.HasSort A.ctx ψ.toTree .wff := eqψ.symm ▸ hψ
      have hχ := sorted .ch .wff (by simp [TAssertion.ctx, SecondOrder.ax2])
      obtain ⟨χ, eqχ⟩ := Formula.toTree_surjective hc hχ
      have sχ : SecondOrder.grammar.HasSort A.ctx χ.toTree .wff := eqχ.symm ▸ hχ
      refine ⟨.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)), ?_, .ax2 φ ψ χ, ⟨sφ, sψ, sχ⟩⟩
      simp [Formula.toTree, SecondOrder.ax2, TExpr.subst, eqφ, eqψ, eqχ]
    · have hφ := sorted .ph .wff (by simp [TAssertion.ctx, SecondOrder.ax3])
      obtain ⟨φ, eqφ⟩ := Formula.toTree_surjective hc hφ
      have sφ : SecondOrder.grammar.HasSort A.ctx φ.toTree .wff := eqφ.symm ▸ hφ
      have hψ := sorted .ps .wff (by simp [TAssertion.ctx, SecondOrder.ax3])
      obtain ⟨ψ, eqψ⟩ := Formula.toTree_surjective hc hψ
      have sψ : SecondOrder.grammar.HasSort A.ctx ψ.toTree .wff := eqψ.symm ▸ hψ
      refine ⟨.imp (.imp (.neg φ) (.neg ψ)) (.imp ψ φ), ?_, .ax3 φ ψ, ⟨sφ, sψ⟩⟩
      simp [Formula.toTree, SecondOrder.ax3, TExpr.subst, eqφ, eqψ]
    · have hφ := sorted .ph .wff (by simp [TAssertion.ctx, SecondOrder.axMp])
      obtain ⟨φ, eqφ⟩ := Formula.toTree_surjective hc hφ
      have sφ : SecondOrder.grammar.HasSort A.ctx φ.toTree .wff := eqφ.symm ▸ hφ
      have hψ := sorted .ps .wff (by simp [TAssertion.ctx, SecondOrder.axMp])
      obtain ⟨ψ, eqψ⟩ := Formula.toTree_surjective hc hψ
      have sψ : SecondOrder.grammar.HasSort A.ctx ψ.toTree .wff := eqψ.symm ▸ hψ
      obtain ⟨a, eqa, p, sp⟩ := ih ⟨.turnstile, .var .ph⟩ (by decide)
      obtain ⟨b, eqb, q, sq⟩ := ih ⟨.turnstile, .node .wi [.var .ph, .var .ps]⟩ (by decide)
      have ea : a = φ := Formula.toTree_injective (eqa.trans eqφ.symm)
      have eb : b = .imp φ ψ := Formula.toTree_injective (by
        simpa [TExpr.subst, Formula.toTree, eqφ, eqψ] using eqb)
      subst ea eb
      refine ⟨ψ, ?_, .mp p q, ⟨sp, sq⟩⟩
      simpa [SecondOrder.axMp, TExpr.subst] using eqψ

/-- Actual bidirectional derivability for the named classical fragment.
The left side retains a finite independent proof and its frame typing. -/
theorem hilbert_derivation_iff {A : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V}
    (hc : NameContext A.ctx) (he : A.essentials = []) (φ : Formula SecondOrder.V) :
    (∃ p : HilbertProof φ, p.Sorted A.ctx) ↔
      Nonempty (TDerivation SecondOrder.grammar hilbertAxioms A ⟨.turnstile, φ.toTree⟩) := by
  constructor
  · rintro ⟨p, hp⟩
    exact p.toNative hp
  · rintro ⟨d⟩
    obtain ⟨ψ, eqψ, p, hp⟩ := hilbert_fromNative hc he d
    have eψ : ψ = φ := Formula.toTree_injective eqψ
    subst eψ
    exact ⟨p, hp⟩

end Silmaril.Logic.SecondOrderArithmetic
