module

public import Silmaril.Logic.SecondOrderArithmetic.MetamathHilbert

@[expose] public section

/-! Exact syntax correspondence for subsystem schemas, and certified native
proof transport for the already completed Hilbert fragment. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open Silmaril.Logic.Metamath Grammar

theorem axInd_toTree (nx : SecondOrder.V) (ny : SecondOrder.V) (φ : Formula SecondOrder.V) :
    (Formula.induction nx ny φ).toTree =
      SecondOrder.axInd.concl.tree.subst (fun
      | .x => .var nx
      | .y => .var ny
      | .ph => φ.toTree
      | q => .var q) := by
  simp [Formula.induction, Formula.toTree, Term.toTree, SecondOrder.axInd]

theorem axIndSig1_toTree (nx : SecondOrder.V) (ny : SecondOrder.V) (φ : Formula SecondOrder.V) :
    (Formula.induction nx ny φ).toTree =
      SecondOrder.axIndSig1.concl.tree.subst (fun
      | .x => .var nx
      | .y => .var ny
      | .ph => φ.toTree
      | q => .var q) := by
  simp [Formula.induction, Formula.toTree, Term.toTree, SecondOrder.axIndSig1]

theorem axComp_toTree (nx : SecondOrder.V) (sX : SecondOrder.V) (φ : Formula SecondOrder.V) :
    (Formula.comprehension nx sX φ).toTree =
      SecondOrder.axComp.concl.tree.subst (fun
      | .x => .var nx
      | .X => .var sX
      | .ph => φ.toTree
      | q => .var q) := by
  simp [Formula.comprehension, Formula.toTree, Term.toTree, SecondOrder.axComp]

theorem axAcomp_toTree (nx : SecondOrder.V) (sX : SecondOrder.V) (φ : Formula SecondOrder.V) :
    (Formula.comprehension nx sX φ).toTree =
      SecondOrder.axAcomp.concl.tree.subst (fun
      | .x => .var nx
      | .X => .var sX
      | .ph => φ.toTree
      | q => .var q) := by
  simp [Formula.comprehension, Formula.toTree, Term.toTree, SecondOrder.axAcomp]

theorem axDcomp_toTree (nx : SecondOrder.V) (sX : SecondOrder.V) (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) :
    (Formula.deltaComprehension nx sX φ ψ).toTree =
      SecondOrder.axDcomp.concl.tree.subst (fun
      | .x => .var nx
      | .X => .var sX
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q) := by
  simp [Formula.deltaComprehension, Formula.toTree, Term.toTree, SecondOrder.axDcomp, Formula.comprehension]

theorem axSep1_toTree (nx : SecondOrder.V) (sX : SecondOrder.V) (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) :
    (Formula.separation nx sX φ ψ).toTree =
      SecondOrder.axSep1.concl.tree.subst (fun
      | .x => .var nx
      | .X => .var sX
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q) := by
  simp [Formula.separation, Formula.toTree, Term.toTree, SecondOrder.axSep1]

theorem hilbert_subset_native_base : hilbertAxioms ⊆ SecondOrder.base := by
  intro B hB
  simp only [hilbertAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hB
  rcases hB with rfl | rfl | rfl | rfl <;>
    simp [SecondOrder.base, SecondOrder.logicList]

/-- Transport into native `RCA0` for the completed classical fragment. -/
theorem HilbertProof.toNativeRCA0 {A : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V}
    {φ : Formula SecondOrder.V} (p : HilbertProof φ) (h : p.Sorted A.ctx) :
    Nonempty (TDerivation SecondOrder.grammar SecondOrder.RCA0 A ⟨.turnstile, φ.toTree⟩) := by
  obtain ⟨d⟩ := p.toNative h
  refine ⟨d.mono (hilbert_subset_native_base.trans ?_)⟩
  exact Set.subset_union_left

/-- Transport into native `WKL0` for the completed classical fragment. -/
theorem HilbertProof.toNativeWKL0 {A : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V}
    {φ : Formula SecondOrder.V} (p : HilbertProof φ) (h : p.Sorted A.ctx) :
    Nonempty (TDerivation SecondOrder.grammar SecondOrder.WKL0 A ⟨.turnstile, φ.toTree⟩) := by
  obtain ⟨d⟩ := p.toNative h
  refine ⟨d.mono (hilbert_subset_native_base.trans ?_)⟩
  exact Set.subset_union_left.trans Set.subset_union_left

/-- Transport into native `ACA0` for the completed classical fragment. -/
theorem HilbertProof.toNativeACA0 {A : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V}
    {φ : Formula SecondOrder.V} (p : HilbertProof φ) (h : p.Sorted A.ctx) :
    Nonempty (TDerivation SecondOrder.grammar SecondOrder.ACA0 A ⟨.turnstile, φ.toTree⟩) := by
  obtain ⟨d⟩ := p.toNative h
  refine ⟨d.mono (hilbert_subset_native_base.trans ?_)⟩
  exact Set.subset_union_left

/-- Transport into native `Z2` for the completed classical fragment. -/
theorem HilbertProof.toNativeZ2 {A : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V}
    {φ : Formula SecondOrder.V} (p : HilbertProof φ) (h : p.Sorted A.ctx) :
    Nonempty (TDerivation SecondOrder.grammar SecondOrder.Z2 A ⟨.turnstile, φ.toTree⟩) := by
  obtain ⟨d⟩ := p.toNative h
  refine ⟨d.mono (hilbert_subset_native_base.trans ?_)⟩
  exact Set.subset_union_left.trans Set.subset_union_left

end Silmaril.Logic.SecondOrderArithmetic
