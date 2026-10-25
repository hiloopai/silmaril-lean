module

public import Silmaril.Logic.SetTheory.Inductive.MetamathSchemas

@[expose] public section

/-! # Executable and proof-object regression checks for the independent ZF presentation -/

namespace Silmaril.Logic.SetTheory.Inductive.Tests

open Silmaril.Logic.Metamath Grammar MetamathZF

/-- Instantiation under a binder preserves the bound index and shifts the substituted variable. -/
example : ((.all (.mem 0 1) : Formula 2).instantiate 0) = (.all (.mem 0 1) : Formula 1) := rfl

/-- Bound names need no free-name assignment, even in a closed sentence. -/
example : (ZF.Axioms.nul (0 : Fin 2) 1).scope (fun _ => none) = some ZF.emptySet := by decide

/-- A missing free name is rejected rather than converted into a bound variable. -/
example : (Named.Formula.mem (0 : Fin 1) 0).scope (fun _ => (none : Option (Fin 0))) = none := rfl

/-- Native class metavariables are outside the pure finite membership fragment. -/
example : decode (.node .wcel [.var .A, .var .B]) = none := rfl

/-- Separation's native DV condition rejects occurrences of an output name even under a binder. -/
theorem separation_rejects_bound_output {A : TAssertion Native.L Native.C Native.V} :
    ¬ Peano.ZF.axSep.DVSafe
      (schemaSubst .x .y .z .w (.all .y (.eq .x .x))) A.Disjoint := by
  intro hdv
  exact (hdv .y .ph (by decide) .y (by simp [schemaSubst]) .y
    (by simp [schemaSubst, Named.Formula.vars])).1 rfl

/-- A concrete multi-rule native proof is produced, rather than just a model-truth proposition. -/
noncomputable def nativeExtensionality :=
  nativeExtensionalityApplication .x .y .z (by decide)

/-- That native proof reflects back to the independent ZF inference system. -/
example : Nonempty (Named.Hilbert (V := Native.V) ZF.Schema
    [.all .z (.iff (.mem .z .x) (.mem .z .y))] (.eq .x .y)) := by
  let d := extensionalityApplication (.x : Native.V) .y .z (by decide)
  obtain ⟨q, he, hq⟩ := nativeToZF
    (fun aVar s hs => (zfFrame_ctx _ _ _ aVar s).mp hs |>.2)
    (by
      intro e he
      rw [zfFrame_essentials] at he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      exact ⟨q, hq, rfl⟩)
    (zfToNative d)
  have heq := encode_injective (congrArg TExpr.tree he).symm
  exact heq ▸ hq


/-- The independent closed empty-set proof is sound in the standard set universe. -/
example : ZF.emptySet.holds (M := _root_.ZFSet) :=
  ZF.zfSet_sound ZF.emptySetProof Fin.elim0 (by simp)

end Silmaril.Logic.SetTheory.Inductive.Tests
