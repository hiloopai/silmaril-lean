module

public import Silmaril.Wasm.Binaryen.ConstSelectSim

@[expose] public section

namespace Silmaril.Wasm.Binaryen.ConstSelect

open Execution.Core Execution.Core.Sim Validation Numerics

mutual
theorem foldE_rel : ∀ x : BExpr, InstrsRel csBI x.lower (foldE x).lower
  | x => by
    unfold foldE
    split
    · rename_i _ ts a b c
      split
      · next hc =>
        simpa [BExpr.lower, List.append_assoc] using
          ((foldE_rel a).append (foldE_rel b)).append
            (InstrsRel.base (.selectTrue ts c hc))
      · next hc =>
        have hc0 : c = 0 := by simpa using hc
        subst c
        split
        · next _ v =>
          simpa [BExpr.lower, List.append_assoc] using
            (foldE_rel a).append (InstrsRel.base (.selectFalse ts v))
        · simpa [BExpr.lower, List.append_assoc] using
            ((foldE_rel a).append (foldE_rel b)).append
              (InstrsRel.refl [.intConst .i32 0, .select ts])
    · rename_i _ ls d c
      simp only [BExpr.lower, BExpr.lowerList_cons, BExpr.lowerList_nil,
        List.nil_append, List.append_nil, List.singleton_append]
      exact InstrsRel.base (csBI.table ls d c)
    · rename_i _ i args _ _
      simpa [BExpr.lower] using (foldA_rel args).append (InstrsRel.refl [i])
    · rename_i _ bt b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.block bt (foldL_rel b)) .nil
    · rename_i _ bt b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.loop bt (foldL_rel b)) .nil
    · rename_i _ bt c t e
      simpa [BExpr.lower] using (foldL_rel c).append
        (InstrsRel.cons (InstrRel.if_ bt (foldL_rel t) (foldL_rel e)) .nil)
    · rename_i _ bt cs b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.tryTable bt cs (foldL_rel b)) .nil
termination_by x => sizeOf x
decreasing_by all_goals (try subst_vars); all_goals simp_wf; all_goals omega

theorem foldA_rel : ∀ es : List BExpr,
    InstrsRel csBI (BExpr.lowerList es) (BExpr.lowerList (foldA es))
  | [] => by simpa [foldA] using (InstrsRel.nil (BI := csBI))
  | e :: es => by simpa [foldA] using (foldE_rel e).append (foldA_rel es)
termination_by es => sizeOf es
decreasing_by all_goals simp_wf <;> omega

theorem foldL_rel : ∀ es : List BExpr,
    InstrsRel csBI (BExpr.lowerList es) (BExpr.lowerList (foldL es))
  | [] => by simpa [foldL] using (InstrsRel.nil (BI := csBI))
  | [e] => by simpa [foldL] using foldE_rel e
  | x :: y :: es => by
    unfold foldL
    split
    · rename_i _ k ts hx
      obtain rfl := ConstBranch.constLeaf?_some hx
      split
      · next hk =>
        simpa [BExpr.lower] using
          (InstrsRel.base (csBI.selectTrue ts k hk)).append (foldL_rel es)
      · simpa [foldE, foldA, BExpr.lower] using (InstrsRel.refl [.intConst .i32 k]).append
          (foldL_rel (.op (.select ts) [] :: es))
    · rename_i _ k ls d hx
      obtain rfl := ConstBranch.constLeaf?_some hx
      simpa [BExpr.lower] using
        (InstrsRel.base (csBI.table ls d k)).append (foldL_rel es)
    · rename_i y _ _ _
      simpa using (foldE_rel x).append (foldL_rel (y :: es))

termination_by es => sizeOf es
decreasing_by all_goals (try subst_vars); all_goals simp_wf; all_goals omega
end

/-- Function bodies before and after the fold are related. -/
theorem constSelect_bodiesRel (m : BModule) :
    ModuleBodiesRel csBI m.lower (constSelect m).lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, constSelect, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, foldL_rel f.body⟩ ih

/-- Constant select/table folding preserves exports of valid modules. -/
theorem constSelect_sound {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool}
    {m : BModule} (hm : m.Ok) (hm' : (constSelect m).Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
      (constSelect m).lower m.lower := by
  have h := CodeSimClosed.exportEquiv_of_baseSim (H := H) (o := o) csBaseSim cs_noRedex
    (constSelect_bodiesRel m) hm hm'
  exact ⟨h.2.mono fun _ _ e => e.symm, h.1.mono fun _ _ e => e.symm⟩

end Silmaril.Wasm.Binaryen.ConstSelect
