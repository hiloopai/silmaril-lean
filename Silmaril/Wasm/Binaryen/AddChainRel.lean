module

public import Silmaril.Wasm.Binaryen.AddChainSim

@[expose] public section

namespace Silmaril.Wasm.Binaryen.AddChain

open Execution.Core Execution.Core.Sim Validation Numerics

mutual
theorem foldE_rel : ∀ x : BExpr, InstrsRel acBI x.lower (foldE x).lower
  | x => by
    unfold foldE
    split
    · rename_i _ y a b
      simpa [BExpr.lower, List.append_assoc] using
        (foldE_rel y).append (InstrsRel.base (.add .i32 a b))
    · rename_i _ y a b
      simpa [BExpr.lower, List.append_assoc] using
        (foldE_rel y).append (InstrsRel.base (.add .i64 a b))
    · rename_i _ i args _ _
      simpa [BExpr.lower] using (foldL_rel args).append (InstrsRel.refl [i])
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

theorem foldL_rel : ∀ es : List BExpr,
    InstrsRel acBI (BExpr.lowerList es) (BExpr.lowerList (foldL es))
  | es => by
    unfold foldL
    split
    · rename_i _ a b ys
      simpa [BExpr.lower, List.append_assoc] using
        (InstrsRel.base (acBI.add .i32 a b)).append (foldL_rel ys)
    · rename_i _ a b ys
      simpa [BExpr.lower, List.append_assoc] using
        (InstrsRel.base (acBI.add .i64 a b)).append (foldL_rel ys)
    · exact .nil
    · rename_i _ e ys _ _
      simpa using (foldE_rel e).append (foldL_rel ys)
termination_by es => sizeOf es
decreasing_by all_goals (try subst_vars); all_goals simp_wf; all_goals omega
end

/-- Every original function body is related to its rewritten body. -/
theorem addChain_bodiesRel (m : BModule) :
    ModuleBodiesRel acBI m.lower (addChain m).lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, addChain, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, foldL_rel f.body⟩ ih

/-- Constant-addition chain folding preserves exports of valid modules. -/
theorem addChain_sound {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool}
    {m : BModule} (hm : m.Ok) (hm' : (addChain m).Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
      (addChain m).lower m.lower := by
  exact CodeSimClosed.exportEquiv_of_baseSim acBaseSim ac_noRedex
    (addChain_bodiesRel m).flip hm' hm

end Silmaril.Wasm.Binaryen.AddChain
