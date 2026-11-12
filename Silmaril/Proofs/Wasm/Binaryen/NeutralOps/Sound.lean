module

public import Silmaril.Proofs.Wasm.Binaryen.NeutralOps.Sim

@[expose] public section

/-! # Neutral-operand elimination: every body is related to its rewrite

`elimL_rel` relates the lowering of every sequence to the lowering of its rewrite
by the base pairs `nBI`; with the two simulations of `Sim.lean` this gives exact
export equivalence at every numerical profile under the closed host.
-/

namespace Silmaril.Proofs.Wasm.Binaryen.NeutralOps

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.NeutralOps

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- A base pair from an accepted `fits` test. -/
theorem fits_base {X : Instr} {t : IntType} {op : IntBinOp} {t' : IntType}
    {k : BitVec t'.width} (h : fits X t op t' k = true) :
    InstrsRel nBI [.intConst t' k, .intBinOp t op, X] [X] := by
  obtain ⟨e, hX, hn⟩ := fits_spec h
  subst e
  exact .base (.mk t' op k X hn hX)

mutual
theorem elimE_rel : ∀ x : BExpr, InstrsRel nBI x.lower (elimE x).lower
  | x => by
    unfold elimE
    split
    · rename_i X t op y t' k
      split
      · next h =>
        simpa [BExpr.lower, List.append_assoc] using (elimE_rel y).append (fits_base h)
      · simpa [BExpr.lower, List.append_assoc] using
          (elimE_rel y).append (InstrsRel.refl [.intConst t' k, .intBinOp t op, X])
    · rename_i X a t op y t' k
      split
      · next h =>
        simpa [BExpr.lower, List.append_assoc] using
          (elimE_rel a).append ((elimE_rel y).append (fits_base h))
      · simpa [BExpr.lower, List.append_assoc] using
          (elimE_rel a).append ((elimE_rel y).append
            (InstrsRel.refl [.intConst t' k, .intBinOp t op, X]))
    · rename_i i args _ _
      simpa [BExpr.lower] using (elimL_rel args).append (InstrsRel.refl [i])
    · rename_i bt b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.block bt (elimL_rel b)) .nil
    · rename_i bt b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.loop bt (elimL_rel b)) .nil
    · rename_i bt c t e
      simpa [BExpr.lower] using (elimL_rel c).append
        (InstrsRel.cons (InstrRel.if_ bt (elimL_rel t) (elimL_rel e)) .nil)
    · rename_i bt cs b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.tryTable bt cs (elimL_rel b)) .nil
termination_by x => sizeOf x

theorem elimL_rel : ∀ es : List BExpr,
    InstrsRel nBI (BExpr.lowerList es) (BExpr.lowerList (elimL es))
  | es => by
    unfold elimL
    split
    · rename_i t k t' op X ys
      split
      · next h =>
        simpa [BExpr.lower, List.append_assoc] using (fits_base h).append (elimL_rel ys)
      · simpa [BExpr.lower, List.append_assoc] using
          (InstrsRel.refl (BI := nBI) [.intConst t k]).append
            (elimL_rel (.op (.intBinOp t' op) [] :: .op X [] :: ys))
    · rename_i t op y t' k X ys
      split
      · next h =>
        simpa [BExpr.lower, List.append_assoc] using
          (elimE_rel y).append ((fits_base h).append (elimL_rel ys))
      · simpa [BExpr.lower, List.append_assoc] using
          (elimE_rel y).append ((InstrsRel.refl [.intConst t' k, .intBinOp t op]).append
            (elimL_rel (.op X [] :: ys)))
    · exact .nil
    · rename_i e ys _ _
      simpa using (elimE_rel e).append (elimL_rel ys)
termination_by es => sizeOf es
end

/-- Every original function body is related to its rewritten body. -/
theorem neutralOps_bodiesRel (m : BModule) :
    ModuleBodiesRel nBI m.lower (neutralOps m).lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, neutralOps, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, elimL_rel f.body⟩ ih

/-- The raw rewrite is exactly export-equivalent at every numerical profile, for
valid input and output. -/
theorem neutralOps_sound_any {m : BModule} (hm : m.Ok) (hm' : (neutralOps m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (neutralOps m).lower m.lower :=
  ⟨exportRefines_of_bodiesRel resultBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (neutralOps_bodiesRel m).flip hm' hm,
    (exportRefines_of_bodiesRel sourceBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (neutralOps_bodiesRel m) hm hm').mono fun _ _ h => h.symm⟩

/-- The checked stage keeps validity and is exactly export-equivalent at every
numerical profile; its validator fallback is the identity. -/
theorem neutralOpsChecked_sound_any {m : BModule} (hm : m.Ok) :
    (neutralOpsChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (neutralOpsChecked m).lower m.lower := by
  unfold neutralOpsChecked
  dsimp only
  split
  · next h => exact ⟨Exe.validOk_sound h, neutralOps_sound_any hm (Exe.validOk_sound h)⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Proofs.Wasm.Binaryen.NeutralOps
