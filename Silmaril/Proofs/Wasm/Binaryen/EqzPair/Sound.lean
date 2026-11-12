module

public import Silmaril.Proofs.Wasm.Binaryen.EqzPair.Sim

@[expose] public section

/-! # Double `i32.eqz` elimination: every body is related to its rewrite -/

namespace Silmaril.Proofs.Wasm.Binaryen.EqzPair

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.EqzPair

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

theorem consumer_base {X : Instr} (h : boolConsumer X = true) :
    InstrsRel eBI [eqz, eqz, X] [X] := .base (.mk X h)

mutual
theorem elimE_rel : ∀ x : BExpr, InstrsRel eBI x.lower (elimE x).lower
  | .op i args => by
    rw [elimE]
    split
    · next h => simpa [BExpr.lower] using elimArgs_rel h args
    · simpa [BExpr.lower] using (elimL_rel args).append (InstrsRel.refl [i])
  | .block bt b => by
    simpa [elimE, BExpr.lower] using InstrsRel.cons (InstrRel.block bt (elimL_rel b)) .nil
  | .loop bt b => by
    simpa [elimE, BExpr.lower] using InstrsRel.cons (InstrRel.loop bt (elimL_rel b)) .nil
  | .if_ bt c t e => by
    simpa [elimE, BExpr.lower] using (elimL_rel c).append
      (InstrsRel.cons (InstrRel.if_ bt (elimL_rel t) (elimL_rel e)) .nil)
  | .tryTable bt cs b => by
    simpa [elimE, BExpr.lower] using InstrsRel.cons (InstrRel.tryTable bt cs (elimL_rel b)) .nil
termination_by x => sizeOf x

theorem elimArgs_rel {X : Instr} (hX : boolConsumer X = true) : ∀ args : List BExpr,
    InstrsRel eBI (BExpr.lowerList args ++ [X]) (BExpr.lowerList (elimArgs args) ++ [X])
  | args => by
    unfold elimArgs
    split
    · exact InstrsRel.refl _
    · rename_i c
      simpa [BExpr.lower, List.append_assoc] using (elimE_rel c).append (consumer_base hX)
    · rename_i e es _
      simpa [List.append_assoc] using (elimE_rel e).append (elimArgs_rel hX es)
termination_by args => sizeOf args

theorem elimL_rel : ∀ es : List BExpr,
    InstrsRel eBI (BExpr.lowerList es) (BExpr.lowerList (elimL es))
  | es => by
    unfold elimL
    split
    · rename_i X ys
      split
      · next h => simpa [BExpr.lower, List.append_assoc] using (consumer_base h).append (elimL_rel ys)
      · simpa [BExpr.lower, List.append_assoc] using
          (InstrsRel.refl (BI := eBI) [eqz]).append (elimL_rel (.op eqz [] :: .op X [] :: ys))
    · rename_i c X ys
      split
      · next h =>
        simpa [BExpr.lower, List.append_assoc] using
          (elimE_rel c).append ((consumer_base h).append (elimL_rel ys))
      · simpa [BExpr.lower, List.append_assoc] using
          (elimE_rel c).append ((InstrsRel.refl [eqz, eqz]).append (elimL_rel (.op X [] :: ys)))
    · exact .nil
    · rename_i e ys _ _
      simpa using (elimE_rel e).append (elimL_rel ys)
termination_by es => sizeOf es
end

theorem eqzPair_bodiesRel (m : BModule) : ModuleBodiesRel eBI m.lower (eqzPair m).lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, eqzPair, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, elimL_rel f.body⟩ ih

/-- The raw rewrite is exactly export-equivalent at every numerical profile, for
valid input and output. -/
theorem eqzPair_sound_any {m : BModule} (hm : m.Ok) (hm' : (eqzPair m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (eqzPair m).lower m.lower :=
  ⟨exportRefines_of_bodiesRel resultBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (eqzPair_bodiesRel m).flip hm' hm,
    (exportRefines_of_bodiesRel sourceBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (eqzPair_bodiesRel m) hm hm').mono fun _ _ h => h.symm⟩

/-- The checked stage keeps validity and is exactly export-equivalent at every
numerical profile. -/
theorem eqzPairChecked_sound_any {m : BModule} (hm : m.Ok) :
    (eqzPairChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (eqzPairChecked m).lower m.lower := by
  unfold eqzPairChecked
  dsimp only
  split
  · next h => exact ⟨Exe.validOk_sound h, eqzPair_sound_any hm (Exe.validOk_sound h)⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Proofs.Wasm.Binaryen.EqzPair
