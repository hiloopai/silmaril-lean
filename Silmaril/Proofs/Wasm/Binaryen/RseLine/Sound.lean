module

public import Silmaril.Wasm.Binaryen.RseLine.Defs
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim

@[expose] public section

/-! # Self-store elimination: the body relation

`foldL_rel` relates every rewritten body to its original by silmaril's base pairs
`RedundantSetLine.rsBI`. With silmaril's `rsBaseSim` (the result simulates the
original, at every numerical profile) and the deferred reverse simulation of
`Reverse.lean`, this gives exact export equivalence at every numerical profile.
-/
namespace Silmaril.Proofs.Wasm.Binaryen.RseLine

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.RseLine

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen.RedundantSetLine

variable {H : Type}

mutual
theorem foldE_rel : ∀ x : BExpr, InstrsRel rsBI (foldE x).lower x.lower
  | e₀ => by
    unfold foldE
    split
    · rename_i x y
      split
      · next h =>
        have e := beq_iff_eq.mp h
        subst e
        exact by simpa [BExpr.lower] using (InstrsRel.base (rsBI.set x) : InstrsRel rsBI _ _)
      · simpa [BExpr.lower] using InstrsRel.refl (BI := rsBI) [Instr.localGet y, .localSet x]
    · rename_i x y
      split
      · next h =>
        have e := beq_iff_eq.mp h
        subst e
        exact by simpa [BExpr.lower] using (InstrsRel.base (rsBI.tee x) : InstrsRel rsBI _ _)
      · simpa [BExpr.lower] using InstrsRel.refl (BI := rsBI) [Instr.localGet y, .localTee x]
    · rename_i i es _ _
      simpa [BExpr.lower] using (foldL_rel es).append (InstrsRel.refl [i])
    · rename_i bt b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.block bt (foldL_rel b)) .nil
    · rename_i bt b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.loop bt (foldL_rel b)) .nil
    · rename_i bt c t e
      simpa [BExpr.lower] using (foldL_rel c).append
        (InstrsRel.cons (InstrRel.if_ bt (foldL_rel t) (foldL_rel e)) .nil)
    · rename_i bt cs b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.tryTable bt cs (foldL_rel b)) .nil
termination_by x => sizeOf x

theorem foldL_rel : ∀ es : List BExpr,
    InstrsRel rsBI (BExpr.lowerList (foldL es)) (BExpr.lowerList es)
  | es => by
    unfold foldL
    split
    · exact .nil
    · rename_i x y ys
      split
      · next h =>
        have e := beq_iff_eq.mp h
        subst e
        simpa [BExpr.lower, List.append_assoc] using
          (InstrsRel.base (rsBI.set x) : InstrsRel rsBI _ _).append (foldL_rel ys)
      · simpa [BExpr.lower, List.append_assoc] using
          (InstrsRel.refl (BI := rsBI) [Instr.localGet x]).append
            (foldL_rel (.op (.localSet y) [] :: ys))
    · rename_i x y ys
      split
      · next h =>
        have e := beq_iff_eq.mp h
        subst e
        simpa [BExpr.lower, List.append_assoc] using
          (InstrsRel.base (rsBI.tee x) : InstrsRel rsBI _ _).append (foldL_rel ys)
      · simpa [BExpr.lower, List.append_assoc] using
          (InstrsRel.refl (BI := rsBI) [Instr.localGet x]).append
            (foldL_rel (.op (.localTee y) [] :: ys))
    · rename_i e ys _ _
      simpa using (foldE_rel e).append (foldL_rel ys)
termination_by es => sizeOf es
end

theorem rseLine_bodiesRel (m : BModule) :
    ModuleBodiesRel rsBI (rseLine m).lower m.lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, rseLine, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, foldL_rel f.body⟩ ih

end Silmaril.Proofs.Wasm.Binaryen.RseLine
