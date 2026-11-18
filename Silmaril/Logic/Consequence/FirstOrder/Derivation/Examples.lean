module

public import Silmaril.Logic.Consequence.FirstOrder.Derivation.SExp.Thms
public meta import Silmaril.Logic.Consequence.FirstOrder.Derivation.SExp.Thms

/-!
# Concrete first-order proofs over `orderSig`, checked by the kernel

Each proof is a raw proof tree over the named signature `orderSig` (`zero`, `succ`, `<`); each
`…_checks` theorem says the whole pipeline (decode, elaborate, check) accepts its S-expression with
the stated conclusion, and `…_derives` turns acceptance into derivability (`treeDerives orderSig`).

* `succIrreflProof`: `∀x ¬ succ x < succ x` from the order theory (`∀x ¬ x < x`, `∀x x < succ x`),
  by `∀`-elimination of irreflexivity at `succ x`; also as indexed lines.
* `eqSymmProof`: `∀x ∀y. x = y → …`, in this language `∀x ∀y ¬(x = y ∧ ¬ y = x)`, by equality
  elimination and the negation rules.
* **Rejections**: a hypothesis that is not in the context, an `∀`-elimination at the wrong term, an
  unknown rule.
-/

@[expose] public section

namespace Silmaril.Consequence.FirstOrder.ND.Examples

open Silmaril.Logic.Institution.Examples.UFOL Silmaril.Consequence Silmaril.Consequence.FirstOrder
open Silmaril.Logic.Smt (SE)

/-- The order theory with one more variable in scope (closed sentences shift to themselves). -/
def theory1 : List (Formula orderSig 1) := orderTheory.map Formula.shift

/-- `¬ succ x < succ x`, for the innermost variable `x`. -/
def succIrreflBody : Formula orderSig 1 :=
  .not (.rel lt (args2 (.app succ (args1 (.var 0))) (.app succ (args1 (.var 0)))))

/-- `∀x ¬ x < x`, with one more variable in scope. -/
def irrefl1 : Formula orderSig 1 := irrefl.shift

/-- **`orderTheory ⊢ ∀x ¬ succ x < succ x`**: instantiate irreflexivity at `succ x`. -/
def succIrreflProof : ProofTree SE (Seq orderSig) :=
  .infer (.atom "all-intro") ⟨0, orderTheory, succIrrefl⟩
    [.infer (.list [.atom "all-elim", .list [.atom "app", .atom "succ", .list [.atom "var", .atom "0"]]])
        ⟨1, theory1, succIrreflBody⟩
      [.infer (.atom "hyp") ⟨1, theory1, irrefl1⟩ []]]

theorem succIrreflProof_checks :
    checkTree orderOps orderRels ((treeCodec orderOps orderRels).encode succIrreflProof) =
      .ok ⟨0, orderTheory, succIrrefl⟩ := by
  rw [checkTree_encode]; rfl

/-- The same proof as indexed lines. -/
theorem succIrreflProof_lines_checks :
    checkLines orderOps orderRels ((linesCodec orderOps orderRels).encode (succIrreflProof.lines 0)) =
      .ok ⟨0, orderTheory, succIrrefl⟩ := by
  rw [checkLines_encode]; rfl

/-- **Derived**: the order theory derives `∀x ¬ succ x < succ x` by a checked proof tree. -/
theorem succIrrefl_derives : treeDerives orderSig orderTheory succIrrefl :=
  checkTree_sound succIrreflProof_checks

/-- `x = y` for the two innermost variables (`var 1`, `var 0`). -/
def xEqY : Formula orderSig 2 := .eq (.var 1) (.var 0)

/-- `y = x`. -/
def yEqX : Formula orderSig 2 := .eq (.var 0) (.var 1)

/-- `∀x ∀y ¬(x = y ∧ ¬ y = x)`: symmetry of equality, in the connectives `¬`, `∧`. -/
def eqSymm : Sentence orderSig := .all (.all (.not (.and xEqY (.not yEqX))))

/-- **`⊢ ∀x ∀y ¬(x = y ∧ ¬ y = x)`**: assume `x = y ∧ ¬ y = x`; rewriting `x = x` along `x = y`
(motive `z = x`) gives `y = x`, contradicting `¬ y = x`. -/
def eqSymmProof : ProofTree SE (Seq orderSig) :=
  let h : Formula orderSig 2 := .and xEqY (.not yEqX)
  .infer (.atom "all-intro") ⟨0, [], eqSymm⟩
    [.infer (.atom "all-intro") ⟨1, [], .all (.not h)⟩
      [.infer (.atom "not-intro") ⟨2, [], .not h⟩
        [.infer (.list [.atom "eq-elim", .list [.atom "=", .list [.atom "var", .atom "0"],
              .list [.atom "var", .atom "2"]]]) ⟨2, [h], yEqX⟩
            [.infer (.atom "and-left") ⟨2, [h], xEqY⟩ [.infer (.atom "hyp") ⟨2, [h], h⟩ []],
             .infer (.atom "eq-refl") ⟨2, [h], .eq (.var 1) (.var 1)⟩ []],
         .infer (.atom "and-right") ⟨2, [h], .not yEqX⟩ [.infer (.atom "hyp") ⟨2, [h], h⟩ []]]]]

theorem eqSymmProof_checks :
    checkTree orderOps orderRels ((treeCodec orderOps orderRels).encode eqSymmProof) =
      .ok ⟨0, [], eqSymm⟩ := by
  rw [checkTree_encode]; rfl

theorem eqSymm_derives : treeDerives orderSig [] eqSymm := checkTree_sound eqSymmProof_checks

/-! ## Rejections -/

/-- Claims `∀x ¬ succ x < succ x` as a hypothesis of the order theory: it is not one. -/
def notAHyp : ProofTree SE (Seq orderSig) := .infer (.atom "hyp") ⟨0, orderTheory, succIrrefl⟩ []

theorem notAHyp_rejected :
    checkTree orderOps orderRels ((treeCodec orderOps orderRels).encode notAHyp) = .error .check := by
  rw [checkTree_encode]; rfl

/-- Instantiates irreflexivity at `x` but claims the instance at `succ x`. -/
def wrongInstance : ProofTree SE (Seq orderSig) :=
  .infer (.list [.atom "all-elim", .list [.atom "var", .atom "0"]]) ⟨1, theory1, succIrreflBody⟩
    [.infer (.atom "hyp") ⟨1, theory1, irrefl1⟩ []]

theorem wrongInstance_rejected :
    checkTree orderOps orderRels ((treeCodec orderOps orderRels).encode wrongInstance) =
      .error .check := by
  rw [checkTree_encode]; rfl

/-- An unknown rule. -/
def unknownRule : ProofTree SE (Seq orderSig) := .infer (.atom "magic") ⟨0, [], eqSymm⟩ []

theorem unknownRule_rejected :
    checkTree orderOps orderRels ((treeCodec orderOps orderRels).encode unknownRule) =
      .error .elaboration := by
  rw [checkTree_encode]; rfl

/-! ## Bytes (evaluated) -/

#guard (((treeCodec orderOps orderRels).parse ((treeCodec orderOps orderRels).print succIrreflProof)).map
  (checkRawTree orderOps orderRels)) == some (.ok ⟨0, orderTheory, succIrrefl⟩)

end Silmaril.Consequence.FirstOrder.ND.Examples
