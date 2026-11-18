module

public import Silmaril.Logic.Consequence.Arithmetic.Derivation.SExp.Thms
public meta import Silmaril.Logic.Consequence.Arithmetic.Derivation.SExp.Thms

/-!
# Concrete PA and Q proofs, checked by the kernel

Each proof is a raw proof tree; its S-expression is `treeCodec.encode` of it, and each `…_checks`
theorem says the whole pipeline (decode, elaborate, check) accepts that S-expression with the
stated conclusion. `…_derives` turns acceptance into derivability (`paDerives` / `qDerives`).

* `zeroAddZero`: `⊢ 0 + 0 = 0` (the axiom `add-zero`), in Q and PA.
* `instAddZero`: `⊢ 0 + 0 = 0` again, from `⊢ ∀x. x + 0 = x` by `∀`-elimination at `0`; also in
  the indexed lines format.
* `eqSymm`: `⊢ ∀x ∀y. x = y → y = x`, by equality elimination (pure logic: Q and PA).
* `zeroAdd`: `⊢ ∀x. 0 + x = x` **by induction**: PA accepts it, Q rejects its induction axiom.

**Rejections** (negative tests): a wrong conclusion for an axiom, an unknown rule, a hypothesis
that is not in the context, a citation of a later line, empty lines, and a non-proof.
-/

@[expose] public section

namespace Silmaril.Consequence.Arithmetic.ND.Examples

open Silmaril.Logic.Arithmetic Silmaril.Consequence
open Silmaril.Logic.Smt (SE)

/-- A raw axiom rule. -/
def ax (name : String) : SE := .list [.atom "ax", .atom name]

/-- A judgment with no hypotheses and no free variables. -/
def closed (φ : Sentence) : Seq := ⟨0, [], φ⟩

/-- `0 + 0 = 0`. -/
def zeroAddZeroFormula : Sentence := .equal (.add .zero .zero) .zero

/-! ## `⊢ 0 + 0 = 0` -/

/-- `⊢ 0 + 0 = 0` by the axiom `add-zero`. -/
def zeroAddZero : ProofTree SE Seq := .infer (ax "add-zero") (closed zeroAddZeroFormula) []

theorem zeroAddZero_checks_q :
    checkTree .q (treeCodec.encode zeroAddZero) = .ok (closed zeroAddZeroFormula) := by
  rw [checkTree_encode]; rfl

theorem zeroAddZero_checks_pa :
    checkTree .pa (treeCodec.encode zeroAddZero) = .ok (closed zeroAddZeroFormula) := by
  rw [checkTree_encode]; rfl

theorem zeroAddZero_derives : paDerives [] zeroAddZeroFormula :=
  checkTree_sound zeroAddZero_checks_pa

/-! ## `∀`-elimination -/

/-- `⊢ ∀x. x + 0 = x`. -/
def allAddZero : ProofTree SE Seq :=
  .infer (.atom "all-intro") (closed (.all (.equal (.add (.var 0) .zero) (.var 0))))
    [.infer (ax "add-zero") ⟨1, [], .equal (.add (.var 0) .zero) (.var 0)⟩ []]

/-- `⊢ 0 + 0 = 0` from `⊢ ∀x. x + 0 = x` at `0`. -/
def instAddZero : ProofTree SE Seq :=
  .infer (.list [.atom "all-elim", .atom "zero"]) (closed zeroAddZeroFormula) [allAddZero]

theorem instAddZero_checks :
    checkTree .q (treeCodec.encode instAddZero) = .ok (closed zeroAddZeroFormula) := by
  rw [checkTree_encode]; rfl

/-- The same proof as indexed lines (`ProofTree.lines`). -/
theorem instAddZero_lines_checks :
    checkLines .q (linesCodec.encode (instAddZero.lines 0)) = .ok (closed zeroAddZeroFormula) := by
  rw [checkLines_encode]; rfl

theorem instAddZero_derives : qDerives [] zeroAddZeroFormula :=
  checkTree_sound instAddZero_checks

/-! ## Symmetry of equality -/

/-- `x = y` with `x` and `y` the two innermost variables (`var 1`, `var 0`). -/
def xEqY : Formula 2 := .equal (.var 1) (.var 0)

/-- `y = x`. -/
def yEqX : Formula 2 := .equal (.var 0) (.var 1)

/-- `∀x ∀y. x = y → y = x`. -/
def eqSymmFormula : Sentence := .all (.all (.imp xEqY yEqX))

/-- `⊢ ∀x ∀y. x = y → y = x`: rewrite `x = x` along `x = y` with the motive `z = x`. -/
def eqSymm : ProofTree SE Seq :=
  .infer (.atom "all-intro") (closed eqSymmFormula)
    [.infer (.atom "all-intro") ⟨1, [], .all (.imp xEqY yEqX)⟩
      [.infer (.atom "imp-intro") ⟨2, [], .imp xEqY yEqX⟩
        [.infer (.list [.atom "eq-elim", .list [.atom "=", .list [.atom "var", .atom "0"],
            .list [.atom "var", .atom "2"]]]) ⟨2, [xEqY], yEqX⟩
          [.infer (.atom "hyp") ⟨2, [xEqY], xEqY⟩ [],
           .infer (.atom "eq-refl") ⟨2, [xEqY], .equal (.var 1) (.var 1)⟩ []]]]]

theorem eqSymm_checks : checkTree .q (treeCodec.encode eqSymm) = .ok (closed eqSymmFormula) := by
  rw [checkTree_encode]; rfl

theorem eqSymm_derives : qDerives [] eqSymmFormula := checkTree_sound eqSymm_checks

/-! ## Induction: `⊢ ∀x. 0 + x = x` in PA -/

/-- `0 + x = x`, in the induction variable. -/
def zeroAddBody : Formula 1 := .equal (.add .zero (.var 0)) (.var 0)

/-- `∀x. 0 + x = x`. -/
def zeroAddFormula : Sentence := .all zeroAddBody

/-- `⊢ ∀x. 0 + x = x`: the induction axiom for `0 + x = x`, with the base case by `add-zero` and
the step `0 + x = x ⊢ 0 + Sx = Sx` by rewriting `add-succ` along the hypothesis. -/
def zeroAdd : ProofTree SE Seq :=
  .infer (.atom "imp-elim") (closed zeroAddFormula)
    [.infer (ax "induction") (closed (inductionSchema zeroAddBody)) [],
     .infer (.atom "and-intro")
        (closed (.conj (zeroAddBody.inst .zero) (.all (.imp zeroAddBody zeroAddBody.step))))
      [.infer (ax "add-zero") (closed (zeroAddBody.inst .zero)) [],
       .infer (.atom "all-intro") (closed (.all (.imp zeroAddBody zeroAddBody.step)))
        [.infer (.atom "imp-intro") ⟨1, [], .imp zeroAddBody zeroAddBody.step⟩
          [.infer (.list [.atom "eq-elim", .list [.atom "=",
                .list [.atom "+", .atom "zero", .list [.atom "succ", .list [.atom "var", .atom "1"]]],
                .list [.atom "succ", .list [.atom "var", .atom "0"]]]])
              ⟨1, [zeroAddBody], zeroAddBody.step⟩
            [.infer (.atom "hyp") ⟨1, [zeroAddBody], zeroAddBody⟩ [],
             .infer (ax "add-succ")
              ⟨1, [zeroAddBody], .equal (.add .zero (.succ (.var 0))) (.succ (.add .zero (.var 0)))⟩
              []]]]]]

theorem zeroAdd_checks_pa :
    checkTree .pa (treeCodec.encode zeroAdd) = .ok (closed zeroAddFormula) := by
  rw [checkTree_encode]; rfl

/-- **Q rejects it**: induction is not a Q axiom. -/
theorem zeroAdd_rejected_q : checkTree .q (treeCodec.encode zeroAdd) = .error .check := by
  rw [checkTree_encode]; rfl

theorem zeroAdd_derives : paDerives [] zeroAddFormula := checkTree_sound zeroAdd_checks_pa

/-! ## Rejections -/

/-- `add-zero` does not conclude `0 + 0 = S0`. -/
theorem wrongAxiom_rejected :
    checkTree .pa (treeCodec.encode (.infer (ax "add-zero")
      (closed (.equal (.add .zero .zero) (.succ .zero))) [])) = .error .check := by
  rw [checkTree_encode]; rfl

/-- An unknown rule. -/
theorem unknownRule_rejected :
    checkTree .pa (treeCodec.encode (.infer (.atom "magic") (closed zeroAddZeroFormula) [])) =
      .error .elaboration := by
  rw [checkTree_encode]; rfl

/-- A hypothesis that is not in the context. -/
theorem missingHyp_rejected :
    checkTree .pa (treeCodec.encode (.infer (.atom "hyp") (closed zeroAddZeroFormula) [])) =
      .error .check := by
  rw [checkTree_encode]; rfl

/-- A line citing a later line. -/
theorem forwardCitation_rejected :
    checkLines .q (linesCodec.encode
      [.infer (.atom "all-intro") (closed (.all (.equal (.add (.var 0) .zero) (.var 0)))) [1],
       .infer (ax "add-zero") ⟨1, [], .equal (.add (.var 0) .zero) (.var 0)⟩ []]) =
      .error .elaboration := by
  rw [checkLines_encode]; rfl

/-- No lines. -/
theorem empty_rejected : checkLines .q (linesCodec.encode []) = .error .empty := by
  rw [checkLines_encode]; rfl

/-- Not a proof. -/
theorem notProof_rejected : checkTree .q (.atom "proof") = .error .syntax := rfl

/-! ## Bytes (evaluated) -/

#guard checkTreeBytes .q ("(infer (all-elim zero) (seq 0 () (= (+ zero zero) zero)) " ++
  "(infer all-intro (seq 0 () (forall (= (+ (var 0) zero) (var 0)))) " ++
  "(infer (ax add-zero) (seq 1 () (= (+ (var 0) zero) (var 0))))))").toUTF8.toList ==
    .ok (closed zeroAddZeroFormula)
#guard checkLinesBytes .q ("(proof (infer (ax add-zero) (seq 1 () (= (+ (var 0) zero) (var 0))) ()) " ++
  "(infer all-intro (seq 0 () (forall (= (+ (var 0) zero) (var 0)))) (0)) " ++
  "(infer (all-elim zero) (seq 0 () (= (+ zero zero) zero)) (1)))").toUTF8.toList ==
    .ok (closed zeroAddZeroFormula)
/- A non-canonical numeral (`00`) is a syntax error. -/
#guard checkTreeBytes .q "(infer (ax add-zero) (seq 00 () (= (+ zero zero) zero)))".toUTF8.toList ==
  .error .syntax
#guard checkTreeBytes .q "(infer (ax add-zero) (seq 0 () (= (+ zero zero) zero))".toUTF8.toList ==
  .error .syntax

end Silmaril.Consequence.Arithmetic.ND.Examples
