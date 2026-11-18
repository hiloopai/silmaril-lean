module

public import Silmaril.Logic.Consequence.Arithmetic.Derivation.Examples

/-!
# PA proofs as exported declarations (constructor normal form)

Proof objects written with constructors and literals only, so that an exported declaration's value
*is* the proof: `lean4export` writes these declarations to Lean-NDJSON, and the importer
(`Silmaril.ProofFormats.LeanNDJSON.Arithmetic`) reads them back and checks them, without trusting
their declared types. Each is equal to the corresponding proof of `…Derivation.Examples`.

Parameterless definitions (such as `body` below) may appear inside a proof: the importer unfolds
them. Functions such as `inductionSchema` may not: `Examples.zeroAdd`, which uses them, is exported
as a negative case.
-/

@[expose] public section

namespace Silmaril.Consequence.Arithmetic.ND.Exported

open Silmaril.Logic.Arithmetic Silmaril.Consequence
open Silmaril.Logic.Smt (SE)

/-- `⊢ 0 + 0 = 0` by the axiom `add-zero`. -/
def zeroAddZero : ProofTree SE Seq :=
  .infer (.list [.atom "ax", .atom "add-zero"]) ⟨0, [], .equal (.add .zero .zero) .zero⟩ []

theorem zeroAddZero_eq : zeroAddZero = Examples.zeroAddZero := rfl

/-- `⊢ 0 + 0 = 0` from `⊢ ∀x. x + 0 = x`, by `∀`-elimination at `0`. -/
def instAddZero : ProofTree SE Seq :=
  .infer (.list [.atom "all-elim", .atom "zero"]) ⟨0, [], .equal (.add .zero .zero) .zero⟩
    [.infer (.atom "all-intro") ⟨0, [], .all (.equal (.add (.var 0) .zero) (.var 0))⟩
      [.infer (.list [.atom "ax", .atom "add-zero"]) ⟨1, [], .equal (.add (.var 0) .zero) (.var 0)⟩ []]]

theorem instAddZero_eq : instAddZero = Examples.instAddZero := rfl

/-- `⊢ ∀x ∀y. x = y → y = x`. -/
def eqSymm : ProofTree SE Seq :=
  .infer (.atom "all-intro")
      ⟨0, [], .all (.all (.imp (.equal (.var 1) (.var 0)) (.equal (.var 0) (.var 1))))⟩
    [.infer (.atom "all-intro") ⟨1, [], .all (.imp (.equal (.var 1) (.var 0)) (.equal (.var 0) (.var 1)))⟩
      [.infer (.atom "imp-intro") ⟨2, [], .imp (.equal (.var 1) (.var 0)) (.equal (.var 0) (.var 1))⟩
        [.infer (.list [.atom "eq-elim", .list [.atom "=", .list [.atom "var", .atom "0"],
            .list [.atom "var", .atom "2"]]]) ⟨2, [.equal (.var 1) (.var 0)], .equal (.var 0) (.var 1)⟩
          [.infer (.atom "hyp") ⟨2, [.equal (.var 1) (.var 0)], .equal (.var 1) (.var 0)⟩ [],
           .infer (.atom "eq-refl") ⟨2, [.equal (.var 1) (.var 0)], .equal (.var 1) (.var 1)⟩ []]]]]

theorem eqSymm_eq : eqSymm = Examples.eqSymm := rfl

/-- `0 + x = x`, in the induction variable. -/
def body : Formula 1 := .equal (.add .zero (.var 0)) (.var 0)

/-- `0 + Sx = Sx`: the induction step's conclusion. -/
def bodyStep : Formula 1 := .equal (.add .zero (.succ (.var 0))) (.succ (.var 0))

/-- `⊢ ∀x. 0 + x = x` by induction, with the induction instance written out. -/
def zeroAdd : ProofTree SE Seq :=
  .infer (.atom "imp-elim") ⟨0, [], .all body⟩
    [.infer (.list [.atom "ax", .atom "induction"])
        ⟨0, [], .imp (.conj (.equal (.add .zero .zero) .zero) (.all (.imp body bodyStep))) (.all body)⟩ [],
     .infer (.atom "and-intro")
        ⟨0, [], .conj (.equal (.add .zero .zero) .zero) (.all (.imp body bodyStep))⟩
      [.infer (.list [.atom "ax", .atom "add-zero"]) ⟨0, [], .equal (.add .zero .zero) .zero⟩ [],
       .infer (.atom "all-intro") ⟨0, [], .all (.imp body bodyStep)⟩
        [.infer (.atom "imp-intro") ⟨1, [], .imp body bodyStep⟩
          [.infer (.list [.atom "eq-elim", .list [.atom "=",
                .list [.atom "+", .atom "zero", .list [.atom "succ", .list [.atom "var", .atom "1"]]],
                .list [.atom "succ", .list [.atom "var", .atom "0"]]]])
              ⟨1, [body], bodyStep⟩
            [.infer (.atom "hyp") ⟨1, [body], body⟩ [],
             .infer (.list [.atom "ax", .atom "add-succ"])
              ⟨1, [body], .equal (.add .zero (.succ (.var 0))) (.succ (.add .zero (.var 0)))⟩ []]]]]]

theorem zeroAdd_eq : zeroAdd = Examples.zeroAdd := rfl

/-- Claims `⊢ 0 + 0 = S0` by `add-zero`: a well-formed declaration of a wrong proof. -/
def wrongAxiom : ProofTree SE Seq :=
  .infer (.list [.atom "ax", .atom "add-zero"]) ⟨0, [], .equal (.add .zero .zero) (.succ .zero)⟩ []

end Silmaril.Consequence.Arithmetic.ND.Exported
