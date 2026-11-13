module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding.Thms
/-! Syntactic shape and exact annotation preservation for the actual folding
implementation. This theorem is independent of arithmetic purity or evaluation;
effectful and partial typed terms require separate semantic preservation. -/
@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.ShapePreservation
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Machine.RTL (Opcode)

theorem constantOp_results {opcode : Old.Opcode} {known : Abstract} {word : Silmaril.Machine.Lir.Word}
    (folded : constantOp opcode known = some word) : opcode.results = 1 := by
  cases opcode with
  | const | load | store | call | test => cases folded
  | move | unary | binary => rfl

/-- The actual term fold retains the existing shape judgment, independently of
purity, successful evaluation or the contents of the abstract environment. -/
theorem foldTm_fits {context : List Shape} {term : Old.Tm} {shape : Shape}
    (typed : TmFits [] context term shape) (known : List Abstract) :
    TmFits [] context (foldTm known term).1 shape := by
  induction typed generalizing known with
  | var lookup => exact .var lookup
  | unit => exact .unit
  | pair typedA typedB ihA ihB => exact .pair (ihA known) (ihB known)
  | @op context opcode argument notTest typedArg ih =>
    show TmFits [] context (foldTm known (.op opcode argument)).1 (.tuple opcode.results)
    by_cases constant : ∃ word, opcode = .const word
    · obtain ⟨word, rfl⟩ := constant
      exact .op (by intro impossible; cases impossible) typedArg
    · show TmFits [] context (foldTm known (.op opcode argument)).1 (.tuple opcode.results)
      have nonconstant : ∀ word, opcode ≠ .const word :=
        fun word same => constant ⟨word, same⟩
      rw [Folding.foldTm_op_eq known opcode argument nonconstant]
      cases folded : constantOp opcode (foldTm known argument).2.1 with
      | none =>
        simpa only [folded] using (TmFits.op notTest (ih known))
      | some word =>
        have resultShape : opcode.results = 1 := constantOp_results folded
        simp only [folded]
        rw [resultShape]
        exact .op (by intro impossible; cases impossible) .unit
  | let₁ typedA typedB ihA ihB => exact .let₁ (ihA known) (ihB _)
  | let₂ typedA typedB ihA ihB => exact .let₂ (ihA known) (ihB _)

/-- Region structure and every existing region annotation are retained by the
actual foldRegion, including test branches and arbitrary nested CFGs. This is
a syntactic typing theorem; effectful/partial terms need separate semantics. -/
theorem foldRegion_fits {context : List Shape} {region : Old.Region}
    {annotation : Silmaril.Machine.RTL.SSA.Ann} {labels : List Nat}
    (typed : RegionFits [] context region annotation labels) (known : List Abstract) :
    RegionFits [] context (foldRegion known region).1 annotation labels := by
  induction typed generalizing known with
  | br lookup typedArg => exact .br lookup (foldTm_fits typedArg known)
  | let₁ typedValue typedBody ih => exact .let₁ (foldTm_fits typedValue known) (ih _)
  | let₂ typedValue typedBody ih => exact .let₂ (foldTm_fits typedValue known) (ih _)
  | case typedArg typedLeft typedRight ihLeft ihRight =>
    exact .case (foldTm_fits typedArg known) (ihLeft _) (ihRight _)
  | cfg length typedEntry typedBlocks ihEntry ihBlocks =>
    exact .cfg length (ihEntry known) (fun index => ihBlocks index _)

/-- The actual RTL root wrapper keeps the special block-only shape context and
its exact annotation, as required by ofLambdaSSA's root-entry convention. -/
theorem foldRegion_rootWrapper_fits {blocks : Fin 1 → Old.Region}
    {width params results : Nat} {annotation : Silmaril.Machine.RTL.SSA.Ann}
    (typed : RootFits [] (.cfg (.br 0 (.var 0)) 1 blocks)
      (.cfg [width] .br [annotation]) params results) (known : List Abstract) :
    RootFits [] (foldRegion known (.cfg (.br 0 (.var 0)) 1 blocks)).1
      (.cfg [width] .br [annotation]) params results := by
  exact ⟨typed.1, foldRegion_fits typed.2 (.unknown :: known)⟩

end Silmaril.Compiler.Native.Optimize.LambdaSSA.ShapePreservation
