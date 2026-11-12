module

public import Silmaril.Machine.OfLambdaSSA.Defs

/-!
# Why the fragment is needed

A region that `ofLambdaSSA` compiles, but whose RTL function does something the
region does not.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

/-! ## A pair whose first component is a tuple -/

theorem pairExample_compiles : Compiles [] pairExample .br 1 1 := by decide

theorem pairExample_fn :
    ofLambdaSSA [] pairExample .br 1 1 = ⟨⟨1, 1⟩, 0, [⟨[0], [], .ret [0]⟩]⟩ := rfl

/-- The function returns its argument, `[7]`; the region evaluates to the pair
`(7, ())` paired with `()`, which is not `packValues [7]`. -/
theorem pairExample_differs (m : Memory) :
    (Frame.empty.set 0 7 : Frame ℕ).readAll (freshRegs 0 1) = some [7] ∧
      Func.Exec noCalls (ofLambdaSSA [] pairExample .br 1 1) 0 (Frame.empty.set 0 7) m
        (.returned [7] m) ∧
      ¬ Semantics.Region.Eval (Opcode.step noCalls) (fun _ => packValues [7]) pairExample m 0
        (packValues [7]) m := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [pairExample_fn]
    exact .ret rfl .nil rfl rfl
  · intro h
    cases h with
    | br harg =>
      cases harg with
      | pair h₁ _ => cases h₁

end Silmaril.Proofs.Machine.OfLambdaSSA

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope.LambdaSSA

/-! ## The fragment excludes it, and includes loops -/

theorem pairExample_not_fits : ¬ RootFits [] pairExample .br 1 1 := by
  intro h
  simp only [RootFits, pairExample] at h
  cases h with
  | br _ harg =>
    cases harg with
    | pair ha _ =>
      cases ha with
      | var hΓ => simp at hΓ

theorem loopExample_compiles : Compiles [] loopExample SSA.aliasAnn 1 1 := by decide

theorem loopExample_fits : RootFits [] loopExample SSA.aliasAnn 1 1 :=
  ⟨rfl, .case (.var rfl) (.br rfl (.op (by decide) .unit)) (.br rfl (.var rfl))⟩

end Silmaril.Proofs.Machine.OfLambdaSSA
