import Silmaril.Project.Shapes.CTV.Thms
import Silmaril.Project.CTV.Examples.Defs

/-! Regression tests from the review of #943 (3ba15ad0): the function-level shape needs nonempty
contexts and a substitution witness; the weak relation's vacuous cases stay possible only there.
Kernel-checked (`cbv`, `decide`). -/

open Silmaril.Cerberus Silmaril.Cerberus.TV Silmaril.Project.CTV.Examples Silmaril.Project.Shapes.CTV

set_option maxRecDepth 100000

/-- C1. No context: the weak relation holds vacuously, the shape does not, and the validator
rejects. -/
example (d d' : Core.FunDecl Codec.wireModel Unit Unit) : ContextRefines Spec.Impl.lp64 [] mainSym d d' :=
  ContextRefines.nil _ _ _ _
example (d d' : Core.FunDecl Codec.wireModel Unit Unit) : ¬ CContextRefines Spec.Impl.lp64 [] mainSym d d' :=
  FunctionRefines.not_nil
example : validateContexts Spec.Impl.lp64 [] mainSym mainFoldBefore (mainDecl 2 2) = false := by cbv

/-- C2. A symbol the context does not define: `setFunction` is a no-op, so the weak relation holds
even for a wrong body, but there is no substitution witness, the shape does not hold, and the
validator rejects. -/
def bogusSym : Sym := ⟨⟨[]⟩, 999, .none⟩

example : (addBindings 1 2).setFunction bogusSym (mainDecl 2 2) = addBindings 1 2 := by cbv
example : ¬ Substitutes (addBindings 1 2) bogusSym := by decide +kernel
example : validateContexts Spec.Impl.lp64 mainContexts bogusSym mainFoldBefore (mainDecl 2 2) = false := by cbv
example : ¬ CContextRefines Spec.Impl.lp64 mainContexts bogusSym mainFoldBefore (mainDecl 2 2) :=
  fun h => absurd (h.substitutes (addBindings 1 2) (by simp [mainContexts])) (by decide +kernel)

/-- Shadowing: a context whose runtime library also defines `f` (looked up first by the dynamics)
has no substitution witness. -/
def shadowed : Codec.FileBindings :=
  { addBindings 1 2 with stdlib := (mainSym, mainDecl 1 2) :: (addBindings 1 2).stdlib }

example : ¬ Substitutes shadowed mainSym := by decide +kernel
example : validateContexts Spec.Impl.lp64 [shadowed] mainSym mainFoldBefore mainFoldAfter = false := by cbv

/-- C3. With the real symbol, a wrong body is rejected; the right one is accepted. -/
example : Substitutes (addBindings 1 2) mainSym := by decide +kernel
example : validateContexts Spec.Impl.lp64 mainContexts mainSym mainFoldBefore (mainDecl 2 2) = false := by cbv
example : validateContexts Spec.Impl.lp64 mainContexts mainSym mainFoldBefore mainFoldAfter = true := by cbv

/-! Module level (`ModuleRefines`, `validateModule`): the same side conditions. -/

attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
set_option cbv.maxSteps 10000000

example {rs : List Replacement} : ¬ CModuleRefines Spec.Impl.lp64 [] rs := ModuleRefines.not_nil
example : validateModule Spec.Impl.lp64 [] twoReplacements = false := by cbv
example : validateModule Spec.Impl.lp64 twoContexts [] = false := by cbv
/-- The same function twice is rejected. -/
example : validateModule Spec.Impl.lp64 twoContexts (twoReplacements ++ twoReplacements) = false := by cbv
/-- A function the context does not define is rejected. -/
example : validateModule Spec.Impl.lp64 twoContexts [⟨bogusSym, mainFoldBefore, mainFoldAfter⟩] = false := by cbv
