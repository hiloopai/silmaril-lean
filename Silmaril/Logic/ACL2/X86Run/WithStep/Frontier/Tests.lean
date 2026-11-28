module

import Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Thms
import Lean

namespace Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Tests

open Standard

private def faultSymbol : X86Step.frontier.Symbol 1 := ⟨faultName, by decide⟩
private def msSymbol : X86Step.frontier.Symbol 1 := ⟨msName, by decide⟩
private def mvNthSymbol : X86Step.frontier.Symbol 2 := ⟨⟨"ACL2", "MV-NTH"⟩, by decide⟩
private def eqlSymbol : X86Step.frontier.Symbol 2 := ⟨⟨"COMMON-LISP", "EQL"⟩, by decide⟩
private def notSymbol : X86Step.frontier.Symbol 1 := ⟨⟨"COMMON-LISP", "NOT"⟩, by decide⟩

example (bindings : Bindings) : Status.observations.all (fun o =>
    decide (extend bindings faultSymbol (fun _ => o.state) = o.fault ∧
      extend bindings msSymbol (fun _ => o.state) = o.ms)) = true := rfl

example (bindings : Bindings) (index values : Object) :
    extend bindings mvNthSymbol ![index, values] = index.mvNth values := rfl
example (bindings : Bindings) (x y : Object) :
    extend bindings eqlSymbol ![x, y] = x.eql y := rfl
example (bindings : Bindings) (x : Object) :
    extend bindings notSymbol (fun _ => x) = x.logicalNot := rfl

example : (fixedBinding ⟨"ACL2", "FAULT"⟩ 1).isNone = true := rfl
example : (fixedBinding faultName 2).isNone = true := rfl
example : remaining.arity ⟨"X86ISA", "!MS"⟩ = some 2 := by decide
example : remaining.arity ⟨"BITOPS", "PART-SELECT-LOW-HIGH$INLINE"⟩ = some 3 := by decide

private def both := (Status.observations[1]'(by decide)).state
private def msOnly := (Status.observations[2]'(by decide)).state

example (bindings : Bindings) : (machineBindings bindings).run (.integer 2) both = both :=
  (machineBindings bindings).fault_exit _ _ (by intro h; contradiction)

example (bindings : Bindings) : (machineBindings bindings).run (.integer 2) msOnly = msOnly :=
  (machineBindings bindings).ms_exit _ _ rfl (by intro h; contradiction)

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``installed_exact, ``remaining_exact, ``remaining_iff, ``remaining_count,
    ``extend_of_fixed, ``extend_of_remaining, ``fault_agrees, ``ms_agrees,
    ``step_defining_equation, ``run_equation_holds, ``halted_holds]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"ACL2 X86-RUN reduced frontier: audited {declarations.size} declarations"

end Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Tests
