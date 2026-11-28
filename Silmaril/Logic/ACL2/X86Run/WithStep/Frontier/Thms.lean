module

public import Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Defs
public import Silmaril.Logic.ACL2.X86Run.WithStep.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.WithStep.Frontier

open Standard

/-- These are the five installed entries of the pinned, arity-indexed step frontier. -/
theorem installed_exact : installedEntries =
    [(⟨"ACL2", "MV-NTH"⟩, 2), (⟨"COMMON-LISP", "EQL"⟩, 2), (⟨"COMMON-LISP", "NOT"⟩, 1),
      (⟨"X86ISA", "FAULT"⟩, 1), (⟨"X86ISA", "MS"⟩, 1)] := by decide

theorem remaining_exact (entry : Name × Nat) :
    remaining.arity entry.1 = some entry.2 ↔ entry ∈ remainingEntries := by
  simp only [remaining, Option.filter_eq_some_iff, X86Step.frontier_exact,
    remainingEntries, List.mem_filter]

theorem remaining_iff (entry : Name × Nat) :
    remaining.arity entry.1 = some entry.2 ↔
      entry ∈ X86Step.frontierEntries ∧ entry ∉ installedEntries := by
  cases h : fixedBinding entry.1 entry.2 <;>
    simp [remaining_exact, remainingEntries, installedEntries, h]

theorem remaining_count : remainingEntries.length = 28 := by decide

theorem extend_of_fixed (bindings : Bindings) {k : Nat} (f : X86Step.frontier.Symbol k)
    {op : (Fin k → Object) → Object} (h : fixedBinding f.val k = some op) (args : Fin k → Object) :
    extend bindings f args = op args := by
  unfold extend
  split <;> simp_all

/-- Extension preserves the supplied denotation at each remaining symbol. -/
theorem extend_of_remaining (bindings : Bindings) {k : Nat} (f : remaining.Symbol k)
    (args : Fin k → Object) : extend bindings (remainingInclusion.symbol f) args = bindings f args := by
  have h : fixedBinding f.val k = none := Option.isNone_iff_eq_none.mp (Option.filter_eq_some_iff.mp f.property).2
  unfold extend
  split <;> simp_all [Signature.Hom.symbol]

theorem fault_agrees (bindings : Bindings) (x86 : Object) :
    extend bindings (⟨faultName, by decide⟩ : X86Step.frontier.Symbol 1) (fun _ => x86) =
      (machineBindings bindings).admittedModel.interpret
        (declaration.inclusion.symbol faultSymbol) (fun _ => x86) := rfl

theorem ms_agrees (bindings : Bindings) (x86 : Object) :
    extend bindings (⟨msName, by decide⟩ : X86Step.frontier.Symbol 1) (fun _ => x86) =
      (machineBindings bindings).admittedModel.interpret
        (declaration.inclusion.symbol msSymbol) (fun _ => x86) := rfl

/-- The run model interprets the step as the original checked body with the completed frontier. -/
theorem step_defining_equation (bindings : Bindings) (x86 : Object) :
    (machineBindings bindings).admittedModel.interpret
        (declaration.inclusion.symbol stepSymbol) (fun _ => x86) =
      X86Step.definition.body.eval (extend bindings) (fun _ => x86) :=
  WithStep.step_defining_equation (extend bindings) x86

theorem run_equation_holds (bindings : Bindings) :
    (declaration.equation runSymbol).Holds (machineBindings bindings).admittedModel :=
  WithStep.run_equation_holds (extend bindings)

theorem halted_holds (bindings : Bindings) : halted.Holds (machineBindings bindings).admittedModel :=
  WithStep.halted_holds (extend bindings)

end Silmaril.Logic.ACL2.X86Run.WithStep.Frontier
