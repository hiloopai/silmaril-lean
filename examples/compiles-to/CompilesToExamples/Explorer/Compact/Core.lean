module

public import CompilesToExamples.Explorer.Compact.Checks
public import CompilesToExamples.Straight.Proofs.Elaborates
public import CompilesToExamples.Branch.Proofs.Elaborates
public import CompilesToExamples.Straight.Proofs.Add3CanonicalSafe
public import CompilesToExamples.Branch.Proofs.Max2CanonicalSafe

public section
namespace CompilesToExamples.Explorer.Compact

open Silmaril.Project.CompilesTo
open Silmaril.Project.Shapes.CompilesTo

/-- Exact, closed three-way agreement. The existing `elaborates_add3` identifies the Core
procedure with the result of elaborating the exact Ail being projected. -/
theorem add3_agrees : add3.fn.run #[1, 2, 3] = .ok 6 ∧ observeAil Straight.ail [1, 2, 3] = some 6 ∧
    Straight.Task.elaborates_add3 ∧ endsInt 6 (forcedRun Straight.add3Fn.file Straight.add3Fn.labels 400
      (Straight.add3Fn.canonicalEntry Straight.add3Args)) = true :=
  ⟨add3_observes.1, add3_observes.2, Straight.elaborates_add3, Straight.add3_returns_six⟩

/-- Exact, closed agreement on the taken branch, not universal Core soundness. -/
theorem max2_agrees : max2.fn.run #[1, 2] = .ok 2 ∧ observeAil Branch.ail [1, 2] = some 2 ∧
    Branch.Task.elaborates_max2 ∧ endsInt 2 (forcedRun Branch.max2Fn.file Branch.max2Fn.labels 400
      (Branch.max2Fn.canonicalEntry Branch.max2Args)) = true :=
  ⟨max2_observes.1, max2_observes.2, Branch.elaborates_max2, Branch.max2_returns_two⟩

end CompilesToExamples.Explorer.Compact
