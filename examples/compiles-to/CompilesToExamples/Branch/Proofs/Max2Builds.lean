module

public import CompilesToExamples.Branch.Proofs.O0Max2Function

/-! `examples/compiles-to/branch/branch.c`, `max2`: same source, both builds
(`c.compiles_to.builds`), from the per-build rows; the `-O2` row is open. -/

namespace CompilesToExamples.Branch

open Silmaril.Project.CompilesTo

/-- **Both builds of `max2` implement it**, given that it is safe from every entry
(`Task.max2_safe`) and the `-O2` row (both open). -/
public theorem max2_builds_of (h : Task.max2_safe) (h2 : O2.Task.max2_compiles_to) :
    Task.max2_builds := by
  intro b hb
  simp only [max2Builds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact O0.max2_compiles_to_of h
  · exact h2

end CompilesToExamples.Branch
