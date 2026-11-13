module

public import CompilesToExamples.Straight.Proofs.O0Add3Function
public import CompilesToExamples.Straight.Proofs.O2Add3Function

/-! `examples/compiles-to/straight/straight.c`, `add3`: same source, both builds
(`c.compiles_to.builds`), from the per-build rows. -/

namespace CompilesToExamples.Straight

open Silmaril.Project.CompilesTo

/-- **Both builds of `add3` implement it**, given that it is safe from every entry
(`Task.add3_safe`, open). -/
public theorem add3_builds_of (h : Task.add3_safe) : Task.add3_builds := by
  intro b hb
  simp only [add3Builds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact O0.add3_compiles_to_of h
  · exact O2.add3_compiles_to_of h

end CompilesToExamples.Straight
