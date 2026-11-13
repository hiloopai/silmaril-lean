module

public import Silmaril.Compiler.C.Sem.TargetsC7Ladder.Defs
@[expose] public section

namespace Silmaril.Compile.Targets.Proofs

open Silmaril.Compile.C.Sem

theorem c7_extends_c6 : Targets.c7_extends_c6 := by
  intro p h
  unfold C7.beh C6.beh
  simp only [C7.run_eq_c6 h]

end Silmaril.Compile.Targets.Proofs
