module

public import Silmaril.Compiler.C.Sem.TargetsC6Ladder.Defs
@[expose] public section

namespace Silmaril.Compile.Targets.Proofs

open Silmaril.Compile.C.Sem

theorem c6_extends_c5 : Targets.c6_extends_c5 := by
  intro p h
  unfold C6.beh C5.beh
  simp only [C6.run_eq_c5 h]

end Silmaril.Compile.Targets.Proofs
