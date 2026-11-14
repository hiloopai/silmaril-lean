module

public import Silmaril.X86.Concurrency.Cir.Rc11.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Rc11.Judge

/-!
# RC11 on CIR: theorems

PROVED (standard axioms only):

* `Rc11.judge_spec`: when the decision procedure answers, its first Boolean decides RC11
  consistency (`Rc11.Consistent`) and its second decides raciness (`Rc11.Racy`). The proof
  checks every bitmask the procedure builds against the relation it stands for
  (`Silmaril.Proofs.X86.Concurrency.Cir.Rc11.Judge`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Rc11

open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- **The RC11 decision procedure is correct.** -/
theorem judge_spec {ro : Nat → Role} {x : Exec} {c r : Bool} (h : judge ro x = some (c, r)) :
    (c = true ↔ Consistent ro x) ∧ (r = true ↔ Racy ro x) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc11.judge_spec h

/-- `force` is the identity. -/
theorem force_eq {α : Sort _} (v : Nat) (k : Nat → α) : force v k = k v :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc11.force_eq v k

end Silmaril.X86.Concurrency.Cir.Rc11
