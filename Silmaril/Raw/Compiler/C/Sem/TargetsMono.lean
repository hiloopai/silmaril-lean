module

public import Silmaril.Compiler.C.Sem.C1.Defs
public import Silmaril.Compiler.C.Sem.C2.Defs
public import Silmaril.Compiler.C.Sem.C3.Defs
public import Silmaril.Compiler.C.Sem.C4.Defs
public import Silmaril.Compiler.C.Sem.C5.Defs
@[expose] public section

/-!
# Fuel monotonicity and determinism targets for the rungs C1 … C5

`Targets.c0_run_mono` and `Targets.c0_deterministic` (`Targets.lean`) restated for each rung
above C0: more fuel does not change a final result of the rung's interpreter, and the rung has
one behaviour, or every behaviour after undefined behaviour. They are what exact-behaviour
results above C0 (Core realisation, validator completeness) start from.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.C.Sem

/-! ## c1 -/

/-- More fuel does not change a final result of the C1 interpreter. -/
def c1_run_mono : Prop :=
  ∀ (n k : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) (r : C0.Result),
    C1.run n p = r → (r = .outOfFuel → False) → C1.run (n + k) p = r

/-- C1 is deterministic: one behaviour, or every behaviour after undefined behaviour. -/
def c1_deterministic : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, (C1.beh p).Subsingleton ∨ C1.beh p = Set.univ

/-! ## c2 -/

/-- More fuel does not change a final result of the C2 interpreter. -/
def c2_run_mono : Prop :=
  ∀ (n k : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) (r : C0.Result),
    C2.run n p = r → (r = .outOfFuel → False) → C2.run (n + k) p = r

/-- C2 is deterministic: one behaviour, or every behaviour after undefined behaviour. -/
def c2_deterministic : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, (C2.beh p).Subsingleton ∨ C2.beh p = Set.univ

/-! ## c3 -/

/-- More fuel does not change a final result of the C3 interpreter. -/
def c3_run_mono : Prop :=
  ∀ (n k : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) (r : C0.Result),
    C3.run n p = r → (r = .outOfFuel → False) → C3.run (n + k) p = r

/-- C3 is deterministic: one behaviour, or every behaviour after undefined behaviour. -/
def c3_deterministic : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, (C3.beh p).Subsingleton ∨ C3.beh p = Set.univ

/-! ## c4 -/

/-- More fuel does not change a final result of the C4 interpreter. -/
def c4_run_mono : Prop :=
  ∀ (n k : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) (r : C0.Result),
    C4.run n p = r → (r = .outOfFuel → False) → C4.run (n + k) p = r

/-- C4 is deterministic: one behaviour, or every behaviour after undefined behaviour. -/
def c4_deterministic : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, (C4.beh p).Subsingleton ∨ C4.beh p = Set.univ

/-! ## c5 -/

/-- More fuel does not change a final result of the C5 interpreter. -/
def c5_run_mono : Prop :=
  ∀ (n k : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) (r : C0.Result),
    C5.run n p = r → (r = .outOfFuel → False) → C5.run (n + k) p = r

/-- C5 is deterministic: one behaviour, or every behaviour after undefined behaviour. -/
def c5_deterministic : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, (C5.beh p).Subsingleton ∨ C5.beh p = Set.univ

end Silmaril.Compile.Targets
