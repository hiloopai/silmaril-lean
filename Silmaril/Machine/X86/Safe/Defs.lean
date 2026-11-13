module

public import Silmaril.Machine.X86.Sep.Spec.Defs
public import Silmaril.Machine.Execution

/-!
# Step-indexed safety and triples over any machine that extends the open machine

`SafeN` and `STriple` were defined in `Silmaril.Machine.Link.FnSpec` over the `Ext8` open
machine `Open.step` only. Here they are generic in
the machine: a step function `step : MState → Option MState`, for example `I.step` of a
`SegVC.Isa MState` (`Open.isa`, `Open9.isa`, `JumpTable.isa = Open9.isa`).
`Silmaril.Machine.Link.FnSpec.{SafeN, STriple, Progress}` are now the instances at `Open.step`.

* `SafeN step Q n m`: **step-indexed partial correctness.** Within `n` steps from `m`, the
  machine does not get stuck before it reaches a state satisfying `Q`.
* `STriple step n P Q`: the frame-quantified, step-indexed triple: for every frame `F` and
  every state whose total fragment splits as `P ∗ F`, `SafeN` towards `Q ∗ F`.
* `Progress step P R`: a total triple that takes at least one step (how a call pays for the
  callee's index).
* `Refines step step'`: every `step` step is a `step'` step.
* `ExtendsOpen step` (a class): `Refines Open.step step`. The total triples of the separation-logic layer
  (`Sep.Triple`, over `Open.step`) carry over to any such machine (`STriple.of_triple`, …
  in `Safe/Thms.lean`). Instances: `Open.step` (`Safe/Thms.lean`), `Open9.step` (and so
  `JumpTable.step`; `Safe/Open9/Thms.lean`).
-/

@[expose] public section

namespace Silmaril.Machine.X86.Safe

open Silmaril.X86 (MState)
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.X86.Sep

variable (step : MState → Option MState)

/-- **Step-indexed partial correctness** on the machine `step`. -/
def SafeN (Q : MState → Prop) : Nat → MState → Prop
  | 0, _ => True
  | n + 1, m => Q m ∨ ∃ m', step m = some m' ∧ SafeN Q n m'

/-- **A step-indexed triple** on the machine `step`, frame built in. -/
def STriple (n : Nat) (P Q : SProp) : Prop :=
  ∀ (F : SProp) (m : MState), (P ∗ F) (toFrag m) →
    SafeN step (fun m' => (Q ∗ F) (toFrag m')) n m

/-- A total triple that takes at least one step. -/
def Progress (P R : SProp) : Prop :=
  ∀ (F : SProp) (m : MState), (P ∗ F) (toFrag m) →
    ∃ k m', run step (k + 1) m = some m' ∧ (R ∗ F) (toFrag m')

/-- Every `step` step is a `step'` step. -/
def Refines (step' : MState → Option MState) : Prop :=
  ∀ {m m' : MState}, step m = some m' → step' m = some m'

/-- **The machine extends the `Ext8` open machine**: every `Open.step` step is one of it. -/
class ExtendsOpen : Prop where
  ext : Refines Silmaril.Machine.X86.Open.step step

end Silmaril.Machine.X86.Safe
