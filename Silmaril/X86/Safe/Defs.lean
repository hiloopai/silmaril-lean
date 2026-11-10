module

public import Silmaril.X86.Sep.Spec.Defs
public import Silmaril.Machine.Execution

/-!
# Step-indexed safety and triples over any segment-VC machine

The total triples of `Silmaril.X86.Sep.Triple` promise a finite run. For code that may run
forever (an event loop, a recursive function proved by induction on an index), the
step-indexed forms here promise only that the machine does not get stuck too early:

* `SafeN I Q n s`: **step-indexed partial correctness.** Within `n` steps from `s`, the
  machine `I` does not get stuck before it reaches a state satisfying `Q`.
* `STriple I n P Q`: the frame-quantified, step-indexed triple: for every frame `F` and
  every live state whose fragment splits as `P ∗ F`, `SafeN` towards `Q ∗ F`.
* `Progress I P R`: a total triple that takes at least one step (how a call pays for the
  callee's index).

Machines are related by `SegVC.Isa.Extends` (a lawful lens `view`/`put`): `SafeN.lift`,
`STriple.lift` and `Progress.lift` (`Safe/Thms.lean`) move safety up the tower, from
`Open.isa` to `Open9.isa` to `Str9.isa`, and total triples become step-indexed ones on the
same machine (`STriple.of_triple`).
-/

@[expose] public section

namespace Silmaril.X86.Safe

open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Sep

variable {σ : Type} (I : Isa σ)

/-- **Step-indexed partial correctness** on the machine `I`. -/
def SafeN (Q : σ → Prop) : Nat → σ → Prop
  | 0, _ => True
  | n + 1, s => Q s ∨ ∃ s', I.step s = some s' ∧ SafeN Q n s'

/-- **A step-indexed triple** on the machine `I`, frame built in. -/
def STriple (n : Nat) (P Q : SProp) : Prop :=
  ∀ (F : SProp) (s : σ), I.live s → (P ∗ F) (frag I s) →
    SafeN I (fun t => (Q ∗ F) (frag I t)) n s

/-- A total triple that takes at least one step. -/
def Progress (P R : SProp) : Prop :=
  ∀ (F : SProp) (s : σ), I.live s → (P ∗ F) (frag I s) →
    ∃ k t, run I.step (k + 1) s = some t ∧ (R ∗ F) (frag I t)

end Silmaril.X86.Safe
