module

public import Silmaril.Cerberus.Spec.Allowed.Defs

/-!
# Whole-program behaviours of closed C programs, and refinement between them

The vocabulary that C translation validation (docs/projects/c-tv.md) states its whole-program
edges in. A **closed program** is a Cerberus Core file with its enum registry and its
command-line arguments; its meaning is the nondeterministic Core LTS (`Core.Dynamics.lts`, the
concrete PNVI-ae-udi memory) from the startup state `Core.Dynamics.initial`.

The behaviours a closed program can have are kept apart:

| | definition | reading |
|---|---|---|
| `Ends P o out` | some run reaches a halted state with outcome `o` and stdout `out` | `o` is `defined v`, `ub`, `aborted`, or a **gap** of the Lean dynamics (`error`, `unsupported`) |
| `Stuck P` | some run reaches a state that is not halted and has no transition | a gap the dynamics does not even name |
| `Diverges P` | some run is infinite | divergence (not an observation of `Spec.Obs`) |
| `Allows impl P x` | `Spec.allowed`: some ending admits the observation `x` | undefined behaviour admits every observation; an unspecified exit value every exit status; gaps admit nothing |

**Refinement** (`Refines impl src tgt`) is the whole-program, terminating, observational
refinement:

1. every observation the target allows, the source allows (`Spec.allowed`, with the
   implementation-defined choices `impl`);
2. the target never reaches a gap: no `error` or `unsupported` ending and no stuck state;
3. the target has no infinite run.

(2) is what keeps refinement from being vacuous: a gap admits no observation, so without it a
target whose every run ends in `unsupported` would refine every source. (3) makes the relation
stronger than divergence-preserving refinement: a target that may diverge is never accepted here,
even when the source may diverge too (divergence-aware refinement is a separate shape on the
roadmap). Undefined behaviour on the **source** side is not filtered out: a source run that
reaches undefined behaviour admits every observation (C11 §4p2), so a target refines such a
source on that input whatever it does. Validators report when they relied on it.

**Parameters and fixed choices.** The only implementation-defined choices the relation takes as
parameters are those of `Spec.Impl` (the exit status of `exit(n)` and whether `abort` flushes).
Every other implementation-defined or unspecified choice is fixed inside the port: integer
conversions and shifts in the runtime maps, layouts (`Mem.Concrete`), and the **allocator**,
which is deterministic. Every `unseq` interleaving and `nd` choice the LTS keeps is explored, but
behaviours that ISO C allows through other allocation addresses (pointer comparisons and
address-dependent output) are not. So this is not a semantics parameterized by the full C
implementation; target profiles (`TV.Profile`) only check coherence, which is necessary, not
sufficient, for a result to transfer.

The relation is about the Lean port of Cerberus's Core semantics, not ISO C: how faithful the
Core dynamics and the elaboration are to the C standard is a separate, reviewed assumption
(docs/projects/cerberus.md).
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Spec

/-- **A closed C program as Cerberus Core**: the Core file, its enum registry and the
command-line arguments it is run with. -/
structure Closed where
  file : Program
  enums : Map Sym IntegerType := ∅
  args : List String := []

/-- Whether an ending is a gap of the Lean dynamics rather than a behaviour of C. -/
def Outcome.isGap : Outcome → Bool
  | .error _ | .unsupported _ => true
  | _ => false

/-- Whether an ending is undefined behaviour. -/
def Outcome.isUB : Outcome → Bool
  | .ub _ _ => true
  | _ => false

namespace Closed

variable (P : Closed)

/-- The startup state and the label environment of `main` (`Core.Dynamics.initial`). -/
def start : Except Outcome (State × Labels) :=
  initial P.file P.enums (Core.Startup.execArguments P.args)

/-- One transition of the Core LTS, under any label. -/
def Step (labels : Labels) (s t : State) : Prop :=
  ∃ a, (lts P.file labels).Tr s a t

/-- `n` transitions. -/
inductive Path (labels : Labels) : Nat → State → State → Prop where
  | refl (s : State) : Path labels 0 s s
  | step {n : Nat} {s u t : State} : P.Step labels s u → Path labels n u t → Path labels (n + 1) s t

/-- The states reachable from the start. -/
def Reachable (s : State) : Prop :=
  match P.start with
  | .error _ => False
  | .ok (s0, labels) => Reaches P.file labels s0 s

/-- **An ending**: some run ends halted with outcome `o` having printed `out`. A startup failure
is an ending with no output. -/
def Ends (o : Outcome) (out : String) : Prop :=
  match P.start with
  | .error o' => o = o' ∧ out = ""
  | .ok (s0, labels) =>
      ∃ s, Reaches P.file labels s0 s ∧ s.control = .halt o ∧ s.memory.stdout = out

/-- **Stuck**: some reachable state is not halted and has no transition. -/
def Stuck : Prop :=
  match P.start with
  | .error _ => False
  | .ok (s0, labels) =>
      ∃ s, Reaches P.file labels s0 s ∧ (∀ o, s.control ≠ .halt o) ∧ ∀ t, ¬ P.Step labels s t

/-- **Divergence**: some run is infinite. -/
def Diverges : Prop :=
  match P.start with
  | .error _ => False
  | .ok (s0, labels) => ∃ f : Nat → State, f 0 = s0 ∧ ∀ n, P.Step labels (f n) (f (n + 1))

/-- **The observations** of the program: `Spec.allowed` with the implementation-defined
choices `impl`. -/
def Allows (impl : Impl) (x : Obs) : Prop :=
  allowed impl P.file P.enums P.args x

/-- The program stays inside the supported fragment of the Lean dynamics: no gap ending and
no stuck state. -/
structure Supported : Prop where
  noGap : ∀ o out, P.Ends o out → Outcome.isGap o = false
  noStuck : ¬ P.Stuck

end Closed

/-- **Whole-program refinement** (module docstring): `tgt`'s observations are `src`'s, and
`tgt` is supported and terminates. -/
structure Refines (impl : Impl) (src tgt : Closed) : Prop where
  observations : ∀ x, tgt.Allows impl x → src.Allows impl x
  supported : tgt.Supported
  terminates : ¬ tgt.Diverges

/-- **No undefined behaviour**: no ending of the program is undefined behaviour. -/
def Closed.UBFree (P : Closed) : Prop :=
  ∀ o out, P.Ends o out → Outcome.isUB o = false

/-- **Refinement of a source without undefined behaviour**: the refinement then constrains the
target on every execution (no observation is admitted only because the source may reach UB). -/
structure RefinesUBFree (impl : Impl) (src tgt : Closed) : Prop where
  refines : Refines impl src tgt
  sourceUBFree : src.UBFree

/-- **Whole-program equivalence**: refinement both ways (so both programs are supported and
terminate, and they allow the same observations). -/
def Equivalent (impl : Impl) (P Q : Closed) : Prop :=
  Refines impl P Q ∧ Refines impl Q P

end Silmaril.Cerberus.TV
