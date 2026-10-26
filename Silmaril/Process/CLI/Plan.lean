module

public import Silmaril.Process.CLI.Transcript
public import Silmaril.Process.CLI.Sha256

/-! # PLAN: target statements, not yet proved

**This file is the plan.** Every declaration here is a `def … : Prop` naming a
statement to be proved later; nothing here is asserted, and there is no
`sorry`. A proof of one of these is a term of the named `Prop`, in another
file. The definitions in the rest of `Silmaril.Process.CLI` are complete.

The statements, from the bottom up:

1. (done: `X86Linux.Transcript.fetch` and `Transcript.step` in
   `CLI.Transcript`; the statement first planned here was false without
   `Image.WF`: a segment whose file bytes exceed its memory size.)
2. `StreamLaw`: in `Env.reliable`, the bytes a run has read from stdin are
   exactly the next bytes of the stream (the environment fact a filter proof
   uses). It is false in `Env.linux`, where a failed read may consume input.
3. `Sha256Goal`: the end-to-end statement for a freestanding `sha256` filter
   binary: safety at `eintrClean` (or `linux` for a program that never
   retries), coverage at `linux`, and a step budget at `linux` linear in the
   input plus a constant per refusal.
4. `NoStuck`: under a total ISA and an environment that answers every call,
   every reachable state steps or has exited (the liveness half that
   `Agrees`/`Bounded` deliberately omit).
-/

@[expose] public section

namespace Silmaril.Process.CLI.Plan

open Silmaril.Process.Syscall

/-- (2) In the reliable environment, stdin reads follow the stream exactly. -/
def StreamLaw : Prop :=
  ∀ (I : Isa) (input : ProcInput) (x y : PState I Env.reliable) (events : List Event),
    linuxInit input (Env.reliable.memory x.env) x.env →
    Proc.Runs I Env.reliable x events y →
      input.stdin.Matches 0 (stdinRead events) ∧
      ∀ d, y.env.descriptors 0 = some d → d.cursor = (stdinRead events).length

/-- Finite standard input. -/
def FiniteStdin (input : ProcInput) : Prop := ∃ bytes, input.stdin = .ofList bytes

/-- The length of a finite stdin (0 otherwise; only used under `FiniteStdin`). -/
noncomputable def stdinLength (input : ProcInput) : Nat :=
  open Classical in if h : FiniteStdin input then (Classical.choose h).length else 0

/-- (3) The end-to-end goal for a sha256 filter image, with a budget of
`base + perByte · |stdin|` steps plus `perRefusal` per environment refusal. -/
def Sha256Goal (image : Image) (base perByte perRefusal : Nat) : Prop :=
  Agrees X86Linux.eintrClean image Sha256.strict ∧
  Covered X86Linux.linux image ∧
  Bounded X86Linux.linux image FiniteStdin (fun input => base + perByte * stdinLength input) perRefusal

/-- (3') The same with safety at full `linux`, for a program that exits on every error. -/
def Sha256GoalNoRetry (image : Image) (base perByte perRefusal : Nat) : Prop :=
  Agrees X86Linux.linux image Sha256.strict ∧
  Covered X86Linux.linux image ∧
  Bounded X86Linux.linux image FiniteStdin (fun input => base + perByte * stdinLength input) perRefusal

/-- (4) No reachable state is stuck. -/
def NoStuck (M : Model) (image : Image) : Prop :=
  M.isa.Total → M.env.Answers →
    ∀ input x, input.Valid → M.Init image input x → ∀ events y, Proc.Runs M.isa M.env x events y →
      (∃ events' y', Proc.Step M.isa M.env y events' y') ∨ ∃ o, Proc.Stop M.isa M.env y o

end Silmaril.Process.CLI.Plan
