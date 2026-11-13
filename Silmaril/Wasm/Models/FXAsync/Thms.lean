module

public import Silmaril.Proofs.Wasm.Models.FXAsync.Example

/-!
# An asyncify-style lowering of one-shot effect handlers: results

The header of `Defs`: the handler kernel `sstep` (one-shot shallow handlers with nesting,
forwarding and first-class continuations), the asyncify machine `tstep` (no continuations, no
handler frames: a heap of saved stacks, unwinding by call-site checks, rewinding by re-entering
saved frames) and the local lowering `comp`/`compP`, with `trC` relating configurations.

* **`lower_correct`**: for every function table `P`, branch test and source configuration `x`,
  the source from `x` and the compiled program from `trC x` have the same behaviours (returned
  values, trap, divergence). No well-formedness hypothesis is needed: every source failure is a
  trap, and the target traps in the same situations (an unhandled tag after unwinding every
  frame).
* `lower_correct_init`: the same for a call of function `f` with arguments `args`.
* `sim_step`: the proof's core, a stuttering simulation. A source step is matched by one target
  step, by two for a return (the frame below passes its check), by `1 + |frames|` for a
  `resume` (one rewinding step per saved frame) and by `1 + |passed frames| + 1` for a `suspend`
  (one unwinding step per frame between the suspender and the handling resumer). Both machines
  are functions, so the forward simulation gives equal behaviours (`beh_eq_of_sim`).
* `fwd_beh`, `fwd_beh_tgt`: a generator whose suspensions are forwarded through an inner handler,
  returning `[3]` as its only behaviour on both machines.

What this does **not** say: the kernel is an abstract machine, not `StepFX'`; the target is not
Core 3.0 `Step`. See "Stretch, fxcps" in `docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAsync

open Silmaril.Proofs.Wasm.Models.FXAsync (SimStep)

variable {V : Type}

/-- **The asyncify lowering is a stuttering simulation.** -/
theorem sim_step (P : Prog (Ins V)) (test : V → Bool) :
    SimStep (sstep P test) (tstep (compP P) test) trC :=
  Silmaril.Proofs.Wasm.Models.FXAsync.simStep P test

/-- **The asyncify lowering of one-shot handlers preserves behaviours.** -/
theorem lower_correct (P : Prog (Ins V)) (test : V → Bool) (x : SCfg V) :
    beh (sstep P test) x = beh (tstep (compP P) test) (trC x) :=
  Silmaril.Proofs.Wasm.Models.FXAsync.beh_eq P test x

/-- The same for a call of `f` with arguments `args`. -/
theorem lower_correct_init (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (sstep P test) (sInit f args) = beh (tstep (compP P) test) (tInit f args) :=
  lower_correct P test (sInit f args)

/-- The forwarding generator returns `[3]`, and nothing else, on the source machine. -/
theorem fwd_beh :
    beh (sstep Silmaril.Proofs.Wasm.Models.FXAsync.fwdP Silmaril.Proofs.Wasm.Models.FXAsync.natTest)
      (sInit 2 []) = {.done [.val 3]} :=
  Silmaril.Proofs.Wasm.Models.FXAsync.fwd_beh

/-- … and on the compiled program. -/
theorem fwd_beh_tgt :
    beh (tstep (compP Silmaril.Proofs.Wasm.Models.FXAsync.fwdP)
      Silmaril.Proofs.Wasm.Models.FXAsync.natTest) (tInit 2 []) = {.done [.val 3]} :=
  Silmaril.Proofs.Wasm.Models.FXAsync.fwd_beh_tgt

/-- info: 'Silmaril.Wasm.Models.FXAsync.lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_correct

/-- info: 'Silmaril.Wasm.Models.FXAsync.fwd_beh_tgt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwd_beh_tgt

end Silmaril.Wasm.Models.FXAsync
