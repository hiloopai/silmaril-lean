module

public import Silmaril.Proofs.Wasm.FX.Asyncify.SM.Lock
public import Silmaril.Wasm.FX.Asyncify.Steps.Thms

/-!
# Asyncify by a whole-program state machine: results

The header of `Defs`: the state machine `pstep P f₀ test` (program counter `(fn, pc)` as data,
dispatch on it at every step, frame records instead of a host call stack).

* **`step_dec`**: `sstep P test (dec P f₀ x) = (pstep P f₀ test x).map (dec P f₀)` for every
  configuration `x`: the state machine runs in lock step with the handler kernel, one step for
  one, with no hypothesis on `P`.
* **`kernel_sm_correct`**: a call of `f` in the kernel and in the state machine have the same
  behaviours; **`kernel_sm_steps`**: and stop after the same numbers of steps (`SameSteps`).
* `smScheme`, `sm_correct`, `sm_comorphism`: the instance of the asyncify family
  (`Silmaril.Wasm.FX.Asyncify.Scheme`); every program is in its fragment, and its compiler is the
  identity (the strategy changes the machine, not the instructions).
* Relation to `unwindDispatch`: **`sm_eq_dispatch`** (same behaviours as the dispatch instance on
  that instance's fragment, for every optimization) and **`sm_no_slower_dispatch`** (never slower
  than whole-program dispatch: no checks, no unwinding steps); `fwd_sm_faster`: on the
  forwarding generator of `FXAsync` the state machine stops after 20 steps (as the kernel), the dispatch
  machine after 35.

What this does **not** say: `pstep` is an abstract machine. A `suspend` moves the records above
the handler into the store in one step, which a Core 3.0 implementation does by a loop over
linear memory or a pointer split; the dispatch loop is not given as Core code.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.SM

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify (Scheme Opt srcRun scheme Strategy dispatch_correct)
open Silmaril.Wasm.FX.Asyncify.Steps
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.Models.FXAsyncPC (fstep annP bodies fInit rootCode)

variable {V : Type}

/-- **The state machine runs in lock step with the handler kernel.** -/
theorem step_dec (P : Prog (Ins V)) (f₀ : Nat) (test : V → Bool) (x : PCfg V) :
    sstep P test (dec P f₀ x) = (pstep P f₀ test x).map (dec P f₀) :=
  Silmaril.Proofs.Wasm.FX.Asyncify.SM.step_dec test x

theorem dec_init (P : Prog (Ins V)) (f : Nat) (args : List (SV V)) :
    dec P f (pInit args) = sInit f args := rfl

/-- **The kernel and the state machine have the same behaviours.** -/
theorem kernel_sm_correct (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (sstep P test) (sInit f args) = beh (pstep P f test) (pInit args) :=
  beh_eq_of_map (step_dec P f test) (pInit args)

/-- **… and take the same numbers of steps.** -/
theorem kernel_sm_steps (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    SameSteps (sstep P test) (pstep P f test) (sInit f args) (pInit args) :=
  sameSteps_of_map (step_dec P f test) (pInit args)

/-- **The state-machine instance of the asyncify family.** -/
def smScheme (V : Type) : Scheme V where
  TP := Prog (Ins V)
  compile := id
  run := fun Q test f args => beh (pstep Q f test) (pInit args)
  dom := fun _ => True

theorem sm_correct : (smScheme V).Correct :=
  fun P _ test f args => (kernel_sm_correct P test f args).symm

/-- The state-machine instance is a comorphism (equal on every sentence). -/
def sm_comorphism : Transition (Silmaril.Wasm.FX.Asyncify.srcChart (smScheme V).dom)
    (smScheme V).tgtChart :=
  (smScheme V).comorphism sm_correct

/-- **The state machine and stack unwinding with dispatch agree** on the dispatch instance's
fragment. -/
theorem sm_eq_dispatch (o : Opt) (P : Prog (Ins V)) (hP : o.Dom P) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    (smScheme V).run ((smScheme V).compile P) test f args =
      (scheme V .unwindDispatch o).run ((scheme V .unwindDispatch o).compile P) test f args :=
  (sm_correct P trivial test f args).trans (dispatch_correct o P hP test f args).symm

/-- **The state machine is never slower than whole-program unwinding with dispatch.** -/
theorem sm_no_slower_dispatch (P : Prog (Ins V)) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    NoSlower (pstep P f test) (fstep (annP (compP P)) (bodies (compP P) (rootCode f)) test)
      (pInit args) (fInit f args) :=
  (kernel_sm_steps P test f args).2.trans (kernel_no_slower_dispatch P test f args)

open Silmaril.Proofs.Wasm.Models.FXAsync (fwdP natTest) in
/-- On the forwarding generator, the state machine stops after 20 steps; the dispatch machine
is still running after 34 (it stops after 35). -/
theorem fwd_sm_faster :
    runN (pstep fwdP 2 natTest) 20 (pInit []) = .stop (.done [.val 3]) ∧
      ∃ c, runN (fstep (annP (compP fwdP)) (bodies (compP fwdP) (rootCode 2)) natTest) 34
        (fInit 2 []) = .next c :=
  ⟨rfl, ⟨_, rfl⟩⟩

/-- info: 'Silmaril.Wasm.FX.Asyncify.SM.sm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sm_correct

/-- info: 'Silmaril.Wasm.FX.Asyncify.SM.sm_no_slower_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sm_no_slower_dispatch

end Silmaril.Wasm.FX.Asyncify.SM
