module

public import Silmaril.Proofs.Wasm.FX.Asyncify.CPS.Lock
public import Silmaril.Wasm.FX.Asyncify.SM.Thms

/-!
# Asyncify by continuation-passing style: results

The header of `Defs`: the CPS compiler `compK` (call sites, `resume` and `suspend` annotated with
the label of their continuation) and the CPS machine `cstep` (continuation records instead of a
host call stack, `suspend` and `resume` by splitting and pushing record lists).

* **`step_toC`**: `cstep (compK P) f₀ test (toC (compK P) f₀ x) = (pstep P f₀ test x).map
  (toC (compK P) f₀)`: CPS runs in lock step with the state machine of `SM`, for every program
  and configuration.
* **`kernel_cps_correct`**, **`kernel_cps_steps`**: so a call in the kernel and the same call in
  the CPS-compiled program have the same behaviours and the same step counts.
* `cpsScheme`, `cps_correct`, `cps_comorphism`: the instance of the asyncify family; every
  program is in its fragment.
* Relations: **`sm_cps_run_eq`** and `sm_vs_cps`, a comorphism from the state machine's target
  chart to CPS's (`Q ↦ compK Q`, equal on every sentence, for every target program, not only
  compiled ones); `cps_eq_dispatch` and `cps_no_slower_dispatch` (as for the state machine).

What this does **not** say: `cstep` is an abstract machine; the jumps are `return_call`s and the
dispatch a `br_table` only in the description, no Core 3.0 code is given.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.CPS

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify (Scheme Opt scheme dispatch_correct)
open Silmaril.Wasm.FX.Asyncify.SM (PCfg pstep pInit smScheme kernel_sm_correct kernel_sm_steps)
open Silmaril.Wasm.FX.Asyncify.Steps
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.Models.FXAsyncPC (fstep annP bodies fInit rootCode)

variable {V : Type}

/-- **CPS runs in lock step with the state machine.** -/
theorem step_toC (P : Prog (Ins V)) (f₀ : Nat) (test : V → Bool) (x : PCfg V) :
    cstep (compK P) f₀ test (toC (compK P) f₀ x) = (pstep P f₀ test x).map (toC (compK P) f₀) :=
  Silmaril.Proofs.Wasm.FX.Asyncify.CPS.step_toC test x

theorem toC_init (C : Prog (CIns V)) (f : Nat) (args : List (SV V)) :
    toC C f (pInit args) = cInit C f args := rfl

/-- The state machine and CPS have the same behaviours on every program. -/
theorem sm_cps_run_eq (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (pstep P f test) (pInit args) = beh (cstep (compK P) f test) (cInit (compK P) f args) :=
  (beh_eq_of_map (step_toC P f test) (pInit args)).symm

/-- **The kernel and its CPS compilation have the same behaviours.** -/
theorem kernel_cps_correct (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (sstep P test) (sInit f args) = beh (cstep (compK P) f test) (cInit (compK P) f args) :=
  (kernel_sm_correct P test f args).trans (sm_cps_run_eq P test f args)

/-- **… and the same step counts.** -/
theorem kernel_cps_steps (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    SameSteps (sstep P test) (cstep (compK P) f test) (sInit f args) (cInit (compK P) f args) :=
  let h := sameSteps_of_map (step_toC P f test) (pInit args)
  ⟨(kernel_sm_steps P test f args).1.trans h.2, h.1.trans (kernel_sm_steps P test f args).2⟩

/-- **The CPS instance of the asyncify family.** -/
def cpsScheme (V : Type) : Scheme V where
  TP := Prog (CIns V)
  compile := compK
  run := fun C test f args => beh (cstep C f test) (cInit C f args)
  dom := fun _ => True

theorem cps_correct : (cpsScheme V).Correct :=
  fun P _ test f args => (kernel_cps_correct P test f args).symm

/-- The CPS instance is a comorphism (equal on every sentence). -/
def cps_comorphism : Transition (Silmaril.Wasm.FX.Asyncify.srcChart (cpsScheme V).dom)
    (cpsScheme V).tgtChart :=
  (cpsScheme V).comorphism cps_correct

/-- **From the state machine to CPS**: a comorphism of target charts, equal on every sentence. -/
def sm_vs_cps : Transition (smScheme V).tgtChart (cpsScheme V).tgtChart :=
  BTrans.ofEq (fun q => (compK q.1, q.2)) id (fun _ _ => trivial)
    (fun q _ c => (sm_cps_run_eq q.1 q.2 c.1 c.2).symm)

/-- CPS and stack unwinding with dispatch agree on the dispatch instance's fragment. -/
theorem cps_eq_dispatch (o : Opt) (P : Prog (Ins V)) (hP : o.Dom P) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    (cpsScheme V).run ((cpsScheme V).compile P) test f args =
      (scheme V .unwindDispatch o).run ((scheme V .unwindDispatch o).compile P) test f args :=
  (cps_correct P trivial test f args).trans (dispatch_correct o P hP test f args).symm

/-- CPS is never slower than whole-program unwinding with dispatch. -/
theorem cps_no_slower_dispatch (P : Prog (Ins V)) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    NoSlower (cstep (compK P) f test) (fstep (annP (compP P)) (bodies (compP P) (rootCode f)) test)
      (cInit (compK P) f args) (fInit f args) :=
  (kernel_cps_steps P test f args).2.trans (kernel_no_slower_dispatch P test f args)

open Silmaril.Proofs.Wasm.Models.FXAsync (fwdP natTest) in
/-- The forwarding generator returns `[3]` after 20 CPS steps. -/
theorem fwd_cps : runN (cstep (compK fwdP) 2 natTest) 20 (cInit (compK fwdP) 2 []) =
    .stop (.done [.val 3]) := rfl

/-- info: 'Silmaril.Wasm.FX.Asyncify.CPS.cps_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cps_correct

/-- info: 'Silmaril.Wasm.FX.Asyncify.CPS.cps_no_slower_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cps_no_slower_dispatch

end Silmaril.Wasm.FX.Asyncify.CPS
