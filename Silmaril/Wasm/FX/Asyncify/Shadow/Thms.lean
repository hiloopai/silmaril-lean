module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Lock
public import Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Example
public import Silmaril.Wasm.FX.Asyncify.Thms

/-!
# The shadow-stack strategy: results

The header of `Defs`: `mstep`, asyncify with every saved frame encoded in one linear memory
(operands, then a trailer of function, resume index and operand count), a table of buffer handles
for the continuations, and rewinding that reads the memory backwards from the end of a buffer.

* **`shadow_lock`**, `shadow_beh`: `fstep` (records in a heap) and `mstep` (records in memory) run
  in lock step from `MR`-related configurations (equal stacks and registers; each heap entry is a
  table entry whose buffer encodes its records; the records being written are the end of the
  memory, those being read end at `top`), so they have the same behaviours.
* `init_related`: the initial configurations of a call are related.
* **`kernel_shadow_correct`**: composed with `FXAsyncPC.kernel_pc_correct`, a call in the handler
  kernel and the same call on the shadow-stack machine have the same behaviours, for every
  program and branch test.

**The instance.** `shadowScheme o`: the shadow-stack strategy as a member of the asyncify family
`Silmaril.Wasm.FX.Asyncify.scheme` (same compiler `compPO o` and fragment `o.Dom` as the other
strategies, target behaviours on `mstep`).

* **`shadow_run_eq`**: the shadow-stack and the dispatch strategy have the same target behaviours
  on every compiled program, so **`shadow_correct`**: the instance is correct for every
  optimization on its fragment, and `shadow_comorphism` is its comorphism of behaviour charts.
  `shadow_vs_dispatch`: a comorphism between the two target charts (equal on every sentence).
* `fwd_shadow`: the forwarding generator of `FXAsync` returns `[3]`, and nothing else, on `mstep`.

What this does **not** say: `mstep` is an abstract machine, its memory a list of cells, not
bytes of a Core 3.0 memory (no address arithmetic, no widths, no bounds, no reuse of dead
buffers); see `docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Shadow

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC
open Silmaril.Wasm.FX.Asyncify.RelSim
open Silmaril.Wasm.Atlas
open Silmaril.Proofs.Wasm.FX.Asyncify.Shadow (MR)

variable {V : Type}

/-- **The shadow-stack machine runs in lock step with `fstep`.** -/
theorem shadow_lock (P : Prog (AIns V)) (B : Nat → Option (List (TIns V))) (test : V → Bool) :
    LockStep MR (fstep P B test) (mstep P B test) :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.lock

/-- So related configurations have the same behaviours. -/
theorem shadow_beh (P : Prog (AIns V)) (B : Nat → Option (List (TIns V))) (test : V → Bool)
    {y : FCfg V} {z : MCfg V} (h : MR y z) : beh (fstep P B test) y = beh (mstep P B test) z :=
  beh_eq_of_lock (shadow_lock P B test) h

/-- The initial configurations of a call are related. -/
theorem init_related (f : Nat) (args : List (SV V)) : MR (fInit f args) (mInit f args) :=
  ⟨.nil, rfl, rfl, rfl, rfl, trivial⟩

/-- **The handler kernel and the shadow-stack machine have the same behaviours.** -/
theorem kernel_shadow_correct (P : Prog (Ins V)) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    beh (sstep P test) (sInit f args) =
      beh (mstep (annP (compP P)) (bodies (compP P) (rootCode f)) test) (mInit f args) := by
  rw [Silmaril.Wasm.Models.FXAsyncPC.kernel_pc_correct]
  exact shadow_beh _ _ test (init_related f args)

/-! ## The instance of the asyncify family -/

/-- **The shadow-stack strategy**, for an optimization `o`. -/
def shadowScheme (V : Type) (o : Opt) : Scheme V where
  TP := Prog (TIns V)
  compile := compPO o
  run := fun Q test f args => beh (mstep (annP Q) (bodies Q (rootCode f)) test) (mInit f args)
  dom := o.Dom

/-- **The shadow-stack and dispatch strategies agree on every compiled program.** -/
theorem shadow_run_eq (o : Opt) (Q : Prog (TIns V)) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    (shadowScheme V o).run Q test f args = (scheme V .unwindDispatch o).run Q test f args :=
  (shadow_beh _ _ test (init_related f args)).symm

/-- **The shadow-stack strategy is correct for every optimization, on its fragment.** -/
theorem shadow_correct (o : Opt) : (shadowScheme V o).Correct :=
  fun P hP test f args =>
    (shadow_run_eq o _ test f args).trans (dispatch_correct o P hP test f args)

/-- Its comorphism of behaviour charts. -/
def shadow_comorphism (o : Opt) :
    Transition (srcChart (shadowScheme V o).dom) (shadowScheme V o).tgtChart :=
  (shadowScheme V o).comorphism (shadow_correct o)

/-- The dispatch and shadow-stack targets are related by a comorphism (equal on every
sentence). -/
def shadow_vs_dispatch (o : Opt) :
    Transition (scheme V .unwindDispatch o).tgtChart (shadowScheme V o).tgtChart :=
  BTrans.ofEq (fun q => q) id (fun _ _ => trivial)
    (fun q _ c => shadow_run_eq o q.1 q.2 c.1 c.2)

open Silmaril.Proofs.Wasm.Models.FXAsync (fwdP natTest) in
/-- The forwarding generator returns `[3]`, and nothing else, on the shadow-stack machine. -/
theorem fwd_shadow :
    beh (mstep (annP (compP fwdP)) (bodies (compP fwdP) (rootCode 2)) natTest) (mInit 2 []) =
      {.done [.val 3]} :=
  beh_of_stop Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.fwd_shadow_run

/-- info: 'Silmaril.Wasm.FX.Asyncify.Shadow.shadow_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shadow_correct

end Silmaril.Wasm.FX.Asyncify.Shadow
