module

public import Silmaril.Proofs.Wasm.Models.FXAsyncPC.Sim
public import Silmaril.Wasm.Models.FXAsync.Thms

/-!
# First-order asyncify: results

The header of `Defs`: `fstep`, the asyncify machine of `Silmaril.Wasm.Models.FXAsync` with
first-order state. Saved frames are records of a function number, a resume index and operands;
the mode is a number in a register; rewinding dispatches on the resume index (`disp`, the
`br_table` prologue); `ann` numbers the resume points of the compiled code.

* **`pc_correct`**: for every target function table `Q`, root code `R` and configurations
  related by `RCfg (bodies Q R)`, `tstep Q` and `fstep (annP Q) (bodies Q R)` have the same
  behaviours. The two machines run in lock step (`lock_step`): one step each.
* **`kernel_pc_correct`**: composed with `FXAsync.lower_correct_init`, a call of `f` in the
  handler kernel `sstep P` and the same call in `fstep` on the compiled and annotated program
  `annP (compP P)` have the same behaviours (returned values, trap, divergence), for every
  function table and branch test, with no hypotheses.
* `fwd_beh_pc`: the forwarding generator of `FXAsync` returns `[3]` on `fstep`.

What this does **not** say: `fstep` is still an abstract machine. Its registers, record heap and
dispatch are the data a Core 3.0 implementation would keep in globals and GC structs (or linear
memory), but no Core 3.0 module is given and Core `Step` is not used. See "Stretch, fxcps2" in
`docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAsyncPC

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Proofs.Wasm.Models.FXAsyncPC (RCfg)

variable {V : Type}

/-- **The first-order asyncify machine runs in lock step with `tstep`.** -/
theorem pc_correct (Q : Prog (TIns V)) (R : List (TIns V)) (test : V → Bool) (x : TCfg V)
    (y : FCfg V) (hxy : RCfg (bodies Q R) x y) :
    beh (tstep Q test) x = beh (fstep (annP Q) (bodies Q R) test) y :=
  Silmaril.Proofs.Wasm.Models.FXAsyncPC.beh_eq_pc test hxy

/-- The initial configurations of a call of `f` are related. -/
theorem init_related (Q : Prog (TIns V)) (f : Nat) (args : List (SV V)) :
    RCfg (bodies Q (rootCode f)) (tInit f args) (fInit f args) :=
  Silmaril.Proofs.Wasm.Models.FXAsyncPC.rcfg_init f args

/-- **The handler kernel and the first-order asyncify machine have the same behaviours.** -/
theorem kernel_pc_correct (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (sstep P test) (sInit f args) =
      beh (fstep (annP (compP P)) (bodies (compP P) (rootCode f)) test) (fInit f args) := by
  rw [lower_correct_init]
  exact pc_correct _ _ test _ _ (init_related _ f args)

/-- The forwarding generator of `FXAsync` returns `[3]`, and nothing else, on `fstep`. -/
theorem fwd_beh_pc :
    beh (fstep (annP (compP Silmaril.Proofs.Wasm.Models.FXAsync.fwdP))
      (bodies (compP Silmaril.Proofs.Wasm.Models.FXAsync.fwdP) (rootCode 2))
      Silmaril.Proofs.Wasm.Models.FXAsync.natTest) (fInit 2 []) = {.done [.val 3]} := by
  rw [← kernel_pc_correct]
  exact fwd_beh

/-- info: 'Silmaril.Wasm.Models.FXAsyncPC.kernel_pc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_pc_correct

end Silmaril.Wasm.Models.FXAsyncPC
