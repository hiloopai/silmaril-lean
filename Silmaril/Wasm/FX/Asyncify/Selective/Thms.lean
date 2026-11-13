module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Selective.Sim
public import Silmaril.Proofs.Wasm.FX.Asyncify.Selective.Example
public import Silmaril.Wasm.FX.Asyncify.RelSim.Thms
public import Silmaril.Proofs.Wasm.FX.Asyncify.Selective.Family
public import Silmaril.Wasm.Models.FXAsync.Thms
public import Silmaril.Wasm.FX.Asyncify.Shadow.Thms

/-!
# Selective instrumentation: results

The header of `Defs`: `opt S` drops the call-site check after calls of functions in `S`,
`optP`/`compSel` apply it to a function table, `SafeProg S Q` certifies that no function in `S`
can start or propagate an unwind, and `analyze Q n` computes a certified set.

* **`selective_sim`**: under `SafeProg S Q`, the optimized machine `tstep (optP S Q)` is
  simulated by the instrumented `tstep Q` (one step for one, two for a return to a caller that
  waits on a function in `S`), for the relation `SR S`.
* **`selective_correct`**: so a frame running `opt S false c` and one running `c` have the same
  behaviours, for every target program `Q` (not only compiled kernel programs).
* **`kernel_selective_correct`**: composed with `FXAsync.lower_correct_init`, the handler kernel
  `sstep P` and the selectively instrumented lowering `compSel S P` have the same behaviours from
  a call of `f`, under `SafeProg S (compP P)`;
* **`kernel_analyze_correct`**: the same with the computed set `analyze (compP P) n`, with no
  hypothesis.
* `twice_beh`: the example of `Selective.Example` (a generator calling a pure helper twice)
  returns `[3]`, and nothing else, with all three of its checks removed.

**In the asyncify family** (`Silmaril.Wasm.FX.Asyncify.scheme`):

* **`compSel_eq`**: the peephole on compiled code is the family's source-level selective
  compilation for the complement set: `compSel S P = compPO (.selective (!S ·)) P`.
* **`sound_of_safe`**, `analyze_sound`: a certificate is a sound analysis of the family
  (`Sound (!S ·) P`), so the computed analysis puts every program in the fragment of the
  selective instance: **`unwind_analyze`**, `dispatch_analyze` and **`shadow_analyze`** are the
  three strategies with the computed analysis, with no hypothesis.
* The two derivations agree: `kernel_analyze_correct` (this module's simulation, whose initial
  frame is optimized too) and `unwind_analyze` (the family's simulation, whose initial frame
  keeps its check) both state that the kernel and `compSel (analyze …) P` have the same
  behaviours.

What this does **not** say: completeness of the analysis and step bounds are proved elsewhere:
`Silmaril.Wasm.FX.Asyncify.Analysis` (the check never fails, and the analysis is the greatest
certificate on the functions `< n`) and `Silmaril.Wasm.FX.Asyncify.Steps` (selective instrumentation
is never slower); here fewer steps are shown on the example (`twice_tgt_slower`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Selective

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.RelSim
open Silmaril.Proofs.Wasm.FX.Asyncify.Selective (SR)
open Silmaril.Wasm.FX.Asyncify.Shadow (mstep)

variable {V : Type}

/-- **The optimized machine is simulated by the instrumented one.** -/
theorem selective_sim {S : Nat → Bool} {Q : Prog (TIns V)} (hQ : SafeProg S Q)
    (test : V → Bool) : RSim (SR S) (tstep (optP S Q) test) (tstep Q test) :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Selective.sim hQ

/-- **Selective instrumentation preserves behaviours.** -/
theorem selective_correct {S : Nat → Bool} {Q : Prog (TIns V)} (hQ : SafeProg S Q)
    (test : V → Bool) (c : List (TIns V)) (ops : List (SV V)) :
    beh (tstep (optP S Q) test) ⟨[], .normal, [⟨opt S false c, ops⟩]⟩ =
      beh (tstep Q test) ⟨[], .normal, [⟨c, ops⟩]⟩ :=
  beh_eq_of_rsim (selective_sim hQ test) ⟨.nil, trivial, ⟨rfl, rfl⟩, .nil _⟩

/-- **The handler kernel and its selectively instrumented lowering.** -/
theorem kernel_selective_correct (P : Prog (Ins V)) (test : V → Bool) {S : Nat → Bool}
    (hS : SafeProg S (compP P)) (f : Nat) (args : List (SV V)) :
    beh (sstep P test) (sInit f args) = beh (tstep (compSel S P) test) (selInit S f args) := by
  rw [lower_correct_init]
  exact (selective_correct hS test _ args).symm

/-- **The same with the computed set**, with no hypothesis. -/
theorem kernel_analyze_correct (P : Prog (Ins V)) (test : V → Bool) (n f : Nat)
    (args : List (SV V)) :
    beh (sstep P test) (sInit f args) =
      beh (tstep (compSel (analyze (compP P) n) P) test) (selInit (analyze (compP P) n) f args) :=
  kernel_selective_correct P test
    (Silmaril.Proofs.Wasm.FX.Asyncify.Selective.analyze_safe (compP P) n) f args

open Silmaril.Proofs.Wasm.FX.Asyncify.Selective in
/-- The example returns `[3]`, and nothing else, with its checks removed. -/
theorem twice_beh :
    beh (tstep (compSel twiceS twiceP) twiceTest) (selInit twiceS 3 []) = {.done [.val 3]} := by
  have h : beh (tstep (compSel twiceS twiceP) twiceTest) (selInit twiceS 3 []) =
      beh (sstep twiceP twiceTest) (sInit 3 []) := (kernel_analyze_correct twiceP twiceTest 5 3 []).symm
  rw [h]
  exact beh_of_stop twice_src_run

/-! ## In the asyncify family -/

open Silmaril.Wasm.FX.Asyncify (Opt Sound compPO scheme srcRun unwind_correct dispatch_correct)

/-- **The peephole is the family's selective compilation**, for the complement set. -/
theorem compSel_eq (S : Nat → Bool) (P : Prog (Ins V)) :
    compSel S P = compPO (.selective fun f => !S f) P :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Selective.compSel_eq S P

/-- **A certificate is a sound analysis of the family.** -/
theorem sound_of_safe {S : Nat → Bool} {P : Prog (Ins V)} (h : SafeProg S (compP P)) :
    Sound (fun f => !S f) P :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Selective.sound_of_safe h

/-- The computed analysis is sound. -/
theorem analyze_sound (P : Prog (Ins V)) (n : Nat) :
    Sound (fun f => !analyze (compP P) n f) P :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Selective.analyze_sound P n

/-- The family's optimization of the computed analysis. -/
abbrev analyzed (P : Prog (Ins V)) (n : Nat) : Opt := .selective fun f => !analyze (compP P) n f

/-- **Stack unwinding with the computed analysis**, with no hypothesis. -/
theorem unwind_analyze (P : Prog (Ins V)) (n : Nat) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    beh (tstep (compSel (analyze (compP P) n) P) test) (tInit f args) = srcRun P test f args := by
  rw [compSel_eq]
  exact unwind_correct (analyzed P n) P (analyze_sound P n) test f args

/-- **`br_table` dispatch with the computed analysis**, with no hypothesis. -/
theorem dispatch_analyze (P : Prog (Ins V)) (n : Nat) :
    ∀ test f args, (scheme V .unwindDispatch (analyzed P n)).run
      ((scheme V .unwindDispatch (analyzed P n)).compile P) test f args = srcRun P test f args :=
  dispatch_correct (analyzed P n) P (analyze_sound P n)

/-- **The shadow stack with the computed analysis**, with no hypothesis. -/
theorem shadow_analyze (P : Prog (Ins V)) (n : Nat) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    beh (mstep (Silmaril.Wasm.Models.FXAsyncPC.annP (compSel (analyze (compP P) n) P))
        (Silmaril.Wasm.Models.FXAsyncPC.bodies (compSel (analyze (compP P) n) P)
          (Silmaril.Wasm.Models.FXAsyncPC.rootCode f)) test)
      (Silmaril.Wasm.FX.Asyncify.Shadow.mInit f args) = srcRun P test f args := by
  rw [compSel_eq]
  exact Silmaril.Wasm.FX.Asyncify.Shadow.shadow_correct (analyzed P n) P (analyze_sound P n) test f
    args

/-- info: 'Silmaril.Wasm.FX.Asyncify.Selective.shadow_analyze' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shadow_analyze

/-- info: 'Silmaril.Wasm.FX.Asyncify.Selective.kernel_analyze_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_analyze_correct

end Silmaril.Wasm.FX.Asyncify.Selective
