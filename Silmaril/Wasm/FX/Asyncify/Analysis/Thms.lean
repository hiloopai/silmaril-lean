module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Analysis.Complete

/-!
# Completeness of the suspension analysis: results

The analysis `Selective.analyze Q n` of selective instrumentation (`Silmaril.Wasm.FX.Asyncify.
Selective`: the functions `< n` that cannot reach a suspension) was sound by construction: it
runs `n + 1` rounds of refinement, then checks the result and falls back to the empty set when
the check fails. Here:

* **`check_candidate`**: the check never fails: after `n + 1` rounds the decreasing iteration on
  the `n` functions is stable (`X_stable`: each strict round removes a function);
  `analyze_eq`: so `analyze Q n` is the candidate itself;
* **`analyze_greatest`**: every post-fixpoint of the refinement on the functions `< n` (each of
  its functions is defined and calls only functions of the set) is contained in `analyze Q n`;
* **`analyze_complete`**: equivalently, every certificate `SafeProg T Q` with `T ⊆ {f | f < n}`
  is contained in `analyze Q n`: the analysis removes the checks after every call that any
  certificate allows to remove, so it is the **greatest** certificate on the functions `< n`.

Not covered: functions `≥ n` are never in the analysis (`n` is a bound on the function table
chosen by the caller), and the analysis is a call-graph analysis: a function that calls a
suspending function only on a branch that is never taken stays out of it.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Analysis

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.Selective
open Silmaril.Proofs.Wasm.FX.Asyncify.Analysis (Sub)

variable {V : Type}

/-- **The check of the analysis always passes.** -/
theorem check_candidate (Q : Prog (TIns V)) (n : Nat) : check Q n (candidate Q n) = true :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Analysis.check_candidate Q n

theorem analyze_eq (Q : Prog (TIns V)) (n : Nat) : analyze Q n = candidate Q n :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Analysis.analyze_eq Q n

/-- **The analysis contains every post-fixpoint of the refinement.** -/
theorem analyze_greatest (Q : Prog (TIns V)) (n : Nat) {T : Nat → Bool}
    (hT : ∀ f, T f = true → f < n ∧ okF Q T f = true) : ∀ f, T f = true → analyze Q n f = true :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Analysis.analyze_greatest Q n hT

/-- **The analysis is the greatest certificate on the functions `< n`.** -/
theorem analyze_complete (Q : Prog (TIns V)) (n : Nat) {T : Nat → Bool} (hT : SafeProg T Q)
    (hn : ∀ f, T f = true → f < n) : ∀ f, T f = true → analyze Q n f = true :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Analysis.analyze_complete Q n hT hn

/-- info: 'Silmaril.Wasm.FX.Asyncify.Analysis.analyze_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyze_complete

end Silmaril.Wasm.FX.Asyncify.Analysis
