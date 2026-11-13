module

public import Silmaril.Wasm.Spec.Attest.Litmus.Defs
public import Silmaril.Wasm.Spec.Attest.Core.Thms
public import Silmaril.Proofs.Wasm.Spec.Attest.Runs

/-!
# Litmus tests for "may attest"

Every profile `P`; every statement is a theorem about Core 3.0 game semantics.

**Leaves.**

* `T_play`: an explicit play of `ttMod`: `fire` asked, then `attest` asked (a Core run of
  `call 0` to the host-call redex); `T_attests`.
* `ffMod_neverCall`: `wasm_check` proves `neverCall attest` for `ffMod` (kernel evaluation of the
  verifier, then `check_sound`); `F_neverCall` is the same for the leaf `F`.
* `ttMod_refuted`: the verifier refutes `neverCall` for `ttMod` (its own counterexample search);
  `gateMod_unknown`: the verifier cannot settle the gate, which calls `attest` from reachable code
  but only once both flags are set (the gate's safety is proved in the program logic instead,
  `Core.gate_safe`).

**Encodings** (through `mayAttest_enc`; the false cases reduce to `F_neverCall`, i.e. to the
verifier, the true ones to `T_play` and the gate's liveness play):

| test | formula | valuation | may attest |
| --- | --- | --- | --- |
| `or_TF` | `x0 ∨ x1` | `T F` | yes |
| `or_FF` | `x0 ∨ x1` | `F F` | no |
| `and_TT` | `x0 ∧ x1` | `T T` | yes |
| `and_TF`, `and_FT` | `x0 ∧ x1` | `T F`, `F T` | no |
| `andAnd_TTT` | `(x0 ∧ x1) ∧ x2` | `T T T` | yes (the left conjunct is a link, trap propagation through it) |
| `andAnd_TTF` | `(x0 ∧ x1) ∧ x2` | `T T F` | no |
| `orAnd_FTT` | `x0 ∨ (x1 ∧ x2)` | `F T T` | yes |
| `orAnd_FTF` | `x0 ∨ (x1 ∧ x2)` | `F T F` | no |
| `andOr_TFT` | `x0 ∧ (x1 ∨ x2)` | `T F T` | yes |
| `tt_ff` | `⊤`, `⊥` | — | yes, no |

`entails_and_or`: `x0 ∧ x1 ⊨ x0 ∨ x1` for attesting modules, borrowed from positive logic.

New (no source).
-/

public section

namespace Silmaril.Wasm.Spec.Attest.Litmus

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify Silmaril.Wasm.Spec.Attest
  Silmaril.Wasm.Spec.Attest.Core Silmaril.Logic.Institution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.Execution.Core (Val)

variable (P : Profile)

/-- The module of `φ` under the valuation `a b c`, at profile `P`. -/
noncomputable abbrev M (a b c : CoreLeaf) (φ : PForm (Fin 3)) : Strategy Att (enc (coreKit P)
    (fun x => (val a b c x).toAMod P) φ).F :=
  (enc (coreKit P) (fun x => (val a b c x).toAMod P) φ).σ

/-! ### Leaves -/

/-- **An explicit play of `true`**: `fire` is asked and `attest` is called. -/
theorem T_play : ∃ f e, [.inr (.ask f), .inl (.ask e)] ∈ T.prog.inst.strategy P T.prog.store :=
  Silmaril.Proofs.Wasm.Spec.Attest.tt_play P

/-- `true` attests. -/
theorem T_attests : Attests P T := tt_attests P

/-- **`false` never attests, by `wasm_check`.** -/
theorem ffMod_neverCall :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf ffMod)
      ⟨0, by decide +kernel⟩ := by
  wasm_check

/-- The leaf `F` never attests (the verifier, through `check_sound`). -/
theorem F_neverCall : ¬ Attests P F := fun h => h (ff_neverCall P)

/-- The verifier refutes "`true` never calls `attest`". -/
theorem ttMod_refuted : (check ttMod (.neverCall 0)).verdict = .refuted := by decide +kernel

/-- The verifier cannot settle the gate. -/
theorem gateMod_unknown : (check gateMod (.neverCall 0)).verdict = .unknown := by decide +kernel

/-! ### Encodings -/

theorem or_TF : MayCall (M P T F F orF) := (mayAttest_enc P _ orF).2 (.inl (T_attests P))

theorem or_FF : ¬ MayCall (M P F F F orF) := fun h =>
  ((mayAttest_enc P _ orF).1 h).elim (F_neverCall P) (F_neverCall P)

theorem and_TT : MayCall (M P T T F andF) :=
  (mayAttest_enc P _ andF).2 ⟨T_attests P, T_attests P⟩

theorem and_TF : ¬ MayCall (M P T F F andF) := fun h => F_neverCall P ((mayAttest_enc P _ andF).1 h).2

theorem and_FT : ¬ MayCall (M P F T F andF) := fun h => F_neverCall P ((mayAttest_enc P _ andF).1 h).1

theorem andAnd_TTT : MayCall (M P T T T andAndF) :=
  (mayAttest_enc P _ andAndF).2 ⟨⟨T_attests P, T_attests P⟩, T_attests P⟩

theorem andAnd_TTF : ¬ MayCall (M P T T F andAndF) := fun h =>
  F_neverCall P ((mayAttest_enc P _ andAndF).1 h).2

theorem orAnd_FTT : MayCall (M P F T T orAndF) :=
  (mayAttest_enc P _ orAndF).2 (.inr ⟨T_attests P, T_attests P⟩)

theorem orAnd_FTF : ¬ MayCall (M P F T F orAndF) := fun h =>
  ((mayAttest_enc P _ orAndF).1 h).elim (F_neverCall P) fun h' => F_neverCall P h'.2

theorem andOr_TFT : MayCall (M P T F T andOrF) :=
  (mayAttest_enc P _ andOrF).2 ⟨T_attests P, .inr (T_attests P)⟩

theorem tt_ff : MayCall (M P F F F .tt) ∧ ¬ MayCall (M P T T T .ff) :=
  ⟨(mayAttest_enc P _ .tt).2 trivial, fun h => (mayAttest_enc P _ .ff).1 h⟩

/-- **Borrowed consequence**: for attesting modules, `x0 ∧ x1 ⊨ x0 ∨ x1`. -/
theorem entails_and_or : (attRoom (coreKit P) trapAns (Fin 3)).Entails {andF} orF :=
  (core_entails_iff P {andF} orF).1 fun _ hv => .inl (hv andF rfl).1

end Silmaril.Wasm.Spec.Attest.Litmus
