module

public import Silmaril.Wasm.SpecTec.Meta.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Meta.Import
public import Silmaril.Proofs.Wasm.SpecTec.Meta.Eval
public import Silmaril.Proofs.Wasm.SpecTec.Meta.Original
public import Silmaril.Proofs.Wasm.SpecTec.Meta.Triangle
public import Silmaril.Proofs.Wasm.SpecTec.Meta.Calls

/-!
# SpecTec's semantics of its IL, read by ours: results

Proofs in `Silmaril.Proofs.Wasm.SpecTec.Meta.*`; the comparison and the findings are in
`docs/projects/wasm-extras.md`.

* **Import** (`Import`): the generated script is the elaboration-time import
  (`generated_metail_eq`), the fixed one is the errata splice (`generated_metail_fixed_eq`), and
  the verified reader reads the printed stream as the script (`importAstText?_metailText`). The
  file-to-term link and the validator runs are compiled checks.
* **Agreement on a fragment** (fixed script, `envF`): for a closed Boolean/`nat`/`int`
  expression `e` built from literals with `UnE`, `BinE` and `CmpE`, their `Reduce_exp`, read by
  `Sim.DDerives`, reaches the encoding of `v` exactly when our strict evaluation gives `v`
  (`reduce_iff_strict`), and this is our `Sem.evalExp` whenever the strict value exists
  (`reduce_iff_evalExp`). The only gaps are `pow` on two `int`s (a SpecTec toolchain
  inconsistency, `FExp.NoIntPow`) and eval.ml's short-circuit (`shortCircuit_disagrees`).
* **The original script disagrees** (`Original`): `original_mod` (`6 \ 3 ⟶* 2`),
  `original_one_eq_two` (`1 = 1 + 1 ⟶* true`), `original_ne_stuck` (`k =/= 0` never reaches
  `true`), `original_modPow_stuck` (`(a + b) \ 2^N` reaches no value).
* **A third reading of wasm-3.0** (`Triangle`): `triangle_iadd` (`i32.add`: our `$iadd_`,
  Silmaril's `intBinOp .i32 .add`, and their fixed reduction of the clause's arithmetic agree;
  their original one is stuck), `triangle_brIf` (`br_if-true`'s premise), `triangle_slice` (the
  slice bound of a load at the end of memory: theirs is eval.ml's strict one).
* **No call reduces** (`Calls`): `Match_args` derives nothing in either script (`not_matchArgs`:
  its premise iterates over no domain), so every rule with a `Match_args` premise is dead
  (`dead_of_matchArgs_prem`), `Step_exp/CALL-apply` and `Expand_typ/step` among them
  (`callApply_matchArgs`).
-/

public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (TypedV)

/-- **Their reduction and our strict evaluation agree** on the fragment, in the fixed script, for
every store `S` of their type `S`. -/
theorem reduce_iff_strict {S : Value} (hS : TypedV envF (.varT "S" []) S) {e : FExp}
    (hn : e.NoIntPow) (v : Value) : MReduce envF S e.enc (encVal v) ↔ e.strict = some v :=
  ⟨reduceF_sound, reduceF_complete hS hn⟩

/-- **Their reduction and our evaluator agree** on the fragment, in the fixed script, wherever
strict evaluation is defined (always, unless `/\`, `\/` or `==>` short-circuit past an
undefined operand). -/
theorem reduce_iff_evalExp {S : Value} (hS : TypedV envF (.varT "S" []) S) {e : FExp}
    (hn : e.NoIntPow) (hd : e.strict.isSome) (env : Env) (ρ : VarEnv) (v : Value) :
    MReduce envF S e.enc (encVal v) ↔ EvalExp env ρ e.toExp v :=
  ⟨fun h => evalExp_of_strict (reduceF_sound h),
    fun h => reduceF_complete hS hn (strict_of_evalExp h hd)⟩

/-- Soundness needs no side condition: a reduction to a value is our evaluator's value. -/
theorem evalExp_of_reduce {S : Value} {e : FExp} {v : Value} (h : MReduce envF S e.enc (encVal v))
    (env : Env) (ρ : VarEnv) : EvalExp env ρ e.toExp v :=
  evalExp_of_strict (reduceF_sound h)

/-- The empty store is a store, so the agreement holds at `emptyS`. -/
theorem reduce_iff_strict_emptyS {e : FExp} (hn : e.NoIntPow) (v : Value) :
    MReduce envF emptyS e.enc (encVal v) ↔ e.strict = some v :=
  reduce_iff_strict typedV_emptyS hn v

/-- **The one design difference left on the fragment**: eval.ml short-circuits `false /\ e`, so
our evaluator gives `false /\ (1 / 0 = 1)` the value `false`; their rules need both operands to
be values, and `1 / 0` is not one. -/
theorem shortCircuit_disagrees (S : Value) {env : Env} {ρ : VarEnv} :
    EvalExp env ρ shortCircuitExp.toExp (.bool false) ∧
      ¬ MReduce envF S shortCircuitExp.enc (encVal (.bool false)) :=
  ⟨shortCircuit_evalExp, fun h => by
    have := reduceF_sound h
    rw [shortCircuit_strict] at this
    cases this⟩

end Silmaril.Wasm.SpecTec.Meta
