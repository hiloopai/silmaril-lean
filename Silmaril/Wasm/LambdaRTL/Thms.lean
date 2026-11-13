module

public import Silmaril.Wasm.LambdaRTL.Defs
public import Silmaril.Wasm.SSA.Fragment.Thms
public import Silmaril.Wasm.SSA.Translate.Thms
import Silmaril.Proofs.Wasm.LambdaRTL.Run

/-!
# The loop-free Wasm fragment in λRTL: checked results

For a function `f` of the fragment whose body has no `loop` (`trFunc f = some R`), called with
arguments of its parameter types, and any λRTL store `σ` holding the initial locals
(`InitStore f args σ`, e.g. `initStore f args`):

* `trFunc_run_iff`: `f.Run args o ↔ R.evalObs model σ = obsOf o` for every call outcome `o`
  (a return with its value, or a trap);
* `trFunc_stuck_iff`: the fragment has no derivation for the call exactly when the λRTL run
  ends in `.error .stuck`;
* `trFunc_evalObs`: with fuel that suffices (`fuelSeq f.body ≤ n`), the λRTL observation is the
  fragment interpreter's result, mapped by `obsOpt`;
* `compileFunc_run_iff_evalObs`: the existing λSSA dialect translation `compileFunc` has the
  same outcomes as the λRTL translation (by transitivity through `FragFunc.Run`).

So the λRTL program has exactly the fragment's observable behaviours: returned values, traps and
stuckness. Divergence does not arise on loop-free code. Final locals are not observed (the Wasm
call outcome does not contain them); the final λRTL store holds them, but no theorem here
relates it to the fragment's final locals.

`run_of_evalObs` and `not_run_of_evalObs_stuck` turn a kernel evaluation of the λRTL side
into a fragment run (or its absence); the examples below use them.

Out of scope (see `docs/projects/wasm-wasi.md`): `loop` (λRTL's recursive `where` and an Elgot monad
with divergence), memory, globals, calls, tables, `br_table`, floats; the relation to Wasm Core
3.0 goes through the fragment (`Silmaril.Wasm.SSA.CoreCert`).
-/

@[expose] public section

namespace Silmaril.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut)

theorem trFunc_isSome_iff (f : FragFunc) : (trFunc f).isSome = loopFreeL f.body := by
  unfold trFunc
  split <;> simp_all

theorem initStore_spec (f : FragFunc) (args : List WVal) :
    InitStore f args (initStore f args) :=
  Silmaril.Proofs.Wasm.LambdaRTL.initStore_spec f args

/-- **Exact simulation of terminating runs and traps.** -/
theorem trFunc_run_iff {f : FragFunc} {R : WRegion} (hf : trFunc f = some R) {args : List WVal}
    (hargs : args.map WVal.type = f.params) {σ : Store} (hσ : InitStore f args σ) (o : FOut) :
    f.Run args o ↔ R.evalObs model σ = obsOf o :=
  Silmaril.Proofs.Wasm.LambdaRTL.trFunc_run_iff hf hargs hσ o

/-- **Exact simulation of stuckness.** -/
theorem trFunc_stuck_iff {f : FragFunc} {R : WRegion} (hf : trFunc f = some R)
    {args : List WVal} (hargs : args.map WVal.type = f.params) {σ : Store}
    (hσ : InitStore f args σ) :
    (¬ ∃ o, f.Run args o) ↔ R.evalObs model σ = .error .stuck :=
  Silmaril.Proofs.Wasm.LambdaRTL.trFunc_stuck_iff hf hargs hσ

/-- The λRTL observation is the fragment interpreter's, at fuel that suffices or on which the
interpreter returns. -/
theorem trFunc_evalObs {f : FragFunc} {R : WRegion} (hf : trFunc f = some R) {args : List WVal}
    (hargs : args.map WVal.type = f.params) {σ : Store} (hσ : InitStore f args σ) {n : Nat}
    (hn : fuelSeq f.body ≤ n ∨ (f.eval n args).isSome = true) :
    R.evalObs model σ = obsOpt (f.eval n args) :=
  Silmaril.Proofs.Wasm.LambdaRTL.trFunc_evalObs hf hargs hσ hn

/-- On loop-free functions the λRTL translation and the λSSA dialect translation
`Silmaril.Wasm.SSA.compileFunc` have the same outcomes (transitivity through `FragFunc.Run`). -/
theorem compileFunc_run_iff_evalObs {f : FragFunc} {R : WRegion} (hf : trFunc f = some R)
    {args : List WVal} (hargs : args.map WVal.type = f.params) {σ : Store}
    (hσ : InitStore f args σ) (o : FOut) :
    (Silmaril.Wasm.SSA.compileFunc f).Run args o ↔ R.evalObs model σ = obsOf o :=
  Silmaril.Wasm.SSA.compileFunc_iff.trans (trFunc_run_iff hf hargs hσ o)

/-- A fragment run, certified by evaluating the λRTL translation. -/
theorem run_of_evalObs {f : FragFunc} {args : List WVal} {o : FOut}
    (hargs : args.map WVal.type = f.params)
    (h : (trFunc f).map (fun R => R.evalObs model (initStore f args)) = some (obsOf o)) :
    f.Run args o := by
  cases hf : trFunc f with
  | none => rw [hf] at h; cases h
  | some R =>
    rw [hf] at h
    exact (trFunc_run_iff hf hargs (initStore_spec f args) o).2 (Option.some.inj h)

/-- The absence of a fragment run, certified by evaluating the λRTL translation. -/
theorem not_run_of_evalObs_stuck {f : FragFunc} {args : List WVal}
    (hargs : args.map WVal.type = f.params)
    (h : (trFunc f).map (fun R => R.evalObs model (initStore f args)) = some (.error .stuck)) :
    ¬ ∃ o, f.Run args o := by
  cases hf : trFunc f with
  | none => rw [hf] at h; cases h
  | some R =>
    rw [hf] at h
    exact (trFunc_stuck_iff hf hargs (initStore_spec f args)).2 (Option.some.inj h)

/-! ## Examples (kernel evaluation; no native evaluation) -/

section Examples

open Silmaril.Wasm.SSA (exampleInc exampleDiv exampleSum)

/-- `x + 1` on `i32`: the λRTL translation returns `42` on `41`. -/
example : exampleInc.Run [.i32 41] (.ret (some (.i32 42))) := run_of_evalObs (by decide) rfl

/-- `10 / x` traps on `0` and returns `3` on `3`, in the fragment and in λRTL. -/
example : exampleDiv.Run [.i32 0] .trap := run_of_evalObs (by decide) rfl

example : exampleDiv.Run [.i32 3] (.ret (some (.i32 3))) := run_of_evalObs (by decide) rfl

/-- A body with a `loop` is not translated. -/
example : trFunc exampleSum = none := rfl

/-- `f(x) = if x = 0 then 7 else x + 1`, by a typed `block` left by `br_if` with a value. -/
def exampleBrIf : FragFunc where
  params := [.i32]
  locals := []
  result := some .i32
  body := [.block (some .i32) [
    .brIf 0 [.op (.const (.i32 7)) [], .op (.un (.test .i32)) [.localGet 0]],
    .op (.bin (.int .i32 .add)) [.localGet 0, .op (.const (.i32 1)) []]]]

example : exampleBrIf.Run [.i32 0] (.ret (some (.i32 7))) := run_of_evalObs (by decide) rfl

example : exampleBrIf.Run [.i32 5] (.ret (some (.i32 6))) := run_of_evalObs (by decide) rfl

/-- `f(x) = min(2x, 10)` on `i64` through a local, an untyped `if` and `return`. -/
def exampleClamp : FragFunc where
  params := [.i64]
  locals := [.i64]
  result := some .i64
  body := [
    .localSet 1 (.op (.bin (.int .i64 .mul)) [.localGet 0, .op (.const (.i64 2)) []]),
    .if_ none (.op (.bin (.rel .i64 (.gt .signed))) [.localGet 1, .op (.const (.i64 10)) []])
      [.return_ [.op (.const (.i64 10)) []]] [],
    .localGet 1]

example : exampleClamp.Run [.i64 3] (.ret (some (.i64 6))) := run_of_evalObs (by decide) rfl

example : exampleClamp.Run [.i64 7] (.ret (some (.i64 10))) := run_of_evalObs (by decide) rfl

/-- An `i64` used as an `if` condition: no fragment derivation, and λRTL is stuck. -/
def exampleStuck : FragFunc where
  params := [.i64]
  locals := []
  result := none
  body := [.if_ none (.localGet 0) [] []]

example : ¬ ∃ o, exampleStuck.Run [.i64 1] o := not_run_of_evalObs_stuck (by decide) rfl

end Examples

end Silmaril.Wasm.LambdaRTL
