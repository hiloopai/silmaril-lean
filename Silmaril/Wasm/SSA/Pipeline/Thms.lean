module

public import Silmaril.Wasm.SSA.Pipeline.Defs
public import Silmaril.Wasm.SSA.Translate.Thms
public import Silmaril.Wasm.SSA.Passes.Thms
public import Silmaril.Wasm.SSA.OutOfSSA.Thms
public import Silmaril.Wasm.SSA.Fragment.Thms
public import Silmaril.Wasm.SSA.Bridge.Thms
import Silmaril.Proofs.Wasm.SSA.Pipeline.Bridge

/-!
# The SSA optimiser: correctness

`fragment → SSA → optimise → fragment` is an equivalence on terminating
call outcomes (return value or trap), `optimize?_equiv`; hence the source
diverges or is stuck on an input exactly when the output is:

* `optimizeSSA` is the pass pipeline `ssaPipeline` (a monoid product of
  verified passes), `optimizeSSA_sound`;
* `optimize?_sound` composes `compileFunc_sound`, the passes and
  `decompileFunc_sound`; `optimizePass` packages `optimize` (with fallback) as
  a verified `Pass` of the fragment's contract, and `optimize_unique` uses
  determinism: a terminating source has exactly its own outcome after
  optimisation;
* `optimizeFunc?_equiv` lifts this to silmaril `BFunc`s: when the optimiser
  returns a function, it is recognised again with the same type and has
  exactly the original's terminating outcomes.

Runs are on arguments of the parameter types. Validity of the emitted Wasm is
guaranteed separately by the validator guard in `Checked`; the fragment
semantics is related to silmaril's native interpreter only for arity-checked
functions (`native_adequate` in `Native`), and not to Core execution.

The `example`s at the end are checked by `decide`.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Compile.PassAPI

theorem optimizeSSA_eq (f : SFunc) : optimizeSSA f = ssaPipeline.run f := rfl

/-- The SSA pipeline preserves terminating outcomes. -/
theorem optimizeSSA_sound {f : SFunc} {args : List WVal} {o : FOut} (h : f.Run args o) :
    (optimizeSSA f).Run args o :=
  ssaPipeline.sound trivial args o h

/-- The optimiser, when out-of-SSA succeeds, preserves terminating outcomes. -/
theorem optimize?_sound {f g : FragFunc} (hg : optimize? f = some g) {args : List WVal} {o : FOut}
    (h : f.Run args o) : g.Run args o :=
  decompileFunc_sound hg (optimizeSSA_sound (compileFunc_sound h))

/-- `optimize?` is the composite of the verified translation, the pass pipeline and
out-of-SSA. -/
theorem optimize?_eq (f : FragFunc) :
    optimize? f = decompileFunc (ssaPipeline.run (toSSA.run f)) := rfl

/-- The SSA pipeline is an equivalence on terminating outcomes. -/
theorem optimizeSSA_iff {f : SFunc} {args : List WVal} {o : FOut} :
    (optimizeSSA f).Run args o ↔ f.Run args o :=
  ssaPipeline_iff

/-- **The optimiser is an equivalence**: when out-of-SSA succeeds, source and
output have the same terminating outcomes on every argument list (so one
diverges or is stuck exactly when the other is). -/
theorem optimize?_equiv {f g : FragFunc} (hg : optimize? f = some g) (args : List WVal)
    (o : FOut) : f.Run args o ↔ g.Run args o :=
  ⟨optimize?_sound hg, fun h =>
    compileFunc_complete (optimizeSSA_iff.mp (decompileFunc_complete hg h))⟩

/-- The optimiser with fallback preserves terminating outcomes. -/
theorem optimize_sound {f : FragFunc} {args : List WVal} {o : FOut} (h : f.Run args o) :
    (optimize f).Run args o := by
  unfold optimize
  cases hg : optimize? f with
  | none => exact h
  | some g => exact optimize?_sound hg h

/-- With determinism: the optimised function has exactly the source's outcome. -/
theorem optimize_unique {f : FragFunc} {args : List WVal} {o : FOut} (h : f.Run args o)
    (o' : FOut) : (optimize f).Run args o' ↔ o' = o :=
  ⟨fun h' => FragFunc.Run.det h' (optimize_sound h), fun e => e ▸ optimize_sound h⟩

/-- The optimiser with fallback is an equivalence. -/
theorem optimize_equiv (f : FragFunc) (args : List WVal) (o : FOut) :
    f.Run args o ↔ (optimize f).Run args o := by
  unfold optimize
  cases hg : optimize? f with
  | none => exact Iff.rfl
  | some g => exact optimize?_equiv hg args o

/-- The optimiser as a verified pass on the fragment. -/
def optimizePass : Pass fragIR.contract where
  run := optimize
  inv_run _ := trivial
  sound _ _ _ h := optimize_sound h

@[simp] theorem optimizePass_run (f : FragFunc) : optimizePass.run f = optimize f := rfl

/-- The optimiser keeps the signature. -/
theorem optimize?_params {f g : FragFunc} (hg : optimize? f = some g) :
    g.params = f.params ∧ g.result = f.result :=
  decompileFunc_params hg

/-- **The optimiser on Binaryen functions.** If `bf` is recognised as `f` and the
optimiser returns `bf'`, then `bf'` is recognised (at the same type) as a function
whose terminating runs include all of `f`'s. -/
theorem optimizeFunc?_sound {ft : FuncType} {bf bf' : BFunc} {f : FragFunc}
    (hf : ofBFunc? ft bf = some f) (ho : optimizeFunc? ft bf = some bf') :
    ∃ g, ofBFunc? ft bf' = some g ∧ ∀ args o, f.Run args o → g.Run args o := by
  unfold optimizeFunc? at ho
  rw [hf] at ho
  simp only [Option.bind_eq_bind, Option.bind_some] at ho
  cases hg : optimize? f with
  | none => simp [hg] at ho
  | some g =>
      simp only [hg, Option.bind_some] at ho
      obtain ⟨hp, hr⟩ := Silmaril.Proofs.Wasm.SSA.Pipeline.ofBFunc?_types hf
      obtain ⟨gp, gr⟩ := optimize?_params hg
      refine ⟨g, ofBFunc?_toBFunc? ho (by rw [hp, gp]) (by rw [hr, gr]), ?_⟩
      intro args o h
      exact optimize?_sound hg h

/-- **The optimiser on Binaryen functions is an equivalence.** If `bf` is
recognised as `f` and the optimiser returns `bf'`, then `bf'` is recognised at
the same type as a function with exactly `f`'s terminating outcomes. -/
theorem optimizeFunc?_equiv {ft : FuncType} {bf bf' : BFunc} {f : FragFunc}
    (hf : ofBFunc? ft bf = some f) (ho : optimizeFunc? ft bf = some bf') :
    ∃ g, ofBFunc? ft bf' = some g ∧ ∀ args o, f.Run args o ↔ g.Run args o := by
  unfold optimizeFunc? at ho
  rw [hf] at ho
  simp only [Option.bind_eq_bind, Option.bind_some] at ho
  cases hg : optimize? f with
  | none => simp [hg] at ho
  | some g =>
      simp only [hg, Option.bind_some] at ho
      obtain ⟨hp, hr⟩ := Silmaril.Proofs.Wasm.SSA.Pipeline.ofBFunc?_types hf
      obtain ⟨gp, gr⟩ := optimize?_params hg
      exact ⟨g, ofBFunc?_toBFunc? ho (by rw [hp, gp]) (by rw [hr, gr]), optimize?_equiv hg⟩

/-- A recognised function's type is its integer signature. -/
theorem ofBFunc?_types {ft : FuncType} {bf : BFunc} {f : FragFunc} (h : ofBFunc? ft bf = some f) :
    ft.params = f.params.map (fun t => .num (.int t)) ∧ ft.results = resultTypes f.result :=
  Silmaril.Proofs.Wasm.SSA.Pipeline.ofBFunc?_types h

/-! ## Tests -/

/-- `f(x) = (x + 0) * 1 + (2 + 3)` with a local. -/
def testArith : FragFunc where
  params := [.i32]
  locals := [.i32]
  result := some .i32
  body := [.localSet 1 (.op (.bin (.int .i32 .add)) [.localGet 0, .op (.const (.i32 0)) []]),
    .op (.bin (.int .i32 .add))
      [.op (.bin (.int .i32 .mul)) [.localGet 1, .op (.const (.i32 1)) []],
       .op (.bin (.int .i32 .add)) [.op (.const (.i32 2)) [], .op (.const (.i32 3)) []]]]

/-- The arithmetic folds to a single addition of the constant `5`. -/
example : (optimize? testArith).map (·.body) = some
    [.localSet 1 (.op (.bin (.int .i32 .add)) [.localGet 0, .op (.const (.i32 5)) []]),
     .return_ [.localGet 1], .unreachable] := by rfl

example : (optimize? testArith).bind (·.eval 50 [.i32 7]) = some (.ret (some (.i32 12))) := by
  decide

/-- Sum `n + (n-1) + … + 1` with a loop. -/
def testSum : FragFunc where
  params := [.i32]
  locals := [.i32]
  result := some .i32
  body := [.block none [.loop none [
      .brIf 1 [.op (.un (.test .i32)) [.localGet 0]],
      .localSet 1 (.op (.bin (.int .i32 .add)) [.localGet 1, .localGet 0]),
      .localSet 0 (.op (.bin (.int .i32 .sub)) [.localGet 0, .op (.const (.i32 1)) []]),
      .br 0 []]],
    .localGet 1]

example : testSum.eval 200 [.i32 10] = some (.ret (some (.i32 55))) := by decide

example : (optimize? testSum).bind (·.eval 200 [.i32 10]) = some (.ret (some (.i32 55))) := by
  decide

/-- Division by a constant zero traps, before and after. -/
def testTrap : FragFunc where
  params := [.i32]
  locals := []
  result := some .i32
  body := [.op (.bin (.int .i32 (.div .unsigned))) [.localGet 0, .op (.const (.i32 0)) []]]

example : (optimize? testTrap).bind (·.eval 50 [.i32 3]) = some .trap := by decide

/-- `x - x` and `x ^ x` are zero; `if` on a constant folds. -/
def testAlg : FragFunc where
  params := [.i64]
  locals := []
  result := some .i64
  body := [.if_ (some .i64) (.op (.const (.i32 1)) [])
    [.op (.bin (.int .i64 .xor)) [.localGet 0, .localGet 0]]
    [.localGet 0]]

example : (optimize? testAlg).bind (·.eval 50 [.i64 9]) = some (.ret (some (.i64 0))) := by
  decide

end Silmaril.Wasm.SSA
