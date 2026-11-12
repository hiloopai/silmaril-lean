module

public import Silmaril.Wasm.SSA.Fragment.Defs
import Silmaril.Proofs.Wasm.SSA.Fragment.Interp

/-!
# The fragment: determinism and the fuel interpreter

* The big-step semantics is deterministic (`Exec.det`, `Args.det`, `Seq.det`,
  `FragFunc.Run.det`).
* The fuel interpreter is sound and complete for it: `evalE n ls e = some o`
  for some `n` exactly when `Exec ls e o` (likewise for `evalArgs`/`evalSeq`
  and `FragFunc.eval`/`FragFunc.Run`), and more fuel never changes a result.

Determinism is derived from interpreter completeness and fuel monotonicity.
Nothing here concerns divergence: a run with no derivation (divergent or
stuck) is one on which the interpreter returns `none` for every fuel.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Proofs.Wasm.SSA.Fragment

theorem Exec.det {ls : List WVal} {e : Expr} {o₁ o₂ : Out (Option WVal)}
    (h₁ : Exec ls e o₁) (h₂ : Exec ls e o₂) : o₁ = o₂ := exec_det h₁ h₂

theorem Args.det {ls : List WVal} {es : List Expr} {o₁ o₂ : Out (List WVal)}
    (h₁ : Args ls es o₁) (h₂ : Args ls es o₂) : o₁ = o₂ := args_det h₁ h₂

theorem Seq.det {ls : List WVal} {r : Option WVal} {es : List Expr} {o₁ o₂ : Out (Option WVal)}
    (h₁ : Seq ls r es o₁) (h₂ : Seq ls r es o₂) : o₁ = o₂ := seq_det h₁ h₂

theorem FragFunc.Run.det {f : FragFunc} {args : List WVal} {o₁ o₂ : FOut}
    (h₁ : f.Run args o₁) (h₂ : f.Run args o₂) : o₁ = o₂ := run_det h₁ h₂

theorem evalE_sound {n : Nat} {ls : List WVal} {e : Expr} {o : Out (Option WVal)}
    (h : evalE n ls e = some o) : Exec ls e o := (sound n).1 _ _ _ h

theorem evalArgs_sound {n : Nat} {ls : List WVal} {es : List Expr} {o : Out (List WVal)}
    (h : evalArgs n ls es = some o) : Args ls es o := (sound n).2.1 _ _ _ h

theorem evalSeq_sound {n : Nat} {ls : List WVal} {r : Option WVal} {es : List Expr}
    {o : Out (Option WVal)} (h : evalSeq n ls r es = some o) : Seq ls r es o :=
  (sound n).2.2 _ _ _ _ h

theorem evalE_complete {ls : List WVal} {e : Expr} {o : Out (Option WVal)}
    (h : Exec ls e o) : ∃ n, evalE n ls e = some o := complete h

theorem evalArgs_complete {ls : List WVal} {es : List Expr} {o : Out (List WVal)}
    (h : Args ls es o) : ∃ n, evalArgs n ls es = some o := complete_args h

theorem evalSeq_complete {ls : List WVal} {r : Option WVal} {es : List Expr}
    {o : Out (Option WVal)} (h : Seq ls r es o) : ∃ n, evalSeq n ls r es = some o :=
  complete_seq h

theorem evalE_mono {n m : Nat} (hle : n ≤ m) {ls : List WVal} {e : Expr} {o : Out (Option WVal)}
    (h : evalE n ls e = some o) : evalE m ls e = some o := liftE h hle

theorem FragFunc.eval_sound {fuel : Nat} {f : FragFunc} {args : List WVal} {o : FOut}
    (h : f.eval fuel args = some o) : f.Run args o := Silmaril.Proofs.Wasm.SSA.Fragment.eval_sound h

theorem FragFunc.eval_complete {f : FragFunc} {args : List WVal} {o : FOut}
    (h : f.Run args o) : ∃ fuel, f.eval fuel args = some o :=
  Silmaril.Proofs.Wasm.SSA.Fragment.eval_complete h

/-! ## Examples -/

/-- `f(x) = x + 1` on `i32`. -/
def exampleInc : FragFunc where
  params := [.i32]
  locals := []
  result := some .i32
  body := [.op (.bin (.int .i32 .add)) [.localGet 0, .op (.const (.i32 1)) []]]

example : exampleInc.eval 10 [.i32 41] = some (.ret (some (.i32 42))) := by decide

/-- `f(x) = 10 / x`, trapping on zero. -/
def exampleDiv : FragFunc where
  params := [.i32]
  locals := []
  result := some .i32
  body := [.op (.bin (.int .i32 (.div .unsigned))) [.op (.const (.i32 10)) [], .localGet 0]]

example : exampleDiv.eval 10 [.i32 0] = some .trap := by decide
example : exampleDiv.eval 10 [.i32 3] = some (.ret (some (.i32 3))) := by decide

/-- The run of `exampleInc` on `41`, through interpreter soundness. -/
theorem exampleInc_run : exampleInc.Run [.i32 41] (.ret (some (.i32 42))) :=
  FragFunc.eval_sound (fuel := 10) (by decide)

/-- Counting down from `x` in a loop, summing into a local. -/
def exampleSum : FragFunc where
  params := [.i32]
  locals := [.i32]
  result := some .i32
  body := [.block none [.loop none [
      .brIf 1 [.op (.un (.test .i32)) [.localGet 0]],
      .localSet 1 (.op (.bin (.int .i32 .add)) [.localGet 1, .localGet 0]),
      .localSet 0 (.op (.bin (.int .i32 .sub)) [.localGet 0, .op (.const (.i32 1)) []]),
      .br 0 []]],
    .localGet 1]

example : exampleSum.eval 100 [.i32 10] = some (.ret (some (.i32 55))) := by decide

end Silmaril.Wasm.SSA
