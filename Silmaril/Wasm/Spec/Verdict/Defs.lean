module

public import Silmaril.Wasm.Game.Signature.Defs

/-!
# Verdicts and executable typing of values

`Verdict` is the answer of the checkers of `Silmaril.Wasm.Spec` and `Silmaril.Wasm.Verify`
(`proved`, `refuted`, `unknown`). `hasValB`, `typedB` and `resultTypedB` decide the
scalar typing of values, lists of values and results. These are the executable
parts of the specifications that the checkers need; the specifications themselves
(`Silmaril.Wasm.Spec.Basic`, `Silmaril.Wasm.Spec.Run`) import this header.
-/

@[expose] public section

namespace Silmaril.Wasm.Spec

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- A verdict of a checker. -/
inductive Verdict where
  /-- The property holds. -/
  | proved
  /-- The property fails (with a counterexample). -/
  | refuted
  /-- No conclusion. -/
  | unknown
  deriving DecidableEq, Repr

/-- Decidable scalar typing of a value. -/
def hasValB : ScalarType → Val → Bool
  | .num t, .num v => decide (v.type = t)
  | .v128, .vec _ => true
  | .i31 _, .ref (.i31 _) => true
  | .i31 n, .ref .null => n
  | _, _ => false

/-- Decidable typing of a list of values. -/
def typedB : List ScalarType → List Val → Bool
  | [], [] => true
  | t :: ts, v :: vs => hasValB t v && typedB ts vs
  | _, _ => false

/-- Decidable typing of a result. -/
def resultTypedB (ts : List ScalarType) : Result → Bool
  | .values vs => typedB ts vs
  | _ => true

end Silmaril.Wasm.Spec
