module

public import Silmaril.Compiler.C.Sem.C5.Defs
@[expose] public section

/-!
# Checked agreement between adjacent C semantics

These executable checks compare completed runs of two frozen interpreters. They
decline undefined behaviour, unsupported constructs, exhaustion and disagreement.
They do not assume the universal ladder laws: global initialization, casts and
layout can differ even when a lower fragment checker accepts the program.

`TargetsLadderCheck.lean` proposes a non-vacuous soundness statement for each
check. Those statements require separate proofs using fuel monotonicity to turn
each completed run into its interpreter's entire singleton behaviour set.
There is deliberately no C2/C3 check in this set: C3 changes `float` layout.
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Cerberus.Ail

/-- The fixed fuel bound used independently for each adjacent interpreter. -/
def ladderCheckFuel : Nat := 100000

/-- Accept exactly when both bounded runs finish with the same defined observation.
No fragment premise is needed: acceptance checks the executions themselves. -/
def ladderCheckWith (lower upper : Nat → TypedProgram → C0.Result)
    (p : TypedProgram) : Bool :=
  match lower ladderCheckFuel p with
  | .done a =>
    match upper ladderCheckFuel p with
    | .done b => decide (a = b)
    | _ => false
  | _ => false

/-- Per-program C0/C1 agreement, declining every unfinished or undefined run. -/
def ladderCheck1 : TypedProgram → Bool := ladderCheckWith C0.run C1.run

/-- Per-program C1/C2 agreement, including the effect of aggregate initialization. -/
def ladderCheck2 : TypedProgram → Bool := ladderCheckWith C1.run C2.run

/-- Per-program C3/C4 agreement. -/
def ladderCheck4 : TypedProgram → Bool := ladderCheckWith C3.run C4.run

/-- Per-program C4/C5 agreement. -/
def ladderCheck5 : TypedProgram → Bool := ladderCheckWith C4.run C5.run

end Silmaril.Compile.C.Sem
