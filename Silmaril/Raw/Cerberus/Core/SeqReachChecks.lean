module

public import Silmaril.Cerberus.Core.SeqReach.Defs

/-! Concrete witnesses for the semantic premises and the two important edge cases:
an unspecified value can select an ordinary arm, and a specified integer is not a
Core boolean. These checks use the kernel and the canonical dynamics. -/

@[expose] public section

namespace Silmaril.Cerberus.Core.SeqReachChecks

open Dynamics SeqReach

variable (file : Program) (labels : Labels)

/-- Binding an integer and reading its symbol really computes the bound value. -/
theorem let_integer (sym : Sym) (n : Int) (env : Env) :
    PureEval file labels
      (.mk [] () (.let_ (.mk [] (.base (some sym, .object .integer)))
        (.mk [] () (.val (.object (.integer n)))) (.mk [] () (.sym sym))))
      env (.object (.integer n)) := by
  apply PureEval.let_ [] (pure_value [] (.object (.integer n)) env) rfl
  apply pure_symbol
  simp [extendEnv, runtimeValue, runtimeObject]

/-- Both boolean branches have satisfiable computation premises. -/
theorem if_integer (b : Bool) (env : Env) :
    PureEval file labels
      (.mk [] () (.if_ (.mk [] () (.val (if b then .true else .false)))
        (.mk [] () (.val (.object (.integer 7)))) (.mk [] () (.val (.object (.integer 9))))))
      env (.object (.integer (if b then 7 else 9))) := by
  cases b with
  | false =>
    apply PureEval.if_ [] false
    · simpa [runtimeValue, boolean] using (pure_value (file := file) (labels := labels) [] .false env)
    · simpa [runtimeValue, runtimeObject] using
        (pure_value (file := file) (labels := labels) [] (.object (.integer 9)) env)
  | true =>
    apply PureEval.if_ [] true
    · simpa [runtimeValue, boolean] using (pure_value (file := file) (labels := labels) [] .true env)
    · simpa [runtimeValue, runtimeObject] using
        (pure_value (file := file) (labels := labels) [] (.object (.integer 7)) env)

/-- `Unspecified` may select a normal unit-valued arm; it is not automatically UB. -/
theorem unspecified_unit (ty : Ctype) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.effectExpr (.mk [] (.case_ (.mk [] () (.val (.loaded (.unspecified ty))))
        [(.mk [] (.ctor .specified [.mk [] (.base (none, .object .integer))]),
          .mk [] (.pure (.mk [] () (.val (.object (.integer 7)))))),
         (.mk [] (.ctor .unspecified [.mk [] (.base (none, .ctype))]),
          .mk [] (.pure (.mk [] () (.val .unit))))])) env, k, m⟩
      ⟨.value .unit, k, m⟩ := by
  have h := unspecified_case_reaches (file := file) (labels := labels) [] [] []
    (.mk [] (.base (none, .object .integer))) (.mk [] (.base (none, .ctype)))
    (yes := .mk [] (.pure (.mk [] () (.val (.object (.integer 7))))))
    (no := .mk [] (.pure (.mk [] () (.val .unit))))
    (pure_value [] (.loaded (.unspecified ty)) env) rfl k m
  exact h.trans (by simpa [focusMemory, extendEnv, runtimeValue] using
    (effect_pure_reaches (file := file) (labels := labels) [] (pure_value [] .unit env) k m))

/-- Using a specified integer directly as an `if` condition is an error, not UB. -/
theorem specified_integer_condition (n : Int) (yes no : EE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    request file labels ⟨.value (.loaded (.specified (.integer n))), .effectIf yes no env :: k, m⟩ =
      .end_ (.error "Eif condition is not boolean") := by
  simp [request, requestAux, awaitsScheduling]

end Silmaril.Cerberus.Core.SeqReachChecks
