module

public import Silmaril.Compiler.C.Sem.RefinementContract.Defs
public import Silmaril.Compiler.C.Sem.RefinementContractChecks.Defs
public import Silmaril.Compiler.C.Sem.C1.Defs
/-! Universal integer program proofs through real C0 function entry.
The body models `int add1(int x) { return x + 1; }`, matching the integer
refinement pattern of RefinedC's introductory `add1` example. The typed-Ail body
and source-name views are explicit; no unproved parser or C frontend link is hidden.
The theorem covers all safe signed32 inputs and arbitrary caller locals, globals,
and output, including argument conversion and restoration of the caller frame. -/

@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCPrograms

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Assertion
open AssertionExecution.Checks
open RefinementContract

/-- All signed32 inputs for which mathematical increment is representable. -/
def SafeIncrement (n : Int) : Prop := -2147483648 ≤ n ∧ n < 2147483647

def Signed32 (n : Int) : Prop := -2147483648 ≤ n ∧ n < 2147483648

theorem safeIncrement_input {n : Int} (h : SafeIncrement n) : Signed32 n := by
  unfold SafeIncrement at h
  unfold Signed32
  omega

theorem safeIncrement_output {n : Int} (h : SafeIncrement n) : Signed32 (n + 1) := by
  unfold SafeIncrement at h
  unfold Signed32
  omega

theorem wrap_signed32 {n : Int} (h : Signed32 n) : C0.wrap 4 true n = n := by
  apply C1.C0_wrap_self (by decide)
  simpa [C0.inRange, Signed32] using h

@[simp] theorem intExpr_type (e : ExpressionNode GenTypeCategory) :
    Silmaril.Compile.C.typeOf (intExpr e) = .int 4 true := rfl

/-- Actual callee lookup, argument conversion, arithmetic and return conversion.
No execution equation is assumed; the fixed fuel suffices for every safe input. -/
theorem add1_call (n : Int) (initial : C0.Env) (safe : SafeIncrement n) :
    C0.callFn RefinementContract.Checks.incrementProgram 9 xSym [n] initial =
      .ok (n + 1, initial) := by
  have w1 : C0.wrap 4 true 1 = 1 := by decide +kernel
  have wn := wrap_signed32 (safeIncrement_input safe)
  have wr := wrap_signed32 (safeIncrement_output safe)
  have range : C0.inRange 4 true (n + 1) = true := by
    simpa [C0.inRange, Signed32] using safeIncrement_output safe
  simp only [C0.callFn, RefinementContract.Checks.incrementProgram, program,
    incrementFunction, xSym, Std.HashMap.getElem?_insert]
  simp [C0.convTo, wn]
  simp only [Bind.bind, Except.bind]
  rw [C0.loop, C0.step]
  simp only [incrementBody, Statement.node]
  simp [C0.evalE, intExpr, Expression.node, Expression.annotation, literal, intAnnot,
    Silmaril.Compile.C.typeOf, Silmaril.Compile.C.ofGenType,
    Silmaril.Compile.C.resolve, Silmaril.Compile.C.resolveIsBool,
    Silmaril.Compile.C.intLayout, Silmaril.Cerberus.Mem.Concrete.integerLayout,
    C0.lvalSym, xLvalue, C0.readVar, xSym, C0.constVal,
    Silmaril.Compile.Forks.Csem.C.intConstValue, C0.convTo,
    Silmaril.Cerberus.Mem.Concrete.baseWidth,
    C0.shape, C0.arith, wn, wr, w1, range, Bind.bind, Except.bind, pure, Except.pure]


abbrev IncrementInput := {n : Int // SafeIncrement n}

/-- Every safe mathematical refinement has an actual input; arbitrary caller states
are allowed and are preserved exactly, including globals and buffered output. -/
def incrementSpec : Spec IncrementInput where
  pre n args _ := args = [n.val]
  post n _ initial result finalState := result = n.val + 1 ∧ finalState = initial

theorem increment_checked_total :
    CheckedTotal RefinementContract.Checks.incrementProgram xSym incrementSpec := by
  constructor
  · intro n
    exact ⟨[n.val], {}, rfl⟩
  · intro n args initial hp
    subst args
    exact ⟨9, n.val + 1, initial, add1_call n.val initial n.property, rfl, rfl⟩

/-- This is the exact elaborated contract emitted by `refinedc-lean` for its pinned
`add1.attributes` fixture: the argument and return are signed32 singleton types. -/
def incrementAnnotation : RefinedC.Contract where
  parameters := ["n"]
  args := [⟨.i32, some (.var "n")⟩]
  returns := ⟨.i32, some (.add (.var "n") (.literal 1))⟩
  requires := .and (.le (.add (.var "n") (.literal 1)) (.literal 2147483647)) .truth
  ensures := .truth

/-- Ghost n is explicitly associated with the actual input by the annotation's
singleton argument refinement. It is never read from discarded callee locals. -/
def parameterEnv (n : Int) : Pure.Env := fun name => if name = "n" then n else 0

theorem annotation_pre_iff (n : Int) (args : List Int) :
    incrementAnnotation.pre (parameterEnv n) args ↔ args = [n] ∧ SafeIncrement n := by
  cases args with
  | nil => simp [incrementAnnotation, RefinedC.Contract.pre, RefinedC.ArgRefinements]
  | cons actual rest =>
    cases rest with
    | cons a rest =>
      simp [incrementAnnotation, RefinedC.Contract.pre, RefinedC.ArgRefinements]
    | nil =>
      simp [incrementAnnotation, RefinedC.Contract.pre, RefinedC.ArgRefinements,
        RefinedC.IntRefinement.holds, RefinedC.IntegerType.admits,
        RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
        RefinedC.IntegerType.bits, RefinedC.IntegerType.signed,
        Pure.Formula.holds, Pure.Term.eval, parameterEnv, SafeIncrement]
      omega

theorem annotation_post (n : Int) (safe : SafeIncrement n) :
    incrementAnnotation.post (parameterEnv n) (n + 1) := by
  have range := safeIncrement_output safe
  simpa [incrementAnnotation, RefinedC.Contract.post, RefinedC.IntRefinement.holds,
    RefinedC.IntegerType.admits, RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
    RefinedC.IntegerType.bits, RefinedC.IntegerType.signed, Pure.Formula.holds,
    Pure.Term.eval, parameterEnv, Signed32] using range

/-- The generated integer annotation goal is true for every safe input and actual
return, and successful execution is proved in the accompanying certificate. -/
theorem annotation_goal (n : Int) (safe : SafeIncrement n) :
    incrementAnnotation.leanGoal (parameterEnv n) (parameterEnv n) [n] (n + 1) := by
  apply (RefinedC.Contract.leanGoal_correct _ _ _ _ _).mpr
  intro _
  exact annotation_post n safe

def before (n : IncrementInput) (_ : List Int) (_ : C0.Env) : Pure.Env := parameterEnv n.val

def after (n : IncrementInput) (_ : List Int) (_ : C0.Env) (_ : Int) (_ : C0.Env) :
    Pure.Env := parameterEnv n.val

/-- Total correctness for the translated RefinedC annotation at actual function entry.
All source-name interpretation is visible in `before` and `after`. -/
theorem annotation_total :
    Total RefinementContract.Checks.incrementProgram xSym
      (refinedCSpec incrementAnnotation before after) := by
  apply refinedC_total_of_goals
  intro n args initial hp
  obtain ⟨rfl, safe⟩ := (annotation_pre_iff n.val args).mp hp
  exact ⟨9, n.val + 1, initial, add1_call n.val initial safe, annotation_goal n.val safe⟩

theorem annotation_realizable :
    Realizable (refinedCSpec incrementAnnotation before after) := by
  intro n
  exact ⟨[n.val], {}, (annotation_pre_iff n.val [n.val]).mpr ⟨rfl, n.property⟩⟩

theorem annotation_checked_total :
    CheckedTotal RefinementContract.Checks.incrementProgram xSym
      (refinedCSpec incrementAnnotation before after) :=
  ⟨annotation_realizable, annotation_total⟩

/-- The safe-input family contains ordinary negative, zero and maximal safe values. -/
theorem safe_examples : SafeIncrement (-2147483648) ∧ SafeIncrement 0 ∧
    SafeIncrement 2147483646 := by
  unfold SafeIncrement
  decide +kernel

/-- The annotation excludes the overflowing input instead of certifying it vacuously
as a safe execution. -/
theorem overflowing_input_excluded :
    ¬incrementAnnotation.pre (parameterEnv 2147483647) [2147483647] := by
  rw [annotation_pre_iff]
  unfold SafeIncrement
  decide +kernel


/-- The excluded boundary really triggers the executable semantics' signed UB. -/
theorem overflowing_call (initial : C0.Env) :
    C0.callFn RefinementContract.Checks.incrementProgram 9 xSym [2147483647] initial =
      .error (.undefined "signed integer overflow") := by
  cbv

end Silmaril.Compile.C.Sem.RefinedCPrograms
