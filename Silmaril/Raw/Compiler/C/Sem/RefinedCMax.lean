module

public import Silmaril.Compiler.C.Sem.RefinedCPrograms.Defs
/-! A second universal scalar program: signed32 maximum, including both branches.
The explicit typed-Ail function represents
`int max_i32(int x, int y) { if (x <= y) return y; else return x; }`.
Every signed32 pair is admitted, including negative numbers and both extrema.
The RefinedC-style annotation below uses singleton integer arguments and a pure
maximum characterization, rather than assuming an interpretation of arbitrary
Rocq functions in annotation strings. -/

@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCMax

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Assertion
open Silmaril.Compile.C.Sem.RefinedCPrograms
open Silmaril.Compile.C.Sem.AssertionExecution.Checks
open RefinementContract

def ySym : Sym := ⟨⟨[]⟩, 1, .id "y"⟩
def maxSym : Sym := ⟨⟨[]⟩, 2, .id "max_i32"⟩
def yLvalue : TypedExpression :=
  .mk (.lvalue ⟨false, false, false⟩ (.mk [] (.basic (.integer (.signed .int)))) false)
    [] .unknown (.ident ySym)
def readX : TypedExpression := intExpr (.rvalue xLvalue)
def readY : TypedExpression := intExpr (.rvalue yLvalue)
def returnValue (e : TypedExpression) : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) (.return_ e)
def maxBody : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk [])
    (.if_ (intExpr (.binary readX .le readY)) (returnValue readY) (returnValue readX))
def maxFunction : C0.FunDef :=
  ⟨[(0, .int 4 true), (1, .int 4 true)], .int 4 true, maxBody, {}⟩
def maxProgram : C0.Prog :=
  { program with funcs := ({} : Std.HashMap Nat C0.FunDef).insert maxSym.number maxFunction }

/-- Full real function entry and execution for all signed32 pairs, preserving the
whole caller state. The two mathematical cases exercise both source branches. -/
theorem max_call (x y : Int) (hx : Signed32 x) (hy : Signed32 y) (caller : C0.Env) :
    C0.callFn maxProgram 9 maxSym [x, y] caller = .ok (max x y, caller) := by
  have wx := wrap_signed32 hx
  have wy := wrap_signed32 hy
  by_cases h : x ≤ y
  · rw [max_eq_right h]
    simp only [C0.callFn, maxProgram, program, maxFunction, maxSym,
      Std.HashMap.getElem?_insert]
    simp [C0.convTo, wx, wy]
    simp only [Bind.bind, Except.bind]
    rw [C0.loop, C0.step]
    simp only [maxBody, Statement.node]
    simp [C0.evalE, readX, readY, intExpr, intAnnot, Expression.node, Expression.annotation,
      xLvalue, yLvalue, C0.lvalSym, C0.readVar, xSym, ySym,
      Silmaril.Compile.C.typeOf, Silmaril.Compile.C.ofGenType,
      Silmaril.Compile.C.resolve, Silmaril.Compile.C.resolveIsBool,
      Silmaril.Compile.C.intLayout, Silmaril.Cerberus.Mem.Concrete.integerLayout,
      Silmaril.Cerberus.Mem.Concrete.baseWidth, Silmaril.Compile.C.usual,
      Silmaril.Compile.C.promote, C0.shape, C0.usualOf, C0.compare, C0.convTo,
      wx, wy, h, Std.HashMap.getElem_insert, Bind.bind, Except.bind, pure, Except.pure]
    rw [C0.loop, C0.step]
    simp [returnValue, Statement.node, C0.evalE, Expression.node,
      C0.lvalSym, C0.readVar, C0.convTo, wy,
      Bind.bind, Except.bind, pure, Except.pure]
  · rw [max_eq_left (by omega : y ≤ x)]
    simp only [C0.callFn, maxProgram, program, maxFunction, maxSym,
      Std.HashMap.getElem?_insert]
    simp [C0.convTo, wx, wy]
    simp only [Bind.bind, Except.bind]
    rw [C0.loop, C0.step]
    simp only [maxBody, Statement.node]
    simp [C0.evalE, readX, readY, intExpr, intAnnot, Expression.node, Expression.annotation,
      xLvalue, yLvalue, C0.lvalSym, C0.readVar, xSym, ySym,
      Silmaril.Compile.C.typeOf, Silmaril.Compile.C.ofGenType,
      Silmaril.Compile.C.resolve, Silmaril.Compile.C.resolveIsBool,
      Silmaril.Compile.C.intLayout, Silmaril.Cerberus.Mem.Concrete.integerLayout,
      Silmaril.Cerberus.Mem.Concrete.baseWidth, Silmaril.Compile.C.usual,
      Silmaril.Compile.C.promote, C0.shape, C0.usualOf, C0.compare, C0.convTo,
      wx, wy, h, Std.HashMap.getElem_insert, Bind.bind, Except.bind, pure, Except.pure]
    rw [C0.loop, C0.step]
    simp [returnValue, Statement.node, C0.evalE, Expression.node,
      C0.lvalSym, C0.readVar, C0.convTo, wx, Std.HashMap.getElem_insert,
      Bind.bind, Except.bind, pure, Except.pure]


/-- A mathematical characterization: m is an upper bound and an actual argument. -/
def MaxRelation (x y m : Int) : Prop := x ≤ m ∧ y ≤ m ∧ (m = x ∨ m = y)

theorem maxRelation_correct (x y m : Int) : MaxRelation x y m ↔ m = max x y := by
  by_cases h : x ≤ y
  · rw [max_eq_right h]
    unfold MaxRelation
    omega
  · rw [max_eq_left (by omega : y ≤ x)]
    unfold MaxRelation
    omega

/-- A relational singleton return type using the restricted Rocq comparison and
conjunction/disjunction subset accepted by the annotation frontend. -/
def maxAnnotation : RefinedC.Contract where
  parameters := ["x", "y", "m"]
  args := [⟨.i32, some (.var "x")⟩, ⟨.i32, some (.var "y")⟩]
  returns := ⟨.i32, some (.var "m")⟩
  requires := .and
    (.and (.and (.le (.var "x") (.var "m")) (.le (.var "y") (.var "m")))
      (.or (.eq (.var "m") (.var "x")) (.eq (.var "m") (.var "y")))) .truth
  ensures := .truth

def parameterEnv (x y m : Int) : Pure.Env := fun name =>
  if name = "x" then x else if name = "y" then y else if name = "m" then m else 0

theorem annotation_pre_values (x y m : Int) :
    maxAnnotation.pre (parameterEnv x y m) [x, y] ↔
      Signed32 x ∧ Signed32 y ∧ MaxRelation x y m := by
  simp [maxAnnotation, RefinedC.Contract.pre, RefinedC.ArgRefinements,
    RefinedC.IntRefinement.holds, RefinedC.IntegerType.admits,
    RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
    RefinedC.IntegerType.bits, RefinedC.IntegerType.signed, Pure.Formula.holds,
    Pure.Term.eval, parameterEnv, Signed32, MaxRelation, and_assoc]

theorem max_signed32 (x y : Int) (hx : Signed32 x) (hy : Signed32 y) :
    Signed32 (max x y) := by
  by_cases h : x ≤ y
  · simpa [max_eq_right h] using hy
  · simpa [max_eq_left (by omega : y ≤ x)] using hx

theorem annotation_post (x y : Int) (hx : Signed32 x) (hy : Signed32 y) :
    maxAnnotation.post (parameterEnv x y (max x y)) (max x y) := by
  simpa [maxAnnotation, RefinedC.Contract.post, RefinedC.IntRefinement.holds,
    RefinedC.IntegerType.admits, RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
    RefinedC.IntegerType.bits, RefinedC.IntegerType.signed, Pure.Formula.holds,
    Pure.Term.eval, parameterEnv, Signed32] using max_signed32 x y hx hy

theorem annotation_goal (x y : Int) (hx : Signed32 x) (hy : Signed32 y) :
    maxAnnotation.leanGoal (parameterEnv x y (max x y)) (parameterEnv x y (max x y))
      [x, y] (max x y) := by
  apply (RefinedC.Contract.leanGoal_correct _ _ _ _ _).mpr
  intro _
  exact annotation_post x y hx hy

abbrev MaxInput := {xy : Int × Int // Signed32 xy.1 ∧ Signed32 xy.2}

def maxSpec : Spec MaxInput where
  pre g args _ := args = [g.val.1, g.val.2]
  post g _ initial result finalState := result = max g.val.1 g.val.2 ∧ finalState = initial

theorem max_checked_total : CheckedTotal maxProgram maxSym maxSpec := by
  constructor
  · intro g
    exact ⟨[g.val.1, g.val.2], {}, rfl⟩
  · intro g args caller hp
    subst args
    exact ⟨9, max g.val.1 g.val.2, caller,
      max_call _ _ g.property.1 g.property.2 caller, rfl, rfl⟩

/-- An actual call and the elaborated annotation goal for every signed32 pair.
Ghost m is explicitly chosen as the uniquely characterized mathematical maximum. -/
theorem annotated_max_call (x y : Int) (hx : Signed32 x) (hy : Signed32 y)
    (caller : C0.Env) :
    ∃ fuel result finalState,
      C0.callFn maxProgram fuel maxSym [x, y] caller = .ok (result, finalState) ∧
      maxAnnotation.pre (parameterEnv x y (max x y)) [x, y] ∧
      maxAnnotation.leanGoal (parameterEnv x y (max x y))
        (parameterEnv x y (max x y)) [x, y] result ∧ finalState = caller :=
  ⟨9, max x y, caller, max_call x y hx hy caller,
    (annotation_pre_values _ _ _).mpr
      ⟨hx, hy, (maxRelation_correct _ _ _).mpr rfl⟩,
    annotation_goal x y hx hy, rfl⟩

/-- Both branch regions and equality are realizable, including negative values. -/
theorem branch_examples :
    MaxRelation (-10) 7 7 ∧ MaxRelation 9 (-3) 9 ∧ MaxRelation (-5) (-5) (-5) := by
  unfold MaxRelation
  decide +kernel

end Silmaril.Compile.C.Sem.RefinedCMax
