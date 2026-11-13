module

public import Silmaril.Compiler.C.Sem.RefinedCPrograms.Defs
import Mathlib.Tactic

@[expose] public section

/-! Actual typed-Ail execution of Harbor's triangular.c loop. Source syntax is
written explicitly; no unverified C parser correspondence is assumed. -/
namespace Silmaril.Compile.C.Sem.HarborTriangular

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open AssertionExecution.Checks
open RefinedCPrograms

/-- Mathematical triangular sum, independently of the interpreter. -/
def triangular : Nat → Int
  | 0 => 0
  | n + 1 => triangular n + (n + 1 : Nat)

theorem triangular_formula (n : Nat) : 2 * triangular n = (n : Int) * (n + 1) := by
  induction n with
  | zero => simp [triangular]
  | succ n ih => simp only [triangular, Nat.cast_succ]; nlinarith

theorem triangular_range {n : Nat} (hn : n ≤ 65535) :
    0 ≤ triangular n ∧ triangular n ≤ 2147450880 := by
  have hn0 : (0 : Int) ≤ n := Int.natCast_nonneg n
  have hn1 : (n : Int) ≤ 65535 := by exact_mod_cast hn
  have low : 0 ≤ (n : Int) * (n + 1) := mul_nonneg hn0 (by omega)
  have high : 0 ≤ (65535 - (n : Int)) * (65536 + n) := mul_nonneg (by omega) (by omega)
  constructor <;> nlinarith [triangular_formula n]

theorem triangular_signed {n : Nat} (hn : n ≤ 65535) : Signed32 (triangular n) := by
  have h := triangular_range hn
  unfold Signed32
  omega

def nSym : Sym := ⟨⟨[]⟩, 0, .id "n"⟩
def iSym : Sym := ⟨⟨[]⟩, 1, .id "i"⟩
def sSym : Sym := ⟨⟨[]⟩, 2, .id "s"⟩
def fSym : Sym := ⟨⟨[]⟩, 3, .id "triangular"⟩

def lvalue (x : Sym) : TypedExpression :=
  .mk (.lvalue ⟨false, false, false⟩ (.mk [] (.basic (.integer (.signed .int)))) false)
    [] .unknown (.ident x)
def read (x : Sym) : TypedExpression := intExpr (.rvalue (lvalue x))
def stmt (s : StatementNode GenTypeCategory) : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) s

def condition : TypedExpression := intExpr (.binary (read iSym) .lt (read nSym))
def increment : TypedStatement := stmt (.expr (intExpr (.unary .postfixIncr (lvalue iSym))))
def accumulate : TypedStatement := stmt (.expr (intExpr (.compoundAssign (lvalue sSym) .add (read iSym))))
def loopBody : TypedStatement := stmt (.block [] [increment, accumulate])
def returnSum : TypedStatement := stmt (.return_ (read sSym))
def whileStatement : TypedStatement := stmt (.while_ condition loopBody 0)
def initStatement : TypedStatement := stmt (.declaration [(iSym, some (literal 0)), (sSym, some (literal 0))])
def body : TypedStatement := stmt (.block [] [initStatement, whileStatement, returnSum])
def function : C0.FunDef :=
  ⟨[(0, .int 4 true)], .int 4 true, body,
    (({} : Std.HashMap Nat Silmaril.Compile.C.CType).insert 1 (.int 4 true)).insert 2 (.int 4 true)⟩
def program : C0.Prog :=
  { AssertionExecution.Checks.program with funcs := ({} : Std.HashMap Nat C0.FunDef).insert 3 function }

def loopKont : C0.Kont := .while_ condition loopBody (.seq [returnSum] .stop)

def Stores (env : C0.Env) (n i : Nat) : Prop :=
  env.locals[0]? = some (n : Int) ∧ env.locals[1]? = some (i : Int) ∧
    env.locals[2]? = some (triangular i)

private theorem nat_signed {n : Nat} (h : n ≤ 65535) : Signed32 (n : Int) := by
  unfold Signed32
  omega

private theorem eval_read (fuel : Nat) (x : Sym) (env : C0.Env) (v : Int)
    (hx : env.locals[x.number]? = some v) :
    C0.evalE program (fuel + 1) function (read x) env = .ok (v, env) := by
  simp [C0.evalE, read, intExpr, C0.lvalSym, lvalue, C0.readVar, Expression.node, hx, Bind.bind, Except.bind, pure, Except.pure]

private theorem eval_condition (fuel n i : Nat) (env : C0.Env)
    (stores : Stores env n i) (hn : n ≤ 65535) (hi : i ≤ n) :
    C0.evalE program (fuel + 4) function condition env =
      .ok ((if i < n then 1 else 0), env) := by
  have wn := wrap_signed32 (nat_signed hn)
  have wi := wrap_signed32 (nat_signed (hi.trans hn))
  obtain ⟨hnstore, histore, hsstore⟩ := stores
  simp [C0.evalE, condition, intExpr, Expression.node, Expression.annotation,
    Silmaril.Compile.C.typeOf, Silmaril.Compile.C.ofGenType,
    Silmaril.Compile.C.resolve, Silmaril.Compile.C.resolveIsBool,
    Silmaril.Compile.C.intLayout, Silmaril.Cerberus.Mem.Concrete.integerLayout,
    Silmaril.Cerberus.Mem.Concrete.baseWidth, intAnnot,
    read, C0.lvalSym, lvalue, C0.readVar, nSym, iSym, hnstore, histore,
    C0.usualOf, C0.shape, Silmaril.Compile.C.usual, Silmaril.Compile.C.promote,
    C0.convTo, wn, wi, C0.compare, Bind.bind, Except.bind, pure, Except.pure]

def bumped (env : C0.Env) (i : Nat) : C0.Env :=
  { env with locals := env.locals.insert 1 (i + 1 : Nat) }

def advanced (env : C0.Env) (i : Nat) : C0.Env :=
  { bumped env i with locals := (bumped env i).locals.insert 2 (triangular (i + 1)) }

private theorem eval_increment (fuel n i : Nat) (env : C0.Env)
    (stores : Stores env n i) (hn : n ≤ 65535) (hi : i < n) :
    C0.evalE program (fuel + 4) function (intExpr (.unary .postfixIncr (lvalue iSym))) env =
      .ok ((i : Int), bumped env i) := by
  have wi := wrap_signed32 (nat_signed (Nat.le_trans (Nat.le_of_lt hi) hn))
  have wi1 := wrap_signed32 (nat_signed (Nat.le_trans hi hn))
  have range : C0.inRange 4 true ((i : Int) + 1) = true := by
    simpa [C0.inRange, Signed32] using nat_signed (Nat.le_trans hi hn)
  simp only [Nat.cast_succ] at wi1
  obtain ⟨_, histore, _⟩ := stores
  simp [C0.evalE, intExpr, Expression.node, Expression.annotation,
    Silmaril.Compile.C.typeOf,
    Silmaril.Compile.C.intLayout, Silmaril.Cerberus.Mem.Concrete.integerLayout,
    Silmaril.Cerberus.Mem.Concrete.baseWidth, intAnnot,
    C0.lvalSym, lvalue, C0.readVar, iSym, histore, C0.writeVar, function,
    C0.shape, Silmaril.Compile.C.ofIntegerType, Silmaril.Compile.C.ofCtype, Silmaril.Compile.C.usual, Silmaril.Compile.C.promote,
    C0.convTo, C0.arith, wi, wi1, range, bumped,
    Bind.bind, Except.bind, pure, Except.pure]

private theorem eval_accumulate (fuel n i : Nat) (env : C0.Env)
    (stores : Stores env n i) (hn : n ≤ 65535) (hi : i < n) :
    C0.evalE program (fuel + 4) function
      (intExpr (.compoundAssign (lvalue sSym) .add (read iSym))) (bumped env i) =
      .ok (triangular (i + 1), advanced env i) := by
  have hnext : i + 1 ≤ 65535 := (Nat.le_trans hi hn)
  have wi := wrap_signed32 (nat_signed hnext)
  have ws := wrap_signed32 (triangular_signed ((Nat.le_of_lt hi).trans hn))
  have wr := wrap_signed32 (triangular_signed hnext)
  have range : C0.inRange 4 true (triangular i + (i + 1 : Nat)) = true := by
    have h := triangular_signed hnext
    simpa [C0.inRange, Signed32, triangular] using h
  simp only [Nat.cast_add, Nat.cast_one, triangular] at wi wr range
  obtain ⟨_, _, hs⟩ := stores
  simp [C0.evalE, intExpr, Expression.node, Expression.annotation,
    Silmaril.Compile.C.typeOf, Silmaril.Compile.C.ofGenType, Silmaril.Compile.C.ofCtype,
    Silmaril.Compile.C.ofIntegerType,
    Silmaril.Compile.C.resolve, Silmaril.Compile.C.resolveIsBool,
    Silmaril.Compile.C.intLayout, Silmaril.Cerberus.Mem.Concrete.integerLayout,
    Silmaril.Cerberus.Mem.Concrete.baseWidth, intAnnot,
    C0.lvalSym, lvalue, read, C0.readVar, iSym, sSym, hs, C0.writeVar, function,
    C0.shape, Silmaril.Compile.C.usual, Silmaril.Compile.C.promote,
    C0.convTo, C0.arith, wi, ws, wr, range, bumped, advanced, triangular,
    Std.HashMap.getElem?_insert, Bind.bind, Except.bind, pure, Except.pure]

private theorem stores_advanced (env : C0.Env) (n i : Nat) (h : Stores env n i) :
    Stores (advanced env i) n (i + 1) := by
  obtain ⟨a, b, c⟩ := h
  unfold Stores advanced bumped
  simp only [Std.HashMap.getElem?_insert]
  simp only [a, Nat.cast_add, Nat.cast_one]
  trivial

private theorem loop_iteration (fuel n i : Nat) (env : C0.Env)
    (stores : Stores env n i) (hn : n ≤ 65535) (hi : i < n) :
    C0.loop program (fuel + 20) function none loopKont env =
      C0.loop program (fuel + 13) function none loopKont (advanced env i) := by
  rw [C0.loop]
  unfold loopKont
  rw [C0.step]
  change (match (do
    let (v, e) ← C0.evalE program (fuel + 18) function condition env
    pure (if v != 0 then C0.Next.running (some loopBody) loopKont
      else C0.Next.running none (.seq [returnSum] .stop), e)) with
    | .ok (.running f k, e) => C0.loop program (fuel + 19) function f k e
    | .ok (.returned v, e) => .ok (v, e)
    | .error e => .error e) = _
  rw [show fuel + 18 = (fuel + 14) + 4 by omega,
    eval_condition (fuel + 14) n i env stores hn (Nat.le_of_lt hi)]
  simp only [hi, ite_true, Bind.bind, Except.bind, pure, Except.pure]
  change C0.loop program (fuel + 19) function (some loopBody) loopKont env = _
  rw [C0.loop, C0.step]
  change C0.loop program (fuel + 18) function none
    (.seq [increment, accumulate] loopKont) env = _
  rw [C0.loop, C0.step]
  change C0.loop program (fuel + 17) function (some increment)
    (.seq [accumulate] loopKont) env = _
  rw [C0.loop]
  change (match (do
    let (_, e) ← C0.evalE program (fuel + 15) function
      (intExpr (.unary .postfixIncr (lvalue iSym))) env
    pure (C0.Next.running none (.seq [accumulate] loopKont), e)) with
    | .ok (.running f k, e) => C0.loop program (fuel + 16) function f k e
    | .ok (.returned v, e) => .ok (v, e)
    | .error e => .error e) = _
  rw [show fuel + 15 = (fuel + 11) + 4 by omega,
    eval_increment (fuel + 11) n i env stores hn hi]
  change C0.loop program (fuel + 16) function none (.seq [accumulate] loopKont) (bumped env i) = _
  rw [C0.loop, C0.step]
  change C0.loop program (fuel + 15) function (some accumulate) (.seq [] loopKont) (bumped env i) = _
  rw [C0.loop]
  change (match (do
    let (_, e) ← C0.evalE program (fuel + 13) function
      (intExpr (.compoundAssign (lvalue sSym) .add (read iSym))) (bumped env i)
    pure (C0.Next.running none (.seq [] loopKont), e)) with
    | .ok (.running f k, e) => C0.loop program (fuel + 14) function f k e
    | .ok (.returned v, e) => .ok (v, e)
    | .error e => .error e) = _
  rw [show fuel + 13 = (fuel + 9) + 4 by omega,
    eval_accumulate (fuel + 9) n i env stores hn hi]
  change C0.loop program (fuel + 14) function none (.seq [] loopKont) (advanced env i) = _
  rw [C0.loop, C0.step]
  rfl

private theorem loop_exit (fuel n : Nat) (env : C0.Env)
    (stores : Stores env n n) (hn : n ≤ 65535) :
    C0.loop program (fuel + 20) function none loopKont env = .ok (some (triangular n), env) := by
  rw [C0.loop]
  unfold loopKont
  rw [C0.step]
  change (match (do
    let (v, e) ← C0.evalE program (fuel + 18) function condition env
    pure (if v != 0 then C0.Next.running (some loopBody) loopKont
      else C0.Next.running none (.seq [returnSum] .stop), e)) with
    | .ok (.running f k, e) => C0.loop program (fuel + 19) function f k e
    | .ok (.returned v, e) => .ok (v, e)
    | .error e => .error e) = _
  rw [show fuel + 18 = (fuel + 14) + 4 by omega,
    eval_condition (fuel + 14) n n env stores hn (by omega)]
  simp only [Nat.lt_irrefl, ite_false]
  change C0.loop program (fuel + 19) function none (.seq [returnSum] .stop) env = _
  rw [C0.loop, C0.step]
  change C0.loop program (fuel + 18) function (some returnSum) (.seq [] .stop) env = _
  rw [C0.loop]
  change (match (do
    let (v, e) ← C0.evalE program (fuel + 16) function (read sSym) env
    pure (C0.Next.returned (some (← C0.convTo (.int 4 true) v)), e)) with
    | .ok (.running f k, e) => C0.loop program (fuel + 17) function f k e
    | .ok (.returned v, e) => .ok (v, e)
    | .error e => .error e) = _
  rw [show fuel + 16 = (fuel + 15) + 1 by omega,
    eval_read (fuel + 15) sSym env (triangular n) stores.2.2]
  simp [C0.convTo, wrap_signed32 (triangular_signed hn), Bind.bind, Except.bind, pure, Except.pure]

/-- Actual typed-Ail loop termination and result, for every admissible input. -/
theorem loop_total (remaining n i : Nat) (env : C0.Env)
    (stores : Stores env n i) (hn : n ≤ 65535) (hremaining : i + remaining = n) :
    ∃ finalState, C0.loop program (7 * remaining + 20) function none loopKont env =
      .ok (some (triangular n), finalState) ∧
      finalState.globals = env.globals ∧ finalState.out = env.out := by
  induction remaining generalizing i env with
  | zero =>
    have heq : i = n := by omega
    subst i
    exact ⟨env, loop_exit 0 n env stores hn, rfl, rfl⟩
  | succ k ih =>
    have hi : i < n := by omega
    obtain ⟨finalState, run, globals, output⟩ :=
      ih (i + 1) (advanced env i) (stores_advanced env n i stores) (by omega)
    refine ⟨finalState, ?_, globals, output⟩
    rw [show 7 * (k + 1) + 20 = (7 * k + 7) + 20 by omega,
      loop_iteration (7 * k + 7) n i env stores hn hi]
    convert run using 1

def entryState (initial : C0.Env) (n : Nat) : C0.Env :=
  { initial with locals := ({} : Std.HashMap Nat Int).insert 0 n }
def initialized (initial : C0.Env) (n : Nat) : C0.Env :=
  { entryState initial n with locals := ((entryState initial n).locals.insert 1 0).insert 2 0 }

set_option maxHeartbeats 2000000 in
private theorem declaration_step (fuel n : Nat) (initial : C0.Env) (k : C0.Kont) :
    C0.step program (fuel + 4) function (some initStatement) k (entryState initial n) =
      .ok (.running none k, initialized initial n) := by
  have wz : C0.wrap 4 true 0 = 0 := by decide +kernel
  simp only [C0.step, initStatement, stmt, Statement.node]
  simp only [List.forIn_cons, List.forIn_nil, function, iSym, sSym, Std.HashMap.getElem?_insert]
  simp [Silmaril.Compile.C.typeOf, Expression.annotation, intAnnot,
    Silmaril.Compile.C.ofGenType, Silmaril.Compile.C.resolve, Silmaril.Compile.C.resolveIsBool,
    Silmaril.Compile.C.intLayout, Silmaril.Cerberus.Mem.Concrete.integerLayout,
    Silmaril.Cerberus.Mem.Concrete.baseWidth, C0.evalE, literal, intExpr, Expression.node, C0.constVal,
    Silmaril.Compile.Forks.Csem.C.intConstValue,
    C0.convTo, wz, initialized,
    Bind.bind, Except.bind, pure, Except.pure]


private theorem body_entry (fuel n : Nat) (initial : C0.Env) :
    C0.loop program (fuel + 25) function (some body) .stop (entryState initial n) =
      C0.loop program (fuel + 20) function none loopKont (initialized initial n) := by
  rw [C0.loop, C0.step]
  change C0.loop program (fuel + 24) function none
    (.seq [initStatement, whileStatement, returnSum] .stop) (entryState initial n) = _
  rw [C0.loop, C0.step]
  change C0.loop program (fuel + 23) function (some initStatement)
    (.seq [whileStatement, returnSum] .stop) (entryState initial n) = _
  rw [C0.loop, show fuel + 22 = (fuel + 18) + 4 by omega, declaration_step]
  change C0.loop program (fuel + 22) function none
    (.seq [whileStatement, returnSum] .stop) (initialized initial n) = _
  rw [C0.loop, C0.step]
  change C0.loop program (fuel + 21) function (some whileStatement)
    (.seq [returnSum] .stop) (initialized initial n) = _
  rw [C0.loop, C0.step]
  rfl

/-- Universal actual C0 call: terminates, has no signed overflow, returns the
triangular sum and preserves the entire caller state (`assigns \nothing`). -/
theorem triangular_call (n : Nat) (initial : C0.Env) (hn : n ≤ 65535) :
    C0.callFn program (7 * n + 26) fSym [n] initial = .ok (triangular n, initial) := by
  have stores : Stores (initialized initial n) n 0 := by
    unfold Stores initialized entryState
    simp only [Std.HashMap.getElem?_insert]
    norm_num [triangular]
  obtain ⟨finalState, run, globals, output⟩ := loop_total n n 0 (initialized initial n) stores hn (by omega)
  have wn := wrap_signed32 (nat_signed hn)
  have wr := wrap_signed32 (triangular_signed hn)
  simp only [C0.callFn, program, fSym, Std.HashMap.getElem?_insert]
  simp only [function, List.length_cons, List.length_nil]
  simp [C0.convTo, wn, Bind.bind, Except.bind, pure, Except.pure]
  change (do
    let (r, e) ← C0.loop program (7 * n + 25) function (some body) .stop (entryState initial n)
    pure (C0.wrap 4 true (r.getD 0), { e with locals := initial.locals })) = _
  rw [body_entry, run]
  simp only [Bind.bind, Except.bind, pure, Except.pure, Option.getD_some, wr]
  have hg : finalState.globals = initial.globals := globals
  have ho : finalState.out = initial.out := output
  cases initial
  cases finalState
  simp_all

end Silmaril.Compile.C.Sem.HarborTriangular
