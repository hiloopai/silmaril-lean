module

public import Silmaril.Wasm.Numerics.Float

/-!
# A structured numeric Wasm fragment

The source language of the Wasm lambda-SSA dialect: integer (`i32`/`i64`)
code over locals, shaped like Binaryen's folded `BExpr` trees.

* Values `WVal` are tagged `i32`/`i64` bit vectors. Arithmetic is silmaril's
  (`Silmaril.Wasm.Numerics.intUnOp`, `intBinOp`, `intTestOp`, `intRelOp`,
  `convert`); nothing is redefined here.
* `Op` collects the value operators: constants, unary/test/conversion
  (`UnOp`), binary/compare (`BinOp`) and `select`. `Op.eval` returns
  `some (.val v)`, `some .trap` (division/remainder by zero, signed overflow),
  or `none` (ill-typed operands).
* `Expr` mirrors `BExpr`: an operator applied to its operand trees, locals,
  `drop`, `nop`, `unreachable`, `block`/`loop`/`if` with an optional integer
  result type, and `br`/`br_if`/`return` with their (at most one) value operand.
  For `brIf` the last operand is the condition.

The semantics (`Exec`, `Args`, `Seq`) is big-step and relational. An
outcome `Out α` is normal completion with the new locals, a branch to a de
Bruijn label with the locals and the carried value, a return, or a trap.
Divergence has no derivation; ill-typed code is stuck (no derivation). Locals
are untyped (`local.set` stores any `WVal`, out-of-range writes are ignored,
out-of-range reads are stuck). `FragFunc.Run` runs a function body on its
arguments followed by zero-initialised locals.

Not covered: floats, memory, globals, calls, tables, `br_table`, exceptions,
GC, SIMD, multi-value blocks and block parameters.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm

/-- A runtime integer value. -/
inductive WVal where
  | i32 (x : BitVec 32)
  | i64 (x : BitVec 64)
  deriving DecidableEq, Repr

namespace WVal

/-- The value of type `t` with bits `x`. -/
def ofInt : (t : IntType) → BitVec t.width → WVal
  | .i32, x => .i32 x
  | .i64, x => .i64 x

/-- The bits of a value of type `t`. -/
def asInt : (t : IntType) → WVal → Option (BitVec t.width)
  | .i32, .i32 x => some x
  | .i64, .i64 x => some x
  | _, _ => none

/-- The type of a value. -/
def type : WVal → IntType
  | .i32 _ => .i32
  | .i64 _ => .i64

/-- The default (zero) value of a type. -/
def zero : IntType → WVal
  | .i32 => .i32 0
  | .i64 => .i64 0

/-- An `i32` condition. -/
def truthy : WVal → Option Bool
  | .i32 x => some (x != 0)
  | .i64 _ => none

@[simp] theorem asInt_ofInt (t : IntType) (x : BitVec t.width) : (ofInt t x).asInt t = some x := by
  cases t <;> rfl

theorem eq_ofInt_of_asInt {t : IntType} {v : WVal} {x : BitVec t.width}
    (h : v.asInt t = some x) : v = ofInt t x := by
  cases t <;> cases v <;> simp only [asInt, reduceCtorEq] at h <;>
    exact congrArg _ (Option.some.inj h)

end WVal

/-- Unary operators: integer unary, `eqz`, `i32.wrap_i64` and `i64.extend_i32_{s,u}`. -/
inductive UnOp where
  | int (t : IntType) (op : IntUnOp)
  | test (t : IntType)
  | wrap
  | extend (sign : Signedness)
  deriving DecidableEq, Repr

/-- Binary integer operators and comparisons. -/
inductive BinOp where
  | int (t : IntType) (op : IntBinOp)
  | rel (t : IntType) (op : IntRelOp)
  deriving DecidableEq, Repr

/-- Value operators. Their operands come from the argument list in order. -/
inductive Op where
  | const (v : WVal)
  | un (op : UnOp)
  | bin (op : BinOp)
  /-- `select a b c`: `a` if `c ≠ 0`, else `b`. -/
  | select
  deriving DecidableEq, Repr

/-- The result of a value operator. -/
inductive Res where
  | val (v : WVal)
  | trap
  deriving DecidableEq, Repr

/-- Unary operators, by silmaril's integer numerics. -/
def UnOp.eval : UnOp → WVal → Option WVal
  | .int t op, v => (v.asInt t).map fun x => .ofInt t (Numerics.intUnOp t op x)
  | .test t, v => (v.asInt t).map fun x => .i32 (Numerics.intTestOp t .eqz x)
  | .wrap, .i64 x =>
      match Numerics.convert .wrap x with
      | .ok y => some (.i32 y)
      | .error _ => none
  | .extend s, .i32 x =>
      match Numerics.convert (.extend s) x with
      | .ok y => some (.i64 y)
      | .error _ => none
  | _, _ => none

/-- Binary operators, by silmaril's integer numerics; division traps. -/
def BinOp.eval : BinOp → WVal → WVal → Option Res
  | .int t op, a, b =>
      match a.asInt t, b.asInt t with
      | some x, some y =>
          match Numerics.intBinOp t op x y with
          | .ok z => some (.val (.ofInt t z))
          | .error _ => some .trap
      | _, _ => none
  | .rel t op, a, b =>
      match a.asInt t, b.asInt t with
      | some x, some y => some (.val (.i32 (Numerics.intRelOp t op x y)))
      | _, _ => none

/-- Operators on their argument lists. -/
def Op.eval : Op → List WVal → Option Res
  | .const v, [] => some (.val v)
  | .un o, [a] => (o.eval a).map .val
  | .bin o, [a, b] => o.eval a b
  | .select, [a, b, c] => c.truthy.map fun t => .val (if t then a else b)
  | _, _ => none

/-- The operators that may trap: integer division and remainder. -/
def Op.mayTrap : Op → Bool
  | .bin (.int _ (.div _)) | .bin (.int _ (.rem _)) => true
  | _ => false

/-- The number of operands. -/
def Op.arity : Op → Nat
  | .const _ => 0
  | .un _ => 1
  | .bin _ => 2
  | .select => 3

/-- The fragment's expressions, shaped like Binaryen's folded trees. -/
inductive Expr where
  | op (o : Op) (args : List Expr)
  | localGet (i : Nat)
  | localSet (i : Nat) (e : Expr)
  | localTee (i : Nat) (e : Expr)
  | drop (e : Expr)
  | nop
  | unreachable
  | block (ty : Option IntType) (body : List Expr)
  | loop (ty : Option IntType) (body : List Expr)
  | if_ (ty : Option IntType) (cond : Expr) (thn els : List Expr)
  /-- `br l` with its (at most one) value operand. -/
  | br (l : Nat) (args : List Expr)
  /-- `br_if l`; the last operand is the condition. -/
  | brIf (l : Nat) (args : List Expr)
  | return_ (args : List Expr)
  deriving Repr, Inhabited

/-- Outcomes: normal completion with the locals and a result, a branch to a
label with the locals and the carried value, a return, or a trap. -/
inductive Out (α : Type) where
  | ok (ls : List WVal) (a : α)
  | brk (l : Nat) (ls : List WVal) (r : Option WVal)
  | ret (r : Option WVal)
  | trap
  deriving DecidableEq, Repr

namespace Out

variable {α β : Type}

/-- Abrupt (non-normal) outcomes. -/
def Abrupt : Out α → Prop
  | .ok .. => False
  | _ => True

/-- Change the result type of an abrupt outcome (normal outcomes become traps;
only used on abrupt ones). -/
def cast : Out α → Out β
  | .ok .. => .trap
  | .brk l ls r => .brk l ls r
  | .ret r => .ret r
  | .trap => .trap

@[simp] theorem cast_cast (o : Out α) (h : o.Abrupt) : (o.cast : Out β).cast = o := by
  cases o <;> simp_all [cast, Abrupt]

theorem cast_abrupt (o : Out α) (h : o.Abrupt) : (o.cast : Out β).Abrupt := by
  cases o <;> simp_all [cast, Abrupt]

end Out

/-- The result of a block of type `ty`: a typed block keeps its value. -/
def blockRes (ty : Option IntType) (r : Option WVal) : Option WVal :=
  if ty.isSome then r else none

/-- A typed block must receive a value. -/
def BlockOk (ty : Option IntType) (r : Option WVal) : Prop := ty.isSome → r.isSome

/-- How a structured construct of type `ty` completes, given its body's outcome:
fallthrough and a branch to its own label continue after it. -/
inductive BlockExit (ty : Option IntType) : Out (Option WVal) → Out (Option WVal) → Prop where
  | ok {ls r} : BlockOk ty r → BlockExit ty (.ok ls r) (.ok ls (blockRes ty r))
  | brk0 {ls r} : BlockOk ty r → BlockExit ty (.brk 0 ls r) (.ok ls (blockRes ty r))
  | brk {l ls r} : BlockExit ty (.brk (l + 1) ls r) (.brk l ls r)
  | ret {r} : BlockExit ty (.ret r) (.ret r)
  | trap : BlockExit ty .trap .trap

/-- How a loop of type `ty` completes, except for a branch to its own label. -/
inductive LoopExit (ty : Option IntType) : Out (Option WVal) → Out (Option WVal) → Prop where
  | ok {ls r} : BlockOk ty r → LoopExit ty (.ok ls r) (.ok ls (blockRes ty r))
  | brk {l ls r} : LoopExit ty (.brk (l + 1) ls r) (.brk l ls r)
  | ret {r} : LoopExit ty (.ret r) (.ret r)
  | trap : LoopExit ty .trap .trap

mutual

/-- Big-step execution of an expression on the locals `ls`. -/
inductive Exec : List WVal → Expr → Out (Option WVal) → Prop where
  | op {ls ls' o args vs v} : Args ls args (.ok ls' vs) → o.eval vs = some (.val v) →
      Exec ls (.op o args) (.ok ls' (some v))
  | op_trap {ls ls' o args vs} : Args ls args (.ok ls' vs) → o.eval vs = some .trap →
      Exec ls (.op o args) .trap
  | op_abrupt {ls o args out} : Args ls args out → out.Abrupt → Exec ls (.op o args) out.cast
  | localGet {ls i v} : ls[i]? = some v → Exec ls (.localGet i) (.ok ls (some v))
  | localSet {ls ls' i e v} : Exec ls e (.ok ls' (some v)) →
      Exec ls (.localSet i e) (.ok (ls'.set i v) none)
  | localSet_abrupt {ls i e out} : Exec ls e out → out.Abrupt → Exec ls (.localSet i e) out
  | localTee {ls ls' i e v} : Exec ls e (.ok ls' (some v)) →
      Exec ls (.localTee i e) (.ok (ls'.set i v) (some v))
  | localTee_abrupt {ls i e out} : Exec ls e out → out.Abrupt → Exec ls (.localTee i e) out
  | drop {ls ls' e r} : Exec ls e (.ok ls' r) → Exec ls (.drop e) (.ok ls' none)
  | drop_abrupt {ls e out} : Exec ls e out → out.Abrupt → Exec ls (.drop e) out
  | nop {ls} : Exec ls .nop (.ok ls none)
  | unreachable {ls} : Exec ls .unreachable .trap
  | block {ls ty body out out'} : Seq ls none body out → BlockExit ty out out' →
      Exec ls (.block ty body) out'
  | loop {ls ty body out out'} : Seq ls none body out → LoopExit ty out out' →
      Exec ls (.loop ty body) out'
  | loop_back {ls ls' ty body r out} : Seq ls none body (.brk 0 ls' r) →
      Exec ls' (.loop ty body) out → Exec ls (.loop ty body) out
  | if_ {ls ls₁ ty c t e cv b out out'} : Exec ls c (.ok ls₁ (some cv)) → cv.truthy = some b →
      Seq ls₁ none (if b then t else e) out → BlockExit ty out out' →
      Exec ls (.if_ ty c t e) out'
  | if_abrupt {ls ty c t e out} : Exec ls c out → out.Abrupt → Exec ls (.if_ ty c t e) out
  | br {ls ls' l args vs} : Args ls args (.ok ls' vs) → Exec ls (.br l args) (.brk l ls' vs.head?)
  | br_abrupt {ls l args out} : Args ls args out → out.Abrupt → Exec ls (.br l args) out.cast
  | brIf {ls ls' l args vs c b} : Args ls args (.ok ls' vs) → vs.getLast? = some c →
      c.truthy = some b →
      Exec ls (.brIf l args)
        (if b then .brk l ls' vs.dropLast.head? else .ok ls' vs.dropLast.head?)
  | brIf_abrupt {ls l args out} : Args ls args out → out.Abrupt → Exec ls (.brIf l args) out.cast
  | return_ {ls ls' args vs} : Args ls args (.ok ls' vs) → Exec ls (.return_ args) (.ret vs.head?)
  | return_abrupt {ls args out} : Args ls args out → out.Abrupt →
      Exec ls (.return_ args) out.cast

/-- Operands, left to right; each must produce a value. -/
inductive Args : List WVal → List Expr → Out (List WVal) → Prop where
  | nil {ls} : Args ls [] (.ok ls [])
  | cons {ls ls₁ ls₂ e es v vs} : Exec ls e (.ok ls₁ (some v)) → Args ls₁ es (.ok ls₂ vs) →
      Args ls (e :: es) (.ok ls₂ (v :: vs))
  | head_abrupt {ls e es out} : Exec ls e out → out.Abrupt → Args ls (e :: es) out.cast
  | tail_abrupt {ls ls₁ e es v out} : Exec ls e (.ok ls₁ (some v)) → Args ls₁ es out →
      out.Abrupt → Args ls (e :: es) out

/-- A body, left to right, carrying the result of the last expression so far. -/
inductive Seq : List WVal → Option WVal → List Expr → Out (Option WVal) → Prop where
  | nil {ls r} : Seq ls r [] (.ok ls r)
  | cons {ls ls₁ r r₁ e es out} : Exec ls e (.ok ls₁ r₁) → Seq ls₁ r₁ es out →
      Seq ls r (e :: es) out
  | abrupt {ls r e es out} : Exec ls e out → out.Abrupt → Seq ls r (e :: es) out

end

/-- A function of the fragment. -/
structure FragFunc where
  params : List IntType
  locals : List IntType
  result : Option IntType
  body : List Expr
  deriving Repr

/-- Observable outcomes of a function call. -/
inductive FOut where
  | ret (r : Option WVal)
  | trap
  deriving DecidableEq, Repr

/-- The call outcome of a body outcome; the function body is label `0`. -/
def funcExit (res : Option IntType) : Out (Option WVal) → Option FOut
  | .ok _ r | .brk 0 _ r | .ret r => some (.ret (blockRes res r))
  | .trap => some .trap
  | .brk (_ + 1) _ _ => none

/-- The initial locals of a call. -/
def FragFunc.initLocals (f : FragFunc) (args : List WVal) : List WVal :=
  args ++ f.locals.map WVal.zero

/-- Terminating runs of a function: arguments of the parameter types, then the
body on the arguments and zero-initialised locals. -/
def FragFunc.Run (f : FragFunc) (args : List WVal) (o : FOut) : Prop :=
  args.map WVal.type = f.params ∧
    ∃ out, Seq (f.initLocals args) none f.body out ∧ funcExit f.result out = some o

/-! ## A fuel interpreter

`evalE`, `evalArgs`, `evalSeq` compute the same outcomes with fuel (`none`:
out of fuel or stuck). Used for testing; soundness is in `Thms`. -/

mutual

def evalE : Nat → List WVal → Expr → Option (Out (Option WVal))
  | 0, _, _ => none
  | n + 1, ls, e =>
    match e with
    | .op o args =>
        match evalArgs n ls args with
        | some (.ok ls' vs) =>
            match o.eval vs with
            | some (.val v) => some (.ok ls' (some v))
            | some .trap => some .trap
            | none => none
        | some out => some out.cast
        | none => none
    | .localGet i => ls[i]?.map fun v => .ok ls (some v)
    | .localSet i e =>
        match evalE n ls e with
        | some (.ok ls' (some v)) => some (.ok (ls'.set i v) none)
        | some (.ok _ none) => none
        | r => r
    | .localTee i e =>
        match evalE n ls e with
        | some (.ok ls' (some v)) => some (.ok (ls'.set i v) (some v))
        | some (.ok _ none) => none
        | r => r
    | .drop e =>
        match evalE n ls e with
        | some (.ok ls' _) => some (.ok ls' none)
        | r => r
    | .nop => some (.ok ls none)
    | .unreachable => some .trap
    | .block ty body => (evalSeq n ls none body).bind (blockExit ty)
    | .loop ty body =>
        match evalSeq n ls none body with
        | some (.brk 0 ls' _) => evalE n ls' (.loop ty body)
        | some out => loopExit ty out
        | none => none
    | .if_ ty c t el =>
        match evalE n ls c with
        | some (.ok ls₁ (some cv)) =>
            match cv.truthy with
            | some b => (evalSeq n ls₁ none (if b then t else el)).bind (blockExit ty)
            | none => none
        | some (.ok _ none) => none
        | r => r
    | .br l args =>
        match evalArgs n ls args with
        | some (.ok ls' vs) => some (.brk l ls' vs.head?)
        | some out => some out.cast
        | none => none
    | .brIf l args =>
        match evalArgs n ls args with
        | some (.ok ls' vs) =>
            match vs.getLast? with
            | some c =>
                c.truthy.map fun b =>
                  if b then .brk l ls' vs.dropLast.head? else .ok ls' vs.dropLast.head?
            | none => none
        | some out => some out.cast
        | none => none
    | .return_ args =>
        match evalArgs n ls args with
        | some (.ok _ vs) => some (.ret vs.head?)
        | some out => some out.cast
        | none => none
where
  blockExit (ty : Option IntType) : Out (Option WVal) → Option (Out (Option WVal))
    | .ok ls r | .brk 0 ls r =>
        if ty.isSome && r.isNone then none else some (.ok ls (blockRes ty r))
    | .brk (l + 1) ls r => some (.brk l ls r)
    | .ret r => some (.ret r)
    | .trap => some .trap
  loopExit (ty : Option IntType) : Out (Option WVal) → Option (Out (Option WVal))
    | .ok ls r => if ty.isSome && r.isNone then none else some (.ok ls (blockRes ty r))
    | .brk 0 _ _ => none
    | .brk (l + 1) ls r => some (.brk l ls r)
    | .ret r => some (.ret r)
    | .trap => some .trap

def evalArgs : Nat → List WVal → List Expr → Option (Out (List WVal))
  | 0, _, _ => none
  | _ + 1, ls, [] => some (.ok ls [])
  | n + 1, ls, e :: es =>
    match evalE n ls e with
    | some (.ok ls₁ (some v)) =>
        match evalArgs n ls₁ es with
        | some (.ok ls₂ vs) => some (.ok ls₂ (v :: vs))
        | r => r
    | some (.ok _ none) => none
    | some out => some out.cast
    | none => none

def evalSeq : Nat → List WVal → Option WVal → List Expr → Option (Out (Option WVal))
  | 0, _, _, _ => none
  | _ + 1, ls, r, [] => some (.ok ls r)
  | n + 1, ls, _, e :: es =>
    match evalE n ls e with
    | some (.ok ls₁ r₁) => evalSeq n ls₁ r₁ es
    | r => r

end

/-- Run a function with fuel. -/
def FragFunc.eval (fuel : Nat) (f : FragFunc) (args : List WVal) : Option FOut :=
  if args.map WVal.type = f.params then
    (evalSeq fuel (f.initLocals args) none f.body).bind (funcExit f.result)
  else none

end Silmaril.Wasm.SSA
