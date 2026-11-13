module

public import Silmaril.ML.OCaml.Sem.Defs

/-!
# A fuel-bounded interpreter for `Eval`

`interp ord n st env x` runs the rules of `Eval` with at most `n` nested
rule applications. It returns `ok o st'`, `outOfFuel`, or `stuck why` when
no rule applies (unspecified behaviour or an unsupported primitive), so a
stuck program is never confused with one that ran out of fuel.

`step f` is one layer of the interpreter, with recursive calls going to `f`;
each of its arms is one rule of `Eval`. Soundness, completeness and
monotonicity in the fuel are in `Silmaril.ML.OCaml.Interp.Thms`.
-/

@[expose] public section
namespace Silmaril.ML.OCaml

inductive Res where
  | ok (o : Outcome) (st : Store)
  | outOfFuel
  | stuck (why : String)

def Res.bind (r : Res) (k : Outcome → Store → Res) : Res :=
  match r with
  | .ok o st => k o st
  | .outOfFuel => .outOfFuel
  | .stuck w => .stuck w

def Res.ofOption {α : Type} (x : Option α) (why : String) (k : α → Res) : Res :=
  match x with
  | some a => k a
  | none => .stuck why

/-- `none ↦ n`, `some a ↦ k a`. -/
def Res.caseOption {α : Type} (x : Option α) (n : Res) (k : α → Res) : Res :=
  match x with
  | some a => k a
  | none => n

def consView {α : Type} : List α → Option (α × List α)
  | [] => none
  | a :: as => some (a, as)

/-- The comparison `acc.length + 1` against the arity, as an option. -/
def primArity (acc : List Value) (op : PrimOp) : Option Bool :=
  if acc.length + 1 < op.arity then some false
  else if acc.length + 1 = op.arity then some true else none

abbrev Rec := Store → Env → Ext → Res

/-- One layer of the interpreter: the rules of `Eval`, in the same order. -/
def step (f : Rec) (ord : Order) (st : Store) (env : Env) : Ext → Res
  -- expressions
  | .e (.path p) => Res.ofOption (p.eval env st) "unbound path" fun v => .ok (.ret v) st
  | .e (.const c) => .ok (.ret c.toValue) st
  | .e (.prim op) => .ok (.ret (.prim op [])) st
  | .e (.fn x b) => .ok (.ret (.clos env x b)) st
  | .e (.app id g args) =>
    f st env (.list (ord id (args.length + 1)) (schedule (ord id (args.length + 1)) (g :: args)) [] .app)
  | .e (.let_ id bs body) =>
    f st env (.list (ord id bs.length) (schedule (ord id bs.length) (bs.map (·.2))) []
      (.let_ id (bs.map (·.1)) body))
  | .e (.letRec bs body) => f st (recEnv env bs) (.e body)
  | .e (.match_ id e cs ecs) => (f st env (.e e)).bind fun o s => f s env (.on o (.match_ id cs ecs))
  | .e (.try_ e cs) => (f st env (.e e)).bind fun o s => f s env (.on o (.try_ cs))
  | .e (.tuple id es) =>
    f st env (.list (ord id es.length) (schedule (ord id es.length) es) [] (.build .tuple))
  | .e (.ctor id t es) =>
    f st env (.list (ord id es.length) (schedule (ord id es.length) es) [] (.build (.ctor t)))
  | .e (.exnCtor id p es) =>
    f st env (.list (ord id es.length) (schedule (ord id es.length) es) [] (.build (.exnCtor p)))
  | .e (.record id m es) =>
    f st env (.list (ord id es.length) (schedule (ord id es.length) es) [] (.build (.record m)))
  | .e (.recordWith id m n fs base) =>
    f st env (.list (ord id (fs.length + 1)) (schedule (ord id (fs.length + 1)) (fs.map (·.2) ++ [base]))
      [] (.build (.recordWith m n (fs.map (·.1)))))
  | .e (.field e pos) => (f st env (.e e)).bind fun o s => f s env (.on o (.field pos))
  | .e (.setField e₁ pos e₂) => f st env (.list [1, 0] [e₂, e₁] [] (.build (.setField pos)))
  | .e (.ite c t e) => (f st env (.e c)).bind fun o s => f s env (.on o (.ite t e))
  | .e (.seq a b) => (f st env (.e a)).bind fun o s => f s env (.on o (.seq b))
  | .e (.assert e file line col) =>
    (f st env (.e e)).bind fun o s => f s env (.on o (.assert file line col))
  | .e (.letExn x body) => f st.newExn.2 ((x, .exnTag st.newExn.1 x.name) :: env) (.e body)
  | .e (.letModule x me body) => (f st env (.m me)).bind fun o s => f s env (.on o (.letModule x body))
  | .e (.pack me) => f st env (.m me)
  -- module expressions
  | .m (.path p) => Res.ofOption (p.eval env st) "unbound module path" fun v => .ok (.ret v) st
  | .m (.struct its xs) => f st env (.items its xs)
  | .m (.functor x b) => .ok (.ret (.fctor env x b)) st
  | .m (.apply g a) => (f st env (.m a)).bind fun o s => f s env (.on o (.mapArg g))
  | .m (.applyUnit g) => (f st env (.m g)).bind fun o s => f s env (.on o (.mapFun .unit))
  | .m (.coerce me c) => (f st env (.m me)).bind fun o s => f s env (.on o (.coerce c))
  | .m (.unpack e) => f st env (.e e)
  -- structure items
  | .items [] xs => Res.ofOption (lookupAll env xs) "unbound export" fun vs => .ok (.ret (.mod vs)) st
  | .items (.value id bs :: rest) xs =>
    f st env (.list (ord id bs.length) (schedule (ord id bs.length) (bs.map (·.2))) []
      (.letItem id (bs.map (·.1)) rest xs))
  | .items (.valueRec bs :: rest) xs => f st (recEnv env bs) (.items rest xs)
  | .items (.exn x :: rest) xs => f st.newExn.2 ((x, .exnTag st.newExn.1 x.name) :: env) (.items rest xs)
  | .items (.exnRebind x p :: rest) xs =>
    Res.ofOption (p.eval env st) "unbound exception" fun v => f st ((x, v) :: env) (.items rest xs)
  | .items (.module x me :: rest) xs =>
    (f st env (.m me)).bind fun o s => f s env (.on o (.moduleItem x rest xs))
  | .items (.include me ys :: rest) xs =>
    (f st env (.m me)).bind fun o s => f s env (.on o (.includeItem ys rest xs))
  | .items (.eval e :: rest) xs => (f st env (.e e)).bind fun o s => f s env (.on o (.evalItem rest xs))
  | .items (.primitive x op :: rest) xs => f st ((x, .prim op []) :: env) (.items rest xs)
  -- programs
  | .units [] => .ok (.ret .unit) st
  | .units (u :: us) => (f st [] (.items u.items u.exports)).bind fun o s => f s env (.on o (.unit u.name us))
  -- lists of subterms
  | .list π (e :: es) acc k => (f st env (.e e)).bind fun o s => f s env (.on o (.list π es acc k))
  | .list π [] acc (.build b) => Res.ofOption (b.run env st (unschedule π acc)) "build" fun r => .ok r.1 r.2
  | .list π [] acc .app =>
    Res.ofOption (consView (unschedule π acc)) "application" fun r => f st env (.apply r.1 r.2)
  | .list π [] acc (.let_ id ps body) =>
    Res.caseOption (Pat.matchesList env st ps (unschedule π acc)) (.ok (matchFailure id) st)
      fun bnd => f st (bnd ++ env) (.e body)
  | .list π [] acc (.letItem id ps rest xs) =>
    Res.caseOption (Pat.matchesList env st ps (unschedule π acc)) (.ok (matchFailure id) st)
      fun bnd => f st (bnd ++ env) (.items rest xs)
  -- application
  | .apply v [] => .ok (.ret v) st
  | .apply (.clos cenv x b) (a :: as) =>
    (f st ((x, a) :: cenv) (.e b)).bind fun o s => f s env (.on o (.apply as))
  | .apply (.rclos cenv bundle i) (a :: as) =>
    Res.ofOption bundle[i]? "recursive closure" fun r =>
      (f st ((r.2.1, a) :: recEnv cenv bundle) (.e r.2.2)).bind fun o s => f s env (.on o (.apply as))
  | .apply (.prim op acc) (a :: as) =>
    Res.ofOption (primArity acc op) "arity" fun full =>
      if full then
        Res.ofOption (primExec op (acc ++ [a]) st) "primitive" fun r => f r.2 env (.on r.1 (.apply as))
      else f st env (.apply (.prim op (acc ++ [a])) as)
  | .apply _ (_ :: _) => .stuck "not a function"
  -- functor application
  | .mapply (.fctor cenv x b) a => f st ((x, a) :: cenv) (.m b)
  | .mapply (.fcoerce g c₁ c₂) a =>
    Res.ofOption (c₁.apply a) "coercion" fun a' =>
      (f st env (.mapply g a')).bind fun o s => f s env (.on o (.coerce c₂))
  | .mapply _ _ => .stuck "not a functor"
  -- case analysis
  | .cases _ [] fail => .ok fail st
  | .cases v ((p, g, b) :: cs) fail =>
    Res.caseOption (p.matches env st v) (f st env (.cases v cs fail)) fun bnd =>
      match g with
      | none => f st (bnd ++ env) (.e b)
      | some ge => (f st (bnd ++ env) (.e ge)).bind fun o s => f s env (.on o (.guard bnd b v cs fail))
  -- continuations
  | .on (.exn x) (.match_ _ _ (c :: ecs)) => f st env (.cases x (c :: ecs) (.exn x))
  | .on (.exn x) (.try_ cs) => f st env (.cases x cs (.exn x))
  | .on (.exn x) _ => .ok (.exn x) st
  | .on (.ret v) (.list π es acc k) => f st env (.list π es (acc ++ [v]) k)
  | .on (.ret v) (.apply as) => f st env (.apply v as)
  | .on (.ret v) (.ite t e) => Res.ofOption v.toBool? "if: not a boolean" fun b => f st env (.e (if b then t else e))
  | .on (.ret _) (.seq e) => f st env (.e e)
  | .on (.ret v) (.match_ id cs _) => f st env (.cases v cs (matchFailure id))
  | .on (.ret v) (.try_ _) => .ok (.ret v) st
  | .on (.ret v) (.guard bnd b w cs fail) =>
    Res.ofOption v.toBool? "guard: not a boolean" fun c =>
      if c then f st (bnd ++ env) (.e b) else f st env (.cases w cs fail)
  | .on (.ret v) (.field pos) => Res.ofOption (getField? st v pos) "field" fun w => .ok (.ret w) st
  | .on (.ret v) (.assert file line col) =>
    Res.ofOption v.toBool? "assert: not a boolean" fun b =>
      .ok (if b then .ret .unit else assertFailure file line col) st
  | .on (.ret v) (.letModule x body) => f st ((x, v) :: env) (.e body)
  | .on (.ret v) (.moduleItem x rest xs) => f st ((x, v) :: env) (.items rest xs)
  | .on (.ret v) (.includeItem ys rest xs) =>
    Res.ofOption v.includeFields? "include: not a structure" fun fs =>
      Res.ofOption (includeEnv ys fs) "include: too few fields" fun bnd => f st (bnd ++ env) (.items rest xs)
  | .on (.ret _) (.evalItem rest xs) => f st env (.items rest xs)
  | .on (.ret v) (.unit name us) => f { st with globals := (name, v) :: st.globals } env (.units us)
  | .on (.ret v) (.mapArg g) => (f st env (.m g)).bind fun o s => f s env (.on o (.mapFun v))
  | .on (.ret v) (.mapFun a) => f st env (.mapply v a)
  | .on (.ret v) (.coerce c) => Res.ofOption (c.apply v) "coercion" fun w => .ok (.ret w) st

/-- The interpreter: `n` bounds the depth of the derivation it builds. -/
def interp (ord : Order) : Nat → Rec
  | 0, _, _, _ => .outOfFuel
  | n + 1, st, env, x => step (interp ord n) ord st env x

/-- Run an expression in the empty environment. -/
def run (ord : Order) (fuel : Nat) (st : Store) (e : Expr) : Res := interp ord fuel st [] (.e e)

/-- Initialise a program. -/
def initProg (ord : Order) (fuel : Nat) (p : Program) (st : Store := {}) : Res :=
  interp ord fuel st [] (.units p)

end Silmaril.ML.OCaml
