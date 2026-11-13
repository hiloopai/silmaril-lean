module

public import Silmaril.ML.OCaml.Prim.Defs

/-!
# OCaml deep embedding: big-step semantics

`Eval ord st env x o st'` is a pretty-big-step relation (Charguéraud, ESOP
2013): extended terms `Ext` add intermediate forms, so that one premise
evaluates a subterm and the next continues with its outcome (`Ext.on`).
Exceptions propagate through the single rule `Eval.abort`, except at the
frames that catch them (`try`, `match … with exception`).

* **Store.** Mutable records, `ref`s and `bytes` are store cells; allocation
  is deterministic (`Store.alloc`).
* **Exceptions.** `exception E` and `let exception` allocate a fresh
  identity from `Store.nextExn`, so a generative functor applied twice
  defines two different exceptions.
* **Modules.** Structures evaluate their items in order into `Value.mod`,
  functors are closures over module expressions, coercions rebuild fields by
  position, and first-class modules are module values.
* **Evaluation order.** OCaml leaves the order of application arguments,
  tuple/constructor/record components and `let … and` bindings unspecified.
  `ord : Order` chooses it per node: `ord id n` is the order in which the `n`
  subterms of node `id` are evaluated. `Order.rtl` (right to left) is what
  `ocamlc`/`ocamlopt` without flambda do.
* **Divergence** is the absence of a derivation. Unspecified behaviour
  (`primExec` returning `none`, ill-typed configurations) has no rule: it is
  stuck, not an outcome.
-/

@[expose] public section
namespace Silmaril.ML.OCaml

/-- An evaluation order: for node `id` with `n` subterms, the order in which
they are evaluated (a permutation of `0 … n-1`). -/
abbrev Order := NodeId → Nat → List Nat

/-- Right to left, as `ocamlc` and `ocamlopt` (without flambda) do. -/
def Order.rtl : Order := fun _ n => (List.range n).reverse

/-- Left to right. -/
def Order.ltr : Order := fun _ n => List.range n

/-- The subterms in evaluation order. -/
def schedule (π : List Nat) (es : List Expr) : List Expr := π.map fun i => es.getD i default

/-- Values in evaluation order, put back in source order. -/
def unschedule (π : List Nat) (vs : List Value) : List Value :=
  (List.range π.length).map fun i => match π.idxOf? i with
    | some k => vs.getD k default
    | none => default

/-! ## Pattern matching -/

/-- The fields of a record value (immutable block or mutable cell). -/
def recordFields? (st : Store) : Value → Option (List Value)
  | .block _ vs => some vs
  | .loc l => match st.get? l with
    | some (.fields vs) => some vs
    | _ => none
  | _ => none

mutual
/-- Match a value against a pattern, returning the bindings. Exception
constructors are found through `env` (they may be generative); mutable
record fields are read from `st`. -/
def Pat.matches (env : Env) (st : Store) : Pat → Value → Option Env
  | .any, _ => some []
  | .var x, v => some [(x, v)]
  | .alias p x, v => (p.matches env st v).map ((x, v) :: ·)
  | .const c, v => if c.matches v then some [] else none
  | .tuple ps, .block 0 vs => Pat.matchesList env st ps vs
  | .ctor t [], .cconst u => if t = u then some [] else none
  | .ctor t (p :: ps), .block u vs => if t = u then Pat.matchesList env st (p :: ps) vs else none
  | .exnCtor path ps, .exn i _ args => match path.eval env st with
    | some (.exnTag j _) => if i = j then Pat.matchesList env st ps args else none
    | _ => none
  | .record fs, v => match recordFields? st v with
    | some vs => Pat.matchesFields env st fs vs
    | none => none
  | .or p q, v => match p.matches env st v with
    | some b => some b
    | none => q.matches env st v
  | _, _ => none

def Pat.matchesList (env : Env) (st : Store) : List Pat → List Value → Option Env
  | [], [] => some []
  | p :: ps, v :: vs => match p.matches env st v, Pat.matchesList env st ps vs with
    | some b, some bs => some (b ++ bs)
    | _, _ => none
  | _, _ => none

def Pat.matchesFields (env : Env) (st : Store) : List (Nat × Pat) → List Value → Option Env
  | [], _ => some []
  | (i, p) :: fs, vs => match vs[i]? with
    | some v => match p.matches env st v, Pat.matchesFields env st fs vs with
      | some b, some bs => some (b ++ bs)
      | _, _ => none
    | none => none
end

/-! ## Coercions -/

mutual
def Coercion.apply : Coercion → Value → Option Value
  | .id, v => some v
  | .struct cs, .mod fs => (Coercion.applyFields cs fs).map .mod
  | .struct _, _ => none
  | .functor a r, v => some (.fcoerce v a r)
  | .prim op, _ => some (.prim op [])

def Coercion.applyFields : List (Nat × Coercion) → List Value → Option (List Value)
  | [], _ => some []
  | (i, c) :: cs, fs => match fs[i]? with
    | some v => match c.apply v, Coercion.applyFields cs fs with
      | some w, some ws => some (w :: ws)
      | _, _ => none
    | none => none
end

/-! ## Extended terms -/

/-- First-order constructions applied to the values of the subterms. -/
inductive Build where
  | tuple
  | ctor (tag : Nat)
  | exnCtor (p : Path)
  | record (isMut : Bool)
  /-- Values: the new fields, then the base record. -/
  | recordWith (isMut : Bool) (n : Nat) (pos : List Nat)
  /-- Values: target, new value. -/
  | setField (pos : Nat)

def overwrite (base : List Value) : List Nat → List Value → List Value
  | i :: is, v :: vs => overwrite (base.set i v) is vs
  | _, _ => base

def Build.run (env : Env) (st : Store) : Build → List Value → Option (Outcome × Store)
  | .tuple, vs => some (.ret (.block 0 vs), st)
  | .ctor t, vs => some (.ret (.ctor t vs), st)
  | .exnCtor p, vs => match p.eval env st with
    | some (.exnTag i n) => some (.ret (.exn i n vs), st)
    | _ => none
  | .record false, vs => some (.ret (.block 0 vs), st)
  | .record true, vs => let (l, st') := st.alloc (.fields vs); some (.ret (.loc l), st')
  | .recordWith m n pos, vs => match vs.getLast? with
    | some base => match recordFields? st base with
      | some fs =>
        if fs.length = n then
          let fs' := overwrite fs pos vs.dropLast
          if m then let (l, st') := st.alloc (.fields fs'); some (.ret (.loc l), st')
          else some (.ret (.block 0 fs'), st)
        else none
      | none => none
    | none => none
  | .setField i, [.loc l, v] => (setCellField st l i v).map fun st' => (.ret .unit, st')
  | .setField _, _ => none

/-- What to do with the values of a list of subterms. -/
inductive ListK where
  | build (b : Build)
  /-- Values: function, then arguments. -/
  | app
  | let_ (id : NodeId) (ps : List Pat) (body : Expr)
  | letItem (id : NodeId) (ps : List Pat) (rest : List Item) (exports : List Ident)

/-- Continuation frames, waiting for the outcome of a subterm. -/
inductive Frame where
  | list (π : List Nat) (rest : List Expr) (acc : List Value) (k : ListK)
  | apply (args : List Value)
  | ite (t f : Expr)
  | seq (e : Expr)
  | match_ (id : NodeId) (cases exnCases : List Case)
  | try_ (cases : List Case)
  | guard (bnd : Env) (body : Expr) (v : Value) (cases : List Case) (fail : Outcome)
  | field (pos : Nat)
  | assert (file : String) (line col : Nat)
  | letModule (x : Ident) (body : Expr)
  | moduleItem (x : Ident) (rest : List Item) (exports : List Ident)
  | includeItem (xs : List Ident) (rest : List Item) (exports : List Ident)
  | evalItem (rest : List Item) (exports : List Ident)
  | unit (name : String) (rest : List CUnit)
  | mapArg (f : ModExpr)
  | mapFun (a : Value)
  | coerce (c : Coercion)

/-- Frames that handle exceptions. -/
def Frame.catches : Frame → Bool
  | .match_ _ _ (_ :: _) => true
  | .try_ _ => true
  | _ => false

inductive Ext where
  | e (x : Expr)
  | m (me : ModExpr)
  | items (its : List Item) (exports : List Ident)
  | units (us : List CUnit)
  /-- Evaluate `pending` in order, collecting values in `acc`. -/
  | list (π : List Nat) (pending : List Expr) (acc : List Value) (k : ListK)
  | apply (f : Value) (args : List Value)
  | mapply (f a : Value)
  /-- Try the cases in order; `fail` if none applies. -/
  | cases (v : Value) (cs : List Case) (fail : Outcome)
  | on (o : Outcome) (f : Frame)

def matchFailure (id : NodeId) : Outcome :=
  raiseNamed "Match_failure" [.block 0 [.ofString id.file, .ofInt id.line, .ofInt id.col]]

def assertFailure (file : String) (line col : Nat) : Outcome :=
  raiseNamed "Assert_failure" [.block 0 [.ofString file, .ofInt line, .ofInt col]]

/-- The exports of a structure, looked up in its final environment. -/
def lookupAll (env : Env) : List Ident → Option (List Value)
  | [] => some []
  | x :: xs => match env.lookup x, lookupAll env xs with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Bind `xs` to the first fields of an included module. -/
def includeEnv (xs : List Ident) (fs : List Value) : Option Env :=
  if xs.length ≤ fs.length then some (xs.zip fs) else none

def Value.includeFields? : Value → Option (List Value)
  | .mod fs => Option.some fs
  | _ => Option.none

/-! ## The relation -/

inductive Eval (ord : Order) : Store → Env → Ext → Outcome → Store → Prop where
  -- expressions
  | path {st env p v} : p.eval env st = some v → Eval ord st env (.e (.path p)) (.ret v) st
  | const {st env c} : Eval ord st env (.e (.const c)) (.ret c.toValue) st
  | prim {st env op} : Eval ord st env (.e (.prim op)) (.ret (.prim op [])) st
  | fn {st env x b} : Eval ord st env (.e (.fn x b)) (.ret (.clos env x b)) st
  | app {st env id f args o st'} :
      Eval ord st env (.list (ord id (args.length + 1))
        (schedule (ord id (args.length + 1)) (f :: args)) [] .app) o st' →
      Eval ord st env (.e (.app id f args)) o st'
  | let_ {st env id bs body o st'} :
      Eval ord st env (.list (ord id bs.length) (schedule (ord id bs.length) (bs.map (·.2))) []
        (.let_ id (bs.map (·.1)) body)) o st' →
      Eval ord st env (.e (.let_ id bs body)) o st'
  | letRec {st env bs body o st'} :
      Eval ord st (recEnv env bs) (.e body) o st' → Eval ord st env (.e (.letRec bs body)) o st'
  | match_ {st env id e cs ecs o st₁ o' st₂} :
      Eval ord st env (.e e) o st₁ → Eval ord st₁ env (.on o (.match_ id cs ecs)) o' st₂ →
      Eval ord st env (.e (.match_ id e cs ecs)) o' st₂
  | try_ {st env e cs o st₁ o' st₂} :
      Eval ord st env (.e e) o st₁ → Eval ord st₁ env (.on o (.try_ cs)) o' st₂ →
      Eval ord st env (.e (.try_ e cs)) o' st₂
  | tuple {st env id es o st'} :
      Eval ord st env (.list (ord id es.length) (schedule (ord id es.length) es) [] (.build .tuple))
        o st' → Eval ord st env (.e (.tuple id es)) o st'
  | ctor {st env id t es o st'} :
      Eval ord st env (.list (ord id es.length) (schedule (ord id es.length) es) [] (.build (.ctor t)))
        o st' → Eval ord st env (.e (.ctor id t es)) o st'
  | exnCtor {st env id p es o st'} :
      Eval ord st env (.list (ord id es.length) (schedule (ord id es.length) es) []
        (.build (.exnCtor p))) o st' → Eval ord st env (.e (.exnCtor id p es)) o st'
  | record {st env id m es o st'} :
      Eval ord st env (.list (ord id es.length) (schedule (ord id es.length) es) []
        (.build (.record m))) o st' → Eval ord st env (.e (.record id m es)) o st'
  | recordWith {st env id m n fs base o st'} :
      Eval ord st env (.list (ord id (fs.length + 1))
        (schedule (ord id (fs.length + 1)) (fs.map (·.2) ++ [base])) []
        (.build (.recordWith m n (fs.map (·.1))))) o st' →
      Eval ord st env (.e (.recordWith id m n fs base)) o st'
  | field {st env e pos o st₁ o' st₂} :
      Eval ord st env (.e e) o st₁ → Eval ord st₁ env (.on o (.field pos)) o' st₂ →
      Eval ord st env (.e (.field e pos)) o' st₂
  | setField {st env e₁ pos e₂ o st'} :
      Eval ord st env (.list [1, 0] [e₂, e₁] [] (.build (.setField pos))) o st' →
      Eval ord st env (.e (.setField e₁ pos e₂)) o st'
  | ite {st env c t f o st₁ o' st₂} :
      Eval ord st env (.e c) o st₁ → Eval ord st₁ env (.on o (.ite t f)) o' st₂ →
      Eval ord st env (.e (.ite c t f)) o' st₂
  | seq {st env a b o st₁ o' st₂} :
      Eval ord st env (.e a) o st₁ → Eval ord st₁ env (.on o (.seq b)) o' st₂ →
      Eval ord st env (.e (.seq a b)) o' st₂
  | assert {st env e file line col o st₁ o' st₂} :
      Eval ord st env (.e e) o st₁ → Eval ord st₁ env (.on o (.assert file line col)) o' st₂ →
      Eval ord st env (.e (.assert e file line col)) o' st₂
  | letExn {st env x body o st'} :
      Eval ord st.newExn.2 ((x, .exnTag st.newExn.1 x.name) :: env) (.e body) o st' →
      Eval ord st env (.e (.letExn x body)) o st'
  | letModule {st env x me body o st₁ o' st₂} :
      Eval ord st env (.m me) o st₁ → Eval ord st₁ env (.on o (.letModule x body)) o' st₂ →
      Eval ord st env (.e (.letModule x me body)) o' st₂
  | pack {st env me o st'} : Eval ord st env (.m me) o st' → Eval ord st env (.e (.pack me)) o st'
  -- module expressions
  | mpath {st env p v} : p.eval env st = some v → Eval ord st env (.m (.path p)) (.ret v) st
  | mstruct {st env its xs o st'} :
      Eval ord st env (.items its xs) o st' → Eval ord st env (.m (.struct its xs)) o st'
  | mfunctor {st env x b} : Eval ord st env (.m (.functor x b)) (.ret (.fctor env x b)) st
  | mapply {st env f a o st₁ o' st₂} :
      Eval ord st env (.m a) o st₁ → Eval ord st₁ env (.on o (.mapArg f)) o' st₂ →
      Eval ord st env (.m (.apply f a)) o' st₂
  | mapplyUnit {st env f o st₁ o' st₂} :
      Eval ord st env (.m f) o st₁ → Eval ord st₁ env (.on o (.mapFun .unit)) o' st₂ →
      Eval ord st env (.m (.applyUnit f)) o' st₂
  | mcoerce {st env me c o st₁ o' st₂} :
      Eval ord st env (.m me) o st₁ → Eval ord st₁ env (.on o (.coerce c)) o' st₂ →
      Eval ord st env (.m (.coerce me c)) o' st₂
  | munpack {st env e o st'} : Eval ord st env (.e e) o st' → Eval ord st env (.m (.unpack e)) o st'
  -- structure items
  | itemsNil {st env xs vs} : lookupAll env xs = some vs → Eval ord st env (.items [] xs) (.ret (.mod vs)) st
  | itemValue {st env id bs rest xs o st'} :
      Eval ord st env (.list (ord id bs.length) (schedule (ord id bs.length) (bs.map (·.2))) []
        (.letItem id (bs.map (·.1)) rest xs)) o st' →
      Eval ord st env (.items (.value id bs :: rest) xs) o st'
  | itemValueRec {st env bs rest xs o st'} :
      Eval ord st (recEnv env bs) (.items rest xs) o st' →
      Eval ord st env (.items (.valueRec bs :: rest) xs) o st'
  | itemExn {st env x rest xs o st'} :
      Eval ord st.newExn.2 ((x, .exnTag st.newExn.1 x.name) :: env) (.items rest xs) o st' →
      Eval ord st env (.items (.exn x :: rest) xs) o st'
  | itemExnRebind {st env x p v rest xs o st'} : p.eval env st = some v →
      Eval ord st ((x, v) :: env) (.items rest xs) o st' →
      Eval ord st env (.items (.exnRebind x p :: rest) xs) o st'
  | itemModule {st env x me rest xs o st₁ o' st₂} :
      Eval ord st env (.m me) o st₁ → Eval ord st₁ env (.on o (.moduleItem x rest xs)) o' st₂ →
      Eval ord st env (.items (.module x me :: rest) xs) o' st₂
  | itemInclude {st env me ys rest xs o st₁ o' st₂} :
      Eval ord st env (.m me) o st₁ → Eval ord st₁ env (.on o (.includeItem ys rest xs)) o' st₂ →
      Eval ord st env (.items (.include me ys :: rest) xs) o' st₂
  | itemEval {st env e rest xs o st₁ o' st₂} :
      Eval ord st env (.e e) o st₁ → Eval ord st₁ env (.on o (.evalItem rest xs)) o' st₂ →
      Eval ord st env (.items (.eval e :: rest) xs) o' st₂
  | itemPrimitive {st env x op rest xs o st'} :
      Eval ord st ((x, .prim op []) :: env) (.items rest xs) o st' →
      Eval ord st env (.items (.primitive x op :: rest) xs) o st'
  -- programs
  | unitsNil {st env} : Eval ord st env (.units []) (.ret .unit) st
  | unitsCons {st env u us o st₁ o' st₂} :
      Eval ord st [] (.items u.items u.exports) o st₁ →
      Eval ord st₁ env (.on o (.unit u.name us)) o' st₂ →
      Eval ord st env (.units (u :: us)) o' st₂
  -- lists of subterms
  | listCons {st env π e es acc k o st₁ o' st₂} :
      Eval ord st env (.e e) o st₁ → Eval ord st₁ env (.on o (.list π es acc k)) o' st₂ →
      Eval ord st env (.list π (e :: es) acc k) o' st₂
  | listBuild {st env π acc b o st'} : b.run env st (unschedule π acc) = some (o, st') →
      Eval ord st env (.list π [] acc (.build b)) o st'
  | listApp {st env π acc f args o st'} : unschedule π acc = f :: args →
      Eval ord st env (.apply f args) o st' → Eval ord st env (.list π [] acc .app) o st'
  | listLet {st env π acc id ps body bnd o st'} :
      Pat.matchesList env st ps (unschedule π acc) = some bnd →
      Eval ord st (bnd ++ env) (.e body) o st' → Eval ord st env (.list π [] acc (.let_ id ps body)) o st'
  | listLetFail {st env π acc id ps body} : Pat.matchesList env st ps (unschedule π acc) = none →
      Eval ord st env (.list π [] acc (.let_ id ps body)) (matchFailure id) st
  | listLetItem {st env π acc id ps rest xs bnd o st'} :
      Pat.matchesList env st ps (unschedule π acc) = some bnd →
      Eval ord st (bnd ++ env) (.items rest xs) o st' →
      Eval ord st env (.list π [] acc (.letItem id ps rest xs)) o st'
  | listLetItemFail {st env π acc id ps rest xs} :
      Pat.matchesList env st ps (unschedule π acc) = none →
      Eval ord st env (.list π [] acc (.letItem id ps rest xs)) (matchFailure id) st
  -- application
  | applyNil {st env f} : Eval ord st env (.apply f []) (.ret f) st
  | applyClos {st env cenv x b a as o st₁ o' st₂} :
      Eval ord st ((x, a) :: cenv) (.e b) o st₁ → Eval ord st₁ env (.on o (.apply as)) o' st₂ →
      Eval ord st env (.apply (.clos cenv x b) (a :: as)) o' st₂
  | applyRec {st env cenv bundle i f x b a as o st₁ o' st₂} : bundle[i]? = some (f, x, b) →
      Eval ord st ((x, a) :: recEnv cenv bundle) (.e b) o st₁ →
      Eval ord st₁ env (.on o (.apply as)) o' st₂ →
      Eval ord st env (.apply (.rclos cenv bundle i) (a :: as)) o' st₂
  | applyPrimPartial {st env op acc a as o st'} : acc.length + 1 < op.arity →
      Eval ord st env (.apply (.prim op (acc ++ [a])) as) o st' →
      Eval ord st env (.apply (.prim op acc) (a :: as)) o st'
  | applyPrim {st env op acc a as o st₁ o' st₂} : acc.length + 1 = op.arity →
      primExec op (acc ++ [a]) st = some (o, st₁) → Eval ord st₁ env (.on o (.apply as)) o' st₂ →
      Eval ord st env (.apply (.prim op acc) (a :: as)) o' st₂
  -- functor application
  | mapplyFctor {st env cenv x b a o st'} :
      Eval ord st ((x, a) :: cenv) (.m b) o st' → Eval ord st env (.mapply (.fctor cenv x b) a) o st'
  | mapplyCoerce {st env f c₁ c₂ a a' o st₁ o' st₂} : c₁.apply a = some a' →
      Eval ord st env (.mapply f a') o st₁ → Eval ord st₁ env (.on o (.coerce c₂)) o' st₂ →
      Eval ord st env (.mapply (.fcoerce f c₁ c₂) a) o' st₂
  -- case analysis
  | casesNil {st env v fail} : Eval ord st env (.cases v [] fail) fail st
  | casesSkip {st env v p g b cs fail o st'} : p.matches env st v = none →
      Eval ord st env (.cases v cs fail) o st' → Eval ord st env (.cases v ((p, g, b) :: cs) fail) o st'
  | casesMatch {st env v p b cs fail bnd o st'} : p.matches env st v = some bnd →
      Eval ord st (bnd ++ env) (.e b) o st' →
      Eval ord st env (.cases v ((p, none, b) :: cs) fail) o st'
  | casesGuard {st env v p g b cs fail bnd o st₁ o' st₂} : p.matches env st v = some bnd →
      Eval ord st (bnd ++ env) (.e g) o st₁ →
      Eval ord st₁ env (.on o (.guard bnd b v cs fail)) o' st₂ →
      Eval ord st env (.cases v ((p, some g, b) :: cs) fail) o' st₂
  -- continuations
  | abort {st env x f} : f.catches = false → Eval ord st env (.on (.exn x) f) (.exn x) st
  | onList {st env v π es acc k o st'} :
      Eval ord st env (.list π es (acc ++ [v]) k) o st' →
      Eval ord st env (.on (.ret v) (.list π es acc k)) o st'
  | onApply {st env v as o st'} :
      Eval ord st env (.apply v as) o st' → Eval ord st env (.on (.ret v) (.apply as)) o st'
  | onIte {st env v b t f o st'} : v.toBool? = some b →
      Eval ord st env (.e (if b then t else f)) o st' → Eval ord st env (.on (.ret v) (.ite t f)) o st'
  | onSeq {st env v e o st'} : Eval ord st env (.e e) o st' → Eval ord st env (.on (.ret v) (.seq e)) o st'
  | onMatch {st env v id cs ecs o st'} :
      Eval ord st env (.cases v cs (matchFailure id)) o st' →
      Eval ord st env (.on (.ret v) (.match_ id cs ecs)) o st'
  | onMatchExn {st env x id cs c ecs o st'} :
      Eval ord st env (.cases x (c :: ecs) (.exn x)) o st' →
      Eval ord st env (.on (.exn x) (.match_ id cs (c :: ecs))) o st'
  | onTry {st env v cs} : Eval ord st env (.on (.ret v) (.try_ cs)) (.ret v) st
  | onTryExn {st env x cs o st'} :
      Eval ord st env (.cases x cs (.exn x)) o st' → Eval ord st env (.on (.exn x) (.try_ cs)) o st'
  | onGuardTrue {st env v bnd b w cs fail o st'} : v.toBool? = some true →
      Eval ord st (bnd ++ env) (.e b) o st' →
      Eval ord st env (.on (.ret v) (.guard bnd b w cs fail)) o st'
  | onGuardFalse {st env v bnd b w cs fail o st'} : v.toBool? = some false →
      Eval ord st env (.cases w cs fail) o st' →
      Eval ord st env (.on (.ret v) (.guard bnd b w cs fail)) o st'
  | onField {st env v pos w} : getField? st v pos = some w →
      Eval ord st env (.on (.ret v) (.field pos)) (.ret w) st
  | onAssert {st env v b file line col} : v.toBool? = some b →
      Eval ord st env (.on (.ret v) (.assert file line col))
        (if b then .ret .unit else assertFailure file line col) st
  | onLetModule {st env v x body o st'} :
      Eval ord st ((x, v) :: env) (.e body) o st' →
      Eval ord st env (.on (.ret v) (.letModule x body)) o st'
  | onModuleItem {st env v x rest xs o st'} :
      Eval ord st ((x, v) :: env) (.items rest xs) o st' →
      Eval ord st env (.on (.ret v) (.moduleItem x rest xs)) o st'
  | onIncludeItem {st env v ys rest xs fs bnd o st'} : v.includeFields? = some fs →
      includeEnv ys fs = some bnd → Eval ord st (bnd ++ env) (.items rest xs) o st' →
      Eval ord st env (.on (.ret v) (.includeItem ys rest xs)) o st'
  | onEvalItem {st env v rest xs o st'} :
      Eval ord st env (.items rest xs) o st' → Eval ord st env (.on (.ret v) (.evalItem rest xs)) o st'
  | onUnit {st env v name us o st'} :
      Eval ord { st with globals := (name, v) :: st.globals } env (.units us) o st' →
      Eval ord st env (.on (.ret v) (.unit name us)) o st'
  | onMapArg {st env v f o st₁ o' st₂} :
      Eval ord st env (.m f) o st₁ → Eval ord st₁ env (.on o (.mapFun v)) o' st₂ →
      Eval ord st env (.on (.ret v) (.mapArg f)) o' st₂
  | onMapFun {st env v a o st'} :
      Eval ord st env (.mapply v a) o st' → Eval ord st env (.on (.ret v) (.mapFun a)) o st'
  | onCoerce {st env v c w} : c.apply v = some w →
      Eval ord st env (.on (.ret v) (.coerce c)) (.ret w) st

/-- Initialising a program: its units in link order, each a structure whose
value is recorded in `Store.globals`. -/
def Init (ord : Order) (p : Program) (st : Store) (o : Outcome) (st' : Store) : Prop :=
  Eval ord st [] (.units p) o st'

end Silmaril.ML.OCaml
