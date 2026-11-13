module

public import Silmaril.Compiler.Core.Source.StartupReach.Defs

/-! # Folding closed pure integer expressions

`eval doc fuel env p = some v` folds a closed pure Core expression `p` to a wire value `v`.
It covers integer literals and arithmetic (with `^`, which Cerberus's shift guards use), the
Cerberus guards (`catch_exceptional_condition`, `conv_int`, `wrapI`), `Specified`/`Unspecified`,
tuples, `let`, `case`, `if`, `are_compatible` on `void` and non-enum integer types (the checks
Cerberus elaborates around a call), `sizeof` of non-enum integer types (std.core's
`ctype_width`), and calls of pure functions (std.core's `conv_int`, `conv_loaded_int`,
`is_representable_integer`, `wrapI`, the implementation's functions), whose bodies are folded in
turn. It has no memory, no effects, no procedure calls and no control transfers: it is constant
folding of the pure integer fragment,
not an execution of the program. `undef` and every unsupported form give `none`. It uses no
definition of the Core dynamics or of the memory model, only syntax, `Map` and the LP64
integer bounds (`Mem.Concrete.integerBounds`); enum types are refused.

`eval_reaches`: when `eval` folds `p` to `v`, the Core dynamics reduces `p`, in any related
environment, under any continuation and from any memory, to `runtimeValue v`, without changing
memory.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Fold

open Silmaril.Cerberus Silmaril.Cerberus.Core

abbrev WVal := Value Codec.wireModel
abbrev WEnv := Map Sym WVal
abbrev PExp := Pexpr Codec.wireModel Unit Sym
abbrev Doc := File Codec.wireModel Unit Unit

/-- Simultaneous bindings, the first binding of a key winning (as the dynamics' `extendEnv`). -/
def extend (xs : List (Sym × WVal)) (env : WEnv) : WEnv :=
  xs.foldr (fun (s, v) acc => acc.insert s v) env

mutual
/-- Pattern matching on wire values, case for case the dynamics' `matchPattern`. -/
def matchP : Pattern Sym → WVal → Option (List (Sym × WVal))
  | .mk _ (.base (none, _)), _ => some []
  | .mk _ (.base (some s, _)), v => some [(s, v)]
  | .mk _ (.ctor .specified [p]), .loaded (.specified v) => matchP p (.object v)
  | .mk _ (.ctor .unspecified [p]), .loaded (.unspecified ty) => matchP p (.ctype ty)
  | .mk _ (.ctor .tuple ps), .tuple vs => matchPs ps vs
  | .mk _ (.ctor (.nil _) []), .list _ [] => some []
  | .mk _ (.ctor .cons [p, q]), .list ty (v :: vs) => do
      let xs ← matchP p v
      let ys ← matchP q (.list ty vs)
      pure (xs ++ ys)
  | _, _ => none

def matchPs : List (Pattern Sym) → List WVal → Option (List (Sym × WVal))
  | p :: ps, v :: vs => do
      let xs ← matchP p v
      let ys ← matchPs ps vs
      pure (xs ++ ys)
  | _, _ => some []
end

/-- The first branch whose pattern matches. -/
def select (v : WVal) : List (Pattern Sym × PExp) → Option (List (Sym × WVal) × PExp)
  | [] => none
  | (p, body) :: rest => match matchP p v with
    | some xs => some (xs, body)
    | none => select v rest

def integer (n : Int) : WVal := .object (.integer n)
def boolean (b : Bool) : WVal := if b then .true else .false

/-- The integer type of a C type; enums (whose bounds depend on the run's registrations) are
refused. -/
def intType : Ctype → Option IntegerType
  | .mk _ (.basic (.integer (.enum _))) => none
  | .mk _ (.basic (.integer ty)) => some ty
  | _ => none

def bounds (ty : IntegerType) : Option (Int × Int) :=
  match ty with
  | .enum _ => none
  | _ => Mem.Concrete.integerBounds ty

def wrap (lo hi n : Int) : Int :=
  let r := n % (hi - lo + 1)
  if r ≤ hi then r else r - (hi - lo + 1)

def intBin (op : BinOp) (x y : Int) : Option WVal :=
  match op with
  | .add => some (integer (x + y))
  | .sub => some (integer (x - y))
  | .mul => some (integer (x * y))
  | .exp => if 0 ≤ y && y ≤ 4611686018427387903 then some (integer (x ^ y.toNat)) else none
  | .div => some (integer (x.tdiv y))
  | .remT => if y != 0 then some (integer (x.tmod y)) else none
  | .remF => if y > 0 then some (integer (x % y)) else none
  | .eq => some (boolean (x == y))
  | .lt => some (boolean (x < y))
  | .le => some (boolean (x ≤ y))
  | .gt => some (boolean (x > y))
  | .ge => some (boolean (x ≥ y))
  | _ => none

def intOp (op : IntOp) (x y : Int) : Option Int :=
  match op with
  | .add => some (x + y)
  | .sub => some (x - y)
  | .mul => some (x * y)
  | .div => some (x.tdiv y)
  | .remT => if y != 0 then some (x.tmod y) else none
  | _ => none

/-- Binary operators on integers, Booleans and integer C types. -/
def bin (op : BinOp) : WVal → WVal → Option WVal
  | .object (.integer x), .object (.integer y) => intBin op x y
  | .ctype x, .ctype y => match op, intType x, intType y with
    | .eq, some a, some b => if (bounds a).isSome && (bounds b).isSome then some (boolean (a == b)) else none
    | _, _, _ => none
  | .true, .true => match op with | .and | .or => some .true | _ => none
  | .true, .false => match op with | .and => some .false | .or => some .true | _ => none
  | .false, .true => match op with | .and => some .false | .or => some .true | _ => none
  | .false, .false => match op with | .and | .or => some .false | _ => none
  | _, _ => none

/-- The constructors of the integer fragment. -/
def ctor (c : Ctor) (vs : List WVal) : Option WVal :=
  match c, vs with
  | .specified, [.object (.integer n)] => some (.loaded (.specified (.integer n)))
  | .unspecified, [.ctype ty] => some (.loaded (.unspecified ty))
  | .tuple, vs => some (.tuple vs)
  | .ivMin, [.ctype ty] => do let (lo, _) ← bounds (← intType ty); pure (integer lo)
  | .ivMax, [.ctype ty] => do let (_, hi) ← bounds (← intType ty); pure (integer hi)
  | .ivSizeof, [.ctype ty] => do
      let ity ← intType ty
      let _ ← bounds ity
      let (w, _) ← Mem.Concrete.integerLayout ity
      pure (integer w)
  | _, _ => none

def conv (ty : IntegerType) : WVal → Option WVal
  | .object (.integer n) => do
      let (lo, hi) ← bounds ty
      pure (integer (if ty == .bool then (if n == 0 then 0 else 1)
        else if lo ≤ n && n ≤ hi then n else wrap lo hi n))
  | _ => none

def catchInt (ty : IntegerType) (op : IntOp) : WVal → WVal → Option WVal
  | .object (.integer x), .object (.integer y) => do
      let (lo, hi) ← bounds ty
      let n ← intOp op x y
      if lo ≤ n && n ≤ hi then pure (integer n) else none
  | _, _ => none

def wrapInt (ty : IntegerType) (op : IntOp) : WVal → WVal → Option WVal
  | .object (.integer x), .object (.integer y) => do
      let (lo, hi) ← bounds ty
      let n ← intOp op x y
      pure (integer (wrap lo hi n))
  | _, _ => none

def notBool : WVal → Option WVal
  | .true => some .false
  | .false => some .true
  | _ => none

/-- `is_signed` (`signed = true`) and `is_unsigned` on integer C types. -/
def signedness (signed : Bool) : WVal → Option WVal
  | .ctype ty => do
      let ity ← intType ty
      let (_, s) ← Mem.Concrete.integerLayout ity
      let _ ← bounds ity
      pure (boolean (if signed then s else !s))
  | _ => none

/-- An integer type other than an enum. -/
def nonEnum : IntegerType → Option IntegerType
  | .enum _ => none
  | t => some t

/-- `are_compatible` on `void` and on integer types other than enums, whose normal forms
(`Core.normalizeInteger`) do not depend on the run's enum registrations. -/
def compat : WVal → WVal → Option WVal
  | .ctype (.mk _ .void), .ctype (.mk _ .void) => some .true
  | .ctype (.mk _ (.basic (.integer a))), .ctype (.mk _ (.basic (.integer b))) => do
      let a ← Core.normalizeInteger (← nonEnum a)
      let b ← Core.normalizeInteger (← nonEnum b)
      pure (boolean (a == b))
  | _, _ => none

/-- The parameters and body of a pure function, standard library first. -/
def funBody (doc : Doc) : Name Sym → Option (List Sym × PExp)
  | .sym s =>
      let decl := match doc.stdlib.lookup s with
        | some d => some d
        | none => doc.funs.lookup s
      match decl with
      | some (.function _ params body) => some (params.map Prod.fst, body)
      | _ => none
  | .impl c => match doc.impl.lookup c with
      | some (.function _ params body) => some (params.map Prod.fst, body)
      | _ => none

/-- Fold a closed pure expression; `fuel` bounds the depth of function calls and nesting. -/
def eval (doc : Doc) : Nat → WEnv → PExp → Option WVal
  | 0, _, _ => none
  | fuel+1, env, .mk _ _ e =>
    match e with
    | .val v => some v
    | .sym s => env.lookup s
    | .impl c => match doc.impl.lookup c with
      | some (.constant _ body) => eval doc fuel env body
      | _ => none
    | .ctor c ps => do ctor c (← ps.mapM (eval doc fuel env))
    | .op b p q => do bin b (← eval doc fuel env p) (← eval doc fuel env q)
    | .convInt ty p => do conv ty (← eval doc fuel env p)
    | .catchExceptionalCondition ty op p q => do
        catchInt ty op (← eval doc fuel env p) (← eval doc fuel env q)
    | .wrapI ty op p q => do wrapInt ty op (← eval doc fuel env p) (← eval doc fuel env q)
    | .not p => do notBool (← eval doc fuel env p)
    | .isSigned p => do signedness true (← eval doc fuel env p)
    | .isUnsigned p => do signedness false (← eval doc fuel env p)
    | .areCompatible p q => do compat (← eval doc fuel env p) (← eval doc fuel env q)
    | .call name ps => do
        let vs ← ps.mapM (eval doc fuel env)
        let (params, body) ← funBody doc name
        if params.length = vs.length then eval doc fuel (extend (params.zip vs) ∅) body else none
    | .let_ pat p body => do
        let xs ← matchP pat (← eval doc fuel env p)
        eval doc fuel (extend xs env) body
    | .case_ p bs => do
        let (xs, body) ← select (← eval doc fuel env p) bs
        eval doc fuel (extend xs env) body
    | .if_ c yes no => do
        match ← eval doc fuel env c with
        | .true => eval doc fuel env yes
        | .false => eval doc fuel env no
        | _ => none
    | _ => none

end Silmaril.Compile.Core.Verified.Fold
