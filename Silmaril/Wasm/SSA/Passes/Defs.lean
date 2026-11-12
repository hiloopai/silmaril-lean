module

public import Silmaril.Wasm.SSA.Dialect.Defs

/-!
# SSA optimisation passes on the Wasm dialect

Two transformations of regions, both computable:

* `simpR cfg F T r`, a forward simplifier over **facts** and **types**. A
  fact for variable `i` is a term that evaluates to the value of `i` in the
  environment above `i`'s binding (so it is shift invariant); a type for `i`
  says that `i` holds an atom of that type. Each `let₁` records its
  simplified value and, when it is static, its type (`stTy`); the parameters'
  types seed `T` (`SFunc.simp`). The flags of `SimpCfg` select:
  - `fold` (constant propagation and folding): variables with constant facts
    become constants; operators, conditions and trapping operators on
    constant arguments are evaluated; a `case` on a known injection becomes a
    `let₁` (branch folding);
  - `alg` (algebraic simplification of integer operators **whose two operands
    are typed variables or constants of the operator's type** (`atomTy`):
    `x+0`, `x-0`, `0+x`, `x*1`, `1*x`, `x*0`, `x&-1`, `x&0`, `x|0`, `x^0`,
    shifts by `0`, `x-x`, `x^x`, `x&x`, `x|x`, `x==x`, `x!=x`; division by a
    constant that cannot trap becomes the non-trapping operator);
  - `copy` (copy propagation): uses of a variable bound to another variable
    are replaced by that variable;
  - `cse` (common subexpressions): an operator term already bound (as a fact)
    in scope is replaced by that variable.
* `dce r` removes unused bindings of **total** terms (`Tm.total`: variables,
  `()`, constants, pairs and injections of those), and unused `let₂` of a
  pair of total terms. Unused operator bindings are kept, since they may be
  stuck.

`Thms` proves that the input and output have the same evaluations (both
directions). The typing guard and the totality restriction are what make the
backward direction hold: without them an ill-typed (stuck) input could become
a terminating output.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm (IntType IntBinOp IntRelOp Signedness)
open Silmaril.Isotope.LambdaSSA (Tm Region)

/-- The constant term for a value. -/
def constTm (w : WVal) : Tm Prim := .op (.op (.const w)) .unit

/-- A constant term's value. -/
def constOf? : Tm Prim → Option WVal
  | .op (.op (.const w)) .unit => some w
  | _ => none

/-- Decode an argument tuple of terms. -/
def tmArgs? : Tm Prim → Option (List (Tm Prim))
  | .unit => some []
  | .pair a r => (tmArgs? r).map (a :: ·)
  | _ => none

/-- Encode a list of terms as an argument tuple. -/
def tmTuple : List (Tm Prim) → Tm Prim
  | [] => .unit
  | a :: as => .pair a (tmTuple as)

/-- Flags selecting the simplifications. -/
structure SimpCfg where
  fold : Bool := true
  alg : Bool := true
  copy : Bool := true
  cse : Bool := true
  deriving DecidableEq, Repr

/-- Facts, indexed by de Bruijn index. -/
abbrev Facts := List (Option (Tm Prim))

/-- The fact for a variable. -/
def Facts.get (F : Facts) (i : Nat) : Option (Tm Prim) := (F[i]?).join

/-- The facts hold in an environment: the fact of variable `i` evaluates, in
the environment above `i`, to the value of `i`. -/
def FactsOK (F : Facts) (env : Silmaril.Isotope.LambdaSSA.Semantics.Env WVal) : Prop :=
  ∀ i t, F.get i = some t →
    Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval instr (fun j => env (j + (i + 1))) t () (env i) ()

/-- Types, indexed by de Bruijn index. -/
abbrev Tys := List (Option IntType)

/-- The known type of a variable. -/
def Tys.get (T : Tys) (i : Nat) : Option IntType := (T[i]?).join

/-- The types hold in an environment: a variable of known type `t` holds an
atom of type `t`. -/
def TysOK (T : Tys) (env : Silmaril.Isotope.LambdaSSA.Semantics.Env WVal) : Prop :=
  ∀ i t, T.get i = some t → ∃ w, env i = .atom w ∧ w.type = t

/-- The result type of an operator, when it does not depend on the arguments. -/
def Op.staticTy : Op → Option IntType
  | .const w => some w.type
  | .un (.int t _) => some t
  | .un (.test _) => some .i32
  | .un .wrap => some .i32
  | .un (.extend _) => some .i64
  | .bin (.int t _) => some t
  | .bin (.rel _ _) => some .i32
  | .select => none

/-- The type of the value of a term, when it evaluates. -/
def stTy (T : Tys) : Tm Prim → Option IntType
  | .var i => T.get i
  | .op (.op o) _ => o.staticTy
  | _ => none

/-- An operand that always evaluates to an atom of the given type: a typed
variable or a constant. -/
def atomTy (T : Tys) : Tm Prim → Option IntType
  | .var i => T.get i
  | .op (.op (.const w)) .unit => some w.type
  | _ => none

/-- Is `w` the integer `c` of type `t`? -/
def isInt (t : IntType) (c : BitVec t.width) (w : WVal) : Bool :=
  decide (w.asInt t = some c)

/-- The zero of type `t`. -/
def zeroTm (t : IntType) : Tm Prim := constTm (.ofInt t 0)

/-- Algebraic identities for a binary integer operator. -/
def algBin (t : IntType) (op : IntBinOp) (x y : Tm Prim) : Option (Tm Prim) :=
  let cx := constOf? x
  let cy := constOf? y
  let y0 := cy.any (isInt t 0)
  let x0 := cx.any (isInt t 0)
  let y1 := cy.any (isInt t 1)
  let x1 := cx.any (isInt t 1)
  let yM := cy.any (isInt t (BitVec.allOnes _))
  let xM := cx.any (isInt t (BitVec.allOnes _))
  match op with
  | .add => if y0 then some x else if x0 then some y else none
  | .sub => if y0 then some x else if x == y then some (zeroTm t) else none
  | .mul => if y1 then some x else if x1 then some y else
      if y0 || x0 then some (zeroTm t) else none
  | .and => if yM then some x else if xM then some y else
      if y0 || x0 then some (zeroTm t) else if x == y then some x else none
  | .or => if y0 then some x else if x0 then some y else if x == y then some x else none
  | .xor => if y0 then some x else if x0 then some y else
      if x == y then some (zeroTm t) else none
  | .shl | .shr _ => if y0 then some x else none
  | _ => none

/-- Algebraic identities for a comparison. -/
def algRel (op : IntRelOp) (x y : Tm Prim) : Option (Tm Prim) :=
  if x == y then
    match op with
    | .eq => some (constTm (.i32 1))
    | .ne => some (constTm (.i32 0))
    | _ => none
  else none

/-- A divisor for which division/remainder of type `t` cannot trap. -/
def safeDivisor (t : IntType) (op : IntBinOp) (w : WVal) : Bool :=
  match op, w.asInt t with
  | .div .unsigned, some d | .rem .unsigned, some d | .rem .signed, some d => d != 0
  | .div .signed, some d => d != 0 && d != -1
  | _, _ => false

/-- Simplify an application of a primitive to already simplified arguments. -/
def rewriteOp (cfg : SimpCfg) (T : Tys) : Prim → Tm Prim → Tm Prim
  | .op o, a =>
      let folded : Option (Tm Prim) :=
        if cfg.fold then
          match (tmArgs? a).bind fun ts => ts.mapM constOf? with
          | some ws =>
              match o.eval ws with
              | some (.val w) => some (constTm w)
              | _ => none
          | none => none
        else none
      let alg : Option (Tm Prim) :=
        if cfg.alg then
          match o, tmArgs? a with
          | .bin (.int t op), some [x, y] =>
              if atomTy T x = some t ∧ atomTy T y = some t then algBin t op x y else none
          | .bin (.rel t op), some [x, y] =>
              if atomTy T x = some t ∧ atomTy T y = some t then algRel op x y else none
          | _, _ => none
        else none
      (folded.orElse fun _ => alg).getD (.op (.op o) a)
  | .opT o, a =>
      let folded : Option (Tm Prim) :=
        if cfg.fold then
          match (tmArgs? a).bind fun ts => ts.mapM constOf? with
          | some ws =>
              match o.eval ws with
              | some (.val w) => some (.inl (constTm w))
              | some .trap => some (.inr .unit)
              | none => none
          | none => none
        else none
      let safe : Option (Tm Prim) :=
        if cfg.alg then
          match o, tmArgs? a with
          | .bin (.int t op), some [_, y] =>
              match constOf? y with
              | some d => if safeDivisor t op d then some (.inl (.op (.op o) a)) else none
              | none => none
          | _, _ => none
        else none
      (folded.orElse fun _ => safe).getD (.op (.opT o) a)
  | .truthy, a =>
      if cfg.fold then
        match constOf? a with
        | some w =>
            match w.truthy with
            | some true => .inl .unit
            | some false => .inr .unit
            | none => .op .truthy a
        | none => .op .truthy a
      else .op .truthy a

/-- Resolve a variable through its fact. -/
def resolveVar (cfg : SimpCfg) (F : Facts) (i : Nat) : Tm Prim :=
  match F.get i with
  | some (.var j) => if cfg.copy then .var (i + 1 + j) else .var i
  | some t =>
      match constOf? t with
      | some w => if cfg.fold then constTm w else .var i
      | none => .var i
  | none => .var i

/-- Simplify a term (variables, operator applications and tuples). -/
def simpTm (cfg : SimpCfg) (F : Facts) (T : Tys) : Tm Prim → Tm Prim
  | .var i => resolveVar cfg F i
  | .op p a => rewriteOp cfg T p (simpTm cfg F T a)
  | .pair a b => .pair (simpTm cfg F T a) (simpTm cfg F T b)
  | t => t

/-- Find an earlier binding of the same operator term. -/
def cseFind (F : Facts) (a : Tm Prim) : Option Nat :=
  (List.range F.length).find? fun p => F.get p |>.any fun t => t.rename (· + (p + 1)) == a

/-- Common subexpressions: replace an operator term by an earlier binding. -/
def cseTm (cfg : SimpCfg) (F : Facts) (a : Tm Prim) : Tm Prim :=
  match a with
  | .op _ _ =>
      if cfg.cse then
        match cseFind F a with
        | some p => .var p
        | none => a
      else a
  | _ => a

/-- The simplifier on regions. -/
def simpR (cfg : SimpCfg) : Facts → Tys → Region Prim → Region Prim
  | F, T, .br l a => .br l (simpTm cfg F T a)
  | F, T, .let₁ a b =>
      let a' := cseTm cfg F (simpTm cfg F T a)
      .let₁ a' (simpR cfg (some a' :: F) (stTy T a' :: T) b)
  | F, T, .let₂ a b => .let₂ (simpTm cfg F T a) (simpR cfg (none :: none :: F) (none :: none :: T) b)
  | F, T, .case a l r =>
      match simpTm cfg F T a with
      | .inl t => .let₁ t (simpR cfg (some t :: F) (stTy T t :: T) l)
      | .inr t => .let₁ t (simpR cfg (some t :: F) (stTy T t :: T) r)
      | a' => .case a' (simpR cfg (none :: F) (none :: T) l) (simpR cfg (none :: F) (none :: T) r)
  | F, T, .cfg e n bs =>
      .cfg (simpR cfg F T e) n fun i => simpR cfg (none :: F) (none :: T) (bs i)

/-! ## Dead bindings -/

/-- Does a term mention variable `i`? -/
def Tm.mentions : Nat → Tm Prim → Bool
  | i, .var j => i == j
  | i, .op _ a => Tm.mentions i a
  | i, .let₁ a b => Tm.mentions i a || Tm.mentions (i + 1) b
  | i, .pair a b => Tm.mentions i a || Tm.mentions i b
  | _, .unit => false
  | i, .let₂ a b => Tm.mentions i a || Tm.mentions (i + 2) b
  | i, .inl a => Tm.mentions i a
  | i, .inr a => Tm.mentions i a
  | i, .case a l r => Tm.mentions i a || Tm.mentions (i + 1) l || Tm.mentions (i + 1) r
  | i, .abort a => Tm.mentions i a

/-- Does a region mention variable `i`? -/
def Region.mentions : Nat → Region Prim → Bool
  | i, .br _ a => Tm.mentions i a
  | i, .let₁ a b => Tm.mentions i a || Region.mentions (i + 1) b
  | i, .let₂ a b => Tm.mentions i a || Region.mentions (i + 2) b
  | i, .case a l r =>
      Tm.mentions i a || Region.mentions (i + 1) l || Region.mentions (i + 1) r
  | i, .cfg e n bs =>
      Region.mentions i e || (List.finRange n).any fun j => Region.mentions (i + 1) (bs j)

/-- Terms that evaluate in every environment: variables, `()`, constants, and
pairs and injections of those. -/
def Tm.total : Tm Prim → Bool
  | .var _ | .unit => true
  | .op (.op (.const _)) .unit => true
  | .pair a b => Tm.total a && Tm.total b
  | .inl a | .inr a => Tm.total a
  | _ => false

/-- Remove unused bindings of total terms (a `let₂` only of a pair of total terms). -/
def dce : Region Prim → Region Prim
  | .br l a => .br l a
  | .let₁ a b =>
      let b' := dce b
      if Region.mentions 0 b' then .let₁ a b'
      else if Tm.total a then b'.renameVars (· - 1) else .let₁ a b'
  | .let₂ a b =>
      let b' := dce b
      if Region.mentions 0 b' || Region.mentions 1 b' then .let₂ a b'
      else match a with
        | .pair x y => if Tm.total x && Tm.total y then b'.renameVars (· - 2) else .let₂ a b'
        | _ => .let₂ a b'
  | .case a l r => .case a (dce l) (dce r)
  | .cfg e n bs => .cfg (dce e) n fun i => dce (bs i)

/-! ## Passes on functions -/

/-- The simplifier on a function. -/
def SFunc.simp (cfg : SimpCfg) (f : SFunc) : SFunc :=
  { f with body := simpR cfg [] (f.params.reverse.map some) f.body }

/-- Dead-binding elimination on a function. -/
def SFunc.dce (f : SFunc) : SFunc := { f with body := Silmaril.Wasm.SSA.dce f.body }

end Silmaril.Wasm.SSA
