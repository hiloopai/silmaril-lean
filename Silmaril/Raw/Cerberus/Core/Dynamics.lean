module

public import Silmaril.Cerberus.Codec.WellFormed.Defs
public import Mathlib.Data.Int.Bitwise
public import Silmaril.Cerberus.Mem.Operations.Defs
public import Silmaril.Cerberus.Core.Formatted.Defs
public import Silmaril.Cerberus.Core.Startup.Defs
public import Silmaril.Semantics.CPort.Foundations.Operational.Execution.Defs

/-! A Core machine with typed concrete memory at Cerberus b3e11ea3. Source citations below
refer to frontend/model/*.lem unless a runtime or memory path is given.
Evaluation contexts are explicit frames. Calls unfold only one body per step.
The relation has separate continuation, choice and terminal rules. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics

abbrev Val := Value Mem.Concrete.model

mutual
/-- Runtime conversion preserves the decoded wire values. -/
def runtimeObject : ObjectValue Codec.wireModel → ObjectValue Mem.Concrete.model
  | .integer n => .integer n
  | .floating f => .floating f
  | .pointer (.null ty) => .pointer (.null ty)
  | .pointer (.function s) => .pointer (.function s)
  | .array xs => .array (runtimeLoadedList xs)
  | .struct tag [] => .struct tag []
  | .struct _ ((_, _, e) :: _) => nomatch e
  | .union _ _ e => nomatch e
def runtimeLoaded : LoadedValue Codec.wireModel → LoadedValue Mem.Concrete.model
  | .specified v => .specified (runtimeObject v)
  | .unspecified ty => .unspecified ty
def runtimeLoadedList : List (LoadedValue Codec.wireModel) → List (LoadedValue Mem.Concrete.model)
  | [] => []
  | x :: xs => runtimeLoaded x :: runtimeLoadedList xs
end
mutual
def runtimeValue : Value Codec.wireModel → Val
  | .object v => .object (runtimeObject v)
  | .loaded v => .loaded (runtimeLoaded v)
  | .unit => .unit
  | .true => .true
  | .false => .false
  | .ctype ty => .ctype ty
  | .list ty xs => .list ty (runtimeValues xs)
  | .tuple xs => .tuple (runtimeValues xs)
def runtimeValues : List (Value Codec.wireModel) → List Val
  | [] => []
  | x :: xs => runtimeValue x :: runtimeValues xs
end
abbrev PE := Pexpr Codec.wireModel Unit Sym
abbrev EE := Expr Codec.wireModel Unit Unit Sym
abbrev Program := File Codec.wireModel Unit Unit
abbrev Env := Map Sym Val
abbrev Bindings := List (Sym × Val)
abbrev Labels := Map Sym (List Sym × EE)

/-- Apply simultaneous substitutions in list order. The first occurrence of a
binder takes precedence, matching core_aux.lem's substitution traversal. -/
def extendEnv (xs : Bindings) (env : Env) : Env :=
  xs.foldr (fun (s, v) acc => acc.insert s v) env

mutual
/-- core_aux.lem:1994-2025. Tuple patterns deliberately use Lem's truncating zip. -/
def matchPattern : Pattern Sym → Val → Option Bindings
  | .mk _ (.base (none, _)), _ => some []
  | .mk _ (.base (some s, _)), v => some [(s, v)]
  | .mk _ (.ctor .specified [p]), .loaded (.specified v) =>
      matchPattern p (.object v)
  | .mk _ (.ctor .unspecified [p]), .loaded (.unspecified ty) =>
      matchPattern p (.ctype ty)
  | .mk _ (.ctor .tuple ps), .tuple vs =>
      matchPatterns ps vs
  | .mk _ (.ctor (.nil _) []), .list _ [] => some []
  | .mk _ (.ctor .cons [p, q]), .list ty (v :: vs) => do
      let xs ← matchPattern p v
      let ys ← matchPattern q (.list ty vs)
      pure (xs ++ ys)
  | _, _ => none

def matchPatterns : List (Pattern Sym) → List Val → Option Bindings
  | p :: ps, v :: vs => do
      let xs ← matchPattern p v
      let ys ← matchPatterns ps vs
      pure (xs ++ ys)
  | _, _ => some []
end

def selectCase {α : Type} (v : Val) : List (Pattern Sym × α) → Option (Bindings × α)
  | [] => none
  | (p, body) :: rest => match matchPattern p v with
    | some env => some (env, body)
    | none => selectCase v rest

inductive Outcome where
  | defined : Val → Outcome
  | ub : Loc → UndefinedBehaviour → Outcome
  | error : String → Outcome
  | unsupported : String → Outcome
  /-- `abort()`: abnormal termination (C11 §7.22.4.1; see `libraryCall`). -/
  | aborted : Outcome

/-- driver.lem:671-742 dispatches these memory actions. -/
inductive MemoryOp where
  | create : Prefix → MemoryOp
  | createReadOnly : Prefix → MemoryOp
  | alloc
  | store
  | storeLocking
  | load
  | kill : Ctype → MemoryOp
  deriving Repr

inductive Prim where
  | memory : MemoryOp → Prim
  | bin : BinOp → Prim
  | ctor : Ctor → Prim
  | conv : IntegerType → Prim
  | catchInt : IntegerType → IntOp → Prim
  | wrapInt : IntegerType → IntOp → Prim
  | notBool
  | isType : Nat → Prim
  | procedure : Env → Prim
  | directProcedure : Env → Prim
  | pointerCompare : Bool → Prim
  | functionInfo
  | compatible
  | arrayShift : Ctype → Prim
  | memberShift : Sym → Identifier → Prim
  | structValue : Sym → List Identifier → Prim
  | memberValue : Sym → Identifier → Prim
  | pointerCheck : Bool → Prim
  | pointerFromInteger
  | builtin : String → Prim
  | memop : MemOp Sym → Prim
  | seqRMW : Bool → Sym → PE → Env → Prim
  | call : Name Sym → Prim

instance : Repr Prim where
  reprPrec op _ := match op with
    | .memory m => "memory " ++ repr m
    | .bin b => "bin " ++ repr b
    | .ctor c => "ctor " ++ repr c
    | .conv ty => "conv " ++ repr ty
    | .catchInt ty i => "catchInt " ++ repr ty ++ " " ++ repr i
    | .wrapInt ty i => "wrapInt " ++ repr ty ++ " " ++ repr i
    | .notBool => "notBool"
    | .isType n => "isType " ++ repr n
    | .call n => "call " ++ repr n
    | .procedure _ => "procedure"
    | .directProcedure _ => "direct procedure"
    | .pointerCompare ne => "pointerCompare " ++ repr ne
    | .functionInfo => "functionInfo"
    | .compatible => "compatible"
    | .arrayShift _ => "arrayShift"
    | .memberShift _ _ => "memberShift"
    | .structValue _ _ => "structValue"
    | .memberValue _ _ => "memberValue"
    | .pointerCheck _ => "pointerCheck"
    | .pointerFromInteger => "pointerFromInteger"
    | .builtin name => "builtin " ++ repr name
    | .memop op => "memop " ++ repr op
    | .seqRMW .. => "SeqRMW"

/-- Bounds follow concrete/impl_mem.ml:2190-2265 and the selected LP64 helper. -/
def bounds := Mem.Concrete.integerBounds

def intType : Ctype → Option IntegerType
  | .mk _ (.basic (.integer ty)) => some ty
  | _ => none

def integer (n : Int) : Val := .object (.integer n)
def boolean (b : Bool) : Val := if b then .true else .false

/-- core_eval.lem:26-88. Positive-modulus emod is Lem's rem_f here. -/
def wrap (lo hi n : Int) : Int :=
  let r := n % (hi - lo + 1)
  if r ≤ hi then r else r - (hi - lo + 1)

/-- concrete/impl_mem.ml:2290-2312 uses Zarith truncating division. Division
by zero at this level returns zero; the C elaboration inserts the UB guard. -/
def integerBin (op : BinOp) (x y : Int) : Option Val :=
  match op with
  | .add => some (integer (x + y))
  | .sub => some (integer (x - y))
  | .mul => some (integer (x * y))
  -- core_eval.lem:425-442; concrete/impl_mem.ml:2308-2313 uses
  -- Z.pow after conversion to a signed 63-bit OCaml int. Negative or
  -- unrepresentable exponents are host exceptions, not C undefined behavior.
  | .exp => if 0 ≤ y && y ≤ 4611686018427387903
      then some (integer (x ^ y.toNat)) else none
  | .div => some (integer (x.tdiv y))
  | .remT => if y != 0 then some (integer (x.tmod y)) else none
  | .remF => if y > 0 then some (integer (x % y)) else none
  | .eq => some (boolean (x == y))
  | .lt => some (boolean (x < y))
  | .le => some (boolean (x ≤ y))
  | .gt => some (boolean (x > y))
  | .ge => some (boolean (x ≥ y))
  | _ => none

/-- core_eval.lem:368-452. Ge and Gt reverse their operands. -/
def floatingBin (op : BinOp) (x y : Numeric.Ieee754.F64) : Option Val :=
  match op with
  | .add => some (.object (.floating (Floating.binary .add x y)))
  | .sub => some (.object (.floating (Floating.binary .sub x y)))
  | .mul => some (.object (.floating (Floating.binary .mul x y)))
  | .div => some (.object (.floating (Floating.binary .div x y)))
  | .eq => some (boolean (Floating.compare .eqQuiet x y))
  | .lt => some (boolean (Floating.compare .ltSignaling x y))
  | .le => some (boolean (Floating.compare .leSignaling x y))
  | .gt => some (boolean (Floating.compare .ltSignaling y x))
  | .ge => some (boolean (Floating.compare .leSignaling y x))
  | _ => none

def integerOp (op : IntOp) (x y : Int) : Option Int :=
  match op with
  | .add => some (x + y)
  | .sub => some (x - y)
  | .mul => some (x * y)
  | .div => some (x.tdiv y)
  | .remT => if y != 0 then some (x.tmod y) else none
  | _ => none

/-- core_eval.lem:347-443, 607-686, 810-857, 1050-1088. Unsupported
operators and types are explicit outcomes, including within supported forms. -/
def primitive (op : Prim) (vs : List Val) (tags : Mem.Concrete.Tags := ∅) : Except Outcome Val := do
  match op, vs with
  | .bin b, [.object (.integer x), .object (.integer y)] =>
      match integerBin b x y with
      | some v => pure v
      | none => throw (.unsupported s!"integer binop {reprStr b}")
  | .bin b, [.object (.floating x), .object (.floating y)] =>
      match floatingBin b x y with
      | some v => pure v
      | none => throw (.error s!"ill-typed floating binop {reprStr b}")
  | .bin .eq, [.ctype x, .ctype y] =>
      match intType x, intType y with
      | some a, some b =>
          if (Mem.Concrete.registeredIntegerBounds tags a).isSome && (Mem.Concrete.registeredIntegerBounds tags b).isSome then pure (boolean (a == b))
          else throw (.unsupported "ctype equality outside enabled integer types")
      | _, _ => throw (.unsupported "ctype equality outside integer types")
  | .bin .and, [.true, v] | .bin .or, [.false, v] =>
      match v with
      | .true | .false => pure v
      | _ => throw (.error "ill-typed boolean operator")
  | .bin .and, [.false, .true] | .bin .and, [.false, .false] => pure .false
  | .bin .or, [.true, .true] | .bin .or, [.true, .false] => pure .true
  | .ctor .ivAnd, [.ctype ty, .object (.integer x), .object (.integer y)]
  | .ctor .ivOr, [.ctype ty, .object (.integer x), .object (.integer y)]
  | .ctor .ivXor, [.ctype ty, .object (.integer x), .object (.integer y)] =>
      -- core_eval.lem:661-674 unatomizes once. impl_mem.ml:2321-2326
      -- ignores the integer type and uses unbounded two's-complement bitwise ops.
      let ity := match ty with | .mk _ (.atomic t) => intType t | _ => intType ty
      let some _ := ity | throw (.unsupported "bitwise constructor outside integer types")
      pure (integer (match op with
        | .ctor .ivAnd => Int.land x y
        | .ctor .ivOr => Int.lor x y
        | _ => Int.xor x y))
  | .ctor .ivCompl, [.ctype ty, .object (.integer x)] =>
      -- core_eval.lem:654-660; concrete/impl_mem.ml:2315-2329.
      -- PNVI integers carry no provenance. Zarith complements without masking.
      let ity := match ty with | .mk _ (.atomic t) => intType t | _ => intType ty
      let some _ := ity | throw (.unsupported "bitwise constructor outside integer types")
      pure (integer (-x - 1))
  -- core_eval.lem:687-690. The type argument of ivfromfloat is ignored by Zarith.
  | .ctor .fvFromInt, [.object (.integer n)] =>
      pure (.object (.floating (Floating.ofInt n)))
  | .ctor .ivFromFloat, [.ctype ty, .object (.floating x)] =>
      let some _ := intType ty | throw (.error "ivfromfloat non-integer type")
      let some n := Floating.toInt? x
        | throw (.unsupported "Cerberus Z.of_float overflow exception on NaN or infinity")
      pure (integer n)
  | .ctor .fvFromInt, _ | .ctor .ivFromFloat, _ =>
      throw (.error "ill-typed floating conversion")
  | .ctor .specified, [.object v] => pure (.loaded (.specified v))
  | .ctor .unspecified, [.ctype ty] => pure (.loaded (.unspecified ty))
  | .ctor .array, vs =>
      let xs ← vs.mapM fun v => match v with
        | .loaded x => pure x
        | _ => throw (.error "array operand not loaded")
      pure (.object (.array xs))
  | .arrayShift ty, [.object (.pointer ptr), .object (.integer n)] =>
      -- concrete/impl_mem.ml:2026-2045. Null/function shifts raise host
      -- exceptions at this pin, even for a zero null shift. No C UB is invented.
      let size ← match ty with
        | .mk _ .void => pure 1
        | _ => match Mem.Concrete.typeLayout 64 tags ty with
          | .ok l => pure l.size
          | .error _ => throw (.unsupported "array shift layout")
      let off := size*n
      let shifted ← match ptr with
        | .allocated id addr => pure (.allocated id (addr + off))
        | .unprovenanced addr => pure (.unprovenanced (addr + off))
        | .null _ => throw (.unsupported s!"Cerberus null array shift exception offset:{off}")
        | .function _ => throw (.unsupported "Cerberus function array shift exception")
      pure (.object (.pointer shifted))
  | .memberShift tag name, [.object (.pointer ptr)] =>
      -- concrete/impl_mem.ml:2047-2067. Struct shifts preserve provenance.
      -- A null base stays null at offset zero; other offsets are unprovenanced.
      if (tags.lookup tag).any (fun (_, t) => match t with
          | .union _ => true | _ => false) then
        throw (.unsupported "union member pointer tracking")
      let members ← match Mem.Concrete.memberOffsets 64 tags tag with
        | .ok members => pure members
        | .error _ => throw (.unsupported "member shift layout")
      let some (_, _, off) := members.find? (fun x => Mem.Concrete.identifierEq x.1 name)
        | throw (.error "unknown member")
      let shifted ← match ptr with
        | .allocated id addr => pure (.allocated id (addr+off))
        | .unprovenanced addr => pure (.unprovenanced (addr+off))
        | .null ty => pure (if off == 0 then .null ty else .unprovenanced off)
        | .function _ => throw (.unsupported "Cerberus function member shift exception")
      pure (.object (.pointer shifted))
  | .pointerFromInteger, _ => throw (.unsupported "stateful integer-to-pointer operands")
  | .pointerCheck _, _ => throw (.unsupported "pointer check operands")
  | .structValue _ _, _ | .memberValue _ _, _ => throw (.unsupported "aggregate operands")
  | .arrayShift _, _ | .memberShift _ _, _ => throw (.unsupported "pointer shift operands")
  | .ctor .tuple, vs => pure (.tuple vs)
  | .ctor (.nil ty), [] => pure (.list ty [])
  | .ctor .cons, [v, .list ty vs] => pure (.list ty (v :: vs))
  | .ctor .ivMin, [.ctype ty] | .ctor .ivMax, [.ctype ty] =>
      let some ity := intType ty | throw (.unsupported "integer bound type")
      let some (lo, hi) := Mem.Concrete.registeredIntegerBounds tags ity | throw (.unsupported s!"integer bounds {reprStr ity}")
      match op with
      | .ctor .ivMin => pure (integer lo)
      | _ => pure (integer hi)
  | .conv ity, [.object (.integer n)] =>
      let some (lo, hi) := Mem.Concrete.registeredIntegerBounds tags ity | throw (.unsupported s!"conversion {reprStr ity}")
      pure (integer (if ity == .bool then (if n == 0 then 0 else 1)
        else if lo ≤ n && n ≤ hi then n else wrap lo hi n))
  | .catchInt ity iop, [.object (.integer x), .object (.integer y)] =>
      let some (lo, hi) := Mem.Concrete.registeredIntegerBounds tags ity | throw (.unsupported "catch integer type")
      let some n := integerOp iop x y | throw (.unsupported "catch integer operator")
      if lo ≤ n && n ≤ hi then pure (integer n)
      else throw (.ub .unknown .UB036_exceptional_condition)
  | .wrapInt ity iop, [.object (.integer x), .object (.integer y)] =>
      let some (lo, hi) := Mem.Concrete.registeredIntegerBounds tags ity | throw (.unsupported "wrap integer type")
      let some n := integerOp iop x y | throw (.unsupported "wrap integer operator")
      pure (integer (wrap lo hi n))
  | .notBool, [.true] => pure .false
  | .notBool, [.false] => pure .true
  | .isType k, [.ctype (.mk _ (.pointer _ _))] => pure (boolean (k == 0))
  | .isType k, [.ctype (.mk _ (.basic (.floating (.realFloating _))))] =>
      pure (boolean (k == 0))
  | .isType k, [.ctype ty] =>
      let some ity := intType ty | throw (.unsupported "type predicate outside integers")
      let some _ := Mem.Concrete.registeredIntegerBounds tags ity | throw (.unsupported "type predicate outside enabled integer types")
      pure (boolean (match k, ity with
        | 0, _ | 1, _ => true
        | 2, _ => (Mem.Concrete.registeredIntegerLayout tags ity).any (·.2)
        | 3, _ => (Mem.Concrete.registeredIntegerLayout tags ity).any (fun x => !x.2)
        | _, _ => false))
  | .ctor .ivAlignof, [.ctype ty] | .ctor .ivSizeof, [.ctype ty] =>
      let l : Except Mem.Concrete.Failure Int := match op with
        | .ctor .ivAlignof => Mem.Concrete.alignment tags ty
        | _ => (Mem.Concrete.typeLayout 64 tags ty).map Mem.Concrete.TypeLayout.size
      match l with
      | .ok n => pure (integer n)
      | .error (.unsupported why) => throw (.unsupported why)
      | .error (.invalid why) => throw (.error why)
      | .error (.ub ub) => throw (.ub .unknown ub)
  | .pointerCompare ne, [.object (.pointer x), .object (.pointer y)] =>
      -- driver.lem:780-787; concrete/impl_mem.ml:1652-1674.
      let eq ← match x, y with
        | .function a, .function b => pure (a.key == b.key)
        | .null _, .null _ => pure true
        | .null _, _ | _, .null _ => pure false
        | .function _, .allocated _ _ | .allocated _ _, .function _ => pure false
        | .allocated i a, .allocated j b =>
            if i == j then pure (a == b)
            else throw (.unsupported "distinct provenance pointer equality choices")
        | .unprovenanced a, .unprovenanced b => pure (a == b)
        | _, _ => throw (.unsupported "pointer equality with differing provenance")
      pure (boolean (if ne then !eq else eq))
  | .compatible, [.ctype x, .ctype y] =>
      -- core_eval.lem:1092-1101 supplies unqualified outer types.
      match Core.compatibleWith tags.enums 256 Core.noQualifiers x Core.noQualifiers y with
      | .ok b => pure (boolean b)
      | .error why => throw (.unsupported why)
  | .functionInfo, _ => throw (.error "function metadata dispatched separately")
  | .procedure _, _ => throw (.error "procedure dispatched separately")
  | .call _, _ => throw (.error "call dispatched separately")
  | .seqRMW .., _ => throw (.error "SeqRMW dispatched separately")
  | .ctor c, _ => throw (.unsupported s!"constructor {reprStr c}")
  | _, _ => throw (.error s!"ill-typed primitive {reprStr op}")

/-- core_eval.lem:118-160. Standard library takes precedence over user functions. -/
def functionBody (file : Program) (name : Name Sym) (vs : List Val) : Except Outcome (PE × Env) := do
  let decl ← match name with
    | .sym s => match file.stdlib.lookup s with
      | some d => pure d
      | none => match file.funs.lookup s with
        | some d => pure d
        | none => throw (.error "calling an unknown function")
    | .impl c => match file.impl.lookup c with
      | some (.function ty params body) => pure (.function ty params body)
      | _ => throw (.error "calling an unknown impl-function")
  match decl with
  | .function _ params body =>
      if params.length == vs.length then pure (body, extendEnv ((params.map Prod.fst).zip vs) ∅)
      else throw (.error "function argument count")
  | _ => throw (.error "pure call to a non-function")

/-- core_eval.lem's pure evaluation for the update operand of SeqRMW.
The finite depth bound is separate from machine fuel. Unsupported operators
remain explicit, and no memory or scheduling step occurs inside the update. -/
def evalUpdate (enums : Map Sym IntegerType := ∅) : Nat → Program → PE → Env → Except Outcome Val
  | 0, _, _, _ => .error (.unsupported "SeqRMW pure evaluation depth")
  | fuel+1, file, .mk _ _ p, env => do
      let eval := fun p => evalUpdate enums fuel file p env
      let apply := fun op ps => do primitive op (← ps.mapM eval) ⟨file.tagDefs, enums⟩
      match p with
      | .val v => pure (runtimeValue v)
      | .sym sym => match env.lookup sym with
          | some v => pure v
          | none => throw (.error "unresolved SeqRMW symbol")
      | .impl c => match file.impl.lookup c with
          | some (.constant _ p) => eval p
          | _ => throw (.error "unknown SeqRMW implementation constant")
      | .undef loc ub => throw (.ub loc ub)
      | .error reason _ => throw (.error reason)
      | .ctor op ps => apply (.ctor op) ps
      | .op op p q => apply (.bin op) [p,q]
      | .convInt ty p => apply (.conv ty) [p]
      | .catchExceptionalCondition ty op p q => apply (.catchInt ty op) [p,q]
      | .wrapI ty op p q => apply (.wrapInt ty op) [p,q]
      | .not p => apply .notBool [p]
      | .isScalar p => apply (.isType 0) [p]
      | .isInteger p => apply (.isType 1) [p]
      | .isSigned p => apply (.isType 2) [p]
      | .isUnsigned p => apply (.isType 3) [p]
      | .areCompatible p q => apply .compatible [p,q]
      | .arrayShift p ty q => apply (.arrayShift ty) [p,q]
      | .memberShift p tag name => apply (.memberShift tag name) [p]
      | .call name ps =>
          let (body, env) ← functionBody file name (← ps.mapM eval)
          evalUpdate enums fuel file body env
      | .let_ pat p body =>
          let some bindings := matchPattern pat (← eval p)
            | throw (.error "SeqRMW pure pattern mismatch")
          evalUpdate enums fuel file body (extendEnv bindings env)
      | .case_ p branches =>
          let some (bindings, body) := selectCase (← eval p) branches
            | throw (.error "SeqRMW pure case mismatch")
          evalUpdate enums fuel file body (extendEnv bindings env)
      | .if_ p yes no => match ← eval p with
          | .true => eval yes
          | .false => eval no
          | _ => throw (.error "SeqRMW condition not Boolean")
      | _ => throw (.unsupported "SeqRMW pure update expression")

mutual
/-- core_aux.lem:2195-2251, for the enabled sequencing fragment.
Saves in a left sequence retain the right continuation. -/
def saves : EE → List (Sym × (List Sym × EE))
  | .mk ann (.sseq p a b) =>
      (saves a).map (fun (s, ps, e) => (s, ps, .mk ann (.sseq p e b))) ++ saves b
  | .mk ann (.wseq p a b) =>
      (saves a).map (fun (s, ps, e) => (s, ps, .mk ann (.wseq p e b))) ++ saves b
  | .mk _ (.save (s, _) ps body) =>
      (s, ps.map Prod.fst, body) :: saves body
  | .mk _ (.let_ _ _ body) => saves body
  | .mk _ (.if_ _ a b) => saves a ++ saves b
  | .mk _ (.case_ _ bs) => savesCases bs
  | .mk _ (.unseq es) => savesList es
  | _ => []

def savesList : List EE → List (Sym × (List Sym × EE))
  | [] => []
  | e :: es => saves e ++ savesList es
def savesCases : List (Pattern Sym × EE) → List (Sym × (List Sym × EE))
  | [] => []
  | (_, e) :: es => saves e ++ savesCases es
end

/-- core_reduction.lem:199-224. Exclusions name lifted negative actions. -/
structure Access where
  negative : Option Nat := none
  exclusions : List Nat := []
  write : Bool
  address : Int
  size : Int
  deriving Repr

def races (a b : Access) : Bool :=
  !(a.negative.any (· ∈ b.exclusions) || b.negative.any (· ∈ a.exclusions)) &&
    (a.write || b.write) && a.address < b.address+b.size && b.address < a.address+a.size

mutual
inductive Control where
  | globals : List (Sym × EE) → List String → Env → Control
  | enterMain : List String → Env → Control
  | mainArgs : List Startup.Object → List Mem.Concrete.Pointer → List Sym → Control → Control
  | startup : Control → Control
  | commitUpdate : Mem.Concrete.State → Control → Control
  | setLocation : Loc → Control → Control
  | commitMemory : String → Mem.Concrete.State → Control → Control
  | pureExpr : PE → Env → Control
  | effectExpr : EE → Env → Control
  | value : Val → Control
  | apply : Prim → List Val → Control
  | halt : Outcome → Control
  | raise : Outcome → Control
  | jumping : Sym → List Val → Env → Control
  | pulling : Control → Control → List Frame → Control
  | resuming : Control → Control
  | rmwFinish : Val → Int → Int → Control
  | rmwMarker : Int → Int → Control
  | interleave : List (Nat × (Val × List Access)) → List (Nat × (Control × List Frame)) → Control

inductive Frame where
  | globalResult : Sym → List (Sym × EE) → List String → Env →
      Labels → Frame
  | mainObject : Ctype → Mem.Concrete.MemoryValue → Control → Frame
  | mainNext : Mem.Concrete.Pointer → Control → Frame
  | startupStore : Control → Frame
  | startupEnter : Control → Frame
  | arguments : Prim → List Val → List PE → Env → Frame
  | pureBind : Pattern Sym → PE → Env → Frame
  | effectBind : Pattern Sym → EE → Env → Frame
  | strongBind : Pattern Sym → EE → Env → Frame
  | diagnosticLocation : Loc → Frame
  | bound : Frame
  | annotations : List Access → Frame
  | excluded : Nat → Frame
  | liftedResult : Frame
  | pureCase : List (Pattern Sym × PE) → Env → Frame
  | effectCase : List (Pattern Sym × EE) → Env → Frame
  | pureIf : PE → PE → Env → Frame
  | effectIf : EE → EE → Env → Frame
  | runLabel : Sym → List Val → List PE → Env → Frame
  | procedureReturn : Labels → Frame
  | saveArguments : List Sym → List Val → List PE → EE → Env → Frame
end

structure State where
  control : Control
  stack : List Frame := []
  memory : Mem.Concrete.State := {}

/-- Administrative continuation steps, genuine Core choices, and labelled endings. -/
inductive Request where
  | memory : String → Mem.Concrete.State → Control → List Frame → Request
  | next : Control → List Frame → Request
  | update : Mem.Concrete.State → Control → List Frame → Request
  | pull : Control → Control → List Frame → Request
  | choose : List (Control × List Frame) → Request
  | scheduled : List (Control × List Frame) → Request
  | end_ : Outcome → Request

/-- The source relation distinguishes branching from deterministic continuation
and terminal observations. The syntax decomposition below fixes each premise. -/
inductive Label where
  | tau
  | memory : String → Label
  | terminal : Outcome → Label

inductive Respond (mem : Mem.Concrete.State := {}) : Request → Label → State → Prop where
  | memory {name : String} {m : Mem.Concrete.State} {c : Control} {k : List Frame} :
      Respond mem (.memory name m c k) (.memory name) ⟨c, k, m⟩
  | update {m : Mem.Concrete.State} {c : Control} {k : List Frame} :
      Respond mem (.update m c k) .tau ⟨c, k, m⟩
  | pull {action c : Control} {k : List Frame} :
      Respond mem (.pull action c k) (.terminal (.error "negative action without bound"))
        ⟨.halt (.error "negative action without bound"), [], mem⟩
  | next {c : Control} {k : List Frame} : Respond mem (.next c k) .tau ⟨c, k, mem⟩
  | choose {c : Control} {k : List Frame} {choices : List (Control × List Frame)} : (c, k) ∈ choices → Respond mem (.choose choices) .tau ⟨c, k, mem⟩
  | empty : Respond mem (.choose []) (.terminal (.error "empty choice")) ⟨.halt (.error "empty choice"), [], mem⟩
  | scheduled {c : Control} {k : List Frame} {choices : List (Control × List Frame)} :
      (c, k) ∈ choices → Respond mem (.scheduled choices) .tau ⟨c, k, mem⟩
  | scheduledEmpty : Respond mem (.scheduled []) (.terminal (.error "empty choice"))
      ⟨.halt (.error "empty choice"), [], mem⟩
  | end_ {o : Outcome} : Respond mem (.end_ o) (.terminal o) ⟨.halt o, [], mem⟩

/-- Evaluate a list left to right as in EU.mapM in core_eval.lem:608, 965. -/
def arguments (op : Prim) (ps : List PE) (env : Env) (k : List Frame) : Request :=
  match ps with
  | [] => .next (.apply op []) k
  | p :: rest => .next (.pureExpr p env) (.arguments op [] rest env :: k)

/-- The C library procedures that the exported documents declare without a Core body and that the
dynamics implements, after Cerberus's runtime C library at b3e11ea3 (`runtime/libc/src/stdlib.c`):

* `exit(code)` (stdlib.c:223-227) runs the `atexit` handlers and calls `_Exit(code)`, which calls
  `__builtin_exit(code)` (stdlib.c:235-239), the builtin `exit` of std.core: the program ends with `code`
  as its result (`Step_done`, core_run.lem:1122-1127). `atexit` itself is an unknown procedure in these
  documents, so no handler can have been registered and `exit` is `_Exit`.
* `abort()` (stdlib.c:140-144) is `raise(SIGABRT); _Exit(127)` in Cerberus's library, whose default
  handler prints a message on stderr (signal.c:51-58). The dynamics instead ends with `aborted`, the
  abnormal termination of C11 §7.22.4.1 (what gcc's library and ccomp's runtime do: SIGABRT).

A program that defines its own `exit` or `abort` (a `procedure` with a body) is not affected. -/
inductive LibraryCall where
  | exit
  | abort

def libraryCall (file : Program) (s : Sym) : Option LibraryCall :=
  match file.funs.lookup s, s.description with
  | some (.procedureDecl ..), .id "exit" | some (.procedureDecl ..), .id "_Exit" => some .exit
  | some (.procedureDecl ..), .id "abort" => some .abort
  | _, _ => none

/-- core_run.lem:34-75, core_reduction.lem:1328-1353. -/
def procedureBody (file : Program) (s : Sym) (vs : List Val) :
    Except Outcome (EE × Bindings) := do
  let decl : Option (FunDecl Codec.wireModel Unit Unit) := match file.stdlib.lookup s with
    | some (.procedure l m ty ps body) => some (.procedure l m ty ps body)
    | _ => file.funs.lookup s
  match decl with
  | some (.procedure _ _ _ ps body) =>
      if ps.length == vs.length then pure (body, (ps.map Prod.fst).zip vs)
      else throw (.error "procedure argument count")
  | _ => match s with
      -- core_run.lem:68-69; symbol.lem:99-105,199-201; pp_errors.ml:509.
      | .mk _ n (.id name) => throw (.error
          s!"ill-formed program: `calling an unknown procedure: Symbol({n}, SD_Id(\"{batchEscape name}\"))'")
      | _ => throw (.unsupported "unknown procedure symbol description")

/-- The nearest procedure boundary selects labels and retains the caller's context. -/
def procedureContext (fallback : Labels) :
    List Frame → Labels × List Frame
  | [] => (fallback, [])
  | .procedureReturn ls :: rest => (ls, .procedureReturn ls :: rest)
  | .globalResult s pending args env ls :: rest =>
      (ls, .globalResult s pending args env ls :: rest)
  | _ :: rest => procedureContext fallback rest

def jumpDestination (labels : Labels)
    (s : Sym) (vs : List Val) (env : Env) (k : List Frame) :
    Except Outcome (Control × List Frame) :=
  let (labels, retained) := procedureContext labels k
  match labels.lookup s with
  | none => .error (.error "Erun could not resolve label")
  | some (ps, body) =>
      if ps.length == vs.length then .ok (.effectExpr body (extendEnv (ps.zip vs) env), retained)
      else .error (.error "Erun argument count")

def jump (labels : Labels)
    (s : Sym) (vs : List Val) (env : Env) (k : List Frame) : Request :=
  match jumpDestination labels s vs env k with
  | .ok (c, frames) => .next c frames
  | .error o => .end_ o

def hasBoundary (k : List Frame) : Bool :=
  k.any (fun frame => match frame with
    | .procedureReturn _ | .globalResult _ _ _ _ _ => true
    | _ => false)

/-- A saved-label transfer escapes an operand arena until the enclosing
procedure or global-initializer boundary is visible. Erun replaces that arena
(core_reduction.lem:1393-1420), rather than returning to its remaining operands. -/
def requestJump (labels : Labels)
    (s : Sym) (vs : List Val) (env : Env) (k : List Frame) : Request :=
  if hasBoundary k then jump labels s vs env k
  else .next (.jumping s vs env) k

/-- Propagate a chosen transfer through nested arenas immediately, stopping
at a boundary inside the parent operand rather than escaping its caller. -/
def arenaJump (labels : Labels)
    (s : Sym) (vs : List Val) (env : Env) (k : List Frame) : Control × List Frame :=
  if hasBoundary k then
    match jumpDestination labels s vs env k with
    | .ok destination => destination
    | .error o => (.raise o, [])
  else (.jumping s vs env, k)

mutual
/-- core_aux.lem: memory value conversion retains member types. -/
def toMemory (ty : Ctype) : LoadedValue Mem.Concrete.model → Except Mem.Concrete.Failure Mem.Concrete.MemoryValue
  | .unspecified t => pure (.unspecified t)
  | .specified v => objectMemory ty v
def objectMemory (ty : Ctype) : ObjectValue Mem.Concrete.model → Except Mem.Concrete.Failure Mem.Concrete.MemoryValue
  | .integer n => match intType ty with
      | some i => pure (.integer i n)
      | none => throw (.unsupported "integer store type")
  | .pointer p => match ty with
      | .mk _ (.pointer _ refTy) => pure (.pointer refTy p)
      | _ => throw (.unsupported "pointer store type")
  | .array xs => match ty with
      | .mk _ (.array elem _) => do pure (.array (← loadedMemoryList elem xs))
      | _ => throw (.unsupported "array store type")
  | .struct tag xs => match ty with
      | .mk _ (.struct expected) =>
          if Mem.Concrete.symbolEq tag expected then pure (.struct_ expected xs)
          else throw (.invalid "struct store tag mismatch")
      | _ => throw (.unsupported "struct store type")
  | .union _ _ _ => throw (.unsupported "union memory value")
  | .floating x => match Floating.realType ty with
      | some fty => pure (.floating fty x)
      | none => throw (.unsupported "floating store type")
def loadedMemoryList (ty : Ctype) : List (LoadedValue Mem.Concrete.model) → Except Mem.Concrete.Failure (List Mem.Concrete.MemoryValue)
  | [] => pure []
  | x :: xs => do pure ((← toMemory ty x) :: (← loadedMemoryList ty xs))
end
mutual
/-- core_aux.lem: loaded values preserve unspecified subobjects. -/
def fromMemory : Mem.Concrete.MemoryValue → LoadedValue Mem.Concrete.model
  | .unspecified ty => .unspecified ty
  | .integer _ n => .specified (.integer n)
  | .floating _ x => .specified (.floating x)
  | .pointer _ p => .specified (.pointer p)
  | .array xs => .specified (.array (fromMemoryList xs))
  | .struct_ tag xs => .specified (.struct tag xs)
def fromMemoryList : List Mem.Concrete.MemoryValue → List (LoadedValue Mem.Concrete.model)
  | [] => []
  | x :: xs => fromMemory x :: fromMemoryList xs
end

/-- driver.lem:671-742, concrete impl_mem.ml:1111,1287,1375,1490.
Typed non-atomic actions use the decoded program's tag definitions. -/
def memoryRequest (m : Mem.Concrete.State) (op : MemoryOp) (vs : List Val)
    (k : List Frame) (tags : Mem.Concrete.Tags := ∅) : Request :=
  let result : Except Mem.Concrete.Failure (Val × Mem.Concrete.State) := do
    match op, vs with
    | .alloc, [.object (.integer align), .object (.integer size)] =>
        let (p, m') ← Mem.Concrete.allocateRegion m align size
        pure (.object (.pointer p), m')
    | .create pref, [.object (.integer align), .ctype ty] =>
        let (p, m') ← Mem.Concrete.allocateTyped tags m align ty
        pure (.object (.pointer p), Mem.Concrete.updateLastAllocation m' fun a =>
          {a with readonlyKind := Mem.Concrete.readonlyKind pref})
    | .createReadOnly pref, [.object (.integer align), .ctype ty, .loaded v] =>
        let n ← toMemory (Mem.Concrete.unatomic ty) v
        let (p, m') ← Mem.Concrete.createReadOnly tags m align ty n pref
        pure (.object (.pointer p), m')
    | .storeLocking, [.ctype ty, .object (.pointer p), .loaded v] =>
        let n ← toMemory (Mem.Concrete.unatomic ty) v
        let (_, m') ← Mem.Concrete.storeLocking tags m ty p n true
        pure (.unit, m')
    | .store, [.ctype ty, .object (.pointer p), .loaded v] =>
        let n ← toMemory (Mem.Concrete.unatomic ty) v
        let (_, m') ← Mem.Concrete.storeTyped tags m ty p n
        pure (.unit, m')
    | .load, [.ctype ty, .object (.pointer p)] =>
        let (n, m') ← Mem.Concrete.loadTyped tags m ty p
        pure (.loaded (fromMemory n), m')
    | .kill ty, [.object (.pointer p)] =>
        let (_, m') ← Mem.Concrete.killTyped tags m ty p
        pure (.unit, m')
    | .create _, _ => throw (.unsupported "Create")
    | _, _ => throw (.unsupported "memory action arguments")
  match result with
  | .ok (v, m') =>
      let k := match op, vs with
        | .storeLocking, .ctype ty :: .object (.pointer p) :: _
        | .store, .ctype ty :: .object (.pointer p) :: _
        | .load, .ctype ty :: .object (.pointer p) :: _ =>
            match Mem.Concrete.accessTyped tags m ty p with
            | .ok (_, addr, size) =>
                let negative := k.findSome? fun f => match f with | .excluded n => some n | _ => none
                .annotations [⟨negative, [], match op with | .store | .storeLocking => true | _ => false, addr, size⟩] :: k
            | _ => k
        | _, _ => k
      .memory (match op with
      | .create _ => "Create" | .createReadOnly _ => "CreateReadOnly" | .alloc => "Alloc"
      | .store | .storeLocking => "Store" | .load => "Load" | .kill _ => "Kill") m' (.value v) k
  | .error (.unsupported why) => .end_ (.unsupported why)
  | .error (.invalid why) => .end_ (.error why)
  | .error (.ub ub) => .end_ (.ub .unknown ub)

/-- Annotations already on the lifted context acquire the new exclusion.
Sibling operands and future actions do not. core_reduction.lem:925-944. -/
def excludeFrames (n : Nat) : List Frame → List Frame := List.map fun f => match f with
  | .annotations xs => .annotations (xs.map fun x => {x with exclusions := n :: x.exclusions})
  | f => f

/-- Apply exclusions along the selected operand's context. Completed siblings
are not context annotations. A resumption marks the hole while a pull crosses
nested unsequenced operands. core_reduction.lem:925-944. -/
def excludePath (n : Nat) : (c : Control) → Bool × Control
  | .resuming c => (true, c)
  | .interleave done tasks =>
      let tasks := tasks.attach.map fun task =>
        let (found, c) := excludePath n task.val.2.1
        (found, task.val.1, c, if found then excludeFrames n task.val.2.2 else task.val.2.2)
      (tasks.any (·.1), .interleave done (tasks.map (·.2)))
  | c => (false, c)
termination_by c => sizeOf c
decreasing_by
  rcases task with ⟨⟨i, c, frames⟩, member⟩
  have h := List.sizeOf_lt_of_mem member
  simp_all
  omega

/-- Split at the nearest strong sequence or bound, preserving the inner context.
A pull request crosses an unsequenced operand before the split is retried. -/
def liftAction (mem : Mem.Concrete.State) (action c : Control) (k : List Frame) : Request :=
  let split := k.span (fun f => match f with | .strongBind .. | .bound => false | _ => true)
  match split.2 with
  | [] => .pull action c k
  | boundary :: outer =>
      let n := mem.nextExcluded
      .update {mem with nextExcluded := n+1}
        (.interleave [] [(0, action, [.excluded n]), (1, (excludePath n c).2, excludeFrames n split.1)])
        (.liftedResult :: boundary :: outer)

def annotationsOnly : List Frame → Option (List Access)
  | [] => some []
  | .annotations xs :: rest => (annotationsOnly rest).map (xs ++ ·)
  | _ => none

/-- core_reduction.lem:443-482. Calls in future sequence and branch bodies
count as well as calls at the current focus. Eproc and excluded actions do not. -/
def hasCCall : EE → Bool
  | .mk _ e => match e with
    | .ccall .. => true
    | .case_ _ bs => bs.attach.any fun b => hasCCall b.val.2
    | .let_ _ _ e | .bound e | .save _ _ e | .annot _ e => hasCCall e
    | .if_ _ a b | .wseq _ a b | .sseq _ a b => hasCCall a || hasCCall b
    | .unseq es | .nd es => es.attach.any fun e => hasCCall e.val
    | _ => false
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (rcases b with ⟨⟨p, e⟩, member⟩; have h := List.sizeOf_lt_of_mem member; simp_all; omega)
    | (have h := List.sizeOf_lt_of_mem e.property; simp_all; omega)
    | (simp_all; omega)

/-- Reconstruct the call predicate on the remaining operand, including its
continuations. A bound still belongs to the expression searched by has_ccall. -/
def controlHasCCall (c : Control) (frames : List Frame) : Bool :=
  (match c with
    | .effectExpr e _ => hasCCall e
    | .apply (.procedure _) _ => true
    | .setLocation _ c | .commitMemory _ _ c | .commitUpdate _ c | .resuming c =>
        controlHasCCall c []
    | .pulling action c inner => controlHasCCall action [] || controlHasCCall c inner
    | .interleave _ tasks => tasks.attach.any fun t => controlHasCCall t.val.2.1 t.val.2.2
    | _ => false) || frames.any fun f => match f with
      | .effectBind _ e _ | .strongBind _ e _ | .saveArguments _ _ _ e _ => hasCCall e
      | .effectCase bs _ => bs.any fun b => hasCCall b.2
      | .effectIf a b _ => hasCCall a || hasCCall b
      | .arguments (.procedure _) _ _ _ => true
      | _ => false
termination_by sizeOf c
decreasing_by
  all_goals first
    | (rcases t with ⟨⟨i, c, frames⟩, member⟩; have h := List.sizeOf_lt_of_mem member; simp_all; omega)
    | simp_all
  all_goals omega

/-- core_reduction.lem:1331-1353 saves the caller arena when entering a
procedure. Caller siblings resume only after that procedure returns. -/
def activeCall (c : Control) (frames : List Frame) : Bool :=
  frames.any (fun f => match f with | .procedureReturn _ => true | _ => false) ||
    match c with
    | .setLocation _ c | .commitMemory _ _ c | .commitUpdate _ c | .resuming c => activeCall c []
    | .pulling action c inner => activeCall action [] || activeCall c inner
    | .interleave _ tasks => tasks.attach.any fun t => activeCall t.val.2.1 t.val.2.2
    | _ => false
termination_by sizeOf c
decreasing_by
  all_goals first
    | (rcases t with ⟨⟨i, c, frames⟩, member⟩; have h := List.sizeOf_lt_of_mem member; simp_all; omega)
    | simp_all
  all_goals omega

/-- Convert a deferred request without promoting a failed memory operation to
an administrative error. The operation's memory snapshot commits only if chosen. -/
def scheduledRequest : Request → Request
  | .next c k => .scheduled [(c, k)]
  | .memory name m c k => .scheduled [(.commitMemory name m c, k)]
  | .update m c k => .scheduled [(.commitUpdate m c, k)]
  | .end_ o => .scheduled [(.raise o, [])]
  | .choose cs | .scheduled cs => .scheduled cs
  | .pull action c k => .scheduled [(.pulling action c k, [])]

/-- driver.lem:902-925. Calls and filesystem builtins await scheduling;
actions and memops do so only in an unsequenced context containing a call. -/
def awaitsScheduling (unseqWithCall : Bool) : Control → Bool
  | .apply (.procedure _) _ | .apply (.builtin _) _ => true
  | .apply (.memory _) _ | .apply (.memop _) _ | .apply .pointerFromInteger _
  | .apply (.pointerCheck _) _ | .apply (.pointerCompare _) _ | .apply (.seqRMW ..) _ =>
      unseqWithCall
  | _ => false

/-- One syntax decomposition, without recursive evaluation. References cover
all enabled forms; the final catch-all gives every other form an ending. -/
def requestAux (file : Program) (labels : Labels)
    (mem : Mem.Concrete.State) (control : Control) (k : List Frame)
    (unseqWithCall : Bool := false) : Request :=
  -- Contexts run from the hole outwards; any bound cuts off outer siblings.
  let unseqWithCall := unseqWithCall && !(k.any fun f => match f with | .bound => true | _ => false)
  let priorLocation := mem.currentLocation
  let mem := match control with
    | .effectExpr (.mk annots e) _ =>
        let focused := match e with
          | .wseq _ _ _ | .sseq _ _ _ | .bound _ | .unseq _ => false
          | _ => true
        if !focused then mem else
        match annots.findSome? (fun a => match a with | .loc l => some l | _ => none) with
        | some l => if libraryLocation l then mem else {mem with currentLocation := l}
        | none => mem
    | _ => mem
  let tags : Mem.Concrete.Tags := ⟨file.tagDefs, mem.enumTypes⟩
  let result := match control with
  | .jumping s vs env => requestJump labels s vs env k
  -- driver.lem:1556-1602,1714-1737. Select main after global initialization.
  | .globals [] args env => .next (.enterMain args env) k
  | .globals ((sym, e) :: pending) args env =>
      .next (.effectExpr e env) (.globalResult sym pending args env (Map.ofList (saves e).reverse) :: k)
  | .enterMain args env =>
      match file.main with
      | none => .end_ (.error "no startup function")
      | some sym => match file.funs.lookup sym with
        | none => .end_ (.error "startup function missing")
        | some decl =>
            let entry : Option (Loc × List Sym × Control) := match decl with
              | .procedure loc _ _ ps body => some (loc, ps.map Prod.fst, .effectExpr body env)
              | .function _ ps body => some (.other "main args", ps.map Prod.fst, .pureExpr body env)
              | _ => none
            match entry with
            | none => .end_ (.unsupported "startup declaration or parameters")
            | some (loc, ps, c) =>
                match ps with
                | [argc, argv] =>
                  match Startup.objects args (match file.callingConvention with | .innerArg => true | .normal => false)
                      loc sym argc argv with
                  | .error (.unsupported why) => .end_ (.unsupported why)
                  | .error _ => .end_ (.error "startup argument objects")
                  | .ok objects => .next (.mainArgs objects [] ps c) k
                | _ => .next (.startup c) k
  | .mainArgs (obj :: rest) pointers ps c =>
      match Startup.contents pointers obj.contents,
          Mem.Concrete.typeLayout 64 file.tagDefs obj.type with
      | .ok value, .ok layout =>
          memoryRequest mem (.create obj.allocationPrefix) [integer layout.align, .ctype obj.type]
            (.mainObject obj.type value (.mainArgs rest pointers ps c) :: k) file.tagDefs
      | .error (.unsupported why), _ | _, .error (.unsupported why) => .end_ (.unsupported why)
      | _, _ => .end_ (.error "startup argument object")
  | .mainArgs [] pointers ps c =>
      let values := if (match file.callingConvention with | .innerArg => true | .normal => false) then
        [.loaded (.specified (.integer (pointers.length - 1))),
         .loaded (.specified (.pointer (pointers.getLast?.getD (.null Startup.charPointer))))]
        else (pointers.drop (pointers.length - 2)).map (fun p => .object (.pointer p))
      let bind := fun env => extendEnv (ps.zip values) env
      match c with
      | .effectExpr body env => .next (.startup (.effectExpr body (bind env))) k
      | .pureExpr body env => .next (.startup (.pureExpr body (bind env))) k
      | _ => .end_ (.error "startup body")
  | .startup c =>
      let ty := Ctype.mk [] (.basic (.integer (.signed .int)))
      memoryRequest mem (.create (.other "errno")) [integer 4, .ctype ty] [.startupStore c] tags
  | .commitMemory name m c => .memory name m c k
  | .setLocation loc c => .update {mem with currentLocation := loc} c k
  | .commitUpdate m c => .update m c k
  | .halt o | .raise o => .end_ o
  | .pulling action c frames => liftAction mem action c (frames ++ k)
  | .rmwFinish v addr size => liftAction mem (.rmwMarker addr size) (.resuming (.value v)) k
  | .resuming _ => .end_ (.error "unhandled negative resumption")
  | .rmwMarker addr size =>
      let negative := k.findSome? fun f => match f with | .excluded n => some n | _ => none
      .next (.value .unit) (.annotations [⟨negative, [], true, addr, size⟩] :: k)
  | .pureExpr (.mk _ _ pe) env =>
      match pe with
      -- core_eval.lem:570-606
      | .val v => .next (.value (runtimeValue v)) k
      | .sym s => match env.lookup s with
        | some v => .next (.value v) k
        | none => .end_ (.error ("unresolved symbol: " ++ symbolText s ++
            " at " ++ locationText ((k.findSome? fun f => match f with
              | .diagnosticLocation l => some l | _ => none).getD mem.currentLocation)))
      | .impl c => match file.impl.lookup c with
        | some (.constant _ body) => .next (.pureExpr body env) k
        | _ => .end_ (.error "unknown implementation constant")
      | .undef loc ub => .end_ (.ub loc ub)
      | .error str _ => .end_ (.error str)
      -- core_eval.lem:607-747, 810-857, 965-1088
      | .ctor c ps => arguments (.ctor c) ps env k
      | .arrayShift p ty n => arguments (.arrayShift ty) [p, n] env k
      | .memberShift p tag member => arguments (.memberShift tag member) [p] env k
      | .struct tag xs => arguments (.structValue tag (xs.map Prod.fst)) (xs.map Prod.snd) env k
      | .memberof tag member p => arguments (.memberValue tag member) [p] env k
      | .op b p q => arguments (.bin b) [p, q] env k
      | .convInt ty p => arguments (.conv ty) [p] env k
      | .catchExceptionalCondition ty op p q => arguments (.catchInt ty op) [p, q] env k
      | .wrapI ty op p q => arguments (.wrapInt ty op) [p, q] env k
      | .not p => arguments .notBool [p] env k
      | .cfunction p => arguments .functionInfo [p] env k
      | .areCompatible a b => arguments .compatible [a, b] env k
      | .call nm ps => arguments (.call nm) ps env k
      | .let_ pat p body => .next (.pureExpr p env) (.pureBind pat body env :: k)
      | .case_ p bs => .next (.pureExpr p env) (.pureCase bs env :: k)
      | .if_ p yes no => .next (.pureExpr p env) (.pureIf yes no env :: k)
      | .isScalar p => arguments (.isType 0) [p] env k
      | .isInteger p => arguments (.isType 1) [p] env k
      | .isSigned p => arguments (.isType 2) [p] env k
      | .isUnsigned p => arguments (.isType 3) [p] env k
      | _ => .end_ (.unsupported "pure expression outside the enabled fragment")
  | .apply (.seqRMW forward sym update env) [.ctype ty, .object (.pointer p)] =>
      let result : Except Outcome (Val × Mem.Concrete.State × Int × Int) := do
        let convert := fun {α : Type} (r : Except Mem.Concrete.Failure α) =>
          r.mapError fun e => match e with
            | .unsupported why => Outcome.unsupported why
            | .invalid why => .error why
            | .ub ub => .ub .unknown ub
        let (old, snapshot) ← convert (Mem.Concrete.loadTyped tags mem ty p)
        let value ← evalUpdate mem.enumTypes 256 file update (env.insert sym (.loaded (fromMemory old)))
        let new ← convert (match value with
          | .loaded v => toMemory (Mem.Concrete.unatomic ty) v
          | .object v => objectMemory (Mem.Concrete.unatomic ty) v
          | _ => .error (.unsupported "SeqRMW update value"))
        let ((addr, size), finish) ← convert (Mem.Concrete.storeTyped tags snapshot ty p new)
        pure (.loaded (fromMemory (if forward then new else old)), finish, addr, size)
      match result with
      | .error o => .end_ o
      | .ok (value, finish, addr, size) => .memory "SeqRMW" finish (.rmwFinish value addr size) k
  | .apply (.memory op) vs => memoryRequest mem op vs k tags
  | .apply (.builtin "printf") [.list _ fmt, .list _ args] =>
      -- core_run.lem:1062-1072; driver.lem:245-256,399-411.
      let result : Except Mem.Concrete.Failure (Val × Mem.Concrete.State) := do
        let chars ← fmt.mapM fun v => match v with
          | .object (.integer n) =>
              if 0 ≤ n && n < 256 then pure (Char.ofNat n.toNat)
              else throw (.unsupported "printf format character")
          | _ => throw (.unsupported "printf format value")
        let args ← args.mapM fun v => match v with
          | .tuple [.ctype ty, .object (.pointer p)] => pure (ty, p)
          | _ => throw (.unsupported "printf argument list")
        let (text, finish) ← printFormat tags (chars.length+1) chars args mem
        pure (.loaded (.specified (.integer text.length)),
          {finish with stdout := finish.stdout ++ text})
      match result with
      | .ok (v, finish) => .memory "printf" finish (.value v) k
      | .error (.unsupported why) => .end_ (.unsupported why)
      | .error (.invalid why) => .end_ (.error why)
      | .error (.ub ub) => .end_ (.ub .unknown ub)
  -- core_run.lem:1122-1127, core_reduction.lem:976-990: `Step_done cval`, and driver.lem:1326-1335
  -- (`prepare_exit`): the program ends with `cval` as its result, as if `main` returned it.
  | .apply (.builtin "exit") [v] => .end_ (.defined v)
  | .apply (.builtin name) _ => .end_ (.unsupported s!"builtin {name}")
  | .apply .pointerFromInteger
      [.ctype (.mk _ (.basic (.integer _))), .ctype refTy, .object (.integer n)] =>
      -- driver.lem:772-774; impl_mem.ml:1948-1987, with the live exposure state.
      match Mem.Concrete.addressPointer mem.allocations mem.dead refTy (n % 18446744073709551616) with
      | .ok p => .next (.value (.object (.pointer p))) k
      | .error (.unsupported why) => .end_ (.unsupported why)
      | .error (.invalid why) => .end_ (.error why)
      | .error (.ub ub) => .end_ (.ub .unknown ub)
  | .apply (.memop .intFromPtr)
      [.ctype _, .ctype (.mk _ (.basic (.integer ity))), .object (.pointer p)] =>
      -- driver.lem:763-770. Exposure is a memory-state transition.
      match Mem.Concrete.integerFromPointer mem ity p with
      | .ok (n, finish) => .memory "IntFromPtr" finish (.value (integer n)) k
      | .error (.unsupported why) => .end_ (.unsupported why)
      | .error (.invalid why) => .end_ (.error why)
      | .error (.ub ub) => .end_ (.ub .unknown ub)
  | .apply (.memop op) vs =>
      -- core_run.lem:1354-1365; driver.lem:759-762,823-840.
      let result : Except Mem.Concrete.Failure Val := do
        match op, vs with
        | .ptrArrayShift, [.object (.pointer p), .ctype ty, .object (.integer n)] =>
            pure (.object (.pointer (← Mem.Concrete.shiftPointer tags mem p ty n)))
        | .ptrdiff, [.ctype ty, .object (.pointer p), .object (.pointer q)] =>
            pure (integer (← Mem.Concrete.difference tags mem ty p q))
        | _, _ => throw (.unsupported s!"memory operation {reprStr op}")
      match result with
      | .ok v => .next (.value v) k
      | .error (.unsupported why) => .end_ (.unsupported why)
      | .error (.invalid why) => .end_ (.error why)
      | .error (.ub ub) => .end_ (.ub .unknown ub)
  | .apply .functionInfo vs =>
      -- core_eval.lem:901-940. No host function signatures are substituted.
      match vs with
      | [.loaded (.specified (.pointer (.function s)))] =>
          match file.funInfo.lookup s with
          | some (_, _, ret, params, variadic, proto) =>
              .next (.value (.tuple [.ctype ret,
                .list .ctype (params.map fun p => .ctype p.2),
                boolean variadic, boolean proto])) k
          | none => .end_ (.error "missing function metadata")
      | _ => .end_ (.unsupported "function metadata for non-function pointer")
  | .apply (.procedure outer) vs | .apply (.directProcedure outer) vs =>
      match vs with
      | .loaded (.specified (.pointer (.function s))) :: args =>
          match libraryCall file s, args with
          -- `exit(status)`: load the `int` argument, then the builtin `exit` (`libraryCall`).
          | some .exit, [p] =>
              .next (.apply (.memory .load) [.ctype (Ctype.mk [] (.basic (.integer (.signed .int)))), p])
                (.arguments (.builtin "exit") [] [] ∅ :: k)
          | some .abort, [] => .end_ .aborted
          | _, _ =>
          match procedureBody file s args with
          | .ok (body, env) =>
              .next (.effectExpr body (extendEnv env outer)) (.procedureReturn (Map.ofList (saves body).reverse) :: k)
          | .error o => .end_ o
      | .loaded (.specified (.pointer (.null _))) :: _ =>
          .end_ (.error "null function pointer")
      | _ => .end_ (.unsupported "calling through a non-function pointer")
  | .apply (.call name) vs =>
      match functionBody file name vs with
      | .ok (body, env) => .next (.pureExpr body env) k
      | .error o => .end_ o
  | .apply (.pointerCheck valid) [.ctype ty, .object (.pointer p)] =>
      -- driver.lem:776-778,815-817; impl_mem.ml:1884-1945.
      let result : Except Mem.Concrete.Failure Bool := do
        let align ← Mem.Concrete.alignment tags ty
        match p with
        | .null _ => pure (!valid)
        | .function _ => if valid then pure false else throw (.unsupported "function alignment")
        | .allocated id addr => pure ((addr % align == 0) && (!valid || !(id ∈ mem.dead)))
        | .unprovenanced addr => pure (!valid && addr % align == 0)
      match result with
      | .ok b => .next (.value (boolean b)) k
      | .error (.unsupported why) => .end_ (.unsupported why)
      | .error (.invalid why) => .end_ (.error why)
      | .error (.ub ub) => .end_ (.ub .unknown ub)
  | .apply (.structValue tag names) vs =>
      let result : Except Mem.Concrete.Failure Val := do
        let l ← Mem.Concrete.typeLayout 64 tags (.mk [] (.struct tag))
        let xs ← (names.zip vs).mapM fun (name, v) => do
          let some (_, ty, _) := l.members.find? (fun x => Mem.Concrete.identifierEq x.1 name)
            | throw (.invalid "unknown struct member")
          let value ← match v with
            | .loaded v => toMemory ty v
            | .object v => objectMemory ty v
            | _ => throw (.unsupported "struct member operand")
          pure (name, ty, value)
        pure (.object (.struct tag xs))
      match result with
      | .ok v => .next (.value v) k
      | .error (.unsupported why) => .end_ (.unsupported why)
      | .error (.invalid why) => .end_ (.error why)
      | .error (.ub ub) => .end_ (.ub .unknown ub)
  | .apply (.memberValue tag name) [.object (.struct actual xs)] =>
      if !Mem.Concrete.symbolEq tag actual then .end_ (.error "member access tag mismatch")
      else match xs.find? (fun x => Mem.Concrete.identifierEq x.1 name) with
      | some (_, _, v) => .next (.value (.loaded (fromMemory v))) k
      | none => .end_ (.error "missing member value")
  | .apply op vs => match primitive op vs tags with
      | .ok v => .next (.value v) k
      | .error o => .end_ o
  | .effectExpr (.mk _ e) env =>
      match e with
      -- core_run.lem:1540-1553, core_reduction.lem:308-430, 1207-1211
      | .ccall _ _ p ps => arguments (.procedure env) (p :: ps) env k
      | .proc _ (.impl (.builtinFunction name)) ps => arguments (.builtin name) ps env k
      | .proc _ (.sym s) ps => arguments (.directProcedure env)
          ((.mk [] () (.val (.loaded (.specified (.pointer (.function s)))))) :: ps) env k
      | .memop .ptrFromInt ps => arguments .pointerFromInteger ps env k
      | .memop .ptrValidForDeref ps => arguments (.pointerCheck true) ps env k
      | .memop .ptrWellAligned ps => arguments (.pointerCheck false) ps env k
      | .memop .ptrEq ps => arguments (.pointerCompare false) ps env k
      | .memop .ptrNe ps => arguments (.pointerCompare true) ps env k
      | .memop op ps => arguments (.memop op) ps env k
      | .pure p => .next (.pureExpr p env) (.diagnosticLocation priorLocation :: k)
      | .bound e => .next (.effectExpr e env) (.bound :: k)
      | .sseq p a b => .next (.effectExpr a env) (.strongBind p b env :: k)
      | .wseq p a b => .next (.effectExpr a env) (.effectBind p b env :: k)
      | .let_ p a b => .next (.pureExpr a env) (.effectBind p b env :: k)
      | .case_ p bs => .next (.pureExpr p env) (.effectCase bs env :: k)
      | .if_ p yes no => .next (.pureExpr p env) (.effectIf yes no env :: k)
      | .unseq es => .next (.interleave [] (es.zipIdx.map fun (e, i) =>
          (i, .effectExpr e env, []))) k
      -- core_reduction.lem:433-435, nondeterministic Core choice
      | .nd [] => .end_ (.error "empty nondeterministic choice")
      | .nd es => .choose (es.map fun e => (.effectExpr e env, k))
      -- core_reduction.lem:412-430, 1393-1420
      | .save _ ps body =>
          match ps.map (fun p => p.2.2) with
          | [] => .next (.effectExpr body env) k
          | p :: rest =>
              .next (.pureExpr p env)
                (.saveArguments (ps.map Prod.fst) [] rest body env :: k)
      | .run _ s ps => match ps with
          | [] => requestJump labels s [] env k
          | p :: rest => .next (.pureExpr p env) (.runLabel s [] rest env :: k)
      | .action (.mk .pos (.mk _ _ action)) => match action with
          | .seqRmw forward ty p sym update => arguments (.seqRMW forward sym update env) [ty,p] env k
          | .alloc align size _ => arguments (.memory .alloc) [align, size] env k
          | .create align ty pref => arguments (.memory (.create pref)) [align, ty] env k
          | .createReadOnly align ty v pref => arguments (.memory (.createReadOnly pref)) [align, ty, v] env k
          -- driver.lem:681-702 ignores memory order in the sequential driver.
          | .store true ty p v .seqCst
          | .store true ty p v .na => arguments (.memory .storeLocking) [ty, p, v] env k
          | .store false ty p v .seqCst
          | .store false ty p v .na => arguments (.memory .store) [ty, p, v] env k
          | .load ty p .seqCst
          | .load ty p .na => arguments (.memory .load) [ty, p] env k
          | .kill (.static ty) p => arguments (.memory (.kill ty)) [p] env k
          | _ => .end_ (.unsupported "memory action outside the enabled fragment")
      | .action (.mk .neg (.mk _ _ (.seqRmw ..))) =>
          .end_ (.error "negative SeqRMW forbidden by typecheck")
      | .action (.mk .neg act) => liftAction mem (.effectExpr (.mk [] (.action (.mk .pos act))) env) (.resuming (.value .unit)) k
      | _ => .end_ (.unsupported "effectful expression outside the enabled fragment")
  -- core_reduction.lem:199-263,530-534. Compare annotations at tuple completion.
  | .interleave done [] =>
      if done.any (fun x => done.any (fun y => x.1 != y.1 &&
          x.2.2.any (fun a => y.2.2.any (races a)))) then
        .end_ (.ub .unknown .UB035_unsequenced_race)
      else .next (.value (.tuple ((done.mergeSort (fun a b => a.1 ≤ b.1)).map (·.2.1))))
        (.annotations (done.flatMap (·.2.2)) :: k)
  | .interleave done tasks =>
      let inCall := tasks.any fun t => activeCall t.2.1 t.2.2
      let groups := tasks.attach.reverse.map fun task =>
        let i := task.val.1
        let c := task.val.2.1
        let frames := task.val.2.2
        let rest := tasks.filter (fun t => t.1 != i)
        let replace := fun c' frames' => tasks.map fun t =>
          if t.1 == i then (i, c', frames') else t
        let wrap := fun c' frames' => match c' with
          | .raise o => (.raise o, [])
          | .jumping s vs env => arenaJump labels s vs env k
          | _ => (.interleave done (replace c' frames'), k)
        let withCall := unseqWithCall || rest.any (fun t => controlHasCCall t.2.1 t.2.2)
        if inCall && !activeCall c frames then (false, []) else
        match c, annotationsOnly frames with
        | .value v, some xs => (true, [(.interleave ((i, v, xs) :: done) rest, k)])
        | _, _ =>
            match requestAux file labels mem c frames withCall with
            | .scheduled cs => (false, cs.map fun (c', frames') => wrap c' frames')
            | .memory name m' c' frames' =>
                (true, [(.commitMemory name m' (.interleave done (replace c' frames')), k)])
            | .next (.jumping s vs env) _ => (true, [arenaJump labels s vs env k])
            | .update m' c' frames' =>
                (true, [(.commitUpdate m' (.interleave done (replace c' frames')), k)])
            | .pull action c' frames' =>
                let cs := match liftAction mem action (.interleave done (replace c' frames')) k with
                  | .update m' next frames => [(.commitUpdate m' next, frames)]
                  | .pull action next frames => [(.pulling action next frames, [])]
                  | _ => []
                (true, cs)
            | .next c' frames' => (true, [wrap c' frames'])
            | .choose cs => (true, cs.map fun (c', frames') => wrap c' frames')
            | .end_ o => (true, [(.raise o, [])])
      -- Advance the first eligible reduction in reverse source order. An ND
      -- reduction keeps all its alternatives; otherwise retain every scheduled step.
      match groups.find? (·.1) with
      | some (_, cs) => .choose cs
      | none => .scheduled (groups.flatMap (·.2))
  | .value v =>
      match k with
      -- core_run.lem:1540-1542
      | [] => .end_ (.defined v)
      | .globalResult sym pending args env _ :: tail =>
          .next (.globals pending args (env.insert sym v)) tail
      | .mainObject ty value c :: tail =>
          memoryRequest mem .store [.ctype ty, v, .loaded (fromMemory value)]
            (.mainNext (match v with | .object (.pointer p) => p | _ => .null ty) c :: tail)
            file.tagDefs
      | .mainNext p (.mainArgs rest pointers ps c) :: tail =>
          .next (.mainArgs rest (pointers ++ [p]) ps c) tail
      | .mainNext _ _ :: _ => .end_ (.error "startup allocation continuation")
      | .startupStore c :: tail =>
          let ty := Ctype.mk [] (.basic (.integer (.signed .int)))
          memoryRequest mem .store [.ctype ty, v, .loaded (.specified (.integer 0))]
            (.startupEnter c :: tail)
      | .procedureReturn _ :: tail => .next (.value v) tail
      | .startupEnter c :: tail => .update {mem with currentLocation := .other "Driver.drive"} c tail
      | .arguments op vs rest env :: tail => match rest with
          | [] => .next (.apply op (vs ++ [v])) tail
          | p :: ps => .next (.pureExpr p env) (.arguments op (vs ++ [v]) ps env :: tail)
      -- core_eval.lem:998-1048, core_reduction.lem:308-409
      | .pureBind p body env :: tail => match matchPattern p v with
          | some xs => .next (.pureExpr body (extendEnv xs env)) tail
          | none => .end_ (.error "PElet pattern mismatch")
      | .bound :: tail | .excluded _ :: tail | .diagnosticLocation _ :: tail => .next (.value v) tail
      | .liftedResult :: tail => match v with
          | .tuple [_, result] => .next (.value result) tail
          | _ => .end_ (.error "lifted action tuple")
      | .annotations _ :: .bound :: tail => .next (.value v) tail
      | .annotations xs :: .annotations ys :: tail =>
          .next (.value v) (.annotations (xs ++ ys) :: tail)
      | .annotations xs :: tail =>
          match requestAux file labels mem (.value v) tail unseqWithCall with
          | .next c frames => .next c (.annotations xs :: frames)
          | .memory name m c frames => .memory name m c (.annotations xs :: frames)
          | .update m c frames => .update m c (.annotations xs :: frames)
          | .pull action c frames => .pull action c (.annotations xs :: frames)
          | .choose choices => .choose (choices.map fun (c, frames) => (c, .annotations xs :: frames))
          | .scheduled choices => .scheduled (choices.map fun (c, frames) => (c, .annotations xs :: frames))
          | .end_ o => .end_ o
      | .strongBind p body env :: tail | .effectBind p body env :: tail => match matchPattern p v with
          | some xs => .next (.effectExpr body (extendEnv xs env)) tail
          | none => .end_ (.error "effect sequence pattern mismatch")
      | .pureCase bs env :: tail => match selectCase v bs with
          | some (xs, body) => .next (.pureExpr body (extendEnv xs env)) tail
          | none => .end_ (.error "PEcase pattern mismatch")
      | .effectCase bs env :: tail => match selectCase v bs with
          | some (xs, body) => .next (.effectExpr body (extendEnv xs env)) tail
          | none => .end_ (.error "Ecase pattern mismatch")
      | .pureIf yes no env :: tail => match v with
          | .true => .next (.pureExpr yes env) tail
          | .false => .next (.pureExpr no env) tail
          | _ => .end_ (.error "PEif condition is not boolean")
      | .effectIf yes no env :: tail => match v with
          | .true => .next (.effectExpr yes env) tail
          | .false => .next (.effectExpr no env) tail
          | _ => .end_ (.error "Eif condition is not boolean")
      | .runLabel s vs rest env :: tail => match rest with
          | p :: ps => .next (.pureExpr p env) (.runLabel s (vs ++ [v]) ps env :: tail)
          | [] => requestJump labels s (vs ++ [v]) env tail
      | .saveArguments syms vs rest body env :: tail => match rest with
          | p :: ps => .next (.pureExpr p env) (.saveArguments syms (vs ++ [v]) ps body env :: tail)
          | [] => .next (.effectExpr body (extendEnv (syms.zip (vs ++ [v])) env)) tail

  let result := if awaitsScheduling unseqWithCall control then scheduledRequest result else result
  if mem.currentLocation == priorLocation then result else
    match result with
    | .next c frames => .next (.setLocation mem.currentLocation c) frames
    | .choose choices => .choose (choices.map fun (c, frames) => (.setLocation mem.currentLocation c, frames))
    | .scheduled choices => .scheduled (choices.map fun (c, frames) => (.setLocation mem.currentLocation c, frames))
    | r => r

termination_by sizeOf control + sizeOf k
decreasing_by
  all_goals try { simp_all only [List.cons.sizeOf_spec]; omega }
  rcases task with ⟨⟨i, c, frames⟩, member⟩
  have h := List.sizeOf_lt_of_mem member
  simp_all
  omega

def request (file : Program) (labels : Labels)
    (state : State) : Request :=
  match requestAux file labels state.memory state.control state.stack with
  | .next (.jumping s vs env) k => jump labels s vs env k
  | r => r

/-- A terminal state has no outgoing transition. All live states have a
request, including states outside the supported language fragment. -/
inductive Step (file : Program) (labels : Labels) :
    State → Label → State → Prop where
  | respond {s t : State} {a : Label} : (∀ o, s.control ≠ .halt o) → Respond s.memory (request file labels s) a t → Step file labels s a t

def lts (file : Program) (labels : Labels) :
    Cslib.LTS State Label where
  Tr := Step file labels

/-- driver.lem:1542-1619 initializes definitions in file order and ignores
declarations. Initializer effects share main's labelled memory transitions. -/
def initial (file : Program) (enums : Map Sym IntegerType := ∅) (args : List String := Startup.execArguments) : Except Outcome (State × Labels) :=
  let definitions := file.globs.filterMap fun (sym, decl) => match decl with
    | .definition _ e => some (sym, e)
    | .declaration _ => none
  let labels := match file.main.bind (fun sym => file.funs.lookup sym) with
    | some (.procedure _ _ _ _ body) => Map.ofList (saves body).reverse
    | _ => ∅
  .ok (⟨.globals definitions args ∅, [], {enumTypes := enums}⟩, labels)

end Silmaril.Cerberus.Core.Dynamics
