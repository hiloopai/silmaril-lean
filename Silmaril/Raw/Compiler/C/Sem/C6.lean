module

public import Silmaril.Compiler.C.Sem.C6Interp.Defs
@[expose] public section

/-!
# C6: compound literals, statement expressions and members of structure values

C6 extends C5 with three expression forms that produce or name unnamed objects. Everything
else is C5's.

* **Compound literals** `(T){ init }` (STD §6.5.2.5) in a function body: an lvalue designating
  an unnamed object of type `T` (an array of unknown size takes the size its initializer gives,
  as Cerberus's typing already records), initialised from `init` as a declaration of that type
  would be (STD §6.5.2.5#6, §6.7.9). The object has automatic storage duration associated with
  the enclosing block (STD §6.5.2.5#5): one object per occurrence and activation of the
  function, and every evaluation of the literal re-initialises that same object (STD
  §6.5.2.5#15, EXAMPLE 8: a literal reached twice through a `goto` within its block designates
  one object, so the two addresses compare equal). As C1 does for block-scope objects, the
  object stays addressable until its function returns: an access after its block has ended is
  not detected (C6 is more defined than C there).
* **Statement expressions** `({ s₁ … sₙ })` (a GNU extension, gcc manual "Statements and
  Declarations in Expressions"): a block evaluated in expression position. Its declarations
  are scoped to it; its value is that of `sₙ` when `sₙ` is an expression statement (after
  lvalue conversion, so an aggregate is copied), and it is `void` otherwise. C6 takes only
  bodies without jumps or labels (`goto`, `return`, `break`, `continue`, `switch`, `case`,
  `default`, labelled statements), since gcc leaves jumps into a statement expression undefined
  and C6 declines jumps out of one.
* **Members of structure and union values** `e.m` where `e` is not an lvalue (a call, an
  assignment, a conditional or comma expression, a statement expression, or such a member
  itself): the member of the value (STD §6.5.2.3#3; the value is not an lvalue). Array
  members of such values, whose decay would need the temporary lifetime of STD §6.2.4#8, are
  outside C6.

Compound literals at file scope (static storage duration) are outside C6.

The fragment is `check` below: C5's check with these forms added, and the functions reachable
from `main` found through compound-literal initializers and statement-expression bodies as
well. `run` executes C5 on C5's fragment and the extended evaluator elsewhere.

## Statement: C6 extends C5 on C5's fragment

The ladder law `C5.sem ⊑[C5.fragment] C6.sem` holds with exact equality of behaviours:
`run` delegates to the frozen C5 interpreter when `C5.check` succeeds. `C6Ladder.lean` proves
`Targets.c6_extends_c5`, including undefined behaviour and divergence. The driver tries
C1 → … → C5 before C6, so the extended evaluator runs only programs C5 rejects.
-/

namespace Silmaril.Compile.C.Sem.C6

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C Silmaril.Compile.Category
open C0 (Result)
open C1 (FunDef externals plainString)
open C4 (Prog prepare isFunction checkFloat checkC callTypes)
open C5 (heapExternals checkCallShape)

/-! ## The interpreter -/

/-- **The C6 interpreter.** The C5 fragment uses C5 itself, preserving every fuel-indexed
result exactly. Other programs use the extended evaluator. -/
def run (fuel : Nat) (p : TypedProgram) : Result :=
  if C5.check p = .ok () then C5.run fuel p else runExtended fuel p

/-- The preservation law is by construction, including UB and divergence. -/
theorem run_eq_c5 {p : TypedProgram} (h : C5.InFragment p) (fuel : Nat) :
    run fuel p = C5.run fuel p := by
  simp only [run, C5.InFragment] at *
  rw [ite_eq_left h]

/-! ## Behaviours and the language -/

/-- The behaviours of a program under C6, as for C0 (`C0.beh`). -/
def beh (p : TypedProgram) : Set Obs := {o |
  (∃ n, run n p = .done o) ∨ (∃ n why, run n p = .undefined why) ∨
    (o = ⟨[], .diverges⟩ ∧ ∀ n, run n p = .outOfFuel)}

/-- C6 as a semantics of C. -/
def sem : Semantics := beh

/-- C6 as a language of the zoo. -/
def lang : Language.{0} := cSyntax.lang sem

theorem beh_of_done {p : TypedProgram} {n : Nat} {o : Obs} (h : run n p = .done o) :
    o ∈ beh p := .inl ⟨n, h⟩

/-- Undefined behaviour allows every behaviour. -/
theorem beh_of_undefined {p : TypedProgram} {n : Nat} {why : String}
    (h : run n p = .undefined why) : beh p = Set.univ :=
  Set.eq_univ_of_forall fun _ => .inr (.inl ⟨n, why, h⟩)

/-! ## Reachability -/

mutual
/-- The symbols an expression mentions as identifiers and the functions it calls directly,
including those of compound-literal initializers and statement-expression bodies. -/
def callsE : TypedExpression → List Nat
  | .mk _ _ _ node => callsN node
def callsN : ExpressionNode GenTypeCategory → List Nat
  | .ident x => [x.number]
  | .call f args =>
    (match f.node with
      | .functionDecay ⟨_, _, _, .ident g⟩ => [g.number]
      | _ => callsE f) ++ callsL args
  | .unary _ a | .annot _ a | .cast _ _ a | .assert a | .rvalue a | .sizeofExpr a
  | .functionDecay a | .arrayDecay a | .memberof a _ | .memberofptr a _
  | .vaStart a _ | .vaArg a _ | .vaEnd a | .compound _ _ a => callsE a
  | .binary a _ b | .assign a b | .compoundAssign a _ b | .vaCopy a b => callsE a ++ callsE b
  | .cond c a b => callsE c ++ (match a with | some a => callsE a | none => []) ++ callsE b
  | .array _ _ es => callsO es
  | .struct _ ms => callsM ms
  | .union _ _ (some e) => callsE e
  | .generic _ _ gs => callsG gs
  | .gccStatement _ ss => callsSL ss
  | _ => []
def callsL : List TypedExpression → List Nat
  | [] => []
  | e :: es => callsE e ++ callsL es
def callsO : List (Option TypedExpression) → List Nat
  | [] => []
  | none :: es => callsO es
  | some e :: es => callsE e ++ callsO es
def callsM : List (Identifier × Option TypedExpression) → List Nat
  | [] => []
  | (_, none) :: ms => callsM ms
  | (_, some e) :: ms => callsE e ++ callsM ms
def callsG : List (GenericAssociation GenTypeCategory) → List Nat
  | [] => []
  | .type_ _ _ e :: gs | .default e :: gs => callsE e ++ callsG gs
def callsS : TypedStatement → List Nat
  | .mk _ _ _ node => callsSN node
def callsSN : StatementNode GenTypeCategory → List Nat
  | .expr e | .return_ e => callsE e
  | .block _ ss | .par ss => callsSL ss
  | .if_ c a b => callsE c ++ callsS a ++ callsS b
  | .while_ c b _ | .do_ b c _ | .switch c b => callsE c ++ callsS b
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => callsS b
  | .declaration ds => callsD ds
  | _ => []
def callsSL : List TypedStatement → List Nat
  | [] => []
  | s :: ss => callsS s ++ callsSL ss
def callsD : List (Sym × Option TypedExpression) → List Nat
  | [] => []
  | (_, some e) :: ds => callsE e ++ callsD ds
  | (_, none) :: ds => callsD ds
end

/-- The functions defined in the program and reachable from `roots` by direct calls. -/
def reachable (P : Prog) (roots : List Nat) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo := roots
  let mut out : Array Nat := #[]
  for _ in [0:P.funcs.size + roots.length + 1] do
    let mut next : List Nat := []
    for f in todo do
      if seen.contains f then continue
      seen := seen.insert f
      if let some fd := P.funcs[f]? then
        out := out.push f
        next := callsS fd.body ++ next
    todo := next
  return out.toList

/-! ## The fragment -/

mutual
/-- Is a statement-expression body free of jumps and labels? -/
def jumpFree : TypedStatement → Bool
  | .mk _ _ _ node => jumpFreeN node
def jumpFreeN : StatementNode GenTypeCategory → Bool
  | .skip | .expr _ | .declaration _ => true
  | .block _ ss => jumpFreeL ss
  | .if_ _ a b => jumpFree a && jumpFree b
  | .while_ _ b _ | .do_ b _ _ | .marker _ b => jumpFree b
  | _ => false
def jumpFreeL : List TypedStatement → Bool
  | [] => true
  | s :: ss => jumpFree s && jumpFreeL ss
end

/-- The context of a check: the function, whether the check is inside a statement expression,
the locals of the enclosing statement expressions (with their blocks'), and whether the check
is at file scope (an initializer of an object of static storage duration). -/
structure Ctx where
  fd : FunDef
  inSE : Bool := false
  seLocals : List (Nat × Ctype) := []
  fileScope : Bool := false

/-- The locals of a statement have types of C6. -/
def checkLocals (P : Prog) (bs : Bindings) : Except String Unit := do
  for (x, (_, _, _, ty)) in bs do
    if !P.obj ty then throw s!"local {Silmaril.Compile.Forks.Csem.C.symName x} of a type outside C6"

/-- The locals of a block, as `(number, type)`. -/
def bindingTypes (bs : Bindings) : List (Nat × Ctype) :=
  bs.map fun (x, (_, _, _, ty)) => (x.number, ty)

/-- The expression of the last statement of a statement-expression body, if it is one. -/
def lastExpr : List TypedStatement → Option TypedExpression
  | [] => none
  | [.mk _ _ _ (.expr e)] => some e
  | [_] => none
  | _ :: ss => lastExpr ss

/-- The conditions on a statement expression besides its body's statements; `agg` says its
value is a structure or union. -/
def seGuard (P : Prog) (c : Ctx) (bs : Bindings) (ss : List TypedStatement) (agg : Bool) :
    Except String Unit := do
  if c.fileScope then throw "a statement expression at file scope"
  if !jumpFreeL ss then throw "a statement expression with a jump or a label"
  checkLocals P bs
  if agg && (lastExpr ss).isNone then
    throw "a statement expression without a value of its type"

/-- The context of a statement-expression body. -/
def Ctx.enterSE (c : Ctx) (bs : Bindings) : Ctx :=
  { c with inSE := true, seLocals := bindingTypes bs ++ c.seLocals }

mutual
/-- Check a function designator, including the targets whose addresses escape. -/
def checkF (P : Prog) (c : Ctx) : TypedExpression → Except String Unit
  | .mk _ _ _ node => do
  match node with
  | .ident g =>
    if !P.symbols.contains g.number then throw "an undeclared function designator"
    if !P.funcs.contains g.number && !(externals.contains (P.name g)) &&
        !(heapExternals.contains (P.name g)) && (C3.F.libm (P.name g)).isNone then
      throw s!"address of the external function {P.name g}"
  | .unary .indirection p => checkE P c p
  | .annot _ a => checkF P c a
  | _ => throw "a function designator outside C6"

/-- Check that an rvalue is in the fragment. -/
def checkE (P : Prog) (c : Ctx) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue .. => throw "an lvalue in value position"
    | .rvalue g =>
      let t := ofGenType g
      if P.aggType t then checkA P c node
      else
        if !P.valueType t then throw "an expression of a type outside C6"
        checkN P c node
/-- Check an expression of a struct or union type. -/
def checkA (P : Prog) (c : Ctx) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a => checkLv P c a
  | .vaArg ap _ => checkE P c ap
  | .assign l r => do checkLv P c l; checkE P c r
  | .call f args => do checkCallShape P f args; checkE P c f; checkL P c args
  | .cond c' (some a) b => do checkE P c c'; checkE P c a; checkE P c b
  | .binary a .comma b => do checkE P c a; checkE P c b
  | .annot _ a => checkE P c a
  | .memberof a _ =>
    match a with
    | .mk (.lvalue ..) _ _ _ => checkLv P c a
    | .mk (.rvalue _) _ _ _ => checkE P c a
  | .gccStatement bs ss => do seGuard P c bs ss true; checkSL P (c.enterSE bs) ss
  | _ => throw "an aggregate expression outside C6"
def checkN (P : Prog) (c : Ctx) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a | .arrayDecay a => checkLv P c a
  | .functionDecay a => checkF P c a
  | .vaStart _ _ => pure ()
  | .vaArg a _ | .vaEnd a => checkE P c a
  | .vaCopy _ b => checkE P c b
  | .const k =>
    match k with
    | .integer _ | .character _ | .predefined _ | .null => pure ()
    | .floating fc => checkFloat fc
    | _ => throw "a constant outside C6"
  | .annot _ a | .cast _ _ a | .assert a => checkE P c a
  | .unary op a =>
    match op with
    | .plus | .minus | .bnot => checkE P c a
    | .address => if isFunction a then checkF P c a else checkLv P c a
    | .postfixIncr | .postfixDecr => checkLv P c a
    | .indirection => throw "an indirection outside an lvalue"
  | .binary a _ b => do checkE P c a; checkE P c b
  | .assign l r | .compoundAssign l _ r => do checkLv P c l; checkE P c r
  | .cond c' a b => do
    checkE P c c'
    match a with
    | some a => checkE P c a
    | none => pure ()
    checkE P c b
  | .call f args => do checkCallShape P f args; checkE P c f; checkL P c args
  | .sizeof _ ty | .alignof _ ty => P.sized ty
  | .offsetof ty m => do let _ ← P.memberS ty m
  | .sizeofExpr _ => pure ()
  | .generic _ (some _) assocs => checkG P c assocs
  | .memberof a _ =>
    match a with
    | .mk (.lvalue ..) _ _ _ => checkLv P c a
    | .mk (.rvalue _) _ _ _ => checkE P c a
  | .gccStatement bs ss => do seGuard P c bs ss false; checkSL P (c.enterSE bs) ss
  | _ => throw "an expression outside the fragment"
/-- Check that an lvalue is in the fragment. -/
def checkLv (P : Prog) (c : Ctx) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue _ ty _ => if !P.obj ty then throw "an object of a type outside C6"
    | .rvalue _ => throw "an rvalue in lvalue position"
    match node with
    | .ident _ => pure ()
    | .unary .indirection p => checkE P c p
    | .memberof a _ => checkLv P c a
    | .memberofptr p _ => do
      checkE P c p
      match typeOf p with
      | .ptr sty => if !P.obj sty then throw "a member of an incomplete struct or union"
      | _ => throw "a member through a non-pointer"
    | .str s => if !plainString s then throw "a wide string literal"
    | .annot _ a => checkLv P c a
    | .compound _ ty init => do
      if c.fileScope then throw "a compound literal at file scope"
      checkI P c ty init
    | _ => throw "an lvalue outside C6"
def checkL (P : Prog) (c : Ctx) : List TypedExpression → Except String Unit
  | [] => pure ()
  | e :: es => do checkE P c e; checkL P c es
def checkG (P : Prog) (c : Ctx) : List (GenericAssociation GenTypeCategory) →
    Except String Unit
  | [] => pure ()
  | .type_ _ _ e :: gs | .default e :: gs => do checkE P c e; checkG P c gs

/-- Check an initializer of an object of type `ty` (C5's `checkI`, by structure rather than
with a depth bound). -/
def checkI (P : Prog) (c : Ctx) : Ctype → TypedExpression → Except String Unit
  | ty, .mk ann _ _ node =>
    match ty, node with
    | .mk _ (.array et _), .array _ _ elems => checkIO P c et elems
    | .mk _ (.array _ _), .str s => if plainString s then pure () else throw "a wide string literal"
    | .mk _ (.array _ _), .const k => checkC k
    | .mk _ (.array _ _), _ => throw "an array initializer outside C6"
    | .mk _ (.struct _), .struct _ ms | .mk _ (.union _), .struct _ ms => checkIM P c ty ms
    | .mk _ (.struct _), .union _ m (some x) | .mk _ (.union _), .union _ m (some x) => do
      checkI P c (← P.memberS ty m).2 x
    | .mk _ (.struct _), .union _ _ none | .mk _ (.union _), .union _ _ none => pure ()
    | .mk _ (.struct _), .const k | .mk _ (.union _), .const k => checkC k
    | _, nd => do
      let agg := match ty with
        | .mk _ (.struct _) | .mk _ (.union _) => true
        | _ => false
      if !agg && !P.valueType (ofCtype ty) then
        throw "an initializer of an object without values in C6"
      match ann with
      | .lvalue .. => throw "an lvalue in value position"
      | .rvalue g =>
        let t := ofGenType g
        if P.aggType t then checkA P c nd
        else
          if !P.valueType t then throw "an expression of a type outside C6"
          checkN P c nd
def checkIO (P : Prog) (c : Ctx) (et : Ctype) :
    List (Option TypedExpression) → Except String Unit
  | [] => pure ()
  | some x :: xs => do checkI P c et x; checkIO P c et xs
  | none :: xs => checkIO P c et xs
def checkIM (P : Prog) (c : Ctx) (ty : Ctype) :
    List (Identifier × Option TypedExpression) → Except String Unit
  | [] => pure ()
  | (m, some x) :: ms => do checkI P c (← P.memberS ty m).2 x; checkIM P c ty ms
  | (_, none) :: ms => checkIM P c ty ms

def checkS (P : Prog) (c : Ctx) : TypedStatement → Except String Unit
  | .mk _ _ _ node => checkSN P c node
def checkSN (P : Prog) (c : Ctx) : StatementNode GenTypeCategory → Except String Unit
  | .skip | .break_ | .continue_ | .returnVoid | .goto _ => pure ()
  | .expr e | .return_ e => checkE P c e
  | .block bs ss => do
    checkLocals P bs
    checkSL P (if c.inSE then { c with seLocals := bindingTypes bs ++ c.seLocals } else c) ss
  | .if_ e a b => do checkE P c e; checkS P c a; checkS P c b
  | .while_ e b _ | .do_ b e _ => do checkE P c e; checkS P c b
  | .switch e b => do checkE P c e; checkS P c b
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => checkS P c b
  | .declaration ds => checkD P c ds
  | _ => throw "a statement outside the fragment"
def checkSL (P : Prog) (c : Ctx) : List TypedStatement → Except String Unit
  | [] => pure ()
  | s :: ss => do checkS P c s; checkSL P c ss
def checkD (P : Prog) (c : Ctx) : List (Sym × Option TypedExpression) → Except String Unit
  | [] => pure ()
  | (x, some e) :: ds => do
    match c.fd.memLocals.find? (·.1 == x.number) with
    | some (_, ty) => checkI P c ty e
    | none =>
      match c.seLocals.find? (·.1 == x.number) with
      | some (_, ty) => checkI P c ty e
      | none => checkE P c e
    checkD P c ds
  | (_, none) :: ds => checkD P c ds
end

/-- Is the program in the C6 fragment? The reason when it is not. Only the functions reachable
from `main` are checked, and the initializers of the objects of static storage duration whose
type is in C6 (the others are left zero, and their uses are rejected where they occur). -/
def check (p : TypedProgram) : Except String Unit := do
  let P := prepare p
  let some m := P.main | throw "no main"
  let some _ := P.funcs[m]? | throw "main is not defined"
  let live := reachable P
    (m :: (P.statics.flatMap fun (_, _, i) => (i.map callsE).getD []))
  for (x, (_, _, d)) in p.2.declarations do
    match d with
    | .function _ (_, ret) ps _ _ _ =>
      if live.contains x.number then
        let r := ofCtype ret
        if !P.valueType r && !P.aggType r then
          throw s!"a function with a result outside C6: {Silmaril.Compile.Forks.Csem.C.symName x}"
        if ps.any fun (_, t, _) =>
            !P.obj t || !((C3.width (ofCtype t)).isSome || P.aggType (ofCtype t)) then
          throw s!"a function with a parameter outside C6: {Silmaril.Compile.Forks.Csem.C.symName x}"
    | .object .. => pure ()
  for (_, ty, init) in P.statics do
    if P.obj ty then
      if let some e := init then checkI P { fd := C1.topFrame, fileScope := true } ty e
  for f in live do
    if let some fd := P.funcs[f]? then checkS P { fd } fd.body

/-- The C6 fragment. -/
def InFragment (p : TypedProgram) : Prop := check p = .ok ()

instance (p : TypedProgram) : Decidable (InFragment p) :=
  inferInstanceAs (Decidable (check p = .ok ()))

/-- The fragment as a set of programs. -/
def fragment : Set TypedProgram := {p | InFragment p}

end Silmaril.Compile.C.Sem.C6
