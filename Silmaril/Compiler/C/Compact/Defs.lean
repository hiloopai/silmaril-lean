module

public import Silmaril.Compiler.C.Sem.C0.Defs

/-! A compact projection of a leaf fragment of typed Ail. Every value is LP64 signed `int`.
The tree stores neither per-node types nor symbols/locations. Slots are append-only, with
arguments first and initialized locals in declaration order. The Ail recognizer retains a
separate preorder origin table. -/

@[expose] public section
namespace Silmaril.Compiler.C.Compact

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C Silmaril.Compile.C.Sem

inductive Op where
  | add | gt
  deriving DecidableEq, Repr

def Op.ail : Op → BinaryOperator
  | .add => .arithmetic .add
  | .gt => .gt

inductive Expr where
  | literal (value : Int)
  | slot (index : Nat)
  | bin (op : Op) (left right : Expr)
  deriving DecidableEq, Repr

def Expr.depth : Expr → Nat
  | .literal _ | .slot _ => 1
  | .bin _ left right => max left.depth right.depth + 1

inductive Body where
  | ret (value : Expr)
  | bind (init : Expr) (next : Body)
  | branch (test : Expr) (yes no : Body)
  deriving DecidableEq, Repr

structure Function where
  arity : Nat
  body : Body
  deriving DecidableEq, Repr

def Expr.scoped (slots : Nat) : Expr → Bool
  | .literal value => 0 ≤ value && C0.inRange 4 true value
  | .slot index => index < slots
  | .bin _ left right => left.scoped slots && right.scoped slots

def Body.scoped (slots : Nat) : Body → Bool
  | .ret value => value.scoped slots
  | .bind init next => init.scoped slots && next.scoped (slots + 1)
  | .branch test yes no => test.scoped slots && yes.scoped slots && no.scoped slots

/-- Sufficient C0 loop fuel with the first statement already in focus. -/
def Body.fuel : Body → Nat
  | .ret value => value.depth + 2
  | .bind init next => max (init.depth + 2) (next.fuel + 2)
  | .branch test yes no => max (test.depth + 2) (max yes.fuel no.fuel + 1)

def Op.eval (op : Op) (left right : Int) : Except C0.Stop Int :=
  let lhs := C0.wrap 4 true left
  let rhs := C0.wrap 4 true right
  match op with
  | .add =>
    if C0.inRange 4 true (lhs + rhs) then .ok (lhs + rhs) else C0.ub "signed integer overflow"
  | .gt => .ok (if lhs > rhs then 1 else 0)

/-- Pure, left-to-right expression evaluation, with the C0 signed-32 arithmetic domain.
`read` specifies the initialized-slot observation and the error on a missing slot. -/
def Expr.eval (read : Nat → Except C0.Stop Int) : Expr → Except C0.Stop Int
  | .literal value => .ok (C0.wrap 4 true value)
  | .slot index => read index
  | .bin op left right => do op.eval (← left.eval read) (← right.eval read)

def readSlot (slots : Array Int) (index : Nat) : Except C0.Stop Int :=
  match slots[index]? with
  | some value => .ok value
  | none => .error (.unsupported "compact slot outside the initialized scope")

/-- Only the chosen branch runs. Bindings extend the store after the initializer succeeds. -/
def Body.run (slots : Array Int) : Body → Except C0.Stop Int
  | .ret value => value.eval (readSlot slots)
  | .bind init next => do next.run (slots.push (← init.eval (readSlot slots)))
  | .branch test yes no => do
    if (← test.eval (readSlot slots)) != 0 then yes.run slots else no.run slots

/-- Signed `int` arguments must already be in range. No memory, globals, output or calls. -/
def Function.run (fn : Function) (args : Array Int) : Except C0.Stop Int :=
  if args.size == fn.arity && args.toList.all (C0.inRange 4 true) && fn.body.scoped fn.arity then
    fn.body.run args
  else .error (.unsupported "invalid compact function or arguments")

def valueType (ty : GenIntegerType) : GenTypeCategory := .rvalue (.basic (.integer ty))

def checkInt : (ctype : CType) → Option (PLift (ctype = .int 4 true))
  | .int 4 true => some ⟨rfl⟩
  | _ => none

def plainInt : Qualifiers → Ctype → Bool
  | ⟨false, false, false⟩, .mk _ (.basic (.integer (.signed .int))) => true
  | _, _ => false

/-- The projection relation keeps the exact Ail node, including annotations and locations.
The slot relation uses structural symbol identity; it does not conflate distinct symbols
that happen to share a printable name. -/
inductive Projects (scope : List Sym) : Expr → TypedExpression → Prop where
  | literal {ty : GenIntegerType} (typed : ofGenType (.basic (.integer ty)) = .int 4 true)
      (value : Int) (annots : List Annot) (loc : Loc) :
      Projects scope (.literal value)
        (.mk (valueType ty) annots loc (.const (.integer (.iconstant value .decimal none))))
  | slot {index : Nat} {symbol : Sym} (lookup : scope[index]? = some symbol)
      {ty : GenIntegerType} (typed : ofGenType (.basic (.integer ty)) = .int 4 true)
      (quals : Qualifiers) (ctype : Ctype) (annots innerAnnots : List Annot) (loc innerLoc : Loc) :
      Projects scope (.slot index)
        (.mk (valueType ty) annots loc (.rvalue (.mk (.lvalue quals ctype false) innerAnnots innerLoc
          (.ident symbol))))
  | bin {left right : Expr} {ailLeft ailRight : TypedExpression} (op : Op)
      {ty : GenIntegerType} (typed : ofGenType (.basic (.integer ty)) = .int 4 true)
      (annots : List Annot) (loc : Loc)
      (lhs : Projects scope left ailLeft) (rhs : Projects scope right ailRight) :
      Projects scope (.bin op left right) (.mk (valueType ty) annots loc (.binary ailLeft op.ail ailRight))

structure ExprProjection (scope : List Sym) (ail : TypedExpression) where
  expr : Expr
  origins : List Loc
  projects : Projects scope expr ail

/-- A bounded, rejecting projection, not a type checker for arbitrary C text. -/
def projectExpr (scope : List Sym) : (fuel : Nat) → (ail : TypedExpression) →
    Except String (ExprProjection scope ail)
  | 0, _ => .error "compact expression depth exceeded"
  | fuel + 1, .mk (.rvalue (.basic (.integer ty))) annots loc node => do
    let some ⟨typed⟩ := checkInt (ofGenType (.basic (.integer ty))) | throw "not a signed-int rvalue"
    match (dependent := true) node with
    | .const (.integer (.iconstant value .decimal none)) => do
      unless 0 ≤ value && C0.inRange 4 true value do throw "literal outside signed int"
      return ⟨.literal value, [loc], .literal typed value annots loc⟩
    | .rvalue (.mk (.lvalue quals ctype false) innerAnnots innerLoc (.ident symbol)) => do
      unless plainInt quals ctype do throw "not an unqualified signed-int object"
      let some index := scope.findIdx? (fun candidate => decide (candidate = symbol))
        | throw "object outside initialized scope"
      if lookup : scope[index]? = some symbol then
        return ⟨.slot index, [loc], .slot lookup typed quals ctype annots innerAnnots loc innerLoc⟩
      else throw "object outside initialized scope"
    | .binary left (.arithmetic .add) right => do
      let lhs ← projectExpr scope fuel left
      let rhs ← projectExpr scope fuel right
      return ⟨.bin .add lhs.expr rhs.expr, loc :: lhs.origins ++ rhs.origins,
        .bin .add typed annots loc lhs.projects rhs.projects⟩
    | .binary left .gt right => do
      let lhs ← projectExpr scope fuel left
      let rhs ← projectExpr scope fuel right
      return ⟨.bin .gt lhs.expr rhs.expr, loc :: lhs.origins ++ rhs.origins,
        .bin .gt typed annots loc lhs.projects rhs.projects⟩
    | _ => .error "unsupported compact expression"
  | _, _ => .error "not a signed-int rvalue"

structure Origin where
  location : Loc
  binder : Option String := none
  deriving DecidableEq, Repr

structure Projection where
  fn : Function
  name : String
  arguments : List String
  origins : List Origin
  deriving DecidableEq, Repr

def symbolName (symbol : Sym) : String := match symbol.description with
  | .id name | .objectAddress name => name
  | _ => ""

def exprOrigins (locations : List Loc) : List Origin := locations.map fun loc => ⟨loc, none⟩

/-- Ail's terminal statement trees have no continuation after a leaf return. -/
inductive TerminalProjects (scope : List Sym) : Body → TypedStatement → Prop where
  | ret {value ail} {loc desug attrs} (matched : Projects scope value ail) :
      TerminalProjects scope (.ret value) (.mk loc desug attrs (.return_ ail))
  | branch {test yes no ailTest ailYes ailNo} {loc desug attrs}
      (testMatch : Projects scope test ailTest) (yesMatch : TerminalProjects scope yes ailYes)
      (noMatch : TerminalProjects scope no ailNo) :
      TerminalProjects scope (.branch test yes no) (.mk loc desug attrs (.if_ ailTest ailYes ailNo))

/-- Match compact bindings, in order, to single initialized Ail declarations. Numeric
symbol freshness is needed because C0's local store uses symbol numbers as keys. -/
inductive BlockProjects : List Sym → List Sym → Body → List TypedStatement → Prop where
  | terminal {scope body ail} (matched : TerminalProjects scope body ail) :
      BlockProjects scope [] body [ail]
  | bind {scope : List Sym} {symbol : Sym} {rest init next ailInit ailNext} {loc desug attrs}
      (fresh : ∀ previous ∈ scope, previous.number ≠ symbol.number)
      (valueMatch : Projects scope init ailInit)
      (nextMatch : BlockProjects (scope ++ [symbol]) rest next ailNext) :
      BlockProjects scope (symbol :: rest) (.bind init next)
        (.mk loc desug attrs (.declaration [(symbol, some ailInit)]) :: ailNext)

structure TerminalProjection (scope : List Sym) (ail : TypedStatement) where
  body : Body
  origins : List Origin
  projects : TerminalProjects scope body ail

structure BlockProjection (scope bindings : List Sym) (ail : List TypedStatement) where
  body : Body
  origins : List Origin
  projects : BlockProjects scope bindings body ail

/-- The result of extraction describes the sole original Ail function body, not a
reconstructed statement. This witness concerns tree structure, not the Core semantics. -/
structure FunctionProjects (ail : TypedProgram) (fn : Function) : Prop where
  shape : ∃ (symbol : Sym) (source : FunctionDefinition GenTypeCategory)
    (loc : Loc) (bindings : Bindings) (statements : List TypedStatement) (locals : List Sym),
    ail.2.functionDefinitions = [(symbol, source)] ∧
    source.body = .mk loc ⟨false, none⟩ (.mk []) (.block bindings statements) ∧
    fn.arity = source.params.length ∧ locals = bindings.map Prod.fst ∧
    BlockProjects source.params locals fn.body statements
  wellScoped : fn.body.scoped fn.arity = true

structure CheckedProjection (ail : TypedProgram) where
  value : Projection
  projects : FunctionProjects ail value.fn

/-- Every compact slot denotes an initialized, in-range local in the current C0 activation. -/
structure SlotState (scope : List Sym) (slots : Array Int) (env : C0.Env) : Prop where
  size : slots.size = scope.length
  initialized : ∀ (index : Nat) (symbol : Sym), scope[index]? = some symbol →
    ∃ value, slots[index]? = some value ∧ env.locals[symbol.number]? = some value ∧
      C0.inRange 4 true value = true

/-- A return is a signed `int`; the only allowed stop is checked signed addition overflow. -/
def IntOutcome : Except C0.Stop Int → Prop
  | .ok value => C0.inRange 4 true value = true
  | .error stop => stop = .undefined "signed integer overflow"

/-- Observe a finished C0 activation as its caller would: private locals are discarded,
but globals, output, return and stops are retained. -/
def observeActivation (caller : C0.Env) : Except C0.Stop (Option Int × C0.Env) →
    Except C0.Stop (Option Int × C0.Env) :=
  Except.map fun (returned, env) => (returned, { env with locals := caller.locals })

/-- Branches are terminal: both arms must themselves return or branch. -/
def projectTerminal (scope : List Sym) : Nat → (ail : TypedStatement) →
    Except String (TerminalProjection scope ail)
  | 0, _ => .error "compact statement depth exceeded"
  | fuel + 1, .mk loc ⟨false, none⟩ (.mk []) node => do
    match (dependent := true) node with
    | .return_ value => do
      let item ← projectExpr scope 256 value
      return ⟨.ret item.expr, ⟨loc, none⟩ :: exprOrigins item.origins, .ret item.projects⟩
    | .if_ test yes no => do
      let cond ← projectExpr scope 256 test
      let lhs ← projectTerminal scope fuel yes
      let rhs ← projectTerminal scope fuel no
      return ⟨.branch cond.expr lhs.body rhs.body,
        ⟨loc, none⟩ :: exprOrigins cond.origins ++ lhs.origins ++ rhs.origins,
        .branch cond.projects lhs.projects rhs.projects⟩
    | _ => .error "expected return or terminal if"
  | _, _ => .error "unsupported statement attributes or desugaring"

def projectBlock (scope : List Sym) : (bindings : List Sym) → (ail : List TypedStatement) →
    Except String (BlockProjection scope bindings ail)
  | [], [last] => do
    let item ← projectTerminal scope 256 last
    return ⟨item.body, item.origins, .terminal item.projects⟩
  | symbol :: bindings, .mk loc ⟨false, none⟩ (.mk []) (.declaration [(actual, some init)]) :: rest => do
    if same : symbol = actual then
      if allFresh : symbol.number ∉ scope.map Sym.number then
        let value ← projectExpr scope 256 init
        let next ← projectBlock (scope ++ [symbol]) bindings rest
        have fresh : ∀ (previous : Sym), previous ∈ scope → previous.number ≠ symbol.number := by
          intro previous mem equal
          exact allFresh (List.mem_map.mpr ⟨previous, mem, equal⟩)
        return ⟨.bind value.expr next.body,
          ⟨loc, some (symbolName symbol)⟩ :: exprOrigins value.origins ++ next.origins,
          by subst actual; exact .bind fresh value.projects next.projects⟩
      else throw "duplicate object identity"
    else throw "declarations do not match block bindings in order"
  | _, _ => .error "expected initialized local declarations followed by a terminal statement"

/-- Accept one function definition and one matching declaration in a translation unit.
The discarded Ail environment is not needed to evaluate this fragment. The original Ail,
not a reconstructed surrogate, remains the input to Cerberus elaboration. -/
def projectFunction (ail : TypedProgram) (symbol : Sym) (fn : FunctionDefinition GenTypeCategory)
    (functions : ail.2.functionDefinitions = [(symbol, fn)]) : Except String (CheckedProjection ail) := do
  let sigma := ail.2
  let [(decl, (_, .mk [], .function _ (quals, result) args false false false))] := sigma.declarations
    | throw "expected a single non-variadic function declaration without attributes"
  unless symbol = decl && plainInt quals result && args.length = fn.params.length &&
      args.all (fun (qual, ty, reg) => !reg && plainInt qual ty) do
    throw "not a signed-int function signature"
  unless sigma.loopAttributes.isEmpty do throw "loop metadata is outside the compact fragment"
  unless sigma.objectDefinitions.isEmpty && sigma.staticAssertions.isEmpty &&
      sigma.tagDefinitions.isEmpty && sigma.typedefAttributes.isEmpty &&
      sigma.cnFunctions.isEmpty && sigma.cnLemmata.isEmpty && sigma.cnPredicates.isEmpty &&
      sigma.cnDatatypes.isEmpty && sigma.cnDeclSpecs.isEmpty && sigma.cnIdents.isEmpty do
    throw "unsupported top-level declarations"
  let .mk [] := fn.attrs | throw "unsupported function attributes"
  match outer : fn.body with
  | .mk loc ⟨false, none⟩ (.mk []) (.block bindings statements) => do
    unless bindings.all (fun (_, (_, align, qual, ctype)) => align.isNone && plainInt qual ctype) do
      throw "unsupported local type"
    let locals := bindings.map Prod.fst
    unless bindings.all (fun (_, ((_, dur, reg), _)) => dur == .automatic && !reg) do
      throw "non-automatic or register binding"
    let numbers := fn.params.map (·.number)
    unless numbers.eraseDups.length == numbers.length do throw "duplicate object identity"
    let block ← projectBlock fn.params locals statements
    if valid : block.body.scoped fn.params.length = true then
      return ⟨⟨⟨fn.params.length, block.body⟩, symbolName symbol, fn.params.map symbolName, block.origins⟩,
        ⟨⟨symbol, fn, loc, bindings, statements, locals, functions, outer, rfl, rfl, block.projects⟩, valid⟩⟩
    else throw "invalid compact body"
  | _ => throw "expected a single function block"

def projectChecked (ail : TypedProgram) : Except String (CheckedProjection ail) :=
  match functions : ail.2.functionDefinitions with
  | [(symbol, fn)] => projectFunction ail symbol fn functions
  | _ => .error "expected exactly one function body"

def project (ail : TypedProgram) : Except String Projection :=
  (projectChecked ail).map (·.value)

end Silmaril.Compiler.C.Compact
