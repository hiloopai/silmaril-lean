module

public import Silmaril.Logic.ACL2.Books.Defs
public import Silmaril.Logic.ACL2.Standard.Objects.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Translated

open CategoryTheory Standard

/-- Quoted integers and resolved symbols in this translated fragment. -/
inductive Literal where
  | integer (value : Int)
  | symbol (name : Name)

def Literal.value? : Literal → Option Object
  | .integer value => some (.integer value)
  | .symbol name => (Symbol.ofName? name).map Object.symbol

mutual
  /-- Translated terms preserve the order of both lambda formals and actuals. -/
  inductive Raw where
    | var (name : Name)
    | quote (literal : Literal)
    | ite (test yes no : Raw)
    | call (name : Name) (actuals : RawArgs)
    | lambda (formals : List Name) (body : Raw) (actuals : RawArgs)

  inductive RawArgs where
    | nil
    | cons (head : Raw) (tail : RawArgs)
end

def RawArgs.ofList : List Raw → RawArgs
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def RawArgs.arity : RawArgs → Nat
  | .nil => 0
  | .cons _ tail => tail.arity + 1

def ifName : Name := ⟨"COMMON-LISP", "IF"⟩

mutual
  /-- Every named call site, including primitives and all branches. -/
  def Raw.calls : Raw → List (Name × Nat)
    | .var _ | .quote _ => []
    | .ite test yes no => (ifName, 3) :: (test.calls ++ yes.calls ++ no.calls)
    | .call name actuals => (name, actuals.arity) :: actuals.calls
    | .lambda _ body actuals => body.calls ++ actuals.calls

  def RawArgs.calls : RawArgs → List (Name × Nat)
    | .nil => []
    | .cons head tail => head.calls ++ tail.calls
end

/-- The fixed two-argument primitives used in the projected step body. -/
inductive Primitive where
  | cons | equal | binaryAdd

def Primitive.name : Primitive → Name
  | .cons => ⟨"COMMON-LISP", "CONS"⟩
  | .equal => ⟨"COMMON-LISP", "EQUAL"⟩
  | .binaryAdd => ⟨"ACL2", "BINARY-+"⟩

def Primitive.lookup (name : Name) : Option { p : Primitive // p.name = name } :=
  if h : Primitive.cons.name = name then some ⟨.cons, h⟩
  else if h : Primitive.equal.name = name then some ⟨.equal, h⟩
  else if h : Primitive.binaryAdd.name = name then some ⟨.binaryAdd, h⟩
  else none

def Primitive.eval (op : Primitive) (args : Fin 2 → Object) : Object :=
  match op with
  | .cons => .cons (args 0) (args 1)
  | .equal => (args 0).equal (args 1)
  | .binaryAdd => (args 0).binaryAdd (args 1)

/-- A total denotation for every external declaration, indexed by name and arity. -/
abbrev Interpretation (S : Signature) := ∀ {n}, S.Symbol n → (Fin n → Object) → Object

inductive Callee (S : Signature) (name : Name) (arity : Nat) where
  | primitive (op : Primitive) (named : op.name = name) (binary : arity = 2)
  | external (declared : S.arity name = some arity)

def Callee.resolve (S : Signature) (name : Name) (arity : Nat) : Option (Callee S name arity) :=
  match Primitive.lookup name with
  | some ⟨op, named⟩ => if h : arity = 2 then some (.primitive op named h) else none
  | none => if h : S.arity name = some arity then some (.external h) else none

def Callee.eval {S : Signature} {name : Name} {n : Nat} (M : Interpretation S)
    (callee : Callee S name n) (args : Fin n → Object) : Object :=
  match callee with
  | .primitive op _ h => op.eval (fun i => args (i.cast h.symm))
  | .external declared => M ⟨name, declared⟩ args

mutual
  /-- A typed term indexed by its exact source and its ordered lexical scope.
  A closed translated lambda body has only its own formals in scope. -/
  inductive Checked (S : Signature) : List Name → Raw → Type where
    | var {scope : List Name} {name} (slot : Fin scope.length) (bound : scope.get slot = name) :
        Checked S scope (.var name)
    | quote {scope} {literal : Literal} (value : Object) (decoded : literal.value? = some value) :
        Checked S scope (.quote literal)
    | ite {scope test yes no} : Checked S scope test → Checked S scope yes → Checked S scope no →
        Checked S scope (.ite test yes no)
    | call {scope name} {actuals : RawArgs} : Callee S name actuals.arity → CheckedArgs S scope actuals →
        Checked S scope (.call name actuals)
    | lambda {scope} {formals : List Name} {body} {actuals : RawArgs}
        (distinct : formals.Nodup) (arity : formals.length = actuals.arity) :
        Checked S formals body → CheckedArgs S scope actuals → Checked S scope (.lambda formals body actuals)

  inductive CheckedArgs (S : Signature) : List Name → RawArgs → Type where
    | nil {scope} : CheckedArgs S scope .nil
    | cons {scope head tail} : Checked S scope head → CheckedArgs S scope tail → CheckedArgs S scope (.cons head tail)
end

mutual
  /-- Resolve lexical positions and complete function identities without evaluating a call. -/
  def lower (S : Signature) (scope : List Name) : (raw : Raw) → Option (Checked S scope raw)
    | .var name => do
        let slot ← scope.findFinIdx? (fun formal => decide (formal = name))
        if h : scope.get slot = name then some (.var slot h) else none
    | .quote literal =>
        match h : literal.value? with
        | some value => some (.quote value h)
        | none => none
    | .ite test yes no => do
        return .ite (← lower S scope test) (← lower S scope yes) (← lower S scope no)
    | .call name actuals => do
        return .call (← Callee.resolve S name actuals.arity) (← lowerArgs S scope actuals)
    | .lambda formals body actuals =>
        if distinct : formals.Nodup then
          if arity : formals.length = actuals.arity then do
            return .lambda distinct arity (← lower S formals body) (← lowerArgs S scope actuals)
          else none
        else none

  def lowerArgs (S : Signature) (scope : List Name) :
      (raw : RawArgs) → Option (CheckedArgs S scope raw)
    | .nil => some .nil
    | .cons head tail => do return .cons (← lower S scope head) (← lowerArgs S scope tail)
end

mutual
  /-- Logical evaluation with all external functions abstract. -/
  def Checked.eval {S : Signature} (M : Interpretation S) {scope : List Name} {raw : Raw}
      (env : Fin scope.length → Object) : Checked S scope raw → Object
    | .var slot _ => env slot
    | .quote value _ => value
    | .ite test yes no => if test.eval M env = Object.nil then no.eval M env else yes.eval M env
    | .call callee args => callee.eval M (args.eval M env)
    | .lambda _ arity body args => body.eval M (fun i => args.eval M env (i.cast arity))

  def CheckedArgs.eval {S : Signature} (M : Interpretation S) {scope : List Name} {raw : RawArgs}
      (env : Fin scope.length → Object) : CheckedArgs S scope raw → Fin raw.arity → Object
    | .nil => Fin.elim0
    | .cons head tail => Fin.cases (head.eval M env) (tail.eval M env)
end

/-- A fresh nonrecursive definition over a signature of external declarations. -/
structure Definition (S : Signature) where
  name : Name
  formals : List Name
  distinct : formals.Nodup
  source : Raw
  body : Checked S formals source
  fresh : S.arity name = none

namespace Definition

variable {S : Signature} (D : Definition S)

def signature : Signature := S.add D.name D.formals.length

def symbol : D.signature.Symbol D.formals.length := S.addSymbol D.name D.formals.length

def inclusion : S ⟶ D.signature := Signature.addInclusion D.fresh D.formals.length

/-- Extend a total interpretation by evaluating the checked body at the new symbol. -/
def extend (M : Interpretation S) : Interpretation D.signature :=
  fun {n} f args =>
    if h : f.val = D.name then
      have arity : D.formals.length = n := Option.some.inj (by simpa [signature, Signature.add, h] using f.property)
      D.body.eval M (fun i => args (i.cast arity))
    else M ⟨f.val, by simpa [signature, Signature.add, h] using f.property⟩ args

end Definition

end Silmaril.Logic.ACL2.Translated
