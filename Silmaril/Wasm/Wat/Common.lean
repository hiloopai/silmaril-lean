module

public meta import Silmaril.Wasm.Types
public meta import Silmaril.Wasm.Wat.Lexer

/-! # Shared WAT elaboration infrastructure

Profile-independent terms, diagnostics, names, index spaces, and function headers.
Type parsers remain parameters so scalar and Core3 declarations share the same
parameter binding and signature-order rules.
-/

public meta section

open Lean
namespace Silmaril.Wasm.Wat

abbrev Term := TSyntax `term

def termName (name : String) : Term := ⟨mkIdent name.toName⟩
def natTerm (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩

def applyTerm (name : String) (args : Array Term := #[]) : MacroM Term := do
  let f := termName name
  if args.isEmpty then return f else `($f $args*)

def coreTerm (family name : String) (args : Array Term := #[]) : MacroM Term :=
  applyTerm ("Silmaril.Wasm." ++ family ++ "." ++ name) args

def listTerm (xs : List Term) : MacroM Term := do
  let xs := xs.toArray
  `([$xs,*])

def watError {α : Type} (n : Node) (msg : String) : MacroM α :=
  Macro.throwError s!"WAT at character {n.pos}: {msg}"

def checked {α : Type} (n : Node) (result : Except String α) : MacroM α :=
  match result with
  | .ok value => pure value
  | .error msg => watError n msg

def atom (n : Node) : MacroM String := match n with
  | .atom _ s => pure s
  | _ => watError n "expected an unquoted token"

def nameString (n : Node) : MacroM String := match n with
  | .string _ bytes => match String.fromUTF8? bytes with
      | some s => pure s
      | none => watError n "name is not valid UTF-8"
  | _ => watError n "expected a quoted name"

def identifier (n : Node) : MacroM String := do
  if let .quotedIdentifier _ bytes := n then
    let some name := String.fromUTF8? bytes | watError n "identifier is not valid UTF-8"
    unless !name.isEmpty do watError n "identifier must not be empty"
    return "$" ++ name
  let s ← atom n
  unless s.startsWith "$" && s.length > 1 && (s.drop 1).toString.toList.all idChar do
    watError n "invalid symbolic identifier"
  return s

def takeName : List Node → MacroM (Option String × List Node)
  | n :: rest => if n.isIdentifier then do
      return (some (← identifier n), rest)
    else pure (none, n :: rest)
  | [] => pure (none, [])

abbrev Names := List (Option String)

def addName (origin : Node) (names : Names) (name : Option String) : MacroM Names := do
  if let some name := name then
    if names.contains (some name) then watError origin s!"duplicate identifier {name}"
  return names ++ [name]

def index (names : Names) (kind : String) (n : Node) : MacroM Nat := do
  if n.isIdentifier then
    let s ← identifier n
    match names.findIdx? (· == some s) with
    | some i => return i
    | none => watError n s!"unknown {kind} identifier {s}"
  else
    let i ← checked n (unsigned (← atom n))
    unless i < Nat.pow 2 32 do watError n "index out of unsigned 32-bit range"
    return i

def indexTerm (i : Nat) : MacroM Term := do
  let i := natTerm i
  `(⟨$i⟩)

/-- The independent module index spaces shared by all supported profiles. -/
structure NameSpaces where
  typeNames : Names := []
  funcs : Names := []
  globals : Names := []
  memories : Names := []
  tables : Names := []
  tags : Names := []
  elems : Names := []
  data : Names := []

structure Scope where
  locals : Names := []
  labels : Names := []

abbrev Signature := Wasm.FuncType

/-- Parse parameters before results. In type declarations parameter names are
annotations; in function definitions they bind locals and must be distinct. -/
def signatureWith {m : Type → Type} [Monad m] [MonadLiftT MacroM m]
    (parseType : Node → m Wasm.ValType) (nodes : List Node) (bindNames : Bool := true) :
    m (Signature × Names × List Node) := do
  let mut rest := nodes
  let mut sig : Signature := ⟨[], []⟩
  let mut names : Names := []
  while let n :: tail := rest do
    if n.head? != some "param" then break
    let .list _ (_ :: args) := n | unreachable!
    let (name, args) ← takeName args
    if name.isSome && args.length != 1 then watError n "named parameter must have exactly one type"
    let tys ← args.mapM parseType
    for _ in tys do
      names ← if bindNames then addName n names name else pure (names ++ [name])
    sig := { sig with params := sig.params ++ tys }
    rest := tail
  while let n :: tail := rest do
    if n.head? != some "result" then break
    let .list _ (_ :: args) := n | unreachable!
    sig := { sig with results := sig.results ++ (← args.mapM parseType) }
    rest := tail
  return (sig, names, rest)

/-- A module declaration or type field, preserving its diagnostic location. -/
def field (n : Node) : MacroM (String × List Node) := match n with
  | .list _ (h :: rest) => return (← atom h, rest)
  | _ => watError n "expected a nonempty parenthesized module field"

def exportsPrefix (nodes : List Node) : MacroM (List String × List Node) := do
  let mut rest := nodes
  let mut exports := []
  while let n :: tail := rest do
    if n.head? != some "export" then break
    let .list _ [_, name] := n | watError n "inline export requires one name"
    exports := exports ++ [← nameString name]
    rest := tail
  return (exports, rest)

/-- The groups belonging to a function or block type use. -/
def isTypeUseGroup (n : Node) : Bool :=
  n.head?.any (["type", "param", "result"].contains ·)

def endLabel (name : Option String) (nodes : List Node) : MacroM (List Node) := do
  let (endName, rest) ← takeName nodes
  if endName.isSome && endName != name then
    watError nodes.head! "closing label does not match opening label"
  return rest

structure Fields where
  imports : List Term := []
  tags : List Term := []
  funcs : List Term := []
  globals : List Term := []
  memories : List Term := []
  tables : List Term := []
  exports : List Term := []
  exportNames : List String := []
  elems : List Term := []
  data : List Term := []
  start : Option Term := none
  tagCount : Nat := 0
  funcCount : Nat := 0
  globalCount : Nat := 0
  memoryCount : Nat := 0
  tableCount : Nat := 0

/-- Shared duplicate-export checking, independent of the AST constructor. -/
def addExportWith (emit : String → Nat → String → MacroM Term)
    (origin : Node) (f : Fields) (kind : String) (i : Nat) (name : String) : MacroM Fields := do
  if f.exportNames.contains name then watError origin s!"duplicate export name '{name}'"
  return { f with exports := f.exports ++ [← emit kind i name], exportNames := f.exportNames ++ [name] }


/-- Parse ordered offset/alignment attributes; return log₂ alignment, offset, and tail.
The profile fixes the unsigned width (32 for Wasm1/Lime1, 64 for Core3). -/
def memoryAttributes (width naturalAlign : Nat) (nodes : List Node) :
    MacroM (Nat × Nat × List Node) := do
  let mut rest := nodes
  let mut offset := 0
  let mut align := naturalAlign
  if let n :: tail := rest then
    if (n.atom?.getD "").startsWith "offset=" then
      offset ← checked n (unsigned ((← atom n).drop 7).toString)
      unless offset < Nat.pow 2 width do watError n s!"memory offset exceeds unsigned {width}-bit range"
      rest := tail
  if let n :: tail := rest then
    if (n.atom?.getD "").startsWith "align=" then
      let bytes ← checked n (unsigned ((← atom n).drop 6).toString)
      unless bytes > 0 && bytes < Nat.pow 2 width && Nat.pow 2 bytes.log2 == bytes do
        watError n s!"alignment must be a nonzero power of two in unsigned {width}-bit range"
      align := bytes.log2
      rest := tail
  return (align, offset, rest)


end Silmaril.Wasm.Wat
