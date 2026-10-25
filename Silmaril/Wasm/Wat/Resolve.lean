module

public import Silmaril.Wasm.V1.Modules
public import Silmaril.Wasm.Lime1.Modules
public meta import Silmaril.Wasm.Wat.Common
public meta import Silmaril.Wasm.TypeUse

/-! # WAT name and type-use resolution

The quotation expands to ordinary constructors. Numeric indices are bounded but
stack typing, store validity, and instruction validation remain separate.
-/

public meta section

open Lean
namespace Silmaril.Wasm.Wat

inductive Profile where
  | v1 | lime
  deriving BEq

def Profile.ns : Profile → String
  | .v1 => "Silmaril.Wasm.V1"
  | .lime => "Silmaril.Wasm.Lime1"

def consTerm (p : Profile) (family name : String) (args : Array Term := #[]) : MacroM Term :=
  applyTerm (p.ns ++ "." ++ family ++ "." ++ name) args

def valType (n : Node) : MacroM String := do
  let s ← atom n
  unless ["i32", "i64", "f32", "f64"].contains s do
    watError n "expected scalar value type i32, i64, f32, or f64"
  return s

def valTerm (s : String) : MacroM Term :=
  applyTerm ("Silmaril.Wasm.V1.ValType." ++ s)

def scalarValType (n : Node) : MacroM Wasm.ValType := do
  return match ← valType n with
  | "i32" => .i32 | "i64" => .i64 | "f32" => .f32 | _ => .f64

def scalarValTerm : Wasm.ValType → MacroM Term
  | .num (.int .i32) => valTerm "i32"
  | .num (.int .i64) => valTerm "i64"
  | .num (.float .f32) => valTerm "f32"
  | .num (.float .f64) => valTerm "f64"
  | _ => Macro.throwError "non-scalar type in scalar WAT profile"

def Signature.term (s : Signature) : MacroM Term := do
  let ps ← listTerm (← s.params.mapM scalarValTerm)
  let rs ← listTerm (← s.results.mapM scalarValTerm)
  `(Silmaril.Wasm.V1.FuncType.mk $ps $rs)

structure Tables extends NameSpaces where
  profile : Profile
  types : List Signature := []

abbrev Build := StateT Tables MacroM

def signature (nodes : List Node) (bindNames : Bool := true) :
    MacroM (Signature × Names × List Node) :=
  signatureWith scalarValType nodes bindNames

def checkSignature (n : Node) (s : Signature) : Build Unit := do
  if (← get).profile == .v1 && s.results.length > 1 then
    watError n "Wasm1 function types have at most one result"

/-- Explicit types are collected first; implicit signatures intern the first match. -/
def typeUse (origin : Node) (nodes : List Node) : Build (Nat × Signature × Names × List Node) := do
  let mut rest := nodes
  let mut reference : Option Node := none
  if let n :: tail := rest then
    if n.head? == some "type" then
      let .list _ [_, ref] := n | watError n "type use requires one index"
      reference := some ref
      rest := tail
  let annotated := rest.head?.any (fun n => n.head? == some "param" || n.head? == some "result")
  let (sig, names, remaining) ← signature rest
  let t ← get
  if let some ref := reference then
    let i ← index t.typeNames "type" ref
    let some idx := Idx.ofNat? (kind := .type_) i | watError ref "type index out of range"
    let resolved := TypeUse.resolve (.index idx (if annotated then some sig else none)) t.types
    let .ok _ := resolved | match resolved with
      | .error (.unknownType _) => watError ref "type index does not name a declared type"
      | _ => watError origin "inline signature does not match referenced type"
    let some actual := t.types[i]? | watError ref "type index does not name a declared type"
    checkSignature origin actual
    return (i, actual, if annotated then names else actual.params.map (fun _ => none), remaining)
  else
    checkSignature origin sig
    let .ok (idx, types) := TypeUse.resolve (.inline sig) t.types |
      watError origin "too many function types"
    modify fun t => { t with types := types }
    return (idx.toNat, sig, names, remaining)

def blockType (origin : Node) (nodes : List Node) : Build (Term × List Node) := do
  let p := (← get).profile
  if p == .v1 then
    if nodes.head?.any (fun n => n.head? == some "type" || n.head? == some "param") then
      watError origin "Wasm1 block signatures cannot have type indices or parameters"
    let (sig, _, rest) ← signature nodes
    if sig.results.length > 1 then watError origin "Wasm1 block signatures have at most one result"
    let result ← match sig.results with
      | [] => `(none)
      | [s] => do let ty ← scalarValTerm s; `(some $ty)
      | _ => watError origin "invalid block signature"
    return (result, rest)
  else
    if nodes.head?.any (fun n => n.head? == some "type") then
      let (i, _, names, rest) ← typeUse origin nodes
      if names.any Option.isSome then
        watError origin "block signature parameters must be anonymous"
      return (← consTerm p "BlockType" "typeIdx" #[← indexTerm i], rest)
    let (sig, names, rest) ← signature nodes
    if names.any Option.isSome then
      watError origin "block signature parameters must be anonymous"
    -- Empty parameter groups are syntactic abbreviations. Only a genuinely
    -- nonempty input or multiple results require an implicit type definition.
    match sig.params, sig.results with
    | [], [] => return (← consTerm p "BlockType" "empty", rest)
    | [], [s] => return (← consTerm p "BlockType" "value" #[← scalarValTerm s], rest)
    | _, _ =>
      let (i, _, _, _) ← typeUse origin nodes
      return (← consTerm p "BlockType" "typeIdx" #[← indexTerm i], rest)

end Silmaril.Wasm.Wat
