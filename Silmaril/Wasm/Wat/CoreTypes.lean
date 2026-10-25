module

public import Silmaril.Wasm.Modules
public meta import Silmaril.Wasm.Types
public meta import Silmaril.Wasm.Wat.Common

/-! # Core 3 WAT types

Metadata uses the existing source types rather than strings or generated syntax.
Recursive groups and flattened indices are both retained: an implicit function
type can reuse only a singleton final group, while an explicit use may reference
any function composite. Parsing does not prove structural or instruction validity.

See https://webassembly.github.io/spec/core/text/types.html.
-/

public meta section
open Lean
namespace Silmaril.Wasm.Wat.Core

structure Tables extends NameSpaces where
  types : List SubType := []
  groups : List RecType := []
  fieldNames : List Names := []

abbrev Build := StateT Tables MacroM

def boundedIndex {kind : IndexKind} (n : Node) (i : Nat) : MacroM (Idx kind) :=
  match Idx.ofNat? i with
  | some x => pure x
  | none => watError n "index out of unsigned 32-bit range"

def absHeap? : String → Option AbsHeapType
  | "any" => some .any | "eq" => some .eq | "i31" => some .i31
  | "struct" => some .struct | "array" => some .array | "none" => some .none
  | "func" => some .func | "nofunc" => some .nofunc
  | "exn" => some .exn | "noexn" => some .noexn
  | "extern" => some .extern | "noextern" => some .noextern
  | _ => none

def heapType (n : Node) : Build HeapType := do
  if let some h := n.atom?.bind absHeap? then return .abstract h
  return .typeIdx (← boundedIndex n (← index (← get).typeNames "type" n))

def shortRef? : String → Option AbsHeapType
  | "anyref" => some .any | "eqref" => some .eq | "i31ref" => some .i31
  | "structref" => some .struct | "arrayref" => some .array | "nullref" => some .none
  | "funcref" => some .func | "nullfuncref" => some .nofunc
  | "exnref" => some .exn | "nullexnref" => some .noexn
  | "externref" => some .extern | "nullexternref" => some .noextern
  | _ => none

def refType (n : Node) : Build RefType := do
  match n with
  | .atom _ s =>
    let some h := shortRef? s | watError n "expected a reference type"
    return ⟨true, .abstract h⟩
  | .list _ [.atom _ "ref", h] => return ⟨false, ← heapType h⟩
  | .list _ [.atom _ "ref", .atom _ "null", h] => return ⟨true, ← heapType h⟩
  | _ => watError n "expected (ref [null] heaptype)"

def valType (n : Node) : Build ValType := do
  match n.atom? with
  | some "i32" => return .i32 | some "i64" => return .i64
  | some "f32" => return .f32 | some "f64" => return .f64
  | some "v128" => return .v128
  | _ => return .ref (← refType n)

def absHeapName : AbsHeapType → String
  | .any => "any" | .eq => "eq" | .i31 => "i31"
  | .struct => "struct" | .array => "array" | .none => "none"
  | .func => "func" | .nofunc => "nofunc" | .exn => "exn" | .noexn => "noexn"
  | .extern => "extern" | .noextern => "noextern"

def heapTerm : HeapType → MacroM Term
  | .abstract h => do coreTerm "HeapType" "abstract" #[← coreTerm "AbsHeapType" (absHeapName h)]
  | .typeIdx i => do coreTerm "HeapType" "typeIdx" #[← indexTerm i.toNat]

def refTerm (t : RefType) : MacroM Term := do
  coreTerm "RefType" "mk" #[quote t.nullable, ← heapTerm t.heap]

def valTerm : ValType → MacroM Term
  | .num (.int .i32) => applyTerm "Silmaril.Wasm.ValType.i32"
  | .num (.int .i64) => applyTerm "Silmaril.Wasm.ValType.i64"
  | .num (.float .f32) => applyTerm "Silmaril.Wasm.ValType.f32"
  | .num (.float .f64) => applyTerm "Silmaril.Wasm.ValType.f64"
  | .vec .v128 => applyTerm "Silmaril.Wasm.ValType.v128"
  | .ref t => do coreTerm "ValType" "ref" #[← refTerm t]

def signatureTerm (s : FuncType) : MacroM Term := do
  coreTerm "FuncType" "mk" #[← listTerm (← s.params.mapM valTerm), ← listTerm (← s.results.mapM valTerm)]

def storageType (n : Node) : Build StorageType := do
  match n.atom? with
  | some "i8" => return .packed .i8
  | some "i16" => return .packed .i16
  | _ => return .val (← valType n)

def fieldType (n : Node) : Build FieldType := do
  match n with
  | .list _ [.atom _ "mut", t] => return ⟨.var, ← storageType t⟩
  | _ => return ⟨.const, ← storageType n⟩

def storageTerm : StorageType → MacroM Term
  | .val t => do coreTerm "StorageType" "val" #[← valTerm t]
  | .packed t => do coreTerm "StorageType" "packed" #[← coreTerm "PackType" (match t with | .i8 => "i8" | .i16 => "i16")]

def fieldTerm (t : FieldType) : MacroM Term := do
  coreTerm "FieldType" "mk" #[← coreTerm "Mutability" (if t.mutability == .var then "var" else "const"),
    ← storageTerm t.storage]

def compositeTerm : CompositeType → MacroM Term
  | .func t => do coreTerm "CompositeType" "func" #[← signatureTerm t]
  | .struct fs => do coreTerm "CompositeType" "struct" #[← listTerm (← fs.mapM fieldTerm)]
  | .array f => do coreTerm "CompositeType" "array" #[← fieldTerm f]

def subtypeTerm (t : SubType) : MacroM Term := do
  coreTerm "SubType" "mk" #[quote t.final_, ← listTerm (← t.supertypes.mapM (indexTerm ∘ Idx.toNat)),
    ← compositeTerm t.body]

def recTerm (t : RecType) : MacroM Term := do
  coreTerm "RecType" "mk" #[← listTerm (← t.types.mapM subtypeTerm)]


/-- Field identifiers belong to their containing struct, not a module-wide space. -/
def compositeType (n : Node) : Build (CompositeType × Names) := do
  match n with
  | .list _ (.atom _ "func" :: args) =>
    let (sig, _, rest) ← signatureWith valType args false
    unless rest.isEmpty do watError n "unexpected function-type field"
    return (.func sig, [])
  | .list _ (.atom _ "struct" :: fields) =>
    let mut fs := []
    let mut names : Names := []
    for f in fields do
      let .list _ (.atom _ "field" :: args) := f | watError f "expected (field ...)"
      let (name, args) ← takeName args
      if name.isSome && args.length != 1 then watError f "named field must have exactly one type"
      for a in args do
        names ← addName f names name
        fs := fs ++ [← fieldType a]
    return (.struct fs, names)
  | .list _ [.atom _ "array", ft] => return (.array (← fieldType ft), [])
  | _ => watError n "expected func, struct, or array composite type"

def subtype (n : Node) : Build (SubType × Names) := do
  match n with
  | .list _ (.atom _ "sub" :: args) =>
    let (final_, args) := match args with
      | .atom _ "final" :: rest => (true, rest)
      | _ => (false, args)
    let mut parents := []
    let mut rest := args
    while let a :: tail := rest do
      if a.atom?.isNone then break
      parents := parents ++ [← boundedIndex a (← index (← get).typeNames "type" a)]
      rest := tail
    let [body] := rest | watError n "subtype requires one composite type after its supertypes"
    let (body, names) ← compositeType body
    return (⟨final_, parents, body⟩, names)
  | _ =>
    let (body, names) ← compositeType n
    return (⟨true, [], body⟩, names)

def typeDeclaration (n : Node) : MacroM (Option String × Node) := do
  let .list _ (.atom _ "type" :: args) := n | watError n "recursive group requires type declarations"
  let (name, args) ← takeName args
  let [body] := args | watError n "type declaration requires one subtype"
  return (name, body)

/-- Collect all explicit names before parsing any bodies, including mutually
recursive references. Preserve group boundaries for later implicit interning. -/
def collectTypes (fields : List Node) : Build Unit := do
  let mut groups : List (List Node) := []
  for n in fields do
    match n with
    | .list _ (.atom _ "rec" :: types) => groups := groups ++ [types]
    | .list _ (.atom _ "type" :: _) => groups := groups ++ [[n]]
    | _ => pure ()
  for group in groups do
    for n in group do
      let (name, _) ← typeDeclaration n
      let names ← addName n (← get).typeNames name
      unless names.length ≤ Nat.pow 2 32 do watError n "too many type declarations"
      modify fun t => {t with typeNames := names}
  for group in groups do
    let mut types := []
    for n in group do
      let (_, body) ← typeDeclaration n
      let (st, names) ← subtype body
      types := types ++ [st]
      modify fun t => {t with fieldNames := t.fieldNames ++ [names]}
    modify fun t => {t with groups := t.groups ++ [⟨types⟩], types := t.types ++ types}

/-- Find the first eligible singleton group, not an equal body inside a larger
recursive group or an extensible subtype. -/
def implicitType? (groups : List RecType) (sig : FuncType) : Option Nat := Id.run do
  let mut offset := 0
  for group in groups do
    if group.types == [⟨true, [], .func sig⟩] then return some offset
    offset := offset + group.types.length
  return none

def internFunction (origin : Node) (sig : FuncType) : Build Nat := do
  let t ← get
  if let some i := implicitType? t.groups sig then return i
  let i := t.types.length
  discard <| boundedIndex (kind := .type_) origin i
  let st : SubType := ⟨true, [], .func sig⟩
  modify fun t => { t with
    types := t.types ++ [st]
    groups := t.groups ++ [⟨[st]⟩]
    typeNames := t.typeNames ++ [none]
    fieldNames := t.fieldNames ++ [[]] }
  return i

def typeUse (origin : Node) (nodes : List Node) : Build (Nat × FuncType × Names × List Node) := do
  let mut rest := nodes
  let mut reference : Option Node := none
  if let n :: tail := rest then
    if n.head? == some "type" then
      let .list _ [_, ref] := n | watError n "type use requires one index"
      reference := some ref
      rest := tail
  let annotated := rest.head?.any (fun n => n.head? == some "param" || n.head? == some "result")
  let (sig, names, remaining) ← signatureWith valType rest
  if let some ref := reference then
    let t ← get
    let i ← index t.typeNames "type" ref
    let some st := t.types[i]? | watError ref "type index does not name a declared type"
    let .func actual := st.body | watError ref "type use does not name a function type"
    if annotated && sig != actual then watError origin "inline signature does not match referenced type"
    return (i, actual, if annotated then names else actual.params.map (fun _ => none), remaining)
  else
    return (← internFunction origin sig, sig, names, remaining)

def blockType (origin : Node) (nodes : List Node) : Build (Term × List Node) := do
  if nodes.head?.any (fun n => n.head? == some "type") then
    let (i, _, names, rest) ← typeUse origin nodes
    if names.any Option.isSome then watError origin "block signature parameters must be anonymous"
    return (← coreTerm "BlockType" "typeIdx" #[← indexTerm i], rest)
  let (sig, names, rest) ← signatureWith valType nodes
  if names.any Option.isSome then watError origin "block signature parameters must be anonymous"
  match sig.params, sig.results with
  | [], [] => return (← coreTerm "BlockType" "empty", rest)
  | [], [t] => return (← coreTerm "BlockType" "value" #[← valTerm t], rest)
  | _, _ => return (← coreTerm "BlockType" "typeIdx" #[← indexTerm (← internFunction origin sig)], rest)

def localGroups (nodes : List Node) (params : Names) : Build (Names × List Term × List Node) := do
  let mut names := params
  let mut types := []
  let mut rest := nodes
  while let n :: tail := rest do
    if n.head? != some "local" then break
    let .list _ (_ :: args) := n | watError n "invalid local group"
    let (name, args) ← takeName args
    if name.isSome && args.length != 1 then watError n "named local must have exactly one type"
    for arg in args do
      names ← addName n names name
      types := types ++ [← valTerm (← valType arg)]
    rest := tail
  return (names, types, rest)

def addressType (nodes : List Node) : MacroM (AddrType × List Node) := do
  match nodes with
  | .atom _ "i32" :: rest => return (.i32, rest)
  | .atom _ "i64" :: rest => return (.i64, rest)
  | _ => return (.i32, nodes)

def limits (origin : Node) (nodes : List Node) : MacroM (Limits × List Node) := do
  let first :: rest := nodes | watError origin "limits require a minimum"
  let lo ← checked first (unsigned (← atom first))
  if h : lo < Nat.pow 2 64 then
    let mut hi : Option (Fin (Nat.pow 2 64)) := none
    let mut rest := rest
    if let next :: tail := rest then
      if next.atom?.any (fun s => s.toList.head?.any Char.isDigit) then
        let n ← checked next (unsigned (← atom next))
        if hn : n < Nat.pow 2 64 then hi := some ⟨n, hn⟩
        else watError next "limit exceeds unsigned 64-bit range"
        rest := tail
    return (⟨⟨lo, h⟩, hi⟩, rest)
  else watError first "limit exceeds unsigned 64-bit range"

def limitsTerm (l : Limits) : MacroM Term := do
  let upper ← match l.max with
    | none => `(none)
    | some n => `(some $(natTerm n.val))
  coreTerm "Limits" "mk" #[natTerm l.min.val, upper]

def addressTerm (a : AddrType) : MacroM Term := coreTerm "AddrType" (if a == .i64 then "i64" else "i32")

def memoryType (origin : Node) (nodes : List Node) : Build Term := do
  let (address, nodes) ← addressType nodes
  let (lim, rest) ← limits origin nodes
  unless rest.isEmpty do watError origin "unexpected memory declaration field"
  coreTerm "MemoryType" "mk" #[← addressTerm address, ← limitsTerm lim]

def tableType (origin : Node) (nodes : List Node) : Build (Term × RefType × List Node) := do
  let (address, nodes) ← addressType nodes
  let (lim, rest) ← limits origin nodes
  let ref :: rest := rest | watError origin "table requires a reference element type"
  let rt ← refType ref
  return (← coreTerm "TableType" "mk" #[← addressTerm address, ← limitsTerm lim, ← refTerm rt], rt, rest)

def globalType (n : Node) : Build Term := do
  let (mutability, ty) ← match n with
    | .list _ [.atom _ "mut", ty] => pure (Mutability.var, ← valType ty)
    | _ => pure (Mutability.const, ← valType n)
  coreTerm "GlobalType" "mk" #[← coreTerm "Mutability" (if mutability == .var then "var" else "const"),
    ← valTerm ty]

end Silmaril.Wasm.Wat.Core
