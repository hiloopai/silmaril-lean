module

public meta import Silmaril.Wasm.Wat.CoreTypes
public meta import Silmaril.Wasm.Wat.CoreMemory
public meta import Silmaril.Wasm.Wat.InstructionParser
public meta import Silmaril.Wasm.Wat.Float

/-! # Core3 instruction text

This frontend emits the existing Core3 AST, including GC, exception handling,
tail calls, multiple memories and tables, memory64 immediates, and SIMD. It shares
the flat/folded traversal with the older profiles. Parsing is separate from type
validation, so numeric indices may refer to declarations not yet validated.
-/

public meta section
open Lean
namespace Silmaril.Wasm.Wat.Core

def scalarSyntax : ScalarSyntax := ⟨"Silmaril.Wasm", true, "Silmaril.Wasm"⟩

def plain (scope : Scope) (origin : Node) (nodes : List Node) : Build (Term × List Node) := do
  let op ← atom origin
  let t ← get
  for (wat, lean) in [("nop", "nop"), ("unreachable", "unreachable"), ("drop", "drop"),
      ("return", "return_"), ("throw_ref", "throwRef"), ("ref.is_null", "refIsNull"),
      ("ref.as_non_null", "refAsNonNull"), ("ref.eq", "refEq"), ("ref.i31", "refI31"),
      ("array.len", "arrayLen"), ("any.convert_extern", "anyConvertExtern"),
      ("extern.convert_any", "externConvertAny")] do
    if op == wat then return (← instr lean, nodes)
  if op == "select" then
    let mut rest := nodes
    let mut types := []
    let mut typed := false
    while let n :: tail := rest do
      let .list _ (.atom _ "result" :: ns) := n | break
      typed := true
      for n in ns do types := types ++ [← valTerm (← valType n)]
      rest := tail
    let ts ← if typed then do let ts ← listTerm types; `(some $ts) else `(none)
    return (← instr "select" #[ts], rest)
  for (wat, lean, names, kind) in [
      ("local.get", "localGet", scope.locals, "local"),
      ("local.set", "localSet", scope.locals, "local"),
      ("local.tee", "localTee", scope.locals, "local"),
      ("global.get", "globalGet", t.globals, "global"),
      ("global.set", "globalSet", t.globals, "global"),
      ("call", "call", t.funcs, "function"), ("return_call", "returnCall", t.funcs, "function"),
      ("call_ref", "callRef", t.typeNames, "type"),
      ("return_call_ref", "returnCallRef", t.typeNames, "type"),
      ("ref.func", "refFunc", t.funcs, "function"),
      ("throw", "throw", t.tags, "tag"), ("data.drop", "dataDrop", t.data, "data"),
      ("elem.drop", "elemDrop", t.elems, "element"),
      ("br", "br", scope.labels, "label"), ("br_if", "brIf", scope.labels, "label"),
      ("br_on_null", "brOnNull", scope.labels, "label"),
      ("br_on_non_null", "brOnNonNull", scope.labels, "label")] do
    if op == wat then
      let (i, rest) ← requiredIndex origin names kind nodes
      return (← instr lean #[i], rest)
  if op == "br_table" then
    let mut rest := nodes
    let mut labels := []
    while let n :: tail := rest do
      unless isIndex n do break
      labels := labels ++ [← indexTerm (← index scope.labels "label" n)]
      rest := tail
    let some fallback := labels.getLast? | watError origin "br_table requires a default label"
    return (← instr "brTable" #[← listTerm labels.dropLast, fallback], rest)
  if op == "br_on_cast" || op == "br_on_cast_fail" then
    let (label, rest) ← requiredIndex origin scope.labels "label" nodes
    let source :: target :: rest := rest | watError origin "cast branch requires source and target reference types"
    return (← instr (if op == "br_on_cast" then "brOnCast" else "brOnCastFail")
      #[label, ← refTerm (← refType source), ← refTerm (← refType target)], rest)
  if op == "call_indirect" || op == "return_call_indirect" then
    let (table, rest) ← optionalIndex t.tables "table" nodes
    let (i, _, names, rest) ← typeUse origin rest
    if names.any Option.isSome then watError origin "indirect call parameters must be anonymous"
    return (← instr (if op == "call_indirect" then "callIndirect" else "returnCallIndirect")
      #[table, ← indexTerm i], rest)
  for (wat, lean, names, kind) in [
      ("table.get", "tableGet", t.tables, "table"), ("table.set", "tableSet", t.tables, "table"),
      ("table.size", "tableSize", t.tables, "table"), ("table.grow", "tableGrow", t.tables, "table"),
      ("table.fill", "tableFill", t.tables, "table"),
      ("memory.size", "memorySize", t.memories, "memory"),
      ("memory.grow", "memoryGrow", t.memories, "memory"),
      ("memory.fill", "memoryFill", t.memories, "memory")] do
    if op == wat then
      let (i, rest) ← optionalIndex names kind nodes
      return (← instr lean #[i], rest)
  for (wat, lean, names, kind) in [("table.copy", "tableCopy", t.tables, "table"),
      ("memory.copy", "memoryCopy", t.memories, "memory")] do
    if op == wat then
      let (a, b, rest) ← pairIndices origin names kind nodes
      return (← instr lean #[a, b], rest)
  for (wat, lean, targets, segments, targetKind, segmentKind) in [
      ("table.init", "tableInit", t.tables, t.elems, "table", "element"),
      ("memory.init", "memoryInit", t.memories, t.data, "memory", "data")] do
    if op == wat then
      let (a, b, rest) ← segmentIndices origin targets segments targetKind segmentKind nodes
      return (← instr lean #[a, b], rest)
  if op == "ref.null" then
    let n :: rest := nodes | watError origin "missing heap type"
    return (← instr "refNull" #[← heapTerm (← heapType n)], rest)
  if op == "ref.test" || op == "ref.cast" then
    let n :: rest := nodes | watError origin "missing reference type"
    return (← instr (if op == "ref.test" then "refTest" else "refCast") #[← refTerm (← refType n)], rest)
  if op == "i31.get_s" || op == "i31.get_u" then
    return (← instr "i31Get" #[← signTerm (op == "i31.get_s")], nodes)
  for (wat, lean) in [("struct.new", "structNew"), ("struct.new_default", "structNewDefault"),
      ("array.new", "arrayNew"), ("array.new_default", "arrayNewDefault"),
      ("array.set", "arraySet"), ("array.fill", "arrayFill")] do
    if op == wat then
      let (i, rest) ← requiredIndex origin t.typeNames "type" nodes
      return (← instr lean #[i], rest)
  if ["struct.get", "struct.get_s", "struct.get_u", "struct.set"].contains op then
    let type :: field :: rest := nodes | watError origin "struct access requires type and field indices"
    let i ← index t.typeNames "type" type
    let fieldNames := t.fieldNames[i]?.getD []
    let ti ← indexTerm i
    let fi ← indexTerm (← index fieldNames "field" field)
    if op == "struct.set" then return (← instr "structSet" #[ti, fi], rest)
    let sign ← if op == "struct.get" then `(none)
      else do let s ← signTerm (op == "struct.get_s"); `(some $s)
    return (← instr "structGet" #[sign, ti, fi], rest)
  if ["array.get", "array.get_s", "array.get_u"].contains op then
    let (i, rest) ← requiredIndex origin t.typeNames "type" nodes
    let sign ← if op == "array.get" then `(none)
      else do let s ← signTerm (op == "array.get_s"); `(some $s)
    return (← instr "arrayGet" #[sign, i], rest)
  if op == "array.new_fixed" then
    let (i, rest) ← requiredIndex origin t.typeNames "type" nodes
    let n :: rest := rest | watError origin "missing fixed array length"
    let count ← checked n (unsigned (← atom n))
    unless count < Nat.pow 2 32 do watError n "array length exceeds unsigned 32-bit range"
    return (← instr "arrayNewFixed" #[i, natTerm count], rest)
  for (wat, lean, names, kind) in [
      ("array.new_data", "arrayNewData", t.data, "data"),
      ("array.new_elem", "arrayNewElem", t.elems, "element"),
      ("array.init_data", "arrayInitData", t.data, "data"),
      ("array.init_elem", "arrayInitElem", t.elems, "element"),
      ("array.copy", "arrayCopy", t.typeNames, "type")] do
    if op == wat then
      let (i, rest) ← requiredIndex origin t.typeNames "type" nodes
      let (j, rest) ← requiredIndex origin names kind rest
      return (← instr lean #[i, j], rest)
  if let some result ← vectorPlain floatBits origin nodes then return result
  match op.splitOn "." with
  | [ty, name] =>
    if name == "const" && ["i32", "i64", "f32", "f64"].contains ty then
      let n :: rest := nodes | watError origin "missing numeric literal"
      let width := if ty == "i32" || ty == "f32" then 32 else 64
      let integer := ty == "i32" || ty == "i64"
      let bits ← checked n ((if integer then integerBits else floatBits) width (← atom n))
      let b ← `(BitVec.ofNat $(natTerm width) $(natTerm bits))
      return (← instr (if integer then "intConst" else "floatConst")
        #[← if integer then integerType ty else floatType ty, b], rest)
    if let some result ← coreMemoryOp t.memories origin ty name nodes then return result
    if let some result ← scalarOpWith scalarSyntax ty name then return (result, nodes)
  | _ => pure ()
  watError origin s!"unsupported Core3 instruction '{op}'"

def catchTerm (scope : Scope) (origin : Node) : Build Term := do
  let .list _ (head :: args) := origin | watError origin "expected catch clause"
  let op ← atom head
  let t ← get
  let (tag, rest) ← if op == "catch" || op == "catch_ref" then do
    let (tag, rest) ← requiredIndex origin t.tags "tag" args
    pure (#[tag], rest)
  else pure (#[], args)
  let (label, rest) ← requiredIndex origin scope.labels "label" rest
  unless rest.isEmpty do watError origin "unexpected catch clause operands"
  let ctor := match op with
    | "catch" => "catch_" | "catch_ref" => "catchRef"
    | "catch_all" => "catchAll" | _ => "catchAllRef"
  coreTerm "Catch" ctor (tag.push label)

def control (scope : Scope) (origin : Node) (op : String) (nodes : List Node) :
    Build (ControlHeader × List Node) := do
  let (bt, rest) ← blockType origin nodes
  if op == "try_table" then
    let (clauses, rest) := rest.span (fun n => n.head?.any
      (["catch", "catch_ref", "catch_all", "catch_all_ref"].contains ·))
    let catches ← clauses.mapM (catchTerm { scope with labels := scope.labels.drop 1 })
    return (⟨fun body _ => do instr "tryTable" #[bt, ← listTerm catches, ← listTerm body]⟩, rest)
  return (⟨fun left right => do
    if op == "if" then instr "if_" #[bt, ← listTerm left, ← listTerm right]
    else instr op #[bt, ← listTerm left]⟩, rest)

def instructionSyntax : InstructionSyntax Tables where
  plain := plain
  isControl := (["block", "loop", "if", "try_table"].contains ·)
  control := control
  deferredFolded := (["call_indirect", "return_call_indirect"].contains ·)
  splitFolded := fun _ nodes => do
    let (table, rest) := match nodes with
      | n :: rest => if isIndex n then ([n], rest) else ([], nodes)
      | [] => ([], [])
    let (types, operands) := rest.span isTypeUseGroup
    return (table ++ types, operands)

def instructions (scope : Scope) (nodes : List Node) (stops : List String := []) :
    Build (List Term × List Node) := parseInstructions instructionSyntax scope nodes stops

def expressionTerm (text : String) : MacroM Term := do
  let nodes ← match parse text with
    | .ok ns => pure ns | .error e => Macro.throwError e
  let ((body, rest), tables) ← (instructions {} nodes).run {}
  unless rest.isEmpty do watError rest.head! "unexpected instruction delimiter"
  unless tables.groups.isEmpty do
    Macro.throwError "WAT expression requires implicit function types; use wat3! with a module context"
  let body ← listTerm body
  `(($body : Silmaril.Wasm.Expr))

end Silmaril.Wasm.Wat.Core
