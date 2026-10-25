module

public meta import Silmaril.Wasm.Wat.CoreTypes

/-! # Core 3 WAT modules

All Core 3 source declaration families expand to `Wasm.Module`, using the shared
name spaces and rich source-type metadata. Imports remain before definitions;
inline declarations retain their place in the independent segment index spaces.
Body parsing is supplied by the instruction frontend, keeping module and type
resolution independent of the instruction traversal implementation.

See https://webassembly.github.io/spec/core/text/modules.html.
-/

public meta section
open Lean
namespace Silmaril.Wasm.Wat.Core

abbrev InstructionParser := Scope → List Node → Build (List Term × List Node)

def space (t : Tables) : String → Names
  | "func" => t.funcs | "global" => t.globals | "memory" => t.memories
  | "table" => t.tables | "tag" => t.tags | "elem" => t.elems | "data" => t.data
  | _ => []

def declareName (origin : Node) (kind : String) (name : Option String) : Build Unit := do
  let names ← addName origin (space (← get) kind) name
  unless names.length ≤ Nat.pow 2 32 do watError origin s!"too many {kind} declarations"
  match kind with
  | "func" => modify fun t => {t with funcs := names}
  | "global" => modify fun t => {t with globals := names}
  | "memory" => modify fun t => {t with memories := names}
  | "table" => modify fun t => {t with tables := names}
  | "tag" => modify fun t => {t with tags := names}
  | "elem" => modify fun t => {t with elems := names}
  | "data" => modify fun t => {t with data := names}
  | _ => watError origin s!"unknown declaration kind '{kind}'"

/-- Inline exports precede the optional inline import in the grammar. -/
def declarationPrefix (nodes : List Node) :
    MacroM (Option String × List String × Option (String × String) × List Node) := do
  let (name, nodes) ← takeName nodes
  let (exports, nodes) ← exportsPrefix nodes
  match nodes with
  | .list _ [.atom _ "import", mod, field] :: rest =>
    return (name, exports, some (← nameString mod, ← nameString field), rest)
  | _ => return (name, exports, none, nodes)

/-- First pass records all names, including segments introduced by abbreviations.
All explicit types are parsed before bodies can intern additional signatures. -/
def collect (fields : List Node) : Build Unit := do
  collectTypes fields
  let mut definitions := false
  for n in fields do
    let (kind, args) ← field n
    if kind == "type" || kind == "rec" then continue
    if kind == "import" then
      if definitions then watError n "imports must precede definitions"
      let [mod, name, desc] := args | watError n "import requires module/name strings and a descriptor"
      discard <| nameString mod
      discard <| nameString name
      let (kind, args) ← field desc
      unless ["func", "global", "memory", "table", "tag"].contains kind do
        watError desc "unsupported import kind"
      let (name, _) ← takeName args
      declareName desc kind name
    else if ["func", "global", "memory", "table", "tag"].contains kind then
      let (name, _, imported, args) ← declarationPrefix args
      if imported.isSome then
        if definitions then watError n "imports must precede definitions"
      else definitions := true
      declareName n kind name
      if imported.isNone && (kind == "memory" || kind == "table") then
        let (_, rest) ← addressType args
        if kind == "memory" && rest.head?.any (·.head? == some "data") then
          declareName n "data" none
        if kind == "table" && (rest.drop 1).head?.any (·.head? == some "elem") then
          declareName n "elem" none
    else if kind == "elem" || kind == "data" then
      let (name, _) ← takeName args
      declareName n kind name
    else if !["export", "start"].contains kind then watError n s!"unknown module field '{kind}'"

def exportIndex (origin : Node) (kind : String) (ref : Node) : Build Nat := do
  unless ["func", "global", "memory", "table", "tag"].contains kind do
    watError origin "unknown export kind"
  index (space (← get) kind) kind ref

def exportTerm (kind : String) (i : Nat) (name : String) : MacroM Term := do
  let idx ← coreTerm "ExternIdx" kind #[← indexTerm i]
  coreTerm "Export" "mk" #[quote name, idx]

def addExport (origin : Node) (f : Fields) (kind : String) (i : Nat) (name : String) : MacroM Fields :=
  addExportWith exportTerm origin f kind i name

def bodyTerm (parseInstructions : InstructionParser) (_origin : Node) (scope : Scope)
    (nodes : List Node) : Build Term := do
  let (body, rest) ← parseInstructions scope nodes
  unless rest.isEmpty do watError rest.head! "unexpected control delimiter in expression"
  listTerm body

def offsetTerm (parseInstructions : InstructionParser) (n : Node) : Build Term := do
  match n with
  | .list _ (.atom _ "offset" :: body) => bodyTerm parseInstructions n {} body
  | .list .. => bodyTerm parseInstructions n {} [n]
  | _ => watError n "expected an offset expression"

def bytes (nodes : List Node) : MacroM ByteArray := do
  let mut result := ByteArray.empty
  for n in nodes do
    let .string _ bs := n | watError n "data payload requires byte strings"
    result := result ++ bs
  return result

def bytesTerm (bs : ByteArray) : MacroM Term := do
  let elems := bs.data.map (fun b => natTerm b.toNat)
  `(ByteArray.mk #[$elems,*])

/-- Function-index element shorthand has non-nullable `ref func` type. -/
def elementList (parseInstructions : InstructionParser) (origin : Node) (nodes : List Node)
    (legacy : Bool := false) : Build (RefType × List Term) := do
  let (functionIndices, nodes) := match nodes with
    | .atom _ "func" :: rest => (true, rest)
    | _ => (legacy && (nodes.isEmpty || nodes.head?.any (fun (n : Node) =>
        n.atom?.any (fun (s : String) => s.startsWith "$" || s.toList.head?.any Char.isDigit))), nodes)
  if functionIndices then
    let mut inits := []
    for n in nodes do
      let i ← index (← get).funcs "function" n
      inits := inits ++ [← listTerm [← coreTerm "Instr" "refFunc" #[← indexTerm i]]]
    return (⟨false, .abstract .func⟩, inits)
  let ty :: rest := nodes | watError origin "element segment requires an element type"
  let rt ← refType ty
  let mut inits := []
  for n in rest do
    let body ← match n with
      | .list _ (.atom _ "item" :: body) => pure body
      | .list .. => pure [n]
      | _ => watError n "element initializer requires (item ...) or a folded instruction"
    inits := inits ++ [← bodyTerm parseInstructions n {} body]
  return (rt, inits)

def dataSegment (parseInstructions : InstructionParser) (origin : Node) (nodes : List Node) : Build Term := do
  let mut nodes := nodes
  let mut memory := 0
  let mut explicitMemory := false
  if let n :: rest := nodes then
    if n.head? == some "memory" then
      let .list _ [_, ref] := n | watError n "memory use requires one index"
      memory ← index (← get).memories "memory" ref
      explicitMemory := true
      nodes := rest
  let mut mode ← coreTerm "DataMode" "passive"
  if explicitMemory || nodes.head?.any (fun n => n.head?.isSome) then
    let off :: rest := nodes | watError origin "active data segment requires an offset"
    mode ← coreTerm "DataMode" "active" #[← indexTerm memory, ← offsetTerm parseInstructions off]
    nodes := rest
  coreTerm "Data" "mk" #[← bytesTerm (← bytes nodes), mode]

def elemSegment (parseInstructions : InstructionParser) (origin : Node) (nodes : List Node) : Build Term := do
  let mut nodes := nodes
  let mut mode ← coreTerm "ElemMode" "passive"
  let mut legacy := false
  if nodes.head?.any (·.atom? == some "declare") then
    mode ← coreTerm "ElemMode" "declarative"
    nodes := nodes.drop 1
  else
    let mut table := 0
    let mut explicitTable := false
    if let n :: rest := nodes then
      if n.head? == some "table" then
        let .list _ [_, ref] := n | watError n "table use requires one index"
        table ← index (← get).tables "table" ref
        explicitTable := true
        nodes := rest
    if explicitTable || nodes.head?.any (fun n => n.head?.isSome && n.head? != some "ref") then
      let off :: rest := nodes | watError origin "active element segment requires an offset"
      mode ← coreTerm "ElemMode" "active" #[← indexTerm table, ← offsetTerm parseInstructions off]
      legacy := !explicitTable
      nodes := rest
  let (rt, inits) ← elementList parseInstructions origin nodes legacy
  coreTerm "Elem" "mk" #[← refTerm rt, ← listTerm inits, mode]

/-- Import descriptors resolve type uses before producing the source `ExternType`. -/
def importType (origin : Node) (kind : String) (args : List Node) : Build Term := do
  match kind with
  | "func" | "tag" =>
    let (i, _, _, rest) ← typeUse origin args
    unless rest.isEmpty do watError origin "imported function/tag cannot have locals or a body"
    coreTerm "ExternType" kind #[← indexTerm i]
  | "global" =>
    let [ty] := args | watError origin "global import requires one global type"
    coreTerm "ExternType" "global" #[← globalType ty]
  | "memory" => coreTerm "ExternType" "memory" #[← memoryType origin args]
  | "table" =>
    let (ty, _, rest) ← tableType origin args
    unless rest.isEmpty do watError origin "imported table cannot have an initializer"
    coreTerm "ExternType" "table" #[ty]
  | _ => watError origin "unknown import kind"

def count (f : Fields) : String → Nat
  | "func" => f.funcCount | "global" => f.globalCount | "memory" => f.memoryCount
  | "table" => f.tableCount | "tag" => f.tagCount | _ => 0

def increment (f : Fields) : String → Fields
  | "func" => {f with funcCount := f.funcCount + 1}
  | "global" => {f with globalCount := f.globalCount + 1}
  | "memory" => {f with memoryCount := f.memoryCount + 1}
  | "table" => {f with tableCount := f.tableCount + 1}
  | "tag" => {f with tagCount := f.tagCount + 1}
  | _ => f

def addImport (f : Fields) (origin : Node) (kind : String) (args : List Node)
    (mod name : String) : Build Fields := do
  let ty ← importType origin kind args
  let term ← coreTerm "Import" "mk" #[quote mod, quote name, ty]
  return increment {f with imports := f.imports ++ [term]} kind

/-- The offset integer matches the address type of an inline memory/table. -/
def zeroOffset (address : AddrType) : MacroM Term := do
  listTerm [← coreTerm "Instr" "intConst"
    #[← coreTerm "IntType" (if address == .i64 then "i64" else "i32"), natTerm 0]]

def fixedLimitsTerm (origin : Node) (n : Nat) : MacroM Term := do
  unless n < Nat.pow 2 64 do watError origin "inferred limit exceeds unsigned 64-bit range"
  coreTerm "Limits" "mk" #[natTerm n, ← `(some $(natTerm n))]

/-- Inline memory data expands to a fixed-size memory and an active segment. -/
def memoryDefinition (f : Fields) (origin : Node) (args : List Node) : Build Fields := do
  let (address, rest) ← addressType args
  if let [.list _ (.atom _ "data" :: strings)] := rest then
    let bs ← bytes strings
    let pages := (bs.size + 65535) / 65536
    let ty ← coreTerm "MemoryType" "mk" #[← addressTerm address, ← fixedLimitsTerm origin pages]
    let mode ← coreTerm "DataMode" "active" #[← indexTerm f.memoryCount, ← zeroOffset address]
    let seg ← coreTerm "Data" "mk" #[← bytesTerm bs, mode]
    return {f with memories := f.memories ++ [ty], data := f.data ++ [seg], memoryCount := f.memoryCount + 1}
  else
    return {f with memories := f.memories ++ [← memoryType origin args], memoryCount := f.memoryCount + 1}

/-- Inline element lists infer exact limits. An explicit element-list type belongs
to the segment; the reference interpreter's untyped index/expression abbreviations
inherit the enclosing table's reference type. -/
def tableDefinition (parseInstructions : InstructionParser) (f : Fields) (origin : Node)
    (args : List Node) : Build Fields := do
  let (address, rest) ← addressType args
  if let [ref, .list _ (.atom _ "elem" :: init)] := rest then
    let rt ← refType ref
    let explicitType := init.head?.any fun n =>
      n.atom? == some "func" || (n.atom?.bind shortRef?).isSome || n.head? == some "ref"
    let (segmentType, inits) ← if explicitType then elementList parseInstructions origin init
      else if init.head?.any (fun n => n.atom?.isSome) then do
        let (_, inits) ← elementList parseInstructions origin (.atom origin.pos "func" :: init)
        pure (rt, inits)
      else elementList parseInstructions origin (ref :: init)
    let ty ← coreTerm "TableType" "mk" #[← addressTerm address, ← fixedLimitsTerm origin inits.length, ← refTerm rt]
    let initial ← listTerm [← coreTerm "Instr" "refNull" #[← heapTerm rt.heap]]
    let table ← coreTerm "Table" "mk" #[ty, initial]
    let mode ← coreTerm "ElemMode" "active" #[← indexTerm f.tableCount, ← zeroOffset address]
    let seg ← coreTerm "Elem" "mk" #[← refTerm segmentType, ← listTerm inits, mode]
    return {f with tables := f.tables ++ [table], elems := f.elems ++ [seg], tableCount := f.tableCount + 1}
  else
    let (ty, rt, rest) ← tableType origin args
    let init ← if rest.isEmpty then listTerm [← coreTerm "Instr" "refNull" #[← heapTerm rt.heap]]
      else bodyTerm parseInstructions origin {} rest
    let table ← coreTerm "Table" "mk" #[ty, init]
    return {f with tables := f.tables ++ [table], tableCount := f.tableCount + 1}

def elaborateFields (parseInstructions : InstructionParser) (fields : List Node) : Build Fields := do
  let mut f : Fields := {}
  for n in fields do
    let (kind, args) ← field n
    if kind == "type" || kind == "rec" then continue
    if kind == "import" then
      let [mod, name, desc] := args | watError n "invalid import"
      let (kind, args) ← field desc
      let (_, args) ← takeName args
      f ← addImport f desc kind args (← nameString mod) (← nameString name)
    else if ["func", "global", "memory", "table", "tag"].contains kind then
      let (_, exports, imported, args) ← declarationPrefix args
      let i := count f kind
      for name in exports do f ← addExport n f kind i name
      if let some (mod, name) := imported then
        f ← addImport f n kind args mod name
      else if kind == "func" then
        let (ty, _, params, args) ← typeUse n args
        let (locals, types, body) ← localGroups args params
        let body ← bodyTerm parseInstructions n ⟨locals, [none]⟩ body
        let term ← coreTerm "Func" "mk" #[← indexTerm ty, ← listTerm types, body]
        f := {f with funcs := f.funcs ++ [term], funcCount := f.funcCount + 1}
      else if kind == "tag" then
        let (ty, _, _, rest) ← typeUse n args
        unless rest.isEmpty do watError n "tag declaration cannot have a body"
        f := {f with tags := f.tags ++ [← indexTerm ty], tagCount := f.tagCount + 1}
      else if kind == "global" then
        let ty :: body := args | watError n "global requires a type and initializer"
        let init ← bodyTerm parseInstructions n {} body
        let term ← coreTerm "Global" "mk" #[← globalType ty, init]
        f := {f with globals := f.globals ++ [term], globalCount := f.globalCount + 1}
      else if kind == "memory" then f ← memoryDefinition f n args
      else f ← tableDefinition parseInstructions f n args
    else if kind == "export" then
      let [name, .list _ [kind, ref]] := args | watError n "export requires a name and (kind index)"
      let kind ← atom kind
      f ← addExport n f kind (← exportIndex n kind ref) (← nameString name)
    else if kind == "start" then
      if f.start.isSome then watError n "duplicate start declaration"
      let [ref] := args | watError n "start requires one function index"
      f := {f with start := some (← indexTerm (← exportIndex n "func" ref))}
    else if kind == "elem" then
      let (_, args) ← takeName args
      f := {f with elems := f.elems ++ [← elemSegment parseInstructions n args]}
    else if kind == "data" then
      let (_, args) ← takeName args
      f := {f with data := f.data ++ [← dataSegment parseInstructions n args]}
    else watError n s!"unknown module field '{kind}'"
  return f

def moduleTerm (parseInstructions : InstructionParser) (text : String) : MacroM Term := do
  let nodes ← match parse text with
    | .ok nodes => pure nodes
    | .error msg => Macro.throwError msg
  let fields ← match nodes with
    | [.list _ (.atom _ "module" :: args)] => pure (← takeName args).2
    | _ => pure nodes
  let build : Build Fields := do collect fields; elaborateFields parseInstructions fields
  let (f, t) ← build.run {}
  let types ← listTerm (← t.groups.mapM recTerm)
  let imports ← listTerm f.imports
  let tags ← listTerm f.tags
  let funcs ← listTerm f.funcs
  let globals ← listTerm f.globals
  let tables ← listTerm f.tables
  let memories ← listTerm f.memories
  let elems ← listTerm f.elems
  let data ← listTerm f.data
  let start ← match f.start with | none => `(none) | some s => `(some $s)
  let exports ← listTerm f.exports
  `(show Silmaril.Wasm.Module from {
    types := $types
    imports := $imports
    tags := $tags
    funcs := $funcs
    globals := $globals
    tables := $tables
    memories := $memories
    elems := $elems
    data := $data
    start := $start
    exports := $exports })

end Silmaril.Wasm.Wat.Core
