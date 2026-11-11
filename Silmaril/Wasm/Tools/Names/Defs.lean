module

public import Silmaril.Wasm.Binaryen.Exe.EncodeBase
public import Silmaril.Wasm.Text.Values

/-!
# The `name` custom section that `wasm-tools parse` writes

`wasm-tools parse` (the `wast` crate, `core/binary.rs`, `names`) appends a `name` custom
section recording the identifiers of the text: the module name, functions, locals
(parameters and declared locals), labels (every `block`/`loop`/`if`/`try_table`/`try`, in the
order of the flat instruction sequence), types, tables, memories, globals, element and data
segments, struct fields, tags, function-type parameters and tag parameters, as subsections
0–13 of the extended name section, in that order, each map in index order.

`ofTree` reads these names from the S-expression tree of the text (the tree that silmaril's
certified lexer produced) and `section` encodes them. The section is custom, so it does not
change the module a binary encodes (`Silmaril.Wasm.Tools.Names.Thms.encodes_append_custom`).
The `(@name "…")` annotation form is not read (silmaril's lexer treats annotations as
whitespace).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Names

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Formats.SExpEncoding (toList?)

abbrev NameMap := List (Nat × String)
abbrev IndirectMap := List (Nat × NameMap)

structure NameTable where
  module : Option String := none
  funcs : NameMap := []
  locals : IndirectMap := []
  labels : IndirectMap := []
  types : NameMap := []
  tables : NameMap := []
  memories : NameMap := []
  globals : NameMap := []
  elems : NameMap := []
  data : NameMap := []
  fields : IndirectMap := []
  tags : NameMap := []
  parameters : IndirectMap := []
  tagParameters : IndirectMap := []
  deriving Inhabited, Repr

/-! ## Reading the tree -/

def idOf : SExp → Option String
  | .atom (.id n) => some n
  | _ => none

def headKw (x : SExp) : Option String :=
  match toList? x with
  | some (.atom (.sym k) :: _) => some k
  | _ => none

def children (x : SExp) : List SExp := (toList? x).getD []

/-- The optional identifier right after the keyword of a list node. -/
def nodeId (x : SExp) : Option String :=
  match children x with
  | _ :: y :: _ => idOf y
  | _ => none

/-- Names of `(param $x t)` / `(param t*)` (or `local`, `field`) clauses, numbered from
`start`; returns the names and the next index. -/
def namedDecls (kw : String) (start : Nat) (xs : List SExp) : NameMap × Nat :=
  xs.foldl (fun (acc, i) x =>
    if headKw x == some kw then
      match children x with
      | _ :: y :: _ =>
        match idOf y with
        | some n => (acc ++ [(i, n)], i + 1)
        | none => (acc, i + ((children x).length - 1))
      | _ => (acc, i)
    else (acc, i)) ([], start)

/-- Function-type parameter clauses of a node's direct children. -/
def paramNames (xs : List SExp) : NameMap := (namedDecls "param" 0 xs).1

def blockKws : List String := ["block", "loop", "if", "try_table", "try"]

/-- Labels of an instruction sequence, in flat order, numbering block instructions from `i`;
appends to `acc`. Every call consumes one unit of `fuel` (callers pass the text length). -/
def labelsSeq : Nat → List SExp → NameMap → Nat → NameMap × Nat
  | 0, _, acc, i => (acc, i)
  | _ + 1, [], acc, i => (acc, i)
  | fuel + 1, x :: rest, acc, i =>
    match x with
    | .atom (.sym k) =>
      if blockKws.contains k then
        match rest with
        | y :: rest' =>
          match idOf y with
          | some n => labelsSeq fuel rest' (acc ++ [(i, n)]) (i + 1)
          | none => labelsSeq fuel rest acc (i + 1)
        | [] => labelsSeq fuel rest acc (i + 1)
      else labelsSeq fuel rest acc i
    | .atom _ => labelsSeq fuel rest acc i
    | _ =>
      -- a folded instruction
      let cs := children x
      match headKw x with
      | some k =>
        if k == "if" then
          let lbl := (cs.drop 1).head?.bind idOf
          let body := cs.drop (if lbl.isSome then 2 else 1)
          let isArm (y : SExp) := headKw y == some "then" || headKw y == some "else"
          let isHdr (y : SExp) := headKw y == some "result" || headKw y == some "param" ||
            headKw y == some "type"
          let conds := body.filter (fun y => !isArm y && !isHdr y)
          let (acc, i1) := labelsSeq fuel conds acc i
          let acc := match lbl with | some n => acc ++ [(i1, n)] | none => acc
          let arms := (body.filter isArm).flatMap (fun y => (children y).drop 1)
          let (acc, i2) := labelsSeq fuel arms acc (i1 + 1)
          labelsSeq fuel rest acc i2
        else if blockKws.contains k then
          let lbl := (cs.drop 1).head?.bind idOf
          let acc := match lbl with | some n => acc ++ [(i, n)] | none => acc
          let body := cs.drop (if lbl.isSome then 2 else 1)
          let (acc, i2) := labelsSeq fuel body acc (i + 1)
          labelsSeq fuel rest acc i2
        else
          let (acc, i2) := labelsSeq fuel (cs.drop 1) acc i
          labelsSeq fuel rest acc i2
      | none => labelsSeq fuel rest acc i

/-- The state of the field walk: per-space counters and the names so far. -/
structure Walk where
  names : NameTable := {}
  func : Nat := 0
  table : Nat := 0
  memory : Nat := 0
  global : Nat := 0
  tag : Nat := 0
  type : Nat := 0
  elem : Nat := 0
  data : Nat := 0

def addTo (m : NameMap) (i : Nat) (n : Option String) : NameMap :=
  match n with | some s => m ++ [(i, s)] | none => m

def addInd (m : IndirectMap) (i : Nat) (ns : NameMap) : IndirectMap :=
  if ns.isEmpty then m else m ++ [(i, ns)]

/-- The number of parameters of type `i` of a module (for functions without inline params). -/
def typeParams (m : Wasm.Module) (i : Nat) : Option Nat :=
  match m.types[i]? with
  | some ⟨[⟨_, _, .func ft⟩]⟩ => some ft.params.length
  | _ => none

/-- A function: its name, local names (parameters, then locals), labels. -/
def walkFunc (m : Wasm.Module) (fuel : Nat) (w : Walk) (id : Option String)
    (xs₀ : List SExp) : Walk :=
  -- only the header clauses: a flat body's `(param …)`/`(type …)` belong to its blocks
  let isHeader (x : SExp) : Bool := match headKw x with
    | some k => ["export", "import", "type", "param", "result", "local"].contains k
    | none => false
  let xs := xs₀.takeWhile isHeader
  let isImport := xs.any (headKw · == some "import")
  let hasInline := xs.any (fun x => headKw x == some "param" || headKw x == some "result")
  let typeIdx : Option Nat := xs.findSome? (fun x =>
    if headKw x == some "type" then
      match children x with
      | [_, .atom (.sym s)] => s.toNat?
      | _ => none
    else none)
  let (pnames, start) : NameMap × Option Nat :=
    if hasInline then
      let (ns, k) := namedDecls "param" 0 xs
      (ns, some k)
    else
      match typeIdx with
      | some t => ([], typeParams m t)
      | none => ([], some 0)  -- no type use: an implicit `[] -> []` type
  let names := w.names
  let names := { names with funcs := addTo names.funcs w.func id }
  let names :=
    if isImport then { names with locals := addInd names.locals w.func pnames }
    else
      let localsN := match start with
        | some k => some (pnames ++ (namedDecls "local" k xs).1)
        | none => none
      let body := xs₀.drop xs.length
      let lbls := (labelsSeq fuel body [] 0).1
      let names := match localsN with
        | some ls => { names with locals := addInd names.locals w.func ls }
        | none => names
      { names with labels := addInd names.labels w.func lbls }
  { w with names, func := w.func + 1 }

/-- One type definition (inside `type` or `rec`). -/
def walkType (w : Walk) (x : SExp) : Walk :=
  let cs := children x
  let id := (cs.drop 1).head?.bind idOf
  let names := w.names
  let names := { names with types := addTo names.types w.type id }
  -- the composite type, possibly under `(sub …)`
  let rec comp : Nat → SExp → Option SExp
    | 0, _ => none
    | n + 1, y =>
      match headKw y with
      | some "sub" => (children y).reverse.head?.bind (comp n)
      | some _ => some y
      | none => none
  let ct := (cs.reverse.head?).bind (comp 8)
  let names := match ct.bind headKw, ct with
    | some "func", some c =>
      { names with parameters := addInd names.parameters w.type (paramNames (children c)) }
    | some "struct", some c =>
      { names with fields := addInd names.fields w.type (namedDecls "field" 0 (children c)).1 }
    | _, _ => names
  { w with names, type := w.type + 1 }

/-- One import: the kind of its descriptor. -/
def walkImport (m : Wasm.Module) (fuel : Nat) (w : Walk) (desc : SExp) : Walk :=
  let id := nodeId desc
  let cs := children desc
  match headKw desc with
  | some "func" => walkFunc m fuel w id (cs.drop 1) |> fun w' =>
      -- imports carry only their inline parameter names
      w'
  | some "table" => { w with names.tables := addTo w.names.tables w.table id, table := w.table + 1 }
  | some "memory" => { w with names.memories := addTo w.names.memories w.memory id, memory := w.memory + 1 }
  | some "global" => { w with names.globals := addTo w.names.globals w.global id, global := w.global + 1 }
  | some "tag" =>
    { w with names.tags := addTo w.names.tags w.tag id,
             names.tagParameters := addInd w.names.tagParameters w.tag (paramNames cs),
             tag := w.tag + 1 }
  | _ => w

def walkField (m : Wasm.Module) (fuel : Nat) (w : Walk) (x : SExp) : Walk :=
  let id := nodeId x
  let cs := children x
  let rest := cs.drop (if id.isSome then 2 else 1)
  match headKw x with
  | some "func" =>
    let w := walkFunc m fuel w id rest
    if rest.any (headKw · == some "import") then
      -- inline import: parameter names only (already recorded); no locals/labels walk needed
      w
    else w
  | some "import" =>
    match cs with
    | [_, _, _, desc] =>
      let w := walkImport m fuel w desc
      -- an imported function records its inline parameter names as locals
      w
    | _ => w
  | some "type" => walkType w x
  | some "rec" => (cs.drop 1).foldl walkType w
  | some "table" =>
    let w := { w with names.tables := addTo w.names.tables w.table id, table := w.table + 1 }
    if rest.any (headKw · == some "elem") then { w with elem := w.elem + 1 } else w
  | some "memory" =>
    let w := { w with names.memories := addTo w.names.memories w.memory id, memory := w.memory + 1 }
    if rest.any (headKw · == some "data") then { w with data := w.data + 1 } else w
  | some "global" => { w with names.globals := addTo w.names.globals w.global id, global := w.global + 1 }
  | some "tag" =>
    { w with names.tags := addTo w.names.tags w.tag id,
             names.tagParameters := addInd w.names.tagParameters w.tag (paramNames rest),
             tag := w.tag + 1 }
  | some "elem" => { w with names.elems := addTo w.names.elems w.elem id, elem := w.elem + 1 }
  | some "data" => { w with names.data := addTo w.names.data w.data id, data := w.data + 1 }
  | _ => w

/-- The fields of the module document and the module's own identifier. -/
def moduleFields (x : SExp) : Option String × List SExp :=
  match toList? x with
  | some [top] =>
    if headKw top == some "module" then
      let cs := children top
      match cs.drop 1 with
      | y :: ys => match idOf y with
        | some n => (some n, ys)
        | none => (none, y :: ys)
      | [] => (none, [])
    else (none, [top])
  | some fs => (none, fs)
  | none => (none, [])

/-- The names of a text module (its S-expression document `x`, elaborated to `m`). -/
def ofTree (x : SExp) (m : Wasm.Module) (fuel : Nat) : NameTable :=
  let (mid, fields) := moduleFields x
  let w := fields.foldl (walkField m fuel) {}
  { w.names with module := mid }

/-- Rename by `(@name …)` annotations: a name equal to an annotated identifier becomes the
annotation's name. -/
def NameTable.rename (n : NameTable) (r : List (String × String)) : NameTable :=
  if r.isEmpty then n else
  let f (s : String) : String := ((r.find? (·.1 == s)).map (·.2)).getD s
  let fm (m : NameMap) : NameMap := m.map fun (i, s) => (i, f s)
  let fi (m : IndirectMap) : IndirectMap := m.map fun (i, ns) => (i, fm ns)
  { module := n.module.map f, funcs := fm n.funcs, locals := fi n.locals,
    labels := fi n.labels, types := fm n.types, tables := fm n.tables,
    memories := fm n.memories, globals := fm n.globals, elems := fm n.elems,
    data := fm n.data, fields := fi n.fields, tags := fm n.tags,
    parameters := fi n.parameters, tagParameters := fi n.tagParameters }

/-! ## Encoding -/

open Silmaril.Wasm.Binaryen.Exe (encU)

def encStr (s : String) : List UInt8 := encU s.utf8ByteSize ++ s.toUTF8.data.toList

def encMap (m : NameMap) : List UInt8 :=
  encU m.length ++ m.flatMap (fun (i, n) => encU i ++ encStr n)

def encIndirect (m : IndirectMap) : List UInt8 :=
  encU m.length ++ m.flatMap (fun (i, ns) => encU i ++ encMap ns)

def subsection (id : UInt8) (body : List UInt8) : List UInt8 := id :: (encU body.length ++ body)

def NameTable.isEmpty (n : NameTable) : Bool :=
  n.module.isNone && n.funcs.isEmpty && n.locals.isEmpty && n.labels.isEmpty &&
  n.types.isEmpty && n.tables.isEmpty && n.memories.isEmpty && n.globals.isEmpty &&
  n.elems.isEmpty && n.data.isEmpty && n.fields.isEmpty && n.tags.isEmpty &&
  n.parameters.isEmpty && n.tagParameters.isEmpty

/-- The payload of the `name` custom section (after its own name). -/
def NameTable.payload (n : NameTable) : List UInt8 :=
  let opt {α} (xs : List α) (f : List α → List UInt8) (id : UInt8) : List UInt8 :=
    if xs.isEmpty then [] else subsection id (f xs)
  (match n.module with | some s => subsection 0 (encStr s) | none => []) ++
  opt n.funcs encMap 1 ++ opt n.locals encIndirect 2 ++ opt n.labels encIndirect 3 ++
  opt n.types encMap 4 ++ opt n.tables encMap 5 ++ opt n.memories encMap 6 ++
  opt n.globals encMap 7 ++ opt n.elems encMap 8 ++ opt n.data encMap 9 ++
  opt n.fields encIndirect 10 ++ opt n.tags encMap 11 ++ opt n.parameters encIndirect 12 ++
  opt n.tagParameters encIndirect 13

/-- A custom section with the given name and payload, as bytes (`.error` only if a length
does not fit in `u32`). -/
def customSection (name : String) (payload : List UInt8) : Except String (List UInt8) := do
  let bn ← Binaryen.Exe.encName name
  let c := bn ++ payload
  pure ([0] ++ (← Binaryen.Exe.encU32 c.length) ++ c)

/-- The `name` section of `n`, or nothing when there are no names. -/
def NameTable.section (n : NameTable) : Except String (List UInt8) :=
  if n.isEmpty then pure [] else customSection "name" n.payload

end Silmaril.Wasm.Tools.Names
