module

public import Silmaril.Wasm.Tools.Names.Defs
public import Silmaril.Wasm.Tools.Annot.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Tools.Print.Raw

/-!
# The binary layout `wasm-tools parse` chooses

A module has many binary encodings. silmaril-lean's certified encoder writes one canonical
encoding; `wasm-tools parse` (the `wast` crate and `wasm-encoder`) chooses others from the
shape of the text:

* an element segment written with `(table x)` (or a legacy bare table index) uses the
  explicit-table forms (flags 2 and 6), one written with `func` (or bare indices) uses the
  function-index forms, and one written with a reference type the expression forms;
* a type written inside `(rec …)` keeps the `0x4E` group prefix even when the group has one
  type;
* a table with an initializer expression uses the `0x40 0x00` form;
* `(@custom …)` annotations become custom sections at their placement (`(before first)`,
  `(after code)`, …; `(after last)` by default), and the `name` section comes last.

`hints` reads these choices from the text's S-expression tree and `candidate` writes the
bytes. Neither is trusted: `relayout` keeps the candidate only when silmaril-lean's
certified decoder reads it back as a module whose canonical encoding is the canonical bytes,
so the result always encodes the module (`Silmaril.Wasm.Tools.Layout.Thms.relayout_sound`).
Otherwise the canonical bytes (followed by the `name` section) are used.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Layout

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Wasm.Binaryen.Exe
open Silmaril.Wasm.Tools.Names (headKw children nodeId moduleFields)

/-- How an element segment was written. -/
structure ElemHint where
  explicitTable : Bool
  indices : Bool
  deriving Repr, Inhabited

/-- The layout choices of a text, in field order. -/
structure Hints where
  /-- Per type-section entry: written as `(rec …)`. -/
  recs : Array Bool := #[]
  /-- Per defined table: has an initializer expression. -/
  tables : Array Bool := #[]
  elems : Array ElemHint := #[]
  /-- Per defined function: per `if` in flat order, was an `else` written? -/
  elses : Array (Array Bool) := #[]
  /-- Per defined function: branch hints as (index of the hinted instruction among the
  function's instruction starts, in encoding order; taken). -/
  branch : Array (List (Nat × Bool)) := #[]
  deriving Inhabited

def isSym (s : String) : SExp → Bool
  | .atom (.sym k) => k == s
  | _ => false

def isRefType (y : SExp) : Bool :=
  match y with
  | .atom (.sym s) => s.endsWith "ref"
  | _ => headKw y == some "ref"

def isFuncref (y : SExp) : Bool :=
  isSym "funcref" y ||
    (match children y with
     | [a, b, c] => isSym "ref" a && isSym "null" b && isSym "func" c
     | _ => false)

def isNumber : SExp → Bool
  | .atom (.sym s) => s.toNat?.isSome
  | _ => false

def isList (y : SExp) : Bool := headKw y |>.isSome

def tableField (h : Hints) (rest : List SExp) : Hints :=
  if rest.any (headKw · == some "import") then h
  else
    let rest := rest.filter (headKw · != some "export")
    match rest.dropWhile (!isRefType ·) with
    | rt :: after =>
      match after with
      | [e] =>
        if headKw e == some "elem" then
          let items := (children e).drop 1
          { h with tables := h.tables.push false,
                   elems := h.elems.push ⟨true, isFuncref rt && !items.any isList⟩ }
        else { h with tables := h.tables.push true }
      | [] => { h with tables := h.tables.push false }
      | _ => { h with tables := h.tables.push true }
    | [] => { h with tables := h.tables.push false }

def elemField (h : Hints) (rest : List SExp) : Hints :=
  let payload (tableOmitted : Bool) (ps : List SExp) : Bool :=
    match ps with
    | p :: _ => if isSym "func" p then true else if isRefType p then false else tableOmitted
    | [] => tableOmitted
  let hint : ElemHint :=
    match rest with
    | d :: ps =>
      if isSym "declare" d then ⟨false, payload false ps⟩
      else if headKw d == some "table" || isNumber d then ⟨true, payload false (ps.drop 1)⟩
      else if isList d && !isRefType d then ⟨false, payload true ps⟩
      else ⟨false, payload false rest⟩
    | [] => ⟨false, false⟩
  { h with elems := h.elems.push hint }

/-- Explicit `else`s of an instruction sequence, per `if` in the flat order of the
encoding (a folded `if`'s conditions come first). `stack` holds the open flat blocks
(`some k` for the `k`-th `if`). -/
def elsesSeq : Nat → List SExp → List (Option Nat) → Array Bool → Array Bool
  | 0, _, _, out => out
  | _ + 1, [], _, out => out
  | fuel + 1, x :: rest, stack, out =>
    match x with
    | .atom (.sym k) =>
      if k == "if" then elsesSeq fuel rest (some out.size :: stack) (out.push false)
      else if ["block", "loop", "try_table", "try"].contains k then
        elsesSeq fuel rest (none :: stack) out
      else if k == "else" then
        match stack with
        | some i :: _ => elsesSeq fuel rest stack (out.set! i true)
        | _ => elsesSeq fuel rest stack out
      else if k == "end" then elsesSeq fuel rest (stack.drop 1) out
      else elsesSeq fuel rest stack out
    | .atom _ => elsesSeq fuel rest stack out
    | _ =>
      let cs := children x
      match headKw x with
      | some "if" =>
        let isArm (y : SExp) := headKw y == some "then" || headKw y == some "else"
        let conds := cs.drop 1 |>.filter (fun y => isList y && !isArm y &&
          !(["result", "param", "type"].map some).contains (headKw y))
        let out := elsesSeq fuel conds [] out
        let hasElse := cs.any (headKw · == some "else")
        let out := out.push hasElse
        let arms := (cs.filter isArm).flatMap (fun y => (children y).drop 1)
        let out := elsesSeq fuel arms [] out
        elsesSeq fuel rest stack out
      | some _ =>
        let out := elsesSeq fuel (cs.drop 1) [] out
        elsesSeq fuel rest stack out
      | none => elsesSeq fuel rest stack out

def funcHdr (x : SExp) : Bool :=
  match headKw x with
  | some k => ["export", "import", "type", "param", "result", "local"].contains k
  | none => false

/-- The layout hints of a module document. -/
def hints (x : SExp) (fuel : Nat) : Hints :=
  (moduleFields x).2.foldl (fun h f =>
    let rest := (children f).drop (if (nodeId f).isSome then 2 else 1)
    match headKw f with
    | some "type" => { h with recs := h.recs.push false }
    | some "rec" => { h with recs := h.recs.push true }
    | some "table" => tableField h rest
    | some "elem" => elemField h rest
    | some "func" =>
      if rest.any (headKw · == some "import") then h
      else
        let body := rest.filter (!funcHdr ·)
        { h with elses := h.elses.push (elsesSeq fuel body [] #[]) }
    | _ => h) {}

/-! ## Branch hints -/

/-- The instruction starts of a body in encoding order (each instruction before its bodies,
`then` before `else`). -/
def flatInstrs : List Instr → List Instr
  | [] => []
  | i :: is =>
    let inner := match i with
      | .block _ b | .loop _ b | .tryTable _ _ b => flatInstrs b
      | .if_ _ t e => flatInstrs t ++ flatInstrs e
      | _ => []
    i :: (inner ++ flatInstrs is)

def isMarker : Instr → Bool
  | .intConst .i64 b => b.toNat == Annot.markerBits
  | _ => false

/-- The positions of the hinted instructions of one marked body: the instruction after each
marker pair, counted without the markers. -/
def markedPositions (body : List Instr) : List Nat :=
  let rec go : List Instr → Nat → List Nat
    | i :: .drop :: rest, k => if isMarker i then k :: go rest k else go (.drop :: rest) (k + 1)
    | _ :: rest, k => go rest (k + 1)
    | [], _ => []
  go (flatInstrs body) 0

/-- Per defined function of the marked module `m'`, its hints (positions paired with the hint
values in text order). -/
def hintPositions (m' : Module) (vals : List Bool) : Array (List (Nat × Bool)) :=
  let (out, _) := m'.funcs.foldl (fun (acc : Array (List (Nat × Bool)) × List Bool) f =>
    let ps := markedPositions f.body
    (acc.1.push (ps.zip acc.2), acc.2.drop ps.length)) (#[], vals)
  out

/-- The `metadata.code.branch_hint` section for the function bodies `bodies` (locals and
expression), the first defined function having index `nimp`. -/
def branchHintSection (h : Hints) (bodies : List (List UInt8)) (nimp : Nat) : List UInt8 :=
  let funcs := (bodies.zipIdx).filterMap fun (body, k) =>
    match h.branch[k]? with
    | some hs@(_ :: _) =>
      let b : ByteArray := ⟨body.toArray⟩
      match Silmaril.Wasm.Tools.Print.Raw.bodyEvents b 0 b.size with
      | some evs =>
        let starts := evs.toList.filterMap fun (off, ev) =>
          match ev with
          | .else_ | .end_ => none
          | _ => some off
        let entries := hs.filterMap fun (pos, taken) =>
          starts[pos]?.map fun off => encU off ++ [0x01, if taken then 1 else 0]
        some (encU (nimp + k) ++ encU entries.length ++ entries.flatten)
      | none => none
    | _ => none
  if funcs.isEmpty then []
  else
    let nm := "metadata.code.branch_hint".toUTF8.data.toList
    let body := encU nm.length ++ nm ++ encU funcs.length ++ funcs.flatten
    [0] ++ encU body.length ++ body

/-! ## Writing the candidate -/

def funcref : RefType := ⟨true, .abstract .func⟩

def funcItems (e : Elem) : Option (List FuncIdx) :=
  e.init.mapM fun (x : Expr) => match x with | [Instr.refFunc f] => some f | _ => none

def encElemHint (h : ElemHint) (e : Elem) : Except String (List UInt8) := do
  let fs := if h.indices then funcItems e else none
  let items ← match fs with
    | some ys => encVec (fun y => pure (encIdx y)) ys
    | none => encVec encExpr e.init
  let exprBit := if fs.isSome then 0 else 4
  let kind := match fs with | some _ => [0x00] | none => encRefType e.type
  match e.mode with
  | .active x off =>
    if !h.explicitTable && x.toNat = 0 && (fs.isSome || e.type == funcref) then
      pure (encU exprBit ++ (← encExpr off) ++ items)
    else pure (encU (2 + exprBit) ++ encIdx x ++ (← encExpr off) ++ kind ++ items)
  | .passive => pure (encU (1 + exprBit) ++ kind ++ items)
  | .declarative => pure (encU (3 + exprBit) ++ kind ++ items)

def encTableHint (explicit : Bool) (t : Table) : Except String (List UInt8) :=
  if explicit then do pure ([0x40, 0x00] ++ (← encTableType t.type) ++ (← encExpr t.init))
  else encTableWith encExpr t

def encRecHint (explicit : Bool) (r : RecType) : Except String (List UInt8) :=
  if explicit then do pure ([0x4E] ++ (← encVec encSubType r.types)) else encRecType r

/-- Insert an `else` opcode before the `end` of each `if` flagged in `flags` that has
none, in a function body `body` (locals and expression). -/
def insertElses (body : List UInt8) (flags : Array Bool) : List UInt8 :=
  if !flags.any id then body else
  let b : ByteArray := ⟨body.toArray⟩
  match Silmaril.Wasm.Tools.Print.Raw.bodyEvents b 0 b.size with
  | none => body
  | some evs => Id.run do
    -- positions of the `end`s to prefix with `else`
    let mut at_ : List Nat := []
    let mut stack : List (Option (Nat × Bool)) := []
    let mut k := 0
    for (off, ev) in evs do
      match ev with
      | .if_ => stack := some (k, false) :: stack; k := k + 1
      | .block => stack := none :: stack
      | .else_ =>
        match stack with
        | some (i, _) :: st => stack := some (i, true) :: st
        | _ => pure ()
      | .end_ =>
        match stack with
        | some (i, false) :: st =>
          if flags.getD i false then at_ := off :: at_
          stack := st
        | _ :: st => stack := st
        | [] => pure ()
      | .op => pure ()
    -- `at_` is in decreasing order
    return at_.foldl (fun bs p => bs.take p ++ [0x05] ++ bs.drop p) body

def bodyHint (flags : Array Bool) (f : Func) : Except String (List UInt8) := do
  let l ← encLocals f.locals
  let e ← encExpr f.body
  pure (insertElses (l ++ e) flags)

/-- `encVec` with the position of each element. -/
def encVecI {α : Type} (f : Nat → α → Except String (List UInt8)) (xs : List α) :
    Except String (List UInt8) := do
  let parts ← (xs.zipIdx).mapM fun (x, i) => f i x
  pure ((← encU32 xs.length) ++ parts.flatten)

def encCustom (c : Annot.Custom) : Except String (List UInt8) := do
  let body := (← encU32 c.name.length) ++ c.name ++ c.data
  pure ([0] ++ (← encU32 body.length) ++ body)

/-- The candidate bytes: the module in `wast`'s layout, the custom sections at their places
and `names` (the `name` section) last. -/
def candidate (h : Hints) (cs : List Annot.Custom) (names : List UInt8) (dataCount : Bool)
    (m : Module) : Except String (List UInt8) := do
  let at_ (p : Annot.Place) : Except String (List UInt8) := do
    pure ((← (cs.filter (·.place == p)).mapM encCustom).flatten)
  let around (a : String) (s : List UInt8) : Except String (List UInt8) := do
    pure ((← at_ (.before a)) ++ s ++ (← at_ (.after a)))
  let ty ← encVecI (fun i r => encRecHint (h.recs.getD i false) r) m.types
  let im ← encVec encImport m.imports
  let fn ← encVec (fun f => pure (encIdx f.type)) m.funcs
  let me ← encVec encMemory m.memories
  let tg ← encVec (fun t => pure (encTagType t)) m.tags
  let gl ← encVec encGlobal m.globals
  let ex ← encVec encExport m.exports
  let bodies ← (m.funcs.zipIdx).mapM fun (f, i) => bodyHint (h.elses.getD i #[]) f
  let co := (← encU32 bodies.length) ++ (← bodies.mapM fun b => do pure ((← encU32 b.length) ++ b)).flatten
  let nimp := (m.imports.filter fun im => match im.type with | .func _ => true | _ => false).length
  let bh := branchHintSection h bodies nimp
  let da ← encVec encData m.data
  let dc ← encU32 m.data.length
  let tb ← encVecI (fun i t => encTableHint (h.tables.getD i false) t) m.tables
  let el ← encVecI (fun i e => encElemHint (h.elems.getD i ⟨false, true⟩) e) m.elems
  let s1 ← encSection 1 m.types.length ty
  let s2 ← encSection 2 m.imports.length im
  let s3 ← encSection 3 m.funcs.length fn
  let s4 ← encSection 4 m.tables.length tb
  let s5 ← encSection 5 m.memories.length me
  let s13 ← encSection 13 m.tags.length tg
  let s6 ← encSection 6 m.globals.length gl
  let s7 ← encSection 7 m.exports.length ex
  let s8 ← encSection 8 (if m.start.isSome then 1 else 0) (encStart m.start)
  let s9 ← encSection 9 m.elems.length el
  let s12 ← encSection 12 (if dataCount && !m.data.isEmpty then 1 else 0) dc
  let s10 ← encSection 10 m.funcs.length co
  let s11 ← encSection 11 m.data.length da
  pure (header ++ (← at_ .beforeFirst) ++ (← around "type" s1) ++ (← around "import" s2) ++
    (← around "func" s3) ++ (← around "table" s4) ++ (← around "memory" s5) ++
    (← around "tag" s13) ++ (← around "global" s6) ++ (← around "export" s7) ++
    (← around "start" s8) ++ (← around "elem" s9) ++ s12 ++ (← at_ (.before "code")) ++ bh ++ s10 ++ (← at_ (.after "code")) ++
    (← around "data" s11) ++ (← at_ .afterLast) ++ names)

/-- Is `cand` a binary of the module whose canonical encoding (data count policy
`dataCount`) is `canon`? Checked with the certified decoder. -/
def accepts (dataCount : Bool) (canon cand : List UInt8) : Bool :=
  match Binary.Core.Decode.decodeModule ⟨cand.toArray⟩ with
  | .ok m' =>
    match encodeModuleWith? dataCount m' with
    | .ok c' => c' == canon
    | .error _ => false
  | .error _ => false

/-- The bytes `wasm-tools parse` writes, when the check accepts the candidate; otherwise the
canonical bytes followed by `names`. -/
def relayout (h : Hints) (cs : List Annot.Custom) (names : List UInt8) (dataCount : Bool)
    (m : Module) (canon : List UInt8) : List UInt8 :=
  match candidate h cs names dataCount m with
  | .ok cand => if accepts dataCount canon cand then cand else canon ++ names
  | .error _ => canon ++ names

end Silmaril.Wasm.Tools.Layout
