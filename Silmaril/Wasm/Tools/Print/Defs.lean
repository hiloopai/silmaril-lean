module

public import Silmaril.Wasm.Tools.Print.Float
public import Silmaril.Wasm.Tools.Print.Raw
public import Silmaril.Wasm.Tools.Print.Arity
public import Silmaril.Wasm.Tools.Parse.Defs
public import Silmaril.Wasm.Tools.Annot.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax

/-!
# `wasm-tools print`: a Core module binary to WAT, in wasmprinter's format

`printText cfg b` decodes `b` with silmaril-lean's certified decoder
(`Binary.Core.Decode.decodeModule`, sound for `Binary.Core.Encodes`) and writes its module in
the layout of wasmprinter 0.262 (wasm-tools 1.262.0): one field per line, instructions in
the flat form with `;; label = @N` and `(;@N;)` comments, `(;N;)` index comments, names from
the `name` section, `(@custom …)` and `(@producers …)` annotations in place.

The printer itself is untrusted. `printModule` **checks** its output: the text is read back
by the certified text pipeline of `Silmaril.Wasm.Tools.Parse` (`textModule`, sound for
`Text.Core.Encodes`), and both modules are re-encoded with silmaril-lean's certified encoder;
equal encodings make the two modules equal (the binary grammar is functional). The result
says whether the check passed (`certified`), and
`Silmaril.Wasm.Tools.Print.Thms.printModule_sound` turns a passed check into the specification:
the input bytes and the output text encode the same module.

Not printed from the binary (the decoded module does not keep them; see
`tools/wasm-tools/README.md`): whether a one-type recursion group was written as `rec`, an
empty `else`, an explicit table initializer equal to the default, and the element-segment
encoding (function indices versus expressions, explicit table index 0), which is
reconstructed from the module.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Print

open Silmaril Silmaril.Wasm
open Raw (Naming Names NameMap IndirectMap)
open Silmaril.Wasm.Tools.Annot (stripTrivia)

/-- Printer options (`wasm-tools print` flags). -/
structure Config where
  indentText : String := "  "
  nameUnnamed : Bool := false
  skeleton : Bool := false
  printOffsets : Bool := false
  /-- `-f`: folded instructions. -/
  fold : Bool := false
  /-- Terminal colours (`--color always`): the ANSI escapes termcolor writes for
  wasmprinter's `start_keyword`, `start_name`, … (`print.rs`, `PrintTermcolor`). -/
  color : Bool := false
  deriving Repr, Inhabited

/-- A folded instruction (wasmprinter's `FoldedInstruction`): its own text, the folded
operands, its result count and its offset and branch hint. -/
inductive FInst where
  | mk (plain : String) (folded : Array FInst) (results : Nat) (offset : Option Nat)
      (hint : Option String)
  deriving Inhabited

/-- The kind of an open block of the folding printer (`FrameKind`). -/
inductive FKind where
  | block | loop | if_ | else_ | tryTable
  deriving BEq, Inhabited

/-- An open block of the folding printer (wasmprinter's `Block`). -/
structure Frame where
  kind : FKind
  arity : Option (Nat × Nat)
  plain : String
  folded : Array FInst := #[]
  predicate : Array FInst := #[]
  consequent : Array FInst := #[]
  ifOffset : Option Nat := none
  offset : Option Nat
  hint : Option String := none
  deriving Inhabited

inductive Sep where
  | newline | none | noneThenSpace | space
  deriving BEq, Inhabited

structure PState where
  out : String := ""
  nesting : Nat := 0
  line : Nat := 0
  groupLines : List Nat := []
  -- operator state
  nestingStart : Nat := 0
  label : Nat := 0
  labelIdx : Array Nat := #[]
  sep : Sep := .newline
  func : Nat := 0
  -- raw opcode information of the current function body (`Raw.codeEvents`)
  evs : Array (Nat × Raw.Ev) := #[]
  evIdx : Nat := 0
  hints : List (Nat × Bool × Nat) := []
  elses : Array Bool := #[]
  ifIdx : Nat := 0
  bodyStart : Nat := 0
  curOff : Option Nat := none
  -- the folding printer (`-f`)
  frames : Array Frame := #[]
  pendingHint : Option String := none
  folding : Bool := false
  /-- Fold constant expressions (cleared for the one-instruction sugar form). -/
  foldConst : Bool := true
  deriving Inhabited

structure Env where
  cfg : Config
  names : Names
  module : Wasm.Module
  types : Array SubType
  /-- Per defined function: its body (`Raw.codeInfo`), when the walk succeeded. -/
  code : Array Raw.BodyInfo := #[]
  /-- The branch hints, per function index: instruction offset, taken, entry offset. -/
  branchHints : List (Nat × List (Nat × Bool × Nat)) := []
  /-- The type index of every function (imports first). -/
  funcTypes : Array Nat := #[]
  /-- The type index of every tag (imports first). -/
  tagTypes : Array Nat := #[]

abbrev PM := ReaderT Env (StateM PState)

def write (s : String) : PM Unit := modify fun st => { st with out := st.out ++ s }

/-! ## Colours (`PrintTermcolor` over termcolor's `Ansi`)

`set_color` writes a reset first (`ColorSpec::new()` has `reset`), then bold, then the
foreground: intense colours as `38;5;(8 + n)`. Without `cfg.color` these write nothing. -/

def esc (s : String) : PM Unit := do if (← read).cfg.color then write s
def startKeyword : PM Unit := esc "\x1b[0m\x1b[1m\x1b[38;5;11m"
def startType : PM Unit := esc "\x1b[0m\x1b[1m\x1b[38;5;10m"
def startName : PM Unit := esc "\x1b[0m\x1b[35m"
def startLiteral : PM Unit := esc "\x1b[0m\x1b[31m"
def startComment : PM Unit := esc "\x1b[0m\x1b[36m"
def resetColor : PM Unit := esc "\x1b[0m"

/-- `print_type_keyword`. -/
def typeKw (k : String) : PM Unit := do startType; write k; resetColor

/-- Hexadecimal, left-aligned in 6 columns (`{offset:<6x}`). -/
def offsetCol (off : Nat) : String :=
  let h := Float.hex off
  h ++ String.ofList (List.replicate (6 - h.length) ' ')

/-- `print_newline`: a new line, the offset comment under `--print-offsets` (spaces when the
offset is unknown), and the indentation. -/
def newlineOpt (off : Option Nat) : PM Unit := do
  let env ← read
  let (c0, c1) := if env.cfg.color then ("\x1b[0m\x1b[36m", "\x1b[0m") else ("", "")
  let pre := if env.cfg.printOffsets then
      match off with
      | some o => c0 ++ "(;@" ++ offsetCol o ++ ";)" ++ c1
      | none => "           "
    else ""
  let ind := String.join (List.replicate (min (← get).nesting 50) env.cfg.indentText)
  -- one append to the (unshared) output string
  modify fun st => { st with out := st.out ++ ("\n" ++ pre ++ ind), line := st.line + 1 }

def newline : PM Unit := newlineOpt none

def newlineAt (off : Nat) : PM Unit := newlineOpt (some off)

/-- `end_group_at_pos`: close a group; under `--print-offsets` always on a new line. -/
def endGroupAt (off : Nat) : PM Unit := do
  -- (the state is read field by field so that the output string stays unshared)
  let gl := (← get).groupLines
  let line := (← get).line
  modify fun st => { st with nesting := st.nesting - 1, groupLines := gl.drop 1 }
  match gl with
  | l :: _ => if (← read).cfg.printOffsets || l != line then newlineAt off
  | [] => if (← read).cfg.printOffsets then newlineAt off
  write ")"

def startGroup (name : String) : PM Unit := do
  write "("; startKeyword; write name; resetColor
  modify fun st => { st with nesting := st.nesting + 1, groupLines := st.line :: st.groupLines }

def endGroup : PM Unit := do
  let gl := (← get).groupLines
  let line := (← get).line
  modify fun st => { st with nesting := st.nesting - 1, groupLines := gl.drop 1 }
  match gl with
  | l :: _ => if l != line then newline
  | [] => pure ()
  write ")"

/-! ## Strings and names -/

def strContents (s : String) : String :=
  s.foldl (fun acc c =>
    let v := c.toNat
    if 0x20 ≤ v && v < 0x7f && c != '"' && c != '\\' then acc.push c
    else acc ++ "\\u{" ++ Float.hex v ++ "}") ""

def str (s : String) : String := "\"" ++ strContents s ++ "\""

def hexByte (x : UInt8) : String :=
  "\\" ++ String.singleton (Float.hexDigit (x.toNat / 16)) ++
    String.singleton (Float.hexDigit (x.toNat % 16))

def bytesLit (b : ByteArray) : String :=
  b.foldl (fun acc x =>
    if x ≥ 0x20 && x < 0x7f && x != 34 && x != 92 then acc.push (Char.ofNat x.toNat)
    else acc ++ hexByte x) "\"" ++ "\""

def Raw.Naming.ident (n : Naming) : String :=
  match n.kind with
  | .dollar => "$" ++ n.name
  | .quoted => "$\"" ++ strContents n.name ++ "\""
  | .synthetic p => "$\"" ++ p ++ " " ++ strContents n.name ++ "\""

def Raw.Naming.full (n : Naming) : String :=
  match n.kind with
  | .synthetic _ => n.ident ++ " (@name \"" ++ strContents n.name ++ "\")"
  | _ => n.ident

/-- `print_str`: a string literal. -/
def strLit (x : String) : PM Unit := do startLiteral; write (str x); resetColor

/-- `print_bytes`: a byte string literal. -/
def bytesP (b : ByteArray) : PM Unit := do startLiteral; write (bytesLit b); resetColor

/-- `Naming::write`: the identifier, and for a synthetic one its `(@name …)` group. -/
def writeNaming (n : Naming) : PM Unit := do
  write n.ident
  if let .synthetic _ := n.kind then
    write " "; startGroup "@name \""; write (strContents n.name); write "\""; endGroup

/-- `print_idx`: a reference to an item. -/
def idx (m : NameMap) (desc : String) (i : Nat) : PM Unit := do
  let env ← read
  startName
  match m.get? i with
  | some n => write n.ident
  | none => if env.cfg.nameUnnamed then write s!"$#{desc}{i}" else write (toString i)
  resetColor

/-- `print_name`: the name and index comment at a definition. -/
def nameAt (m : NameMap) (desc : String) (i : Nat) : PM Unit := do
  let env ← read
  startName
  match m.get? i with
  | some n => writeNaming n; write " "
  | none => if env.cfg.nameUnnamed then write s!"$#{desc}{i} " else pure ()
  write s!"(;{i};)"
  resetColor

def typeIdx (i : Nat) : PM Unit := do idx (← read).names.types "type" i

/-! ## Types -/

def absHeap : AbsHeapType → String
  | .any => "any" | .eq => "eq" | .i31 => "i31" | .struct => "struct" | .array => "array"
  | .none => "none" | .func => "func" | .nofunc => "nofunc" | .exn => "exn"
  | .noexn => "noexn" | .extern => "extern" | .noextern => "noextern"

def heapType : HeapType → PM Unit
  | .abstract a => typeKw (absHeap a)
  | .typeIdx i => typeIdx i.toNat

def refType (r : RefType) : PM Unit :=
  if r.nullable then
    match r.heap with
    | .abstract .func => typeKw "funcref" | .abstract .extern => typeKw "externref"
    | .abstract .i31 => typeKw "i31ref" | .abstract .any => typeKw "anyref"
    | .abstract .none => typeKw "nullref" | .abstract .noextern => typeKw "nullexternref"
    | .abstract .nofunc => typeKw "nullfuncref" | .abstract .eq => typeKw "eqref"
    | .abstract .struct => typeKw "structref" | .abstract .array => typeKw "arrayref"
    | .abstract .exn => typeKw "exnref" | .abstract .noexn => typeKw "nullexnref"
    | h => do startGroup "ref"; write " null "; heapType h; endGroup
  else do startGroup "ref "; heapType r.heap; endGroup

def valType : ValType → PM Unit
  | .num (.int .i32) => typeKw "i32"
  | .num (.int .i64) => typeKw "i64"
  | .num (.float .f32) => typeKw "f32"
  | .num (.float .f64) => typeKw "f64"
  | .vec .v128 => typeKw "v128"
  | .ref r => refType r

/-- Whose names a parameter list uses. -/
inductive ParamNames where
  | type (t : Nat) | tag (t : Nat) | locals (f : Nat) | none

/-- `NamedLocalPrinter`: params or locals, grouped while unnamed. -/
def namedLocals (group : String) (names : ParamNames) (start : Nat) (ts : List ValType) :
    PM Unit := do
  let env ← read
  let mut inGroup := false
  let mut first := true
  let mut i := start
  for t in ts do
    let n : Option Naming := match names with
      | .type ty => env.names.params.get? (ty, i)
      | .tag ty => env.names.tagParams.get? (ty, i)
      | .locals f => env.names.locals.get? (f, i)
      | .none => none
    if n.isSome && inGroup then endGroup; inGroup := false
    if first then first := false else write " "
    if !inGroup then startGroup group; write " "; inGroup := true
    let mut endAfter := false
    match n with
    | some n => writeNaming n; write " "; endAfter := true
    | none =>
      match names with
      | .locals _ => if env.cfg.nameUnnamed then write s!"$#local{i} "; endAfter := true
      | _ => pure ()
    valType t
    if endAfter then endGroup; inGroup := false
    i := i + 1
  if inGroup then endGroup

def funcType (ft : FuncType) (names : ParamNames) : PM Unit := do
  if !ft.params.isEmpty then write " "
  namedLocals "param" names 0 ft.params
  if !ft.results.isEmpty then
    write " "; startGroup "result"
    for r in ft.results do write " "; valType r
    endGroup

def storageType : StorageType → PM Unit
  | .val t => valType t
  | .packed .i8 => write "i8"
  | .packed .i16 => write "i16"

def fieldType (f : FieldType) (tyField : Option (Nat × Nat)) : PM Unit := do
  let env ← read
  write " "
  if let some (t, i) := tyField then
    match env.names.fields.get? (t, i) with
    | some n => write (n.ident ++ " ")
    | none => if env.cfg.nameUnnamed then write s!"$#field{i} "
  if f.mutability == .var then write "(mut "
  storageType f.storage
  if f.mutability == .var then write ")"

def composite (ct : CompositeType) (tyIdx : Nat) : PM Unit :=
  match ct with
  | .func ft => do startGroup "func"; funcType ft (.type tyIdx); endGroup
  | .array f => do startGroup "array"; fieldType f none; endGroup
  | .struct fs => do
    startGroup "struct"
    let mut i := 0
    for f in fs do
      write " (field"; fieldType f (some (tyIdx, i)); write ")"; i := i + 1
    endGroup

def subType (st : SubType) (tyIdx : Nat) : PM Unit := do
  if !st.final_ || !st.supertypes.isEmpty then
    startGroup "sub"
    write " "
    if st.final_ then write "final "
    for s in st.supertypes do typeIdx s.toNat; write " "
    composite st.body tyIdx
    endGroup
  else composite st.body tyIdx

def typeDef (st : SubType) (tyIdx : Nat) : PM Unit := do
  startGroup "type "
  nameAt (← read).names.types "type" tyIdx
  write " "
  subType st tyIdx
  endGroup

/-- The function type at a type index, if it is a plain final function type. -/
def funcTypeAt (i : Nat) : PM (Option FuncType) := do
  let env ← read
  match env.types[i]? with
  | some ⟨_, _, .func ft⟩ => pure (some ft)
  | _ => pure none

/-- `print_core_type_ref`: `(type N)`. -/
def typeRef (i : Nat) : PM Unit := do startGroup "type "; typeIdx i; endGroup

/-- `print_core_functype_idx`: `(type N)` and the signature. -/
def typeUse (i : Nat) (names : ParamNames) : PM Unit := do
  startGroup "type "; typeIdx i; endGroup
  if let some ft ← funcTypeAt i then funcType ft names

def limits (l : Limits) : String :=
  toString l.min.val ++ (match l.max with | some m => " " ++ toString m.val | none => "")

def tableType (t : TableType) (index : Option Nat) : PM Unit := do
  startGroup "table "
  if let some i := index then nameAt (← read).names.tables "table" i; write " "
  if t.address == .i64 then typeKw "i64 "
  startLiteral; write (limits t.limits); resetColor; write " "; refType t.element

def memoryType (t : MemoryType) (index : Option Nat) : PM Unit := do
  startGroup "memory "
  if let some i := index then nameAt (← read).names.memories "memory" i; write " "
  if t.address == .i64 then typeKw "i64 "
  startLiteral; write (limits t.limits); resetColor

def globalType (t : GlobalType) (index : Option Nat) : PM Unit := do
  startGroup "global "
  if let some i := index then nameAt (← read).names.globals "global" i; write " "
  if t.mutability == .var then write "("; typeKw "mut "; valType t.value; write ")"
  else valType t.value

def tagType (t : TagType) (index : Option Nat) : PM Unit := do
  startGroup "tag "
  if let some i := index then nameAt (← read).names.tags "tag" i; write " "
  typeUse t.toNat (match index with | some i => .tag i | none => .none)

/-! ## Instructions -/

def separator : PM Unit := do
  match (← get).sep with
  | .newline => do newlineOpt (← get).curOff
  | .none => pure ()
  | .noneThenSpace => modify fun st => { st with sep := .space }
  | .space => write " "

def curDepth : PM Nat := do let st ← get; pure (st.nesting - st.nestingStart)

def blockStart : PM Unit := do
  separator
  modify fun st => { st with nesting := st.nesting + 1, labelIdx := st.labelIdx.push st.label }

def blockMid : PM Unit := do
  modify fun st => { st with nesting := st.nesting - 1 }
  separator
  modify fun st => { st with nesting := st.nesting + 1 }

def blockEnd : PM Unit := do
  modify fun st => if st.nesting > st.nestingStart then { st with nesting := st.nesting - 1 } else st
  separator

def blockType (bt : BlockType) : PM Bool := do
  let env ← read
  let key := ((← get).func, (← get).label)
  let hasName ← match env.names.labels.get? key with
    | some n => do write " "; writeNaming n; pure true
    | none =>
      if env.cfg.nameUnnamed then do
        let d ← curDepth; write s!" $#label{d - 1}"; pure true
      else pure false
  match bt with
  | .empty => pure ()
  | .value t => do write " "; startGroup "result "; valType t; endGroup
  | .typeIdx i => do write " "; typeUse i.toNat .none
  pure hasName

def labelComment (hasName : Bool) : PM Unit := do
  if !hasName then
    let d ← curDepth
    write " "
    startComment
    match (← get).sep with
    | .newline | .none => write s!";; label = @{d}"
    | _ => write s!" (; label = @{d} ;)"
    resetColor
  modify fun st => { st with label := st.label + 1 }

def relDepth (depth : Nat) : PM Unit := do
  let env ← read
  write " "
  let cur ← curDepth
  if depth ≤ cur then
    let i := cur - depth
    let st ← get
    let name : Option Naming :=
      if i = 0 then none
      else (st.labelIdx[i - 1]?).bind fun li => env.names.labels.get? (st.func, li)
    let conflict := match name with
      | some n => (st.labelIdx.toList.drop i).any fun other =>
          match env.names.labels.get? (st.func, other) with
          | some o => o.name == n.name
          | none => false
      | none => false
    match name with
    | some n => if !conflict then writeNaming n else do startName; write (toString depth); resetColor
    | none =>
      if !conflict && env.cfg.nameUnnamed && i > 0 then
        startName; write s!"$#label{i - 1}"; resetColor
      else
        startName; write (toString depth); resetColor
        if !conflict && i > 0 then startComment; write s!" (;@{i};)"; resetColor
  else write s!"{depth} (; INVALID ;)"

def localIdx (i : Nat) : PM Unit := do
  let env ← read
  startName
  match env.names.locals.get? ((← get).func, i) with
  | some n => write n.ident
  | none => if env.cfg.nameUnnamed then write s!"$#local{i}" else write (toString i)
  resetColor

def fieldIdx (t i : Nat) : PM Unit := do
  let env ← read
  startName
  match env.names.fields.get? (t, i) with
  | some n => write n.ident
  | none => if env.cfg.nameUnnamed then write s!"$#field{i}" else write (toString i)
  resetColor

def sp : PM Unit := write " "

def funcI (i : Nat) : PM Unit := do sp; idx (← read).names.funcs "func" i
def globalI (i : Nat) : PM Unit := do sp; idx (← read).names.globals "global" i
def tableI (i : Nat) : PM Unit := do sp; idx (← read).names.tables "table" i
def memoryI (i : Nat) : PM Unit := do sp; idx (← read).names.memories "memory" i
def dataI (i : Nat) : PM Unit := do sp; idx (← read).names.datas "data" i
def elemI (i : Nat) : PM Unit := do sp; idx (← read).names.elems "elem" i
def tagI (i : Nat) : PM Unit := do sp; idx (← read).names.tags "tag" i
def typeI (i : Nat) : PM Unit := do sp; typeIdx i

def signedInt (w : Nat) (n : Nat) : String :=
  if n ≥ 2 ^ (w - 1) then "-" ++ toString (2 ^ w - n) else toString n

def memarg (m : MemIdx) (a : MemArg) (natural : Nat) : PM Unit := do
  if m.toNat != 0 then memoryI m.toNat
  if a.offset.val != 0 then write s!" offset={a.offset.val}"
  if 2 ^ a.align.val != natural then write s!" align={2 ^ a.align.val}"

/-- Name and natural alignment (bytes) of a load/store. -/
def memOpName (i : Instr) (m : MemIdx) (a : MemArg) : Option (String × Nat) :=
  (Text.Core.memOps.find? (fun e => Binaryen.Toolkit.Wat.integerMemoryEq (e.2.2 m a) i)).map
    fun e => (e.1, e.2.1)

def laneMemOpName (i : Instr) (m : MemIdx) (a : MemArg) (l : LaneIdx) : Option (String × Nat) :=
  (Text.Core.laneMemOps.find? (fun e =>
      Binaryen.Toolkit.Wat.laneInstructionEq (e.2.2 m a l) i)).map fun e => (e.1, e.2.1)

def laneOpName (i : Instr) (l : LaneIdx) : Option String :=
  (Text.Core.laneOps.find? (fun e => Binaryen.Toolkit.Wat.laneInstructionEq (e.2 l) i)).map
    (·.1)

def v128Lit (bits : BitVec 128) : String :=
  let n := bits.toNat
  " i32x4" ++ String.join ((List.range 4).map fun k =>
    let w := n / 2 ^ (32 * k) % 2 ^ 32
    let h := Float.hex w
    " 0x" ++ String.ofList (List.replicate (8 - h.length) '0') ++ h)

def signedName (base : String) : Option Signedness → String
  | none => base
  | some .signed => base ++ "_s"
  | some .unsigned => base ++ "_u"

/-- A float literal of `Float.f32`/`Float.f64` (`[-]LIT (;=…;)`) in `print_f32`'s colours: the
sign plain, the literal in the literal colour, the `(;=…;)` comment in the comment colour
(for `inf`/`nan` the space before it is part of the literal). -/
def floatLit (t : String) : PM Unit := do
  let (sign, rest) := if t.startsWith "-" then ("-", (t.drop 1).toString) else ("", t)
  write sign
  match rest.splitOn " (;=" with
  | [lit, cmt] =>
    let special := lit.startsWith "inf" || lit.startsWith "nan"
    startLiteral; write (if special then lit ++ " " else lit)
    startComment; write ((if special then "(;=" else " (;=") ++ cmt)
    resetColor
  | _ => write rest

/-- A plain (non-block) instruction, after its separator. Unknown forms print as an
`unknown` keyword, which the check then rejects. -/
def plain (i : Instr) : PM Unit := do
  match i with
  | .select none => write "select"
  | .select (some ts) => do
    -- `TypedSelect` (one type) opens `(result ` with the space inside the keyword colour,
    -- `TypedSelectMulti` writes ` t` per type
    write "select "
    match ts with
    | [t] => do startGroup "result "; valType t
    | _ => do startGroup "result"; for t in ts do write " "; valType t
    endGroup
  | .br l => do write "br"; relDepth l.toNat
  | .brIf l => do write "br_if"; relDepth l.toNat
  | .brTable ls l => do write "br_table"; for x in ls do relDepth x.toNat
                        relDepth l.toNat
  | .brOnNull l => do write "br_on_null"; relDepth l.toNat
  | .brOnNonNull l => do write "br_on_non_null"; relDepth l.toNat
  | .brOnCast l s t => do write "br_on_cast"; relDepth l.toNat; sp; refType s; sp; refType t
  | .brOnCastFail l s t => do
    write "br_on_cast_fail"; relDepth l.toNat; sp; refType s; sp; refType t
  | .call f => do write "call"; funcI f.toNat
  | .callRef t => do write "call_ref"; sp; typeIdx t.toNat
  | .callIndirect tb t => do
    write "call_indirect"; if tb.toNat != 0 then tableI tb.toNat
    sp; typeRef t.toNat
  | .returnCall f => do write "return_call"; funcI f.toNat
  | .returnCallRef t => do write "return_call_ref"; sp; typeIdx t.toNat
  | .returnCallIndirect tb t => do
    write "return_call_indirect"; if tb.toNat != 0 then tableI tb.toNat
    sp; typeRef t.toNat
  | .throw t => do write "throw"; tagI t.toNat
  | .localGet n => do write "local.get"; sp; localIdx n.toNat
  | .localSet n => do write "local.set"; sp; localIdx n.toNat
  | .localTee n => do write "local.tee"; sp; localIdx n.toNat
  | .globalGet n => do write "global.get"; globalI n.toNat
  | .globalSet n => do write "global.set"; globalI n.toNat
  | .tableGet t => do write "table.get"; tableI t.toNat
  | .tableSet t => do write "table.set"; tableI t.toNat
  | .tableSize t => do write "table.size"; tableI t.toNat
  | .tableGrow t => do write "table.grow"; tableI t.toNat
  | .tableFill t => do write "table.fill"; tableI t.toNat
  | .tableCopy d s => do
    write "table.copy"; if d.toNat != 0 || s.toNat != 0 then tableI d.toNat; tableI s.toNat
  | .tableInit t e => do write "table.init"; if t.toNat != 0 then tableI t.toNat
                         elemI e.toNat
  | .elemDrop e => do write "elem.drop"; elemI e.toNat
  | .intLoad _ _ m a | .intStore _ _ m a | .floatLoad _ m a | .floatStore _ m a
  | .vecLoad _ m a | .vecStore m a =>
    match memOpName i m a with
    | some (n, nat) => do write n; memarg m a nat
    | none => write "unknown"
  | .vecLoadLane _ m a l | .vecStoreLane _ m a l =>
    match laneMemOpName i m a l with
    | some (n, nat) => do write n; memarg m a nat; write s!" {l.val}"
    | none => write "unknown"
  | .memorySize m => do write "memory.size"; if m.toNat != 0 then memoryI m.toNat
  | .memoryGrow m => do write "memory.grow"; if m.toNat != 0 then memoryI m.toNat
  | .memoryFill m => do write "memory.fill"; if m.toNat != 0 then memoryI m.toNat
  | .memoryCopy d s => do
    write "memory.copy"; if d.toNat != 0 || s.toNat != 0 then memoryI d.toNat; memoryI s.toNat
  | .memoryInit m d => do write "memory.init"; if m.toNat != 0 then memoryI m.toNat
                          dataI d.toNat
  | .dataDrop d => do write "data.drop"; dataI d.toNat
  | .refNull h => do write "ref.null"; sp; heapType h
  | .refTest r => do write "ref.test"; sp; refType r
  | .refCast r => do write "ref.cast"; sp; refType r
  | .refFunc f => do write "ref.func"; funcI f.toNat
  | .structNew t => do write "struct.new"; typeI t.toNat
  | .structNewDefault t => do write "struct.new_default"; typeI t.toNat
  | .structGet s t f => do
    write (signedName "struct.get" s)
    typeI t.toNat; sp; fieldIdx t.toNat f.toNat
  | .structSet t f => do write "struct.set"; typeI t.toNat; sp; fieldIdx t.toNat f.toNat
  | .arrayNew t => do write "array.new"; typeI t.toNat
  | .arrayNewDefault t => do write "array.new_default"; typeI t.toNat
  | .arrayNewFixed t n => do write "array.new_fixed"; typeI t.toNat; write s!" {n.val}"
  | .arrayNewData t d => do write "array.new_data"; typeI t.toNat; dataI d.toNat
  | .arrayNewElem t e => do write "array.new_elem"; typeI t.toNat; elemI e.toNat
  | .arrayGet s t => do
    write (signedName "array.get" s)
    typeI t.toNat
  | .arraySet t => do write "array.set"; typeI t.toNat
  | .arrayFill t => do write "array.fill"; typeI t.toNat
  | .arrayCopy d s => do write "array.copy"; typeI d.toNat; typeI s.toNat
  | .arrayInitData t d => do write "array.init_data"; typeI t.toNat; dataI d.toNat
  | .arrayInitElem t e => do write "array.init_elem"; typeI t.toNat; elemI e.toNat
  | .intConst .i32 b => do
    write "i32.const"; startLiteral; write s!" {signedInt 32 b.toNat}"; resetColor
  | .intConst .i64 b => do
    write "i64.const"; startLiteral; write s!" {signedInt 64 b.toNat}"; resetColor
  | .floatConst .f32 b => do write "f32.const "; floatLit (Float.f32 b.toNat)
  | .floatConst .f64 b => do write "f64.const "; floatLit (Float.f64 b.toNat)
  | .vecConst b => do
    write "v128.const"; typeKw " i32x4"; startLiteral; write ((v128Lit b).drop 6).toString
    resetColor
  | .vecShuffle ls => do write "i8x16.shuffle"; for l in ls do write s!" {l.val}"
  | .vecExtractLane _ _ l | .vecReplaceLane _ l =>
    match laneOpName i l with
    | some n => write s!"{n} {l.val}"
    | none => write "unknown"
  | _ =>
    match Text.Core.nullaryName i with
    | some n => write n
    | none => write "unknown"

def catchClause (c : Catch) : PM Unit := do
  write " "
  match c with
  | .catch_ t l => do startGroup "catch"; tagI t.toNat; relDepth l.toNat; endGroup
  | .catchRef t l => do startGroup "catch_ref"; tagI t.toNat; relDepth l.toNat; endGroup
  | .catchAll l => do startGroup "catch_all"; relDepth l.toNat; endGroup
  | .catchAllRef l => do startGroup "catch_all_ref"; relDepth l.toNat; endGroup

/-- Before each opcode of a function body: print its branch hint, if any
(`(@metadata.code.branch_hint …)`, as wasmprinter's `print_operators`). -/
def opHook : PM Unit := do
  match (← get).evs[(← get).evIdx]? with
  | some (off, _) =>
    modify fun st => { st with evIdx := st.evIdx + 1, curOff := some (st.bodyStart + off) }
    match (← get).hints.find? (·.1 == off) with
    | some (_, taken, at_) =>
      let h := if taken then "@metadata.code.branch_hint \"\\01\""
        else "@metadata.code.branch_hint \"\\00\""
      -- the folding printer attaches the hint to the next folded instruction
      if (← get).folding then modify fun st => { st with pendingHint := some h }
      else newlineAt at_; startComment; write ("(" ++ h ++ ")"); resetColor
    | none => pure ()
  | none => pure ()

/-- Was the next `if` written with an `else`? -/
def nextIfElse : PM Bool := do
  let i := (← get).ifIdx
  modify fun st => { st with ifIdx := st.ifIdx + 1 }
  pure ((← get).elses.getD i false)

def endOp : PM Unit := do
  opHook; blockEnd; write "end"
  modify fun st => { st with labelIdx := st.labelIdx.pop }

mutual
def instr : Instr → PM Unit
  | .block bt body => do
    opHook; blockStart; write "block"; let h ← blockType bt; labelComment h
    instrs body; endOp
  | .loop bt body => do
    opHook; blockStart; write "loop"; let h ← blockType bt; labelComment h
    instrs body; endOp
  | .if_ bt th el => do
    opHook
    let explicitElse ← nextIfElse
    blockStart; write "if"; let h ← blockType bt; labelComment h
    instrs th
    if !el.isEmpty || explicitElse then
      opHook; blockMid; write "else"
      instrs el
    endOp
  | .tryTable bt cs body => do
    opHook; blockStart; write "try_table"; let h ← blockType bt
    -- the catch labels are resolved outside the `try_table`
    modify fun st => { st with nesting := st.nesting - 2, labelIdx := st.labelIdx.pop }
    for c in cs do catchClause c
    modify fun st => { st with nesting := st.nesting + 2, labelIdx := st.labelIdx.push st.label }
    labelComment h
    instrs body; endOp
  | i => do opHook; separator; plain i

def instrs : List Instr → PM Unit
  | [] => pure ()
  | i :: is => do instr i; instrs is
end

/-! ## Folded instructions (`-f`, wasmprinter's `PrintOperatorFolded`)

Each instruction's own text is printed as in the flat form (separator `none`) into a buffer;
an instruction then takes as folded operands the preceding instructions whose result counts
add up to its parameter count (`handle_plain`), with the arities of wasmparser's
`operator_arity`. Blocks collect their bodies; an `if` takes the preceding instruction as
its condition. -/

/-- Run `act` with the output redirected to a fresh buffer and the separator `none`;
return the buffer. -/
def capture (act : PM Unit) : PM String := do
  let saved := (← get).out
  let sep := (← get).sep
  modify fun st => { st with out := "", sep := .none }
  act
  let o := (← get).out
  modify fun st => { st with out := saved, sep }
  pure o

def typeArity (t : Nat) : PM (Option (Nat × Nat)) := do
  match (← read).types[t]? with
  | some ⟨_, _, .func ft⟩ => pure (some (ft.params.length, ft.results.length))
  | some ⟨_, _, .struct fs⟩ => pure (some (fs.length, fs.length))
  | _ => pure none

def blockArity : BlockType → PM (Option (Nat × Nat))
  | .empty => pure (some (0, 0))
  | .value _ => pure (some (0, 1))
  | .typeIdx i => typeArity i.toNat

/-- `label_block`: the arity and kind of the block `depth` labels out. -/
def labelBlock (depth : Nat) : PM (Option (Option (Nat × Nat) × FKind)) := do
  let fs := (← get).frames
  let cur ← curDepth
  if fs.size != cur + 1 || depth + 1 > fs.size then return none
  pure ((fs[fs.size - 1 - depth]?).map fun f => (f.arity, f.kind))

def brArity (depth : Nat) : PM (Option Nat) := do
  match ← labelBlock depth with
  | some (some (p, r), k) => pure (some (if k == .loop then p else r))
  | _ => pure none

/-- `operator_arity` of a non-block instruction whose text is `txt`. -/
def opArity (i : Instr) (txt : String) : PM (Option (Nat × Nat)) := do
  let env ← read
  let fixed : Option (Nat × Nat) :=
    -- the mnemonic: the text up to the first space or colour escape
    let name := ((String.ofList (txt.toList.takeWhile (· != '\x1b'))).splitOn " ").headD ""
    (Arity.table.lookup name)
  let ofType (t : Nat) (f : Nat × Nat → Nat × Nat) : PM (Option (Nat × Nat)) := do
    pure ((← typeArity t).map f)
  match i with
  | .br l => pure ((← brArity l.toNat).map (·, 0))
  | .brIf l => pure ((← brArity l.toNat).map fun n => (n + 1, n))
  | .brTable _ l => pure ((← brArity l.toNat).map fun n => (n + 1, 0))
  | .return_ =>
    match ← labelBlock ((← get).frames.size - 1) with
    | some (some (_, r), _) => pure (some (r, 0))
    | _ => pure none
  | .call f => match env.funcTypes[f.toNat]? with
    | some t => typeArity t
    | none => pure none
  | .returnCall f => match env.funcTypes[f.toNat]? with
    | some t => ofType t fun (p, _) => (p, 0)
    | none => pure none
  | .callIndirect _ t | .callRef t => ofType t.toNat fun (p, r) => (p + 1, r)
  | .returnCallIndirect _ t | .returnCallRef t => ofType t.toNat fun (p, _) => (p + 1, 0)
  | .structNew t => ofType t.toNat fun (p, _) => (p, 1)
  | .arrayNewFixed _ n => pure (some (n.val, 1))
  | .select (some ts) =>
    if ts.length == 1 then pure (some (3, 1)) else pure (some (1 + 2 * ts.length, ts.length))
  | .throw tg => match env.tagTypes[tg.toNat]? with
    | some t => ofType t fun (p, _) => (p, 0)
    | none => pure none
  | .brOnNull l => pure ((← brArity l.toNat).map fun n => (n + 1, n + 1))
  | .brOnNonNull l => pure ((← brArity l.toNat).bind fun n => if n = 0 then none else some (n, n - 1))
  | .brOnCast l _ _ | .brOnCastFail l _ _ => pure ((← brArity l.toNat).map fun n => (n, n))
  | _ => pure fixed

def FInst.results : FInst → Nat | .mk _ _ r _ _ => r

/-- `handle_plain`. -/
def handlePlain (txt : String) (params results : Nat) : PM Unit := do
  let fs := (← get).frames
  match fs.back? with
  | none => pure ()
  | some top =>
    let n := top.folded.size
    let (first, results) := Id.run do
      let mut first := n
      let mut count := 0
      let mut results := results
      if params > 0 then
        for k in [0:n] do
          let pos := n - 1 - k
          count := count + (top.folded[pos]!).results
          if count == params then first := pos; break
          else if count > params then results := 2 ^ 32 - 1; break
      return (first, results)
    let inst := FInst.mk txt (top.folded.extract first n) results (← get).curOff
      (← get).pendingHint
    let top := { top with folded := (top.folded.extract 0 first).push inst }
    modify fun st => { st with frames := st.frames.pop.push top, pendingHint := none }

def pushFrame (f : Frame) : PM Unit := modify fun st => { st with frames := st.frames.push f }

/-- `push_if`: the preceding instruction becomes the condition. -/
def pushIf (arity : Option (Nat × Nat)) (txt : String) : PM Unit := do
  let fs := (← get).frames
  match fs.back? with
  | none => pure ()
  | some top =>
    let pred := match top.folded.back? with | some p => #[p] | none => #[]
    let top := { top with folded := top.folded.pop }
    let hint := (← get).pendingHint
    modify fun st => { st with frames := st.frames.pop.push top, pendingHint := none }
    pushFrame { kind := .if_, arity, plain := txt, predicate := pred, offset := (← get).curOff, hint }

def handleElse : PM Unit := do
  match (← get).frames.back? with
  | some f =>
    if f.kind == .if_ then
      let off := (← get).curOff
      let f' : Frame := { f with kind := .else_, folded := #[], consequent := f.folded, ifOffset := f.offset, offset := off }
      modify fun st => { st with frames := st.frames.pop.push f' }
  | none => pure ()

/-- `handle_end`: close the innermost block into an instruction of its parent. -/
def handleEnd (results : Nat) : PM Unit := do
  match (← get).frames.back? with
  | none => pure ()
  | some f =>
    let inst := match f.kind with
      | .block | .loop | .tryTable => FInst.mk f.plain f.folded results f.offset none
      | .if_ =>
        FInst.mk f.plain (f.predicate.push (.mk "then" f.folded results f.offset none)) results
          f.offset f.hint
      | .else_ =>
        FInst.mk f.plain ((f.predicate.push (.mk "then" f.consequent results f.ifOffset none)).push
          (.mk "else" f.folded results f.offset none)) results f.ifOffset f.hint
    modify fun st =>
      let fs := st.frames.pop
      match fs.back? with
      | some p => { st with frames := fs.pop.push { p with folded := p.folded.push inst } }
      | none => { st with frames := fs }

/-- `print_separator` of the folded printer. -/
def foldSep (off : Option Nat) : PM Unit := do
  match (← get).sep with
  | .newline => newlineOpt off
  | .none => pure ()
  | .noneThenSpace => modify fun st => { st with sep := .space }
  | .space => write " "

/-- Print a folded instruction (`PrintOperatorFolded::print`). -/
def printF : FInst → PM Unit
  | .mk plain folded _ off hint => do
    if let some h := hint then
      foldSep off; write ("(" ++ h ++ ")")
    foldSep off
    write ("(" ++ plain)
    if folded.isEmpty && (plain.splitOn ";;").length > 1 then newlineOpt off
    modify fun st => { st with nesting := st.nesting + 1 }
    for _h : fi in folded do printF fi
    modify fun st => { st with nesting := st.nesting - 1 }
    write ")"
termination_by f => sizeOf f
decreasing_by
  have := Array.sizeOf_lt_of_mem ‹_ ∈ folded›
  simp_wf; omega

/-- The `end` of the innermost block. -/
def endF : PM Unit := do
  -- (`endOp` runs `opHook` for the `end`)
  let results := match ← labelBlock 0 with
    | some (some (_, r), _) => r
    | _ => 0
  let _ ← capture endOp
  handleEnd results

mutual
/-- The folded visit of one instruction (and its body). -/
def instrF : Instr → PM Unit
  | .block bt body => do
    opHook
    let a ← blockArity bt
    let txt ← capture (do blockStart; write "block"; let h ← blockType bt; labelComment h)
    pushFrame { kind := .block, arity := a, plain := txt, offset := (← get).curOff }
    modify fun st => { st with pendingHint := none }
    instrsF body; endF
  | .loop bt body => do
    opHook
    let a ← blockArity bt
    let txt ← capture (do blockStart; write "loop"; let h ← blockType bt; labelComment h)
    pushFrame { kind := .loop, arity := a, plain := txt, offset := (← get).curOff }
    modify fun st => { st with pendingHint := none }
    instrsF body; endF
  | .if_ bt th el => do
    opHook
    let explicitElse ← nextIfElse
    let a ← blockArity bt
    let txt ← capture (do blockStart; write "if"; let h ← blockType bt; labelComment h)
    pushIf a txt
    instrsF th
    if !el.isEmpty || explicitElse then
      opHook
      let _ ← capture (do blockMid; write "else")
      handleElse
      instrsF el
    endF
  | .tryTable bt cs body => do
    opHook
    let a ← blockArity bt
    let txt ← capture (do
      blockStart; write "try_table"; let h ← blockType bt
      modify fun st => { st with nesting := st.nesting - 2, labelIdx := st.labelIdx.pop }
      for c in cs do catchClause c
      modify fun st => { st with nesting := st.nesting + 2, labelIdx := st.labelIdx.push st.label }
      labelComment h)
    pushFrame { kind := .tryTable, arity := a, plain := txt, offset := (← get).curOff }
    modify fun st => { st with pendingHint := none }
    instrsF body; endF
  | i => do
    opHook
    let txt ← capture (plain i)
    let a ← opArity i txt
    let (p, r) := a.getD (0, 0)
    handlePlain txt p r

def instrsF : List Instr → PM Unit
  | [] => pure ()
  | i :: is => do instrF i; instrsF is
end

/-- Fold an instruction sequence under an outer frame of arity `arity`, then print it with
the current separator (`finalize`). -/
def foldedSeq (arity : Option (Nat × Nat)) (e : List Instr) : PM Unit := do
  let frames := (← get).frames
  let outer : Frame := { kind := .block, arity, plain := "", offset := (← get).curOff }
  modify fun st => { st with folding := true, pendingHint := none, frames := #[outer] }
  -- `opArity` reads the function frame's arity; `labelBlock` its depth
  instrsF e
  let top := (← get).frames[0]?
  modify fun st => { st with folding := false, frames }
  if let some f := top then
    for i in f.folded do printF i

/-- A constant expression, space separated (`print_const_expr`). -/
def constExpr (e : Expr) : PM Unit := do
  let sep := (← get).sep
  let nestingStart := (← get).nestingStart
  let label := (← get).label
  let labelIdx := (← get).labelIdx
  modify fun st => { st with sep := .noneThenSpace, nestingStart := st.nesting, label := 0, labelIdx := #[] }
  if (← read).cfg.fold && (← get).foldConst then foldedSeq (some (0, 0)) e else instrs e
  modify fun st => { st with sep, nestingStart, label, labelIdx }

/-- `print_const_expr_sugar`: `(op …)` for one instruction, `(KW op …)` otherwise (also for
none: `(offset )`, as wasmprinter, whose test `!reader.is_end_then_eof()` after one read holds
for an empty expression). -/
def constSugar (e : Expr) (kw : String) : PM Unit := do
  startGroup ""
  if e.length != 1 then write (kw ++ " ")
  -- one instruction is never folded (`print_const_expr(.., false)`)
  let fc := (← get).foldConst
  modify fun st => { st with foldConst := e.length > 1 }
  constExpr e
  modify fun st => { st with foldConst := fc }
  endGroup

/-! ## Module fields -/

def importDecl (im : Import) (counts : Nat × Nat × Nat × Nat × Nat) : PM Unit := do
  let env ← read
  let (fs, ts, ms, gs, tgs) := counts
  startGroup "import "
  strLit im.moduleName; write " "; strLit im.name; write " "
  match im.type with
  | .func t => do
    startGroup "func "; nameAt env.names.funcs "func" fs; write " "
    typeUse t.toNat (.locals fs)
  | .table t => tableType t (some ts)
  | .memory t => memoryType t (some ms)
  | .global t => globalType t (some gs)
  | .tag t => tagType t (some tgs)
  endGroup
  endGroup

def exportDecl (e : Export) : PM Unit := do
  let env ← read
  startGroup "export "; strLit e.name; write " "
  match e.index with
  | .func i => do startGroup "func "; idx env.names.funcs "func" i.toNat
  | .table i => do startGroup "table "; idx env.names.tables "table" i.toNat
  | .global i => do startGroup "global "; idx env.names.globals "global" i.toNat
  | .memory i => do startGroup "memory "; idx env.names.memories "memory" i.toNat
  | .tag i => do startGroup "tag "; write (toString i.toNat)
  endGroup
  endGroup

def funcDecl (f : Func) (fi k : Nat) : PM Unit := do
  let env ← read
  let body := env.code[k]?
  newlineOpt (body.map (·.start))
  startGroup "func "
  nameAt env.names.funcs "func" fi
  write " "
  typeUse f.type.toNat (.locals fi)
  let nparams := match env.types[f.type.toNat]? with
    | some ⟨_, _, .func ft⟩ => ft.params.length
    | _ => 0
  if env.cfg.skeleton then
    write " ..."; endGroup
  else
    if !f.locals.isEmpty then
      newlineOpt (body.bind (·.localsAt))
      namedLocals "local" (.locals fi) nparams f.locals
    let evs := (body.map (·.evs)).getD #[]
    let hints := ((env.branchHints.find? (·.1 == fi)).map (·.2)).getD []
    let bodyStart := (body.map (·.start)).getD 0
    modify fun st => { st with sep := .newline, nestingStart := st.nesting, label := 0, labelIdx := #[], func := fi, evs, evIdx := 0, hints, elses := Raw.explicitElses evs, ifIdx := 0, bodyStart, curOff := none }
    if env.cfg.fold then
      let a := match env.types[f.type.toNat]? with
        | some ⟨_, _, .func ft⟩ => some (ft.params.length, ft.results.length)
        | _ => none
      foldedSeq a f.body
    else instrs f.body
    modify fun st => { st with evs := #[], hints := [], elses := #[], curOff := none }
    endGroupAt ((body.map (·.endAt)).getD 0)

/-- Is every item a single `ref.func` (the function-index form of a segment)? -/
def funcItems (e : Elem) : Option (List Nat) :=
  if e.type == ⟨true, .abstract .func⟩ then
    e.init.mapM fun | [.refFunc f] => some f.toNat | _ => none
  else none

def elemDecl (e : Elem) (i : Nat) (form : Option Raw.ElemForm) (off : Option Nat) :
    PM Unit := do
  let env ← read
  newlineOpt off
  startGroup "elem "
  nameAt env.names.elems "elem" i
  match e.mode with
  | .passive => pure ()
  | .declarative => write " declare"
  | .active t off => do
    let explicit := match form with | some f => f.explicitTable | none => t.toNat != 0
    if explicit then
      write " "; startGroup "table "; idx env.names.tables "table" t.toNat; endGroup
    write " "; constSugar off "offset"
  write " "
  if env.cfg.skeleton then write "..."
  else
    let items := match form with
      | some f => if f.exprs then none else
          e.init.mapM fun (x : Expr) => match x with | [Instr.refFunc f] => some f.toNat | _ => none
      | none => funcItems e
    match items with
    | some fs => do write "func"; for f in fs do write " "; idx env.names.funcs "func" f
    | none => do
      refType e.type
      for x in e.init do write " "; constSugar x "item"
  endGroup

def dataDecl (d : Data) (i : Nat) (off : Option Nat) : PM Unit := do
  let env ← read
  newlineOpt off
  startGroup "data "
  nameAt env.names.datas "data" i
  write " "
  match d.mode with
  | .passive => pure ()
  | .active m off => do
    if m.toNat != 0 then
      startGroup "memory "; idx env.names.memories "memory" m.toNat; endGroup; write " "
    constSugar off "offset"; write " "
  if env.cfg.skeleton then write "..." else bytesP d.bytes
  endGroup

def isDefaultTable (t : Table) : Bool := Binaryen.Toolkit.Wat.defaultTableInit t

/-! ## Custom sections -/

def customDecl (b : ByteArray) (s : Raw.Section) (place : Option String) : PM Unit := do
  let env ← read
  match Raw.customName b s with
  | none => pure ()
  | some (nm, q) =>
    let data := b.extract q (s.payload + s.size)
    if nm == "name" || nm == "metadata.code.branch_hint" then pure ()
    else if nm == "producers" then
      match Raw.readProducersAt b q with
      | some fields => do
        newlineAt s.payload; startGroup "@producers"
        for (f, vs) in fields do
          for (n, v, at_) in vs do
            newlineAt at_; startGroup f; write " "; strLit n; write " "; strLit v; endGroup
        endGroup
      | none => raw nm data env
    else raw nm data env
where
  raw (nm : String) (data : ByteArray) (env : Env) : PM Unit := do
    newlineAt s.payload; startGroup "@custom "; strLit nm
    if let some p := place then write s!" ({p})"
    write " "
    if env.cfg.skeleton then write "..." else bytesP data
    endGroup

/-! ## The module -/

/-- Print the module `m` decoded from `b` (its sections `secs`). -/
def moduleText (b : ByteArray) (secs : List Raw.Section) : PM Unit := do
  let env ← read
  let m := env.module
  startGroup "module"
  if let some n := env.names.module then write " "; writeNaming n
  let mut place : String := "before first"
  let mut tyIdx := 0
  let mut nfuncImports := 0
  for s in secs do
    let offs := (Raw.entryOffsets b s).getD []
    match s.id with
    | 0 => customDecl b s (some place)
    | 1 =>
      let recs := (Raw.recForms b s.payload).getD []
      let mut k := 0
      for rt in m.types do
        let off := offs[k]?
        newlineOpt off
        let explicitRec := recs.getD k false
        k := k + 1
        match rt.types with
        | [st] =>
          if explicitRec then
            startGroup "rec"; newlineOpt (off.map (· + 2)); typeDef st tyIdx; tyIdx := tyIdx + 1
            endGroup
          else typeDef st tyIdx; tyIdx := tyIdx + 1
        | sts => do
          startGroup "rec"
          for st in sts do newlineOpt (off.map (· + 2)); typeDef st tyIdx; tyIdx := tyIdx + 1
          endGroup
      if !m.types.isEmpty then place := "after type"
    | 2 =>
      let mut counts := (0, 0, 0, 0, 0)
      let mut k := 0
      for im in m.imports do
        newlineOpt offs[k]?; importDecl im counts; k := k + 1
        let (f, t, me, g, tg) := counts
        counts := match im.type with
          | .func _ => (f + 1, t, me, g, tg) | .table _ => (f, t + 1, me, g, tg)
          | .memory _ => (f, t, me + 1, g, tg) | .global _ => (f, t, me, g + 1, tg)
          | .tag _ => (f, t, me, g, tg + 1)
      nfuncImports := counts.1
      if !m.imports.isEmpty then place := "after import"
    | 3 => if !m.funcs.isEmpty then place := "after func"
    | 4 =>
      let nimp := (m.imports.filter fun im => match im.type with | .table _ => true | _ => false).length
      let inits := Raw.tableInits b s.payload
      let mut i := nimp
      let mut k := 0
      for t in m.tables do
        newlineOpt offs[k]?; tableType t.type (some i)
        let explicit := match inits with
          | some l => l.getD k false
          | none => !isDefaultTable t
        if explicit then write " "; constExpr t.init
        endGroup; i := i + 1; k := k + 1
      if !m.tables.isEmpty then place := "after table"
    | 5 =>
      let nimp := (m.imports.filter fun im => match im.type with | .memory _ => true | _ => false).length
      let mut i := nimp
      let mut k := 0
      for t in m.memories do
        newlineOpt offs[k]?; memoryType t (some i); endGroup; i := i + 1; k := k + 1
      if !m.memories.isEmpty then place := "after memory"
    | 13 =>
      let nimp := (m.imports.filter fun im => match im.type with | .tag _ => true | _ => false).length
      let mut i := nimp
      let mut k := 0
      for t in m.tags do
        newlineOpt offs[k]?; tagType t (some i); endGroup; i := i + 1; k := k + 1
      if !m.tags.isEmpty then place := "after tag"
    | 6 =>
      let nimp := (m.imports.filter fun im => match im.type with | .global _ => true | _ => false).length
      let mut i := nimp
      let mut k := 0
      for g in m.globals do
        newlineOpt offs[k]?; globalType g.type (some i); write " "; constExpr g.init; endGroup
        i := i + 1; k := k + 1
      if !m.globals.isEmpty then place := "after global"
    | 7 =>
      let mut k := 0
      for e in m.exports do newlineOpt offs[k]?; exportDecl e; k := k + 1
      if !m.exports.isEmpty then place := "after export"
    | 8 =>
      if let some f := m.start then
        newlineAt s.payload; startGroup "start "; idx env.names.funcs "func" f.toNat; endGroup
      place := "after start"
    | 9 =>
      let forms := (Raw.elemForms b s.payload).getD []
      let mut i := 0
      for e in m.elems do elemDecl e i forms[i]? offs[i]?; i := i + 1
      if !m.elems.isEmpty then place := "after elem"
    | 10 =>
      let nimp := (m.imports.filter fun im => match im.type with | .func _ => true | _ => false).length
      let code := ((Raw.codeInfo b s.payload).map List.toArray).getD #[]
      let mut i := nimp
      let mut k := 0
      for f in m.funcs do
        withReader (fun e => { e with code }) (funcDecl f i k); i := i + 1; k := k + 1
      if !m.funcs.isEmpty then place := "after code"
    | 11 =>
      let mut i := 0
      for d in m.data do dataDecl d i offs[i]?; i := i + 1
      if !m.data.isEmpty then place := "after data"
    | _ => pure ()
  -- close `module` (`end_group_at_pos` at the end of the module)
  endGroupAt b.size
  write "\n"

/-- Why printing failed. -/
inductive Error where
  | decode (msg : String)
  | sections
  deriving Repr, Inhabited

def Error.message : Error → String
  | .decode msg => msg
  | .sections => "malformed section structure"

/-- The text of the module binary `b` (no check). -/
def printText (cfg : Config) (b : ByteArray) : Except Error (Wasm.Module × String) := do
  let m ← (Binary.Core.Decode.decodeModule b).mapError Error.decode
  let secs ← match Raw.sections b with | some s => pure s | none => throw Error.sections
  let names := secs.foldl (fun acc s =>
    match Raw.customName b s with
    | some ("name", q) => Raw.readNames b q (s.payload + s.size)
    | _ => acc) ({} : Names)
  let branchHints := secs.foldl (fun acc s =>
    match Raw.customName b s with
    | some ("metadata.code.branch_hint", q) => (Raw.readBranchHintsAt b q).getD acc
    | _ => acc) []
  let funcTypes := (m.imports.filterMap fun im => match im.type with
    | .func t => some t.toNat | _ => none).toArray ++ (m.funcs.map (·.type.toNat)).toArray
  let tagTypes := (m.imports.filterMap fun im => match im.type with
    | .tag t => some t.toNat | _ => none).toArray ++ (m.tags.map (·.toNat)).toArray
  let env : Env := { cfg, names, module := m, types := (m.types.flatMap (·.types)).toArray, branchHints, funcTypes, tagTypes }
  let ((), st) := (moduleText b secs).run env |>.run {}
  pure (m, st.out)

/-- The result of `printModule`: the text and whether the check passed. -/
structure Printed where
  module : Wasm.Module
  text : String
  certified : Bool

/-- The module a text reads back to: silmaril-lean's certified lexer, then its source-directed
elaborator (`Wat.Source.module?`, as `Parse.textModule`), else its canonical reader
(`Wat.parseCanonical?`, which reads some forms the source elaborator does not, such as an
empty `(offset )` with function indices). Both are sound for the text grammar. -/
def readBack (s : String) : Option Wasm.Module :=
  match Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 s with
  | none => none
  | some x =>
    match Binaryen.Toolkit.Wat.Source.module? x with
    | some m => some m.1
    | none => Binaryen.Toolkit.Wat.parseCanonical? x

/-- The check: the text, annotations removed, reads back (certified elaborator) to a module
whose encoding equals that of `m`. -/
def check (m : Wasm.Module) (t : String) : Bool :=
  match readBack (stripTrivia t) with
  | some m' =>
    match Binaryen.Exe.encodeModule? m, Binaryen.Exe.encodeModule? m' with
    | .ok a, .ok a' => a == a'
    | _, _ => false
  | none => false

/-- `wasm-tools print`: the text, checked. -/
def printModule (cfg : Config) (b : ByteArray) : Except Error Printed := do
  let (m, t) ← printText cfg b
  pure ⟨m, t, if cfg.skeleton then false else check m t⟩

end Silmaril.Wasm.Tools.Print
