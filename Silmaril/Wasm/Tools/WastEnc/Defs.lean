module

public import Silmaril.Wasm.Tools.WastEnc.Ops.Defs
public import Silmaril.Wasm.Tools.Wast.Json.Defs
public import Silmaril.Wasm.Tools.Annot.Defs
public import Std.Data.HashMap

/-!
# The `wast` crate's text-to-binary encoder for core modules

`encodeModule x` is the binary the `wast` crate (wasm-tools 1.262.0, `crates/wast/src/core`)
writes for the core text module `x` (`(module $id? field…)`, as an S-expression), transcribed
step by step:

* **parsing** (`parse*`) over the module's token stream, with the `wast` crate's grammar:
  `module.rs`, `types.rs`, `func.rs`, `table.rs`, `memory.rs`, `global.rs`, `tag.rs`,
  `import.rs`, `export.rs`, and the instruction parser of `expr.rs` (`ExpressionParser`:
  folded and flat instructions, `(if … (then …) (else …))`). Every instruction of the
  crate's `instructions!` table is read through the generated table `ops`
  (`Silmaril.Wasm.Tools.WastEnc.Ops`), its payload by its kind;
* **de-inlining** (`resolve/deinline_import_export.rs`): inline exports become `export` fields
  before the item, inline imports become `import` fields, `(memory (data …))` and
  `(table T (elem …))` become a memory or table of the data's size and an active segment at 0;
  identifiers are filled with generated symbols (`gensym`, never named);
* the **import order** check (`import after …`);
* **type expansion** (`resolve/types.rs`): every type use without an index refers to the first
  function type with the same parameters and results among the `type` fields (not `rec`
  groups), else to a new type appended at the end of the type section; block types get one
  only when they have parameters or several results;
* **name resolution** (`resolve/names.rs`): index spaces in field order, locals (parameters
  first), labels (relative depth), struct field names, the inline/explicit type check;
* **encoding** (`binary.rs` and `wasm-encoder`): sections in the crate's order, the data count
  section exactly when a function body uses a data index, the `name` section
  (`find_names`: module, functions, locals, labels, types, tables, memories, globals, elements,
  data, fields, tags, parameters, tag parameters).

Not transcribed: annotations (`@custom`, `@producers`, `@dylink.0`, `@name`,
`@metadata.code.branch_hint`; the readers of this repository drop annotations before this
encoder sees the module), DWARF (`-g`), and the crate's error spans (errors are messages only).

This encoder is **not verified**: it is a tested transcription (`tools/wasm-tools/tests/wast`,
byte-for-byte against `wasm-tools json-from-wast`). The `wast` backend uses it only for text
modules outside the certified `parse` pipeline (`Silmaril.Wasm.Tools.Text.textToBinary`), so that
every module silmaril-lean's certified elaborator accepts is still encoded by the certified path
(`Silmaril.Wasm.Tools.Wast.parseText`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.WastEnc

open Silmaril.Formats.SExpEncoding (SExp Atom)

/-! ## Tokens -/

/-- A token of the text format, as the S-expression reader delivers it. -/
inductive Tok where
  | lp
  | rp
  | kw (s : String)
  | str (b : List UInt8)
  | id (s : String)
  deriving Inhabited, BEq, Repr

mutual
  /-- The tokens of one S-expression item. -/
  def flatItem : SExp → Array Tok → Array Tok
    | .nil, acc => (acc.push .lp).push .rp
    | .atom (.sym s), acc => acc.push (.kw s)
    | .atom (.str b), acc => acc.push (.str b)
    | .atom (.id s), acc => acc.push (.id s)
    | .cons a d, acc => (flatRest d (flatItem a (acc.push .lp))).push .rp

  /-- The tokens of the rest of a list. -/
  def flatRest : SExp → Array Tok → Array Tok
    | .nil, acc => acc
    | .cons a d, acc => flatRest d (flatItem a acc)
    | x, acc => flatItem x acc
end

/-! ## Little-endian base 128 -/

/-- Unsigned LEB128. -/
def uleb (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: uleb (n / 128)
termination_by n
decreasing_by omega

/-- Signed LEB128. -/
def slebFuel : Nat → Int → List UInt8
  | 0, _ => []
  | f + 1, i =>
    let b := i % 128
    let rest := (i - b) / 128
    let bt := b.toNat
    if (rest == 0 && bt < 64) || (rest == -1 && bt ≥ 64) then [bt.toUInt8]
    else (bt + 128).toUInt8 :: slebFuel f rest

def sleb (i : Int) : List UInt8 := slebFuel 20 i

/-- A vector: its length, then the items. -/
def vecB (xs : List (List UInt8)) : List UInt8 := uleb xs.length ++ xs.flatten

/-- A name: its UTF-8 length, then the bytes. -/
def nameB (s : String) : List UInt8 := uleb s.utf8ByteSize ++ s.toUTF8.toList

def leBytes (n width : Nat) : List UInt8 :=
  (List.range width).map fun i => ((n / 2 ^ (8 * i)) % 256).toUInt8

/-! ## Syntax -/

/-- An index: a number or an identifier (`$x`, without the `$`). -/
inductive Idx where
  | num (n : Nat)
  | id (s : String)
  deriving Inhabited, BEq, Repr

/-- A heap type (`HeapType`): abstract (shared or not, by its binary code), concrete, exact. -/
inductive Heap where
  | abs (shared : Bool) (code : UInt8)
  | conc (i : Idx)
  | exact (i : Idx)
  deriving Inhabited, BEq, Repr

structure RefT where
  nullable : Bool
  heap : Heap
  deriving Inhabited, BEq, Repr

inductive ValT where
  | num (code : UInt8)
  | ref (r : RefT)
  deriving Inhabited, BEq, Repr

inductive StorT where
  | i8
  | i16
  | val (v : ValT)
  deriving Inhabited, BEq, Repr

structure FuncT where
  params : List (Option String × ValT) := []
  results : List ValT := []
  deriving Inhabited, Repr

def FuncT.key (f : FuncT) : List ValT × List ValT := (f.params.map (·.2), f.results)

structure FieldT where
  id : Option String
  mutable : Bool
  ty : StorT
  deriving Inhabited, Repr

inductive Comp where
  | func (f : FuncT)
  | struct (fs : List FieldT)
  | array (mutable : Bool) (t : StorT)
  | cont (i : Idx)
  deriving Inhabited, Repr

structure TypeDef where
  kind : Comp
  shared : Bool := false
  parents : List Idx := []
  descriptor : Option Idx := none
  describes : Option Idx := none
  final : Option Bool := none
  deriving Inhabited, Repr

structure TyDecl where
  id : Option String
  def_ : TypeDef
  deriving Inhabited, Repr

structure TypeUse where
  index : Option Idx := none
  inline : Option FuncT := none
  deriving Inhabited, Repr

structure Limits where
  is64 : Bool := false
  min : Nat
  max : Option Nat := none
  deriving Inhabited, Repr

structure TableT where
  limits : Limits
  elem : RefT
  shared : Bool := false
  deriving Inhabited, Repr

structure MemT where
  limits : Limits
  shared : Bool := false
  pageLog : Option Nat := none
  deriving Inhabited, Repr

structure GlobalT where
  ty : ValT
  mutable : Bool := false
  shared : Bool := false
  deriving Inhabited, Repr

structure MemArg where
  align : Nat
  offset : Nat
  mem : Idx
  deriving Inhabited, Repr

structure BlockT where
  label : Option String := none
  ty : TypeUse := {}
  deriving Inhabited, Repr

inductive Catch where
  | one (tag label : Idx)
  | oneRef (tag label : Idx)
  | all (label : Idx)
  | allRef (label : Idx)
  deriving Inhabited, Repr

inductive Handle where
  | onLabel (tag label : Idx)
  | onSwitch (tag : Idx)
  deriving Inhabited, Repr

/-- A parsed instruction payload. -/
inductive Imm where
  | none
  | idx (i : Idx)
  | ord (o : UInt8) (i : Idx)
  | ordStruct (o : UInt8) (t f : Idx)
  | memarg (m : MemArg)
  | lsLane (m : MemArg) (lane : Nat)
  | lane (n : Nat)
  | struct (t f : Idx)
  | block (b : BlockT)
  | endLabel (l : Option String)
  | callIndirect (table : Idx) (tu : TypeUse)
  | bytes (bs : List UInt8)
  | int (v : Int)
  | tryTable (b : BlockT) (cs : List Catch)
  | two (a b : Idx)
  | select (tys : Option (List ValT))
  | resume (t : Idx) (tag : Option Idx) (hs : List Handle)
  | ref (r : RefT)
  | heap (h : Heap)
  | brTable (ls : List Idx) (d : Idx)
  | brOnCast (l : Idx) (src dst : RefT)
  | arrayNewFixed (t : Idx) (n : Nat)
  deriving Inhabited, Repr

structure Instr where
  op : OpRow
  imm : Imm
  deriving Inhabited, Repr

inductive Sig where
  | func (tu : TypeUse)
  | funcExact (tu : TypeUse)
  | table (t : TableT)
  | memory (m : MemT)
  | global (g : GlobalT)
  | tag (tu : TypeUse)
  deriving Inhabited, Repr

structure ItemSig where
  id : Option String
  kind : Sig
  deriving Inhabited, Repr

inductive Imports where
  | single (module name : String) (sig : ItemSig)
  | group1 (module : String) (items : List (String × ItemSig))
  | group2 (module : String) (sig : ItemSig) (names : List String)
  deriving Inhabited, Repr

/-- The signatures an import field defines, in index order (`item_sigs`). -/
def Imports.sigs : Imports → List ItemSig
  | .single _ _ s => [s]
  | .group1 _ items => items.map (·.2)
  | .group2 _ s ns => ns.map fun _ => s

inductive ElemMode where
  | passive
  | declared
  | active (table : Option Idx) (offset : Array Instr)
  deriving Inhabited, Repr

inductive ElemPayload where
  | indices (fs : List Idx)
  | exprs (ty : RefT) (es : List (Array Instr))
  deriving Inhabited, Repr

/-- A module field after de-inlining (`ModuleField`). -/
inductive Field where
  | type (t : TyDecl)
  | recGroup (ts : List TyDecl)
  | import (im : Imports)
  | func (id : Option String) (tu : TypeUse) (locals : List (Option String × ValT))
      (body : Array Instr)
  | table (id : Option String) (t : TableT) (init : Option (Array Instr))
  | memory (id : Option String) (m : MemT)
  | global (id : Option String) (g : GlobalT) (init : Array Instr)
  | tag (id : Option String) (tu : TypeUse)
  | export (name : String) (space : Space) (item : Idx)
  | start (i : Idx)
  | elem (id : Option String) (mode : ElemMode) (payload : ElemPayload)
  | data (id : Option String) (mem : Option (Idx × Array Instr)) (bytes : List UInt8)
  deriving Inhabited, Repr

/-! ## The parser -/

structure PState where
  toks : Array Tok
  pos : Nat := 0
  gensym : Nat := 0

abbrev P := StateT PState (Except String)

def peekAt (k : Nat) : P (Option Tok) := do
  let s ← get
  pure s.toks[s.pos + k]?

def peek : P (Option Tok) := peekAt 0

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def next : P Tok := do
  match ← peek with
  | some t => advance; pure t
  | none => throw "unexpected end of input"

def fail {α : Type} (msg : String) : P α := throw msg

/-- Is the parser at the end of the current list (`Parser::is_empty`)? -/
def atEnd : P Bool := do
  match ← peek with
  | none | some .rp => pure true
  | _ => pure false

def isKw (s : String) : Option Tok → Bool
  | some (.kw k) => k == s
  | _ => false

def peekKw (s : String) : P Bool := do pure (isKw s (← peek))

/-- `peek2::<kw::s>`: a `(` then the keyword `s`. -/
def peek2Kw (s : String) : P Bool := do
  match ← peek with
  | some .lp => pure (isKw s (← peekAt 1))
  | _ => pure false

def expectLp : P Unit := do
  match ← next with
  | .lp => pure ()
  | _ => fail "expected `(`"

def expectRp : P Unit := do
  match ← next with
  | .rp => pure ()
  | _ => fail "expected `)`"

def kwTok (s : String) : P Unit := do
  match ← next with
  | .kw k => if k == s then pure () else fail s!"expected keyword `{s}`"
  | _ => fail s!"expected keyword `{s}`"

def parens {α : Type} (p : P α) : P α := do
  expectLp
  let a ← p
  expectRp
  pure a

def freshId : P String := do
  let s ← get
  set { s with gensym := s.gensym + 1 }
  pure ("\x00gensym" ++ toString s.gensym)

def isGensym (s : String) : Bool := s.startsWith "\x00"

/-- Digits with single `_` separators between digits (`num`/`hexnum` of the text format). -/
def digitsSep (isD : Char → Bool) : List Char → Bool
  | [] => false
  | c :: cs => isD c && go cs
where
  go : List Char → Bool
    | [] => true
    | '_' :: c :: cs => isD c && go cs
    | c :: cs => isD c && go cs

def dropSign : List Char → List Char
  | '+' :: r | '-' :: r => r
  | r => r

/-- An integer token (`Token::Integer`): an optional sign, then `num` or `0x hexnum`. -/
def isIntTok (s : String) : Bool :=
  match dropSign s.toList with
  | '0' :: 'x' :: r => digitsSep Char.isHexDigit r
  | r => digitsSep Char.isDigit r

/-- A float token (`Token::Float`), or an integer token. -/
def isFloatTok (s : String) : Bool :=
  isIntTok s ||
  let cs := dropSign s.toList
  let splitAt (c : Char) (l : List Char) : List Char × Option (List Char) :=
    match l.findIdx? (· == c) with
    | some i => (l.take i, some (l.drop (i + 1)))
    | none => (l, none)
  let expOk (e : List Char) : Bool := digitsSep Char.isDigit (dropSign e)
  let mantOk (isD : Char → Bool) (m : List Char) : Bool :=
    match splitAt '.' m with
    | (a, none) => digitsSep isD a
    | (a, some []) => digitsSep isD a
    | (a, some f) => digitsSep isD a && digitsSep isD f
  match cs with
  | ['i', 'n', 'f'] | ['n', 'a', 'n'] => true
  | 'n' :: 'a' :: 'n' :: ':' :: '0' :: 'x' :: r => digitsSep Char.isHexDigit r
  | '0' :: 'x' :: r =>
    match splitAt 'p' (r.map fun c => if c == 'P' then 'p' else c) with
    | (m, none) => mantOk Char.isHexDigit m
    | (m, some e) => mantOk Char.isHexDigit m && expOk e
  | r =>
    match splitAt 'e' (r.map fun c => if c == 'E' then 'e' else c) with
    | (m, none) => mantOk Char.isDigit m
    | (m, some e) => mantOk Char.isDigit m && expOk e

def peekIdx : P Bool := do
  match ← peek with
  | some (.id _) => pure true
  | some (.kw k) => pure (isIntTok k)
  | _ => pure false

def peekInt : P Bool := do
  match ← peek with
  | some (.kw k) => pure (isIntTok k)
  | _ => pure false

def natTok (bits : Nat) (what : String) : P Nat := do
  match ← next with
  | .kw k =>
    if k.startsWith "-" then fail "unexpected token"
    match Silmaril.Wasm.Tools.Wast.natLit? bits k with
    | some n => pure n
    | none => fail s!"invalid {what}: constant out of range"
  | _ => fail s!"expected a {what}"

def u32Tok : P Nat := natTok 32 "u32"
def u64Tok : P Nat := natTok 64 "u64"

def parseIdx : P Idx := do
  match ← peek with
  | some (.id s) => advance; pure (.id s)
  | some (.kw k) =>
    if isIntTok k then pure (.num (← u32Tok)) else fail "unexpected token, expected an index or an identifier"
  | _ => fail "unexpected token, expected an index or an identifier"

def optIdx : P (Option Idx) := do
  if ← peekIdx then pure (some (← parseIdx)) else pure none

def optId : P (Option String) := do
  match ← peek with
  | some (.id s) => advance; pure (some s)
  | _ => pure none

def strTok : P (List UInt8) := do
  match ← next with
  | .str b => pure b
  | _ => fail "expected a string"

def strName : P String := do
  let b ← strTok
  match String.fromUTF8? ⟨b.toArray⟩ with
  | some s => pure s
  | none => fail "malformed UTF-8 encoding"

/-! ### Types -/

def absHeap? : String → Option UInt8
  | "func" => some 0x70 | "extern" => some 0x6F | "any" => some 0x6E | "none" => some 0x71
  | "noextern" => some 0x72 | "nofunc" => some 0x73 | "eq" => some 0x6D
  | "struct" => some 0x6B | "array" => some 0x6A | "i31" => some 0x6C | "exn" => some 0x69
  | "noexn" => some 0x74 | "cont" => some 0x68 | "nocont" => some 0x75
  | _ => none

def refShort? : String → Option RefT
  | "funcref" => some ⟨true, .abs false 0x70⟩ | "externref" => some ⟨true, .abs false 0x6F⟩
  | "exnref" => some ⟨true, .abs false 0x69⟩ | "contref" => some ⟨true, .abs false 0x68⟩
  | "anyref" => some ⟨true, .abs false 0x6E⟩ | "eqref" => some ⟨true, .abs false 0x6D⟩
  | "structref" => some ⟨true, .abs false 0x6B⟩ | "arrayref" => some ⟨true, .abs false 0x6A⟩
  | "i31ref" => some ⟨true, .abs false 0x6C⟩ | "nullfuncref" => some ⟨true, .abs false 0x73⟩
  | "nullexternref" => some ⟨true, .abs false 0x72⟩ | "nullexnref" => some ⟨true, .abs false 0x74⟩
  | "nullcontref" => some ⟨true, .abs false 0x75⟩ | "nullref" => some ⟨true, .abs false 0x71⟩
  | _ => none

def numVal? : String → Option UInt8
  | "i32" => some 0x7F | "i64" => some 0x7E | "f32" => some 0x7D | "f64" => some 0x7C
  | "v128" => some 0x7B | _ => none

/-- `type_parse_error` of `types.rs`. -/
def typeParseError (withVal : Bool) : String :=
  let vals := if withVal then ["i32", "i64", "f32", "f64", "v128"] else []
  let refs := ["funcref", "externref", "exnref", "contref", "anyref", "eqref", "structref",
    "arrayref", "i31ref", "nullfuncref", "nullexternref", "nullexnref", "nullcontref", "nullref"]
  "unexpected token, expected one of: " ++
    String.join ((vals ++ refs).map fun n => "`" ++ n ++ "`, ") ++ "lparen"

def parseHeap : P Heap := do
  if ← peekIdx then return .conc (← parseIdx)
  match ← peek with
  | some .lp =>
    parens do
      if ← peekKw "exact" then advance; pure (.exact (← parseIdx))
      else
        kwTok "shared"
        match ← next with
        | .kw k => match absHeap? k with
          | some c => pure (.abs true c)
          | none => fail "unexpected token, expected a heap type"
        | _ => fail "unexpected token, expected a heap type"
  | some (.kw k) => match absHeap? k with
    | some c => advance; pure (.abs false c)
    | none => fail "unexpected token, expected a heap type"
  | _ => fail "unexpected token, expected a heap type"

def parseRefType : P RefT := do
  match ← peek with
  | some (.kw k) =>
    match refShort? k with
    | some r => advance; pure r
    | none => fail (typeParseError false)
  | some .lp =>
    parens do
      if ← peekKw "ref" then
        advance
        let nullable ← if ← peekKw "null" then (do advance; pure true) else pure false
        pure ⟨nullable, ← parseHeap⟩
      else
        kwTok "shared"
        match ← next with
        | .kw k => match refShort? k with
          | some ⟨n, .abs _ c⟩ => pure ⟨n, .abs true c⟩
          | _ => fail (typeParseError false)
        | _ => fail (typeParseError false)
  | _ => fail (typeParseError false)

def peekRefType : P Bool := do
  match ← peek with
  | some (.kw k) => pure (refShort? k).isSome
  | some .lp => pure (isKw "ref" (← peekAt 1) || isKw "shared" (← peekAt 1))
  | _ => pure false

def peekValType : P Bool := do
  match ← peek with
  | some (.kw k) => pure ((numVal? k).isSome || (refShort? k).isSome)
  | some .lp => pure (isKw "ref" (← peekAt 1) || isKw "shared" (← peekAt 1))
  | _ => pure false

def parseValType : P ValT := do
  match ← peek with
  | some (.kw k) =>
    match numVal? k with
    | some c => advance; pure (.num c)
    | none => if (refShort? k).isSome then pure (.ref (← parseRefType)) else fail (typeParseError true)
  | some .lp => pure (.ref (← parseRefType))
  | _ => fail (typeParseError true)

def parseStorage : P StorT := do
  if ← peekKw "i8" then advance; return .i8
  if ← peekKw "i16" then advance; return .i16
  pure (.val (← parseValType))

/-- `FunctionType::finish_parse`. -/
def parseFuncT (allowNames : Bool) : P FuncT := do
  let mut params : Array (Option String × ValT) := #[]
  let mut results : Array ValT := #[]
  while (← peek2Kw "param") || (← peek2Kw "result") do
    expectLp
    if ← peekKw "param" then
      advance
      if !results.isEmpty then
        fail "result before parameter (or unexpected token): cannot list params after results"
      if !(← atEnd) then
        let id ← if allowNames then optId else pure none
        params := params.push (id, ← parseValType)
        if id.isNone then
          while !(← atEnd) do params := params.push (none, ← parseValType)
    else
      kwTok "result"
      while !(← atEnd) do results := results.push (← parseValType)
    expectRp
  pure ⟨params.toList, results.toList⟩

def parseTypeUse (allowNames : Bool) : P TypeUse := do
  let index ← if ← peek2Kw "type" then (do
      let i ← parens (do kwTok "type"; parseIdx)
      pure (some i)) else pure none
  let inline ← if (← peek2Kw "param") || (← peek2Kw "result") then
      (do pure (some (← parseFuncT allowNames))) else pure none
  pure ⟨index, inline⟩

def parseLimits : P Limits := do
  let is64 ← if ← peekKw "i32" then (do advance; pure false)
    else if ← peekKw "i64" then (do advance; pure true) else pure false
  let min ← u64Tok
  let max ← if ← peekInt then (do pure (some (← u64Tok))) else pure none
  pure ⟨is64, min, max⟩

def parseTableT : P TableT := do
  let shared ← if ← peekKw "shared" then (do advance; pure true) else pure false
  let limits ← parseLimits
  pure ⟨limits, ← parseRefType, shared⟩

def log2? (n : Nat) : Option Nat :=
  (List.range 64).find? fun k => 2 ^ k == n

def parsePageSize : P (Option Nat) := do
  if ← peek2Kw "pagesize" then
    parens do
      kwTok "pagesize"
      let n ← u32Tok
      match log2? n with
      | some k => pure (some k)
      | none => fail s!"invalid custom page size: {n}"
  else pure none

def parseMemT : P MemT := do
  let limits ← parseLimits
  let shared ← if ← peekKw "shared" then (do advance; pure true) else pure false
  pure ⟨limits, shared, ← parsePageSize⟩

def parseGlobalT : P GlobalT := do
  if (← peek2Kw "shared") || (← peek2Kw "mut") then
    parens do
      let shared ← if ← peekKw "shared" then (do advance; pure true) else pure false
      let mutable ← if ← peekKw "mut" then (do advance; pure true) else pure false
      pure ⟨← parseValType, mutable, shared⟩
  else pure ⟨← parseValType, false, false⟩

def parseFieldT (id : Option String) : P FieldT := do
  if ← peek2Kw "mut" then
    let t ← parens (do kwTok "mut"; parseStorage)
    pure ⟨id, true, t⟩
  else pure ⟨id, false, ← parseStorage⟩

def parseStructT : P (List FieldT) := do
  let mut fs : Array FieldT := #[]
  while !(← atEnd) do
    expectLp
    kwTok "field"
    let id ← optId
    if id.isSome then fs := fs.push (← parseFieldT id)
    else
      while !(← atEnd) do fs := fs.push (← parseFieldT none)
    expectRp
  pure fs.toList

def parseComp : P Comp := do
  match ← next with
  | .kw "func" => pure (.func (← parseFuncT true))
  | .kw "struct" => pure (.struct (← parseStructT))
  | .kw "array" =>
    let f ← parseFieldT none
    pure (.array f.mutable f.ty)
  | .kw "cont" => pure (.cont (← parseIdx))
  | _ => fail "unexpected token, expected one of: `func`, `struct`, `array`, `cont`"

/-- `parse_shared_and_kind` of `TypeDef::parse`. -/
def parseSharedKind : P (Bool × Option Idx × Option Idx × Comp) := do
  let body (shared : Bool) : P (Bool × Option Idx × Option Idx × Comp) := do
    let describes ← if ← peekKw "describes" then (do
        advance
        let i ← parseIdx
        expectRp; expectLp
        pure (some i)) else pure none
    let descriptor ← if ← peekKw "descriptor" then (do
        advance
        let i ← parseIdx
        expectRp; expectLp
        pure (some i)) else pure none
    pure (shared, descriptor, describes, ← parseComp)
  if ← peekKw "shared" then
    advance
    parens (body true)
  else body false

def parseTypeDef : P TypeDef := do
  if ← peekKw "sub" then
    advance
    let final ← if ← peekKw "final" then (do advance; pure true) else pure false
    let mut parents : Array Idx := #[]
    while ← peekIdx do parents := parents.push (← parseIdx)
    let (shared, descriptor, describes, kind) ← parens parseSharedKind
    pure { kind, shared, parents := parents.toList, descriptor, describes, final := some final }
  else
    let (shared, descriptor, describes, kind) ← parseSharedKind
    pure { kind, shared, descriptor, describes }

/-- `(type $id? (def))` after `type`. -/
def parseTypeBody : P TyDecl := do
  let id ← optId
  pure ⟨id, ← parens parseTypeDef⟩

/-! ### Instructions -/

/-- The instruction table by text name. -/
def opMap : Std.HashMap String OpRow :=
  ops.foldl (fun m r => if m.contains r.name then m else m.insert r.name r) {}

def opNamed (s : String) : OpRow := (opMap.get? s).getD ⟨s, [], .none⟩

def parseOrdering : P UInt8 := do
  if ← peekKw "seqcst" then advance; return 0
  if ← peekKw "acqrel" then advance; return 1
  fail "expected a memory ordering: `seqcst` or `acqrel`"

/-- `MemArg::parse_field`: `name=N`. -/
def memField (name : String) : P (Option Nat) := do
  match ← peek with
  | some (.kw k) =>
    if k.startsWith (name ++ "=") then
      let num := (k.drop (name.length + 1)).toString
      if !isIntTok num || num.startsWith "-" || num.startsWith "+" then
        fail "expected u64 integer constant"
      match Silmaril.Wasm.Tools.Wast.natLit? 64 num with
      | some n => advance; pure (some n)
      | none => fail "u64 constant out of range"
    else pure none
  | _ => pure none

def parseMemArg (dflt : Nat) : P MemArg := do
  let mem ← (·.getD (.num 0)) <$> optIdx
  let offset ← (·.getD 0) <$> memField "offset"
  let align ← match ← memField "align" with
    | some n => if (log2? n).isNone then fail "alignment must be a power of two" else pure n
    | none => pure dflt
  pure ⟨align, offset, mem⟩

def laneTok : P Nat := do
  match ← next with
  | .kw k =>
    if k.startsWith "-" || k.startsWith "+" then fail "unexpected token"
    match Silmaril.Wasm.Tools.Wast.natLit? 8 k with
    | some n => pure n
    | none => fail "malformed lane index"
  | _ => fail "expected a lane index"

def intTok (bits : Nat) : P Int := do
  match ← next with
  | .kw k =>
    if !isIntTok k then fail s!"expected a i{bits}"
    match Silmaril.Wasm.Tools.Wast.intLit? bits k with
    | some b => pure b.toInt
    | none => fail s!"invalid i{bits} number: constant out of range"
  | _ => fail s!"expected a i{bits}"

def floatTok (t : Silmaril.Wasm.FloatType) : P Nat := do
  match ← next with
  | .kw k =>
    if !isFloatTok k then fail "expected a float"
    match Silmaril.Wasm.Tools.Wast.floatLitFast? t k with
    | some b => pure b.toNat
    | none => fail "invalid float value: constant out of range"
  | _ => fail "expected a float"

def parseBlockT : P BlockT := do
  let label ← optId
  pure ⟨label, ← parseTypeUse false⟩

def parseV128 : P (List UInt8) := do
  let lanes (n bits : Nat) : P (List UInt8) := do
    let mut out : List UInt8 := []
    for _ in [0:n] do
      let v ← intTok bits
      out := out ++ leBytes (v % (2 ^ bits : Nat)).toNat (bits / 8)
    pure out
  let flanes (n : Nat) (t : Silmaril.Wasm.FloatType) (w : Nat) : P (List UInt8) := do
    let mut out : List UInt8 := []
    for _ in [0:n] do out := out ++ leBytes (← floatTok t) w
    pure out
  match ← next with
  | .kw "i8x16" => lanes 16 8
  | .kw "i16x8" => lanes 8 16
  | .kw "i32x4" => lanes 4 32
  | .kw "i64x2" => lanes 2 64
  | .kw "f32x4" => flanes 4 .f32 4
  | .kw "f64x2" => flanes 2 .f64 8
  | _ => fail "unexpected token, expected a v128 shape"

def parseHandles : P (List Handle) := do
  let mut hs : Array Handle := #[]
  while ← peek2Kw "on" do
    expectLp; advance
    let tag ← parseIdx
    if ← peekKw "switch" then advance; hs := hs.push (.onSwitch tag)
    else hs := hs.push (.onLabel tag (← parseIdx))
    expectRp
  pure hs.toList

def parseCatches : P (List Catch) := do
  let mut cs : Array Catch := #[]
  while (← peek2Kw "catch") || (← peek2Kw "catch_ref") || (← peek2Kw "catch_all") ||
      (← peek2Kw "catch_all_ref") do
    expectLp
    match ← next with
    | .kw "catch_ref" => let t ← parseIdx; cs := cs.push (.oneRef t (← parseIdx))
    | .kw "catch" => let t ← parseIdx; cs := cs.push (.one t (← parseIdx))
    | .kw "catch_all" => cs := cs.push (.all (← parseIdx))
    | _ => cs := cs.push (.allRef (← parseIdx))
    expectRp
  pure cs.toList

/-- `peek2::<Index>`: the token after the next is an index. -/
def peek2Idx : P Bool := do
  match ← peekAt 1 with
  | some (.id _) => pure true
  | some (.kw k) => pure (isIntTok k)
  | _ => pure false

def parseImm : ImmKind → P Imm
  | .none => pure .none
  | .idx _ => .idx <$> parseIdx
  | .ordIdx _ => do let o ← parseOrdering; pure (.ord o (← parseIdx))
  | .memarg a => .memarg <$> parseMemArg a
  | .lsLane a => do
    -- `LoadOrStoreLane::parse`: a memarg unless the next token is a lone lane index
    let hasMem ← do
      match ← peek with
      | some (.kw k) =>
        if isIntTok k then
          match ← peekAt 1 with
          | some (.kw k2) => pure (isIntTok k2 || k2.startsWith "offset=" || k2.startsWith "align=")
          | _ => pure false
        else pure true
      | _ => pure true
    let m ← if hasMem then parseMemArg a else pure ⟨a, 0, .num 0⟩
    pure (.lsLane m (← laneTok))
  | .lane => .lane <$> laneTok
  | .struct => do let t ← parseIdx; pure (.struct t (← parseIdx))
  | .ordStruct => do
    let o ← parseOrdering
    let t ← parseIdx
    pure (.ordStruct o t (← parseIdx))
  | .table | .memory => do pure (.idx ((← optIdx).getD (.num 0)))
  | .ordTable => do let o ← parseOrdering; pure (.ord o ((← optIdx).getD (.num 0)))
  | .block => .block <$> parseBlockT
  | .endLabel => .endLabel <$> optId
  | .callIndirect => do
    let t ← (·.getD (.num 0)) <$> optIdx
    pure (.callIndirect t (← parseTypeUse false))
  | .v128 => .bytes <$> parseV128
  | .tryTable => do let b ← parseBlockT; pure (.tryTable b (← parseCatches))
  | .tableInit | .memoryInit => do
    if ← peek2Idx then
      let a ← parseIdx
      pure (.two a (← parseIdx))
    else pure (.two (.num 0) (← parseIdx))
  | .tableCopy | .memoryCopy => do
    match ← optIdx with
    | some d => pure (.two d (← parseIdx))
    | none => pure (.two (.num 0) (.num 0))
  | .switch | .contBind | .arrayNewElem | .arrayNewData | .arrayCopy | .arrayInit _ => do
    let a ← parseIdx
    pure (.two a (← parseIdx))
  | .select => do
    let mut found := false
    let mut tys : Array ValT := #[]
    while ← peek2Kw "result" do
      found := true
      expectLp; advance
      while !(← atEnd) do tys := tys.push (← parseValType)
      expectRp
    pure (.select (if found then some tys.toList else none))
  | .resume => do let t ← parseIdx; pure (.resume t none (← parseHandles))
  | .resumeThrow => do
    let t ← parseIdx
    let g ← parseIdx
    pure (.resume t (some g) (← parseHandles))
  | .resumeThrowRef => do let t ← parseIdx; pure (.resume t none (← parseHandles))
  | .refTest | .refCast | .refCastDescEq => .ref <$> parseRefType
  | .shuffle => do
    let mut out : List UInt8 := []
    for _ in [0:16] do out := out ++ [(← laneTok).toUInt8]
    pure (.bytes out)
  | .i32 => .int <$> intTok 32
  | .i64 => .int <$> intTok 64
  | .f32 => do pure (.bytes (leBytes (← floatTok .f32) 4))
  | .f64 => do pure (.bytes (leBytes (← floatTok .f64) 8))
  | .heap => .heap <$> parseHeap
  | .brTable => do
    let mut ls : Array Idx := #[← parseIdx]
    while ← peekIdx do ls := ls.push (← parseIdx)
    pure (.brTable ls.pop.toList ls.back!)
  | .brOnCast | .brOnCastFail | .brOnCastDescEq | .brOnCastDescEqFail => do
    let l ← parseIdx
    let a ← parseRefType
    pure (.brOnCast l a (← parseRefType))
  | .arrayNewFixed => do let t ← parseIdx; pure (.arrayNewFixed t (← u32Tok))
  | .arrayFill => .idx <$> parseIdx

def parseInstr : P Instr := do
  match ← next with
  | .kw k =>
    match opMap.get? k with
    | some r => pure ⟨r, ← parseImm r.kind⟩
    | none => fail "unknown operator or unexpected token"
  | _ => fail "expected an instruction"

def mkEnd : Instr := ⟨opNamed "end", .endLabel none⟩
def mkElse : Instr := ⟨opNamed "else", .endLabel none⟩

def Instr.isBlockLike (i : Instr) : Bool :=
  i.op.name == "block" || i.op.name == "loop" || i.op.name == "try_table"

/-- A level of `ExpressionParser`'s stack. -/
inductive Level where
  | endWith (i : Instr)
  | ifClause (i : Instr)
  | ifThen
  | ifElse
  | ifArm
  deriving Inhabited

/-- `ExpressionParser::parse`: an instruction sequence up to the end of the current list. -/
def parseExpr : P (Array Instr) := do
  let mut out : Array Instr := #[]
  let mut stack : Array Level := #[]
  while !(← atEnd) || !stack.isEmpty do
    match stack.back? with
    | some (.ifClause _) | some .ifThen | some .ifElse =>
      if !(← atEnd) && (← peek) != some .lp then fail "expected `(`"
    | _ => pure ()
    match ← peek with
    | some .lp =>
      advance
      -- `handle_if_lparen`
      let handled ← match stack.back? with
        | some (.ifClause i) =>
          if ← peekKw "then" then
            advance
            out := out.push i
            stack := stack.pop.push .ifThen |>.push .ifArm
            pure true
          else pure false
        | some .ifThen =>
          kwTok "else"
          out := out.push mkElse
          stack := stack.pop.push .ifElse |>.push .ifArm
          pure true
        | some .ifElse => fail "unexpected token: too many payloads inside of `(if)`"
        | _ => pure false
      if !handled then
        let i ← parseInstr
        if i.isBlockLike then
          out := out.push i
          stack := stack.push (.endWith mkEnd)
        else if i.op.name == "if" then stack := stack.push (.ifClause i)
        else stack := stack.push (.endWith i)
    | some .rp =>
      if stack.isEmpty then
        out := out.push (← parseInstr)
      else
        advance
        match stack.back? with
        | some (.endWith i) => out := out.push i
        | some .ifArm => pure ()
        | some (.ifClause _) => fail "previous `if` had no `then`"
        | some _ => out := out.push mkEnd
        | none => pure ()
        stack := stack.pop
    | _ => out := out.push (← parseInstr)
  pure out

/-- `parse_folded_instruction`: exactly one folded instruction. -/
def parseFolded : P (Array Instr) := do
  let mut out : Array Instr := #[]
  let mut stack : Array Instr := #[]
  let mut done := false
  while !done do
    match ← peek with
    | some .lp =>
      advance
      stack := stack.push (← parseInstr)
    | some .rp =>
      if stack.isEmpty then fail "expected to continue a folded instruction"
      advance
      out := out.push stack.back!
      stack := stack.pop
      if stack.isEmpty then done := true
    | _ => fail "expected to continue a folded instruction"
  pure out

/-- `parse_expr_or_single_instr::<kw>`. -/
def parseExprOrSingle (k : String) : P (Array Instr) := do
  if ← peek2Kw k then parens (do kwTok k; parseExpr) else parseFolded

def constOne (is64 : Bool) : Array Instr :=
  if is64 then #[⟨opNamed "i64.const", .int 0⟩] else #[⟨opNamed "i32.const", .int 0⟩]

/-! ### Module fields -/

/-- `InlineExport`: `(export "n")*`. -/
def parseInlineExports : P (List String) := do
  let mut ns : Array String := #[]
  while (← peek2Kw "export") && (match ← peekAt 2 with | some (.str _) => true | _ => false) &&
      ((← peekAt 3) == some .rp) do
    expectLp; advance
    ns := ns.push (← strName)
    expectRp
  pure ns.toList

/-- `InlineImport`: `(import "m" "n")`. -/
def parseInlineImport : P (Option (String × String)) := do
  if ← peek2Kw "import" then
    parens do
      kwTok "import"
      let m ← strName
      pure (some (m, ← strName))
  else pure none

def exportsOf (ns : List String) (s : Space) (id : String) : List Field :=
  ns.map fun n => .export n s (.id id)

/-- Fill an identifier (`gensym::fill`) when exports or an inline segment need one. -/
def fillId (id : Option String) (need : Bool) : P (Option String) := do
  match id with
  | some i => pure (some i)
  | none => if need then pure (some (← freshId)) else pure none

def parseItemSig : P ItemSig := do
  match ← next with
  | .kw "func" =>
    let id ← optId
    if ← peek2Kw "exact" then
      let tu ← parens (do kwTok "exact"; parseTypeUse true)
      pure ⟨id, .funcExact tu⟩
    else pure ⟨id, .func (← parseTypeUse true)⟩
  | .kw "table" => let id ← optId; pure ⟨id, .table (← parseTableT)⟩
  | .kw "memory" => let id ← optId; pure ⟨id, .memory (← parseMemT)⟩
  | .kw "global" => let id ← optId; pure ⟨id, .global (← parseGlobalT)⟩
  | .kw "tag" => let id ← optId; pure ⟨id, .tag (← parseTypeUse true)⟩
  | _ => fail "unexpected token, expected one of: `func`, `table`, `memory`, `global`, `tag`"

def parseImport : P Imports := do
  let m ← strName
  let empty ← atEnd
  if empty || (← peek) == some .lp then
    -- compact imports
    let mut enc : Nat := if empty then 1 else 0
    let mut items : Array (String × Option ItemSig) := #[]
    while ← peek2Kw "item" do
      expectLp; advance
      let n ← strName
      let sig ← if ← atEnd then pure none else (do pure (some (← parens parseItemSig)))
      expectRp
      match sig, enc with
      | some _, 0 => enc := 1
      | some _, 2 => fail "unexpected import type"
      | none, 0 => enc := 2
      | none, 1 => fail "unexpected `)`"
      | _, _ => pure ()
      items := items.push (n, sig)
    if enc == 1 then
      pure (.group1 m (items.toList.map fun (n, s) => (n, s.getD default)))
    else
      let sig ← parens parseItemSig
      if sig.id.isSome then fail "identifier not allowed"
      pure (.group2 m sig (items.toList.map (·.1)))
  else
    let n ← strName
    pure (.single m n (← parens parseItemSig))

def parseFunc : P (List Field) := do
  let id ← optId
  let exps ← parseInlineExports
  let id ← fillId id (!exps.isEmpty)
  let ex := exportsOf exps .func (id.getD "")
  match ← parseInlineImport with
  | some (m, n) =>
    let sig ← if ← peek2Kw "exact" then (do
        let tu ← parens (do kwTok "exact"; parseTypeUse true)
        pure (Sig.funcExact tu)) else (do pure (Sig.func (← parseTypeUse true)))
    pure (ex ++ [.import (.single m n ⟨id, sig⟩)])
  | none =>
    let tu ← parseTypeUse true
    let mut locals : Array (Option String × ValT) := #[]
    while ← peek2Kw "local" do
      expectLp; advance
      if !(← atEnd) then
        let lid ← optId
        locals := locals.push (lid, ← parseValType)
        if lid.isNone then
          while !(← atEnd) do locals := locals.push (none, ← parseValType)
      expectRp
    let body ← parseExpr
    pure (ex ++ [.func id tu locals.toList body])

/-- One data value (`DataVal`): a string or `(i8 …)` … `(v128 …)`. -/
def parseDataVal : P (List UInt8) := do
  match ← peek with
  | some (.str b) => advance; pure b
  | some .lp =>
    parens do
      let k ← match ← next with
        | .kw k => pure k
        | _ => fail "unexpected token"
      let mut out : List UInt8 := []
      while !(← atEnd) do
        match k with
        | "i8" => out := out ++ leBytes ((← intTok 8) % (256 : Nat)).toNat 1
        | "i16" => out := out ++ leBytes ((← intTok 16) % (65536 : Nat)).toNat 2
        | "i32" => out := out ++ leBytes ((← intTok 32) % (2 ^ 32 : Nat)).toNat 4
        | "i64" => out := out ++ leBytes ((← intTok 64) % (2 ^ 64 : Nat)).toNat 8
        | "f32" => out := out ++ leBytes (← floatTok .f32) 4
        | "f64" => out := out ++ leBytes (← floatTok .f64) 8
        | "v128" => out := out ++ (← parseV128)
        | _ => fail "unexpected token"
      pure out
  | _ => fail "expected a string"

def parseMemory : P (List Field) := do
  let id ← optId
  let exps ← parseInlineExports
  match ← parseInlineImport with
  | some (m, n) =>
    let id ← fillId id (!exps.isEmpty)
    let mt ← parseMemT
    pure (exportsOf exps .memory (id.getD "") ++ [.import (.single m n ⟨id, .memory mt⟩)])
  | none =>
    let inl ← do
      match ← peek with
      | some .lp => pure true
      | some (.kw k) =>
        if k == "i32" || k == "i64" then pure ((← peekAt 1) == some .lp) else pure false
      | _ => pure false
    if inl then
      let is64 ← if ← peekKw "i32" then (do advance; pure false)
        else if ← peekKw "i64" then (do advance; pure true) else pure false
      let pl ← parsePageSize
      let data ← parens do
        kwTok "data"
        let mut d : List UInt8 := []
        while !(← atEnd) do d := d ++ (← parseDataVal)
        pure d
      let id ← fillId id true
      let ps := 2 ^ (pl.getD 16)
      let pages := (data.length + ps - 1) / ps
      let mt : MemT := ⟨⟨is64, pages, some pages⟩, false, pl⟩
      pure (exportsOf exps .memory (id.getD "") ++
        [.data none (some (.id (id.getD ""), constOne is64)) data, .memory id mt])
    else
      let id ← fillId id (!exps.isEmpty)
      pure (exportsOf exps .memory (id.getD "") ++ [.memory id (← parseMemT)])

def parseIndices (ty : Option RefT) : P ElemPayload := do
  let mut fs : Array Idx := #[]
  while !(← atEnd) do fs := fs.push (← parseIdx)
  match ty with
  | none => pure (.indices fs.toList)
  | some r =>
    if r == ⟨true, .abs false 0x70⟩ then pure (.indices fs.toList)
    else pure (.exprs r (fs.toList.map fun f => #[⟨opNamed "ref.func", .idx f⟩]))

def parseElemExprs (ty : RefT) : P ElemPayload := do
  let mut es : Array (Array Instr) := #[]
  while !(← atEnd) do es := es.push (← parseExprOrSingle "item")
  pure (.exprs ty es.toList)

def parseTable : P (List Field) := do
  let id ← optId
  let exps ← parseInlineExports
  let isShared ← peekKw "shared"
  let hasIdxT := (← peekKw "i32") || (← peekKw "i64")
  let refNext ← peekRefType
  let ref2 ← do
    -- `peek2::<RefType>`: the token after the next starts a reference type
    match ← peekAt 1 with
    | some (.kw k) => pure (refShort? k).isSome
    | some .lp => pure (isKw "ref" (← peekAt 2) || isKw "shared" (← peekAt 2))
    | _ => pure false
  if refNext || ((isShared || hasIdxT) && ref2) then
    let shared ← if ← peekKw "shared" then (do advance; pure true) else pure false
    let is64 ← if ← peekKw "i32" then (do advance; pure false)
      else if ← peekKw "i64" then (do advance; pure true) else pure false
    let elem ← parseRefType
    let payload ← parens do
      kwTok "elem"
      if (← peek) == some .lp then parseElemExprs elem else parseIndices (some elem)
    let id ← fillId id true
    let len := match payload with
      | .indices fs => fs.length
      | .exprs _ es => es.length
    let tt : TableT := ⟨⟨is64, len, some len⟩, elem, shared⟩
    pure (exportsOf exps .table (id.getD "") ++
      [.elem none (.active (some (.id (id.getD ""))) (constOne is64)) payload, .table id tt none])
  else if isShared || hasIdxT || (← peekInt) then
    let tt ← parseTableT
    let init ← if ← atEnd then pure none else (do pure (some (← parseExpr)))
    let id ← fillId id (!exps.isEmpty)
    pure (exportsOf exps .table (id.getD "") ++ [.table id tt init])
  else
    match ← parseInlineImport with
    | some (m, n) =>
      let id ← fillId id (!exps.isEmpty)
      let tt ← parseTableT
      pure (exportsOf exps .table (id.getD "") ++ [.import (.single m n ⟨id, .table tt⟩)])
    | none => fail "unexpected token, expected a table type"

def parseGlobal : P (List Field) := do
  let id ← optId
  let exps ← parseInlineExports
  let id ← fillId id (!exps.isEmpty)
  let ex := exportsOf exps .global (id.getD "")
  match ← parseInlineImport with
  | some (m, n) => pure (ex ++ [.import (.single m n ⟨id, .global (← parseGlobalT)⟩)])
  | none =>
    let gt ← parseGlobalT
    pure (ex ++ [.global id gt (← parseExpr)])

def parseTag : P (List Field) := do
  let id ← optId
  let exps ← parseInlineExports
  let id ← fillId id (!exps.isEmpty)
  let ex := exportsOf exps .tag (id.getD "")
  match ← parseInlineImport with
  | some (m, n) => pure (ex ++ [.import (.single m n ⟨id, .tag (← parseTypeUse true)⟩)])
  | none => pure (ex ++ [.tag id (← parseTypeUse true)])

def parseElem : P Field := do
  let id ← optId
  let lpNotRef ← do
    match ← peek with
    | some .lp => pure !(← peekRefType)
    | _ => pure false
  let (mode, tableOmitted) ← if ← peekKw "declare" then (do advance; pure (ElemMode.declared, false))
    else if (← peekInt) || lpNotRef then do
      let (table, omitted) ← if ← peekInt then (do pure (some (Idx.num (← u32Tok)), true))
        else if ← peek2Kw "table" then (do
          let t ← parens (do kwTok "table"; parseIdx)
          pure (some t, false))
        else pure (none, true)
      let off ← parseExprOrSingle "offset"
      pure (ElemMode.active table off, omitted)
    else pure (ElemMode.passive, false)
  let indices ← if ← peekKw "func" then (do advance; pure true)
    else if ← peekRefType then pure false
    else pure tableOmitted
  let payload ← if indices then parseIndices none else (do parseElemExprs (← parseRefType))
  pure (.elem id mode payload)

def parseData : P Field := do
  let id ← optId
  let passive ← do
    match ← peek with
    | some (.str _) | some .rp | none => pure true
    | _ => pure false
  let mem ← if passive then pure none else do
    let m ← if ← peekInt then (do pure (Idx.num (← u32Tok)))
      else if ← peek2Kw "memory" then parens (do kwTok "memory"; parseIdx)
      else pure (Idx.num 0)
    let off ← parens do
      if ← peekKw "offset" then advance; parseExpr
      else
        let insn ← parseInstr
        if ← atEnd then pure #[insn]
        else pure ((← parseExpr).push insn)
    pure (some (m, off))
  let mut d : List UInt8 := []
  while !(← atEnd) do d := d ++ (← parseDataVal)
  pure (.data id mem d)

def parseField : P (List Field) := do
  match ← next with
  | .kw "type" => pure [.type (← parseTypeBody)]
  | .kw "rec" =>
    let mut ts : Array TyDecl := #[]
    while ← peek2Kw "type" do
      ts := ts.push (← parens (do kwTok "type"; parseTypeBody))
    pure [.recGroup ts.toList]
  | .kw "import" => pure [.import (← parseImport)]
  | .kw "func" => parseFunc
  | .kw "table" => parseTable
  | .kw "memory" => parseMemory
  | .kw "global" => parseGlobal
  | .kw "tag" => parseTag
  | .kw "export" =>
    let n ← strName
    let (s, i) ← parens do
      let s ← match ← next with
        | .kw "func" => pure Space.func | .kw "table" => pure .table
        | .kw "memory" => pure .memory | .kw "global" => pure .global | .kw "tag" => pure .tag
        | _ => fail "unexpected token, expected an export kind"
      pure (s, ← parseIdx)
    pure [.export n s i]
  | .kw "start" => pure [.start (← parseIdx)]
  | .kw "elem" => pure [← parseElem]
  | .kw "data" => pure [← parseData]
  | _ => fail "expected a module field"

/-- `(module $id? field*)`: the module identifier and the de-inlined fields. -/
def parseModule : P (Option String × List Field) := do
  expectLp
  kwTok "module"
  let id ← optId
  let mut fs : Array Field := #[]
  while !(← atEnd) do
    fs := fs ++ (← parens parseField)
  expectRp
  pure (id, fs.toList)

/-! ## Type expansion (`resolve/types.rs`) -/

structure XState where
  keys : List ((List ValT × List ValT) × Idx) := []
  appended : Array Field := #[]
  gensym : Nat

abbrev XM := StateT XState (Except String)

def xFresh : XM String := do
  let s ← get
  set { s with gensym := s.gensym + 1 }
  pure ("\x00gensym" ++ toString s.gensym)

def xInsert (k : List ValT × List ValT) (i : Idx) : XM Unit :=
  modify fun s => if s.keys.any (·.1 == k) then s else { s with keys := s.keys ++ [(k, i)] }

def expandTypeUse (tu : TypeUse) : XM TypeUse := do
  if tu.index.isSome then return tu
  let k := match tu.inline with
    | some f => f.key
    | none => ([], [])
  match (← get).keys.find? (·.1 == k) with
  | some (_, i) => pure { tu with index := some i }
  | none =>
    let id ← xFresh
    let f : FuncT := ⟨k.1.map fun t => (none, t), k.2⟩
    modify fun s => { s with appended := s.appended.push (.type ⟨some id, { kind := .func f }⟩) }
    xInsert k (.id id)
    pure { tu with index := some (.id id) }

def expandBlock (b : BlockT) : XM BlockT := do
  if b.ty.index.isSome then return b
  match b.ty.inline with
  | some f =>
    if f.params.isEmpty && f.results.length ≤ 1 then pure b
    else pure { b with ty := ← expandTypeUse b.ty }
  | none => pure { b with ty := { b.ty with inline := some {} } }

def expandInstr (i : Instr) : XM Instr := do
  match i.imm with
  | .block b => pure { i with imm := .block (← expandBlock b) }
  | .tryTable b cs => pure { i with imm := .tryTable (← expandBlock b) cs }
  | .callIndirect t tu => pure { i with imm := .callIndirect t (← expandTypeUse tu) }
  | _ => pure i

def expandExpr (e : Array Instr) : XM (Array Instr) := e.mapM expandInstr

def expandSig (s : ItemSig) : XM ItemSig := do
  match s.kind with
  | .func tu => pure { s with kind := .func (← expandTypeUse tu) }
  | .funcExact tu => pure { s with kind := .funcExact (← expandTypeUse tu) }
  | .tag tu => pure { s with kind := .tag (← expandTypeUse tu) }
  | _ => pure s

def expandField : Field → XM Field
  | .import im => do
    match im with
    | .single m n s => pure (.import (.single m n (← expandSig s)))
    | .group1 m items => pure (.import (.group1 m (← items.mapM fun (n, s) => do pure (n, ← expandSig s))))
    | .group2 m s ns => pure (.import (.group2 m (← expandSig s) ns))
  | .func id tu ls body => do
    let tu ← expandTypeUse tu
    pure (.func id tu ls (← expandExpr body))
  | .global id g e => do pure (.global id g (← expandExpr e))
  | .data id (some (m, off)) d => do pure (.data id (some (m, ← expandExpr off)) d)
  | .elem id mode p => do
    let mode ← match mode with
      | .active t off => do pure (ElemMode.active t (← expandExpr off))
      | m => pure m
    let p ← match p with
      | .exprs ty es => do pure (ElemPayload.exprs ty (← es.mapM expandExpr))
      | p => pure p
    pure (.elem id mode p)
  | .tag id tu => do pure (.tag id (← expandTypeUse tu))
  | .table id t (some e) => do pure (.table id t (some (← expandExpr e)))
  | f => pure f

/-- `types::expand`: fill gensyms of `type` fields, intern their function types, expand every
type use, and append the new types at the end. -/
def expand (fs : List Field) (gensym : Nat) : Except String (List Field) := do
  let go : XM (List Field) := do
    let mut hdr : Array Field := #[]
    for f in fs do
      match f with
      | .type ⟨id, d⟩ =>
        let id ← match id with
          | some i => pure i
          | none => xFresh
        match d.kind with
        | .func ft => xInsert ft.key (.id id)
        | _ => pure ()
        hdr := hdr.push (.type ⟨some id, d⟩)
      | f => hdr := hdr.push f
    let out ← hdr.toList.mapM expandField
    pure (out ++ (← get).appended.toList)
  (go.run' { gensym := gensym })

/-! ## Name resolution (`resolve/names.rs`) -/

abbrev NS := Std.HashMap String Nat

structure Ctx where
  funcs : NS := {}
  tables : NS := {}
  mems : NS := {}
  globals : NS := {}
  tags : NS := {}
  types : NS := {}
  datas : NS := {}
  elems : NS := {}
  nFuncs : Nat := 0
  nTables : Nat := 0
  nMems : Nat := 0
  nGlobals : Nat := 0
  nTags : Nat := 0
  nTypes : Nat := 0
  nDatas : Nat := 0
  nElems : Nat := 0
  /-- Struct field names per type index. -/
  fields : Std.HashMap Nat NS := {}
  /-- Per type index: the function type (`TypeInfo::Func`), if it is one. -/
  typeInfo : Array (Option (List ValT × List ValT)) := #[]
  deriving Inhabited

def spaceDesc : Space → String
  | .func => "func" | .table => "table" | .memory => "memory" | .global => "global"
  | .tag => "tag" | .type => "type" | .data => "data" | .elem => "elem" | .local => "local"
  | .label => "label"

def reg (m : NS) (n : Nat) (id : Option String) (desc : String) : Except String NS :=
  match id with
  | none => pure m
  | some i => if m.contains i then throw s!"duplicate {desc} identifier" else pure (m.insert i n)

def Ctx.regSpace (c : Ctx) (s : Space) (id : Option String) : Except String Ctx := do
  match s with
  | .func => pure { c with funcs := ← reg c.funcs c.nFuncs id "func", nFuncs := c.nFuncs + 1 }
  | .table => pure { c with tables := ← reg c.tables c.nTables id "table", nTables := c.nTables + 1 }
  | .memory => pure { c with mems := ← reg c.mems c.nMems id "memory", nMems := c.nMems + 1 }
  | .global => pure { c with globals := ← reg c.globals c.nGlobals id "global", nGlobals := c.nGlobals + 1 }
  | .tag => pure { c with tags := ← reg c.tags c.nTags id "tag", nTags := c.nTags + 1 }
  | .data => pure { c with datas := ← reg c.datas c.nDatas id "data", nDatas := c.nDatas + 1 }
  | .elem => pure { c with elems := ← reg c.elems c.nElems id "elem", nElems := c.nElems + 1 }
  | _ => pure c

def Ctx.regType (c : Ctx) (t : TyDecl) : Except String Ctx := do
  let n := c.nTypes
  let types ← reg c.types n t.id "type"
  let fields ← match t.def_.kind with
    | .struct fs => do
      let mut m : NS := (c.fields.get? n).getD {}
      let mut any := c.fields.contains n
      for (f, i) in fs.zipIdx do
        if let some id := f.id then
          if m.contains id then throw s!"duplicate identifier: duplicate field named `{id}`"
          m := m.insert id i
          any := true
      pure (if any then c.fields.insert n m else c.fields)
    | _ => pure c.fields
  let info := match t.def_.kind with
    | .func f => some f.key
    | _ => none
  pure { c with types, nTypes := n + 1, fields, typeInfo := c.typeInfo.push info }

def sigSpace : Sig → Space
  | .func _ | .funcExact _ => .func
  | .table _ => .table
  | .memory _ => .memory
  | .global _ => .global
  | .tag _ => .tag

def register (fs : List Field) : Except String Ctx := do
  let mut c : Ctx := {}
  for f in fs do
    match f with
    | .import im => for s in im.sigs do c ← c.regSpace (sigSpace s.kind) s.id
    | .global id .. => c ← c.regSpace .global id
    | .memory id _ => c ← c.regSpace .memory id
    | .func id .. => c ← c.regSpace .func id
    | .table id .. => c ← c.regSpace .table id
    | .type t => c ← c.regType t
    | .recGroup ts => for t in ts do c ← c.regType t
    | .elem id .. => c ← c.regSpace .elem id
    | .data id .. => c ← c.regSpace .data id
    | .tag id _ => c ← c.regSpace .tag id
    | _ => pure ()
  pure c

def Ctx.space (c : Ctx) : Space → NS
  | .func => c.funcs | .table => c.tables | .memory => c.mems | .global => c.globals
  | .tag => c.tags | .type => c.types | .data => c.datas | .elem => c.elems
  | _ => {}

def Ctx.resolve (c : Ctx) (s : Space) : Idx → Except String Nat
  | .num n => pure n
  | .id x => match (c.space s).get? x with
    | some n => pure n
    | none => throw s!"unknown {spaceDesc s}: failed to find name `${x}`"

/-! ## Encoding -/

def Ctx.heap (c : Ctx) : Heap → Except String (List UInt8)
  | .abs sh code => pure ((if sh then [0x65] else []) ++ [code])
  | .conc i => do pure (sleb (← c.resolve .type i))
  | .exact i => do pure (0x62 :: uleb (← c.resolve .type i))

def Ctx.ref (c : Ctx) (r : RefT) : Except String (List UInt8) := do
  match r with
  | ⟨true, h@(.abs ..)⟩ => c.heap h
  | ⟨true, h⟩ => pure (0x63 :: (← c.heap h))
  | ⟨false, h⟩ => pure (0x64 :: (← c.heap h))

def Ctx.val (c : Ctx) : ValT → Except String (List UInt8)
  | .num code => pure [code]
  | .ref r => c.ref r

def Ctx.stor (c : Ctx) : StorT → Except String (List UInt8)
  | .i8 => pure [0x78]
  | .i16 => pure [0x77]
  | .val v => c.val v

def Ctx.vals (c : Ctx) (ts : List ValT) : Except String (List UInt8) := do
  pure (vecB (← ts.mapM c.val))

/-- `check_matches`: an index and an inline type of one type use must agree. -/
def Ctx.checkMatches (c : Ctx) (n : Nat) (f : FuncT) : Except String Unit := do
  match c.typeInfo[n]? with
  | some (some (ps, rs)) =>
    let eqv (a b : ValT) : Bool :=
      match c.val a, c.val b with
      | .ok x, .ok y => x == y
      | _, _ => a == b
    let bad := ps.length != f.params.length || rs.length != f.results.length ||
      (ps.zip f.params).any (fun (a, (_, b)) => !eqv a b) ||
      (rs.zip f.results).any (fun (a, b) => !eqv a b)
    if bad then throw "inline function type doesn't match type reference"
  | some none => throw "invalid type: not a function type"
  | none => throw "unknown type: type index out of bounds"

/-- `resolve_type_use`: the index, after checking an inline type against it. -/
def Ctx.typeUse (c : Ctx) (tu : TypeUse) : Except String Nat := do
  let n ← c.resolve .type (tu.index.getD (.num 0))
  if let some f := tu.inline then
    if tu.index.isSome then
      -- resolve the inline value types (errors are the resolver's)
      for (_, t) in f.params do discard (c.val t)
      for t in f.results do discard (c.val t)
      c.checkMatches n f
  pure n

def Ctx.blockType (c : Ctx) (b : BlockT) : Except String (List UInt8) := do
  match b.ty.index with
  | some _ => pure (sleb (← c.typeUse b.ty))
  | none =>
    match b.ty.inline with
    | some ⟨[], []⟩ | none => pure [0x40]
    | some ⟨[], [t]⟩ => c.val t
    | some _ => throw "multi-value block types should have an index"

def Ctx.memarg (c : Ctx) (m : MemArg) : Except String (List UInt8) := do
  let a := (log2? m.align).getD 0
  let mem ← c.resolve .memory m.mem
  if mem == 0 then pure (uleb a ++ uleb m.offset)
  else pure (uleb (a + 64) ++ uleb mem ++ uleb m.offset)

/-- The state of the expression resolver: the local scope and the open blocks' labels. -/
structure ExprSt where
  locals : NS := {}
  blocks : Array (Option String) := #[]

/-- `resolve_label`: the relative depth of a label. -/
def ExprSt.label (st : ExprSt) : Idx → Except String Nat
  | .num n => pure n
  | .id x =>
    match (st.blocks.toList.reverse.zipIdx).find? (fun (b, _) => b == some x) with
    | some (_, i) => pure i
    | none => throw s!"unknown label: failed to find name `${x}`"

def ExprSt.local (st : ExprSt) : Idx → Except String Nat
  | .num n => pure n
  | .id x => match st.locals.get? x with
    | some n => pure n
    | none => throw s!"unknown local: failed to find name `${x}`"

def Ctx.field (c : Ctx) (t : Nat) : Idx → Except String Nat
  | .num n => pure n
  | .id x =>
    match c.fields.get? t with
    | none => throw s!"accessing a named field `{x}` in a struct without named fields, type index {t}"
    | some m => match m.get? x with
      | some n => pure n
      | none => throw s!"unknown field: failed to find name `${x}`"

def Ctx.idxIn (c : Ctx) (st : ExprSt) (s : Space) (i : Idx) : Except String Nat :=
  match s with
  | .label => st.label i
  | .local => st.local i
  | s => c.resolve s i

def Ctx.catch (c : Ctx) (st : ExprSt) : Catch → Except String (List UInt8)
  | .one t l => do pure (0x00 :: uleb (← c.resolve .tag t) ++ uleb (← st.label l))
  | .oneRef t l => do pure (0x01 :: uleb (← c.resolve .tag t) ++ uleb (← st.label l))
  | .all l => do pure (0x02 :: uleb (← st.label l))
  | .allRef l => do pure (0x03 :: uleb (← st.label l))

def Ctx.handle (c : Ctx) (st : ExprSt) : Handle → Except String (List UInt8)
  | .onLabel t l => do pure (0x00 :: uleb (← c.resolve .tag t) ++ uleb (← st.label l))
  | .onSwitch t => do pure (0x01 :: uleb (← c.resolve .tag t))

/-- The non-null variant of a nullable cast opcode (`ref.test`, `ref.cast`,
`ref.cast_desc_eq`): the last opcode byte minus one. -/
def nonNullCode (code : List UInt8) : List UInt8 :=
  match code.reverse with
  | b :: r => ((b - 1) :: r).reverse
  | [] => []

/-- Encode one instruction, updating the label stack. -/
def Ctx.instr (c : Ctx) (st : ExprSt) (i : Instr) : Except String (List UInt8 × ExprSt) := do
  let code := i.op.code
  let k := i.op.kind
  let pushBlock (b : BlockT) : ExprSt := { st with blocks := st.blocks.push b.label }
  match i.imm with
  | .none => pure (code, st)
  | .idx x =>
    match k with
    | .idx .label =>
      if i.op.name == "delegate" then
        let st' := { st with blocks := st.blocks.pop }
        pure (code ++ uleb (← st'.label x), st')
      else pure (code ++ uleb (← st.label x), st)
    | .idx s => pure (code ++ uleb (← c.idxIn st s x), st)
    | .table => pure (code ++ uleb (← c.resolve .table x), st)
    | .memory => pure (code ++ uleb (← c.resolve .memory x), st)
    | .arrayFill => pure (code ++ uleb (← c.resolve .type x), st)
    | _ => pure (code ++ uleb (← c.resolve .type x), st)
  | .ord o x =>
    match k with
    | .ordIdx s => pure (code ++ [o] ++ uleb (← c.resolve s x), st)
    | _ => pure (code ++ [o] ++ uleb (← c.resolve .table x), st)
  | .ordStruct o t f => do
    let tn ← c.resolve .type t
    pure (code ++ [o] ++ uleb tn ++ uleb (← c.field tn f), st)
  | .memarg m => pure (code ++ (← c.memarg m), st)
  | .lsLane m l => pure (code ++ (← c.memarg m) ++ [l.toUInt8], st)
  | .lane l => pure (code ++ [l.toUInt8], st)
  | .struct t f => do
    let tn ← c.resolve .type t
    pure (code ++ uleb tn ++ uleb (← c.field tn f), st)
  | .block b =>
    let st' := pushBlock b
    pure (code ++ (← c.blockType b), st')
  | .endLabel l =>
    if i.op.name == "end" then
      match st.blocks.back? with
      | none => pure (code, st)
      | some lab =>
        if l.isSome && l != lab then throw "mismatching labels between end and block"
        pure (code, { st with blocks := st.blocks.pop })
    else
      match st.blocks.back? with
      | some lab =>
        if l.isSome && l != lab then throw "mismatching labels between end and block"
        pure (code, st)
      | none => pure (code, st)
  | .callIndirect t tu => do
    let ty ← c.typeUse tu
    pure (code ++ uleb ty ++ uleb (← c.resolve .table t), st)
  | .bytes bs => pure (code ++ bs, st)
  | .int v => pure (code ++ sleb v, st)
  | .tryTable b cs => do
    let bt ← c.blockType b
    let cs ← cs.mapM (c.catch st)
    pure (code ++ bt ++ vecB cs, pushBlock b)
  | .two a b =>
    match k with
    | .tableInit => pure (code ++ uleb (← c.resolve .elem b) ++ uleb (← c.resolve .table a), st)
    | .memoryInit => pure (code ++ uleb (← c.resolve .data b) ++ uleb (← c.resolve .memory a), st)
    | .tableCopy => pure (code ++ uleb (← c.resolve .table a) ++ uleb (← c.resolve .table b), st)
    | .memoryCopy => pure (code ++ uleb (← c.resolve .memory a) ++ uleb (← c.resolve .memory b), st)
    | .switch => pure (code ++ uleb (← c.resolve .type a) ++ uleb (← c.resolve .tag b), st)
    | .arrayNewData => pure (code ++ uleb (← c.resolve .type a) ++ uleb (← c.resolve .data b), st)
    | .arrayNewElem => pure (code ++ uleb (← c.resolve .type a) ++ uleb (← c.resolve .elem b), st)
    | .arrayInit s => pure (code ++ uleb (← c.resolve .type a) ++ uleb (← c.resolve s b), st)
    | _ => pure (code ++ uleb (← c.resolve .type a) ++ uleb (← c.resolve .type b), st)
  | .select none => pure (code, st)
  | .select (some ts) => pure ([0x1c] ++ (← c.vals ts), st)
  | .resume t g hs => do
    let tn ← c.resolve .type t
    let gb ← match g with
      | some g => do pure (uleb (← c.resolve .tag g))
      | none => pure []
    let hs ← hs.mapM (c.handle st)
    pure (code ++ uleb tn ++ gb ++ vecB hs, st)
  | .ref r => do
    let h ← c.heap r.heap
    pure ((if r.nullable then code else nonNullCode code) ++ h, st)
  | .heap h => pure (code ++ (← c.heap h), st)
  | .brTable ls d => do
    let ls ← ls.mapM st.label
    pure (code ++ vecB (ls.map uleb) ++ uleb (← st.label d), st)
  | .brOnCast l a b => do
    let flags : UInt8 := (if a.nullable then 1 else 0) + (if b.nullable then 2 else 0)
    let lab ← st.label l
    pure (code ++ [flags] ++ uleb lab ++ (← c.heap a.heap) ++ (← c.heap b.heap), st)
  | .arrayNewFixed t n => pure (code ++ uleb (← c.resolve .type t) ++ uleb n, st)

/-- Encode an instruction sequence with the given scope (blocks are pushed by the
instructions themselves). -/
def Ctx.instrs (c : Ctx) (st : ExprSt) (is : Array Instr) : Except String (List UInt8) := do
  let mut st := st
  let mut out : Array UInt8 := #[]
  for i in is do
    let (bs, st') ← c.instr st i
    out := out ++ bs.toArray
    st := st'
  pure out.toList

/-- A constant expression (with its `end`). -/
def Ctx.constExpr (c : Ctx) (e : Array Instr) : Except String (List UInt8) := do
  pure ((← c.instrs {} e) ++ [0x0b])

def limitsB (flagsExtra : Nat) (l : Limits) : List UInt8 :=
  uleb l.min ++ (match l.max with | some m => uleb m | none => [])
    |> fun rest => [(flagsExtra + (if l.max.isSome then 1 else 0) + (if l.is64 then 4 else 0)).toUInt8] ++ rest

def Ctx.tableT (c : Ctx) (t : TableT) : Except String (List UInt8) := do
  pure ((← c.ref t.elem) ++ limitsB (if t.shared then 2 else 0) t.limits)

def memTB (m : MemT) : List UInt8 :=
  let flags := (if m.limits.max.isSome then 1 else 0) + (if m.shared then 2 else 0) +
    (if m.limits.is64 then 4 else 0) + (if m.pageLog.isSome then 8 else 0)
  [flags.toUInt8] ++ uleb m.limits.min ++ (match m.limits.max with | some x => uleb x | none => []) ++
    (match m.pageLog with | some p => uleb p | none => [])

def Ctx.globalT (c : Ctx) (g : GlobalT) : Except String (List UInt8) := do
  pure ((← c.val g.ty) ++ [((if g.mutable then 1 else 0) + (if g.shared then 2 else 0) : Nat).toUInt8])

def Ctx.entity (c : Ctx) : Sig → Except String (List UInt8)
  | .func tu => do pure (0x00 :: uleb (← c.typeUse tu))
  | .funcExact tu => do pure (0x20 :: uleb (← c.typeUse tu))
  | .table t => do pure (0x01 :: (← c.tableT t))
  | .memory m => pure (0x02 :: memTB m)
  | .global g => do pure (0x03 :: (← c.globalT g))
  | .tag tu => do pure ([0x04, 0x00] ++ uleb (← c.typeUse tu))

def Ctx.subtype (c : Ctx) (d : TypeDef) : Except String (List UInt8) := do
  let isFinal := d.final.getD true
  let pre ← if !d.parents.isEmpty || !isFinal then do
      let ps ← d.parents.mapM (c.resolve .type)
      pure ([if isFinal then (0x4f : UInt8) else 0x50] ++ vecB (ps.map uleb))
    else pure []
  let sh : List UInt8 := if d.shared then [0x65] else []
  let des ← match d.describes with
    | some i => do pure (0x4c :: uleb (← c.resolve .type i))
    | none => pure []
  let dor ← match d.descriptor with
    | some i => do pure (0x4d :: uleb (← c.resolve .type i))
    | none => pure []
  let body ← match d.kind with
    | .func f => do pure (0x60 :: (← c.vals (f.params.map (·.2))) ++ (← c.vals f.results))
    | .array m t => do pure (0x5e :: (← c.stor t) ++ [if m then 1 else 0])
    | .struct fs => do
      let xs ← fs.mapM fun f => do pure ((← c.stor f.ty) ++ [if f.mutable then (1 : UInt8) else 0])
      pure (0x5f :: vecB xs)
    | .cont i => do pure (0x5d :: sleb (← c.resolve .type i))
  pure (pre ++ sh ++ des ++ dor ++ body)

def secB (id : UInt8) (items : List (List UInt8)) : List UInt8 :=
  if items.isEmpty then [] else
  let body := vecB items
  id :: uleb body.length ++ body

def rawSection (id : UInt8) (body : List UInt8) : List UInt8 := id :: uleb body.length ++ body

def funcref : RefT := ⟨true, .abs false 0x70⟩

def Ctx.elem (c : Ctx) (mode : ElemMode) (p : ElemPayload) : Except String (List UInt8) := do
  let exprBit : Nat := match p with | .indices _ => 0 | .exprs .. => 4
  let typeB ← match p with
    | .indices _ => pure [0x00]
    | .exprs ty _ => c.ref ty
  let items ← match p with
    | .indices fs => do pure (vecB ((← fs.mapM (c.resolve .func)).map uleb))
    | .exprs _ es => do pure (vecB (← es.mapM c.constExpr))
  match mode with
  | .passive => pure ([(1 + exprBit).toUInt8] ++ typeB ++ items)
  | .declared => pure ([(3 + exprBit).toUInt8] ++ typeB ++ items)
  | .active t off =>
    let offB ← c.constExpr off
    let plain := match p with
      | .indices _ => true
      | .exprs ty _ => ty == funcref
    match t with
    | none =>
      if plain then pure ([exprBit.toUInt8] ++ offB ++ items)
      else pure ([(2 + exprBit).toUInt8] ++ uleb 0 ++ offB ++ typeB ++ items)
    | some t => do
      pure ([(2 + exprBit).toUInt8] ++ uleb (← c.resolve .table t) ++ offB ++ typeB ++ items)

/-- `needs_data_count`. -/
def needsDataCount (fs : List Field) : Bool :=
  fs.any fun
    | .func _ _ _ body => body.any fun i =>
        ["memory.init", "data.drop", "array.new_data", "array.init_data"].contains i.op.name
    | _ => false

/-- The local scope of a function (`resolve_field` on `Func`). -/
def Ctx.localScope (c : Ctx) (tu : TypeUse) (locals : List (Option String × ValT)) :
    Except String NS := do
  let n ← c.typeUse tu
  let mut m : NS := {}
  let mut k := 0
  match tu.inline with
  | some f =>
    for (id, _) in f.params do
      m ← reg m k id "local"
      k := k + 1
  | none =>
    match c.typeInfo[n]? with
    | some (some (ps, _)) => k := ps.length
    | _ => pure ()
  for (id, _) in locals do
    m ← reg m k id "local"
    k := k + 1
  pure m

/-- The locals of a code entry, as runs of equal encoded types. -/
def Ctx.localRuns (c : Ctx) (ls : List (Option String × ValT)) : Except String (List UInt8) := do
  let ts ← ls.mapM fun (_, t) => c.val t
  let runs := ts.foldl (fun (acc : Array (Nat × List UInt8)) t =>
    match acc.back? with
    | some (n, u) => if u == t then acc.pop.push (n + 1, u) else acc.push (1, t)
    | none => acc.push (1, t)) #[]
  pure (vecB (runs.toList.map fun (n, t) => uleb n ++ t))

/-! ### The `name` section (`find_names`) -/

def nm? (id : Option String) : Option String :=
  match id with
  | some s => if isGensym s then none else some s
  | none => none

/-- The name of an identifier: its `(@name "…")` annotation (`ren`), else the identifier. -/
def nmR (ren : List (String × String)) (id : Option String) : Option String :=
  match nm? id with
  | some s => some ((ren.find? (·.1 == s)).map (·.2) |>.getD s)
  | none => none

def nameMap (xs : List (Nat × String)) : List UInt8 :=
  vecB (xs.map fun (i, s) => uleb i ++ nameB s)

def indirectMap (xs : List (Nat × List (Nat × String))) : List UInt8 :=
  vecB (xs.map fun (i, m) => uleb i ++ nameMap m)

def subsec (id : UInt8) (body : List UInt8) : List UInt8 := id :: uleb body.length ++ body

structure Names where
  funcs : Array (Nat × String) := #[]
  locals : Array (Nat × List (Nat × String)) := #[]
  labels : Array (Nat × List (Nat × String)) := #[]
  types : Array (Nat × String) := #[]
  tables : Array (Nat × String) := #[]
  mems : Array (Nat × String) := #[]
  globals : Array (Nat × String) := #[]
  elems : Array (Nat × String) := #[]
  datas : Array (Nat × String) := #[]
  fields : Array (Nat × List (Nat × String)) := #[]
  tags : Array (Nat × String) := #[]
  params : Array (Nat × List (Nat × String)) := #[]
  tagParams : Array (Nat × List (Nat × String)) := #[]
  nF : Nat := 0
  nTy : Nat := 0
  nTb : Nat := 0
  nM : Nat := 0
  nG : Nat := 0
  nE : Nat := 0
  nD : Nat := 0
  nTg : Nat := 0

def paramNames (ren : List (String × String)) (f : FuncT) : List (Nat × String) :=
  f.params.zipIdx.filterMap fun ((id, _), i) => (nmR ren id).map (i, ·)

def addName (ren : List (String × String)) (xs : Array (Nat × String)) (i : Nat)
    (id : Option String) : Array (Nat × String) :=
  match nmR ren id with
  | some s => xs.push (i, s)
  | none => xs

/-- The function type of a type index in the final type list (`func_type`). -/
def funcTypeAt (types : Array TypeDef) (n : Nat) : Option FuncT :=
  match types[n]? with
  | some d => match d.kind with
    | .func f => some f
    | _ => none
  | none => none

def findNames (ren : List (String × String)) (c : Ctx) (fs : List Field) (types : Array TypeDef) :
    Except String Names := do
  let mut r : Names := {}
  for f in fs do
    match f with
    | .import im =>
      for s in im.sigs do
        match s.kind with
        | .func tu | .funcExact tu =>
          r := { r with funcs := addName ren r.funcs r.nF s.id }
          if let some ty := tu.inline then
            let ps := paramNames ren ty
            if !ps.isEmpty then r := { r with locals := r.locals.push (r.nF, ps) }
          r := { r with nF := r.nF + 1 }
        | .table _ => r := { r with tables := addName ren r.tables r.nTb s.id, nTb := r.nTb + 1 }
        | .memory _ => r := { r with mems := addName ren r.mems r.nM s.id, nM := r.nM + 1 }
        | .global _ => r := { r with globals := addName ren r.globals r.nG s.id, nG := r.nG + 1 }
        | .tag _ => r := { r with tags := addName ren r.tags r.nTg s.id, nTg := r.nTg + 1 }
    | .global id .. => r := { r with globals := addName ren r.globals r.nG id, nG := r.nG + 1 }
    | .table id .. => r := { r with tables := addName ren r.tables r.nTb id, nTb := r.nTb + 1 }
    | .memory id _ => r := { r with mems := addName ren r.mems r.nM id, nM := r.nM + 1 }
    | .tag id tu =>
      r := { r with tags := addName ren r.tags r.nTg id }
      if let some ty := tu.inline then
        let ps := paramNames ren ty
        if !ps.isEmpty then r := { r with tagParams := r.tagParams.push (r.nTg, ps) }
      r := { r with nTg := r.nTg + 1 }
    | .type t =>
      r := { r with types := addName ren r.types r.nTy t.id }
      match t.def_.kind with
      | .func ft =>
        let ps := paramNames ren ft
        if !ps.isEmpty then r := { r with params := r.params.push (r.nTy, ps) }
      | .struct sfs =>
        let ns := sfs.zipIdx.filterMap fun (x, i) => (nmR ren x.id).map (i, ·)
        if !ns.isEmpty then r := { r with fields := r.fields.push (r.nTy, ns) }
      | _ => pure ()
      r := { r with nTy := r.nTy + 1 }
    | .recGroup ts =>
      for t in ts do
        r := { r with types := addName ren r.types r.nTy t.id }
        match t.def_.kind with
        | .func ft =>
          let ps := paramNames ren ft
          if !ps.isEmpty then r := { r with params := r.params.push (r.nTy, ps) }
        | .struct sfs =>
          let ns := sfs.zipIdx.filterMap fun (x, i) => (nmR ren x.id).map (i, ·)
          if !ns.isEmpty then r := { r with fields := r.fields.push (r.nTy, ns) }
        | _ => pure ()
        r := { r with nTy := r.nTy + 1 }
    | .elem id .. => r := { r with elems := addName ren r.elems r.nE id, nE := r.nE + 1 }
    | .data id .. => r := { r with datas := addName ren r.datas r.nD id, nD := r.nD + 1 }
    | .func id tu ls body =>
      r := { r with funcs := addName ren r.funcs r.nF id }
      let mut lns : Array (Nat × String) := #[]
      let mut li := 0
      let mut discard := false
      match tu.inline with
      | some ty =>
        for (pid, _) in ty.params do
          lns := addName ren lns li pid
          li := li + 1
      | none =>
        let n ← c.resolve .type (tu.index.getD (.num 0))
        match funcTypeAt types n with
        | some ft => li := ft.params.length
        | none => discard := true
      for (lid, _) in ls do
        lns := addName ren lns li lid
        li := li + 1
      let mut labs : Array (Nat × String) := #[]
      let mut bi := 0
      for i in body do
        match i.imm with
        | .block b | .tryTable b _ =>
          labs := addName ren labs bi b.label
          bi := bi + 1
        | _ => pure ()
      if !discard && !lns.isEmpty then r := { r with locals := r.locals.push (r.nF, lns.toList) }
      if !labs.isEmpty then r := { r with labels := r.labels.push (r.nF, labs.toList) }
      r := { r with nF := r.nF + 1 }
    | _ => pure ()
  pure r

def Names.toSection (modName : Option String) (r : Names) : List UInt8 :=
  let parts : List UInt8 :=
    (match modName with | some s => subsec 0 (nameB s) | none => []) ++
    (if r.funcs.isEmpty then [] else subsec 1 (nameMap r.funcs.toList)) ++
    (if r.locals.isEmpty then [] else subsec 2 (indirectMap r.locals.toList)) ++
    (if r.labels.isEmpty then [] else subsec 3 (indirectMap r.labels.toList)) ++
    (if r.types.isEmpty then [] else subsec 4 (nameMap r.types.toList)) ++
    (if r.tables.isEmpty then [] else subsec 5 (nameMap r.tables.toList)) ++
    (if r.mems.isEmpty then [] else subsec 6 (nameMap r.mems.toList)) ++
    (if r.globals.isEmpty then [] else subsec 7 (nameMap r.globals.toList)) ++
    (if r.elems.isEmpty then [] else subsec 8 (nameMap r.elems.toList)) ++
    (if r.datas.isEmpty then [] else subsec 9 (nameMap r.datas.toList)) ++
    (if r.fields.isEmpty then [] else subsec 10 (indirectMap r.fields.toList)) ++
    (if r.tags.isEmpty then [] else subsec 11 (nameMap r.tags.toList)) ++
    (if r.params.isEmpty then [] else subsec 12 (indirectMap r.params.toList)) ++
    (if r.tagParams.isEmpty then [] else subsec 13 (indirectMap r.tagParams.toList))
  if parts.isEmpty then [] else rawSection 0 (nameB "name" ++ parts)

/-! ### The module -/

/-- The import order check of `resolve`: imports before every function, table, memory and
global. -/
def checkImportOrder (fs : List Field) : Except String Unit := do
  let mut last : Option String := none
  for f in fs do
    match f with
    | .import _ => if let some n := last then throw s!"import after {n}"
    | .memory .. => last := some "memory"
    | .func .. => last := some "function"
    | .table .. => last := some "table"
    | .global .. => last := some "global"
    | _ => pure ()

/-- A custom section from an annotation. -/
def customB (c : Annot.Custom) : List UInt8 :=
  rawSection 0 (uleb c.name.length ++ c.name ++ c.data)

/-- The custom sections placed at `p`, in order. -/
def customsAt (cs : List Annot.Custom) (p : Annot.Place) : List UInt8 :=
  (cs.filter (·.place == p)).flatMap customB

/-- Encode resolved fields (`binary.rs` `encode`), with the custom sections `cs` of the
`@custom`/`@producers` annotations at their places and the names `ren` of the `@name`
annotations. -/
def encodeFields (modName : Option String) (fs : List Field) (cs : List Annot.Custom := [])
    (ren : List (String × String) := []) : Except String ByteArray := do
  let c ← register fs
  let typesL := fs.flatMap fun | .type t => [t] | .recGroup ts => ts | _ => []
  let typeDefs := (typesL.map (·.def_)).toArray
  let tySec ← fs.filterMapM fun
    | .type t => do pure (some (← c.subtype t.def_))
    | .recGroup ts => do pure (some (0x4e :: vecB (← ts.mapM fun t => c.subtype t.def_)))
    | _ => pure none
  let imSec ← fs.filterMapM fun
    | .import (.single m n s) => do pure (some (nameB m ++ nameB n ++ (← c.entity s.kind)))
    | .import (.group1 m items) => do
      let xs ← items.mapM fun (n, s) => do pure (nameB n ++ (← c.entity s.kind))
      pure (some (nameB m ++ [0x00, 0x7F] ++ vecB xs))
    | .import (.group2 m s ns) => do
      pure (some (nameB m ++ [0x00, 0x7E] ++ (← c.entity s.kind) ++ vecB (ns.map nameB)))
    | _ => pure none
  let fnSec ← fs.filterMapM fun
    | .func _ tu .. => do pure (some (uleb (← c.typeUse tu)))
    | _ => pure none
  let tbSec ← fs.filterMapM fun
    | .table _ t none => do pure (some (← c.tableT t))
    | .table _ t (some e) => do pure (some ([0x40, 0x00] ++ (← c.tableT t) ++ (← c.constExpr e)))
    | _ => pure none
  let memSec := fs.filterMap fun
    | .memory _ m => some (memTB m)
    | _ => none
  let tagSec ← fs.filterMapM fun
    | .tag _ tu => do pure (some ([0x00] ++ uleb (← c.typeUse tu)))
    | _ => pure none
  let glSec ← fs.filterMapM fun
    | .global _ g e => do pure (some ((← c.globalT g) ++ (← c.constExpr e)))
    | _ => pure none
  let exSec ← fs.filterMapM fun
    | .export n s i => do
      let kb : UInt8 := match s with
        | .func => 0 | .table => 1 | .memory => 2 | .global => 3 | _ => 4
      pure (some (nameB n ++ [kb] ++ uleb (← c.resolve s i)))
    | _ => pure none
  let stSec ← fs.filterMapM fun
    | .start i => do pure (some (rawSection 8 (uleb (← c.resolve .func i))))
    | _ => pure none
  let elSec ← fs.filterMapM fun
    | .elem _ m p => do pure (some (← c.elem m p))
    | _ => pure none
  let datas := fs.filterMap fun | .data _ m d => some (m, d) | _ => none
  let dcSec := if needsDataCount fs then rawSection 12 (uleb datas.length) else []
  let codeSec ← fs.filterMapM fun
    | .func _ tu ls body => do
      let scope ← c.localScope tu ls
      let body ← c.instrs { locals := scope } body
      let entry := (← c.localRuns ls) ++ body ++ [0x0b]
      pure (some (uleb entry.length ++ entry))
    | _ => pure none
  let dtSec ← datas.mapM fun (m, d) => do
    match m with
    | none => pure ([0x01] ++ vecB (d.map fun b => [b]))
    | some (mi, off) =>
      let n ← c.resolve .memory mi
      let offB ← c.constExpr off
      if n == 0 then pure ([0x00] ++ offB ++ uleb d.length ++ d)
      else pure ([0x02] ++ uleb n ++ offB ++ uleb d.length ++ d)
  let names ← findNames ren c fs typeDefs
  let around (a : String) (b : List UInt8) : List UInt8 :=
    customsAt cs (.before a) ++ b ++ customsAt cs (.after a)
  let hasName := cs.any (·.name == "name".toUTF8.toList)
  let bytes : List UInt8 :=
    [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00] ++ customsAt cs .beforeFirst ++
    around "type" (secB 1 tySec) ++ around "import" (secB 2 imSec) ++
    around "func" (secB 3 fnSec) ++ around "table" (secB 4 tbSec) ++
    around "memory" (secB 5 memSec) ++ around "tag" (secB 13 tagSec) ++
    around "global" (secB 6 glSec) ++ around "export" (secB 7 exSec) ++
    around "start" stSec.flatten ++ around "elem" (secB 9 elSec) ++ dcSec ++
    around "code" (secB 10 codeSec) ++ around "data" (secB 11 dtSec) ++
    customsAt cs .afterLast ++
    (if hasName then [] else names.toSection (nmR ren modName))
  pure ⟨bytes.toArray⟩

/-- **The encoder**: the binary of a core text module given as an S-expression
`(module $id? field…)`. -/
def encodeModule (x : SExp) (cs : List Annot.Custom := []) (ren : List (String × String) := []) :
    Except String ByteArray := do
  let toks := flatItem x #[]
  let ((modName, fs), st) ← parseModule.run { toks }
  if st.pos != toks.size then throw "extra tokens after the module"
  checkImportOrder fs
  let fs ← expand fs st.gensym
  encodeFields modName fs cs ren

/-- `encodeModule` with the `@custom`/`@producers` and `@name` annotations of the module's
source text `src` (`Annot.customs`, `Annot.nameAnnots`); a malformed annotation is an error,
as in the `wast` crate. -/
def encodeModuleSrc (x : SExp) (src : String) : Except String ByteArray := do
  let some cs := Annot.customs src | throw "malformed custom annotation"
  encodeModule x cs (Annot.nameAnnots src)

end Silmaril.Wasm.Tools.WastEnc
