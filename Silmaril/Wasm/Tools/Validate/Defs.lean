module

public import Silmaril.Wasm.Tools.Features.Defs
public import Silmaril.Wasm.Tools.Framing.Defs
public import Silmaril.Wasm.Models.Syntax.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binary.Core.CompactImportsDecode
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# `wasm-tools validate` for core modules

The specification of `wasm-tools validate` on a core module binary under a wasmparser feature
set `F` (`Silmaril.Wasm.Tools.Features`):

* `Enc F b m`: the bytes `b` encode the module `m` in the Core 3.0 binary grammar
  (`Silmaril.Wasm.Binary.Core.Encodes`), extended by the compact-imports grammar
  (`CompactImports.Encodes`) when `F` has `compact-imports` (on by default, as upstream);
* `wnorm m`: erases the two Core 3.0 spellings of Wasm 1.0 forms that wasmparser does not
  gate behind any feature: the implicit `ref.null` initialiser of a table (`(ref.null t)` for a
  table of element type `(ref null t)`), and the element list of function indices, which the
  3.0 grammar decodes to element type `(ref func)` with `ref.func` initialisers (wasmparser:
  `ElementItems::Functions`, type `RefType::FUNC`, never feature-checked);
* `InFeatW F m`: `m` uses only the capabilities `F` grants: `Module.InFeat (toFS F) (wnorm m)`
  (`Silmaril.Wasm.Models.Module.InFeat`), `global.get` of a defined global in a constant
  expression only with GC (`constGlobalsB`), and mutable globals imported or exported only with
  `mutable-global` (`mutGlobalIOB`);
* `binGates F b`: the gates wasmparser puts on encodings rather than on modules (data count
  section, tag section, GC type-section forms);
* `ValidW F m := ModuleValid m ∧ InFeatW F m` (`Silmaril.Wasm.Validation.ModuleValid`, the
  specification's module validity);
* `Accepts F b := binGates F b ∧ ∃ m, Enc F b m ∧ ValidW F m`: **what `validate` accepts**.

The executable side:

* `decodeW F b`: silmaril-lean's decoder (sound for `Enc F`), with its error message;
* `check F b : Except Error Unit`: the encoding gates, decode, `validate?` (sound and complete
  for `ModuleValid`), then the feature check; `Error` says which step failed. `Thms` proves
  `check F b = .ok ()` iff the decoder accepts `b` and `Accepts F b`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Validate

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models Silmaril.Wasm.Tools.Features

/-- Is the compact-imports flag set? -/
def compact (F : WFeatures) : Bool := WFeatures.hasFlag F "compact-imports"

/-- **The binary grammar under `F`**: Core 3.0, plus compact imports when `F` has them. -/
def Enc (F : WFeatures) (b : List UInt8) (m : Module) : Prop :=
  if compact F then Core.CompactImports.Encodes b m else Core.Encodes b m

/-- The decoder under `F`, with its error message. -/
def decodeW (F : WFeatures) (b : ByteArray) : Except String Module :=
  if compact F then Core.CompactImports.Decode.decodeModule b else Core.Decode.decodeModule b

/-- Is the expression `[ref.null h]`? -/
def isNullOf (h : HeapType) : Expr → Bool
  | [.refNull h'] => h' == h
  | _ => false

/-- The implicit initialiser of a table of element type `t`: `ref.null` of its heap type. -/
def implicitInit (t : Table) : Bool :=
  t.type.element.nullable && isNullOf t.type.element.heap t.init

/-- Is an element initialiser a function index (`[ref.func f]`)? -/
def isFuncIdx : Expr → Bool
  | [.refFunc _] => true
  | _ => false

/-- An element segment of function indices, as the 3.0 grammar decodes it. -/
def funcIdxElem (e : Elem) : Bool :=
  e.type == ⟨false, .abstract .func⟩ && e.init.all isFuncIdx

/-- **Erase the ungated Wasm 1.0 forms**: implicit table initialisers, and function-index element
segments (to element type `funcref`, no initialiser expressions). -/
def wnorm (m : Module) : Module :=
  { m with
    tables := m.tables.map fun t => if implicitInit t then { t with init := [] } else t
    elems := m.elems.map fun e =>
      if funcIdxElem e then { e with type := ⟨true, .abstract .func⟩, init := e.init.map fun _ => [] }
      else e }

/-- The number of imported globals. -/
def nImportedGlobals (m : Module) : Nat :=
  (m.imports.filter fun i => match i.type with | .global _ => true | _ => false).length

/-- Every constant expression of a module: global, table and element initialisers, element
and data offsets. -/
def constExprs (m : Module) : List Expr :=
  m.globals.map (·.init) ++ m.tables.map (·.init) ++ (m.elems.map (·.init)).flatten ++
    m.elems.filterMap (fun e => match e.mode with | .active _ off => some off | _ => none) ++
    m.data.filterMap (fun d => match d.mode with | .active _ off => some off | _ => none)

/-- wasmparser's gate on constant expressions: `global.get` of a global the module defines
needs GC (`validate_global`). -/
def constGlobalsB (S : FeatureSet) (m : Module) : Bool :=
  S.has .gcImm || (constExprs m).all fun e => e.all fun
    | .globalGet x => decide (x.toNat < nImportedGlobals m)
    | _ => true

/-- The types of the global index space: imported, then defined. -/
def globalTypes (m : Module) : List GlobalType :=
  m.imports.filterMap (fun i => match i.type with | .global g => some g | _ => none) ++
    m.globals.map (·.type)

/-- wasmparser's `mutable-global` gate: without it, no mutable global is imported or exported. -/
def mutGlobalIOB (F : WFeatures) (m : Module) : Bool :=
  F.hasBit 0 ||
    (m.imports.all (fun i => match i.type with | .global g => g.mutability == .const | _ => true) &&
     m.exports.all fun e => match e.index with
      | .global x => match (globalTypes m)[x.toNat]? with
        | some g => g.mutability == .const
        | none => true
      | _ => true)

/-- `m` uses only what `F` grants. -/
def InFeatW (F : WFeatures) (m : Module) : Prop :=
  Module.InFeat (WFeatures.toFS F) (wnorm m) ∧ constGlobalsB (WFeatures.toFS F) m = true ∧
    mutGlobalIOB F m = true

/-- The Boolean form of `InFeatW`. -/
def inFeatWB (F : WFeatures) (m : Module) : Bool :=
  Module.inFeatB (WFeatures.toFS F) (wnorm m) && constGlobalsB (WFeatures.toFS F) m &&
    mutGlobalIOB F m

/-! ## Gates on the encoding

Five wasmparser gates depend on how a module is encoded, not on the module: the data count
section needs `bulk-memory`, a tag section (even empty) needs `exceptions`, an explicit
recursion group (`0x4e`) or a sub type form (`0x4f`, `0x50`) needs `gc`, and a table with an
explicit initialiser (`0x40 0x00`) or an element segment with an explicit non-nullable type
needs `function-references`. -/

open Silmaril.Wasm.Tools.Framing in
/-- Skip a value type (`0x63`/`0x64` with a heap type: an `s33`). -/
def skipValType : List UInt8 → Option (List UInt8)
  | [] => none
  | v :: r =>
    if v = 0x63 || v = 0x64 then
      let lebLen := (r.takeWhile (· ≥ 0x80)).length + 1
      if lebLen ≤ r.length then some (r.drop lebLen) else none
    else some r

/-- Skip `n` value types. -/
def skipValTypes : Nat → List UInt8 → Option (List UInt8)
  | 0, r => some r
  | n + 1, r => (skipValType r).bind (skipValTypes n)

open Silmaril.Wasm.Tools.Framing in
/-- Does a type section use a GC encoding form (`0x4e`, `0x4f`, `0x50`) before its first
struct or array type? (A struct or array type needs GC in `Module.inFeatB` already; a
malformed section is left to the decoder.) -/
def typeSecUsesGc (content : List UInt8) : Bool :=
  match readU32 content with
  | none => false
  | some (n, _, r) => go n r
where
  go : Nat → List UInt8 → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | k + 1, t :: r =>
    if t = 0x4e || t = 0x4f || t = 0x50 then true
    else if t = 0x60 then
      match readU32 r with
      | none => false
      | some (np, _, r) =>
        match skipValTypes np r with
        | none => false
        | some r =>
          match readU32 r with
          | none => false
          | some (nr, _, r) =>
            match skipValTypes nr r with
            | none => false
            | some r => go k r
    else false

/-- Skip an LEB128 number (any width). -/
def skipLeb (r : List UInt8) : Option (List UInt8) :=
  let n := (r.takeWhile (· ≥ 0x80)).length + 1
  if n ≤ r.length then some (r.drop n) else none

/-- Skip a reference type (`0x63`/`0x64` with a heap type, or one byte). -/
def skipRefType : List UInt8 → Option (List UInt8)
  | [] => none
  | v :: r => if v = 0x63 || v = 0x64 then skipLeb r else some r

open Silmaril.Wasm.Tools.Framing in
/-- Does a table section give a table an explicit initialiser (`0x40 0x00`)? Scans until the
first entry it cannot skip. -/
def tableSecHasInit (content : List UInt8) : Bool :=
  match readU32 content with
  | none => false
  | some (n, _, r) => go n r
where
  go : Nat → List UInt8 → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | k + 1, t :: r =>
    if t = 0x40 then true
    else
      match skipRefType (t :: r) with
      | none => false
      | some (fl :: r) =>
        let r := skipLeb r
        let r := if fl.toNat % 2 = 1 then r.bind skipLeb else r
        match r with
        | some r => go k r
        | none => false
      | some [] => false

/-- Skip one constant instruction (the opcodes of constant expressions of Core 3.0); `none`
when the opcode is not one of them. -/
def skipConstInstr : List UInt8 → Option (List UInt8)
  | [] => none
  | op :: r =>
    if op = 0x41 || op = 0x42 || op = 0x23 || op = 0xD2 || op = 0xD0 then skipLeb r
    else if op = 0x43 then (if 4 ≤ r.length then some (r.drop 4) else none)
    else if op = 0x44 then (if 8 ≤ r.length then some (r.drop 8) else none)
    else if op = 0x6a || op = 0x6b || op = 0x6c || op = 0x7c || op = 0x7d || op = 0x7e then
      some r
    else none

/-- Skip a constant expression up to and including its `end`. -/
def skipConstExpr : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _, [] => none
  | k + 1, op :: r => if op = 0x0b then some r else (skipConstInstr (op :: r)).bind (skipConstExpr k)

open Silmaril.Wasm.Tools.Framing in
/-- Does an element section declare an explicit non-nullable element type (`0x64`, flags with
`0b100` and a type) for an expression list? Scans until the first entry it cannot skip. -/
def elemSecNonNull (content : List UInt8) : Bool :=
  match readU32 content with
  | none => false
  | some (n, _, r) => go n r
where
  go : Nat → List UInt8 → Bool
  | 0, _ => false
  | k + 1, r =>
    match readU32 r with
    | none => false
    | some (fl, _, r) =>
      let exprs := fl / 4 % 2 = 1
      let typed := fl % 4 ≠ 0
      -- table index and offset
      let r : Option (List UInt8) :=
        if fl % 2 = 1 then some r
        else
          let r := if fl / 2 % 2 = 1 then skipLeb r else some r
          r.bind fun r => skipConstExpr r.length r
      match r with
      | none => false
      | some r =>
        if exprs && typed && r.head? = some 0x64 then true
        else
          let r : Option (List UInt8) := if typed then (if exprs then skipRefType r else
            r.tail?) else some r
          match r.bind readU32 with
          | none => false
          | some (cnt, _, r) =>
            let r := if exprs then skipN cnt (skipConstExpr r.length) r else skipN cnt skipLeb r
            match r with
            | some r => go k r
            | none => false
  skipN : Nat → (List UInt8 → Option (List UInt8)) → List UInt8 → Option (List UInt8)
  | 0, _, r => some r
  | c + 1, f, r => (f r).bind (skipN c f)

open Silmaril.Wasm.Tools.Framing in
/-- **The encoding gates of `F`** on the bytes `b` (true when the sections cannot be split: the
decoder rejects those). -/
def binGates (F : WFeatures) (b : List UInt8) : Bool :=
  let bulk := F.hasFlag "bulk-memory"
  let exn := F.hasFlag "exceptions"
  let gc := F.hasFlag "gc"
  let fref := F.hasFlag "function-references"
  if bulk && exn && gc && fref then true else
  match splitSecs (b.drop 8) with
  | none => true
  | some ss => ss.all fun s =>
    (s.id != 12 || bulk) && (s.id != 13 || exn) && (s.id != 1 || gc || !typeSecUsesGc s.content) &&
    (s.id != 4 || fref || !tableSecHasInit s.content) &&
    (s.id != 9 || fref || !elemSecNonNull s.content)

/-- **A valid module under `F`**. -/
def ValidW (F : WFeatures) (m : Module) : Prop :=
  Validation.ModuleValid m ∧ InFeatW F m

/-- **What `wasm-tools validate` accepts under `F`** (core modules). -/
def Accepts (F : WFeatures) (b : List UInt8) : Prop :=
  binGates F b = true ∧ ∃ m, Enc F b m ∧ ValidW F m

/-- Why a binary was rejected. -/
inductive Error where
  /-- The decoder rejected the bytes (with its message). -/
  | malformed (msg : String)
  /-- The module is not valid (`validate?` returned `none`). -/
  | invalid
  /-- The module is valid but uses a capability `F` does not grant. -/
  | feature
  /-- The encoding uses a form `F` does not grant (`binGates`). -/
  | encodingFeature
  deriving Repr, DecidableEq

/-- **The validator**: decode, validate, check the features. -/
def check (F : WFeatures) (b : ByteArray) : Except Error Unit :=
  if !binGates F b.data.toList then .error .encodingFeature else
  match decodeW F b with
  | .error e => .error (.malformed e)
  | .ok m =>
    match Validation.validate? m with
    | none => .error .invalid
    | some _ => if inFeatWB F m then .ok () else .error .feature

/-- The message printed for a rejection (the class of upstream's message, not its text). -/
def Error.message : Error → String
  | .malformed e => s!"failed to parse WebAssembly module: {e}"
  | .invalid => "module failed to validate: the module is not valid (Wasm 3.0 validation)"
  | .feature => "module failed to validate: the module uses a feature that is not enabled"
  | .encodingFeature => "the binary uses an encoding of a feature that is not enabled"

end Silmaril.Wasm.Tools.Validate
