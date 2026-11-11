module

public import Silmaril.Wasm.Tools.OpTable.Defs
public import Silmaril.Wasm.Tools.RustDebug.Defs
public import Silmaril.Wasm.Tools.DumpOps.Defs

/-!
# `wasm-tools dump`: wasmparser's reader, transcribed

`dump` reads every item of a module with wasmparser 0.262's readers (all features enabled, as
`Parser::new` does). This module transcribes those readers, for the whole of what wasmparser
reads, beyond silmaril-lean's Core 3.0 model: shared types and references (shared-everything
threads), exact references and descriptor types (custom descriptors), continuation types
(stack switching), custom page sizes, compact imports, and every operator of the operator
table (`OpTable`, generated from wasmparser's sources), threads and atomics, legacy
exceptions, wide arithmetic and stack switching included.

* `R`: a reader over the bytes `[_, lim)` whose position survives a failure (wasmparser's
  `BinaryReader`: `dump` prints `??` for an operator that fails and goes on from where the
  reader stopped);
* the LEB128 readers with wasmparser's limits and failure positions (`varU32`, `varU64`,
  `varS32`, `varS33`, `varS64`), `str` (`read_string`);
* the types (`HT`, `RT`, `VT` and the `Debug`/`Display` forms), `subTypeR`, `tableTypeR`,
  `memTypeR`, `globalTypeR`, `tagTypeR`, `typeRefR` (`TypeRef` of imports);
* `opR frames`: one operator and the new control frame stack (`FrameStackAdapter`).

This transcription is not verified; the walker uses it for items, and for operators only
where the certified decoder with a log (`DumpOps.dExpr`) does not read the whole body.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.DumpFlat

open Silmaril.Wasm.Tools.OpTable (Imm)
open Silmaril.Wasm.Tools.DumpOps (listDbg)

/-- The bytes and the end of the readable range. -/
structure Env where
  b : ByteArray
  lim : Nat

/-- wasmparser's `BinaryReader`: failure keeps the position. -/
abbrev R := ReaderT Env (ExceptT String (StateM Nat))

def pos : R Nat := get

/-- Fail with wasmparser's `{message} (at offset 0x…)`, at offset `at_`. -/
def bailAt {α : Type} (msg : String) (at_ : Nat) : R α :=
  throw s!"{msg} (at offset 0x{RustDebug.hexDigits at_})"

/-- Fail at the current position. -/
def bail {α : Type} (msg : String) : R α := do bailAt msg (← get)

def eof : R Bool := do pure ((← get) ≥ (← read).lim)

def u8 : R Nat := do
  let e ← read
  let p ← get
  if p < e.lim ∧ p < e.b.size then
    set (p + 1); pure e.b[p]!.toNat
  else bail "unexpected end-of-file"

def peek : R Nat := do
  let e ← read
  let p ← get
  if p < e.lim ∧ p < e.b.size then pure e.b[p]!.toNat else bail "unexpected end-of-file"

/-- An unsigned LEB128 of at most `bits` bits, as `read_var_u32`/`read_var_u64`. -/
def varU (bits : Nat) : R Nat := do
  let mut result := 0
  let mut shift := 0
  for _ in [0:(bits + 6) / 7] do
    let x ← u8
    result := result + (x % 128) * 2 ^ shift
    if shift + 7 ≥ bits && x / 2 ^ (bits - shift) != 0 then
      if x ≥ 128 then bailAt s!"invalid var_u{bits}: integer representation too long" ((← get) - 1)
      else bailAt s!"invalid var_u{bits}: integer too large" ((← get) - 1)
    if x < 128 then return result
    shift := shift + 7
  pure result

def varU32 : R Nat := varU 32
def varU64 : R Nat := varU 64

/-- A signed LEB128 of at most `bits` bits, as `read_var_i32`/`read_var_s33`/`read_var_i64`. -/
def varS (bits : Nat) (name : String) : R Int := do
  let mut result : Nat := 0
  let mut shift := 0
  for _ in [0:(bits + 6) / 7] do
    let x ← u8
    result := result + (x % 128) * 2 ^ shift
    if shift + 7 ≥ bits then
      -- the last byte: no continuation, and its unused bits are the sign extension
      let cont := x ≥ 128
      let rest := (x % 128) / 2 ^ (bits - 1 - shift)
      let allOnes := 2 ^ (7 - (bits - 1 - shift)) - 1
      if cont || (rest != 0 && rest != allOnes) then
        if cont then bailAt s!"invalid var_{name}: integer representation too long" ((← get) - 1)
        else bailAt s!"invalid var_{name}: integer too large" ((← get) - 1)
      let total := shift + 7
      return (if result ≥ 2 ^ (total - 1) then (result : Int) - 2 ^ total else result)
    if x < 128 then
      let total := shift + 7
      return (if result ≥ 2 ^ (total - 1) then (result : Int) - 2 ^ total else result)
    shift := shift + 7
  pure result

def varS32 : R Int := varS 32 "i32"
def varS33 : R Int := varS 33 "s33"
def varS64 : R Int := varS 64 "i64"

def bytes (n : Nat) : R ByteArray := do
  let e ← read
  let p ← get
  if p + n ≤ e.lim ∧ p + n ≤ e.b.size then
    set (p + n); pure (e.b.extract p (p + n))
  else bail "unexpected end-of-file"

/-- `read_unlimited_string`. -/
def ustr : R String := do
  let n ← varU32
  let p ← get
  let bs ← bytes n
  match String.fromUTF8? bs with
  | some s => pure s
  | none => bailAt "malformed UTF-8 encoding" p

/-- `read_string` (at most 100,000 bytes). -/
def str : R String := do
  let p ← get
  let n ← varU32
  if n > 100000 then bailAt "string size out of bounds" ((← get) - 1)
  set p
  ustr

/-- A vector count (`read_size`, with wasmparser's limit `max`). -/
def size (max : Nat) (desc : String) : R Nat := do
  let n ← varU32
  if n > max then bail s!"{desc} size is out of bounds"
  pure n

/-! ## Types -/

/-- `AbstractHeapType`. -/
inductive AH where
  | func | extern | any | none | noextern | nofunc | eq | struct | array | i31 | exn | noexn
  | cont | nocont
  deriving Repr, Inhabited, BEq

def AH.dbg : AH → String
  | .func => "Func" | .extern => "Extern" | .any => "Any" | .none => "None"
  | .noextern => "NoExtern" | .nofunc => "NoFunc" | .eq => "Eq" | .struct => "Struct"
  | .array => "Array" | .i31 => "I31" | .exn => "Exn" | .noexn => "NoExn" | .cont => "Cont"
  | .nocont => "NoCont"

/-- `as_str(nullable)`. -/
def AH.name (nullable : Bool) : AH → String
  | .any => "any" | .none => if nullable then "null" else "none"
  | .noextern => if nullable then "nullextern" else "noextern"
  | .nofunc => if nullable then "nullfunc" else "nofunc"
  | .eq => "eq" | .struct => "struct" | .array => "array" | .i31 => "i31" | .extern => "extern"
  | .func => "func" | .exn => "exn" | .noexn => if nullable then "nullexn" else "noexn"
  | .cont => "cont" | .nocont => if nullable then "nullcont" else "nocont"

/-- `HeapType`. -/
inductive HT where
  | abs (shared : Bool) (a : AH)
  | concrete (i : Nat)
  | exact (i : Nat)
  deriving Repr, Inhabited

def HT.dbg : HT → String
  | .abs s a => s!"Abstract \{ shared: {s}, ty: {a.dbg} }"
  | .concrete i => s!"Concrete(Module({i}))"
  | .exact i => s!"Exact(Module({i}))"

structure RT where
  nullable : Bool
  heap : HT
  deriving Repr, Inhabited

/-- `RefType`'s `Debug` (= `Display`). -/
def RT.dbg (r : RT) : String :=
  match r.heap with
  | .abs shared a =>
    let n := a.name r.nullable
    match r.nullable, shared with
    | true, true => s!"(shared {n}ref)"
    | true, false => s!"{n}ref"
    | false, true => s!"(ref (shared {n}))"
    | false, false => s!"(ref {n})"
  | .concrete i => if r.nullable then s!"(ref null (module {i}))" else s!"(ref (module {i}))"
  | .exact i => s!"(ref (exact (module {i})))"

inductive VT where
  | i32 | i64 | f32 | f64 | v128
  | ref (r : RT)
  deriving Repr, Inhabited

def VT.dbg : VT → String
  | .i32 => "I32" | .i64 => "I64" | .f32 => "F32" | .f64 => "F64" | .v128 => "V128"
  | .ref r => "Ref(" ++ r.dbg ++ ")"

def VT.disp : VT → String
  | .i32 => "i32" | .i64 => "i64" | .f32 => "f32" | .f64 => "f64" | .v128 => "v128"
  | .ref r => r.dbg

def ahR : R AH := do
  match ← u8 with
  | 0x70 => pure .func | 0x6F => pure .extern | 0x6E => pure .any | 0x71 => pure .none
  | 0x72 => pure .noextern | 0x73 => pure .nofunc | 0x6D => pure .eq | 0x6B => pure .struct
  | 0x6A => pure .array | 0x6C => pure .i31 | 0x69 => pure .exn | 0x74 => pure .noexn
  | 0x68 => pure .cont | 0x75 => pure .nocont
  | _ => bail "invalid abstract heap type"

/-- `HeapType::from_reader`: an `s33` index if non-negative, else `0x65` (shared), `0x62`
(exact) or an abstract heap type. -/
def heapR : R HT := do
  let p ← get
  let x ← varS33
  if 0 ≤ x ∧ x < 2 ^ 32 then pure (.concrete x.toNat)
  else
    set p
    match ← peek with
    | 0x65 => do let _ ← u8; pure (.abs true (← ahR))
    | 0x62 => do let _ ← u8; pure (.exact (← varU32))
    | _ => pure (.abs false (← ahR))

def refR : R RT := do
  match ← peek with
  | 0x63 => do let _ ← u8; pure ⟨true, ← heapR⟩
  | 0x64 => do let _ ← u8; pure ⟨false, ← heapR⟩
  | 0x62 => bail "unexpected exact type"
  | b => do
    let shared := b == 0x65
    if shared then let _ ← u8
    pure ⟨true, .abs shared (← ahR)⟩

def valR : R VT := do
  match ← peek with
  | 0x7F => do let _ ← u8; pure .i32
  | 0x7E => do let _ ← u8; pure .i64
  | 0x7D => do let _ ← u8; pure .f32
  | 0x7C => do let _ ← u8; pure .f64
  | 0x7B => do let _ ← u8; pure .v128
  | _ => pure (.ref (← refR))

/-- A vector of `f`. -/
def vecR {α : Type} (max : Nat) (desc : String) (f : R α) : R (List α) := do
  let n ← size max desc
  let mut acc : Array α := #[]
  for _ in [0:n] do acc := acc.push (← f)
  pure acc.toList

/-- `PackedIndex`'s `Debug` (a module type index). -/
def packedDbg (i : Nat) : String := s!"CoreTypeIndex \{ kind: \"module\", index: {i} }"

/-- `StorageType`, read: its `Display` and `Debug`. -/
def storageR : R (String × String) := do
  match ← peek with
  | 0x78 => do let _ ← u8; pure ("i8", "I8")
  | 0x77 => do let _ ← u8; pure ("i16", "I16")
  | _ => do let t ← valR; pure (t.disp, "Val(" ++ t.dbg ++ ")")

/-- `FieldType`, read: its `Display` and `Debug`. -/
def fieldR : R (String × String) := do
  let (sd, sg) ← storageR
  let m ← match ← u8 with
    | 0 => pure false
    | 1 => pure true
    | _ => bail "malformed mutability byte for field type"
  pure (if m then s!"(mut {sd})" else sd, s!"FieldType \{ element_type: {sg}, mutable: {m} }")

def optIdxDbg : Option Nat → String
  | none => "None"
  | some i => "Some(" ++ packedDbg i ++ ")"

/-- `read_composite_type`: `CompositeType`'s `Display` and `Debug`. -/
def compositeR (op0 : Nat) : R (String × String) := do
  let (shared, op) ← if op0 == 0x65 then do pure (true, ← u8) else pure (false, op0)
  let (describes, op) ← if op == 0x4C then do
      let i ← varU32; pure (some i, ← u8) else pure (none, op)
  let (descriptor, op) ← if op == 0x4D then do
      let i ← varU32; pure (some i, ← u8) else pure (none, op)
  let (inner, innerDbg) ← match op with
    | 0x60 => do
      let ps ← vecR 1000 "function params" valR
      let rs ← vecR 1000 "function returns" valR
      pure ("(func" ++
        (if ps.isEmpty then "" else " (param" ++ String.join (ps.map (" " ++ ·.disp)) ++ ")") ++
        (if rs.isEmpty then "" else " (result" ++ String.join (rs.map (" " ++ ·.disp)) ++ ")") ++
        ")",
        "Func(FuncType { params: [" ++ ", ".intercalate (ps.map (·.dbg)) ++ "], results: [" ++
          ", ".intercalate (rs.map (·.dbg)) ++ "] })")
    | 0x5E => do
      let (fd, fg) ← fieldR
      pure ("(array " ++ fd ++ ")", "Array(ArrayType(" ++ fg ++ "))")
    | 0x5F => do
      let fs ← vecR 10000 "struct fields" fieldR
      pure ("(struct" ++ String.join (fs.map (" " ++ ·.1)) ++ ")",
        "Struct(StructType { fields: [" ++ ", ".intercalate (fs.map (·.2)) ++ "] })")
    | 0x5D => do
      let x ← varS33
      unless 0 ≤ x ∧ x < 2 ^ 32 do bail "invalid continuation type"
      pure (s!"(cont (module {x.toNat}))", "Cont(ContType(" ++ packedDbg x.toNat ++ "))")
    | x => bail s!"invalid leading byte (0x{RustDebug.hexDigits x}) for type"
  pure (if shared then "(shared " ++ inner ++ ")" else inner,
    "CompositeType { inner: " ++ innerDbg ++ s!", shared: {shared}, descriptor_idx: " ++
      optIdxDbg descriptor ++ ", describes_idx: " ++ optIdxDbg describes ++ " }")

/-- `SubType`, read: its `Display` and `Debug`. -/
def subTypeR2 : R (String × String) := do
  let (fin, ss, c) ← match ← u8 with
    | 0x4F => do
      let ss ← vecR 5 "supertype idxs" varU32
      pure (true, some ss, ← compositeR (← u8))
    | 0x50 => do
      let ss ← vecR 5 "supertype idxs" varU32
      pure (false, some ss, ← compositeR (← u8))
    | op => do pure (true, none, ← compositeR op)
  let sups := ss.getD []
  let disp := if fin && sups.isEmpty then c.1
    else "(sub " ++ (if fin then "final " else "") ++
      String.join (sups.map fun i => s!"(module {i}) ") ++ c.1 ++ ")"
  pure (disp, s!"SubType \{ is_final: {fin}, supertype_idxs: [" ++
    ", ".intercalate (sups.map packedDbg) ++ "], composite_type: " ++ c.2 ++ " }")

/-- `SubType`'s `Display`, read. -/
def subTypeR : R String := do pure (← subTypeR2).1

def optDbg : Option Nat → String
  | none => "None"
  | some n => s!"Some({n})"

/-- `TableType`'s `Debug`, read. -/
def tableTypeR : R String := do
  let et ← refR
  let f ← u8
  if f ≥ 8 then bail "invalid table resizable limits flags"
  let ini ← varU64
  let mx ← if f % 2 == 1 then do pure (some (← varU64)) else pure none
  pure s!"TableType \{ element_type: {et.dbg}, table64: {f / 4 % 2 == 1}, initial: {ini}, maximum: {optDbg mx}, shared: {f / 2 % 2 == 1} }"

/-- `MemoryType`'s `Debug`, read. -/
def memTypeR : R String := do
  let f ← u8
  if f ≥ 16 then bail "invalid memory limits flags"
  let ini ← varU64
  let mx ← if f % 2 == 1 then do pure (some (← varU64)) else pure none
  let ps ← if f / 8 % 2 == 1 then do
      let v ← varU32
      if v ≥ 64 then bail "invalid custom page size"
      pure (some v)
    else pure none
  pure s!"MemoryType \{ memory64: {f / 4 % 2 == 1}, shared: {f / 2 % 2 == 1}, initial: {ini}, maximum: {optDbg mx}, page_size_log2: {optDbg ps} }"

/-- `GlobalType`'s `Debug`, read. -/
def globalTypeR : R String := do
  let t ← valR
  let f ← u8
  if f > 3 then bail "malformed global flags"
  pure s!"GlobalType \{ content_type: {t.dbg}, mutable: {f % 2 == 1}, shared: {f / 2 == 1} }"

def tagTypeR : R String := do
  unless (← u8) == 0 do bail "invalid tag attributes"
  pure s!"TagType \{ kind: Exception, func_type_idx: {← varU32} }"

/-- The kind of an import: its index-space name (`func`, `func_exact`, …) and `TypeRef`'s
`Debug`. -/
def typeRefR : R (String × String) := do
  match ← u8 with
  | 0x00 => pure ("func", s!"Func({← varU32})")
  | 0x20 => pure ("func_exact", s!"FuncExact({← varU32})")
  | 0x01 => pure ("table", s!"Table({← tableTypeR})")
  | 0x02 => pure ("memory", s!"Memory({← memTypeR})")
  | 0x03 => pure ("global", s!"Global({← globalTypeR})")
  | 0x04 => pure ("tag", s!"Tag({← tagTypeR})")
  | x => bail s!"invalid leading byte (0x{RustDebug.hexDigits x}) for external kind"

/-- `ExternalKind`'s `Debug` of an export. -/
def exportKindR : R String := do
  match ← u8 with
  | 0x00 => pure "Func" | 0x01 => pure "Table" | 0x02 => pure "Memory" | 0x03 => pure "Global"
  | 0x04 => pure "Tag"
  | 0x20 => bail "Exact type is not allowed in the exports"
  | x => bail s!"invalid leading byte (0x{RustDebug.hexDigits x}) for external kind"

/-! ## Operators -/

/-- `BlockType`'s `Debug`, read (`read_block_type`). -/
def blockTypeR : R String := do
  let b ← peek
  if b < 0x80 && b ≥ 0x40 then
    if b == 0x40 then do let _ ← u8; pure "Empty"
    else pure ("Type(" ++ (← valR).dbg ++ ")")
  else
    let x ← varS33
    if 0 ≤ x ∧ x < 2 ^ 32 then pure s!"FuncType({x.toNat})" else bail "invalid function type"

def memArgR (maxAlign : Nat) : R String := do
  let f ← varU32
  let (f, mem) ← if f / 64 % 2 == 1 then do pure (f - 64, ← varU32) else pure (f, 0)
  if f ≥ 64 then bail "malformed memop alignment: alignment too large"
  let off ← varU64
  pure s!"MemArg \{ align: {f}, max_align: {maxAlign}, offset: {off}, memory: {mem} }"

def catchR : R String := do
  match ← u8 with
  | 0 => do let t ← varU32; let l ← varU32; pure s!"One \{ tag: {t}, label: {l} }"
  | 1 => do let t ← varU32; let l ← varU32; pure s!"OneRef \{ tag: {t}, label: {l} }"
  | 2 => do let l ← varU32; pure s!"All \{ label: {l} }"
  | 3 => do let l ← varU32; pure s!"AllRef \{ label: {l} }"
  | x => bail s!"invalid leading byte (0x{RustDebug.hexDigits x}) for catch"

def handleR : R String := do
  match ← u8 with
  | 0 => do let t ← varU32; let l ← varU32; pure s!"OnLabel \{ tag: {t}, label: {l} }"
  | 1 => do let t ← varU32; pure s!"OnSwitch \{ tag: {t} }"
  | x => bail s!"invalid leading byte (0x{RustDebug.hexDigits x}) for on clause"

def littleEndian (bs : ByteArray) : Nat :=
  bs.toList.foldr (fun x acc => acc * 256 + x.toNat) 0

/-- One immediate, read and printed (`{:?}`). -/
def immR : Imm → R String
  | .u32 => do pure (toString (← varU32))
  | .i32 => do pure (toString (← varS32))
  | .i64 => do pure (toString (← varS64))
  | .f32 => do pure s!"Ieee32({littleEndian (← bytes 4)})"
  | .f64 => do pure s!"Ieee64({littleEndian (← bytes 8)})"
  | .v128 => do pure ("V128(" ++ listDbg ((← bytes 16).toList.map (·.toNat)) ++ ")")
  | .blockty => blockTypeR
  | .brtable => do
    let n ← size 1000000 "br_table"
    let mut ts : Array Nat := #[]
    for _ in [0:n] do ts := ts.push (← varU32)
    let d ← varU32
    pure s!"BrTable \{ count: {n}, default: {d}, targets: {listDbg ts.toList} }"
  | .lane => do pure (toString (← u8))
  | .ordering => do
    match ← varU32 with
    | 0 => pure "SeqCst"
    | 1 => pure "AcqRel"
    | x => bail s!"invalid atomic consistency ordering {x}"
  | .memarg m => memArgR m
  | .heap => do pure (← heapR).dbg
  | .val => do pure (← valR).dbg
  | .ref => do pure (← refR).dbg
  | .trytable => do
    let bt ← blockTypeR
    let cs ← vecR 10000 "catches" catchR
    pure ("TryTable { ty: " ++ bt ++ ", catches: [" ++ ", ".intercalate cs ++ "] }")
  | .resumetable => do
    let hs ← vecR 10000 "resume table" handleR
    pure ("ResumeTable { handlers: [" ++ ", ".intercalate hs ++ "] }")

/-- Control frames (`FrameKind`). -/
inductive Frame where
  | block | loop | if_ | else_ | legacyTry | legacyCatch | legacyCatchAll | tryTable
  deriving Repr, BEq, Inhabited

def frameName : Frame → String
  | .block => "Block" | .loop => "Loop" | .if_ => "If" | .else_ => "Else"
  | .legacyTry => "LegacyTry" | .legacyCatch => "LegacyCatch"
  | .legacyCatchAll => "LegacyCatchAll" | .tryTable => "TryTable"

/-- The three immediates of a cast branch (`br_on_cast` and its kin). -/
def castR : R String := do
  let f ← u8
  let d ← varU32
  if f > 3 then bail "invalid cast flags"
  let h1 ← heapR
  let h2 ← heapR
  pure s!"relative_depth:{d} from_ref_type:{(RT.mk (f % 2 == 1) h1).dbg} to_ref_type:{(RT.mk (f / 2 == 1) h2).dbg}"

/-- A table row: its name and immediates. -/
def rowR (name : String) (imms : List (String × Imm)) : R String := do
  let mut s := name
  for (n, k) in imms do
    s := s ++ " " ++ n ++ ":" ++ (← immR k)
  pure s

/-- One operator at the current position, given the control frames (innermost last): its
text and the frames after it. Fails (keeping the position) where wasmparser's reader fails. -/
def opR (frames : List Frame) : R (String × List Frame) := do
  if frames.isEmpty then bail "operators remaining after end of function body or expression"
  let expect (k : Frame) (what : String) : R Unit := do
    unless frames.getLast? == some k do
      bail s!"`{what}` found outside `{frameName k}` block"
  let top := frames.dropLast
  let code ← u8
  match code with
  | 0x02 => do pure ("block blockty:" ++ (← blockTypeR), frames ++ [.block])
  | 0x03 => do pure ("loop blockty:" ++ (← blockTypeR), frames ++ [.loop])
  | 0x04 => do pure ("if blockty:" ++ (← blockTypeR), frames ++ [.if_])
  | 0x05 => do expect .if_ "else"; pure ("else", top ++ [.else_])
  | 0x06 => do pure ("try blockty:" ++ (← blockTypeR), frames ++ [.legacyTry])
  | 0x07 => do
    unless frames.getLast? == some .legacyCatch do expect .legacyTry "catch"
    pure (s!"catch tag_index:{← varU32}", top ++ [.legacyCatch])
  | 0x0B => pure ("end", top)
  | 0x18 => do expect .legacyTry "delegate"; pure (s!"delegate relative_depth:{← varU32}", top)
  | 0x19 => do
    unless frames.getLast? == some .legacyCatch do expect .legacyTry "catch_all"
    pure ("catch_all", top ++ [.legacyCatchAll])
  | 0x1C => do
    let n ← size 10 "select types"
    if n == 1 then pure ("typed_select ty:" ++ (← valR).dbg, frames)
    else
      let mut ts : Array String := #[]
      for _ in [0:n] do ts := ts.push (← valR).dbg
      pure ("typed_select_multi tys:[" ++ ", ".intercalate ts.toList ++ "]", frames)
  | 0x1F => do pure ("try_table try_table:" ++ (← immR .trytable), frames ++ [.tryTable])
  | 0xFB | 0xFC | 0xFD | 0xFE => do
    let sub ← varU32
    if code == 0xFB && (sub == 0x18 || sub == 0x19 || sub == 0x25 || sub == 0x26) then
      let name := match sub with
        | 0x18 => "br_on_cast" | 0x19 => "br_on_cast_fail" | 0x25 => "br_on_cast_desc_eq"
        | _ => "br_on_cast_desc_eq_fail"
      pure (name ++ " " ++ (← castR), frames)
    else if code == 0xFD && sub == 0x0D then
      let mut ls : Array Nat := #[]
      for _ in [0:16] do ls := ls.push (← u8)
      pure ("i8x16_shuffle lanes:" ++ listDbg ls.toList, frames)
    else if code == 0xFE && sub == 0x03 then
      unless (← u8) == 0 do bail "nonzero byte after `atomic.fence`"
      pure ("atomic_fence", frames)
    else
      match OpTable.table.get? (code, sub) with
      | some (n, is) => pure (← rowR n is, frames)
      | none => bail s!"unknown 0x{RustDebug.hexDigits code} subopcode: 0x{RustDebug.hexDigits sub}"
  | _ =>
    match OpTable.table.get? (0, code) with
    | some (n, is) => do
      let s ← rowR n is
      -- `block`-like rows of the table never occur (all are special above)
      pure (s, frames)
    | none => bail s!"illegal opcode: 0x{RustDebug.hexDigits code}"

/-- Run a reader on `[p, lim)`: the result or the error, and the position reached. -/
def runR {α : Type} (m : R α) (b : ByteArray) (lim p : Nat) : Except String α × Nat :=
  (m.run ⟨b, lim⟩).run.run p

end Silmaril.Wasm.Tools.DumpFlat
