module

public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Text.Core.Names
public import Silmaril.Wasm.Tools.Objdump.Defs

/-!
# `wasm-tools dump`: the operator printer and the offset-recording instruction decoder

`wasm-tools dump` (wasm-tools 1.262.0, `src/bin/wasm-tools/dump.rs`) prints every operator of a
function body or constant expression on its own line, with the bytes it occupies.  The text of
an operator is wasmparser's `VisitOperator` form: the `visit_` name without its prefix, then
` arg:{:?}` for every immediate (`define_visit_operator!` in `dump.rs`).

* The Rust `Debug` forms of wasmparser's types that occur in operators and items: `valTypeDbg`
  (`I32`, `Ref(funcref)`), `refTypeDbg` (`funcref`, `(ref null (module 3))`), `heapTypeDbg`
  (`Abstract { shared: false, ty: Func }`, `Concrete(Module(0))`), `blockTypeDbg`, `memArgDbg`
  and the `Display` forms of value types (`valTypeDisp`).
* `opText i`: the line of a non-structured instruction `i` (wasmparser's operator name and
  immediates).  Names come from silmaril-lean's text keywords (`Text.Core.nullaryName`) with
  `.` replaced by `_`, which is wasmparser's naming for all of them; the immediates are spelled
  out per instruction.
* `dInstr` / `dSeq`: **silmaril-lean's instruction decoder** (`Decode.readInstr` /
  `Decode.readSeq`) **with a log**: the same recursion, reading with the same readers, and in
  addition an `Ev` (the text and the end offset of the operator) for every opcode, `end` and
  `else`, in the order of the bytes.  `DumpOps.Thms.dSeq_erase`: forgetting the log gives
  exactly `readSeq` (and `dInstr_erase`: `readInstr`); so the instructions whose bytes dump
  prints are those the certified decoder reads, and the decoder sees nothing else.

New definitions; operator names and formats transcribed from wasmparser 0.262
(`for_each_operator!` in `wasmparser/src/lib.rs`, `Debug` derivations of the reader types).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.DumpOps

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary.Core.Decode

/-! ## `Debug` and `Display` forms of wasmparser's types -/

/-- `AbstractHeapType::as_str(nullable)`. -/
def absName (nullable : Bool) : AbsHeapType → String
  | .any => "any" | .eq => "eq" | .i31 => "i31" | .struct => "struct" | .array => "array"
  | .none => if nullable then "null" else "none"
  | .func => "func" | .nofunc => if nullable then "nullfunc" else "nofunc"
  | .exn => "exn" | .noexn => if nullable then "nullexn" else "noexn"
  | .extern => "extern" | .noextern => if nullable then "nullextern" else "noextern"

/-- `AbstractHeapType`'s derived `Debug`. -/
def absDbg : AbsHeapType → String
  | .any => "Any" | .eq => "Eq" | .i31 => "I31" | .struct => "Struct" | .array => "Array"
  | .none => "None" | .func => "Func" | .nofunc => "NoFunc" | .exn => "Exn"
  | .noexn => "NoExn" | .extern => "Extern" | .noextern => "NoExtern"

/-- `RefType`'s `Debug` (= its `Display`): the short form of nullable abstract references,
`(ref …)` otherwise; concrete indices as `(module N)`. -/
def refTypeDbg (r : RefType) : String :=
  match r.heap with
  | .abstract a => if r.nullable then absName true a ++ "ref" else "(ref " ++ absName false a ++ ")"
  | .typeIdx i =>
    if r.nullable then s!"(ref null (module {i.toNat}))" else s!"(ref (module {i.toNat}))"

/-- `HeapType`'s derived `Debug`. -/
def heapTypeDbg : HeapType → String
  | .abstract a => "Abstract { shared: false, ty: " ++ absDbg a ++ " }"
  | .typeIdx i => s!"Concrete(Module({i.toNat}))"

/-- `ValType`'s derived `Debug`. -/
def valTypeDbg : ValType → String
  | .num (.int .i32) => "I32" | .num (.int .i64) => "I64"
  | .num (.float .f32) => "F32" | .num (.float .f64) => "F64"
  | .vec .v128 => "V128"
  | .ref r => "Ref(" ++ refTypeDbg r ++ ")"

/-- `ValType`'s `Display`. -/
def valTypeDisp : ValType → String
  | .num (.int .i32) => "i32" | .num (.int .i64) => "i64"
  | .num (.float .f32) => "f32" | .num (.float .f64) => "f64"
  | .vec .v128 => "v128"
  | .ref r => refTypeDbg r

/-- `BlockType`'s derived `Debug`. -/
def blockTypeDbg : BlockType → String
  | .empty => "Empty"
  | .value t => "Type(" ++ valTypeDbg t ++ ")"
  | .typeIdx i => s!"FuncType({i.toNat})"

/-- Rust's `{:?}` of a slice of numbers. -/
def listDbg (xs : List Nat) : String :=
  "[" ++ ", ".intercalate (xs.map toString) ++ "]"

/-- `MemArg`'s derived `Debug`; `maxAlign` is the natural alignment exponent of the operator. -/
def memArgDbg (maxAlign : Nat) (m : MemIdx) (a : MemArg) : String :=
  s!"MemArg \{ align: {a.align.val}, max_align: {maxAlign}, offset: {a.offset.val}, memory: {m.toNat} }"

/-- `Catch`'s derived `Debug`. -/
def catchDbg : Catch → String
  | .catch_ t l => s!"One \{ tag: {t.toNat}, label: {l.toNat} }"
  | .catchRef t l => s!"OneRef \{ tag: {t.toNat}, label: {l.toNat} }"
  | .catchAll l => s!"All \{ label: {l.toNat} }"
  | .catchAllRef l => s!"AllRef \{ label: {l.toNat} }"

/-- The 16 little-endian bytes of a 128-bit constant. -/
def v128Bytes (b : BitVec 128) : List Nat :=
  (List.range 16).map fun k => b.toNat / 2 ^ (8 * k) % 256

/-- `_` for `.`: wasmparser's `visit_` names are the text keywords with dots replaced. -/
def underscore (s : String) : String := s.map fun c => if c = '.' then '_' else c

/-! ## Operators -/

/-- The name and natural alignment exponent of a load or store, if `i` is one. -/
def memOpName : Instr → Option (String × Nat)
  | .intLoad t none _ _ => some (Text.Core.itName t ++ "_load", if t = .i32 then 2 else 3)
  | .intLoad t (some (p, s)) _ _ =>
    some (Text.Core.itName t ++ "_load" ++ toString p.width ++ "_" ++ Text.Core.sxName s,
      packLog p)
  | .floatLoad t _ _ => some (Text.Core.ftName t ++ "_load", if t = .f32 then 2 else 3)
  | .intStore t none _ _ => some (Text.Core.itName t ++ "_store", if t = .i32 then 2 else 3)
  | .intStore t (some p) _ _ => some (Text.Core.itName t ++ "_store" ++ toString p.width, packLog p)
  | .floatStore t _ _ => some (Text.Core.ftName t ++ "_store", if t = .f32 then 2 else 3)
  | .vecLoad .full _ _ => some ("v128_load", 4)
  | .vecLoad (.extend8x8 s) _ _ => some ("v128_load8x8_" ++ Text.Core.sxName s, 3)
  | .vecLoad (.extend16x4 s) _ _ => some ("v128_load16x4_" ++ Text.Core.sxName s, 3)
  | .vecLoad (.extend32x2 s) _ _ => some ("v128_load32x2_" ++ Text.Core.sxName s, 3)
  | .vecLoad (.splat p) _ _ => some ("v128_load" ++ toString p.width ++ "_splat", packLog p)
  | .vecLoad .zero32 _ _ => some ("v128_load32_zero", 2)
  | .vecLoad .zero64 _ _ => some ("v128_load64_zero", 3)
  | .vecStore _ _ => some ("v128_store", 4)
  | .vecLoadLane p _ _ _ => some ("v128_load" ++ toString p.width ++ "_lane", packLog p)
  | .vecStoreLane p _ _ _ => some ("v128_store" ++ toString p.width ++ "_lane", packLog p)
  | _ => none
where
  packLog : PackSize → Nat
    | .i8 => 0 | .i16 => 1 | .i32 => 2 | .i64 => 3

/-- The operator line of a non-structured instruction (`visit_*` name and immediates). -/
def opText (i : Instr) : String :=
  match i with
  | .select none => "select"
  | .select (some [t]) => "typed_select ty:" ++ valTypeDbg t
  | .select (some ts) => "typed_select_multi tys:[" ++ ", ".intercalate (ts.map valTypeDbg) ++ "]"
  | .br l => s!"br relative_depth:{l.toNat}"
  | .brIf l => s!"br_if relative_depth:{l.toNat}"
  | .brTable ls d =>
    s!"br_table targets:BrTable \{ count: {ls.length}, default: {d.toNat}, targets: " ++
      listDbg (ls.map (·.toNat)) ++ " }"
  | .brOnNull l => s!"br_on_null relative_depth:{l.toNat}"
  | .brOnNonNull l => s!"br_on_non_null relative_depth:{l.toNat}"
  | .brOnCast l s t =>
    s!"br_on_cast relative_depth:{l.toNat} from_ref_type:{refTypeDbg s} to_ref_type:{refTypeDbg t}"
  | .brOnCastFail l s t =>
    s!"br_on_cast_fail relative_depth:{l.toNat} from_ref_type:{refTypeDbg s} " ++
      s!"to_ref_type:{refTypeDbg t}"
  | .call f => s!"call function_index:{f.toNat}"
  | .callRef t => s!"call_ref type_index:{t.toNat}"
  | .callIndirect tb t => s!"call_indirect type_index:{t.toNat} table_index:{tb.toNat}"
  | .returnCall f => s!"return_call function_index:{f.toNat}"
  | .returnCallRef t => s!"return_call_ref type_index:{t.toNat}"
  | .returnCallIndirect tb t =>
    s!"return_call_indirect type_index:{t.toNat} table_index:{tb.toNat}"
  | .throw t => s!"throw tag_index:{t.toNat}"
  | .localGet n => s!"local_get local_index:{n.toNat}"
  | .localSet n => s!"local_set local_index:{n.toNat}"
  | .localTee n => s!"local_tee local_index:{n.toNat}"
  | .globalGet n => s!"global_get global_index:{n.toNat}"
  | .globalSet n => s!"global_set global_index:{n.toNat}"
  | .tableGet t => s!"table_get table:{t.toNat}"
  | .tableSet t => s!"table_set table:{t.toNat}"
  | .tableSize t => s!"table_size table:{t.toNat}"
  | .tableGrow t => s!"table_grow table:{t.toNat}"
  | .tableFill t => s!"table_fill table:{t.toNat}"
  | .tableCopy d s => s!"table_copy dst_table:{d.toNat} src_table:{s.toNat}"
  | .tableInit t e => s!"table_init elem_index:{e.toNat} table:{t.toNat}"
  | .elemDrop e => s!"elem_drop elem_index:{e.toNat}"
  | .intLoad _ _ m a | .intStore _ _ m a | .floatLoad _ m a | .floatStore _ m a
  | .vecLoad _ m a | .vecStore m a =>
    match memOpName i with
    | some (n, al) => n ++ " memarg:" ++ memArgDbg al m a
    | none => "??"
  | .vecLoadLane _ m a l | .vecStoreLane _ m a l =>
    match memOpName i with
    | some (n, al) => n ++ " memarg:" ++ memArgDbg al m a ++ s!" lane:{l.val}"
    | none => "??"
  | .memorySize m => s!"memory_size mem:{m.toNat}"
  | .memoryGrow m => s!"memory_grow mem:{m.toNat}"
  | .memoryFill m => s!"memory_fill mem:{m.toNat}"
  | .memoryCopy d s => s!"memory_copy dst_mem:{d.toNat} src_mem:{s.toNat}"
  | .memoryInit m d => s!"memory_init data_index:{d.toNat} mem:{m.toNat}"
  | .dataDrop d => s!"data_drop data_index:{d.toNat}"
  | .refNull h => "ref_null hty:" ++ heapTypeDbg h
  | .refTest r =>
    (if r.nullable then "ref_test_nullable hty:" else "ref_test_non_null hty:") ++ heapTypeDbg r.heap
  | .refCast r =>
    (if r.nullable then "ref_cast_nullable hty:" else "ref_cast_non_null hty:") ++ heapTypeDbg r.heap
  | .refFunc f => s!"ref_func function_index:{f.toNat}"
  | .structNew t => s!"struct_new struct_type_index:{t.toNat}"
  | .structNewDefault t => s!"struct_new_default struct_type_index:{t.toNat}"
  | .structGet s t f =>
    let n := match s with
      | none => "struct_get" | some .signed => "struct_get_s" | some .unsigned => "struct_get_u"
    n ++ s!" struct_type_index:{t.toNat} field_index:{f.toNat}"
  | .structSet t f => s!"struct_set struct_type_index:{t.toNat} field_index:{f.toNat}"
  | .arrayNew t => s!"array_new array_type_index:{t.toNat}"
  | .arrayNewDefault t => s!"array_new_default array_type_index:{t.toNat}"
  | .arrayNewFixed t n => s!"array_new_fixed array_type_index:{t.toNat} array_size:{n.val}"
  | .arrayNewData t d => s!"array_new_data array_type_index:{t.toNat} array_data_index:{d.toNat}"
  | .arrayNewElem t e => s!"array_new_elem array_type_index:{t.toNat} array_elem_index:{e.toNat}"
  | .arrayGet s t =>
    let n := match s with
      | none => "array_get" | some .signed => "array_get_s" | some .unsigned => "array_get_u"
    n ++ s!" array_type_index:{t.toNat}"
  | .arraySet t => s!"array_set array_type_index:{t.toNat}"
  | .arrayFill t => s!"array_fill array_type_index:{t.toNat}"
  | .arrayCopy d s =>
    s!"array_copy array_type_index_dst:{d.toNat} array_type_index_src:{s.toNat}"
  | .arrayInitData t d =>
    s!"array_init_data array_type_index:{t.toNat} array_data_index:{d.toNat}"
  | .arrayInitElem t e =>
    s!"array_init_elem array_type_index:{t.toNat} array_elem_index:{e.toNat}"
  | .intConst .i32 b => s!"i32_const value:{b.toInt}"
  | .intConst .i64 b => s!"i64_const value:{b.toInt}"
  | .floatConst .f32 b => s!"f32_const value:Ieee32({b.toNat})"
  | .floatConst .f64 b => s!"f64_const value:Ieee64({b.toNat})"
  | .vecConst b => "v128_const value:V128(" ++ listDbg (v128Bytes b) ++ ")"
  | .vecShuffle ls => "i8x16_shuffle lanes:" ++ listDbg (ls.map (·.val))
  | .vecExtractLane sh s l =>
    Text.Core.shName sh ++ "_extract_lane" ++
      (match s with | none => "" | some s => "_" ++ Text.Core.sxName s) ++ s!" lane:{l.val}"
  | .vecReplaceLane sh l => Text.Core.shName sh ++ s!"_replace_lane lane:{l.val}"
  | _ =>
    match Text.Core.nullaryName i with
    | some n => underscore n
    | none => "??"

/-- The line of a structured instruction's opening operator. -/
def blockText (kw : String) (bt : BlockType) : String := kw ++ " blockty:" ++ blockTypeDbg bt

/-- The line of `try_table`. -/
def tryTableText (bt : BlockType) (cs : List Catch) : String :=
  "try_table try_table:TryTable { ty: " ++ blockTypeDbg bt ++ ", catches: [" ++
    ", ".intercalate (cs.map catchDbg) ++ "] }"

/-! ## The decoder with a log -/

/-- One printed operator: its text and the offset just past its bytes. -/
structure Ev where
  text : String
  stop : Nat
  deriving Repr, Inhabited

/-- The cursor position. -/
def curPos : DecodeM Nat := do pure (← get).pos

mutual
/-- `Decode.readInstr` with a log: one instruction whose opcode `op` has been read, and the
operator lines of its bytes (the opening operator, then the body's lines). -/
def dInstr (fuel : Nat) (op : Nat) : DecodeM (Instr × List Ev) :=
  match fuel with
  | 0 => decodeError "out of fuel"
  | fuel + 1 =>
    match op with
    | 0x02 => do
      let bt ← readBlockType
      let p ← curPos
      let ((body, t), es) ← dSeq fuel
      if t == 0x0B then pure (.block bt body, ⟨blockText "block" bt, p⟩ :: es)
      else decodeError "`else` inside `block`"
    | 0x03 => do
      let bt ← readBlockType
      let p ← curPos
      let ((body, t), es) ← dSeq fuel
      if t == 0x0B then pure (.loop bt body, ⟨blockText "loop" bt, p⟩ :: es)
      else decodeError "`else` inside `loop`"
    | 0x04 => do
      let bt ← readBlockType
      let p ← curPos
      let ((thn, t), es) ← dSeq fuel
      if t == 0x0B then pure (.if_ bt thn [], ⟨blockText "if" bt, p⟩ :: es)
      else
        let ((els, t'), es') ← dSeq fuel
        if t' == 0x0B then pure (.if_ bt thn els, ⟨blockText "if" bt, p⟩ :: (es ++ es'))
        else decodeError "second `else` in `if`"
    | 0x1F => do
      let bt ← readBlockType
      let cs ← readVec readCatch
      let p ← curPos
      let ((body, t), es) ← dSeq fuel
      if t == 0x0B then pure (.tryTable bt cs body, ⟨tryTableText bt cs, p⟩ :: es)
      else decodeError "`else` inside `try_table`"
    | op => do
      let i ← readPlain op
      let p ← curPos
      pure (i, [⟨opText i, p⟩])
/-- `Decode.readSeq` with a log: instructions up to and including a terminator, and the
operator lines of all of them (the terminator's `end`/`else` line last). -/
def dSeq (fuel : Nat) : DecodeM ((List Instr × UInt8) × List Ev) :=
  match fuel with
  | 0 => decodeError "out of fuel"
  | fuel + 1 => do
    let b ← readByte
    if b == 0x0B || b == 0x05 then
      let p ← curPos
      pure (([], b), [⟨if b == 0x0B then "end" else "else", p⟩])
    else
      let (i, es) ← dInstr fuel b.toNat
      let ((rest, t), es') ← dSeq fuel
      pure ((i :: rest, t), es ++ es')
end

/-- `Decode.readExpr` with a log. -/
def dExpr : DecodeM (Expr × List Ev) := do
  let ((is, t), es) ← dSeq ((← remaining) + 1)
  if t == 0x0B then pure (is, es) else decodeError "`else` outside `if`"

end Silmaril.Wasm.Tools.DumpOps
