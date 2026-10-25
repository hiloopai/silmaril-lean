module

public import Silmaril.Wasm.Text.Core.Modules
public import Silmaril.Wasm.Text.ValuesExamplesLemmas
public import Silmaril.Wasm.Wat.Print.Common

@[expose] public section

/-! Canonical anonymous, numeric-index WAT for a checked Core module fragment.
All literal spellings are checked against the existing text literal relations'
executable candidate lists. Unsupported source fields fail explicitly.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit.Wat

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Formats.SExpEncoding (doc)

instance (names : List (Option String)) : Decidable (Distinct names) :=
  inferInstanceAs (Decidable ((names.filterMap id).Nodup))

instance (I : Text.Core.IdCtx) : Decidable I.Ok :=
  inferInstanceAs (Decidable (Distinct I.types ∧ Distinct I.tags ∧ Distinct I.globals ∧
    Distinct I.mems ∧ Distinct I.tables ∧ Distinct I.funcs ∧ Distinct I.datas ∧
    Distinct I.elems ∧ Distinct I.locals ∧ Distinct I.labels ∧ ∀ f ∈ I.fields, Distinct f))

def unsignedSyntax? (width n : Nat) : Option SExp :=
  let text := toString n
  if n ∈ ValuesExamples.unCands width text.toList then some (K text) else none

def bitsSyntax? {width : Nat} (bits : BitVec width) : Option SExp :=
  let text := toString bits.toNat
  if bits ∈ ValuesExamples.inCands width text.toList then some (K text) else none

/-- Exact IEEE bitpattern spelling from the existing printer, independently
checked against the formal WAT floating literal relation before acceptance. -/
def floatBitsSyntax? (t : FloatType) (bits : BitVec t.width) : Option SExp :=
  let text := match t with
    | .f32 => Silmaril.Wasm.Wat.Print.f32Bits bits
    | .f64 => Silmaril.Wasm.Wat.Print.f64Bits bits
  if bits ∈ ValuesExamples.fnCands t text.toList then some (K text) else none

def indexSyntax? {k : IndexKind} (i : Wasm.Idx k) : Option SExp := unsignedSyntax? 32 i.toNat

def heapSyntax? : HeapType → Option SExp
  | .abstract a => some (K (match a with
      | .any => "any" | .eq => "eq" | .i31 => "i31" | .struct => "struct"
      | .array => "array" | .none => "none" | .func => "func" | .nofunc => "nofunc"
      | .exn => "exn" | .noexn => "noexn" | .extern => "extern" | .noextern => "noextern"))
  | .typeIdx i => indexSyntax? i

def refSyntax? (r : RefType) : Option SExp := do
  let heap ← heapSyntax? r.heap
  pure (L (K "ref" :: (if r.nullable then [K "null"] else []) ++ [heap]))

def valueSyntax? : ValType → Option SExp
  | .num (.int .i32) => some (K "i32")
  | .num (.int .i64) => some (K "i64")
  | .num (.float .f32) => some (K "f32")
  | .num (.float .f64) => some (K "f64")
  | .vec .v128 => some (K "v128")
  | .ref r => refSyntax? r

def compositeNames : CompositeType → List (Option String)
  | .struct fs => fs.map fun _ => none
  | _ => []

def typeContext (rt : RecType) : Text.Core.IdCtx :=
  { types := rt.types.map fun _ => none,
    fields := rt.types.map fun st => compositeNames st.body,
    typedefs := (List.range rt.types.length).map fun i => some (rt, i) }

def typeFields (types : List RecType) : List Text.Core.FieldOut :=
  types.map fun rt => ([.type rt], typeContext rt, [])

def functionFields (funcs : List Func) : List Text.Core.FieldOut :=
  funcs.map fun f => ([.func f], { funcs := [none] }, [])

def exportFields (exports : List Export) : List Text.Core.FieldOut :=
  exports.map fun e => ([.export_ e], {}, [])

def moduleFields (types : List RecType) (funcs : List Func) (exports : List Export) :
    List Text.Core.FieldOut := typeFields types ++ functionFields funcs ++ exportFields exports

def moduleContext (types : List RecType) (funcs : List Func) (exports : List Export) :
    Text.Core.IdCtx := Text.Core.IdCtx.concat ((moduleFields types funcs exports).map (·.2.1))

/-- Context contributed by supported explicit anonymous imports. -/
def importContext (im : Import) : Text.Core.IdCtx :=
  match im.type with
  | .func _ => { funcs := [none] }
  | .global _ => { globals := [none] }
  | .memory _ => { mems := [none] }
  | .table _ => { tables := [none] }
  | .tag _ => { tags := [none] }

def importFields (imports : List Import) : List Text.Core.FieldOut :=
  imports.map fun im => ([.import_ im], importContext im, [])

/-- Generalized field assembly. The original `moduleFields` remains the
zero-import API with its original signature. -/
def moduleFieldsWithImports (types : List RecType) (imports : List Import)
    (funcs : List Func) (exports : List Export) : List Text.Core.FieldOut :=
  typeFields types ++ importFields imports ++ functionFields funcs ++ exportFields exports

def moduleContextWithImports (types : List RecType) (imports : List Import)
    (funcs : List Func) (exports : List Export) : Text.Core.IdCtx :=
  Text.Core.IdCtx.concat ((moduleFieldsWithImports types imports funcs exports).map (·.2.1))

def memoryFields (memories : List MemoryType) : List Text.Core.FieldOut :=
  memories.map fun m => ([.mem m], { mems := [none] }, [])

/-- Canonical ordering with defined memories between imports and functions.
The previous field/context APIs remain available unchanged. -/
def moduleFieldsWithMemories (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (funcs : List Func) (exports : List Export) :
    List Text.Core.FieldOut :=
  typeFields types ++ importFields imports ++ memoryFields memories ++
    functionFields funcs ++ exportFields exports

def moduleContextWithMemories (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (funcs : List Func) (exports : List Export) : Text.Core.IdCtx :=
  Text.Core.IdCtx.concat
    ((moduleFieldsWithMemories types imports memories funcs exports).map (·.2.1))

def globalFields (globals : List Global) : List Text.Core.FieldOut :=
  globals.map fun g => ([.global g], { globals := [none] }, [])

/-- Add defined globals after memories, retaining all previous field APIs. -/
def moduleFieldsWithGlobals (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (exports : List Export) : List Text.Core.FieldOut :=
  typeFields types ++ importFields imports ++ memoryFields memories ++ globalFields globals ++
    functionFields funcs ++ exportFields exports

def moduleContextWithGlobals (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (exports : List Export) : Text.Core.IdCtx :=
  Text.Core.IdCtx.concat
    ((moduleFieldsWithGlobals types imports memories globals funcs exports).map (·.2.1))

def dataFields (data : List Data) : List Text.Core.FieldOut :=
  data.map fun d => ([.data d], { datas := [none] }, [])

/-- Data segments follow functions and precede separate exports. -/
def moduleFieldsWithData (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (data : List Data) (exports : List Export) : List Text.Core.FieldOut :=
  typeFields types ++ importFields imports ++ memoryFields memories ++ globalFields globals ++
    functionFields funcs ++ dataFields data ++ exportFields exports

def moduleContextWithData (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (data : List Data) (exports : List Export) : Text.Core.IdCtx :=
  Text.Core.IdCtx.concat
    ((moduleFieldsWithData types imports memories globals funcs data exports).map (·.2.1))

def startFields (start : Option FuncIdx) : List Text.Core.FieldOut :=
  start.toList.map fun f => ([.start f], {}, [])

def moduleFieldsWithStart (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (data : List Data) (start : Option FuncIdx) (exports : List Export) : List Text.Core.FieldOut :=
  typeFields types ++ importFields imports ++ memoryFields memories ++ globalFields globals ++
    functionFields funcs ++ dataFields data ++ startFields start ++ exportFields exports

def moduleContextWithStart (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (data : List Data) (start : Option FuncIdx) (exports : List Export) : Text.Core.IdCtx :=
  Text.Core.IdCtx.concat
    ((moduleFieldsWithStart types imports memories globals funcs data start exports).map (·.2.1))

def tagFields (tags : List TagType) : List Text.Core.FieldOut :=
  tags.map fun t => ([.tag t], { tags := [none] }, [])

def tableFields (tables : List Table) : List Text.Core.FieldOut :=
  tables.map fun t => ([.table t], { tables := [none] }, [])

def elemFields (elems : List Elem) : List Text.Core.FieldOut :=
  elems.map fun e => ([.elem e], { elems := [none] }, [])

def moduleFieldsAll (m : Wasm.Module) : List Text.Core.FieldOut :=
  typeFields m.types ++ importFields m.imports ++ tagFields m.tags ++
    memoryFields m.memories ++ globalFields m.globals ++ tableFields m.tables ++
    functionFields m.funcs ++ dataFields m.data ++ elemFields m.elems ++
    startFields m.start ++ exportFields m.exports

def moduleContextAll (m : Wasm.Module) : Text.Core.IdCtx :=
  Text.Core.IdCtx.concat ((moduleFieldsAll m).map (·.2.1))

def functionType? (I : Text.Core.IdCtx) (i : TypeIdx) : Option FuncType :=
  match I.typedefs[i.toNat]? with
  | some (some (rt, n)) =>
      match rt.types[n]? with
      | some ⟨_, _, .func ft⟩ => some ft
      | _ => none
  | _ => none

def storageSyntax? : StorageType → Option SExp
  | .val t => valueSyntax? t
  | .packed .i8 => some (K "i8")
  | .packed .i16 => some (K "i16")

def fieldTypeSyntax? (f : FieldType) : Option SExp := do
  let storage ← storageSyntax? f.storage
  pure (match f.mutability with | .const => storage | .var => L [K "mut", storage])

def compositeSyntax? : CompositeType → Option SExp
  | .func ft => do
      if ft.params.length ≥ 2 ^ 32 || ft.results.length ≥ 2 ^ 32 then none else do
        let ps ← ft.params.mapM valueSyntax?
        let rs ← ft.results.mapM valueSyntax?
        pure (L [K "func", L (K "param" :: ps), L (K "result" :: rs)])
  | .struct fs => do
      if fs.length ≥ 2 ^ 32 then none else do
        let fields ← fs.mapM fieldTypeSyntax?
        pure (L [K "struct", L (K "field" :: fields)])
  | .array f => do pure (L [K "array", ← fieldTypeSyntax? f])

def subTypeSyntax? (st : SubType) : Option SExp := do
  if st.supertypes.length ≥ 2 ^ 32 then none else do
    let supers ← st.supertypes.mapM indexSyntax?
    let body ← compositeSyntax? st.body
    pure (L (K "sub" :: ((if st.final_ then [K "final"] else []) ++ supers ++ [body])))

def recTypeSyntax? (rt : RecType) : Option SExp := do
  if rt.types.length ≥ 2 ^ 32 then none else do
    let bodies ← rt.types.mapM subTypeSyntax?
    pure (L (K "rec" :: bodies.map fun b => L [K "type", b]))

def typeSyntax? : RecType → Option SExp
  | ⟨[⟨true, [], .func ft⟩]⟩ => do
      if ft.params.length ≥ 2 ^ 32 || ft.results.length ≥ 2 ^ 32 then none else do
        let ps ← ft.params.mapM valueSyntax?
        let rs ← ft.results.mapM valueSyntax?
        pure (L [K "type", L [K "func", L (K "param" :: ps), L (K "result" :: rs)]])
  | rt => recTypeSyntax? rt

/-- Explicit 64-bit offset and byte alignment for scalar and vector memory operations.
The alignment bound prevents constructing an enormous power before the numeric
spelling check. Module validation checks natural alignment separately. -/
def memoryArgSyntax? (a : MemArg) : Option (List SExp) :=
  if a.align.val > 4 then none else
    let offset := toString a.offset.val
    let alignment := toString (2 ^ a.align.val)
    if a.offset.val ∈ ValuesExamples.unCands 64 offset.toList ∧
        2 ^ a.align.val ∈ ValuesExamples.unCands 64 alignment.toList then
      some [K ("offset=" ++ offset), K ("align=" ++ alignment)]
    else none

/-- Compare supported scalar/vector memory constructors without requiring a
decision procedure for equality of arbitrary recursive instructions. The original
name remains available for callers. -/
def integerMemoryEq : Instr → Instr → Bool
  | .intLoad t p m a, .intLoad t' p' m' a' => decide (t = t' ∧ p = p' ∧ m = m' ∧ a = a')
  | .intStore t p m a, .intStore t' p' m' a' => decide (t = t' ∧ p = p' ∧ m = m' ∧ a = a')
  | .floatLoad t m a, .floatLoad t' m' a' => decide (t = t' ∧ m = m' ∧ a = a')
  | .floatStore t m a, .floatStore t' m' a' => decide (t = t' ∧ m = m' ∧ a = a')
  | .vecLoad t m a, .vecLoad t' m' a' => decide (t = t' ∧ m = m' ∧ a = a')
  | .vecStore m a, .vecStore m' a' => decide (m = m' ∧ a = a')
  | _, _ => false

/-- Find an exact constructor in the independent grammar's memory-op table.
Scalar and vector loads/stores call this helper from `instructionSyntax?`. -/
def memoryOpSyntax? (i : Instr) (m : MemIdx) (a : MemArg) : Option (List SExp) := do
  let (name, _, _) ← Text.Core.memOps.find? (fun entry => integerMemoryEq (entry.2.2 m a) i)
  let index ← indexSyntax? m
  let args ← memoryArgSyntax? a
  pure (K name :: index :: args)

def laneInstructionEq : Instr → Instr → Bool
  | .vecLoadLane s m a l, .vecLoadLane s' m' a' l' => decide (s = s' ∧ m = m' ∧ a = a' ∧ l = l')
  | .vecStoreLane s m a l, .vecStoreLane s' m' a' l' => decide (s = s' ∧ m = m' ∧ a = a' ∧ l = l')
  | .vecExtractLane s sign l, .vecExtractLane s' sign' l' => decide (s = s' ∧ sign = sign' ∧ l = l')
  | .vecReplaceLane s l, .vecReplaceLane s' l' => decide (s = s' ∧ l = l')
  | _, _ => false

def laneMemorySyntax? (i : Instr) (m : MemIdx) (a : MemArg) (l : LaneIdx) : Option (List SExp) := do
  let (name, _, _) ← Text.Core.laneMemOps.find? (fun e => laneInstructionEq (e.2.2 m a l) i)
  let memory ← indexSyntax? m
  let args ← memoryArgSyntax? a
  let lane ← unsignedSyntax? 8 l.val
  pure (K name :: memory :: (args ++ [lane]))

def laneSyntax? (i : Instr) (l : LaneIdx) : Option (List SExp) := do
  let (name, _) ← Text.Core.laneOps.find? (fun e => laneInstructionEq (e.2 l) i)
  pure [K name, ← unsignedSyntax? 8 l.val]

/-- The proposed two-lane spelling is accepted only after exact reconstruction
of all 128 bits. This check avoids trusting the lane extraction algorithm. -/
def vectorConstSyntax? (bits : BitVec 128) : Option (List SExp) := do
  let lanes : List (BitVec 64) := [BitVec.ofNat 64 bits.toNat,
    BitVec.ofNat 64 (bits.toNat / 2 ^ 64)]
  if Text.Core.lanesToBits 64 (lanes.map BitVec.toNat) = bits then do
    let xs ← lanes.mapM bitsSyntax?
    pure (K "i64x2" :: xs)
  else none

def instructionSyntax? (i : Instr) : Option (List SExp) := do
  match i with
  | .intConst .i32 bits => pure [K "i32.const", ← bitsSyntax? bits]
  | .intConst .i64 bits => pure [K "i64.const", ← bitsSyntax? bits]
  | .floatConst .f32 bits => pure [K "f32.const", ← floatBitsSyntax? .f32 bits]
  | .floatConst .f64 bits => pure [K "f64.const", ← floatBitsSyntax? .f64 bits]
  | .localGet n => pure [K "local.get", ← indexSyntax? n]
  | .localSet n => pure [K "local.set", ← indexSyntax? n]
  | .localTee n => pure [K "local.tee", ← indexSyntax? n]
  | .globalGet n => pure [K "global.get", ← indexSyntax? n]
  | .globalSet n => pure [K "global.set", ← indexSyntax? n]
  | .call n => pure [K "call", ← indexSyntax? n]
  | .br n => pure [K "br", ← indexSyntax? n]
  | .brIf n => pure [K "br_if", ← indexSyntax? n]
  | .intLoad _ _ m a | .intStore _ _ m a | .floatLoad _ m a | .floatStore _ m a |
      .vecLoad _ m a | .vecStore m a => memoryOpSyntax? i m a
  | .memorySize m => pure [K "memory.size", ← indexSyntax? m]
  | .memoryGrow m => pure [K "memory.grow", ← indexSyntax? m]
  | .memoryInit m d => pure [K "memory.init", ← indexSyntax? m, ← indexSyntax? d]
  | .dataDrop d => pure [K "data.drop", ← indexSyntax? d]
  | .select none => pure [K "select"]
  | .select (some ts) => do
      if ts.length ≥ 2 ^ 32 then none else do
        let txs ← ts.mapM valueSyntax?
        pure [K "select", L (K "result" :: txs)]
  | .brTable ls l => do
      if (ls ++ [l]).length ≥ 2 ^ 32 then none else do
        pure (K "br_table" :: (← (ls ++ [l]).mapM indexSyntax?))
  | .brOnNull n => pure [K "br_on_null", ← indexSyntax? n]
  | .brOnNonNull n => pure [K "br_on_non_null", ← indexSyntax? n]
  | .callRef n => pure [K "call_ref", ← indexSyntax? n]
  | .returnCall n => pure [K "return_call", ← indexSyntax? n]
  | .returnCallRef n => pure [K "return_call_ref", ← indexSyntax? n]
  | .throw n => pure [K "throw", ← indexSyntax? n]
  | .elemDrop n => pure [K "elem.drop", ← indexSyntax? n]
  | .refFunc n => pure [K "ref.func", ← indexSyntax? n]
  | .structNew n => pure [K "struct.new", ← indexSyntax? n]
  | .structNewDefault n => pure [K "struct.new_default", ← indexSyntax? n]
  | .arrayNew n => pure [K "array.new", ← indexSyntax? n]
  | .arrayNewDefault n => pure [K "array.new_default", ← indexSyntax? n]
  | .arraySet n => pure [K "array.set", ← indexSyntax? n]
  | .arrayFill n => pure [K "array.fill", ← indexSyntax? n]
  | .memoryFill n => pure [K "memory.fill", ← indexSyntax? n]
  | .tableGet n => pure [K "table.get", ← indexSyntax? n]
  | .tableSet n => pure [K "table.set", ← indexSyntax? n]
  | .tableSize n => pure [K "table.size", ← indexSyntax? n]
  | .tableGrow n => pure [K "table.grow", ← indexSyntax? n]
  | .tableFill n => pure [K "table.fill", ← indexSyntax? n]
  | .memoryCopy n m => pure [K "memory.copy", ← indexSyntax? n, ← indexSyntax? m]
  | .tableCopy n m => pure [K "table.copy", ← indexSyntax? n, ← indexSyntax? m]
  | .tableInit n m => pure [K "table.init", ← indexSyntax? n, ← indexSyntax? m]
  | .structSet n m => pure [K "struct.set", ← indexSyntax? n, ← indexSyntax? m]
  | .arrayNewData n m => pure [K "array.new_data", ← indexSyntax? n, ← indexSyntax? m]
  | .arrayNewElem n m => pure [K "array.new_elem", ← indexSyntax? n, ← indexSyntax? m]
  | .arrayCopy n m => pure [K "array.copy", ← indexSyntax? n, ← indexSyntax? m]
  | .arrayInitData n m => pure [K "array.init_data", ← indexSyntax? n, ← indexSyntax? m]
  | .arrayInitElem n m => pure [K "array.init_elem", ← indexSyntax? n, ← indexSyntax? m]
  | .refNull h => pure [K "ref.null", ← heapSyntax? h]
  | .refTest r => pure [K "ref.test", ← refSyntax? r]
  | .refCast r => pure [K "ref.cast", ← refSyntax? r]
  | .arrayGet none n => pure [K "array.get", ← indexSyntax? n]
  | .arrayGet (some .signed) n => pure [K "array.get_s", ← indexSyntax? n]
  | .arrayGet (some .unsigned) n => pure [K "array.get_u", ← indexSyntax? n]
  | .structGet none n f => pure [K "struct.get", ← indexSyntax? n, ← indexSyntax? f]
  | .structGet (some .signed) n f => pure [K "struct.get_s", ← indexSyntax? n, ← indexSyntax? f]
  | .structGet (some .unsigned) n f => pure [K "struct.get_u", ← indexSyntax? n, ← indexSyntax? f]
  | .brOnCast l source target => pure [K "br_on_cast", ← indexSyntax? l, ← refSyntax? source, ← refSyntax? target]
  | .brOnCastFail l source target => pure [K "br_on_cast_fail", ← indexSyntax? l, ← refSyntax? source, ← refSyntax? target]
  | .arrayNewFixed t n => pure [K "array.new_fixed", ← indexSyntax? t, ← unsignedSyntax? 32 n.val]
  | .vecLoadLane _ m a l | .vecStoreLane _ m a l => laneMemorySyntax? i m a l
  | .vecExtractLane _ _ l | .vecReplaceLane _ l => laneSyntax? i l
  | .vecConst bits => pure (K "v128.const" :: (← vectorConstSyntax? bits))
  | .vecShuffle lanes => do
      if lanes.length = 16 then do
        pure (K "i8x16.shuffle" :: (← lanes.mapM (fun l => unsignedSyntax? 8 l.val)))
      else none
  | _ => pure [K (← Text.Core.nullaryName i)]

/-- Explicit canonical result clauses for empty and scalar block signatures.
Type-index block signatures are rejected rather than approximated. -/
def blockTypeSyntax? : BlockType → Option (List SExp)
  | .empty => some [L [K "result"]]
  | .value t => do pure [L [K "result", ← valueSyntax? t]]
  | .typeIdx _ => none

/-- Structural serialization with an explicit recursion budget. A successful
result is certified independently of this budget by the grammar theorem. -/
def instructionTreeFuel? : Nat → Instr → Option (List SExp)
  | 0, _ => none
  | fuel + 1, .block bt body => do
      let header ← blockTypeSyntax? bt
      let parts ← body.mapM (instructionTreeFuel? fuel)
      pure [L (K "block" :: (header ++ parts.flatten))]
  | fuel + 1, .loop bt body => do
      let header ← blockTypeSyntax? bt
      let parts ← body.mapM (instructionTreeFuel? fuel)
      pure [L (K "loop" :: (header ++ parts.flatten))]
  | fuel + 1, .if_ bt left right => do
      let header ← blockTypeSyntax? bt
      let ls ← left.mapM (instructionTreeFuel? fuel)
      let rs ← right.mapM (instructionTreeFuel? fuel)
      pure [L (K "if" :: (header ++
        [L (K "then" :: ls.flatten), L (K "else" :: rs.flatten)]))]
  | _ + 1, i => instructionSyntax? i

mutual
/-- Executable structural depth; unlike the kernel's generated `sizeOf`,
this is available to the runtime serializer. -/
def instructionDepth : Instr → Nat
  | .block _ body | .loop _ body | .tryTable _ _ body => instructionDepths body + 1
  | .if_ _ left right => max (instructionDepths left) (instructionDepths right) + 1
  | _ => 1

def instructionDepths : List Instr → Nat
  | [] => 0
  | i :: is => max (instructionDepth i) (instructionDepths is)
end

/-- Canonical flat scalar leaves and recursively nested structured control.
The recursion budget is computed from the source tree's structural depth. -/
def instructionTree? (i : Instr) : Option (List SExp) :=
  instructionTreeFuel? (instructionDepth i) i

/-- Explicit type uses require the surrounding module type context. -/
def instructionSyntaxAt? (I : Text.Core.IdCtx) (i : Instr) : Option (List SExp) := do
  match i with
  | .callIndirect table type => do
      let _ ← functionType? I type
      pure [K "call_indirect", ← indexSyntax? table, L [K "type", ← indexSyntax? type]]
  | .returnCallIndirect table type => do
      let _ ← functionType? I type
      pure [K "return_call_indirect", ← indexSyntax? table, L [K "type", ← indexSyntax? type]]
  | _ => instructionSyntax? i

def blockTypeSyntaxAt? (I : Text.Core.IdCtx) (bt : BlockType) : Option (List SExp) := do
  match bt with
  | .typeIdx type => do
      let _ ← functionType? I type
      pure [L [K "type", ← indexSyntax? type]]
  | _ => blockTypeSyntax? bt

def catchSyntax? : Catch → Option SExp
  | .catch_ t l => do pure (L [K "catch", ← indexSyntax? t, ← indexSyntax? l])
  | .catchRef t l => do pure (L [K "catch_ref", ← indexSyntax? t, ← indexSyntax? l])
  | .catchAll l => do pure (L [K "catch_all", ← indexSyntax? l])
  | .catchAllRef l => do pure (L [K "catch_all_ref", ← indexSyntax? l])

def instructionTreeAtFuel? : Nat → Text.Core.IdCtx → Instr → Option (List SExp)
  | 0, _, _ => none
  | fuel + 1, I, .block bt body => do
      let header ← blockTypeSyntaxAt? I bt
      let parts ← body.mapM (instructionTreeAtFuel? fuel { I with labels := none :: I.labels })
      pure [L (K "block" :: (header ++ parts.flatten))]
  | fuel + 1, I, .loop bt body => do
      let header ← blockTypeSyntaxAt? I bt
      let parts ← body.mapM (instructionTreeAtFuel? fuel { I with labels := none :: I.labels })
      pure [L (K "loop" :: (header ++ parts.flatten))]
  | fuel + 1, I, .if_ bt left right => do
      let header ← blockTypeSyntaxAt? I bt
      let ls ← left.mapM (instructionTreeAtFuel? fuel { I with labels := none :: I.labels })
      let rs ← right.mapM (instructionTreeAtFuel? fuel { I with labels := none :: I.labels })
      pure [L (K "if" :: (header ++
        [L (K "then" :: ls.flatten), L (K "else" :: rs.flatten)]))]
  | fuel + 1, I, .tryTable bt catches body => do
      let header ← blockTypeSyntaxAt? I bt
      let cs ← catches.mapM catchSyntax?
      let parts ← body.mapM (instructionTreeAtFuel? fuel { I with labels := none :: I.labels })
      pure [L (K "try_table" :: (header ++ cs ++ parts.flatten))]
  | _ + 1, I, i => instructionSyntaxAt? I i

def instructionTreeAt? (I : Text.Core.IdCtx) (i : Instr) : Option (List SExp) :=
  instructionTreeAtFuel? (instructionDepth i) I i

def functionSyntax? (I : Text.Core.IdCtx) (f : Func) : Option SExp := do
  let ft ← functionType? I f.type
  if f.locals.length ≥ 2 ^ 32 then none else do
    let localContext : Text.Core.IdCtx :=
      { locals := List.replicate ft.params.length none ++ f.locals.map (fun _ => none) }
    if !(decide (I ++ localContext).Ok) then none else do
      let type ← indexSyntax? f.type
      let locals ← f.locals.mapM valueSyntax?
      let body ← f.body.mapM (instructionTreeAt? (I ++ localContext))
      pure (L (K "func" :: L [K "type", type] :: L (K "local" :: locals) :: body.flatten))

def nameSyntax? (name : String) : Option SExp :=
  let bytes := name.toUTF8.data.toList
  if Unicode.utf8? bytes = some name then some (.atom (.str bytes)) else none

def exportSyntax? (e : Export) : Option SExp := do
  match e.index with
  | .func f => pure (L [K "export", ← nameSyntax? e.name, L [K "func", ← indexSyntax? f]])
  | .memory m => pure (L [K "export", ← nameSyntax? e.name, L [K "memory", ← indexSyntax? m]])
  | .global g => pure (L [K "export", ← nameSyntax? e.name, L [K "global", ← indexSyntax? g]])
  | .tag t => pure (L [K "export", ← nameSyntax? e.name, L [K "tag", ← indexSyntax? t]])
  | .table t => pure (L [K "export", ← nameSyntax? e.name, L [K "table", ← indexSyntax? t]])

/-- Canonical limits preserve their complete unsigned 64-bit values.
Address-specific bounds and ordering remain module validation. -/
def memoryLimitsSyntax? (limits : Limits) : Option (List SExp) := do
  let min ← unsignedSyntax? 64 limits.min.val
  let tail ← match limits.max with
    | none => some []
    | some max => do pure [← unsignedSyntax? 64 max.val]
  pure (min :: tail)

def memoryTypeSyntax? (m : MemoryType) : Option (List SExp) := do
  let limits ← memoryLimitsSyntax? m.limits
  pure ((match m.address with | .i32 => [] | .i64 => [K "i64"]) ++ limits)

def memorySyntax? (m : MemoryType) : Option SExp := do
  pure (L (K "memory" :: (← memoryTypeSyntax? m)))

def globalTypeSyntax? (g : GlobalType) : Option SExp := do
  let value ← valueSyntax? g.value
  match g.mutability with
  | .const => pure value
  | .var => pure (L [K "mut", value])

/-- Serialize the complete initializer expression. The grammar establishes its
syntax; the assembler's independent validation checks constant-expression typing. -/
def constantSyntax? (e : Expr) : Option (List SExp) := do
  pure (← e.mapM instructionTree?).flatten

def globalSyntax? (g : Global) : Option SExp := do
  let type ← globalTypeSyntax? g.type
  let init ← constantSyntax? g.init
  pure (L (K "global" :: type :: init))

/-- Passive bytes, or explicit 32-bit active memory and constant offset.
The checked renderer independently determines which byte strings can be written
with the existing lexical surface; no new escape support is assumed. -/
def dataSyntax? (d : Data) : Option SExp := do
  let payload : SExp := .atom (.str d.bytes.data.toList)
  match d.mode with
  | .passive => pure (L [K "data", payload])
  | .active memory sourceOffset =>
      let index ← indexSyntax? memory
      let offset ← constantSyntax? sourceOffset
      pure (L [K "data", L [K "memory", index], L (K "offset" :: offset), payload])

def tableTypeSyntax? (t : TableType) : Option (List SExp) := do
  let limits ← memoryLimitsSyntax? t.limits
  let element ← refSyntax? t.element
  pure ((match t.address with | .i32 => [] | .i64 => [K "i64"]) ++ limits ++ [element])

def defaultTableInit (t : Table) : Bool :=
  match t.init with
  | [.refNull heap] => heap == t.type.element.heap
  | _ => false

/-- Fold each plain initializer instruction for interoperability with readers
that accept only folded expressions in table initialization. -/
def foldedInitializerSyntax? (e : Expr) : Option (List SExp) := do
  pure ((← e.mapM instructionSyntax?).map L)

def tableSyntax? (t : Table) : Option SExp := do
  let type ← tableTypeSyntax? t.type
  if defaultTableInit t then pure (L (K "table" :: type)) else do
    let init ← foldedInitializerSyntax? t.init
    if init = [] then none else pure (L (K "table" :: (type ++ init)))

def tagSyntax? (I : Text.Core.IdCtx) (t : TagType) : Option SExp := do
  let _ ← functionType? I t
  pure (L [K "tag", L [K "type", ← indexSyntax? t]])

def elemSyntax? (e : Elem) : Option SExp := do
  if e.init.length ≥ 2 ^ 32 then none else do
    let type ← refSyntax? e.type
    let items ← e.init.mapM constantSyntax?
    let rest := type :: items.map fun xs => L (K "item" :: xs)
    match e.mode with
    | .passive => pure (L (K "elem" :: rest))
    | .declarative => pure (L (K "elem" :: K "declare" :: rest))
    | .active t offset => do
        let table ← indexSyntax? t
        let offset ← constantSyntax? offset
        pure (L (K "elem" :: L [K "table", table] :: L (K "offset" :: offset) :: rest))

/-- Explicit imports of every Core external kind. -/
def importSyntax? (I : Text.Core.IdCtx) : Import → Option SExp
  | ⟨moduleName, name, .func type⟩ => do
      let _ ← functionType? I type
      let source ← nameSyntax? moduleName
      let field ← nameSyntax? name
      let index ← indexSyntax? type
      pure (L [K "import", source, field, L [K "func", L [K "type", index]]])
  | ⟨moduleName, name, .global type⟩ => do
      let source ← nameSyntax? moduleName
      let field ← nameSyntax? name
      let type ← globalTypeSyntax? type
      pure (L [K "import", source, field, L [K "global", type]])
  | ⟨moduleName, name, .memory type⟩ => do
      let source ← nameSyntax? moduleName
      let field ← nameSyntax? name
      let type ← memoryTypeSyntax? type
      pure (L [K "import", source, field, L (K "memory" :: type)])
  | ⟨moduleName, name, .table type⟩ => do
      let source ← nameSyntax? moduleName
      let field ← nameSyntax? name
      let type ← tableTypeSyntax? type
      pure (L [K "import", source, field, L (K "table" :: type)])
  | ⟨moduleName, name, .tag type⟩ => do
      let _ ← functionType? I type
      let source ← nameSyntax? moduleName
      let field ← nameSyntax? name
      let index ← indexSyntax? type
      pure (L [K "import", source, field, L [K "tag", L [K "type", index]]])

def startSyntax? (f : FuncIdx) : Option SExp := do
  pure (L [K "start", ← indexSyntax? f])

/-- Serialize all Core module fields in canonical order. Every successful
per-field result is certified by the independent Core text grammar. -/
def moduleSyntax? (m : Wasm.Module) : Option SExp := do
  let I := moduleContextAll m
  if !(decide I.Ok) then none else do
    let ts ← m.types.mapM typeSyntax?
    let ims ← m.imports.mapM (importSyntax? I)
    let tags ← m.tags.mapM (tagSyntax? I)
    let ms ← m.memories.mapM memorySyntax?
    let gs ← m.globals.mapM globalSyntax?
    let tables ← m.tables.mapM tableSyntax?
    let fs ← m.funcs.mapM (functionSyntax? I)
    let ds ← m.data.mapM dataSyntax?
    let elems ← m.elems.mapM elemSyntax?
    let ss ← m.start.toList.mapM startSyntax?
    let es ← m.exports.mapM exportSyntax?
    pure (doc [L (K "module" :: (ts ++ ims ++ tags ++ ms ++ gs ++ tables ++ fs ++ ds ++ elems ++ ss ++ es))])

end Silmaril.Wasm.Binaryen.Toolkit.Wat
