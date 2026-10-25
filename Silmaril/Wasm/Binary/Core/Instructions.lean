module

public import Silmaril.Wasm.Binary.Core.Opcodes
public import Silmaril.Wasm.Binary.Core.OpcodesProps
public import Silmaril.Wasm.Instructions
import Mathlib.Tactic.DefEqTransformations

/-! # Core 3.0 binary format: instructions

Transcribed rule by rule from `5.3-binary.instructions.spectec` (cited `5.3:n`).
Instructions without immediates after their opcode are grouped by opcode prefix
into tables (`PlainOp`, `PrefixFBOp`, `PrefixFCOp`, `PrefixFDOp`) and the memory
families into `MemOp`, `VecMemOp`, `VecMemLaneOp`, `VecLaneOp` (in `Core/Opcodes.lean`,
with their lookups and determinism in `Core/OpcodesProps.lean`): each constructor
is one spec rule, with its line. The tables are generated mechanically from the
pinned SpecTec source; `Instr` then has one rule per table plus one per remaining
production. The `0xFB`/`0xFC`/`0xFD` sub-opcodes are `Bu32` and may therefore be
non-minimal LEB128.

Gated rules use `Forms` (see `Core/Types.lean`): explicit memory indices in
`memarg` and memory instructions, 64-bit offsets, and `call_indirect`'s table index.

Constants follow `BiN` (signed LEB128), see the errata in `Binary/Basic.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary.Core

/-- `Blaneidx = l:Bbyte => l` (5.3:392–393). -/
def laneOf (l : UInt8) : LaneIdx := l.toBitVec.toFin

/-! ## Immediates -/

/-- `Bcastop` (5.3:20–24): the nullability of the source and target types. -/
inductive CastOp : Bytes → Bool × Bool → Prop where
  | r00 : CastOp [0x00] (false, false)
  | r01 : CastOp [0x01] (true, false)
  | r02 : CastOp [0x02] (false, true)
  | r03 : CastOp [0x03] (true, true)

/-- `Bblocktype` (5.3:26–29). -/
inductive BlockType (F : Forms) : Bytes → Wasm.BlockType → Prop where
  | empty : BlockType F [0x40] .empty
  | value {b : Bytes} {t : Wasm.ValType} (h : ValType F b t) : BlockType F b (.value t)
  | idx {b : Bytes} (i : TypeIdx) (h : S33 b i.toNat) : BlockType F b (.typeIdx i)

/-- `Bcatch` (5.3:61–65). -/
inductive Catch : Bytes → Wasm.Catch → Prop where
  | catch_ {b b' : Bytes} {x : TagIdx} {l : LabelIdx} (hx : Index b x) (hl : Index b' l) :
      Catch ([0x00] ++ b ++ b') (.catch_ x l)
  | catchRef {b b' : Bytes} {x : TagIdx} {l : LabelIdx} (hx : Index b x) (hl : Index b' l) :
      Catch ([0x01] ++ b ++ b') (.catchRef x l)
  | catchAll {b : Bytes} {l : LabelIdx} (hl : Index b l) : Catch ([0x02] ++ b) (.catchAll l)
  | catchAllRef {b : Bytes} {l : LabelIdx} (hl : Index b l) : Catch ([0x03] ++ b) (.catchAllRef l)

/-- A `memarg` offset: `Bu64` (5.3:101–102), or, as in Wasm 1.0, `u32`. -/
inductive Offset (F : Forms) : Bytes → Fin (2 ^ 64) → Prop where
  | u64 {b : Bytes} {m : Fin (2 ^ 64)} (g : F .memargOffset64 = true) (h : U64 b m.val) :
      Offset F b m
  | u32 {b : Bytes} {m : Fin (2 ^ 64)} (h : U32 b m.val) : Offset F b m

/-- `Bmemarg : (memidx, memarg)` (5.3:100–102):

* `n:Bu32 m:Bu64 => (0, {ALIGN n, OFFSET m})` if `n < 2^6`;
* `n:Bu32 x:Bmemidx m:Bu64 => (x, {ALIGN n - 2^6, OFFSET m})` if `2^6 ≤ n < 2^7`
  (`Form.memargMemIdx`). -/
inductive Memarg (F : Forms) : Bytes → MemIdx × Wasm.MemArg → Prop where
  | mem0 {bn bm : Bytes} {a : Fin (2 ^ 32)} {m : Fin (2 ^ 64)} (hn : U32 bn a.val)
      (ha : a.val < 2 ^ 6) (hm : Offset F bm m) : Memarg F (bn ++ bm) (⟨0⟩, ⟨a, m⟩)
  | memIdx {bn bx bm : Bytes} {n : Nat} {a : Fin (2 ^ 32)} {x : MemIdx} {m : Fin (2 ^ 64)}
      (g : F .memargMemIdx = true) (hn : U32 bn n) (lo : 2 ^ 6 ≤ n) (hi : n < 2 ^ 7)
      (ha : a.val = n - 2 ^ 6) (hx : Index bx x) (hm : Offset F bm m) :
      Memarg F (bn ++ bx ++ bm) (x, ⟨a, m⟩)

/-- An index immediate that Wasm 1.0 encoded as the reserved byte `0x00`
(`call_indirect`'s table, the memory instructions' memory). In Core 3.0 it is `Bu32`
(rule `idx`, enabled by `allow`); the reserved byte is the minimal `u32` zero. -/
inductive ReservedIdx {k : IndexKind} (allow : Bool) : Bytes → Idx k → Prop where
  | idx {b : Bytes} {x : Idx k} (g : allow = true) (h : Index b x) : ReservedIdx allow b x
  | zero : ReservedIdx allow [0x00] ⟨0⟩

/-! ## Instructions -/

mutual

/-- `Binstr` (5.3, all `Binstr/*` fragments). -/
inductive Instr (F : Forms) : Bytes → Wasm.Instr → Prop where
  /-- Every single-byte rule without immediates (`PlainOp`). -/
  | plain {op : UInt8} {i : Wasm.Instr} (h : PlainOp op i) : Instr F [op] i
  /-- `0xFB n:Bu32` rules without further immediates (`PrefixFBOp`). -/
  | prefixFB {b : Bytes} {n : Nat} {i : Wasm.Instr} (h : PrefixFBOp n i) (hn : U32 b n) :
      Instr F ([0xFB] ++ b) i
  /-- `0xFC n:Bu32` rules without further immediates (`PrefixFCOp`). -/
  | prefixFC {b : Bytes} {n : Nat} {i : Wasm.Instr} (h : PrefixFCOp n i) (hn : U32 b n) :
      Instr F ([0xFC] ++ b) i
  /-- `0xFD n:Bu32` rules without further immediates (`PrefixFDOp`). -/
  | prefixFD {b : Bytes} {n : Nat} {i : Wasm.Instr} (h : PrefixFDOp n i) (hn : U32 b n) :
      Instr F ([0xFD] ++ b) i
  /-- `0x1C t*:Blist(Bvaltype) => SELECT t*` (5.3:12). -/
  | selectT {b : Bytes} {ts : List Wasm.ValType} (h : Vec (ValType F) b ts) :
      Instr F ([0x1C] ++ b) (.select (some ts))
  /-- `0x02 bt:Bblocktype (in:Binstr)* 0x0B => BLOCK bt in*` (5.3:32). -/
  | block {bt b : Bytes} {t : Wasm.BlockType} {body : List Wasm.Instr}
      (ht : BlockType F bt t) (hb : Instrs F b body) :
      Instr F ([0x02] ++ bt ++ b ++ [0x0B]) (.block t body)
  /-- `0x03 bt:Bblocktype (in:Binstr)* 0x0B => LOOP bt in*` (5.3:33). -/
  | loop {bt b : Bytes} {t : Wasm.BlockType} {body : List Wasm.Instr}
      (ht : BlockType F bt t) (hb : Instrs F b body) :
      Instr F ([0x03] ++ bt ++ b ++ [0x0B]) (.loop t body)
  /-- `0x04 bt:Bblocktype (in:Binstr)* 0x0B => IF bt in* ELSE eps` (5.3:34). -/
  | if_ {bt b : Bytes} {t : Wasm.BlockType} {body : List Wasm.Instr}
      (ht : BlockType F bt t) (hb : Instrs F b body) :
      Instr F ([0x04] ++ bt ++ b ++ [0x0B]) (.if_ t body [])
  /-- `0x04 bt:Bblocktype (in_1:Binstr)* 0x05 (in_2:Binstr)* 0x0B => IF bt in_1* ELSE in_2*`
  (5.3:35–36). -/
  | ifElse {bt b₁ b₂ : Bytes} {t : Wasm.BlockType} {body₁ body₂ : List Wasm.Instr}
      (ht : BlockType F bt t) (h₁ : Instrs F b₁ body₁) (h₂ : Instrs F b₂ body₂) :
      Instr F ([0x04] ++ bt ++ b₁ ++ [0x05] ++ b₂ ++ [0x0B]) (.if_ t body₁ body₂)
  /-- `0x08 x:Btagidx => THROW x` (5.3:40). -/
  | throw {b : Bytes} {x : TagIdx} (h : Index b x) : Instr F ([0x08] ++ b) (.throw x)
  /-- `0x0C l:Blabelidx => BR l` (5.3:42). -/
  | br {b : Bytes} {l : LabelIdx} (h : Index b l) : Instr F ([0x0C] ++ b) (.br l)
  /-- `0x0D l:Blabelidx => BR_IF l` (5.3:43). -/
  | brIf {b : Bytes} {l : LabelIdx} (h : Index b l) : Instr F ([0x0D] ++ b) (.brIf l)
  /-- `0x0E l*:Blist(Blabelidx) l_n:Blabelidx => BR_TABLE l* l_n` (5.3:44). -/
  | brTable {b b' : Bytes} {ls : List LabelIdx} {l : LabelIdx} (h : Vec Index b ls)
      (h' : Index b' l) : Instr F ([0x0E] ++ b ++ b') (.brTable ls l)
  /-- `0x10 x:Bfuncidx => CALL x` (5.3:46). -/
  | call {b : Bytes} {x : FuncIdx} (h : Index b x) : Instr F ([0x10] ++ b) (.call x)
  /-- `0x11 y:Btypeidx x:Btableidx => CALL_INDIRECT x (_IDX y)` (5.3:47); the table index
  is `Form.tableIdxImm`, else the reserved `0x00`. -/
  | callIndirect {by_ bx : Bytes} {y : TypeIdx} {x : TableIdx} (hy : Index by_ y)
      (hx : ReservedIdx (F .tableIdxImm) bx x) :
      Instr F ([0x11] ++ by_ ++ bx) (.callIndirect x y)
  /-- `0x12 x:Bfuncidx => RETURN_CALL x` (5.3:48). -/
  | returnCall {b : Bytes} {x : FuncIdx} (h : Index b x) : Instr F ([0x12] ++ b) (.returnCall x)
  /-- `0x13 y:Btypeidx x:Btableidx => RETURN_CALL_INDIRECT x (_IDX y)` (5.3:49). -/
  | returnCallIndirect {by_ bx : Bytes} {y : TypeIdx} {x : TableIdx} (hy : Index by_ y)
      (hx : Index bx x) : Instr F ([0x13] ++ by_ ++ bx) (.returnCallIndirect x y)
  /-- `0x14 x:Btypeidx => CALL_REF (_IDX x)` (5.3:50). -/
  | callRef {b : Bytes} {x : TypeIdx} (h : Index b x) : Instr F ([0x14] ++ b) (.callRef x)
  /-- `0x15 x:Btypeidx => RETURN_CALL_REF (_IDX x)` (5.3:51). -/
  | returnCallRef {b : Bytes} {x : TypeIdx} (h : Index b x) :
      Instr F ([0x15] ++ b) (.returnCallRef x)
  /-- `0x1F bt:Bblocktype c*:Blist(Bcatch) (in:Binstr)* 0x0B => TRY_TABLE bt c* in*` (5.3:52). -/
  | tryTable {bt bc b : Bytes} {t : Wasm.BlockType} {cs : List Wasm.Catch}
      {body : List Wasm.Instr} (ht : BlockType F bt t) (hc : Vec Catch bc cs)
      (hb : Instrs F b body) : Instr F ([0x1F] ++ bt ++ bc ++ b ++ [0x0B]) (.tryTable t cs body)
  /-- `0xD5 l:Blabelidx => BR_ON_NULL l` (5.3:53). -/
  | brOnNull {b : Bytes} {l : LabelIdx} (h : Index b l) : Instr F ([0xD5] ++ b) (.brOnNull l)
  /-- `0xD6 l:Blabelidx => BR_ON_NON_NULL l` (5.3:54). -/
  | brOnNonNull {b : Bytes} {l : LabelIdx} (h : Index b l) :
      Instr F ([0xD6] ++ b) (.brOnNonNull l)
  /-- `0xFB 24:Bu32 castop l ht_1 ht_2 => BR_ON_CAST l (REF null_1? ht_1) (REF null_2? ht_2)`
  (5.3:55–56). -/
  | brOnCast {bn bc bl b₁ b₂ : Bytes} {n₁ n₂ : Bool} {l : LabelIdx} {h₁ h₂ : Wasm.HeapType}
      (hn : U32 bn 24) (hc : CastOp bc (n₁, n₂)) (hl : Index bl l) (ht₁ : HeapType b₁ h₁)
      (ht₂ : HeapType b₂ h₂) :
      Instr F ([0xFB] ++ bn ++ bc ++ bl ++ b₁ ++ b₂) (.brOnCast l ⟨n₁, h₁⟩ ⟨n₂, h₂⟩)
  /-- `0xFB 25:Bu32 castop l ht_1 ht_2 => BR_ON_CAST_FAIL …` (5.3:57–58). -/
  | brOnCastFail {bn bc bl b₁ b₂ : Bytes} {n₁ n₂ : Bool} {l : LabelIdx} {h₁ h₂ : Wasm.HeapType}
      (hn : U32 bn 25) (hc : CastOp bc (n₁, n₂)) (hl : Index bl l) (ht₁ : HeapType b₁ h₁)
      (ht₂ : HeapType b₂ h₂) :
      Instr F ([0xFB] ++ bn ++ bc ++ bl ++ b₁ ++ b₂) (.brOnCastFail l ⟨n₁, h₁⟩ ⟨n₂, h₂⟩)
  /-- `0x20 x:Blocalidx => LOCAL.GET x` (5.3:71). -/
  | localGet {b : Bytes} {x : LocalIdx} (h : Index b x) : Instr F ([0x20] ++ b) (.localGet x)
  /-- `0x21 x:Blocalidx => LOCAL.SET x` (5.3:72). -/
  | localSet {b : Bytes} {x : LocalIdx} (h : Index b x) : Instr F ([0x21] ++ b) (.localSet x)
  /-- `0x22 x:Blocalidx => LOCAL.TEE x` (5.3:73). -/
  | localTee {b : Bytes} {x : LocalIdx} (h : Index b x) : Instr F ([0x22] ++ b) (.localTee x)
  /-- `0x23 x:Bglobalidx => GLOBAL.GET x` (5.3:77). -/
  | globalGet {b : Bytes} {x : GlobalIdx} (h : Index b x) : Instr F ([0x23] ++ b) (.globalGet x)
  /-- `0x24 x:Bglobalidx => GLOBAL.SET x` (5.3:78). -/
  | globalSet {b : Bytes} {x : GlobalIdx} (h : Index b x) : Instr F ([0x24] ++ b) (.globalSet x)
  /-- `0x25 x:Btableidx => TABLE.GET x` (5.3:85). -/
  | tableGet {b : Bytes} {x : TableIdx} (h : Index b x) : Instr F ([0x25] ++ b) (.tableGet x)
  /-- `0x26 x:Btableidx => TABLE.SET x` (5.3:86). -/
  | tableSet {b : Bytes} {x : TableIdx} (h : Index b x) : Instr F ([0x26] ++ b) (.tableSet x)
  /-- `0xFC 12:Bu32 y:Belemidx x:Btableidx => TABLE.INIT x y` (5.3:87). -/
  | tableInit {bn by_ bx : Bytes} {y : ElemIdx} {x : TableIdx} (hn : U32 bn 12)
      (hy : Index by_ y) (hx : Index bx x) : Instr F ([0xFC] ++ bn ++ by_ ++ bx) (.tableInit x y)
  /-- `0xFC 13:Bu32 x:Belemidx => ELEM.DROP x` (5.3:88). -/
  | elemDrop {bn b : Bytes} {x : ElemIdx} (hn : U32 bn 13) (h : Index b x) :
      Instr F ([0xFC] ++ bn ++ b) (.elemDrop x)
  /-- `0xFC 14:Bu32 x_1:Btableidx x_2:Btableidx => TABLE.COPY x_1 x_2` (5.3:89). -/
  | tableCopy {bn b₁ b₂ : Bytes} {x₁ x₂ : TableIdx} (hn : U32 bn 14) (h₁ : Index b₁ x₁)
      (h₂ : Index b₂ x₂) : Instr F ([0xFC] ++ bn ++ b₁ ++ b₂) (.tableCopy x₁ x₂)
  /-- `0xFC 15:Bu32 x:Btableidx => TABLE.GROW x` (5.3:90). -/
  | tableGrow {bn b : Bytes} {x : TableIdx} (hn : U32 bn 15) (h : Index b x) :
      Instr F ([0xFC] ++ bn ++ b) (.tableGrow x)
  /-- `0xFC 16:Bu32 x:Btableidx => TABLE.SIZE x` (5.3:91). -/
  | tableSize {bn b : Bytes} {x : TableIdx} (hn : U32 bn 16) (h : Index b x) :
      Instr F ([0xFC] ++ bn ++ b) (.tableSize x)
  /-- `0xFC 17:Bu32 x:Btableidx => TABLE.FILL x` (5.3:92). -/
  | tableFill {bn b : Bytes} {x : TableIdx} (hn : U32 bn 17) (h : Index b x) :
      Instr F ([0xFC] ++ bn ++ b) (.tableFill x)
  /-- Scalar loads and stores `0xNN (x,ao):Bmemarg` (5.3:105–127, `MemOp`). -/
  | mem {op : UInt8} {b : Bytes} {mk : MemIdx → Wasm.MemArg → Wasm.Instr} {x : MemIdx}
      {ao : Wasm.MemArg} (h : MemOp op mk) (hm : Memarg F b (x, ao)) :
      Instr F ([op] ++ b) (mk x ao)
  /-- `0x3F x:Bmemidx => MEMORY.SIZE x` (5.3:128). -/
  | memorySize {b : Bytes} {x : MemIdx} (h : ReservedIdx (F .memIdxImm) b x) :
      Instr F ([0x3F] ++ b) (.memorySize x)
  /-- `0x40 x:Bmemidx => MEMORY.GROW x` (5.3:129). -/
  | memoryGrow {b : Bytes} {x : MemIdx} (h : ReservedIdx (F .memIdxImm) b x) :
      Instr F ([0x40] ++ b) (.memoryGrow x)
  /-- `0xFC 8:Bu32 y:Bdataidx x:Bmemidx => MEMORY.INIT x y` (5.3:130). -/
  | memoryInit {bn by_ bx : Bytes} {y : DataIdx} {x : MemIdx} (hn : U32 bn 8)
      (hy : Index by_ y) (hx : ReservedIdx (F .memIdxImm) bx x) :
      Instr F ([0xFC] ++ bn ++ by_ ++ bx) (.memoryInit x y)
  /-- `0xFC 9:Bu32 x:Bdataidx => DATA.DROP x` (5.3:131). -/
  | dataDrop {bn b : Bytes} {x : DataIdx} (hn : U32 bn 9) (h : Index b x) :
      Instr F ([0xFC] ++ bn ++ b) (.dataDrop x)
  /-- `0xFC 10:Bu32 x_1:Bmemidx x_2:Bmemidx => MEMORY.COPY x_1 x_2` (5.3:132). -/
  | memoryCopy {bn b₁ b₂ : Bytes} {x₁ x₂ : MemIdx} (hn : U32 bn 10)
      (h₁ : ReservedIdx (F .memIdxImm) b₁ x₁) (h₂ : ReservedIdx (F .memIdxImm) b₂ x₂) :
      Instr F ([0xFC] ++ bn ++ b₁ ++ b₂) (.memoryCopy x₁ x₂)
  /-- `0xFC 11:Bu32 x:Bmemidx => MEMORY.FILL x` (5.3:133). -/
  | memoryFill {bn b : Bytes} {x : MemIdx} (hn : U32 bn 11) (h : ReservedIdx (F .memIdxImm) b x) :
      Instr F ([0xFC] ++ bn ++ b) (.memoryFill x)
  /-- `0xD0 ht:Bheaptype => REF.NULL ht` (5.3:140). -/
  | refNull {b : Bytes} {ht : Wasm.HeapType} (h : HeapType b ht) :
      Instr F ([0xD0] ++ b) (.refNull ht)
  /-- `0xD2 x:Bfuncidx => REF.FUNC x` (5.3:142). -/
  | refFunc {b : Bytes} {x : FuncIdx} (h : Index b x) : Instr F ([0xD2] ++ b) (.refFunc x)
  /-- `0xFB 20:Bu32 ht:Bheaptype => REF.TEST (REF ht)` (5.3:145). -/
  | refTest {bn b : Bytes} {ht : Wasm.HeapType} (hn : U32 bn 20) (h : HeapType b ht) :
      Instr F ([0xFB] ++ bn ++ b) (.refTest ⟨false, ht⟩)
  /-- `0xFB 21:Bu32 ht:Bheaptype => REF.TEST (REF NULL ht)` (5.3:146). -/
  | refTestNull {bn b : Bytes} {ht : Wasm.HeapType} (hn : U32 bn 21) (h : HeapType b ht) :
      Instr F ([0xFB] ++ bn ++ b) (.refTest ⟨true, ht⟩)
  /-- `0xFB 22:Bu32 ht:Bheaptype => REF.CAST (REF ht)` (5.3:147). -/
  | refCast {bn b : Bytes} {ht : Wasm.HeapType} (hn : U32 bn 22) (h : HeapType b ht) :
      Instr F ([0xFB] ++ bn ++ b) (.refCast ⟨false, ht⟩)
  /-- `0xFB 23:Bu32 ht:Bheaptype => REF.CAST (REF NULL ht)` (5.3:148). -/
  | refCastNull {bn b : Bytes} {ht : Wasm.HeapType} (hn : U32 bn 23) (h : HeapType b ht) :
      Instr F ([0xFB] ++ bn ++ b) (.refCast ⟨true, ht⟩)
  /-- `0xFB 0:Bu32 x:Btypeidx => STRUCT.NEW x` (5.3:152). -/
  | structNew {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 0) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.structNew x)
  /-- `0xFB 1:Bu32 x:Btypeidx => STRUCT.NEW_DEFAULT x` (5.3:153). -/
  | structNewDefault {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 1) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.structNewDefault x)
  /-- `0xFB 2:Bu32 x i => STRUCT.GET x i` (5.3:154). -/
  | structGet {bn b b' : Bytes} {x : TypeIdx} {i : FieldIdx} (hn : U32 bn 2) (h : Index b x)
      (h' : Index b' i) : Instr F ([0xFB] ++ bn ++ b ++ b') (.structGet none x i)
  /-- `0xFB 3:Bu32 x i => STRUCT.GET S x i` (5.3:155). -/
  | structGetS {bn b b' : Bytes} {x : TypeIdx} {i : FieldIdx} (hn : U32 bn 3) (h : Index b x)
      (h' : Index b' i) : Instr F ([0xFB] ++ bn ++ b ++ b') (.structGet (some .signed) x i)
  /-- `0xFB 4:Bu32 x i => STRUCT.GET U x i` (5.3:156). -/
  | structGetU {bn b b' : Bytes} {x : TypeIdx} {i : FieldIdx} (hn : U32 bn 4) (h : Index b x)
      (h' : Index b' i) : Instr F ([0xFB] ++ bn ++ b ++ b') (.structGet (some .unsigned) x i)
  /-- `0xFB 5:Bu32 x i => STRUCT.SET x i` (5.3:157). -/
  | structSet {bn b b' : Bytes} {x : TypeIdx} {i : FieldIdx} (hn : U32 bn 5) (h : Index b x)
      (h' : Index b' i) : Instr F ([0xFB] ++ bn ++ b ++ b') (.structSet x i)
  /-- `0xFB 6:Bu32 x => ARRAY.NEW x` (5.3:161). -/
  | arrayNew {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 6) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.arrayNew x)
  /-- `0xFB 7:Bu32 x => ARRAY.NEW_DEFAULT x` (5.3:162). -/
  | arrayNewDefault {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 7) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.arrayNewDefault x)
  /-- `0xFB 8:Bu32 x n:Bu32 => ARRAY.NEW_FIXED x n` (5.3:163). -/
  | arrayNewFixed {bn b b' : Bytes} {x : TypeIdx} {n : Fin (2 ^ 32)} (hn : U32 bn 8)
      (h : Index b x) (h' : U32 b' n.val) :
      Instr F ([0xFB] ++ bn ++ b ++ b') (.arrayNewFixed x n)
  /-- `0xFB 9:Bu32 x y:Bdataidx => ARRAY.NEW_DATA x y` (5.3:164). -/
  | arrayNewData {bn b b' : Bytes} {x : TypeIdx} {y : DataIdx} (hn : U32 bn 9) (h : Index b x)
      (h' : Index b' y) : Instr F ([0xFB] ++ bn ++ b ++ b') (.arrayNewData x y)
  /-- `0xFB 10:Bu32 x y:Belemidx => ARRAY.NEW_ELEM x y` (5.3:165). -/
  | arrayNewElem {bn b b' : Bytes} {x : TypeIdx} {y : ElemIdx} (hn : U32 bn 10) (h : Index b x)
      (h' : Index b' y) : Instr F ([0xFB] ++ bn ++ b ++ b') (.arrayNewElem x y)
  /-- `0xFB 11:Bu32 x => ARRAY.GET x` (5.3:166). -/
  | arrayGet {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 11) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.arrayGet none x)
  /-- `0xFB 12:Bu32 x => ARRAY.GET S x` (5.3:167). -/
  | arrayGetS {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 12) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.arrayGet (some .signed) x)
  /-- `0xFB 13:Bu32 x => ARRAY.GET U x` (5.3:168). -/
  | arrayGetU {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 13) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.arrayGet (some .unsigned) x)
  /-- `0xFB 14:Bu32 x => ARRAY.SET x` (5.3:169). -/
  | arraySet {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 14) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.arraySet x)
  /-- `0xFB 16:Bu32 x => ARRAY.FILL x` (5.3:171). -/
  | arrayFill {bn b : Bytes} {x : TypeIdx} (hn : U32 bn 16) (h : Index b x) :
      Instr F ([0xFB] ++ bn ++ b) (.arrayFill x)
  /-- `0xFB 17:Bu32 x_1 x_2 => ARRAY.COPY x_1 x_2` (5.3:172). -/
  | arrayCopy {bn b b' : Bytes} {x₁ x₂ : TypeIdx} (hn : U32 bn 17) (h : Index b x₁)
      (h' : Index b' x₂) : Instr F ([0xFB] ++ bn ++ b ++ b') (.arrayCopy x₁ x₂)
  /-- `0xFB 18:Bu32 x y:Bdataidx => ARRAY.INIT_DATA x y` (5.3:173). -/
  | arrayInitData {bn b b' : Bytes} {x : TypeIdx} {y : DataIdx} (hn : U32 bn 18) (h : Index b x)
      (h' : Index b' y) : Instr F ([0xFB] ++ bn ++ b ++ b') (.arrayInitData x y)
  /-- `0xFB 19:Bu32 x y:Belemidx => ARRAY.INIT_ELEM x y` (5.3:174). -/
  | arrayInitElem {bn b b' : Bytes} {x : TypeIdx} {y : ElemIdx} (hn : U32 bn 19) (h : Index b x)
      (h' : Index b' y) : Instr F ([0xFB] ++ bn ++ b ++ b') (.arrayInitElem x y)
  /-- `0x41 i:Bi32 => CONST I32 i` (5.3:192; `Bi32` read as `BiN(32)`, see errata). -/
  | i32Const {b : Bytes} {v : BitVec 32} (h : IN 32 b v) : Instr F ([0x41] ++ b) (.intConst .i32 v)
  /-- `0x42 i:Bi64 => CONST I64 i` (5.3:193; `Bi64` read as `BiN(64)`). -/
  | i64Const {b : Bytes} {v : BitVec 64} (h : IN 64 b v) : Instr F ([0x42] ++ b) (.intConst .i64 v)
  /-- `0x43 p:Bf32 => CONST F32 p` (5.3:194). -/
  | f32Const {b : Bytes} {p : BitVec 32} (h : FN 32 b p) :
      Instr F ([0x43] ++ b) (.floatConst .f32 p)
  /-- `0x44 p:Bf64 => CONST F64 p` (5.3:195). -/
  | f64Const {b : Bytes} {p : BitVec 64} (h : FN 64 b p) :
      Instr F ([0x44] ++ b) (.floatConst .f64 p)
  /-- Vector loads and stores `0xFD n:Bu32 (x,ao):Bmemarg` (5.3:396–417, `VecMemOp`). -/
  | vecMem {bn b : Bytes} {n : Nat} {mk : MemIdx → Wasm.MemArg → Wasm.Instr} {x : MemIdx}
      {ao : Wasm.MemArg} (h : VecMemOp n mk) (hn : U32 bn n) (hm : Memarg F b (x, ao)) :
      Instr F ([0xFD] ++ bn ++ b) (mk x ao)
  /-- Vector lane loads and stores `0xFD n:Bu32 (x,ao):Bmemarg i:Blaneidx` (`VecMemLaneOp`). -/
  | vecMemLane {bn b : Bytes} {n : Nat} {mk : MemIdx → Wasm.MemArg → LaneIdx → Wasm.Instr}
      {x : MemIdx} {ao : Wasm.MemArg} {l : UInt8} (h : VecMemLaneOp n mk) (hn : U32 bn n)
      (hm : Memarg F b (x, ao)) : Instr F ([0xFD] ++ bn ++ b ++ [l]) (mk x ao (laneOf l))
  /-- `0xFD 12:Bu32 (b:Bbyte)^16 => VCONST V128 $inv_ibytes_(128, b^16)` (5.3:421). -/
  | vecConst {bn bs : Bytes} (hn : U32 bn 12) (hl : bs.length = 16) :
      Instr F ([0xFD] ++ bn ++ bs) (.vecConst (BitVec.ofNat 128 (littleEndian bs)))
  /-- `0xFD 13:Bu32 (l:Blaneidx)^16 => VSHUFFLE (I8 X 16) l^16` (5.3:425). -/
  | vecShuffle {bn ls : Bytes} (hn : U32 bn 13) (hl : ls.length = 16) :
      Instr F ([0xFD] ++ bn ++ ls) (.vecShuffle (ls.map laneOf))
  /-- Lane extraction and replacement `0xFD n:Bu32 l:Blaneidx` (5.3:440–453, `VecLaneOp`). -/
  | vecLane {bn : Bytes} {n : Nat} {mk : LaneIdx → Wasm.Instr} {l : UInt8} (h : VecLaneOp n mk)
      (hn : U32 bn n) : Instr F ([0xFD] ++ bn ++ [l]) (mk (laneOf l))

/-- `(in:Binstr)*`. -/
inductive Instrs (F : Forms) : Bytes → List Wasm.Instr → Prop where
  | nil : Instrs F [] []
  | cons {b bs : Bytes} {i : Wasm.Instr} {is : List Wasm.Instr} (h : Instr F b i)
      (hs : Instrs F bs is) : Instrs F (b ++ bs) (i :: is)

end

/-- `Bexpr = (in:Binstr)* 0x0B => in*` (5.3:812–813). -/
inductive Expr (F : Forms) : Bytes → Wasm.Expr → Prop where
  | mk {b : Bytes} {is : List Wasm.Instr} (h : Instrs F b is) : Expr F (b ++ [0x0B]) is

/-! ## Data indices referenced by code (`$dataidx_funcs`, used by the module rule) -/

/-- The data indices an instruction mentions (`memory.init`, `data.drop`,
`array.new_data`, `array.init_data`), including nested bodies. -/
def Instr.dataIdxs : Wasm.Instr → List DataIdx
  | .memoryInit _ y | .dataDrop y | .arrayNewData _ y | .arrayInitData _ y => [y]
  | .block _ body | .loop _ body | .tryTable _ _ body =>
      body.attach.flatMap (fun i => dataIdxs i.val)
  | .if_ _ left right => left.attach.flatMap (fun i => dataIdxs i.val) ++
      right.attach.flatMap (fun i => dataIdxs i.val)
  | _ => []
termination_by instruction => sizeOf instruction
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- The data indices an expression mentions. -/
def Expr.dataIdxs (e : Wasm.Expr) : List DataIdx := e.flatMap Instr.dataIdxs

/-! ## Properties -/

/-! ### Generic lemmas -/

/-- Cancel a prefix-free production at the front of two equal byte strings. -/
theorem _root_.Silmaril.Wasm.Binary.PrefixFree.cancel {α : Type} {G : Bytes → α → Prop}
    (hG : PrefixFree G) {b b' r r' : Bytes} {a a' : α} (h : G b a) (h' : G b' a')
    (e : b ++ r = b' ++ r') : b = b' ∧ a = a' ∧ r = r' := by
  obtain ⟨rfl, rfl⟩ := hG h h' e
  exact ⟨rfl, rfl, List.append_cancel_left e⟩

/-- Weaken the element production of a sequence, on encodings no longer than the sequence. -/
theorem _root_.Silmaril.Wasm.Binary.Seq.imp {α : Type} {G G' : Bytes → α → Prop} {b : Bytes}
    {xs : List α} (h : Seq G b xs) (hg : ∀ {c x}, c.length ≤ b.length → G c x → G' c x) :
    Seq G' b xs := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    refine .cons (hg (by simp only [List.length_append]; omega) hx) (ih fun hc hx' => hg ?_ hx')
    simp only [List.length_append]; omega

theorem _root_.Silmaril.Wasm.Binary.Vec.imp {α : Type} {G G' : Bytes → α → Prop} {b : Bytes}
    {xs : List α} (h : Vec G b xs) (hg : ∀ {c x}, G c x → G' c x) : Vec G' b xs := by
  obtain ⟨hn, hs⟩ := h
  exact .mk hn (hs.imp fun _ hx => hg hx)

theorem Instrs.iff_seq {F : Forms} {b : Bytes} {is : List Wasm.Instr} :
    Instrs F b is ↔ Seq (Instr F) b is := by
  constructor
  · intro h
    induction is generalizing b with
    | nil => cases h; exact .nil
    | cons i is ih => cases h with | cons h hs => exact .cons h (ih hs)
  · intro h
    induction h with
    | nil => exact .nil
    | cons h _ ih => exact .cons h ih

/-- Every Core alignment exponent is below `2^6`: bit 6 of the flags is the memory-index
flag, and the flags are below `2^7`. -/
theorem Memarg.align_lt {F : Forms} {b : Bytes} {x : MemIdx} {a : Wasm.MemArg}
    (h : Memarg F b (x, a)) : a.align.val < 2 ^ 6 := by
  cases h with
  | mem0 _ ha _ => exact ha
  | memIdx _ _ _ hi ha _ _ => show _ < _; dsimp only; omega

/-! ### Monotonicity in the encoding forms -/

theorem Offset.mono {F G : Forms} (h : F.Le G) {b : Bytes} {m : Fin (2 ^ 64)}
    (ho : Offset F b m) : Offset G b m := by
  cases ho with
  | u64 g hm => exact .u64 (h _ g) hm
  | u32 hm => exact .u32 hm

theorem Memarg.mono {F G : Forms} (h : F.Le G) {b : Bytes} {a : MemIdx × Wasm.MemArg}
    (hm : Memarg F b a) : Memarg G b a := by
  cases hm with
  | mem0 hn ha ho => exact .mem0 hn ha (ho.mono h)
  | memIdx g hn lo hi ha hx ho => exact .memIdx (h _ g) hn lo hi ha hx (ho.mono h)

theorem BlockType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.BlockType}
    (ht : BlockType F b t) : BlockType G b t := by
  cases ht with
  | empty => exact .empty
  | value hv => exact .value (hv.mono h)
  | idx i hi => exact .idx i hi

theorem ReservedIdx.mono {k : IndexKind} {a a' : Bool} (h : a = true → a' = true) {b : Bytes}
    {x : Idx k} (hr : ReservedIdx a b x) : ReservedIdx a' b x := by
  cases hr with
  | idx g hx => exact .idx (h g) hx
  | zero => exact .zero

local macro "len_tac" : tactic =>
  `(tactic| (simp only [List.length_append, List.length_cons, List.length_nil]; omega))

/-- `Instr.mono` on encodings shorter than `N`, by induction on `N`. -/
theorem Instr.mono_lt {F G : Forms} (hle : F.Le G) :
    ∀ N : Nat, ∀ {b : Bytes} {i : Wasm.Instr}, b.length < N → Instr F b i → Instr G b i
  | 0, _, _, hlen, _ => absurd hlen (Nat.not_lt_zero _)
  | N + 1, b, i, hlen, hi => by
    have ihs : ∀ {c : Bytes} {is : List Wasm.Instr}, Instrs F c is → c.length < b.length →
        Instrs G c is := fun hc hl => Instrs.iff_seq.mpr <|
      (Instrs.iff_seq.mp hc).imp fun hl' hx => Instr.mono_lt hle N (by omega) hx
    cases hi with
    | plain a1 => exact .plain a1
    | prefixFB a1 a2 => exact .prefixFB a1 a2
    | prefixFC a1 a2 => exact .prefixFC a1 a2
    | prefixFD a1 a2 => exact .prefixFD a1 a2
    | selectT a1 => exact .selectT (a1.imp fun hv => ValType.mono hle hv)
    | block a1 a2 => exact .block (a1.mono hle) (ihs a2 (by len_tac))
    | loop a1 a2 => exact .loop (a1.mono hle) (ihs a2 (by len_tac))
    | if_ a1 a2 => exact .if_ (a1.mono hle) (ihs a2 (by len_tac))
    | ifElse a1 a2 a3 => exact .ifElse (a1.mono hle) (ihs a2 (by len_tac)) (ihs a3 (by len_tac))
    | throw a1 => exact .throw a1
    | br a1 => exact .br a1
    | brIf a1 => exact .brIf a1
    | brTable a1 a2 => exact .brTable a1 a2
    | call a1 => exact .call a1
    | callIndirect a1 a2 => exact .callIndirect a1 (a2.mono (hle _))
    | returnCall a1 => exact .returnCall a1
    | returnCallIndirect a1 a2 => exact .returnCallIndirect a1 a2
    | callRef a1 => exact .callRef a1
    | returnCallRef a1 => exact .returnCallRef a1
    | tryTable a1 a2 a3 => exact .tryTable (a1.mono hle) a2 (ihs a3 (by len_tac))
    | brOnNull a1 => exact .brOnNull a1
    | brOnNonNull a1 => exact .brOnNonNull a1
    | brOnCast a1 a2 a3 a4 a5 => exact .brOnCast a1 a2 a3 a4 a5
    | brOnCastFail a1 a2 a3 a4 a5 => exact .brOnCastFail a1 a2 a3 a4 a5
    | localGet a1 => exact .localGet a1
    | localSet a1 => exact .localSet a1
    | localTee a1 => exact .localTee a1
    | globalGet a1 => exact .globalGet a1
    | globalSet a1 => exact .globalSet a1
    | tableGet a1 => exact .tableGet a1
    | tableSet a1 => exact .tableSet a1
    | tableInit a1 a2 a3 => exact .tableInit a1 a2 a3
    | elemDrop a1 a2 => exact .elemDrop a1 a2
    | tableCopy a1 a2 a3 => exact .tableCopy a1 a2 a3
    | tableGrow a1 a2 => exact .tableGrow a1 a2
    | tableSize a1 a2 => exact .tableSize a1 a2
    | tableFill a1 a2 => exact .tableFill a1 a2
    | mem a1 a2 => exact .mem a1 (a2.mono hle)
    | memorySize a1 => exact .memorySize (a1.mono (hle _))
    | memoryGrow a1 => exact .memoryGrow (a1.mono (hle _))
    | memoryInit a1 a2 a3 => exact .memoryInit a1 a2 (a3.mono (hle _))
    | dataDrop a1 a2 => exact .dataDrop a1 a2
    | memoryCopy a1 a2 a3 => exact .memoryCopy a1 (a2.mono (hle _)) (a3.mono (hle _))
    | memoryFill a1 a2 => exact .memoryFill a1 (a2.mono (hle _))
    | refNull a1 => exact .refNull a1
    | refFunc a1 => exact .refFunc a1
    | refTest a1 a2 => exact .refTest a1 a2
    | refTestNull a1 a2 => exact .refTestNull a1 a2
    | refCast a1 a2 => exact .refCast a1 a2
    | refCastNull a1 a2 => exact .refCastNull a1 a2
    | structNew a1 a2 => exact .structNew a1 a2
    | structNewDefault a1 a2 => exact .structNewDefault a1 a2
    | structGet a1 a2 a3 => exact .structGet a1 a2 a3
    | structGetS a1 a2 a3 => exact .structGetS a1 a2 a3
    | structGetU a1 a2 a3 => exact .structGetU a1 a2 a3
    | structSet a1 a2 a3 => exact .structSet a1 a2 a3
    | arrayNew a1 a2 => exact .arrayNew a1 a2
    | arrayNewDefault a1 a2 => exact .arrayNewDefault a1 a2
    | arrayNewFixed a1 a2 a3 => exact .arrayNewFixed a1 a2 a3
    | arrayNewData a1 a2 a3 => exact .arrayNewData a1 a2 a3
    | arrayNewElem a1 a2 a3 => exact .arrayNewElem a1 a2 a3
    | arrayGet a1 a2 => exact .arrayGet a1 a2
    | arrayGetS a1 a2 => exact .arrayGetS a1 a2
    | arrayGetU a1 a2 => exact .arrayGetU a1 a2
    | arraySet a1 a2 => exact .arraySet a1 a2
    | arrayFill a1 a2 => exact .arrayFill a1 a2
    | arrayCopy a1 a2 a3 => exact .arrayCopy a1 a2 a3
    | arrayInitData a1 a2 a3 => exact .arrayInitData a1 a2 a3
    | arrayInitElem a1 a2 a3 => exact .arrayInitElem a1 a2 a3
    | i32Const a1 => exact .i32Const a1
    | i64Const a1 => exact .i64Const a1
    | f32Const a1 => exact .f32Const a1
    | f64Const a1 => exact .f64Const a1
    | vecMem a1 a2 a3 => exact .vecMem a1 a2 (a3.mono hle)
    | vecMemLane a1 a2 a3 => exact .vecMemLane a1 a2 (a3.mono hle)
    | vecConst a1 a2 => exact .vecConst a1 a2
    | vecShuffle a1 a2 => exact .vecShuffle a1 a2
    | vecLane a1 a2 => exact .vecLane a1 a2

theorem Instr.mono {F G : Forms} (h : F.Le G) {b : Bytes} {i : Wasm.Instr}
    (hi : Instr F b i) : Instr G b i :=
  Instr.mono_lt h _ (Nat.lt_succ_self _) hi

theorem Expr.mono {F G : Forms} (h : F.Le G) {b : Bytes} {e : Wasm.Expr}
    (he : Expr F b e) : Expr G b e := by
  cases he with
  | mk hi => exact .mk (Instrs.iff_seq.mpr ((Instrs.iff_seq.mp hi).imp fun _ hx => hx.mono h))

/-! ### Immediates -/

/-- A reserved index is in particular a `Bu32` index. -/
theorem ReservedIdx.index {k : IndexKind} {a : Bool} {b : Bytes} {x : Idx k}
    (h : ReservedIdx a b x) : Index b x := by
  cases h with
  | idx _ hx => exact hx
  | zero => exact (UN.byte 0x00 (by decide) (by decide) : U32 [0x00] 0)

/-- With every form enabled, the reserved-index relation is exactly `Bu32`. -/
theorem ReservedIdx.true_iff {k : IndexKind} (b : Bytes) (x : Idx k) :
    ReservedIdx true b x ↔ Index b x :=
  ⟨ReservedIdx.index, fun h => .idx rfl h⟩

theorem ReservedIdx.prefixFree {k : IndexKind} (a : Bool) :
    PrefixFree (ReservedIdx (k := k) a) := by
  intro _ _ _ _ _ _ h h' e
  exact Index.prefixFree h.index h'.index e

theorem Offset.prefixFree (F : Forms) : PrefixFree (Offset F) := by
  have key : ∀ {b : Bytes} {m : Fin (2 ^ 64)}, Offset F b m → U64 b m.val := fun h => by
    cases h with
    | u64 _ h => exact h
    | u32 h => exact UN.mono (by decide) h
  intro _ _ _ _ _ _ h h' e
  obtain ⟨rfl, hm⟩ := UN.prefixFree 64 (key h) (key h') e
  exact ⟨rfl, Fin.ext hm⟩

theorem Memarg.prefixFree (F : Forms) : PrefixFree (Memarg F) := by
  intro _ _ _ _ _ _ h h' e
  cases h with
  | @mem0 bn bm a m hn ha hm =>
    cases h' with
    | @mem0 bn' bm' a' m' hn' ha' hm' =>
      rw [List.append_assoc, List.append_assoc] at e
      obtain ⟨rfl, hv, e⟩ := (UN.prefixFree 32).cancel hn hn' e
      obtain ⟨rfl, rfl, -⟩ := (Offset.prefixFree F).cancel hm hm' e
      obtain rfl : a = a' := Fin.ext hv
      exact ⟨rfl, rfl⟩
    | memIdx _ hn' lo _ _ _ _ =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc] at e
      obtain ⟨-, hv, -⟩ := (UN.prefixFree 32).cancel hn hn' e
      omega
  | @memIdx bn bx bm n a x m _ hn lo hi ha hx hm =>
    cases h' with
    | mem0 hn' ha' _ =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc] at e
      obtain ⟨-, hv, -⟩ := (UN.prefixFree 32).cancel hn hn' e
      omega
    | @memIdx bn' bx' bm' n' a' x' m' _ hn' lo' hi' ha' hx' hm' =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := (UN.prefixFree 32).cancel hn hn' e
      obtain ⟨rfl, rfl, e⟩ := Index.prefixFree.cancel hx hx' e
      obtain ⟨rfl, rfl, -⟩ := (Offset.prefixFree F).cancel hm hm' e
      obtain rfl : a = a' := Fin.ext (ha.trans ha'.symm)
      exact ⟨rfl, rfl⟩

theorem CastOp.prefixFree : PrefixFree CastOp := by
  intro _ _ _ _ _ _ h h' e
  cases h <;> cases h' <;> first | exact ⟨rfl, rfl⟩ | simp at e

theorem Catch.prefixFree : PrefixFree Catch := by
  intro _ _ _ _ _ _ h h' e
  cases h with
  | catch_ hx hl =>
    cases h' <;> simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.cons.injEq] at e
    case catch_ hx' hl' =>
      obtain ⟨-, e⟩ := e
      obtain ⟨rfl, rfl, e⟩ := Index.prefixFree.cancel hx hx' e
      obtain ⟨rfl, rfl⟩ := Index.prefixFree hl hl' e
      exact ⟨rfl, rfl⟩
    all_goals exact absurd e.1 (by decide)
  | catchRef hx hl =>
    cases h' <;> simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.cons.injEq] at e
    case catchRef hx' hl' =>
      obtain ⟨-, e⟩ := e
      obtain ⟨rfl, rfl, e⟩ := Index.prefixFree.cancel hx hx' e
      obtain ⟨rfl, rfl⟩ := Index.prefixFree hl hl' e
      exact ⟨rfl, rfl⟩
    all_goals exact absurd e.1 (by decide)
  | catchAll hl =>
    cases h' <;> simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.cons.injEq] at e
    case catchAll hl' =>
      obtain ⟨-, e⟩ := e
      obtain ⟨rfl, rfl⟩ := Index.prefixFree hl hl' e
      exact ⟨rfl, rfl⟩
    all_goals exact absurd e.1 (by decide)
  | catchAllRef hl =>
    cases h' <;> simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.cons.injEq] at e
    case catchAllRef hl' =>
      obtain ⟨-, e⟩ := e
      obtain ⟨rfl, rfl⟩ := Index.prefixFree hl hl' e
      exact ⟨rfl, rfl⟩
    all_goals exact absurd e.1 (by decide)

/-- A value type's first byte lies in `(0x40, 0x80)` (a weakening of `ValType.head`). -/
theorem ValType.head_range {F : Forms} {b : Bytes} {t : Wasm.ValType} (h : ValType F b t) :
    ∃ c rest, b = c :: rest ∧ 0x40 < c.toNat ∧ c.toNat < 0x80 := by
  obtain ⟨c, rest, rfl, h₁, h₂, -⟩ := ValType.head h
  exact ⟨c, rest, rfl, by omega, by omega⟩

/-- A signed LEB128 encoding whose first byte lies in `[0x40, 0x80)` is negative. -/
theorem SN.neg_of_head {N : Nat} {c : UInt8} {rest : Bytes} {v : Int}
    (h : SN N (c :: rest) v) (h₁ : 0x40 ≤ c.toNat) (h₂ : c.toNat < 0x80) : v < 0 := by
  cases h with
  | pos _ hc _ => simp only [Nat.reducePow] at hc; omega
  | neg _ _ _ _ => simp only [Int.reducePow]; omega
  | cont _ hc _ _ => simp only [Nat.reducePow] at hc; omega

theorem BlockType.prefixFree (F : Forms) : PrefixFree (BlockType F) := by
  -- An `s33` type index is non-negative, so its first byte is not in `[0x40, 0x80)`.
  have key : ∀ {c : UInt8} {b r s : Bytes} {i : TypeIdx}, S33 b i.toNat → b ++ r = c :: s →
      0x40 ≤ c.toNat → c.toNat < 0x80 → False := by
    intro c b r s i h e h₁ h₂
    cases b with
    | nil => cases h
    | cons c' b =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      have := SN.neg_of_head h h₁ h₂
      omega
  intro _ _ _ _ _ _ h h' e
  cases h with
  | empty =>
    cases h' with
    | empty => exact ⟨rfl, rfl⟩
    | value hv =>
      obtain ⟨c, rest, rfl, h₁, -⟩ := hv.head_range
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      exact absurd h₁ (by decide)
    | idx i hi => exact (key hi e.symm (by decide) (by decide)).elim
  | value hv =>
    cases h' with
    | empty =>
      obtain ⟨c, rest, rfl, h₁, -⟩ := hv.head_range
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      exact absurd h₁ (by decide)
    | value hv' =>
      obtain ⟨rfl, rfl⟩ := ValType.prefixFree F hv hv' e
      exact ⟨rfl, rfl⟩
    | idx i hi =>
      obtain ⟨c, rest, rfl, h₁, h₂⟩ := hv.head_range
      exact (key hi e.symm h₁.le h₂).elim
  | idx i hi =>
    cases h' with
    | empty => exact (key hi e (by decide) (by decide)).elim
    | value hv' =>
      obtain ⟨c, rest, rfl, h₁, h₂⟩ := hv'.head_range
      exact (key hi e h₁.le h₂).elim
    | idx i' hi' =>
      obtain ⟨rfl, hv⟩ := SN.prefixFree 33 hi hi' e
      obtain rfl : i = i' := Idx.toNat_injective (by exact_mod_cast hv)
      exact ⟨rfl, rfl⟩

/-! ### Dispatch on the first byte

`Instr.prefixFree` is proved without comparing the ~80 rules of `Instr` pairwise. The
first byte of an encoding selects a `Dispatch.Kind` (`Dispatch.kind`, a computable
function built on the table lookups of `Core/OpcodesProps.lean`), and `Instr.inv` reads
an encoding as the `Dispatch.KSpec` of its kind: the remaining bytes and the instruction
in one shape per kind. Two encodings sharing a first byte then have the same kind, and
`Dispatch.KSpec.unique` compares them shape by shape; the `0xFB`/`0xFC`/`0xFD` prefixes
dispatch once more on the sub-opcode. Nested bodies are handled by strong induction on
the length of the encoding (`Instr.pfBelow`). -/

namespace Dispatch

/-- The rule family selected by an instruction's first byte. -/
inductive Kind where
  | plain | mem | selectT | block | loop | if_ | throw | br | brIf | brTable | call
  | callIndirect | returnCall | returnCallIndirect | callRef | returnCallRef | tryTable
  | brOnNull | brOnNonNull | localGet | localSet | localTee | globalGet | globalSet
  | tableGet | tableSet | memorySize | memoryGrow | refNull | refFunc
  | i32Const | i64Const | f32Const | f64Const | prefixFB | prefixFC | prefixFD | invalid

/-- The kind of a first byte. -/
def kind (c : UInt8) : Kind :=
  if (plainOp? c).isSome then .plain else if (memOp? c).isSome then .mem else
  match c.toNat with
  | 0x1C => .selectT | 0x02 => .block | 0x03 => .loop | 0x04 => .if_ | 0x08 => .throw
  | 0x0C => .br | 0x0D => .brIf | 0x0E => .brTable | 0x10 => .call | 0x11 => .callIndirect
  | 0x12 => .returnCall | 0x13 => .returnCallIndirect | 0x14 => .callRef
  | 0x15 => .returnCallRef | 0x1F => .tryTable | 0xD5 => .brOnNull | 0xD6 => .brOnNonNull
  | 0x20 => .localGet | 0x21 => .localSet | 0x22 => .localTee | 0x23 => .globalGet
  | 0x24 => .globalSet | 0x25 => .tableGet | 0x26 => .tableSet | 0x3F => .memorySize
  | 0x40 => .memoryGrow | 0xD0 => .refNull | 0xD2 => .refFunc | 0x41 => .i32Const
  | 0x42 => .i64Const | 0x43 => .f32Const | 0x44 => .f64Const | 0xFB => .prefixFB
  | 0xFC => .prefixFC | 0xFD => .prefixFD | _ => .invalid

/-- The rule family selected by a `0xFB` sub-opcode. -/
inductive FBKind where
  | plain | structNew | structNewDefault | structGet | structGetS | structGetU | structSet
  | arrayNew | arrayNewDefault | arrayNewFixed | arrayNewData | arrayNewElem | arrayGet
  | arrayGetS | arrayGetU | arraySet | arrayFill | arrayCopy | arrayInitData | arrayInitElem
  | refTest | refTestNull | refCast | refCastNull | brOnCast | brOnCastFail | invalid

def fbKind (n : Nat) : FBKind :=
  if (prefixFBOp? n).isSome then .plain else
  match n with
  | 0 => .structNew | 1 => .structNewDefault | 2 => .structGet | 3 => .structGetS
  | 4 => .structGetU | 5 => .structSet | 6 => .arrayNew | 7 => .arrayNewDefault
  | 8 => .arrayNewFixed | 9 => .arrayNewData | 10 => .arrayNewElem | 11 => .arrayGet
  | 12 => .arrayGetS | 13 => .arrayGetU | 14 => .arraySet | 16 => .arrayFill
  | 17 => .arrayCopy | 18 => .arrayInitData | 19 => .arrayInitElem | 20 => .refTest
  | 21 => .refTestNull | 22 => .refCast | 23 => .refCastNull | 24 => .brOnCast
  | 25 => .brOnCastFail | _ => .invalid

/-- The rule family selected by a `0xFC` sub-opcode. -/
inductive FCKind where
  | plain | memoryInit | dataDrop | memoryCopy | memoryFill | tableInit | elemDrop | tableCopy
  | tableGrow | tableSize | tableFill | invalid

def fcKind (n : Nat) : FCKind :=
  if (prefixFCOp? n).isSome then .plain else
  match n with
  | 8 => .memoryInit | 9 => .dataDrop | 10 => .memoryCopy | 11 => .memoryFill
  | 12 => .tableInit | 13 => .elemDrop | 14 => .tableCopy | 15 => .tableGrow
  | 16 => .tableSize | 17 => .tableFill | _ => .invalid

/-- The rule family selected by a `0xFD` sub-opcode. -/
inductive FDKind where
  | plain | mem | memLane | lane | const | shuffle | invalid

def fdKind (n : Nat) : FDKind :=
  if (prefixFDOp? n).isSome then .plain
  else if (vecMemOp? n).isSome then .mem
  else if (vecMemLaneOp? n).isSome then .memLane
  else if (vecLaneOp? n).isSome then .lane
  else match n with
  | 12 => .const | 13 => .shuffle | _ => .invalid

/-! #### Shapes of the remaining bytes -/

/-- One immediate. -/
def One {α : Type} (G : Bytes → α → Prop) (f : α → Wasm.Instr) (rest : Bytes)
    (i : Wasm.Instr) : Prop :=
  ∃ x, G rest x ∧ i = f x

/-- Two immediates. -/
def Two {α β : Type} (G : Bytes → α → Prop) (H : Bytes → β → Prop) (f : α → β → Wasm.Instr)
    (rest : Bytes) (i : Wasm.Instr) : Prop :=
  ∃ b b' x y, rest = b ++ b' ∧ G b x ∧ H b' y ∧ i = f x y

/-- A block type and a body terminated by `end`. -/
def Blk (F : Forms) (f : Wasm.BlockType → List Wasm.Instr → Wasm.Instr) (rest : Bytes)
    (i : Wasm.Instr) : Prop :=
  ∃ bt b t body, rest = bt ++ (b ++ [0x0B]) ∧ BlockType F bt t ∧ Instrs F b body ∧
    i = f t body

/-- `if` with an `else` branch. -/
def IfElse (F : Forms) (rest : Bytes) (i : Wasm.Instr) : Prop :=
  ∃ bt b₁ b₂ t body₁ body₂, rest = bt ++ (b₁ ++ 0x05 :: (b₂ ++ [0x0B])) ∧ BlockType F bt t ∧
    Instrs F b₁ body₁ ∧ Instrs F b₂ body₂ ∧ i = .if_ t body₁ body₂

/-- `try_table`. -/
def TryT (F : Forms) (rest : Bytes) (i : Wasm.Instr) : Prop :=
  ∃ bt bc b t cs body, rest = bt ++ (bc ++ (b ++ [0x0B])) ∧ BlockType F bt t ∧
    Vec Catch bc cs ∧ Instrs F b body ∧ i = .tryTable t cs body

/-- `br_on_cast` and `br_on_cast_fail`. -/
def Cast (f : LabelIdx → Wasm.RefType → Wasm.RefType → Wasm.Instr) (rest : Bytes)
    (i : Wasm.Instr) : Prop :=
  ∃ bc bl b₁ b₂ n₁ n₂ l h₁ h₂, rest = bc ++ (bl ++ (b₁ ++ b₂)) ∧ CastOp bc (n₁, n₂) ∧
    Index bl l ∧ HeapType b₁ h₁ ∧ HeapType b₂ h₂ ∧ i = f l ⟨n₁, h₁⟩ ⟨n₂, h₂⟩

/-- A `u32` immediate valued in `Fin (2 ^ 32)`. -/
def U32Fin (b : Bytes) (m : Fin (2 ^ 32)) : Prop := U32 b m.val

theorem U32Fin.prefixFree : PrefixFree U32Fin := by
  intro _ _ _ _ _ _ h h' e
  obtain ⟨rfl, hv⟩ := UN.prefixFree 32 h h' e
  exact ⟨rfl, Fin.ext hv⟩

/-! #### Specifications per kind -/

def FBSpec : FBKind → Nat → Bytes → Wasm.Instr → Prop
  | .plain, n, rest, i => rest = [] ∧ PrefixFBOp n i
  | .structNew, _, rest, i => One Index Wasm.Instr.structNew rest i
  | .structNewDefault, _, rest, i => One Index Wasm.Instr.structNewDefault rest i
  | .structGet, _, rest, i => Two Index Index (Wasm.Instr.structGet none) rest i
  | .structGetS, _, rest, i => Two Index Index (Wasm.Instr.structGet (some .signed)) rest i
  | .structGetU, _, rest, i => Two Index Index (Wasm.Instr.structGet (some .unsigned)) rest i
  | .structSet, _, rest, i => Two Index Index Wasm.Instr.structSet rest i
  | .arrayNew, _, rest, i => One Index Wasm.Instr.arrayNew rest i
  | .arrayNewDefault, _, rest, i => One Index Wasm.Instr.arrayNewDefault rest i
  | .arrayNewFixed, _, rest, i => Two Index U32Fin Wasm.Instr.arrayNewFixed rest i
  | .arrayNewData, _, rest, i => Two Index Index Wasm.Instr.arrayNewData rest i
  | .arrayNewElem, _, rest, i => Two Index Index Wasm.Instr.arrayNewElem rest i
  | .arrayGet, _, rest, i => One Index (Wasm.Instr.arrayGet none) rest i
  | .arrayGetS, _, rest, i => One Index (Wasm.Instr.arrayGet (some .signed)) rest i
  | .arrayGetU, _, rest, i => One Index (Wasm.Instr.arrayGet (some .unsigned)) rest i
  | .arraySet, _, rest, i => One Index Wasm.Instr.arraySet rest i
  | .arrayFill, _, rest, i => One Index Wasm.Instr.arrayFill rest i
  | .arrayCopy, _, rest, i => Two Index Index Wasm.Instr.arrayCopy rest i
  | .arrayInitData, _, rest, i => Two Index Index Wasm.Instr.arrayInitData rest i
  | .arrayInitElem, _, rest, i => Two Index Index Wasm.Instr.arrayInitElem rest i
  | .refTest, _, rest, i => One HeapType (fun ht => Wasm.Instr.refTest ⟨false, ht⟩) rest i
  | .refTestNull, _, rest, i => One HeapType (fun ht => Wasm.Instr.refTest ⟨true, ht⟩) rest i
  | .refCast, _, rest, i => One HeapType (fun ht => Wasm.Instr.refCast ⟨false, ht⟩) rest i
  | .refCastNull, _, rest, i => One HeapType (fun ht => Wasm.Instr.refCast ⟨true, ht⟩) rest i
  | .brOnCast, _, rest, i => Cast Wasm.Instr.brOnCast rest i
  | .brOnCastFail, _, rest, i => Cast Wasm.Instr.brOnCastFail rest i
  | .invalid, _, _, _ => False

def FCSpec (F : Forms) : FCKind → Nat → Bytes → Wasm.Instr → Prop
  | .plain, n, rest, i => rest = [] ∧ PrefixFCOp n i
  | .memoryInit, _, rest, i => Two Index (ReservedIdx (F .memIdxImm))
      (fun (y : DataIdx) (x : MemIdx) => Wasm.Instr.memoryInit x y) rest i
  | .dataDrop, _, rest, i => One Index Wasm.Instr.dataDrop rest i
  | .memoryCopy, _, rest, i => Two (ReservedIdx (F .memIdxImm)) (ReservedIdx (F .memIdxImm))
      Wasm.Instr.memoryCopy rest i
  | .memoryFill, _, rest, i => One (ReservedIdx (F .memIdxImm)) Wasm.Instr.memoryFill rest i
  | .tableInit, _, rest, i => Two Index Index
      (fun (y : ElemIdx) (x : TableIdx) => Wasm.Instr.tableInit x y) rest i
  | .elemDrop, _, rest, i => One Index Wasm.Instr.elemDrop rest i
  | .tableCopy, _, rest, i => Two Index Index Wasm.Instr.tableCopy rest i
  | .tableGrow, _, rest, i => One Index Wasm.Instr.tableGrow rest i
  | .tableSize, _, rest, i => One Index Wasm.Instr.tableSize rest i
  | .tableFill, _, rest, i => One Index Wasm.Instr.tableFill rest i
  | .invalid, _, _, _ => False

def FDSpec (F : Forms) : FDKind → Nat → Bytes → Wasm.Instr → Prop
  | .plain, n, rest, i => rest = [] ∧ PrefixFDOp n i
  | .mem, n, rest, i => ∃ mk x ao, VecMemOp n mk ∧ Memarg F rest (x, ao) ∧ i = mk x ao
  | .memLane, n, rest, i => ∃ b l mk x ao, rest = b ++ [l] ∧ VecMemLaneOp n mk ∧
      Memarg F b (x, ao) ∧ i = mk x ao (laneOf l)
  | .lane, n, rest, i => ∃ l mk, rest = [l] ∧ VecLaneOp n mk ∧ i = mk (laneOf l)
  | .const, _, rest, i =>
      rest.length = 16 ∧ i = .vecConst (BitVec.ofNat 128 (littleEndian rest))
  | .shuffle, _, rest, i => rest.length = 16 ∧ i = .vecShuffle (rest.map laneOf)
  | .invalid, _, _, _ => False

/-- The bytes after the first byte `c`, and the instruction, for the kind of `c`. -/
def KSpec (F : Forms) : Kind → UInt8 → Bytes → Wasm.Instr → Prop
  | .plain, c, rest, i => rest = [] ∧ PlainOp c i
  | .mem, c, rest, i => ∃ mk x ao, MemOp c mk ∧ Memarg F rest (x, ao) ∧ i = mk x ao
  | .selectT, _, rest, i => One (Vec (ValType F)) (fun ts => Wasm.Instr.select (some ts)) rest i
  | .block, _, rest, i => Blk F Wasm.Instr.block rest i
  | .loop, _, rest, i => Blk F Wasm.Instr.loop rest i
  | .if_, _, rest, i => Blk F (fun t body => Wasm.Instr.if_ t body []) rest i ∨ IfElse F rest i
  | .throw, _, rest, i => One Index Wasm.Instr.throw rest i
  | .br, _, rest, i => One Index Wasm.Instr.br rest i
  | .brIf, _, rest, i => One Index Wasm.Instr.brIf rest i
  | .brTable, _, rest, i => Two (Vec Index) Index Wasm.Instr.brTable rest i
  | .call, _, rest, i => One Index Wasm.Instr.call rest i
  | .callIndirect, _, rest, i => Two Index (ReservedIdx (F .tableIdxImm))
      (fun (y : TypeIdx) (x : TableIdx) => Wasm.Instr.callIndirect x y) rest i
  | .returnCall, _, rest, i => One Index Wasm.Instr.returnCall rest i
  | .returnCallIndirect, _, rest, i => Two Index Index
      (fun (y : TypeIdx) (x : TableIdx) => Wasm.Instr.returnCallIndirect x y) rest i
  | .callRef, _, rest, i => One Index Wasm.Instr.callRef rest i
  | .returnCallRef, _, rest, i => One Index Wasm.Instr.returnCallRef rest i
  | .tryTable, _, rest, i => TryT F rest i
  | .brOnNull, _, rest, i => One Index Wasm.Instr.brOnNull rest i
  | .brOnNonNull, _, rest, i => One Index Wasm.Instr.brOnNonNull rest i
  | .localGet, _, rest, i => One Index Wasm.Instr.localGet rest i
  | .localSet, _, rest, i => One Index Wasm.Instr.localSet rest i
  | .localTee, _, rest, i => One Index Wasm.Instr.localTee rest i
  | .globalGet, _, rest, i => One Index Wasm.Instr.globalGet rest i
  | .globalSet, _, rest, i => One Index Wasm.Instr.globalSet rest i
  | .tableGet, _, rest, i => One Index Wasm.Instr.tableGet rest i
  | .tableSet, _, rest, i => One Index Wasm.Instr.tableSet rest i
  | .memorySize, _, rest, i => One (ReservedIdx (F .memIdxImm)) Wasm.Instr.memorySize rest i
  | .memoryGrow, _, rest, i => One (ReservedIdx (F .memIdxImm)) Wasm.Instr.memoryGrow rest i
  | .refNull, _, rest, i => One HeapType Wasm.Instr.refNull rest i
  | .refFunc, _, rest, i => One Index Wasm.Instr.refFunc rest i
  | .i32Const, _, rest, i => One (IN 32) (Wasm.Instr.intConst .i32) rest i
  | .i64Const, _, rest, i => One (IN 64) (Wasm.Instr.intConst .i64) rest i
  | .f32Const, _, rest, i => One (FN 32) (Wasm.Instr.floatConst .f32) rest i
  | .f64Const, _, rest, i => One (FN 64) (Wasm.Instr.floatConst .f64) rest i
  | .prefixFB, _, rest, i => ∃ bn n r, rest = bn ++ r ∧ U32 bn n ∧ FBSpec (fbKind n) n r i
  | .prefixFC, _, rest, i => ∃ bn n r, rest = bn ++ r ∧ U32 bn n ∧ FCSpec F (fcKind n) n r i
  | .prefixFD, _, rest, i => ∃ bn n r, rest = bn ++ r ∧ U32 bn n ∧ FDSpec F (fdKind n) n r i
  | .invalid, _, _, _ => False

/-! #### Kinds of the table opcodes -/

theorem kind_plain {op : UInt8} {i : Wasm.Instr} (h : PlainOp op i) : kind op = .plain := by
  simp [kind, h.lookup]

theorem kind_mem {op : UInt8} {mk : MemIdx → MemArg → Wasm.Instr} (h : MemOp op mk) :
    kind op = .mem := by
  simp [kind, h.lookup, h.plainOp?_eq_none]

theorem fbKind_plain {n : Nat} {i : Wasm.Instr} (h : PrefixFBOp n i) : fbKind n = .plain := by
  simp [fbKind, h.lookup]

theorem fcKind_plain {n : Nat} {i : Wasm.Instr} (h : PrefixFCOp n i) : fcKind n = .plain := by
  simp [fcKind, h.lookup]

theorem fdKind_plain {n : Nat} {i : Wasm.Instr} (h : PrefixFDOp n i) : fdKind n = .plain := by
  simp [fdKind, h.lookup]

theorem fdKind_mem {n : Nat} {mk : MemIdx → MemArg → Wasm.Instr} (h : VecMemOp n mk) :
    fdKind n = .mem := by
  simp [fdKind, h.lookup, h.prefixFDOp?_eq_none]

theorem fdKind_memLane {n : Nat} {mk : MemIdx → MemArg → LaneIdx → Wasm.Instr}
    (h : VecMemLaneOp n mk) : fdKind n = .memLane := by
  obtain ⟨h₁, h₂⟩ := h.lookups_eq_none
  simp [fdKind, h.lookup, h₁, h₂]

theorem fdKind_lane {n : Nat} {mk : LaneIdx → Wasm.Instr} (h : VecLaneOp n mk) :
    fdKind n = .lane := by
  obtain ⟨h₁, h₂, h₃⟩ := h.lookups_eq_none
  simp [fdKind, h.lookup, h₁, h₂, h₃]

end Dispatch

open Dispatch

/-- Every instruction encoding begins with a byte other than `else` (`0x05`) and `end`
(`0x0B`). -/
theorem Instr.head {F : Forms} {b : Bytes} {i : Wasm.Instr} (h : Instr F b i) :
    ∃ c rest, b = c :: rest ∧ c ≠ 0x0B ∧ c ≠ 0x05 := by
  cases h
  all_goals first
    | exact ⟨_, [], rfl, PlainOp.ne_end ‹_›⟩
    | exact ⟨_, _, rfl, MemOp.ne_end ‹_›⟩
    | exact ⟨_, _, rfl, by decide, by decide⟩

local macro "inv_fin" : tactic => `(tactic| first
  | exact ⟨_, ‹_›, rfl⟩
  | exact ⟨‹_›, rfl⟩
  | (refine ⟨_, _, _, ‹_›, ‹_›, ?_⟩; rfl)
  | (refine ⟨_, _, _, _, _, rfl, ‹_›, ‹_›, ?_⟩; rfl)
  | (refine ⟨_, _, rfl, ‹_›, ?_⟩; rfl)
  | exact ⟨_, _, _, _, rfl, ‹_›, ‹_›, rfl⟩
  | exact ⟨_, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, rfl⟩
  | exact ⟨_, _, _, _, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩
  | exact .inl ⟨_, _, _, _, rfl, ‹_›, ‹_›, rfl⟩
  | exact .inr ⟨_, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, rfl⟩)

/-- Inversion on the first byte: an encoding `c :: rest` is described by the kind of `c`. -/
theorem Instr.inv {F : Forms} {b : Bytes} {i : Wasm.Instr} (h : Instr F b i) {c : UInt8}
    {rest : Bytes} (hb : b = c :: rest) : KSpec F (kind c) c rest i := by
  cases h <;>
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq] at hb <;>
    obtain ⟨rfl, rfl⟩ := hb
  all_goals first
    | (rw [kind_plain ‹_›]; whnf; exact ⟨rfl, ‹_›⟩)
    | (rw [kind_mem ‹_›]; whnf; refine ⟨_, _, _, ‹_›, ‹_›, ?_⟩; rfl)
    | (whnf
       first
        | inv_fin
        | (refine ⟨_, _, [], (List.append_nil _).symm, ‹_›, ?_⟩
           first
            | (rw [fbKind_plain ‹_›]; whnf; exact ⟨rfl, ‹_›⟩)
            | (rw [fcKind_plain ‹_›]; whnf; exact ⟨rfl, ‹_›⟩)
            | (rw [fdKind_plain ‹_›]; whnf; exact ⟨rfl, ‹_›⟩))
        | (refine ⟨_, _, _, rfl, ‹_›, ?_⟩
           first
            | (rw [fdKind_mem ‹_›]; whnf; inv_fin)
            | (rw [fdKind_memLane ‹_›]; whnf; inv_fin)
            | (rw [fdKind_lane ‹_›]; whnf; inv_fin)
            | (whnf; inv_fin)))

/-! ### Uniqueness per shape -/

/-- Prefix-freeness of `Instr` on encodings shorter than `N`. -/
def PFBelow (F : Forms) (N : Nat) : Prop :=
  ∀ ⦃b b' r r' : Bytes⦄ ⦃i i' : Wasm.Instr⦄, b.length < N → Instr F b i → Instr F b' i' →
    b ++ r = b' ++ r' → b = b' ∧ i = i'

/-- Two instruction sequences, each followed by `else` or `end`, sharing a prefix agree. -/
theorem seq_term {F : Forms} {M : Nat} (ih : PFBelow F M) {b : Bytes} {is : List Wasm.Instr}
    (h : Seq (Instr F) b is) (hl : b.length < M) {b' : Bytes} {is' : List Wasm.Instr}
    (h' : Seq (Instr F) b' is') {t t' : UInt8} {r r' : Bytes} (ht : t = 0x0B ∨ t = 0x05)
    (ht' : t' = 0x0B ∨ t' = 0x05) (e : b ++ t :: r = b' ++ t' :: r') :
    b = b' ∧ is = is' ∧ t = t' ∧ r = r' := by
  induction h generalizing b' is' with
  | nil =>
    cases h' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      exact ⟨rfl, rfl, e⟩
    | cons hx _ =>
      obtain ⟨c, rest, rfl, h₁, h₂⟩ := Instr.head hx
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      rcases ht with rfl | rfl <;> contradiction
  | cons hx hs ihs =>
    cases h' with
    | nil =>
      obtain ⟨c, rest, rfl, h₁, h₂⟩ := Instr.head hx
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      rcases ht' with rfl | rfl <;> contradiction
    | cons hx' hs' =>
      rw [List.append_assoc, List.append_assoc] at e
      obtain ⟨rfl, rfl⟩ := ih (by simp only [List.length_append] at hl; omega) hx hx' e
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        ihs (by simp only [List.length_append] at hl; omega) hs' (List.append_cancel_left e)
      exact ⟨rfl, rfl, rfl, rfl⟩

namespace Dispatch

theorem One.unique {α : Type} {G : Bytes → α → Prop} {f : α → Wasm.Instr}
    {rest rest' r r' : Bytes} {i i' : Wasm.Instr} (hG : PrefixFree G) (s : One G f rest i)
    (s' : One G f rest' i') (e : rest ++ r = rest' ++ r') : rest = rest' ∧ i = i' := by
  obtain ⟨x, hx, rfl⟩ := s
  obtain ⟨x', hx', rfl⟩ := s'
  obtain ⟨rfl, rfl⟩ := hG hx hx' e
  exact ⟨rfl, rfl⟩

theorem Two.unique {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    {f : α → β → Wasm.Instr} {rest rest' r r' : Bytes} {i i' : Wasm.Instr} (hG : PrefixFree G)
    (hH : PrefixFree H) (s : Two G H f rest i) (s' : Two G H f rest' i')
    (e : rest ++ r = rest' ++ r') : rest = rest' ∧ i = i' := by
  obtain ⟨b, c, x, y, rfl, hx, hy, rfl⟩ := s
  obtain ⟨b', c', x', y', rfl, hx', hy', rfl⟩ := s'
  rw [List.append_assoc, List.append_assoc] at e
  obtain ⟨rfl, rfl, e⟩ := hG.cancel hx hx' e
  obtain ⟨rfl, rfl⟩ := hH hy hy' e
  exact ⟨rfl, rfl⟩

theorem Blk.unique {F : Forms} {M : Nat} (ih : PFBelow F M)
    {f : Wasm.BlockType → List Wasm.Instr → Wasm.Instr} {rest rest' r r' : Bytes}
    {i i' : Wasm.Instr} (hl : rest.length ≤ M) (s : Blk F f rest i) (s' : Blk F f rest' i')
    (e : rest ++ r = rest' ++ r') : rest = rest' ∧ i = i' := by
  obtain ⟨bt, b, t, body, rfl, ht, hb, rfl⟩ := s
  obtain ⟨bt', b', t', body', rfl, ht', hb', rfl⟩ := s'
  simp only [List.append_assoc, List.singleton_append] at e
  obtain ⟨rfl, rfl, e⟩ := (BlockType.prefixFree F).cancel ht ht' e
  obtain ⟨rfl, rfl, -, -⟩ := seq_term ih (Instrs.iff_seq.mp hb)
    (by simp only [List.length_append, List.length_cons, List.length_nil] at hl; omega)
    (Instrs.iff_seq.mp hb') (.inl rfl) (.inl rfl) e
  exact ⟨rfl, rfl⟩

theorem IfS.unique {F : Forms} {M : Nat} (ih : PFBelow F M) {rest rest' r r' : Bytes}
    {i i' : Wasm.Instr} (hl : rest.length ≤ M)
    (s : Blk F (fun t body => Wasm.Instr.if_ t body []) rest i ∨ IfElse F rest i)
    (s' : Blk F (fun t body => Wasm.Instr.if_ t body []) rest' i' ∨ IfElse F rest' i')
    (e : rest ++ r = rest' ++ r') : rest = rest' ∧ i = i' := by
  rcases s with s | ⟨bt, b₁, b₂, t, body₁, body₂, rfl, ht, h₁, h₂, rfl⟩ <;>
    rcases s' with s' | ⟨bt', b₁', b₂', t', body₁', body₂', rfl, ht', h₁', h₂', rfl⟩
  · exact Blk.unique ih hl s s' e
  · obtain ⟨bt, b, t, body, rfl, ht, hb, rfl⟩ := s
    simp only [List.append_assoc, List.cons_append] at e
    obtain ⟨rfl, rfl, e⟩ := (BlockType.prefixFree F).cancel ht ht' e
    obtain ⟨-, -, h, -⟩ := seq_term ih (Instrs.iff_seq.mp hb)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hl; omega)
      (Instrs.iff_seq.mp h₁') (.inl rfl) (.inr rfl) e
    exact absurd h (by decide)
  · obtain ⟨bt', b', t', body', rfl, ht', hb', rfl⟩ := s'
    simp only [List.append_assoc, List.cons_append] at e
    obtain ⟨rfl, rfl, e⟩ := (BlockType.prefixFree F).cancel ht ht' e
    obtain ⟨-, -, h, -⟩ := seq_term ih (Instrs.iff_seq.mp h₁)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hl; omega)
      (Instrs.iff_seq.mp hb') (.inr rfl) (.inl rfl) e
    exact absurd h (by decide)
  · simp only [List.append_assoc, List.cons_append] at e
    obtain ⟨rfl, rfl, e⟩ := (BlockType.prefixFree F).cancel ht ht' e
    obtain ⟨rfl, rfl, -, e⟩ := seq_term ih (Instrs.iff_seq.mp h₁)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hl; omega)
      (Instrs.iff_seq.mp h₁') (.inr rfl) (.inr rfl) e
    obtain ⟨rfl, rfl, -, -⟩ := seq_term ih (Instrs.iff_seq.mp h₂)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hl; omega)
      (Instrs.iff_seq.mp h₂') (.inl rfl) (.inl rfl) e
    exact ⟨rfl, rfl⟩

theorem TryT.unique {F : Forms} {M : Nat} (ih : PFBelow F M) {rest rest' r r' : Bytes}
    {i i' : Wasm.Instr} (hl : rest.length ≤ M) (s : TryT F rest i) (s' : TryT F rest' i')
    (e : rest ++ r = rest' ++ r') : rest = rest' ∧ i = i' := by
  obtain ⟨bt, bc, b, t, cs, body, rfl, ht, hc, hb, rfl⟩ := s
  obtain ⟨bt', bc', b', t', cs', body', rfl, ht', hc', hb', rfl⟩ := s'
  simp only [List.append_assoc, List.singleton_append] at e
  obtain ⟨rfl, rfl, e⟩ := (BlockType.prefixFree F).cancel ht ht' e
  obtain ⟨rfl, rfl, e⟩ := (Vec.prefixFree Catch.prefixFree).cancel hc hc' e
  obtain ⟨rfl, rfl, -, -⟩ := seq_term ih (Instrs.iff_seq.mp hb)
    (by simp only [List.length_append, List.length_cons, List.length_nil] at hl; omega)
    (Instrs.iff_seq.mp hb') (.inl rfl) (.inl rfl) e
  exact ⟨rfl, rfl⟩

theorem Cast.unique {f : LabelIdx → Wasm.RefType → Wasm.RefType → Wasm.Instr}
    {rest rest' r r' : Bytes} {i i' : Wasm.Instr} (s : Cast f rest i) (s' : Cast f rest' i')
    (e : rest ++ r = rest' ++ r') : rest = rest' ∧ i = i' := by
  obtain ⟨bc, bl, b₁, b₂, n₁, n₂, l, h₁, h₂, rfl, hc, hl, hh₁, hh₂, rfl⟩ := s
  obtain ⟨bc', bl', b₁', b₂', n₁', n₂', l', h₁', h₂', rfl, hc', hl', hh₁', hh₂', rfl⟩ := s'
  simp only [List.append_assoc] at e
  obtain ⟨rfl, hn, e⟩ := CastOp.prefixFree.cancel hc hc' e
  simp only [Prod.mk.injEq] at hn
  obtain ⟨rfl, rfl⟩ := hn
  obtain ⟨rfl, rfl, e⟩ := Index.prefixFree.cancel hl hl' e
  obtain ⟨rfl, rfl, e⟩ := HeapType.prefixFree.cancel hh₁ hh₁' e
  obtain ⟨rfl, rfl⟩ := HeapType.prefixFree hh₂ hh₂' e
  exact ⟨rfl, rfl⟩

local macro "pf_tac" : tactic => `(tactic| first
  | exact Index.prefixFree | exact HeapType.prefixFree | exact IN.prefixFree _
  | exact FN.prefixFree _ | exact ReservedIdx.prefixFree _ | exact U32Fin.prefixFree
  | exact Vec.prefixFree Index.prefixFree | exact Vec.prefixFree (ValType.prefixFree _))

theorem FBSpec.unique {k : FBKind} {n : Nat} {rest rest' r r' : Bytes} {i i' : Wasm.Instr}
    (s : FBSpec k n rest i) (s' : FBSpec k n rest' i') (e : rest ++ r = rest' ++ r') :
    rest = rest' ∧ i = i' := by
  cases k
  case plain =>
    obtain ⟨rfl, hp⟩ := s
    obtain ⟨rfl, hp'⟩ := s'
    exact ⟨rfl, hp.det hp'⟩
  case brOnCast => exact Cast.unique s s' e
  case brOnCastFail => exact Cast.unique s s' e
  case invalid => exact (s : False).elim
  all_goals first
    | exact One.unique (by pf_tac) s s' e
    | exact Two.unique (by pf_tac) (by pf_tac) s s' e

theorem FCSpec.unique {F : Forms} {k : FCKind} {n : Nat} {rest rest' r r' : Bytes}
    {i i' : Wasm.Instr} (s : FCSpec F k n rest i) (s' : FCSpec F k n rest' i')
    (e : rest ++ r = rest' ++ r') : rest = rest' ∧ i = i' := by
  cases k
  case plain =>
    obtain ⟨rfl, hp⟩ := s
    obtain ⟨rfl, hp'⟩ := s'
    exact ⟨rfl, hp.det hp'⟩
  case invalid => exact (s : False).elim
  all_goals first
    | exact One.unique (by pf_tac) s s' e
    | exact Two.unique (by pf_tac) (by pf_tac) s s' e

theorem FDSpec.unique {F : Forms} {k : FDKind} {n : Nat} {rest rest' r r' : Bytes}
    {i i' : Wasm.Instr} (s : FDSpec F k n rest i) (s' : FDSpec F k n rest' i')
    (e : rest ++ r = rest' ++ r') : rest = rest' ∧ i = i' := by
  cases k
  case plain =>
    obtain ⟨rfl, hp⟩ := s
    obtain ⟨rfl, hp'⟩ := s'
    exact ⟨rfl, hp.det hp'⟩
  case mem =>
    obtain ⟨mk, x, ao, hm, ha, rfl⟩ := s
    obtain ⟨mk', x', ao', hm', ha', rfl⟩ := s'
    obtain rfl := hm.det hm'
    obtain ⟨rfl, hxa⟩ := Memarg.prefixFree F ha ha' e
    simp only [Prod.mk.injEq] at hxa
    obtain ⟨rfl, rfl⟩ := hxa
    exact ⟨rfl, rfl⟩
  case memLane =>
    obtain ⟨b, l, mk, x, ao, rfl, hm, ha, rfl⟩ := s
    obtain ⟨b', l', mk', x', ao', rfl, hm', ha', rfl⟩ := s'
    obtain rfl := hm.det hm'
    rw [List.append_assoc, List.append_assoc] at e
    obtain ⟨rfl, hxa, e⟩ := (Memarg.prefixFree F).cancel ha ha' e
    simp only [Prod.mk.injEq] at hxa
    obtain ⟨rfl, rfl⟩ := hxa
    simp only [List.singleton_append, List.cons.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact ⟨rfl, rfl⟩
  case lane =>
    obtain ⟨l, mk, rfl, hm, rfl⟩ := s
    obtain ⟨l', mk', rfl, hm', rfl⟩ := s'
    obtain rfl := hm.det hm'
    simp only [List.singleton_append, List.cons.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact ⟨rfl, rfl⟩
  case const =>
    obtain ⟨hl, rfl⟩ := s
    obtain ⟨hl', rfl⟩ := s'
    obtain ⟨rfl, -⟩ := List.append_inj e (hl.trans hl'.symm)
    exact ⟨rfl, rfl⟩
  case shuffle =>
    obtain ⟨hl, rfl⟩ := s
    obtain ⟨hl', rfl⟩ := s'
    obtain ⟨rfl, -⟩ := List.append_inj e (hl.trans hl'.symm)
    exact ⟨rfl, rfl⟩
  case invalid => exact (s : False).elim

theorem KSpec.unique {F : Forms} {M : Nat} (ih : PFBelow F M) {k : Kind} {c : UInt8}
    {rest rest' r r' : Bytes} {i i' : Wasm.Instr} (hl : rest.length ≤ M)
    (s : KSpec F k c rest i) (s' : KSpec F k c rest' i') (e : rest ++ r = rest' ++ r') :
    rest = rest' ∧ i = i' := by
  cases k
  case plain =>
    obtain ⟨rfl, hp⟩ := s
    obtain ⟨rfl, hp'⟩ := s'
    exact ⟨rfl, hp.det hp'⟩
  case mem =>
    obtain ⟨mk, x, ao, hm, ha, rfl⟩ := s
    obtain ⟨mk', x', ao', hm', ha', rfl⟩ := s'
    obtain rfl := hm.det hm'
    obtain ⟨rfl, hxa⟩ := Memarg.prefixFree F ha ha' e
    simp only [Prod.mk.injEq] at hxa
    obtain ⟨rfl, rfl⟩ := hxa
    exact ⟨rfl, rfl⟩
  case block => exact Blk.unique ih hl s s' e
  case loop => exact Blk.unique ih hl s s' e
  case if_ => exact IfS.unique ih hl s s' e
  case tryTable => exact TryT.unique ih hl s s' e
  case prefixFB =>
    obtain ⟨bn, n, q, rfl, hn, s⟩ := s
    obtain ⟨bn', n', q', rfl, hn', s'⟩ := s'
    rw [List.append_assoc, List.append_assoc] at e
    obtain ⟨rfl, rfl, e⟩ := (UN.prefixFree 32).cancel hn hn' e
    obtain ⟨rfl, rfl⟩ := FBSpec.unique s s' e
    exact ⟨rfl, rfl⟩
  case prefixFC =>
    obtain ⟨bn, n, q, rfl, hn, s⟩ := s
    obtain ⟨bn', n', q', rfl, hn', s'⟩ := s'
    rw [List.append_assoc, List.append_assoc] at e
    obtain ⟨rfl, rfl, e⟩ := (UN.prefixFree 32).cancel hn hn' e
    obtain ⟨rfl, rfl⟩ := FCSpec.unique s s' e
    exact ⟨rfl, rfl⟩
  case prefixFD =>
    obtain ⟨bn, n, q, rfl, hn, s⟩ := s
    obtain ⟨bn', n', q', rfl, hn', s'⟩ := s'
    rw [List.append_assoc, List.append_assoc] at e
    obtain ⟨rfl, rfl, e⟩ := (UN.prefixFree 32).cancel hn hn' e
    obtain ⟨rfl, rfl⟩ := FDSpec.unique s s' e
    exact ⟨rfl, rfl⟩
  case invalid => exact (s : False).elim
  all_goals first
    | exact One.unique (by pf_tac) s s' e
    | exact Two.unique (by pf_tac) (by pf_tac) s s' e

end Dispatch

/-- Prefix-freeness on encodings shorter than `N`, by induction on `N`. -/
theorem Instr.pfBelow (F : Forms) : ∀ N, PFBelow F N
  | 0 => by
    intro _ _ _ _ _ _ hl
    exact absurd hl (Nat.not_lt_zero _)
  | N + 1 => by
    intro b b' r r' i i' hl h h' e
    obtain ⟨c, rest, rfl, -⟩ := Instr.head h
    obtain ⟨c', rest', rfl, -⟩ := Instr.head h'
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, e⟩ := e
    obtain ⟨rfl, rfl⟩ := KSpec.unique (Instr.pfBelow F N)
      (by simp only [List.length_cons] at hl; omega) (Instr.inv h rfl) (Instr.inv h' rfl) e
    exact ⟨rfl, rfl⟩

/-! ### Unambiguity -/

/-- Instruction encodings are prefix-free, for every set of forms. -/
theorem Instr.prefixFree (F : Forms) : PrefixFree (Instr F) := by
  intro b _ _ _ _ _ h h' e
  exact Instr.pfBelow F _ (Nat.lt_succ_self b.length) h h' e

/-- Instruction sequences decode uniquely, for every set of forms. -/
theorem Instrs.functional (F : Forms) : Functional (Instrs F) := by
  intro _ _ _ h h'
  refine Seq.functional (Instr.prefixFree F) (fun _ hx => ?_)
    (Instrs.iff_seq.mp h) (Instrs.iff_seq.mp h')
  obtain ⟨_, _, he, -⟩ := Instr.head hx
  cases he

theorem Expr.prefixFree (F : Forms) : PrefixFree (Expr F) := by
  intro _ _ _ _ _ _ h h' e
  cases h with
  | mk hb =>
    cases h' with
    | mk hb' =>
      simp only [List.append_assoc, List.singleton_append] at e
      obtain ⟨rfl, rfl, -, -⟩ := seq_term (Instr.pfBelow F _) (Instrs.iff_seq.mp hb)
        (Nat.lt_succ_self _) (Instrs.iff_seq.mp hb') (.inl rfl) (.inl rfl) e
      exact ⟨rfl, rfl⟩

end Silmaril.Wasm.Binary.Core
