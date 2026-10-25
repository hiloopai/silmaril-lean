module

public import Silmaril.Wasm.V2.ToCore.Types

/-!
# Wasm 2.0 instructions as Core 3.0 syntax

The instruction half of the `2.0 ⊆ 3.0` subset theorem. `Instr.toCore` injects
the Wasm 2.0 instruction syntax of `Silmaril.Wasm.V2.Instructions`
(`1-syntax:400-526`) into the Core 3.0 source syntax of
`Silmaril.Wasm.Instructions`, `Instr.ofCore?` retracts it — rejecting every Core
3.0 instruction that is not Wasm 2.0 syntax — and `Instr.toCore_injective` falls
out of that retraction.

Line references `1-syntax:NN`, `6-typing:NN` and `8-reduction:NN` point into
`specification/wasm-2.0/*.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (hash-pinned in
`specs/wasm/core-2.0.json`), re-checked against the pinned files with `cat -n`;
they agree with the (already re-checked) citations of
`Silmaril/Wasm/V2/ToCore/Types.lean`.

## What the injection adds

Core 3.0 made several immediates explicit that Wasm 2.0 left implicit:

* every memory instruction gets the memory index `⟨0⟩`, because 2.0's
  `MEMORY.SIZE`, `MEMORY.GROW`, `MEMORY.FILL`, `MEMORY.COPY`,
  `MEMORY.INIT dataidx`, `LOAD`, `STORE`, `VLOAD`, `VLOAD_LANE`, `VSTORE` and
  `VSTORE_LANE` (`1-syntax:506-519`) all name memory `0` implicitly — the
  `Instr_ok/*` rules read `C.MEMS[0]` (`6-typing:460-532`);
* `VLOAD vectype vloadop? memarg` (`1-syntax:510`) has an *optional* load shape,
  whereas Core 3.0 spells the full 128-bit load `VecLoadOp.full`; that is
  `VecLoadOp.toCoreOpt`;
* `VSWIZZLE ishape` (`1-syntax:454`) is the only swizzle in 2.0, so it becomes
  `VSWIZZLOP` with `VecSwizzleOp.swizzle`;
* `REF.NULL reftype` (`1-syntax:476`) ranges over `FUNCREF | EXTERNREF`, while
  3.0 takes a `heaptype`; that is `RefType.toCoreHeap`.

`CALL_INDIRECT tableidx typeidx` (`1-syntax:427`) already carries its table
index in 2.0, so no index is inserted there and `ofCore?` accepts *every* table
index, not only `0`.

## Shape argument order

SpecTec 2.0 writes the **result** shape first and the **operand** shape second:
`VEXTUNOP ishape_1 ishape_2`, `VEXTBINOP ishape_1 ishape_2`,
`VNARROW ishape_1 ishape_2` (`1-syntax:462-469`) and `VCVTOP shape shape`
(`1-syntax:470`), and `Step_pure/vnarrow` (`8-reduction:344`) confirms it by
destructuring the first shape as the *narrowed* result. `Silmaril.Wasm.Ops` and
`Silmaril.Wasm.Instructions` put the **source** first:
`Instr.vecExtUnOp (source target)`, `Instr.vecExtBinOp (source target)`,
`Instr.vecNarrow (source target)`, `Instr.vecConvert (source target)`. The
injection therefore swaps those two arguments, and the already-proved
`V2.VecExtBinOp.valid_toCore` / `V2.VecCvtOp.valid_toCore` of
`Silmaril/Wasm/V2/ToCore/Types.lean` record the matching flip on the side
conditions.

## `Instr.toCore` is partial, and only because of `CVTOP`

`CVTOP numtype_1 numtype_2 cvtop` (`1-syntax:437`) carries an *unindexed*
`cvtop` and the only grammar side condition is `numtype_1 =/= numtype_2`.
`Instr_ok/cvtop-convert` (`6-typing:285`) adds no premise at all, so SpecTec 2.0
types nonsense such as `CVTOP F64 I32 WRAP`, for which `3-numerics` defines no
`$cvtop__` equation — the instruction is well-typed and stuck. Core 3.0 closed
this hole by indexing the operator family, `CVTOP numtype_1 numtype_2
cvtop__(numtype_2, numtype_1)`
(`specification/wasm-3.0/1.3-syntax.instructions.spectec`), which
is what `Silmaril.Wasm.ConvertOp` encodes. There is consequently **no total**
map `V2.Instr → Wasm.Instr`, and `V2.CvtOp.toCore` is already `Option`-valued in
`Silmaril/Wasm/V2/ToCore/Types.lean` for exactly this reason. We follow it:
`Instr.toCore : Instr → Option Wasm.Instr` and `Expr.toCore : Expr → Option
Wasm.Expr`, undefined precisely on the instructions whose `CVTOP` immediates
have no `$cvtop__` equation. Everything else is total, so the retraction and
injectivity statements are conditioned on `toCore` being defined, in the same
style as `V2.CvtOp.toCore_injective`.

This is not a deviation from SpecTec 2.0: both the 2.0 binary format
(`A-binary`) and the reference interpreter's typed `Ast.cvtop` can only express
the defined combinations, so no real module is affected.

## `Instr.coreImmediatesValid`

`V2.Instr.immediatesValid` (`Silmaril/Wasm/V2/Instructions.lean`) transcribes
the `-- if …` side conditions of the 2.0 *grammar*, while
`Wasm.Instr.immediatesValid` also checks, syntactically, conditions that 2.0
states as `Instr_ok` premises:

* `|t*| = 1` for `SELECT t*`, implicit in `Instr_ok/select-expl`
  (`6-typing:192`), which writes a single `t`;
* `laneidx < 2*$dim(sh)` for `VSHUFFLE`, `Instr_ok/vshuffle` (`6-typing:340`);
* `laneidx < $dim(sh)` for `VEXTRACT_LANE` and `VREPLACE_LANE`,
  `Instr_ok/vextract_lane` and `Instr_ok/vreplace_lane` (`6-typing:348`,
  `6-typing:352`);
* `laneidx < 128/n` for `VLOAD_LANE` and `VSTORE_LANE`, `Instr_ok/vload_lane`
  and `Instr_ok/vstore_lane` (`6-typing:517`, `6-typing:528`).

`Instr.coreImmediatesValid` collects exactly these, so that
`Instr.immediatesValid_toCore` can be stated and proved.
-/

@[expose] public section

namespace Silmaril.Wasm.V2

/-! ## Reference-null immediates -/

/-- The Core 3.0 heap type named by `REF.NULL reftype` (`1-syntax:476`); 2.0's
`reftype` is `FUNCREF | EXTERNREF` (`1-syntax:135`) and 3.0 takes a `heaptype`.
This is `RefType.toCore` forgetting the (always `true`) nullability flag. -/
def RefType.toCoreHeap : RefType → Wasm.HeapType
  | .funcref => .abstract .func
  | .externref => .abstract .extern

/-- `RefType.toCoreHeap` is the heap component of `RefType.toCore`. -/
@[simp] theorem RefType.toCore_heap (t : RefType) : t.toCore.heap = t.toCoreHeap := by
  cases t <;> rfl

/-- The retraction of `RefType.toCoreHeap` (`1-syntax:476`): every other Core
3.0 heap type is a GC, exception or concrete type that Wasm 2.0 has not. -/
def RefType.ofCoreHeap? : Wasm.HeapType → Option RefType
  | .abstract .func => some .funcref
  | .abstract .extern => some .externref
  | .abstract .any | .abstract .eq | .abstract .i31 | .abstract .struct
  | .abstract .array | .abstract .none | .abstract .nofunc | .abstract .exn
  | .abstract .noexn | .abstract .noextern => none
  | .typeIdx _ => none

@[simp] theorem RefType.ofCoreHeap?_toCoreHeap (t : RefType) :
    ofCoreHeap? t.toCoreHeap = some t := by cases t <;> rfl

theorem RefType.toCoreHeap_injective : Function.Injective RefType.toCoreHeap :=
  injective_of_ofCore? RefType.ofCoreHeap?_toCoreHeap

/-! ## The `CVTOP` immediate triple -/

/-- The 2.0 instruction denoted by a Core 3.0 `CONVERT` operator
(`1-syntax:437`). `CvtOp.ofCore` is total, so this needs no `Option`. -/
def CvtOp.toInstr (c : Wasm.ConvertOp) : Instr :=
  match CvtOp.ofCore c with
  | (target, source, op) => .cvtOp target source op

/-! ## The injection -/

mutual

/-- The Core 3.0 instruction denoted by a Wasm 2.0 instruction
(`1-syntax:406-522`). `none` only for a `CVTOP` whose immediates have no
`$cvtop__` equation; see the module documentation. -/
def Instr.toCore : Instr → Option Wasm.Instr
  -- Parametric instructions (`1-syntax:406`).
  | .nop => some .nop
  | .unreachable => some .unreachable
  | .drop => some .drop
  | .select types => some (.select (types.map ResultType.toCore))
  -- Block instructions (`1-syntax:413`).
  | .block t body => (Expr.toCore body).map (Wasm.Instr.block t.toCore)
  | .loop t body => (Expr.toCore body).map (Wasm.Instr.loop t.toCore)
  | .if_ t left right =>
      (Expr.toCore left).bind fun l =>
        (Expr.toCore right).map fun r => .if_ t.toCore l r
  -- Branch instructions (`1-syntax:419`).
  | .br l => some (.br l)
  | .brIf l => some (.brIf l)
  | .brTable ls l => some (.brTable ls l)
  -- Call instructions (`1-syntax:425`); the table index is already explicit.
  | .call f => some (.call f)
  | .callIndirect table type => some (.callIndirect table type)
  | .return_ => some .return_
  -- Numeric instructions (`1-syntax:431`).
  | .intConst t x => some (.intConst t x)
  | .floatConst t x => some (.floatConst t x)
  | .intUnOp t op => some (.intUnOp t op)
  | .floatUnOp t op => some (.floatUnOp t op)
  | .intBinOp t op => some (.intBinOp t op)
  | .floatBinOp t op => some (.floatBinOp t op)
  | .intTestOp t op => some (.intTestOp t op)
  | .intRelOp t op => some (.intRelOp t op)
  | .floatRelOp t op => some (.floatRelOp t op)
  | .cvtOp target source op => (CvtOp.toCore target source op).map Wasm.Instr.convert
  -- Vector instructions (`1-syntax:442`).
  | .vecConst c => some (.vecConst c)
  | .vvUnOp op => some (.vecUnOp op)
  | .vvBinOp op => some (.vecBinOp op)
  | .vvTernOp op => some (.vecTernOp op)
  | .vvTestOp op => some (.vecTestOp op)
  | .vecIntUnOp s op => some (.vecIntUnOp s op)
  | .vecFloatUnOp s op => some (.vecFloatUnOp s op)
  | .vecIntBinOp s op => some (.vecIntBinOp s op.toCore)
  | .vecFloatBinOp s op => some (.vecFloatBinOp s op.toCore)
  | .vecAllTrue s => some (.vecAllTrue s)
  | .vecIntRelOp s op => some (.vecIntRelOp s op)
  | .vecFloatRelOp s op => some (.vecFloatRelOp s op)
  | .vecShiftOp s op => some (.vecShiftOp s op)
  | .vecBitmask s => some (.vecBitmask s)
  | .vecSwizzle => some (.vecSwizzle .swizzle)
  | .vecShuffle lanes => some (.vecShuffle lanes)
  | .vecSplat s => some (.vecSplat s)
  | .vecExtractLane s sign lane => some (.vecExtractLane s sign lane)
  | .vecReplaceLane s lane => some (.vecReplaceLane s lane)
  -- `ishape_1` is the result and `ishape_2` the operand (`1-syntax:462-470`);
  -- Core 3.0 takes the operand first.
  | .vecExtUnOp target source op => some (.vecExtUnOp source target op)
  | .vecExtBinOp target source op => some (.vecExtBinOp source target op.toCore)
  | .vecNarrow target source sign => some (.vecNarrow source target sign)
  | .vecCvtOp target source op => some (.vecConvert source target op.toCore)
  -- Reference instructions (`1-syntax:475`).
  | .refNull t => some (.refNull t.toCoreHeap)
  | .refFunc f => some (.refFunc f)
  | .refIsNull => some .refIsNull
  -- Local instructions (`1-syntax:481`).
  | .localGet x => some (.localGet x)
  | .localSet x => some (.localSet x)
  | .localTee x => some (.localTee x)
  -- Global instructions (`1-syntax:487`).
  | .globalGet x => some (.globalGet x)
  | .globalSet x => some (.globalSet x)
  -- Table instructions (`1-syntax:492`).
  | .tableGet x => some (.tableGet x)
  | .tableSet x => some (.tableSet x)
  | .tableSize x => some (.tableSize x)
  | .tableGrow x => some (.tableGrow x)
  | .tableFill x => some (.tableFill x)
  | .tableCopy d s => some (.tableCopy d s)
  | .tableInit x y => some (.tableInit x y)
  -- Element instructions (`1-syntax:502`).
  | .elemDrop x => some (.elemDrop x)
  -- Memory instructions (`1-syntax:506`); memory `0` becomes explicit.
  | .intLoad t packed a => some (.intLoad t packed ⟨0⟩ a.toCore)
  | .floatLoad t a => some (.floatLoad t ⟨0⟩ a.toCore)
  | .intStore t packed a => some (.intStore t packed ⟨0⟩ a.toCore)
  | .floatStore t a => some (.floatStore t ⟨0⟩ a.toCore)
  | .vecLoad op a => some (.vecLoad (VecLoadOp.toCoreOpt op) ⟨0⟩ a.toCore)
  | .vecLoadLane size a lane => some (.vecLoadLane size ⟨0⟩ a.toCore lane)
  | .vecStore a => some (.vecStore ⟨0⟩ a.toCore)
  | .vecStoreLane size a lane => some (.vecStoreLane size ⟨0⟩ a.toCore lane)
  | .memorySize => some (.memorySize ⟨0⟩)
  | .memoryGrow => some (.memoryGrow ⟨0⟩)
  | .memoryFill => some (.memoryFill ⟨0⟩)
  | .memoryCopy => some (.memoryCopy ⟨0⟩ ⟨0⟩)
  | .memoryInit x => some (.memoryInit ⟨0⟩ x)
  -- Data instructions (`1-syntax:521`).
  | .dataDrop x => some (.dataDrop x)

/-- `expr ::= instr*` (`1-syntax:525`), injected pointwise. -/
def Expr.toCore : Expr → Option Wasm.Expr
  | [] => some []
  | i :: is => (Instr.toCore i).bind fun c => (Expr.toCore is).map fun cs => c :: cs

end

/-- `Expr.toCore` is the pointwise `Option` lift of `Instr.toCore`
(`1-syntax:525`). -/
theorem Expr.toCore_eq_mapM (es : Expr) : Expr.toCore es = es.mapM Instr.toCore := by
  induction es with
  | nil => rfl
  | cons i es ih =>
      simp only [Expr.toCore, ih, List.mapM_cons]
      cases Instr.toCore i <;> cases List.mapM Instr.toCore es <;> rfl

/-! ## The retraction -/

mutual

/-- Recognise exactly the Wasm 2.0 instruction image inside the Core 3.0 syntax
(`1-syntax:406-522`). Everything 3.0 added — GC, exceptions, tail calls,
`br_on_*`, `call_ref`, relaxed SIMD, a memory index other than `0` and a 64-bit
`memarg` offset — is rejected. -/
def Instr.ofCore? : Wasm.Instr → Option Instr
  -- Parametric instructions (`1-syntax:406`).
  | .nop => some .nop
  | .unreachable => some .unreachable
  | .drop => some .drop
  | .select none => some (.select none)
  | .select (some ts) => (ResultType.ofCore? ts).map fun ts => .select (some ts)
  -- Block instructions (`1-syntax:413`).
  | .block t body =>
      (BlockType.ofCore? t).bind fun t => (Expr.ofCore? body).map fun body => .block t body
  | .loop t body =>
      (BlockType.ofCore? t).bind fun t => (Expr.ofCore? body).map fun body => .loop t body
  | .if_ t left right =>
      (BlockType.ofCore? t).bind fun t =>
        (Expr.ofCore? left).bind fun l =>
          (Expr.ofCore? right).map fun r => .if_ t l r
  -- Branch instructions (`1-syntax:419`).
  | .br l => some (.br l)
  | .brIf l => some (.brIf l)
  | .brTable ls l => some (.brTable ls l)
  -- Call instructions (`1-syntax:425`).
  | .call f => some (.call f)
  | .callIndirect table type => some (.callIndirect table type)
  | .return_ => some .return_
  -- Numeric instructions (`1-syntax:431`).
  | .intConst t x => some (.intConst t x)
  | .floatConst t x => some (.floatConst t x)
  | .intUnOp t op => some (.intUnOp t op)
  | .floatUnOp t op => some (.floatUnOp t op)
  | .intBinOp t op => some (.intBinOp t op)
  | .floatBinOp t op => some (.floatBinOp t op)
  | .intTestOp t op => some (.intTestOp t op)
  | .intRelOp t op => some (.intRelOp t op)
  | .floatRelOp t op => some (.floatRelOp t op)
  | .convert op => some (CvtOp.toInstr op)
  -- Vector instructions (`1-syntax:442`).
  | .vecConst c => some (.vecConst c)
  | .vecUnOp op => some (.vvUnOp op)
  | .vecBinOp op => some (.vvBinOp op)
  | .vecTernOp op => some (.vvTernOp op)
  | .vecTestOp op => some (.vvTestOp op)
  | .vecIntUnOp s op => some (.vecIntUnOp s op)
  | .vecFloatUnOp s op => some (.vecFloatUnOp s op)
  | .vecIntBinOp s op => (VecIntBinOp.ofCore? op).map (.vecIntBinOp s)
  | .vecFloatBinOp s op => (VecFloatBinOp.ofCore? op).map (.vecFloatBinOp s)
  | .vecAllTrue s => some (.vecAllTrue s)
  | .vecIntRelOp s op => some (.vecIntRelOp s op)
  | .vecFloatRelOp s op => some (.vecFloatRelOp s op)
  | .vecShiftOp s op => some (.vecShiftOp s op)
  | .vecBitmask s => some (.vecBitmask s)
  | .vecSwizzle .swizzle => some .vecSwizzle
  | .vecShuffle lanes => some (.vecShuffle lanes)
  | .vecSplat s => some (.vecSplat s)
  | .vecExtractLane s sign lane => some (.vecExtractLane s sign lane)
  | .vecReplaceLane s lane => some (.vecReplaceLane s lane)
  | .vecExtUnOp source target op => some (.vecExtUnOp target source op)
  | .vecExtBinOp source target op =>
      (VecExtBinOp.ofCore? op).map (.vecExtBinOp target source)
  | .vecNarrow source target sign => some (.vecNarrow target source sign)
  | .vecConvert source target op => (VecCvtOp.ofCore? op).map (.vecCvtOp target source)
  -- Reference instructions (`1-syntax:475`).
  | .refNull h => (RefType.ofCoreHeap? h).map .refNull
  | .refFunc f => some (.refFunc f)
  | .refIsNull => some .refIsNull
  -- Local instructions (`1-syntax:481`).
  | .localGet x => some (.localGet x)
  | .localSet x => some (.localSet x)
  | .localTee x => some (.localTee x)
  -- Global instructions (`1-syntax:487`).
  | .globalGet x => some (.globalGet x)
  | .globalSet x => some (.globalSet x)
  -- Table instructions (`1-syntax:492`).
  | .tableGet x => some (.tableGet x)
  | .tableSet x => some (.tableSet x)
  | .tableSize x => some (.tableSize x)
  | .tableGrow x => some (.tableGrow x)
  | .tableFill x => some (.tableFill x)
  | .tableCopy d s => some (.tableCopy d s)
  | .tableInit x y => some (.tableInit x y)
  -- Element instructions (`1-syntax:502`).
  | .elemDrop x => some (.elemDrop x)
  -- Memory instructions (`1-syntax:506`): only memory `0`, only `u32` offsets.
  | .intLoad t packed memory a =>
      if memory = ⟨0⟩ then (MemArg.ofCore? a).map (.intLoad t packed) else none
  | .floatLoad t memory a =>
      if memory = ⟨0⟩ then (MemArg.ofCore? a).map (.floatLoad t) else none
  | .intStore t packed memory a =>
      if memory = ⟨0⟩ then (MemArg.ofCore? a).map (.intStore t packed) else none
  | .floatStore t memory a =>
      if memory = ⟨0⟩ then (MemArg.ofCore? a).map (.floatStore t) else none
  | .vecLoad op memory a =>
      if memory = ⟨0⟩ then (MemArg.ofCore? a).map (.vecLoad (VecLoadOp.ofCoreOpt op))
      else none
  | .vecLoadLane size memory a lane =>
      if memory = ⟨0⟩ then (MemArg.ofCore? a).map fun a => .vecLoadLane size a lane
      else none
  | .vecStore memory a => if memory = ⟨0⟩ then (MemArg.ofCore? a).map .vecStore else none
  | .vecStoreLane size memory a lane =>
      if memory = ⟨0⟩ then (MemArg.ofCore? a).map fun a => .vecStoreLane size a lane
      else none
  | .memorySize memory => if memory = ⟨0⟩ then some .memorySize else none
  | .memoryGrow memory => if memory = ⟨0⟩ then some .memoryGrow else none
  | .memoryFill memory => if memory = ⟨0⟩ then some .memoryFill else none
  | .memoryCopy d s => if d = ⟨0⟩ ∧ s = ⟨0⟩ then some .memoryCopy else none
  | .memoryInit memory x => if memory = ⟨0⟩ then some (.memoryInit x) else none
  -- Data instructions (`1-syntax:521`).
  | .dataDrop x => some (.dataDrop x)
  -- Everything Core 3.0 added after Wasm 2.0.
  -- Typed function references and tail calls.
  | .brOnNull _ | .brOnNonNull _ | .callRef _ | .returnCall _ | .returnCallRef _
  | .returnCallIndirect _ _ | .refAsNonNull => none
  -- Exception handling.
  | .throw _ | .throwRef | .tryTable _ _ _ => none
  -- Garbage collection.
  | .brOnCast _ _ _ | .brOnCastFail _ _ _ | .refEq | .refTest _ | .refCast _
  | .refI31 | .i31Get _ | .structNew _ | .structNewDefault _ | .structGet _ _ _
  | .structSet _ _ | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _
  | .arrayNewData _ _ | .arrayNewElem _ _ | .arrayGet _ _ | .arraySet _
  | .arrayLen | .arrayFill _ | .arrayCopy _ _ | .arrayInitData _ _
  | .arrayInitElem _ _ | .externConvertAny | .anyConvertExtern => none
  -- Relaxed SIMD.
  | .vecIntTernOp _ _ | .vecFloatTernOp _ _ | .vecExtTernOp _ _ _
  | .vecSwizzle .relaxedSwizzle => none

/-- `expr ::= instr*` (`1-syntax:525`). -/
def Expr.ofCore? : Wasm.Expr → Option Expr
  | [] => some []
  | i :: is => (Instr.ofCore? i).bind fun j => (Expr.ofCore? is).map fun js => j :: js

end

/-- `Expr.ofCore?` is the pointwise `Option` lift of `Instr.ofCore?`
(`1-syntax:525`). -/
theorem Expr.ofCore?_eq_mapM (cs : Wasm.Expr) : Expr.ofCore? cs = cs.mapM Instr.ofCore? := by
  induction cs with
  | nil => rfl
  | cons i is ih =>
      simp only [Expr.ofCore?, ih, List.mapM_cons]
      cases Instr.ofCore? i <;> cases List.mapM Instr.ofCore? is <;> rfl

mutual

/-- `Instr.ofCore?` inverts `Instr.toCore` wherever the latter is defined
(`1-syntax:406-522`). -/
theorem Instr.ofCore?_toCore : ∀ {i : Instr} {c : Wasm.Instr},
    Instr.toCore i = some c → Instr.ofCore? c = some i := by
  intro i c h
  match i with
  | .block t body =>
      simp only [Instr.toCore, Option.map_eq_some_iff] at h
      obtain ⟨cs, hcs, rfl⟩ := h
      simp [Instr.ofCore?, Expr.ofCore?_toCore hcs]
  | .loop t body =>
      simp only [Instr.toCore, Option.map_eq_some_iff] at h
      obtain ⟨cs, hcs, rfl⟩ := h
      simp [Instr.ofCore?, Expr.ofCore?_toCore hcs]
  | .if_ t left right =>
      simp only [Instr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨ls, hls, rs, hrs, rfl⟩ := h
      simp [Instr.ofCore?, Expr.ofCore?_toCore hls, Expr.ofCore?_toCore hrs]
  | .cvtOp target source op =>
      simp only [Instr.toCore, Option.map_eq_some_iff] at h
      obtain ⟨c', hc', rfl⟩ := h
      simp [Instr.ofCore?, CvtOp.toInstr, CvtOp.ofCore_toCore _ _ _ _ hc']
  | .select types =>
      cases types <;> simp only [Instr.toCore, Option.some.injEq] at h <;> subst h <;>
        simp [Instr.ofCore?]
  | .nop | .unreachable | .drop
  | .br _ | .brIf _ | .brTable _ _
  | .call _ | .callIndirect _ _ | .return_
  | .intConst _ _ | .floatConst _ _ | .intUnOp _ _ | .floatUnOp _ _
  | .intBinOp _ _ | .floatBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ | .floatRelOp _ _
  | .vecConst _ | .vvUnOp _ | .vvBinOp _ | .vvTernOp _ | .vvTestOp _
  | .vecIntUnOp _ _ | .vecFloatUnOp _ _ | .vecIntBinOp _ _ | .vecFloatBinOp _ _
  | .vecAllTrue _ | .vecIntRelOp _ _ | .vecFloatRelOp _ _ | .vecShiftOp _ _
  | .vecBitmask _ | .vecSwizzle | .vecShuffle _ | .vecSplat _
  | .vecExtractLane _ _ _ | .vecReplaceLane _ _
  | .vecExtUnOp _ _ _ | .vecExtBinOp _ _ _ | .vecNarrow _ _ _ | .vecCvtOp _ _ _
  | .refNull _ | .refFunc _ | .refIsNull
  | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _
  | .tableGet _ | .tableSet _ | .tableSize _ | .tableGrow _ | .tableFill _
  | .tableCopy _ _ | .tableInit _ _ | .elemDrop _
  | .intLoad _ _ _ | .floatLoad _ _ | .intStore _ _ _ | .floatStore _ _
  | .vecLoad _ _ | .vecLoadLane _ _ _ | .vecStore _ | .vecStoreLane _ _ _
  | .memorySize | .memoryGrow | .memoryFill | .memoryCopy | .memoryInit _
  | .dataDrop _ =>
      simp only [Instr.toCore, Option.some.injEq] at h
      subst h
      simp [Instr.ofCore?]
termination_by i => sizeOf i

/-- `Expr.ofCore?` inverts `Expr.toCore` wherever the latter is defined
(`1-syntax:525`). -/
theorem Expr.ofCore?_toCore : ∀ {es : Expr} {cs : Wasm.Expr},
    Expr.toCore es = some cs → Expr.ofCore? cs = some es := by
  intro es cs h
  match es with
  | [] => simp only [Expr.toCore, Option.some.injEq] at h; subst h; rfl
  | i :: is =>
      simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨c, hc, cs', hcs', rfl⟩ := h
      simp [Expr.ofCore?, Instr.ofCore?_toCore hc, Expr.ofCore?_toCore hcs']
termination_by es => sizeOf es

end

/-- Wasm 2.0 instructions are determined by their Core 3.0 image
(`1-syntax:406-522`). Stated for the two instructions whose injections are
defined and equal, which is the usable form for a partial map. -/
theorem Instr.toCore_injective {i j : Instr} {c : Wasm.Instr}
    (hi : Instr.toCore i = some c) (hj : Instr.toCore j = some c) : i = j :=
  Option.some.inj (((Instr.ofCore?_toCore hi).symm).trans (Instr.ofCore?_toCore hj))

/-- Wasm 2.0 expressions are determined by their Core 3.0 image
(`1-syntax:525`). -/
theorem Expr.toCore_injective {es fs : Expr} {cs : Wasm.Expr}
    (hes : Expr.toCore es = some cs) (hfs : Expr.toCore fs = some cs) : es = fs :=
  Option.some.inj (((Expr.ofCore?_toCore hes).symm).trans (Expr.ofCore?_toCore hfs))

/-! ## Immediate side conditions -/

/-- The immediate conditions that `Wasm.Instr.immediatesValid` checks
syntactically but `V2.Instr.immediatesValid` does not, because SpecTec 2.0
states them as `Instr_ok` premises (`6-typing:192`, `6-typing:340`,
`6-typing:348`, `6-typing:352`, `6-typing:517`, `6-typing:528`) rather than as
grammar side conditions. -/
def Instr.coreImmediatesValid : Instr → Bool
  | .select (some ts) => ts.length == 1
  | .block _ body | .loop _ body => body.attach.all fun i => coreImmediatesValid i.val
  | .if_ _ left right =>
      (left.attach.all fun i => coreImmediatesValid i.val) &&
        (right.attach.all fun i => coreImmediatesValid i.val)
  | .vecShuffle lanes => lanes.all fun l => l.val < 32
  | .vecExtractLane s _ lane => lane.val < s.lanes
  | .vecReplaceLane s lane => lane.val < s.lanes
  | .vecLoadLane size _ lane | .vecStoreLane size _ lane => lane.val < 128 / size.width
  | _ => true
  termination_by instruction => sizeOf instruction
  decreasing_by
    all_goals exact Nat.lt_trans (List.sizeOf_lt_of_mem i.property) (by simp; omega)

mutual

/-- The Wasm 2.0 grammar side conditions, together with the `Instr_ok` premises
collected in `Instr.coreImmediatesValid`, imply the Core 3.0 immediate
conditions on the image. This is where the shape argument order of
`VEXTUNOP`/`VEXTBINOP`/`VNARROW`/`VCVTOP` (`1-syntax:462-470`) is pinned down:
with the arguments swapped the statement is false. -/
theorem Instr.immediatesValid_toCore : ∀ {i : Instr} {c : Wasm.Instr},
    i.immediatesValid = true → i.coreImmediatesValid = true →
    Instr.toCore i = some c → c.immediatesValid = true := by
  intro i c h h' hc
  match i with
  | .block t body =>
      simp only [Instr.toCore, Option.map_eq_some_iff] at hc
      obtain ⟨cs, hcs, rfl⟩ := hc
      simp only [Instr.immediatesValid, Instr.coreImmediatesValid, Wasm.Instr.immediatesValid,
        List.all_eq_true, List.mem_attach, forall_const, Subtype.forall] at h h' ⊢
      exact Expr.immediatesValid_toCore h h' hcs
  | .loop t body =>
      simp only [Instr.toCore, Option.map_eq_some_iff] at hc
      obtain ⟨cs, hcs, rfl⟩ := hc
      simp only [Instr.immediatesValid, Instr.coreImmediatesValid, Wasm.Instr.immediatesValid,
        List.all_eq_true, List.mem_attach, forall_const, Subtype.forall] at h h' ⊢
      exact Expr.immediatesValid_toCore h h' hcs
  | .if_ t left right =>
      simp only [Instr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
      obtain ⟨ls, hls, rs, hrs, rfl⟩ := hc
      simp only [Instr.immediatesValid, Instr.coreImmediatesValid, Wasm.Instr.immediatesValid,
        Bool.and_eq_true, List.all_eq_true, List.mem_attach, forall_const, Subtype.forall]
        at h h' ⊢
      exact ⟨Expr.immediatesValid_toCore h.1 h'.1 hls, Expr.immediatesValid_toCore h.2 h'.2 hrs⟩
  | .cvtOp target source op =>
      simp only [Instr.toCore, Option.map_eq_some_iff] at hc
      obtain ⟨c', _, rfl⟩ := hc
      simp [Wasm.Instr.immediatesValid]
  | .select types =>
      cases types <;> simp only [Instr.toCore, Option.some.injEq] at hc <;> subst hc <;>
        simp_all [Instr.coreImmediatesValid, Wasm.Instr.immediatesValid, ResultType.toCore]
  | .intLoad t packed a =>
      simp only [Instr.toCore, Option.some.injEq] at hc
      subst hc
      match packed with
      | none => simp [Wasm.Instr.immediatesValid]
      | some (size, sign) =>
          simp_all [Instr.immediatesValid, Wasm.Instr.immediatesValid]
  | .intStore t packed a =>
      simp only [Instr.toCore, Option.some.injEq] at hc
      subst hc
      match packed with
      | none => simp [Wasm.Instr.immediatesValid]
      | some size =>
          simp_all [Instr.immediatesValid, Wasm.Instr.immediatesValid]
  | .nop | .unreachable | .drop
  | .br _ | .brIf _ | .brTable _ _
  | .call _ | .callIndirect _ _ | .return_
  | .intConst _ _ | .floatConst _ _ | .intUnOp _ _ | .floatUnOp _ _
  | .intBinOp _ _ | .floatBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ | .floatRelOp _ _
  | .vecConst _ | .vvUnOp _ | .vvBinOp _ | .vvTernOp _ | .vvTestOp _
  | .vecIntUnOp _ _ | .vecFloatUnOp _ _ | .vecIntBinOp _ _ | .vecFloatBinOp _ _
  | .vecAllTrue _ | .vecIntRelOp _ _ | .vecFloatRelOp _ _ | .vecShiftOp _ _
  | .vecBitmask _ | .vecSwizzle | .vecShuffle _ | .vecSplat _
  | .vecExtractLane _ _ _ | .vecReplaceLane _ _
  | .vecExtUnOp _ _ _ | .vecExtBinOp _ _ _ | .vecNarrow _ _ _ | .vecCvtOp _ _ _
  | .refNull _ | .refFunc _ | .refIsNull
  | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _
  | .tableGet _ | .tableSet _ | .tableSize _ | .tableGrow _ | .tableFill _
  | .tableCopy _ _ | .tableInit _ _ | .elemDrop _
  | .floatLoad _ _ | .floatStore _ _
  | .vecLoad _ _ | .vecLoadLane _ _ _ | .vecStore _ | .vecStoreLane _ _ _
  | .memorySize | .memoryGrow | .memoryFill | .memoryCopy | .memoryInit _
  | .dataDrop _ =>
      simp only [Instr.toCore, Option.some.injEq] at hc
      subst hc
      simp_all [Instr.immediatesValid, Instr.coreImmediatesValid, Wasm.Instr.immediatesValid,
        VecExtUnOp.valid, VecExtUnOp.valid2]
      all_goals omega
termination_by i => sizeOf i

/-- The expression-level form of `Instr.immediatesValid_toCore` (`1-syntax:525`). -/
theorem Expr.immediatesValid_toCore : ∀ {es : Expr} {cs : Wasm.Expr},
    (∀ i ∈ es, Instr.immediatesValid i = true) →
    (∀ i ∈ es, Instr.coreImmediatesValid i = true) →
    Expr.toCore es = some cs → ∀ c ∈ cs, Wasm.Instr.immediatesValid c = true := by
  intro es cs h h' hc
  match es with
  | [] =>
      simp only [Expr.toCore, Option.some.injEq] at hc
      subst hc
      simp
  | i :: is =>
      simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
      obtain ⟨c, hc1, cs', hcs, rfl⟩ := hc
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Instr.immediatesValid_toCore (h i (by simp)) (h' i (by simp)) hc1
      · exact Expr.immediatesValid_toCore (fun j hj => h j (by simp [hj]))
          (fun j hj => h' j (by simp [hj])) hcs d hd
termination_by es => sizeOf es

end

end Silmaril.Wasm.V2
