module

public import Silmaril.Wasm.Tools.Gen.API.Defs
public import Silmaril.Wasm.Models.Syntax.Defs
public import Silmaril.Wasm.Perf.ValidateR.Defs
public import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# Core Wasm generators, mutators and shrinkers at a point of the feature lattice

The instance of the generic API (`Silmaril.Wasm.Tools.Gen.API`) for Core 3.0 syntax
(`Silmaril.Wasm.Module`) restricted to a feature set `S` (`Silmaril.Wasm.Models.FeatureSet`),
which is the module language of `coreModel P H S` and of `fxModel P H` (`Thms`).

* `featCheck S m := (validateR m).isSome && m.inFeatB S`: the checker of `ValidIn S`, where
  `validateR` is the fast validator proved equal to silmaril's sound and complete `validate?`
  (`Thms`: `featCheck_iff`, from `Silmaril.Wasm.Perf.ValidateR.validateR_eq`);
* `Raw`: an unverified, type-directed generator of instruction sequences (`Raw.gen`: a value
  of a given type, or a statement) and modules (`Raw.module S size`) using only features of `S`;
  `Raw.ctxOf` rebuilds its context from a module so mutators can generate inside it;
* raw mutations `Raw.mutate` (regenerate a body, insert a statement, delete an instruction,
  change a constant, add a global or a function, drop or rotate exports) and shrink candidates
  `Raw.cands` with the structural size `Raw.size`;
* `featGenRun S`, `featMutRun S`: what the checked generator and mutator compute (the raw
  output when `featCheck S` accepts it, else the empty module or the input); `featShrinker`,
  `featShrink S p` (checked shrinking).

This module holds only what runs: it imports no theorem header. `Thms` builds the verified
objects of the API over it: the language `featLang S`, `featGen S` and `featMut S` (with
`featGen_run_eq : (featGen S).run = featGenRun S` and `featMut_run_eq`, both by `rfl`).

The raw generator covers, each gated by its capability: integer, float and SIMD numerics
(relaxed SIMD: `relaxed_madd`, `relaxed_laneselect`, `relaxed_swizzle`, `relaxed_max`,
`relaxed_q15mulr_s`, `relaxed_trunc`), conversions, locals, globals (extended constants),
loads/stores/size/grow/fill/copy over **several memories** (multi-memory) of address type
`i32` or **`i64`** (memory64), blocks/loops/ifs, `br_if`, `select`, direct, indirect and tail
calls, **typed function references** (`ref.func` of declared functions, `call_ref`,
`return_call_ref`, `ref.as_non_null`, `br_on_null`, `ref.null` of concrete types),
**exceptions** (tags carrying nothing or one value, `throw`, `throw_ref`, `try_table` with
`catch`, `catch_all`, `catch_all_ref`), and **GC** (struct and array types with packed and
mutable fields, `struct.new`/`new_default`/`get`/`set`, `array.new`/`new_default`/
`new_fixed`/`get`/`set`/`len`/`fill`, `ref.i31`, `i31.get`, `ref.eq`, `ref.test`, `ref.cast`,
`any.convert_extern`, `extern.convert_any`). Stack switching has no Core 3.0 syntax in
silmaril (the WasmFX model's instructions are FX code without module syntax or validation), so
`wasmFX` generates exactly what `v30` does.

Raw generation aims at validity (operand types, labels, index spaces and feature use are
tracked); the checker is the proof. How often the fallback fires is measured by
`tools/wasm-tools-gen-check` (`docs/projects/wasm-components.md`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Core

open Silmaril.Wasm Silmaril.Wasm.Models

/-! ## The language of a feature set -/

/-- The checker of `ValidIn S`: the fast validator and the feature check. -/
def featCheck (S : FeatureSet) (m : Module) : Bool :=
  (Silmaril.Wasm.Perf.ValidateR.validateR m).isSome && Module.inFeatB S m

/-! ## Raw generation -/

namespace Raw

/-- An index. -/
def idx {k : IndexKind} (n : Nat) : Idx k := ⟨Fin.ofNat _ n⟩

/-- The generation context of a function body. -/
structure Ctx where
  /-- The feature set. -/
  S : FeatureSet
  /-- Function types, by type index. -/
  types : Array FuncType
  /-- The type index of every function (imports first). -/
  funcs : Array Nat
  /-- Globals (imports first). -/
  globals : Array GlobalType
  /-- Is there a memory 0? -/
  mem : Bool
  /-- Locals (parameters first). -/
  locals : Array ValType
  /-- Labels, innermost first: `some []` for a block or `if` without results, `none` otherwise
  (loops and labels with results are never branched to). -/
  labels : List (Option (List ValType))
  /-- Is there a `funcref` table 0? -/
  table : Bool := false
  /-- The address type of every memory (imports first): several with multi-memory, `i64`
  with memory64. `mem` is `!mems.isEmpty`. -/
  mems : Array AddrType := #[]
  /-- The parameters of every exception tag (`[]` or one value type). -/
  tags : Array (List ValType) := #[]
  /-- GC struct types: type index and fields. -/
  structs : Array (Nat × List FieldType) := #[]
  /-- GC array types: type index and element field. -/
  arrays : Array (Nat × FieldType) := #[]
  /-- Functions that `ref.func` may name (declared by an element segment or an export). -/
  refFuncs : List Nat := []

/-- What to generate. -/
inductive Goal where
  /-- Instructions pushing one value of the type. -/
  | val (t : ValType)
  /-- Instructions with no net stack effect. -/
  | stmt

/-- The value types of `S` used in signatures. -/
def valTypes (S : FeatureSet) : List ValType :=
  (if S.has .intNum then [.i32, .i64] else []) ++ (if S.has .floatNum then [.f32, .f64] else []) ++
    (if S.has .simd then [.v128] else [])

/-- A 64-bit random number. -/
def bits : Rand Nat := fun r => let (x, r') := r.next; (x.toNat, r')

/-- An interesting integer of a width. -/
def intBits (w : Nat) : Rand Nat := do
  match ← Rand.nat 6 with
  | 0 => pure 0
  | 1 => pure 1
  | 2 => pure (2 ^ w - 1)
  | 3 => pure (2 ^ (w - 1))
  | 4 => Rand.nat 256
  | _ => return (← bits) % 2 ^ w

/-- A constant of a value type (`ref.null` for references). -/
def const (t : ValType) : Rand (List Instr) := do
  match t with
  | .num (.int it) => return [.intConst it (BitVec.ofNat _ (← intBits it.width))]
  | .num (.float ft) => return [.floatConst ft (BitVec.ofNat _ (← intBits ft.width))]
  | .vec _ => return [.vecConst (BitVec.ofNat 128 ((← bits) * 2 ^ 64 + (← bits)))]
  | .ref rt => return [.refNull rt.heap]

/-- A constant or a local of the type. -/
def leaf (c : Ctx) (t : ValType) : Rand (List Instr) := do
  let ls := (List.range c.locals.size).filter fun i => (c.locals.getD i .i32) == t
  if !ls.isEmpty && (← Rand.bool) then
    return [.localGet (idx (← Rand.pick ls 0))]
  const t

def intBinOps : List IntBinOp :=
  [.add, .sub, .mul, .div .signed, .div .unsigned, .rem .signed, .rem .unsigned, .and, .or, .xor,
    .shl, .shr .signed, .shr .unsigned, .rotl, .rotr]

def intRelOps : List IntRelOp :=
  [.eq, .ne, .lt .signed, .lt .unsigned, .gt .signed, .gt .unsigned, .le .signed, .le .unsigned,
    .ge .signed, .ge .unsigned]

def intUnOps (S : FeatureSet) (it : IntType) : List IntUnOp :=
  [.clz, .ctz, .popcnt] ++
    (if S.has .signExt then
      ([.extend .i8, .extend .i16] ++ if it == .i64 then [.extend .i32] else []) else [])

def floatBinOps : List FloatBinOp := [.add, .sub, .mul, .div, .min, .max, .copysign]
def floatUnOps : List FloatUnOp := [.abs, .neg, .sqrt, .ceil, .floor, .trunc, .nearest]
def floatRelOps : List FloatRelOp := [.eq, .ne, .lt, .gt, .le, .ge]

/-- Conversions of `S` with the given target. -/
def convsTo (S : FeatureSet) (t : NumType) : List ConvertOp :=
  let fl := S.has .floatNum
  let all : List ConvertOp :=
    [.wrap, .extend .signed, .extend .unsigned] ++
    (if fl then
      [.trunc .f32 .i32 .signed, .trunc .f64 .i64 .unsigned, .convert .i32 .f32 .signed,
        .convert .i64 .f64 .unsigned, .convert .i32 .f64 .signed, .demote, .promote,
        .reinterpretInt .f32, .reinterpretInt .f64, .reinterpretFloat .i32,
        .reinterpretFloat .i64] else []) ++
    (if S.has .satConv then [.truncSat .f32 .i32 .signed, .truncSat .f64 .i64 .unsigned] else [])
  all.filter fun op => op.target == t

/-- The value type of an address type. -/
def addrVal (a : AddrType) : ValType := .num (.int a.intType)

/-- The smaller of two address types (the length operand of `memory.copy`). -/
def amin : AddrType → AddrType → AddrType
  | .i64, .i64 => .i64
  | _, _ => .i32

/-- A memory argument with a random alignment up to `nat` (a log2) and a small offset. -/
def memArg (nat : Nat) : Rand MemArg := do
  return ⟨Fin.ofNat _ (← Rand.nat (nat + 1)), Fin.ofNat _ (← Rand.pick [0, 0, 1, 8, 1024] 0)⟩

/-- A load of a numeric type from memory `x`. -/
def load (x : Nat) : ValType → Option (Rand Instr)
  | .num (.int .i32) => some do
      match ← Rand.nat 3 with
      | 0 => return .intLoad .i32 none (idx x) (← memArg 2)
      | 1 => return .intLoad .i32 (some (.i8, .signed)) (idx x) (← memArg 0)
      | _ => return .intLoad .i32 (some (.i16, .unsigned)) (idx x) (← memArg 1)
  | .num (.int .i64) => some do
      match ← Rand.nat 3 with
      | 0 => return .intLoad .i64 none (idx x) (← memArg 3)
      | 1 => return .intLoad .i64 (some (.i32, .signed)) (idx x) (← memArg 2)
      | _ => return .intLoad .i64 (some (.i8, .unsigned)) (idx x) (← memArg 0)
  | .num (.float .f32) => some do return .floatLoad .f32 (idx x) (← memArg 2)
  | .num (.float .f64) => some do return .floatLoad .f64 (idx x) (← memArg 3)
  | _ => none

/-- A store of a numeric type to memory `x`. -/
def store (x : Nat) : ValType → Option (Rand Instr)
  | .num (.int .i32) => some do
      if ← Rand.bool then return .intStore .i32 none (idx x) (← memArg 2)
      else return .intStore .i32 (some .i8) (idx x) (← memArg 0)
  | .num (.int .i64) => some do
      if ← Rand.bool then return .intStore .i64 none (idx x) (← memArg 3)
      else return .intStore .i64 (some .i16) (idx x) (← memArg 1)
  | .num (.float .f32) => some do return .floatStore .f32 (idx x) (← memArg 2)
  | .num (.float .f64) => some do return .floatStore .f64 (idx x) (← memArg 3)
  | _ => none

/-- Is a type numeric or a vector (`select` without annotation)? -/
def plainSel : ValType → Bool
  | .num _ | .vec _ => true
  | _ => false

/-- Concatenate the outputs of generators. -/
def seqs (gs : List (Rand (List Instr))) : Rand (List Instr) := do
  return (← gs.mapM id).flatten

/-- **The raw generator**: instructions for a goal, at a depth bound. -/
def gen : Nat → Ctx → Goal → Rand (List Instr)
  | 0, c, .val t => leaf c t
  | 0, _, .stmt => pure [.nop]
  | n + 1, c, .val t => do
    let sub := gen n c
    let S := c.S
    let i32 : ValType := .i32
    let ints := (valTypes S).filter fun u => u == .i32 || u == .i64
    let opsNum : List (Rand (List Instr)) := match t with
      | .num (.int it) =>
        [ do seqs [sub (.val t), sub (.val t), do return [.intBinOp it (← Rand.pick intBinOps .add)]],
          do seqs [sub (.val t), do return [.intUnOp it (← Rand.pick (intUnOps S it) .clz)]] ] ++
        (if it == .i32 then
          [ do
              let u ← Rand.pick ints .i32
              match u with
              | .num (.int iu) =>
                if ← Rand.bool then seqs [sub (.val u), pure [.intTestOp iu .eqz]]
                else seqs [sub (.val u), sub (.val u),
                  do return [.intRelOp iu (← Rand.pick intRelOps .eq)]]
              | _ => leaf c t ] ++
          (if S.has .floatNum then
            [ do
                let ft ← Rand.pick [FloatType.f32, .f64] .f32
                seqs [sub (.val (.num (.float ft))), sub (.val (.num (.float ft))),
                  do return [.floatRelOp ft (← Rand.pick floatRelOps .eq)]] ] else [])
         else []) ++
        ((convsTo S (.int it)).map fun op =>
          seqs [sub (.val (.num op.source)), pure [.convert op]])
      | .num (.float ft) =>
        [ do seqs [sub (.val t), sub (.val t), do return [.floatBinOp ft (← Rand.pick floatBinOps .add)]],
          do seqs [sub (.val t), do return [.floatUnOp ft (← Rand.pick floatUnOps .neg)]] ] ++
        ((convsTo S (.float ft)).map fun op =>
          seqs [sub (.val (.num op.source)), pure [.convert op]])
      | .vec _ =>
        [ do seqs [sub (.val t), sub (.val t),
            do return [.vecBinOp (← Rand.pick [VecBinOp.and, .or, .xor, .andnot] .and)]],
          do seqs [sub (.val (.num (.int .i32))), pure [.vecSplat (.int .i32x4)]] ] ++
        (if S.has .relaxedSimd then
          [ seqs [sub (.val t), sub (.val t), sub (.val t),
              pure [.vecFloatTernOp .f32x4 .relaxedMadd]],
            seqs [sub (.val t), sub (.val t), sub (.val t),
              pure [.vecIntTernOp .i8x16 .relaxedLaneSelect]],
            seqs [sub (.val t), sub (.val t), pure [.vecSwizzle .relaxedSwizzle]],
            seqs [sub (.val t), sub (.val t), pure [.vecFloatBinOp .f64x2 .relaxedMax]],
            seqs [sub (.val t), sub (.val t), pure [.vecIntBinOp .i16x8 .relaxedQ15mulrS]],
            seqs [sub (.val t),
              pure [.vecConvert (.float .f32x4) (.int .i32x4) (.relaxedTrunc .signed false)]] ]
         else [])
      | .ref _ => []
    let ms := List.range c.mems.size
    let ax (x : Nat) : ValType := addrVal (c.mems.getD x .i32)
    let opsMem : List (Rand (List Instr)) :=
      (if ms.isEmpty then [] else
        [ do
            let x ← Rand.pick ms 0
            match load x t with
            | some l => seqs [sub (.val (ax x)), do return [← l]]
            | none => leaf c t ]) ++
      (let szs := ms.filter fun x => ax x == t
       if szs.isEmpty then [] else
        [ do return [.memorySize (idx (← Rand.pick szs 0))],
          do
            let x ← Rand.pick szs 0
            seqs [sub (.val t), pure [.memoryGrow (idx x)]] ])
    let callees := (List.range c.funcs.size).filter fun f =>
      (c.types.getD (c.funcs.getD f 0) ⟨[], []⟩).results == [t]
    let opsCall : List (Rand (List Instr)) :=
      if S.has .directCall && !callees.isEmpty then
        [ do
            let f ← Rand.pick callees 0
            let ft := c.types.getD (c.funcs.getD f 0) ⟨[], []⟩
            seqs ((ft.params.map fun p => sub (.val p)) ++ [pure [.call (idx f)]]) ]
      else []
    let opsCtl : List (Rand (List Instr)) :=
      if S.has .control then
        [ do
            let c' := { c with labels := none :: c.labels }
            let body ← seqs [gen n c' .stmt, gen n c' (.val t)]
            return [.block (.value t) body],
          do
            let c' := { c with labels := none :: c.labels }
            let cond ← sub (.val i32)
            let th ← gen n c' (.val t)
            let el ← gen n c' (.val t)
            return cond ++ [.if_ (.value t) th el] ] ++
        (if plainSel t then [seqs [sub (.val t), sub (.val t), sub (.val i32), pure [.select none]]]
          else []) ++
        (let ls := (List.range c.locals.size).filter fun i => (c.locals.getD i .i32) == t
         if ls.isEmpty then [] else
          [ do
              let l ← Rand.pick ls 0
              seqs [sub (.val t), pure [.localTee (idx l)]] ])
      else []
    let globs := (List.range c.globals.size).filter fun g => (c.globals.getD g ⟨.const, .i32⟩).value == t
    let opsGlob : List (Rand (List Instr)) :=
      if S.has .globals && !globs.isEmpty then
        [do return [.globalGet (idx (← Rand.pick globs 0))]] else []
    let opsRef : List (Rand (List Instr)) :=
      if S.has .refTypes && t == i32 then [pure [.refNull (.abstract .func), .refIsNull]] else []
    let sigs := (List.range c.types.size).filter fun ti =>
      (c.types.getD ti ⟨[], []⟩).results == [t]
    let opsInd : List (Rand (List Instr)) :=
      if c.table && S.has .callIndirect && !sigs.isEmpty then
        [ do
            let ti ← Rand.pick sigs 0
            let ft := c.types.getD ti ⟨[], []⟩
            seqs ((ft.params.map fun p => sub (.val p)) ++
              [sub (.val i32), pure [.callIndirect (idx 0) (idx ti)]]) ]
      else []
    -- GC: struct and array reads, `i31`, `ref.eq`, `ref.test`, extern/any conversions
    let mkStruct (ti : Nat) (fs : List FieldType) : Rand (List Instr) := do
      if ← Rand.bool then return [.structNewDefault (idx ti)]
      seqs ((fs.map fun f => sub (.val f.storage.unpacked)) ++ [pure [.structNew (idx ti)]])
    let mkArray (ti : Nat) (f : FieldType) : Rand (List Instr) := do
      let len : Instr := .intConst .i32 (BitVec.ofNat _ (← Rand.nat 8))
      match ← Rand.nat 3 with
      | 0 => return [len, .arrayNewDefault (idx ti)]
      | 1 => seqs [sub (.val f.storage.unpacked), pure [len, .arrayNew (idx ti)]]
      | _ =>
        let k ← Rand.nat 3
        seqs ((List.replicate k (sub (.val f.storage.unpacked))) ++
          [pure [.arrayNewFixed (idx ti) (Fin.ofNat _ k)]])
    let sx (st : StorageType) : Rand (Option Signedness) := do
      match st with
      | .packed _ => return some (if ← Rand.bool then .signed else .unsigned)
      | .val _ => return none
    let anyRef : List Instr := [.refNull (.abstract .extern), .anyConvertExtern]
    let opsGC : List (Rand (List Instr)) :=
      if !S.has .gcImm then [] else
        (c.structs.toList.flatMap fun (ti, fs) =>
          (List.range fs.length).filterMap fun i =>
            let f := fs.getD i ⟨.const, .val .i32⟩
            if f.storage.unpacked == t then some (do
              let mk ← mkStruct ti fs
              return mk ++ [.structGet (← sx f.storage) (idx ti) (idx i)]) else none) ++
        (c.arrays.toList.filterMap fun (ti, f) =>
          if f.storage.unpacked == t then some (do
            let a ← mkArray ti f
            seqs [pure a, sub (.val i32), do return [.arrayGet (← sx f.storage) (idx ti)]])
          else none) ++
        (if t == i32 then
          [ do seqs [sub (.val i32), pure [.refI31],
              do return [.i31Get (if ← Rand.bool then .signed else .unsigned)]],
            seqs [sub (.val i32), pure [.refI31], sub (.val i32), pure [.refI31, .refEq]],
            seqs [sub (.val i32), pure [.refI31, .externConvertAny, .refIsNull]],
            do
              let hts : List HeapType := [.abstract .i31, .abstract .eq, .abstract .struct,
                .abstract .array, .abstract .any, .abstract .none] ++
                (c.structs.toList.map fun (ti, _) => .typeIdx (idx ti))
              let ht ← Rand.pick hts (.abstract .i31)
              let rt : RefType := ⟨← Rand.bool, ht⟩
              if ← Rand.bool then return anyRef ++ [.refTest rt]
              else return anyRef ++ [.refCast ⟨true, ht⟩, .refIsNull] ] ++
          (c.arrays.toList.map fun (ti, f) => do
            seqs [mkArray ti f, pure [.arrayLen]])
         else [])
    -- exceptions: a `try_table` catching a tag that carries a `t`
    let tagsT := (List.range c.tags.size).filter fun x => c.tags.getD x [] == [t]
    let opsExn : List (Rand (List Instr)) :=
      if S.has .exn && S.has .control && !tagsT.isEmpty then
        [ do
            let x ← Rand.pick tagsT 0
            let cb := { c with labels := some [] :: some [] :: none :: c.labels }
            let s₁ ← gen n cb .stmt
            let th ← if ← Rand.bool then do
                let cond ← gen n cb (.val i32)
                let ci := { cb with labels := some [] :: cb.labels }
                let v ← gen n ci (.val t)
                pure (cond ++ [.if_ .empty (v ++ [.throw (idx x)]) []])
              else pure []
            let s₂ ← gen n cb .stmt
            let after ← gen n { c with labels := none :: c.labels } (.val t)
            return [.block (.value t)
              ([.block .empty [.tryTable .empty [.catch_ (idx x) (idx 1)] (s₁ ++ th ++ s₂)]] ++
                after)] ]
      else []
    -- typed function references: `call_ref`, `ref.as_non_null`, `br_on_null`
    let refCallees := c.refFuncs.filter fun f =>
      (c.types.getD (c.funcs.getD f 0) ⟨[], []⟩).results == [t]
    let opsFRef : List (Rand (List Instr)) :=
      if !S.has .typedFuncRef then [] else
        (if refCallees.isEmpty then [] else
          [ do
              let f ← Rand.pick refCallees 0
              let ti := c.funcs.getD f 0
              let ft := c.types.getD ti ⟨[], []⟩
              seqs ((ft.params.map fun p => sub (.val p)) ++
                [pure [.refFunc (idx f), .callRef (idx ti)]]) ]) ++
        (if t == i32 && S.has .control then
          [ do
              let v ← gen n { c with labels := none :: c.labels } (.val t)
              return [.block (.value t) (v ++ [.refNull (.abstract .func), .brOnNull (idx 0), .drop])] ] ++
          (if c.refFuncs.isEmpty then [] else
            [ do return [.refFunc (idx (← Rand.pick c.refFuncs 0)), .refAsNonNull, .refIsNull] ])
         else [])
    let opts := [leaf c t] ++ opsNum ++ opsMem ++ opsCall ++ opsCtl ++ opsGlob ++ opsRef ++ opsInd ++
      opsGC ++ opsExn ++ opsFRef
    (opts.getD (← Rand.nat opts.length) (leaf c t))
  | n + 1, c, .stmt => do
    let sub := gen n c
    let S := c.S
    let i32 : ValType := .i32
    let vts := valTypes S
    let anyVal : Rand (List Instr) := do
      let t ← Rand.pick vts .i32
      seqs [sub (.val t), pure [.drop]]
    let opsBase : List (Rand (List Instr)) := [pure [.nop], anyVal]
    let setL := (List.range c.locals.size)
    let opsLocal : List (Rand (List Instr)) :=
      if setL.isEmpty then [] else
        [ do
            let l ← Rand.pick setL 0
            seqs [sub (.val ((c.locals.getD l .i32))), pure [.localSet (idx l)]] ]
    let mutG := (List.range c.globals.size).filter fun g => (c.globals.getD g ⟨.const, .i32⟩).mutability == Mutability.var
    let opsGlob : List (Rand (List Instr)) :=
      if S.has .mutGlobal && !mutG.isEmpty then
        [ do
            let g ← Rand.pick mutG 0
            seqs [sub (.val (c.globals.getD g ⟨.const, .i32⟩).value), pure [.globalSet (idx g)]] ] else []
    let ms := List.range c.mems.size
    let am (x : Nat) : AddrType := c.mems.getD x .i32
    let opsMem : List (Rand (List Instr)) :=
      if ms.isEmpty then [] else
        [ do
            let x ← Rand.pick ms 0
            let t ← Rand.pick vts .i32
            match store x t with
            | some s => seqs [sub (.val (addrVal (am x))), sub (.val t), do return [← s]]
            | none => pure [.nop] ] ++
        (if S.has .bulkMemoryOpt then
          [ do
              let x ← Rand.pick ms 0
              seqs [sub (.val (addrVal (am x))), sub (.val i32), sub (.val (addrVal (am x))),
                pure [.memoryFill (idx x)]],
            do
              let x ← Rand.pick ms 0
              let y ← Rand.pick ms 0
              seqs [sub (.val (addrVal (am x))), sub (.val (addrVal (am y))),
                sub (.val (addrVal (amin (am x) (am y)))), pure [.memoryCopy (idx x) (idx y)]] ]
         else [])
    -- GC writes (mutable fields)
    let opsGC : List (Rand (List Instr)) :=
      if !S.has .gcMut then [] else
        (c.structs.toList.flatMap fun (ti, fs) =>
          (List.range fs.length).filterMap fun i =>
            let f := fs.getD i ⟨.const, .val .i32⟩
            if f.mutability == .var then some (
              seqs [pure [.structNewDefault (idx ti)], sub (.val f.storage.unpacked),
                pure [.structSet (idx ti) (idx i)]]) else none) ++
        (c.arrays.toList.flatMap fun (ti, f) =>
          if f.mutability == .var then
            [ seqs [pure [.intConst .i32 4, .arrayNewDefault (idx ti)], sub (.val i32),
                sub (.val f.storage.unpacked), pure [.arraySet (idx ti)]],
              seqs [pure [.intConst .i32 4, .arrayNewDefault (idx ti)], sub (.val i32),
                sub (.val f.storage.unpacked), sub (.val i32), pure [.arrayFill (idx ti)]] ]
          else [])
    -- exceptions: `try_table` with `catch`/`catch_all`/`catch_all_ref`, `throw`, `throw_ref`
    let tags0 := (List.range c.tags.size).filter fun x => (c.tags.getD x []).isEmpty
    let opsExn : List (Rand (List Instr)) :=
      if !(S.has .exn && S.has .control) then [] else
        [ do
            let cb := { c with labels := some [] :: some [] :: c.labels }
            let body := (← gen n cb .stmt) ++ (← gen n cb .stmt)
            let cs ← if !tags0.isEmpty && (← Rand.bool) then
                pure [Catch.catch_ (idx (← Rand.pick tags0 0)) (idx 0)]
              else pure [Catch.catchAll (idx 0)]
            return [.block .empty [.tryTable .empty cs body]],
          do
            let cb := { c with labels := some [] :: none :: c.labels }
            let body ← gen n cb .stmt
            let exnref : ValType := .ref ⟨true, .abstract .exn⟩
            let thr ← Rand.chance 1 4
            let blk : Instr := .block (.value exnref)
              [.tryTable .empty [.catchAllRef (idx 0)] body, .refNull (.abstract .exn)]
            if !thr then return [blk, .drop]
            let cond ← sub (.val i32)
            return cond ++ [.if_ .empty [blk, .throwRef] []] ] ++
        (if c.tags.isEmpty then [] else
          [ do
              let x ← Rand.nat c.tags.size
              let ci := { c with labels := some [] :: c.labels }
              let args ← (c.tags.getD x []).mapM fun t => gen n ci (.val t)
              let cond ← sub (.val i32)
              return cond ++ [.if_ .empty (args.flatten ++ [.throw (idx x)]) []] ])

    let opsCall : List (Rand (List Instr)) :=
      if S.has .directCall && c.funcs.size > 0 then
        [ do
            let f ← Rand.nat c.funcs.size
            let ft := c.types.getD (c.funcs.getD f 0) ⟨[], []⟩
            seqs ((ft.params.map fun p => sub (.val p)) ++ [pure [.call (idx f)]] ++
              ft.results.map fun _ => pure [.drop]) ]
      else []
    let brs := (List.range c.labels.length).filter fun l => c.labels.getD l none == some []
    let opsCtl : List (Rand (List Instr)) :=
      if S.has .control then
        [ do
            let c' := { c with labels := some [] :: c.labels }
            return [.block .empty ((← gen n c' .stmt) ++ (← gen n c' .stmt))],
          do
            let c' := { c with labels := none :: c.labels }
            return [.loop .empty ((← gen n c' .stmt) ++ (← gen n c' .stmt))],
          do
            let c' := { c with labels := some [] :: c.labels }
            let cond ← sub (.val i32)
            return cond ++ [.if_ .empty (← gen n c' .stmt) (← gen n c' .stmt)] ] ++
        (if brs.isEmpty then [] else
          [ do
              let l ← Rand.pick brs 0
              seqs [sub (.val i32), pure [.brIf (idx l)]] ])
      else []
    let opts := opsBase ++ opsLocal ++ opsGlob ++ opsMem ++ opsCall ++ opsCtl ++ opsGC ++ opsExn
    (opts.getD (← Rand.nat opts.length) (pure [.nop]))

/-- `k` statements. -/
def stmts (n : Nat) (c : Ctx) (k : Nat) : Rand (List Instr) := do
  return ((← Rand.list k (gen n c .stmt))).flatten

/-- A function body for a type: statements, then the results, or (with tail calls) a
`return_call` of a function with the same results. -/
def body (n : Nat) (c : Ctx) (ft : FuncType) : Rand (List Instr) := do
  let s ← stmts n c (← Rand.range 1 (2 + n))
  let tails := (List.range c.funcs.size).filter fun f =>
    (c.types.getD (c.funcs.getD f 0) ⟨[], []⟩).results == ft.results
  if c.S.has .tailCall && !tails.isEmpty && (← Rand.chance 1 4) then
    let f ← Rand.pick tails 0
    let gt := c.types.getD (c.funcs.getD f 0) ⟨[], []⟩
    let args ← gt.params.mapM fun t => gen n c (.val t)
    if c.S.has .typedFuncRef && c.refFuncs.contains f && (← Rand.bool) then
      return s ++ args.flatten ++ [.refFunc (idx f), .returnCallRef (idx (c.funcs.getD f 0))]
    return s ++ args.flatten ++ [.returnCall (idx f)]
  let vs ← ft.results.mapM fun t => gen n c (.val t)
  return s ++ vs.flatten

/-- A function type of `S`. -/
def funcType (S : FeatureSet) : Rand FuncType := do
  let vts := valTypes S
  let np ← Rand.nat 4
  let nr ← Rand.nat (if S.has .multiValue then 3 else 2)
  return ⟨← Rand.list np (Rand.pick vts .i32), ← Rand.list nr (Rand.pick vts .i32)⟩

/-- The single function type of a recursion group (`⟨[], []⟩` otherwise). -/
def RecType.funcType (rt : RecType) : FuncType :=
  match rt.types with
  | [⟨_, [], .func ft⟩] => ft
  | _ => ⟨[], []⟩

/-- The memories of a module (imports first), by address type. -/
def memsOf (m : Module) : Array AddrType :=
  ((m.imports.filterMap fun i => match i.type with
    | .memory mt => some mt.address | _ => none) ++ m.memories.map MemoryType.address).toArray

/-- The type definitions of a module, with their indices. -/
def typeDefs (m : Module) : List (Nat × SubType) :=
  (m.types.flatMap RecType.types).zipIdx.map fun (st, i) => (i, st)

/-- The functions of a module that `ref.func` may name: those in element segments and exports. -/
def declaredFuncs (m : Module) : List Nat :=
  ((m.elems.flatMap fun e => e.init.filterMap fun
      | [.refFunc f] => some f.toNat
      | _ => none) ++
    m.exports.filterMap fun e => match e.index with
      | .func f => some f.toNat
      | _ => none).eraseDups

/-- **The generation context of a module**: its function types, functions, globals,
memories, tags, GC types and declared functions; locals and labels empty. -/
def ctxOf (S : FeatureSet) (m : Module) : Ctx where
  S := S
  types := (m.types.map RecType.funcType).toArray
  funcs := (m.functionTypes.map fun t => t.value.val).toArray
  globals := ((m.imports.filterMap fun i => match i.type with
    | .global g => some g | _ => none) ++ m.globals.map Declaration.Global.type).toArray
  mem := !(memsOf m).isEmpty
  mems := memsOf m
  locals := #[]
  labels := []
  table := !m.tables.isEmpty || m.imports.any Import.isTable
  tags := ((m.imports.filterMap fun i => match i.type with
    | .tag x => some x | _ => none) ++ m.tags).toArray.map fun x =>
      (RecType.funcType (m.types.getD x.toNat ⟨[]⟩)).params
  structs := ((typeDefs m).filterMap fun (i, st) => match st.body with
    | .struct fs => some (i, fs) | _ => none).toArray
  arrays := ((typeDefs m).filterMap fun (i, st) => match st.body with
    | .array f => some (i, f) | _ => none).toArray
  refFuncs := declaredFuncs m

/-- The function type of a function of a module. -/
def funcTypeOf (m : Module) (f : Func) : FuncType :=
  RecType.funcType (m.types.getD f.type.value.val ⟨[]⟩)

/-- A global of `S`. -/
def global (S : FeatureSet) : Rand Global := do
  let t ← Rand.pick (valTypes S) .i32
  let mut_ ← if S.has .mutGlobal then Rand.bool else pure false
  let init ← match t with
    | .num (.int it) =>
      if S.has .extConst && (← Rand.bool) then
        pure ((← const t) ++ (← const t) ++
          [.intBinOp it (← Rand.pick [IntBinOp.add, .sub, .mul] .add)])
      else const t
    | _ => const t
  return ⟨⟨if mut_ then .var else .const, t⟩, init⟩

/-- A GC field of `S`: a numeric (or vector) value or a packed `i8`/`i16`, mutable only with
mutable GC. -/
def field (S : FeatureSet) : Rand FieldType := do
  let k ← Rand.nat 4
  let pk ← Rand.bool
  let vt ← Rand.pick (valTypes S) .i32
  let st : StorageType :=
    if k = 0 then StorageType.packed (if pk then .i8 else .i16) else StorageType.val vt
  let mt : Mutability := if S.has .gcMut && (← Rand.bool) then .var else .const
  return ⟨mt, st⟩

/-- **A raw module of `S`** of a given size. -/
def module (S : FeatureSet) (size : Nat) : Rand Module := do
  let depth := min 4 (1 + size / 8)
  let ftypes ← Rand.list (← Rand.range 1 (1 + min 6 (size / 4))) (funcType S)
  let nt := ftypes.length
  -- exception tags carry nothing or one value; their types follow the function types
  let ntag ← if S.has .exn then Rand.nat 3 else pure 0
  let tagPs ← Rand.list ntag (do
    if ← Rand.bool then pure ([] : List ValType) else return [← Rand.pick (valTypes S) .i32])
  -- GC struct and array types follow
  let nstruct ← if S.has .gcImm then Rand.nat 3 else pure 0
  let structs ← Rand.list nstruct (do Rand.list (← Rand.range 1 3) (field S))
  let narr ← if S.has .gcImm then Rand.nat 3 else pure 0
  let arrays ← Rand.list narr (field S)
  let types : List FuncType := ftypes ++ tagPs.map fun ps => ⟨ps, []⟩
  let gcTypes : List RecType :=
    structs.map (fun fs => ⟨[⟨true, [], .struct fs⟩]⟩) ++ arrays.map fun f => ⟨[⟨true, [], .array f⟩]⟩
  let nimp ← if S.has .directCall then Rand.nat 2 else pure 0
  let imports : List Import := (List.range nimp).map fun i =>
    ⟨"env", s!"f{i}", .func (idx (i % nt))⟩
  let nfun ← Rand.range 1 (1 + min 12 (size / 2))
  let ftys ← Rand.list nfun (Rand.nat nt)
  let globals ← Rand.list (← Rand.nat (if S.has .globals then 4 else 1)) (global S)
  let globals := if S.has .globals then globals else []
  let mem ← if S.has .memory && S.has .intNum then Rand.bool else pure false
  let nmem ← if !mem then pure 0 else if S.has .multiMemory then Rand.range 1 3 else pure 1
  let addrs ← Rand.list nmem (do
    if S.has .memory64 && (← Rand.bool) then pure AddrType.i64 else pure .i32)
  let tbl ← if S.has .table && S.has .refTypes then Rand.bool else pure false
  let funcref : RefType := ⟨true, .abstract .func⟩
  let base : Module :=
    { types := types.map (fun ft => ⟨[⟨true, [], .func ft⟩]⟩) ++ gcTypes
      imports := imports
      tags := (List.range ntag).map fun i => idx (nt + i)
      globals := globals
      memories := addrs.map fun a => ⟨a, ⟨Fin.ofNat _ 1, some (Fin.ofNat _ 4)⟩⟩
      tables := if tbl then
        [⟨⟨.i32, ⟨Fin.ofNat _ (nimp + nfun), none⟩, funcref⟩, [.refNull (.abstract .func)]⟩]
        else []
      elems := (if tbl then
        [⟨funcref, (List.range (nimp + nfun)).map fun f => [.refFunc (idx f)],
          .active (idx 0) [.intConst .i32 0]⟩]
        else []) ++
        (if S.has .typedFuncRef && S.has .bulkMemory then
          [⟨funcref, (List.range nfun).map fun f => [.refFunc (idx (nimp + f))], .declarative⟩]
         else [])
      funcs := ftys.map fun t => ⟨idx t, [], []⟩ }
  let c := ctxOf S base
  let funcs ← ftys.mapM fun t => do
    let ft := types.getD t ⟨[], []⟩
    let locals ← Rand.list (← Rand.nat 3) (Rand.pick (valTypes S) .i32)
    let c' := { c with locals := (ft.params ++ locals).toArray }
    return (⟨idx t, locals, ← body depth c' ft⟩ : Func)
  let data ← if mem && (← Rand.bool) then do
      let off ← Rand.nat 1024
      let bytes ← Rand.list (← Rand.nat 16) (Rand.nat 256)
      let it := (addrs.headD .i32).intType
      pure [(⟨⟨(bytes.map UInt8.ofNat).toArray⟩, .active (idx 0) [.intConst it (BitVec.ofNat _ off)]⟩ :
        Data)]
    else pure []
  let exports : List Export :=
    ((List.range nfun).map fun i => ⟨s!"f{i}", .func (idx (nimp + i))⟩) ++
    ((List.range nmem).map fun i =>
      ⟨if i = 0 then "memory" else s!"memory{i}", .memory (idx i)⟩) ++
    ((List.range ntag).map fun i => ⟨s!"t{i}", .tag (idx i)⟩) ++
    ((List.range globals.length).map fun g => ⟨s!"g{g}", .global (idx g)⟩)
  return { base with funcs := funcs, data := data, exports := exports }

/-! ## Raw mutation -/

/-- Replace the `i`th element. -/
def setAt {α : Type} (xs : List α) (i : Nat) (x : α) : List α := xs.set i x

/-- Constants anywhere in an instruction sequence, rewritten by `f` at the `k`th one. -/
def mapConsts (k : Nat) (f : Instr → Instr) (is : List Instr) : List Instr :=
  (go is k).1
where
  go : List Instr → Nat → List Instr × Nat
    | [], k => ([], k)
    | i :: is, k =>
      let (i', k') := match i with
        | .intConst .. | .floatConst .. => (if k = 0 then f i else i, k - 1)
        | _ => (i, k)
      let (is', k'') := go is k'
      (i' :: is', k'')

/-- **Raw mutation of a module**: one of nine rewrites, chosen by the seed. -/
def mutate (S : FeatureSet) (r : Rng) (m : Module) : Module := Rand.run (do
  let c := ctxOf S m
  let nimp := m.importedFunctions.length
  let nf := m.funcs.length
  match ← Rand.nat 9 with
  | 0 =>
    -- regenerate a function body
    if nf = 0 then return m
    let i ← Rand.nat nf
    let f := m.funcs.getD i ⟨idx 0, [], []⟩
    let ft := funcTypeOf m f
    let c' := { c with locals := (ft.params ++ f.locals).toArray }
    let b ← body 3 c' ft
    return { m with funcs := setAt m.funcs i ⟨f.type, f.locals, b⟩ }
  | 1 =>
    -- insert a statement at the top level of a body
    if nf = 0 then return m
    let i ← Rand.nat nf
    let f := m.funcs.getD i ⟨idx 0, [], []⟩
    let ft := funcTypeOf m f
    let c' := { c with locals := (ft.params ++ f.locals).toArray }
    let s ← gen 2 c' .stmt
    let p ← Rand.nat (f.body.length + 1)
    let nb := f.body.take p ++ s ++ f.body.drop p
    return { m with funcs := setAt m.funcs i ⟨f.type, f.locals, nb⟩ }
  | 2 =>
    -- delete a top-level instruction
    if nf = 0 then return m
    let i ← Rand.nat nf
    let f := m.funcs.getD i ⟨idx 0, [], []⟩
    let p ← Rand.nat f.body.length
    return { m with funcs := setAt m.funcs i ⟨f.type, f.locals, f.body.eraseIdx p⟩ }
  | 3 =>
    -- change a constant
    if nf = 0 then return m
    let i ← Rand.nat nf
    let f := m.funcs.getD i ⟨idx 0, [], []⟩
    let k ← Rand.nat 8
    let v ← bits
    let g : Instr → Instr := fun
      | .intConst it _ => .intConst it (BitVec.ofNat _ v)
      | .floatConst ft _ => .floatConst ft (BitVec.ofNat _ v)
      | j => j
    return { m with funcs := setAt m.funcs i ⟨f.type, f.locals, mapConsts k g f.body⟩ }
  | 4 =>
    -- add a global and export it
    let g ← global S
    let n := c.globals.size
    return { m with globals := m.globals ++ [g],
                    exports := m.exports ++ [⟨s!"gen_g{n}", .global (idx n)⟩] }
  | 5 =>
    -- add a function of a new type and export it
    let ft ← funcType S
    let ti := m.types.length
    let locals ← Rand.list (← Rand.nat 3) (Rand.pick (valTypes S) .i32)
    let c' := { c with locals := (ft.params ++ locals).toArray,
                       types := c.types.push ft, funcs := c.funcs.push ti }
    let b ← body 2 c' ft
    return { m with types := m.types ++ [⟨[⟨true, [], .func ft⟩]⟩],
                    funcs := m.funcs ++ [⟨idx ti, locals, b⟩],
                    exports := m.exports ++ [⟨s!"gen_f{nimp + nf}", .func (idx (nimp + nf))⟩] }
  | 6 =>
    -- drop an export
    if m.exports.isEmpty then return m
    return { m with exports := m.exports.eraseIdx (← Rand.nat m.exports.length) }
  | 7 =>
    -- rotate the exports
    match m.exports with
    | [] => return m
    | e :: es => return { m with exports := es ++ [e] }
  | _ =>
    -- wrap a body's statements in a block
    if nf = 0 then return m
    let i ← Rand.nat nf
    let f := m.funcs.getD i ⟨idx 0, [], []⟩
    let ft := funcTypeOf m f
    if !ft.results.isEmpty then return m
    return { m with funcs := setAt m.funcs i ⟨f.type, f.locals, [.block .empty f.body]⟩ }) r

/-! ## Shrinking -/

mutual
/-- The number of instructions, nested bodies included. -/
def instrSize : Instr → Nat
  | .block _ b | .loop _ b | .tryTable _ _ b => 1 + instrsSize b
  | .if_ _ t e => 1 + instrsSize t + instrsSize e
  | _ => 1

/-- `instrSize` of a sequence. -/
def instrsSize : List Instr → Nat
  | [] => 0
  | i :: is => instrSize i + instrsSize is
end

/-- **The size of a module**: its instructions and the lengths of its sections. -/
def size (m : Module) : Nat :=
  (m.funcs.map fun f => 1 + f.locals.length + instrsSize f.body).sum +
    (m.globals.map fun g => 1 + instrsSize g.init).sum +
    m.types.length + m.imports.length + m.memories.length + m.tables.length + m.data.length +
    m.elems.length + m.exports.length + m.tags.length + (if m.start.isSome then 1 else 0)

/-- The default results of a function type (a minimal body). -/
def defaults (ft : FuncType) : List Instr :=
  ft.results.flatMap fun
    | .num (.int it) => [.intConst it 0]
    | .num (.float ft) => [.floatConst ft 0]
    | .vec _ => [.vecConst 0]
    | .ref rt => [.refNull rt.heap]

/-- Unwrap the `j`th top-level structured instruction of a body. -/
def unwrapAt (b : List Instr) (j : Nat) : List Instr :=
  match b[j]? with
  | some (.block _ inner) | some (.loop _ inner) => b.take j ++ inner ++ b.drop (j + 1)
  | some (.if_ _ th _) => b.take j ++ [.drop] ++ th ++ b.drop (j + 1)
  | _ => b

/-- **Shrink candidates**, largest reductions first: drop the start function, an export, a
data segment, the last global, the last function; replace a body by default results; drop or
unwrap a top-level instruction; drop a local. -/
def cands (m : Module) : List Module :=
  (if m.start.isSome then [{ m with start := none }] else []) ++
  ((List.range m.exports.length).map fun i => { m with exports := m.exports.eraseIdx i }) ++
  ((List.range m.data.length).map fun i => { m with data := m.data.eraseIdx i }) ++
  (if m.globals.isEmpty then [] else [{ m with globals := m.globals.dropLast }]) ++
  (if m.funcs.isEmpty then [] else [{ m with funcs := m.funcs.dropLast }]) ++
  ((List.range m.funcs.length).flatMap fun i =>
    let f := m.funcs.getD i ⟨idx 0, [], []⟩
    let mk (b : List Instr) : Module := { m with funcs := setAt m.funcs i ⟨f.type, f.locals, b⟩ }
    [mk (defaults (funcTypeOf m f))] ++
    ((List.range f.body.length).map fun j => mk (f.body.eraseIdx j)) ++
    ((List.range f.body.length).map fun j => mk (unwrapAt f.body j)) ++
    (if f.locals.isEmpty then [] else
      [{ m with funcs := setAt m.funcs i ⟨f.type, f.locals.dropLast, f.body⟩ }]))

end Raw

/-! ## The checked objects

What the verified generator and mutator of `Thms` (`featGen`, `featMut`) compute
(`featGen_run_eq`, `featMut_run_eq`): an executable runs these. -/

/-- **The generator of a feature set**: the raw generator, checked; the empty module
otherwise. -/
def featGenRun (S : FeatureSet) : Rng → Nat → Module :=
  Generator.guardedRun (featCheck S) (fun r n => Rand.run (Raw.module S n) r) {}

/-- **The mutator of a feature set**: the raw mutation, checked; the input otherwise. -/
def featMutRun (S : FeatureSet) : Rng → Module → Module :=
  Mutator.guardedRun (featCheck S) (Raw.mutate S)

/-- The shrinker of Core modules (sizes and candidates do not depend on the feature set; the
feature set enters through the predicate, `Shrinker.shrink_valid`). -/
def featShrinker : Shrinker Module := ⟨Raw.size, Raw.cands⟩

/-- **Checked shrinking at `S`**: keep the predicate and validity in `S`. -/
def featShrink (S : FeatureSet) (p : Module → Bool) (m : Module) : Module :=
  featShrinker.shrink (fun c => featCheck S c && p c) m

end Silmaril.Wasm.Tools.Gen.Core
