module

public import Silmaril.Wasm.Execution.Core.Step.Table
public import Silmaril.Wasm.Numerics.VectorProfile

@[expose] public section

/-! # Reduction family: memory and data-segment instructions

Spec rules (all 36 present, grouped as in the spec):
* loads: `load-num-oob/val` (integer and float constructors), `load-pack-oob/val`,
  `vload-num-oob/val`, `vload-pack-oob/val`, `vload-splat-oob/val`,
  `vload-zero-oob/val` (the four `vload` shapes share `vecLoadOob`/`vecLoadVal`
  through `VecLoadOp.accessWidth` and `vecLoadResult`), `vload_lane-oob/val`;
* stores: `store-num-oob/val` (integer and float), `store-pack-oob/val`,
  `vstore-oob/val`, `vstore_lane-oob/val`;
* `memory.size`, `memory.grow-succeed/fail`, `memory.fill-oob/zero/succ`,
  `memory.copy-oob/zero/le/gt`, `memory.init-oob/zero/succ`, `data.drop`.

Bounds are checked on natural numbers (`i + offset + width/8 ≤ |bytes|`) before
any truncation, so memory64 needs no special case. The byte-level helpers are
the shared `Execution.Memory.load`/`store`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics

/-- `$memarg0 = {ALIGN 0, OFFSET 0}`. -/
def memarg0 : MemArg := ⟨0, 0⟩

/-- The effective address `i + ao.OFFSET` (not wrapped). -/
def effAddr (i : Nat) (arg : MemArg) : Nat := i + arg.offset.val

/-- Widening lanes of a `K×M` vector load. -/
def extendLanes (K M : Nat) (sx : Signedness) {n : Nat} (c : BitVec n) : V128 :=
  invLanes (2 * K) ((List.range M).map fun k =>
    let l := c.extractLsb' (k * K) K
    match sx with
    | .signed => l.signExtend (2 * K)
    | .unsigned => l.setWidth (2 * K))

/-- The vector produced by a vector load from the loaded bits. -/
def vecLoadResult : VecLoadOp → {n : Nat} → BitVec n → V128
  | .full, _, c => c.setWidth 128
  | .extend8x8 sx, _, c => extendLanes 8 8 sx c
  | .extend16x4 sx, _, c => extendLanes 16 4 sx c
  | .extend32x2 sx, _, c => extendLanes 32 2 sx c
  | .splat sz, _, c => invLanes sz.width (List.replicate (128 / sz.width) (c.setWidth sz.width))
  | .zero32, _, c => c.setWidth 128
  | .zero64, _, c => c.setWidth 128

/-- `STORE I32 8 x $memarg0`. -/
def store8 (x : MemIdx) : Admin := .plain (.intStore .i32 (some .i8) x memarg0)

/-- `LOAD I32 (8 _ U) x $memarg0`. -/
def load8u (x : MemIdx) : Admin := .plain (.intLoad .i32 (some (.i8, .unsigned)) x memarg0)

variable {H : Type}

inductive MemoryStep (P : Profile) : Config H → Config H → Prop where
  /-- `Step_read/load-num-oob` (integers). -/
  | loadIntOob {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg} {a : AddrType}
      {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.intLoad t none x arg)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/load-num-val` (integers). -/
  | loadIntVal {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg} {a : AddrType}
      {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {c : BitVec (8 * (t.width / 8))}
      (hm : s.mem? f x = some (ma, mi))
      (hl : Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) = some c) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.intLoad t none x arg)]⟩
        ⟨s, f, [.plain (.intConst t (c.setWidth t.width))]⟩
  /-- `Step_read/load-pack-oob`. -/
  | loadPackOob {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {sx : Signedness}
      {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {ma : Nat}
      {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/load-pack-val`. -/
  | loadPackVal {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {sx : Signedness}
      {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {ma : Nat}
      {mi : MemInst} {c : BitVec (8 * (sz.width / 8))} (hm : s.mem? f x = some (ma, mi))
      (hl : Memory.load mi.bytes (effAddr i.toNat arg) (sz.width / 8) = some c) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩
        ⟨s, f, [.plain (.intConst t (match sx with
          | .signed => c.signExtend t.width
          | .unsigned => c.setWidth t.width))]⟩
  /-- `Step_read/load-num-oob` (floats). -/
  | loadFloatOob {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
      (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.floatLoad t x arg)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/load-num-val` (floats). -/
  | loadFloatVal {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
      {c : BitVec (8 * (t.width / 8))} (hm : s.mem? f x = some (ma, mi))
      (hl : Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) = some c) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.floatLoad t x arg)]⟩
        ⟨s, f, [.plain (.floatConst t (c.setWidth t.width))]⟩
  /-- `Step_read/vload-{num,pack,splat,zero}-oob`. -/
  | vecLoadOob {s : Store H} {f : Frame} {op : VecLoadOp} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
      (hm : s.mem? f x = some (ma, mi))
      (h : mi.bytes.size < effAddr i.toNat arg + op.accessWidth / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/vload-{num,pack,splat,zero}-val`. -/
  | vecLoadVal {s : Store H} {f : Frame} {op : VecLoadOp} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
      {c : BitVec (8 * (op.accessWidth / 8))} (hm : s.mem? f x = some (ma, mi))
      (hl : Memory.load mi.bytes (effAddr i.toNat arg) (op.accessWidth / 8) = some c) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩
        ⟨s, f, [.plain (.vecConst (vecLoadResult op c))]⟩
  /-- `Step_read/vload_lane-oob`. -/
  | vecLoadLaneOob {s : Store H} {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg}
      {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width} {v : V128} {ma : Nat}
      {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.vecConst v), .plain (.vecLoadLane sz x arg j)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/vload_lane-val`. -/
  | vecLoadLaneVal {s : Store H} {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg}
      {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width} {v : V128} {ma : Nat}
      {mi : MemInst} {k : BitVec (8 * (sz.width / 8))} (hm : s.mem? f x = some (ma, mi))
      (hl : Memory.load mi.bytes (effAddr i.toNat arg) (sz.width / 8) = some k) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.vecConst v), .plain (.vecLoadLane sz x arg j)]⟩
        ⟨s, f, [.plain (.vecConst (invLanes sz.width
          ((lanes sz.width (128 / sz.width) v).set j.val (k.setWidth sz.width))))]⟩
  /-- `Step/store-num-oob` (integers). -/
  | storeIntOob {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {mi : MemInst}
      (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.intConst t c), .plain (.intStore t none x arg)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step/store-num-val` (integers). -/
  | storeIntVal {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {mi : MemInst}
      {b : ByteArray} (hm : s.mem? f x = some (ma, mi))
      (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8)
        (c.setWidth _) = some b) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.intConst t c), .plain (.intStore t none x arg)]⟩
        ⟨s.setMem ma { mi with bytes := b }, f, []⟩
  /-- `Step/store-pack-oob`. -/
  | storePackOob {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {x : MemIdx}
      {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat}
      {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.intConst t c), .plain (.intStore t (some sz) x arg)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step/store-pack-val` (`$wrap__` to the packed width). -/
  | storePackVal {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {x : MemIdx}
      {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat}
      {mi : MemInst} {b : ByteArray} (hm : s.mem? f x = some (ma, mi))
      (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := sz.width / 8)
        (c.setWidth _) = some b) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.intConst t c), .plain (.intStore t (some sz) x arg)]⟩
        ⟨s.setMem ma { mi with bytes := b }, f, []⟩
  /-- `Step/store-num-oob` (floats). -/
  | storeFloatOob {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {mi : MemInst}
      (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.floatConst t c), .plain (.floatStore t x arg)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step/store-num-val` (floats). -/
  | storeFloatVal {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {mi : MemInst}
      {b : ByteArray} (hm : s.mem? f x = some (ma, mi))
      (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8)
        (c.setWidth _) = some b) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.floatConst t c), .plain (.floatStore t x arg)]⟩
        ⟨s.setMem ma { mi with bytes := b }, f, []⟩
  /-- `Step/vstore-oob`. -/
  | vecStoreOob {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
      {i : BitVec a.intType.width} {c : V128} {ma : Nat} {mi : MemInst}
      (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + 16) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStore x arg)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step/vstore-val`. -/
  | vecStoreVal {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
      {i : BitVec a.intType.width} {c : V128} {ma : Nat} {mi : MemInst} {b : ByteArray}
      (hm : s.mem? f x = some (ma, mi))
      (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := 16) c = some b) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStore x arg)]⟩
        ⟨s.setMem ma { mi with bytes := b }, f, []⟩
  /-- `Step/vstore_lane-oob`. -/
  | vecStoreLaneOob {s : Store H} {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg}
      {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width} {c : V128} {ma : Nat}
      {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStoreLane sz x arg j)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step/vstore_lane-val`. -/
  | vecStoreLaneVal {s : Store H} {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg}
      {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width} {c : V128} {ma : Nat}
      {mi : MemInst} {b : ByteArray} (hm : s.mem? f x = some (ma, mi))
      (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := sz.width / 8)
        (((lanes sz.width (128 / sz.width) c).getD j.val 0).setWidth _) = some b) :
      MemoryStep P ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStoreLane sz x arg j)]⟩
        ⟨s.setMem ma { mi with bytes := b }, f, []⟩
  /-- `Step_read/memory.size`. -/
  | size {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
      (hm : s.mem? f x = some (ma, mi)) :
      MemoryStep P ⟨s, f, [.plain (.memorySize x)]⟩
        ⟨s, f, [aconst mi.type.address (BitVec.ofNat _ mi.pages)]⟩
  /-- `Step/memory.grow-succeed`. -/
  | growSucceed {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType} {n : BitVec a.intType.width}
      {ma : Nat} {mi mi' : MemInst} (hm : s.mem? f x = some (ma, mi))
      (hg : mi.grow? n.toNat = some mi') (hp : P.growMaySucceed .memory ma mi.pages n.toNat) :
      MemoryStep P ⟨s, f, [aconst a n, .plain (.memoryGrow x)]⟩
        ⟨s.setMem ma mi', f, [aconst a (BitVec.ofNat _ mi.pages)]⟩
  /-- `Step/memory.grow-fail` (result `-1`). -/
  | growFail {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType} {n : BitVec a.intType.width}
      {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (hp : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none) :
      MemoryStep P ⟨s, f, [aconst a n, .plain (.memoryGrow x)]⟩
        ⟨s, f, [aconst a (BitVec.allOnes _)]⟩
  /-- `Step_read/memory.fill-oob`. -/
  | fillOob {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType} {i n : BitVec a.intType.width}
      {v : Val} {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (h : mi.bytes.size < i.toNat + n.toNat) :
      MemoryStep P ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.memoryFill x)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/memory.fill-zero`. -/
  | fillZero {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType} {i : BitVec a.intType.width}
      {v : Val} {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (h : i.toNat ≤ mi.bytes.size) :
      MemoryStep P ⟨s, f, [aconst a i, v.toAdmin, aconst a 0, .plain (.memoryFill x)]⟩ ⟨s, f, []⟩
  /-- `Step_read/memory.fill-succ`. -/
  | fillSucc {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType} {i n : BitVec a.intType.width}
      {v : Val} {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
      (h : i.toNat + n.toNat ≤ mi.bytes.size) (hn : n ≠ 0) :
      MemoryStep P ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.memoryFill x)]⟩
        ⟨s, f, [aconst a i, v.toAdmin, store8 x,
          aconst a (i + 1), v.toAdmin, aconst a (n - 1), .plain (.memoryFill x)]⟩
  /-- `Step_read/memory.copy-oob`. -/
  | copyOob {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
      {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
      {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
      (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
      (h : mi₁.bytes.size < i₁.toNat + n.toNat ∨ mi₂.bytes.size < i₂.toNat + n.toNat) :
      MemoryStep P ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/memory.copy-zero`. -/
  | copyZero {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
      {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width}
      {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
      (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
      (h : i₁.toNat ≤ mi₁.bytes.size ∧ i₂.toNat ≤ mi₂.bytes.size) :
      MemoryStep P ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' 0, .plain (.memoryCopy x₁ x₂)]⟩
        ⟨s, f, []⟩
  /-- `Step_read/memory.copy-le`. -/
  | copyLe {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
      {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
      {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
      (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
      (h : i₁.toNat + n.toNat ≤ mi₁.bytes.size ∧ i₂.toNat + n.toNat ≤ mi₂.bytes.size)
      (hn : n ≠ 0) (hle : i₁.toNat ≤ i₂.toNat) :
      MemoryStep P ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩
        ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, load8u x₂, store8 x₁,
          aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1), .plain (.memoryCopy x₁ x₂)]⟩
  /-- `Step_read/memory.copy-gt`. -/
  | copyGt {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
      {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
      {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
      (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
      (h : i₁.toNat + n.toNat ≤ mi₁.bytes.size ∧ i₂.toNat + n.toNat ≤ mi₂.bytes.size)
      (hn : n ≠ 0) (hgt : i₂.toNat < i₁.toNat) :
      MemoryStep P ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩
        ⟨s, f, [aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1), aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1),
          load8u x₂, store8 x₁,
          aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1), .plain (.memoryCopy x₁ x₂)]⟩
  /-- `Step_read/memory.init-oob`. -/
  | initOob {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
      {i : BitVec a.intType.width} {j n : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
      (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
      (h : mi.bytes.size < i.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat) :
      MemoryStep P ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/memory.init-zero`. -/
  | initZero {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
      {i : BitVec a.intType.width} {j : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
      (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
      (h : i.toNat ≤ mi.bytes.size ∧ j.toNat ≤ di.bytes.size) :
      MemoryStep P ⟨s, f, [aconst a i, constI32 j, constI32 0, .plain (.memoryInit x y)]⟩ ⟨s, f, []⟩
  /-- `Step_read/memory.init-succ`. -/
  | initSucc {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
      {i : BitVec a.intType.width} {j n : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
      {byte : UInt8}
      (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
      (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size)
      (hn : n ≠ 0) (hb : di.bytes.data[j.toNat]? = some byte) :
      MemoryStep P ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩
        ⟨s, f, [aconst a i, constI32 (BitVec.ofNat 32 byte.toNat), store8 x,
          aconst a (i + 1), constI32 (j + 1), constI32 (n - 1), .plain (.memoryInit x y)]⟩
  /-- `Step/data.drop`. -/
  | dataDrop {s : Store H} {f : Frame} {y : DataIdx} {da : Nat} {di : DataInst}
      (hd : s.data? f y = some (da, di)) :
      MemoryStep P ⟨s, f, [.plain (.dataDrop y)]⟩ ⟨s.setData da ByteArray.empty, f, []⟩

end Silmaril.Wasm.Execution.Core
