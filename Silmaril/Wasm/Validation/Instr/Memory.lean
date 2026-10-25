module

public import Silmaril.Wasm.Validation.TypeOk

@[expose] public section

/-! # Typing family: memory instructions (§2.3 "Memory instructions")

Spec rules (all 17 present): `Instr_ok/memory.size`, `memory.grow`, `memory.fill`,
`memory.copy`, `memory.init`, `data.drop`, `load-num`, `load-pack`, `store-num`,
`store-pack`, `vload-num`, `vload-pack`, `vload-splat`, `vload-zero`,
`vload_lane`, `vstore`, `vstore_lane` (the two commented-out legacy rules
`Instr_ok/load`/`store` of the SpecTec source are not part of the spec).

The source syntax splits `LOAD`/`STORE` by integer/float and packed/unpacked.
The grammar side condition of packed accesses (`K < |Inn|`) is a premise here.
-/

namespace Silmaril.Wasm.Validation

/-- The access width `N` of a vector load (the `Memarg_ok` bound). -/
def _root_.Silmaril.Wasm.VecLoadOp.accessWidth : VecLoadOp → Nat
  | .full => 128
  | .extend8x8 _ | .extend16x4 _ | .extend32x2 _ => 64
  | .splat size => size.width
  | .zero32 => 32
  | .zero64 => 64

inductive MemoryInstrOk (C : Context) : Instr → InstrType → Prop where
  /-- `Instr_ok/memory.size`. -/
  | memorySize {x : MemIdx} {a : AddrType} {l : Limits} (h : C.mems[x.toNat]? = some ⟨a, l⟩) :
      MemoryInstrOk C (.memorySize x) (.plain [] [a.valType])
  /-- `Instr_ok/memory.grow`. -/
  | memoryGrow {x : MemIdx} {a : AddrType} {l : Limits} (h : C.mems[x.toNat]? = some ⟨a, l⟩) :
      MemoryInstrOk C (.memoryGrow x) (.plain [a.valType] [a.valType])
  /-- `Instr_ok/memory.fill`. -/
  | memoryFill {x : MemIdx} {a : AddrType} {l : Limits} (h : C.mems[x.toNat]? = some ⟨a, l⟩) :
      MemoryInstrOk C (.memoryFill x) (.plain [a.valType, .i32, a.valType] [])
  /-- `Instr_ok/memory.copy`. -/
  | memoryCopy {x₁ x₂ : MemIdx} {a₁ a₂ : AddrType} {l₁ l₂ : Limits}
      (h₁ : C.mems[x₁.toNat]? = some ⟨a₁, l₁⟩) (h₂ : C.mems[x₂.toNat]? = some ⟨a₂, l₂⟩) :
      MemoryInstrOk C (.memoryCopy x₁ x₂)
        (.plain [a₁.valType, a₂.valType, (AddrType.min a₁ a₂).valType] [])
  /-- `Instr_ok/memory.init`. -/
  | memoryInit {x : MemIdx} {y : DataIdx} {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hd : C.datas[y.toNat]? = some ()) :
      MemoryInstrOk C (.memoryInit x y) (.plain [a.valType, .i32, .i32] [])
  /-- `Instr_ok/data.drop`. -/
  | dataDrop {y : DataIdx} (hd : C.datas[y.toNat]? = some ()) :
      MemoryInstrOk C (.dataDrop y) (.plain [] [])
  /-- `Instr_ok/load-num` (integers). -/
  | intLoad {t : IntType} {x : MemIdx} {arg : MemArg} {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hm : MemArgOk arg a t.width) :
      MemoryInstrOk C (.intLoad t none x arg) (.plain [a.valType] [.num (.int t)])
  /-- `Instr_ok/load-pack`. -/
  | intLoadPack {t : IntType} {sz : PackSize} {sx : Signedness} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hsz : sz.width < t.width)
      (hm : MemArgOk arg a sz.width) :
      MemoryInstrOk C (.intLoad t (some (sz, sx)) x arg) (.plain [a.valType] [.num (.int t)])
  /-- `Instr_ok/load-num` (floats). -/
  | floatLoad {t : FloatType} {x : MemIdx} {arg : MemArg} {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hm : MemArgOk arg a t.width) :
      MemoryInstrOk C (.floatLoad t x arg) (.plain [a.valType] [.num (.float t)])
  /-- `Instr_ok/store-num` (integers). -/
  | intStore {t : IntType} {x : MemIdx} {arg : MemArg} {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hm : MemArgOk arg a t.width) :
      MemoryInstrOk C (.intStore t none x arg) (.plain [a.valType, .num (.int t)] [])
  /-- `Instr_ok/store-pack`. -/
  | intStorePack {t : IntType} {sz : PackSize} {x : MemIdx} {arg : MemArg}
      {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hsz : sz.width < t.width)
      (hm : MemArgOk arg a sz.width) :
      MemoryInstrOk C (.intStore t (some sz) x arg) (.plain [a.valType, .num (.int t)] [])
  /-- `Instr_ok/store-num` (floats). -/
  | floatStore {t : FloatType} {x : MemIdx} {arg : MemArg} {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hm : MemArgOk arg a t.width) :
      MemoryInstrOk C (.floatStore t x arg) (.plain [a.valType, .num (.float t)] [])
  /-- `Instr_ok/vload-num`, `vload-pack`, `vload-splat`, `vload-zero` (the access
  width is `op.accessWidth`). -/
  | vecLoad {op : VecLoadOp} {x : MemIdx} {arg : MemArg} {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hm : MemArgOk arg a op.accessWidth) :
      MemoryInstrOk C (.vecLoad op x arg) (.plain [a.valType] [.v128])
  /-- `Instr_ok/vload_lane`. -/
  | vecLoadLane {sz : PackSize} {x : MemIdx} {arg : MemArg} {i : LaneIdx}
      {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hm : MemArgOk arg a sz.width)
      (hi : i.val < 128 / sz.width) :
      MemoryInstrOk C (.vecLoadLane sz x arg i) (.plain [a.valType, .v128] [.v128])
  /-- `Instr_ok/vstore`. -/
  | vecStore {x : MemIdx} {arg : MemArg} {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hm : MemArgOk arg a 128) :
      MemoryInstrOk C (.vecStore x arg) (.plain [a.valType, .v128] [])
  /-- `Instr_ok/vstore_lane`. -/
  | vecStoreLane {sz : PackSize} {x : MemIdx} {arg : MemArg} {i : LaneIdx}
      {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (hm : MemArgOk arg a sz.width)
      (hi : i.val < 128 / sz.width) :
      MemoryInstrOk C (.vecStoreLane sz x arg i) (.plain [a.valType, .v128] [])

end Silmaril.Wasm.Validation
