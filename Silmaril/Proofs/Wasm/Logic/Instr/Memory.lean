module

public import Silmaril.Proofs.Wasm.Logic.Instr.Basic

/-!
# Instruction rules: linear memory

Rules for every memory instruction of Core 3.0, over **any memory** of the
module (`MemIdx`, resolved by `Store.mem?`) and any address type (`i32` or
`i64` addresses, `memory64`), in both readings (`Wp m`) and every profile:

* loads (`intLoad` full and packed, `floatLoad`, `vecLoad`, `vecLoadLane`) and
  stores (`intStore` full and packed, `floatStore`, `vecStore`, `vecStoreLane`),
  each with its in-bounds rule (through silmaril-lean's `Memory.load`/`Memory.store`)
  and its out-of-bounds trap;
* `memory.size`, `memory.grow` (both outcomes; some step always exists, so the
  rule needs no progress premise: `Wp.memoryGrow`);
* bulk memory, one step at a time, exactly as the specification unfolds it:
  `memory.fill`, `memory.copy` (both directions), `memory.init` (each with its
  trap, zero-length and successor rule) and `data.drop`.

The bulk rules leave the unfolded code (a byte store followed by the shorter
operation); there is no rule yet that summarises a whole `memory.fill`/`copy`/
`init` by its final memory.

A Silmaril addition; the step rules are silmaril-lean's
`Silmaril/Wasm/Execution/Core/Step/Memory.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}
variable {m : Corr} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin} {Q : Post H}
variable {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {ma : Nat}
  {mi : MemInst}

/-- `famOf` of a concrete instruction. -/
local macro "fam_ok" : term => `(by simp [famOf])

/-- An address operand. -/
abbrev addrVal (a : AddrType) (i : BitVec a.intType.width) : Val := .num ⟨.int a.intType, i⟩

@[simp] theorem addrVal_toAdmin (a : AddrType) (i : BitVec a.intType.width) :
    (addrVal a i).toAdmin = aconst a i := rfl

@[simp] theorem toAdmin_ref (r : Ref) : (Val.ref r).toAdmin = .ref r := rfl

@[simp] theorem toAdmin_i32 (c : BitVec 32) : (Val.i32 c).toAdmin = constI32 c := rfl

/-! ## Loads -/

/-- **Integer load** (full width), in bounds. -/
theorem Wp.intLoad {t : IntType} {c : BitVec (8 * (t.width / 8))} (hm : s.mem? f x = some (ma, mi))
    (hl : Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) = some c)
    (h : Wp m P host s f (vals (us ++ [.num ⟨.int t, c.setWidth t.width⟩]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++ .plain (.intLoad t none x arg) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.memory (.loadIntVal hm hl)) h

/-- **Integer load** (full width), out of bounds: traps. -/
theorem Wp.intLoad_oob {t : IntType} (hm : s.mem? f x = some (ma, mi))
    (hb : mi.bytes.size < effAddr i.toNat arg + t.width / 8) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++ .plain (.intLoad t none x arg) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.loadIntOob hm hb)) hq

/-- **Packed integer load** (`load8/16/32_s/u`), in bounds. -/
theorem Wp.intLoadPack {t : IntType} {sz : PackSize} {sx : Signedness}
    {c : BitVec (8 * (sz.width / 8))} (hm : s.mem? f x = some (ma, mi))
    (hl : Memory.load mi.bytes (effAddr i.toNat arg) (sz.width / 8) = some c)
    (h : Wp m P host s f (vals (us ++ [.num ⟨.int t, match sx with
      | .signed => c.signExtend t.width | .unsigned => c.setWidth t.width⟩]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++
      .plain (.intLoad t (some (sz, sx)) x arg) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.memory (.loadPackVal hm hl)) h

/-- **Packed integer load**, out of bounds: traps. -/
theorem Wp.intLoadPack_oob {t : IntType} {sz : PackSize} {sx : Signedness}
    (hm : s.mem? f x = some (ma, mi)) (hb : mi.bytes.size < effAddr i.toNat arg + sz.width / 8)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++
      .plain (.intLoad t (some (sz, sx)) x arg) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.loadPackOob (t := t) (sx := sx) hm hb)) hq

/-- **Float load**, in bounds. -/
theorem Wp.floatLoad {t : FloatType} {c : BitVec (8 * (t.width / 8))}
    (hm : s.mem? f x = some (ma, mi))
    (hl : Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) = some c)
    (h : Wp m P host s f (vals (us ++ [.num ⟨.float t, c.setWidth t.width⟩]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++ .plain (.floatLoad t x arg) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.memory (.loadFloatVal hm hl)) h

/-- **Float load**, out of bounds: traps. -/
theorem Wp.floatLoad_oob {t : FloatType} (hm : s.mem? f x = some (ma, mi))
    (hb : mi.bytes.size < effAddr i.toNat arg + t.width / 8) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++ .plain (.floatLoad t x arg) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.loadFloatOob hm hb)) hq

/-- **Vector load** (`v128.load`, extending, splat and zero loads), in bounds. -/
theorem Wp.vecLoad {op : VecLoadOp} {c : BitVec (8 * (op.accessWidth / 8))}
    (hm : s.mem? f x = some (ma, mi))
    (hl : Memory.load mi.bytes (effAddr i.toNat arg) (op.accessWidth / 8) = some c)
    (h : Wp m P host s f (vals (us ++ [.vec (vecLoadResult op c)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++ .plain (.vecLoad op x arg) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.memory (.vecLoadVal hm hl)) h

/-- **Vector load**, out of bounds: traps. -/
theorem Wp.vecLoad_oob {op : VecLoadOp} (hm : s.mem? f x = some (ma, mi))
    (hb : mi.bytes.size < effAddr i.toNat arg + op.accessWidth / 8) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++ .plain (.vecLoad op x arg) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.vecLoadOob hm hb)) hq

/-- **Vector lane load**, in bounds. -/
theorem Wp.vecLoadLane {sz : PackSize} {j : LaneIdx} {v : V128} {k : BitVec (8 * (sz.width / 8))}
    (hm : s.mem? f x = some (ma, mi))
    (hl : Memory.load mi.bytes (effAddr i.toNat arg) (sz.width / 8) = some k)
    (h : Wp m P host s f (vals (us ++ [.vec (invLanes sz.width
      ((lanes sz.width (128 / sz.width) v).set j.val (k.setWidth sz.width)))]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .vec v]) ++
      .plain (.vecLoadLane sz x arg j) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.memory (.vecLoadLaneVal hm hl)) h

/-- **Vector lane load**, out of bounds: traps. -/
theorem Wp.vecLoadLane_oob {sz : PackSize} {j : LaneIdx} {v : V128}
    (hm : s.mem? f x = some (ma, mi)) (hb : mi.bytes.size < effAddr i.toNat arg + sz.width / 8)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .vec v]) ++
      .plain (.vecLoadLane sz x arg j) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.vecLoadLaneOob hm hb)) hq

/-! ## Stores -/

/-- **Integer store** (full width), in bounds. -/
theorem Wp.intStore {t : IntType} {c : BitVec t.width} {b : ByteArray}
    (hm : s.mem? f x = some (ma, mi))
    (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8) (c.setWidth _) = some b)
    (h : Wp m P host (s.setMem ma { mi with bytes := b }) f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .num ⟨.int t, c⟩]) ++
      .plain (.intStore t none x arg) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.memory (.storeIntVal hm hs)) (by simpa using h)

/-- **Integer store** (full width), out of bounds: traps. -/
theorem Wp.intStore_oob {t : IntType} {c : BitVec t.width} (hm : s.mem? f x = some (ma, mi))
    (hb : mi.bytes.size < effAddr i.toNat arg + t.width / 8) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .num ⟨.int t, c⟩]) ++
      .plain (.intStore t none x arg) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.storeIntOob hm hb)) hq

/-- **Packed integer store** (`store8/16/32`), in bounds. -/
theorem Wp.intStorePack {t : IntType} {sz : PackSize} {c : BitVec t.width} {b : ByteArray}
    (hm : s.mem? f x = some (ma, mi))
    (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := sz.width / 8) (c.setWidth _) = some b)
    (h : Wp m P host (s.setMem ma { mi with bytes := b }) f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .num ⟨.int t, c⟩]) ++
      .plain (.intStore t (some sz) x arg) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.memory (.storePackVal hm hs)) (by simpa using h)

/-- **Packed integer store**, out of bounds: traps. -/
theorem Wp.intStorePack_oob {t : IntType} {sz : PackSize} {c : BitVec t.width}
    (hm : s.mem? f x = some (ma, mi)) (hb : mi.bytes.size < effAddr i.toNat arg + sz.width / 8)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .num ⟨.int t, c⟩]) ++
      .plain (.intStore t (some sz) x arg) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.storePackOob hm hb)) hq

/-- **Float store**, in bounds. -/
theorem Wp.floatStore {t : FloatType} {c : BitVec t.width} {b : ByteArray}
    (hm : s.mem? f x = some (ma, mi))
    (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8) (c.setWidth _) = some b)
    (h : Wp m P host (s.setMem ma { mi with bytes := b }) f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .num ⟨.float t, c⟩]) ++
      .plain (.floatStore t x arg) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.memory (.storeFloatVal hm hs)) (by simpa using h)

/-- **Float store**, out of bounds: traps. -/
theorem Wp.floatStore_oob {t : FloatType} {c : BitVec t.width} (hm : s.mem? f x = some (ma, mi))
    (hb : mi.bytes.size < effAddr i.toNat arg + t.width / 8) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .num ⟨.float t, c⟩]) ++
      .plain (.floatStore t x arg) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.storeFloatOob hm hb)) hq

/-- **Vector store**, in bounds. -/
theorem Wp.vecStore {c : V128} {b : ByteArray} (hm : s.mem? f x = some (ma, mi))
    (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := 16) c = some b)
    (h : Wp m P host (s.setMem ma { mi with bytes := b }) f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .vec c]) ++ .plain (.vecStore x arg) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.memory (.vecStoreVal hm hs)) (by simpa using h)

/-- **Vector store**, out of bounds: traps. -/
theorem Wp.vecStore_oob {c : V128} (hm : s.mem? f x = some (ma, mi))
    (hb : mi.bytes.size < effAddr i.toNat arg + 16) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .vec c]) ++ .plain (.vecStore x arg) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.vecStoreOob hm hb)) hq

/-- **Vector lane store**, in bounds. -/
theorem Wp.vecStoreLane {sz : PackSize} {j : LaneIdx} {c : V128} {b : ByteArray}
    (hm : s.mem? f x = some (ma, mi))
    (hs : Memory.store mi.bytes (effAddr i.toNat arg) (count := sz.width / 8)
      (((lanes sz.width (128 / sz.width) c).getD j.val 0).setWidth _) = some b)
    (h : Wp m P host (s.setMem ma { mi with bytes := b }) f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .vec c]) ++
      .plain (.vecStoreLane sz x arg j) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.memory (.vecStoreLaneVal hm hs)) (by simpa using h)

/-- **Vector lane store**, out of bounds: traps. -/
theorem Wp.vecStoreLane_oob {sz : PackSize} {j : LaneIdx} {c : V128}
    (hm : s.mem? f x = some (ma, mi)) (hb : mi.bytes.size < effAddr i.toNat arg + sz.width / 8)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .vec c]) ++
      .plain (.vecStoreLane sz x arg j) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.vecStoreLaneOob hm hb)) hq

/-! ## Size and growth -/

/-- **`memory.size`** (in pages, at the memory's address type). -/
theorem Wp.memorySize (hm : s.mem? f x = some (ma, mi))
    (h : Wp m P host s f (vals (us ++ [addrVal mi.type.address (BitVec.ofNat _ mi.pages)]) ++
      rest) Q) :
    Wp m P host s f (vals us ++ .plain (.memorySize x) :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (rest := rest)
    (res := [addrVal mi.type.address (BitVec.ofNat _ mi.pages)]) fam_ok (by trivial)
    (.memory (.size hm)) h

/-- In every profile a `grow` can fail or succeed. -/
theorem grow_progress (P : Profile) (k : GrowKind) (addr sz d : Nat) {α : Type} (g : Option α) :
    (∃ y, g = some y ∧ P.growMaySucceed k addr sz d) ∨ (P.growMayFail k addr sz d ∨ g = none) := by
  rcases hP : P.grow with _ | o
  · exact .inr (.inl (by simp [Profile.growMayFail, hP]))
  · rcases ho : o k addr sz d with _ | _
    · rcases g with _ | y
      · exact .inr (.inr rfl)
      · exact .inl ⟨y, rfl, by simp [Profile.growMaySucceed, hP, ho]⟩
    · exact .inr (.inl (by simp [Profile.growMayFail, hP, ho]))

/-- **`memory.grow`**, in every profile: both outcomes the profile allows must be
covered (success when the memory can grow and the profile allows it, failure
with result `-1` when the profile allows it or the memory cannot grow). -/
theorem Wp.memoryGrow {n : BitVec a.intType.width} (hm : s.mem? f x = some (ma, mi))
    (hsucc : ∀ mi', mi.grow? n.toNat = some mi' → P.growMaySucceed .memory ma mi.pages n.toNat →
      Wp m P host (s.setMem ma mi') f (vals (us ++ [addrVal a (BitVec.ofNat _ mi.pages)]) ++ rest) Q)
    (hfail : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none →
      Wp m P host s f (vals (us ++ [addrVal a (BitVec.allOnes _)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a n]) ++ .plain (.memoryGrow x) :: rest) Q := by
  have hp : ∃ c₀, Head P s f [addrVal a n] (.plain (.memoryGrow x)) c₀ := by
    rcases grow_progress P .memory ma mi.pages n.toNat (mi.grow? n.toNat) with ⟨mi', hg, hs⟩ | hf
    · exact ⟨_, .memory (.growSucceed hm hg hs)⟩
    · exact ⟨_, .memory (.growFail hm hf)⟩
  refine Wp.fam fam_ok hp fun c₀ hh => ?_
  obtain ⟨a', n', ma', mi', hargs, hm', hr⟩ := mem_memoryGrow (hh.fam_inv fam_ok)
  obtain ⟨rfl, hn⟩ := addr_arg_inj (List.singleton_inj.mp hargs).symm
  obtain rfl := eq_of_heq hn
  obtain ⟨rfl, rfl⟩ : ma' = ma ∧ mi' = mi := by simpa [hm] using hm'.symm
  rcases hr with ⟨mi'', hg, hs, rfl⟩ | ⟨hf, rfl⟩
  · simpa using hsucc mi'' hg hs
  · simpa using hfail hf

/-! ## Bulk memory, one step at a time -/

section Bulk

variable {v : Val} {n : BitVec a.intType.width}

/-- **`memory.fill`** out of bounds: traps. -/
theorem Wp.memoryFill_oob (hm : s.mem? f x = some (ma, mi)) (hb : mi.bytes.size < i.toNat + n.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, v, addrVal a n]) ++ .plain (.memoryFill x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.fillOob hm hb)) hq

/-- **`memory.fill`** of zero bytes (in bounds). -/
theorem Wp.memoryFill_zero (hm : s.mem? f x = some (ma, mi)) (hb : i.toNat ≤ mi.bytes.size)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, v, addrVal a 0]) ++ .plain (.memoryFill x) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.memory (.fillZero hm hb)) (by simpa using h)

/-- **`memory.fill`** of `n ≠ 0` bytes (in bounds): store one byte, fill the rest. -/
theorem Wp.memoryFill_succ (hm : s.mem? f x = some (ma, mi))
    (hb : i.toNat + n.toNat ≤ mi.bytes.size) (hn : n ≠ 0)
    (h : Wp m P host s f (vals (us ++ [addrVal a i, v]) ++ store8 x ::
      (vals [addrVal a (i + 1), v, addrVal a (n - 1)] ++ .plain (.memoryFill x) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, v, addrVal a n]) ++ .plain (.memoryFill x) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.memory (.fillSucc hm hb hn)) (by simpa using h)

variable {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType} {i₁ : BitVec a₁.intType.width}
  {i₂ : BitVec a₂.intType.width} {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}

/-- **`memory.copy`** out of bounds: traps. -/
theorem Wp.memoryCopy_oob {n : BitVec a'.intType.width} (h₁ : s.mem? f x₁ = some (ma₁, mi₁))
    (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (hb : mi₁.bytes.size < i₁.toNat + n.toNat ∨ mi₂.bytes.size < i₂.toNat + n.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' n]) ++
      .plain (.memoryCopy x₁ x₂) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.copyOob h₁ h₂ hb)) hq

/-- **`memory.copy`** of zero bytes (in bounds). -/
theorem Wp.memoryCopy_zero (h₁ : s.mem? f x₁ = some (ma₁, mi₁))
    (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (hb : i₁.toNat ≤ mi₁.bytes.size ∧ i₂.toNat ≤ mi₂.bytes.size)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' 0]) ++
      .plain (.memoryCopy x₁ x₂) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.memory (.copyZero h₁ h₂ hb)) (by simpa using h)

/-- **`memory.copy`** forwards (destination at or below the source): copy the
first byte, then the rest. -/
theorem Wp.memoryCopy_le {n : BitVec a'.intType.width} (h₁ : s.mem? f x₁ = some (ma₁, mi₁))
    (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (hb : i₁.toNat + n.toNat ≤ mi₁.bytes.size ∧ i₂.toNat + n.toNat ≤ mi₂.bytes.size)
    (hn : n ≠ 0) (hle : i₁.toNat ≤ i₂.toNat)
    (h : Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂]) ++ load8u x₂ :: store8 x₁ ::
      (vals [addrVal a₁ (i₁ + 1), addrVal a₂ (i₂ + 1), addrVal a' (n - 1)] ++
        .plain (.memoryCopy x₁ x₂) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' n]) ++
      .plain (.memoryCopy x₁ x₂) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.memory (.copyLe h₁ h₂ hb hn hle)) (by simpa using h)

/-- **`memory.copy`** backwards (destination above the source): copy the last
byte, then the rest. -/
theorem Wp.memoryCopy_gt {n : BitVec a'.intType.width} (h₁ : s.mem? f x₁ = some (ma₁, mi₁))
    (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (hb : i₁.toNat + n.toNat ≤ mi₁.bytes.size ∧ i₂.toNat + n.toNat ≤ mi₂.bytes.size)
    (hn : n ≠ 0) (hgt : i₂.toNat < i₁.toNat)
    (h : Wp m P host s f (vals (us ++ [addrVal a₁ (i₁ + BitVec.ofNat _ n.toNat - 1),
        addrVal a₂ (i₂ + BitVec.ofNat _ n.toNat - 1)]) ++ load8u x₂ :: store8 x₁ ::
      (vals [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' (n - 1)] ++
        .plain (.memoryCopy x₁ x₂) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' n]) ++
      .plain (.memoryCopy x₁ x₂) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.memory (.copyGt h₁ h₂ hb hn hgt)) (by simpa using h)

variable {y : DataIdx} {da : Nat} {di : DataInst} {j : BitVec 32}

/-- **`memory.init`** out of bounds: traps. -/
theorem Wp.memoryInit_oob {n : BitVec 32} (hm : s.mem? f x = some (ma, mi))
    (hd : s.data? f y = some (da, di))
    (hb : mi.bytes.size < i.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .i32 j, .i32 n]) ++
      .plain (.memoryInit x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.memory (.initOob hm hd hb)) hq

/-- **`memory.init`** of zero bytes (in bounds). -/
theorem Wp.memoryInit_zero (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
    (hb : i.toNat ≤ mi.bytes.size ∧ j.toNat ≤ di.bytes.size)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .i32 j, .i32 0]) ++
      .plain (.memoryInit x y) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.memory (.initZero hm hd hb)) (by simpa using h)

/-- **`memory.init`** of `n ≠ 0` bytes (in bounds): store the first data byte,
then initialise the rest. -/
theorem Wp.memoryInit_succ {n : BitVec 32} {byte : UInt8} (hm : s.mem? f x = some (ma, mi))
    (hd : s.data? f y = some (da, di))
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size) (hn : n ≠ 0)
    (hbyte : di.bytes.data[j.toNat]? = some byte)
    (h : Wp m P host s f (vals (us ++ [addrVal a i, .i32 (BitVec.ofNat 32 byte.toNat)]) ++
      store8 x :: (vals [addrVal a (i + 1), .i32 (j + 1), .i32 (n - 1)] ++
        .plain (.memoryInit x y) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .i32 j, .i32 n]) ++
      .plain (.memoryInit x y) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.memory (.initSucc hm hd hb hn hbyte)) (by simpa using h)

/-- **`data.drop`.** -/
theorem Wp.dataDrop (hd : s.data? f y = some (da, di))
    (h : Wp m P host (s.setData da ByteArray.empty) f (vals us ++ rest) Q) :
    Wp m P host s f (vals us ++ .plain (.dataDrop y) :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (res := []) (rest := rest) fam_ok (by trivial)
    (.memory (.dataDrop hd)) (by simpa using h)

end Bulk

end Silmaril.Wasm.Logic.Hoare
