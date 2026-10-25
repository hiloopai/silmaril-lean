module

public import Silmaril.Wasm.SingleThreaded.Determinism
public import Silmaril.Wasm.Execution.Core.GrowImpl

@[expose] public section

/-! # Computable interpreter: the memory family

`memoryStep?` executes every `MemoryStep` rule (loads, stores, vector loads and
stores, `memory.size`/`grow`/`fill`/`copy`/`init`, `data.drop`) under the
deterministic single-threaded profile `profile o`, and is sound and complete for
the memory-family head steps.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace Mem

/-! ## Value decoding -/

/-- An address-typed integer constant. -/
def addrOf? : Val → Option ((a : AddrType) × BitVec a.intType.width)
  | .num ⟨.int .i32, i⟩ => some ⟨.i32, i⟩
  | .num ⟨.int .i64, i⟩ => some ⟨.i64, i⟩
  | _ => none

/-- An integer constant of type `t`. -/
def intOf? (t : IntType) : Val → Option (BitVec t.width)
  | .num ⟨.int t', c⟩ => if h : t' = t then some (h ▸ c) else none
  | _ => none

/-- A float constant of type `t`. -/
def floatOf? (t : FloatType) : Val → Option (BitVec t.width)
  | .num ⟨.float t', c⟩ => if h : t' = t then some (h ▸ c) else none
  | _ => none

/-- A vector constant. -/
def vecOf? : Val → Option V128
  | .vec c => some c
  | _ => none

theorem addrOf?_eq_some {v : Val} {a : AddrType} {i : BitVec a.intType.width} :
    addrOf? v = some ⟨a, i⟩ → v = .num ⟨.int a.intType, i⟩ := by
  intro h
  cases a <;> rcases v with ⟨⟨t | t⟩, c⟩ | _ | _ <;>
    simp [addrOf?, AddrType.intType] at h ⊢ <;> (cases h; try rfl)

@[simp] theorem addrOf?_aconst (a : AddrType) (i : BitVec a.intType.width) :
    addrOf? (.num ⟨.int a.intType, i⟩) = some ⟨a, i⟩ := by
  cases a <;> rfl

theorem intOf?_eq_some {t : IntType} {v : Val} {c : BitVec t.width} :
    intOf? t v = some c → v = .num ⟨.int t, c⟩ := by
  intro h
  rcases v with ⟨⟨t' | t'⟩, c'⟩ | _ | _ <;> simp [intOf?] at h
  all_goals (obtain ⟨rfl, rfl⟩ := h; rfl)

@[simp] theorem intOf?_self (t : IntType) (c : BitVec t.width) :
    intOf? t (.num ⟨.int t, c⟩) = some c := by
  simp [intOf?]

theorem floatOf?_eq_some {t : FloatType} {v : Val} {c : BitVec t.width} :
    floatOf? t v = some c → v = .num ⟨.float t, c⟩ := by
  intro h
  rcases v with ⟨⟨t' | t'⟩, c'⟩ | _ | _ <;> simp [floatOf?] at h
  all_goals (obtain ⟨rfl, rfl⟩ := h; rfl)

@[simp] theorem floatOf?_self (t : FloatType) (c : BitVec t.width) :
    floatOf? t (.num ⟨.float t, c⟩) = some c := by
  simp [floatOf?]

theorem vecOf?_eq_some {v : Val} {c : V128} : vecOf? v = some c → v = .vec c := by
  intro h
  rcases v with _ | _ | _ <;> simp [vecOf?] at h
  rw [h]

/-- An `i32` constant. -/
def i32Of? (v : Val) : Option (BitVec 32) := intOf? .i32 v

theorem i32Of?_eq_some {v : Val} {c : BitVec 32} : i32Of? v = some c → v = .i32 c :=
  intOf?_eq_some

@[simp] theorem i32Of?_i32 (c : BitVec 32) : i32Of? (.i32 c) = some c := intOf?_self .i32 c

@[simp] theorem vecOf?_vec (c : V128) : vecOf? (.vec c) = some c := rfl

/-! ## Memory bounds -/

theorem load_none {m : Silmaril.Wasm.Execution.Memory.Bytes} {st n : Nat}
    (h : Silmaril.Wasm.Execution.Memory.load m st n = none) : m.size < st + n := by
  unfold Silmaril.Wasm.Execution.Memory.load Silmaril.Wasm.Execution.Memory.readBytes at h
  split at h
  · simp at h
  · omega

theorem load_of_lt {m : Silmaril.Wasm.Execution.Memory.Bytes} {st n : Nat}
    (h : m.size < st + n) : Silmaril.Wasm.Execution.Memory.load m st n = none := by
  unfold Silmaril.Wasm.Execution.Memory.load Silmaril.Wasm.Execution.Memory.readBytes
  split
  · omega
  · rfl

theorem store_none {m : Silmaril.Wasm.Execution.Memory.Bytes} {st n : Nat} {c : BitVec (8 * n)}
    (h : Silmaril.Wasm.Execution.Memory.store m st c = none) : m.size < st + n := by
  unfold Silmaril.Wasm.Execution.Memory.store Silmaril.Wasm.Execution.Memory.writeBytes at h
  split at h
  · simp at h
  · rename_i hn
    have := Silmaril.Wasm.Execution.Memory.encodeLE_size n c.toNat
    omega

theorem store_of_lt {m : Silmaril.Wasm.Execution.Memory.Bytes} {st n : Nat} {c : BitVec (8 * n)}
    (h : m.size < st + n) : Silmaril.Wasm.Execution.Memory.store m st c = none := by
  unfold Silmaril.Wasm.Execution.Memory.store Silmaril.Wasm.Execution.Memory.writeBytes
  have := Silmaril.Wasm.Execution.Memory.encodeLE_size n c.toNat
  split
  · omega
  · rfl

/-! ## Arity and the step on exact arguments -/

/-- The number of values consumed by a memory instruction. -/
def arity : Admin → Option Nat
  | .plain (.intLoad ..) | .plain (.floatLoad ..) | .plain (.vecLoad ..) => some 1
  | .plain (.vecLoadLane ..) | .plain (.intStore ..) | .plain (.floatStore ..)
  | .plain (.vecStore ..) | .plain (.vecStoreLane ..) => some 2
  | .plain (.memorySize _) | .plain (.dataDrop _) => some 0
  | .plain (.memoryGrow _) => some 1
  | .plain (.memoryFill _) | .plain (.memoryCopy ..) | .plain (.memoryInit ..) => some 3
  | _ => none

/-- Sign- or zero-extend a packed load. -/
def packExt (t : IntType) (sx : Signedness) {n : Nat} (c : BitVec n) : BitVec t.width :=
  match sx with
  | .signed => c.signExtend t.width
  | .unsigned => c.setWidth t.width

section Instrs
open Silmaril.Wasm.Execution

variable (s : Store H) (f : Frame)

def loadInt (t : IntType) (x : MemIdx) (arg : MemArg) : List Val → Option (Config H)
  | [v] =>
    match addrOf? v, s.mem? f x with
    | some ⟨_, i⟩, some (_, mi) =>
      match Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) with
      | some c => some ⟨s, f, [.plain (.intConst t (c.setWidth t.width))]⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _ => none
  | _ => none

def loadPack (t : IntType) (sz : PackSize) (sx : Signedness) (x : MemIdx) (arg : MemArg) :
    List Val → Option (Config H)
  | [v] =>
    match addrOf? v, s.mem? f x with
    | some ⟨_, i⟩, some (_, mi) =>
      match Memory.load mi.bytes (effAddr i.toNat arg) (sz.width / 8) with
      | some c => some ⟨s, f, [.plain (.intConst t (packExt t sx c))]⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _ => none
  | _ => none

def loadFloat (t : FloatType) (x : MemIdx) (arg : MemArg) : List Val → Option (Config H)
  | [v] =>
    match addrOf? v, s.mem? f x with
    | some ⟨_, i⟩, some (_, mi) =>
      match Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) with
      | some c => some ⟨s, f, [.plain (.floatConst t (c.setWidth t.width))]⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _ => none
  | _ => none

def vecLoad (op : VecLoadOp) (x : MemIdx) (arg : MemArg) : List Val → Option (Config H)
  | [v] =>
    match addrOf? v, s.mem? f x with
    | some ⟨_, i⟩, some (_, mi) =>
      match Memory.load mi.bytes (effAddr i.toNat arg) (op.accessWidth / 8) with
      | some c => some ⟨s, f, [.plain (.vecConst (vecLoadResult op c))]⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _ => none
  | _ => none

def vecLoadLane (sz : PackSize) (x : MemIdx) (arg : MemArg) (j : LaneIdx) :
    List Val → Option (Config H)
  | [v, w] =>
    match addrOf? v, vecOf? w, s.mem? f x with
    | some ⟨_, i⟩, some c, some (_, mi) =>
      match Memory.load mi.bytes (effAddr i.toNat arg) (sz.width / 8) with
      | some k => some ⟨s, f, [.plain (.vecConst (invLanes sz.width
          ((lanes sz.width (128 / sz.width) c).set j.val (k.setWidth sz.width))))]⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _, _ => none
  | _ => none

def storeInt (t : IntType) (x : MemIdx) (arg : MemArg) : List Val → Option (Config H)
  | [v, w] =>
    match addrOf? v, intOf? t w, s.mem? f x with
    | some ⟨_, i⟩, some c, some (ma, mi) =>
      match Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8)
          (c.setWidth _) with
      | some b => some ⟨s.setMem ma { mi with bytes := b }, f, []⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _, _ => none
  | _ => none

def storePack (t : IntType) (sz : PackSize) (x : MemIdx) (arg : MemArg) :
    List Val → Option (Config H)
  | [v, w] =>
    match addrOf? v, intOf? t w, s.mem? f x with
    | some ⟨_, i⟩, some c, some (ma, mi) =>
      match Memory.store mi.bytes (effAddr i.toNat arg) (count := sz.width / 8)
          (c.setWidth _) with
      | some b => some ⟨s.setMem ma { mi with bytes := b }, f, []⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _, _ => none
  | _ => none

def storeFloat (t : FloatType) (x : MemIdx) (arg : MemArg) : List Val → Option (Config H)
  | [v, w] =>
    match addrOf? v, floatOf? t w, s.mem? f x with
    | some ⟨_, i⟩, some c, some (ma, mi) =>
      match Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8)
          (c.setWidth _) with
      | some b => some ⟨s.setMem ma { mi with bytes := b }, f, []⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _, _ => none
  | _ => none

def vecStore (x : MemIdx) (arg : MemArg) : List Val → Option (Config H)
  | [v, w] =>
    match addrOf? v, vecOf? w, s.mem? f x with
    | some ⟨_, i⟩, some c, some (ma, mi) =>
      match Memory.store mi.bytes (effAddr i.toNat arg) (count := 16) c with
      | some b => some ⟨s.setMem ma { mi with bytes := b }, f, []⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _, _ => none
  | _ => none

def vecStoreLane (sz : PackSize) (x : MemIdx) (arg : MemArg) (j : LaneIdx) :
    List Val → Option (Config H)
  | [v, w] =>
    match addrOf? v, vecOf? w, s.mem? f x with
    | some ⟨_, i⟩, some c, some (ma, mi) =>
      match Memory.store mi.bytes (effAddr i.toNat arg) (count := sz.width / 8)
          (((lanes sz.width (128 / sz.width) c).getD j.val 0).setWidth _) with
      | some b => some ⟨s.setMem ma { mi with bytes := b }, f, []⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _, _ => none
  | _ => none

def memSize (x : MemIdx) : List Val → Option (Config H)
  | [] =>
    match s.mem? f x with
    | some (_, mi) => some ⟨s, f, [aconst mi.type.address (BitVec.ofNat _ mi.pages)]⟩
    | none => none
  | _ => none

def memGrow (o : GrowOracle) (x : MemIdx) : List Val → Option (Config H)
  | [v] =>
    match addrOf? v, s.mem? f x with
    | some ⟨a, n⟩, some (ma, mi) =>
      if (profile o).growMayFail .memory ma mi.pages n.toNat then
        some ⟨s, f, [aconst a (BitVec.allOnes _)]⟩
      else
        match mi.grow? n.toNat with
        | some mi' => some ⟨s.setMem ma mi', f, [aconst a (BitVec.ofNat _ mi.pages)]⟩
        | none => some ⟨s, f, [aconst a (BitVec.allOnes _)]⟩
    | _, _ => none
  | _ => none

def memFill (x : MemIdx) : List Val → Option (Config H)
  | [v₁, v, v₃] =>
    match addrOf? v₁, s.mem? f x with
    | some ⟨a, i⟩, some (_, mi) =>
      match intOf? a.intType v₃ with
      | some n =>
        if mi.bytes.size < i.toNat + n.toNat then some ⟨s, f, [.trap]⟩
        else if n = 0 then some ⟨s, f, []⟩
        else some ⟨s, f, [aconst a i, v.toAdmin, store8 x,
          aconst a (i + 1), v.toAdmin, aconst a (n - 1), .plain (.memoryFill x)]⟩
      | none => none
    | _, _ => none
  | _ => none

def memCopy (x₁ x₂ : MemIdx) : List Val → Option (Config H)
  | [v₁, v₂, v₃] =>
    match addrOf? v₁, addrOf? v₂, addrOf? v₃, s.mem? f x₁, s.mem? f x₂ with
    | some ⟨a₁, i₁⟩, some ⟨a₂, i₂⟩, some ⟨a', n⟩, some (_, mi₁), some (_, mi₂) =>
      if mi₁.bytes.size < i₁.toNat + n.toNat ∨ mi₂.bytes.size < i₂.toNat + n.toNat then
        some ⟨s, f, [.trap]⟩
      else if n = 0 then some ⟨s, f, []⟩
      else if i₁.toNat ≤ i₂.toNat then
        some ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, load8u x₂, store8 x₁,
          aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1),
          .plain (.memoryCopy x₁ x₂)]⟩
      else
        some ⟨s, f, [aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1),
          aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1), load8u x₂, store8 x₁,
          aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1), .plain (.memoryCopy x₁ x₂)]⟩
    | _, _, _, _, _ => none
  | _ => none

def memInit (x : MemIdx) (y : DataIdx) : List Val → Option (Config H)
  | [v₁, v₂, v₃] =>
    match addrOf? v₁, i32Of? v₂, i32Of? v₃, s.mem? f x, s.data? f y with
    | some ⟨a, i⟩, some j, some n, some (_, mi), some (_, di) =>
      if mi.bytes.size < i.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat then
        some ⟨s, f, [.trap]⟩
      else if n = 0 then some ⟨s, f, []⟩
      else
        match di.bytes.data[j.toNat]? with
        | some byte => some ⟨s, f, [aconst a i, constI32 (BitVec.ofNat 32 byte.toNat), store8 x,
            aconst a (i + 1), constI32 (j + 1), constI32 (n - 1), .plain (.memoryInit x y)]⟩
        | none => none
    | _, _, _, _, _ => none
  | _ => none

def dataDrop (y : DataIdx) : List Val → Option (Config H)
  | [] =>
    match s.data? f y with
    | some (da, _) => some ⟨s.setData da ByteArray.empty, f, []⟩
    | none => none
  | _ => none

end Instrs

/-- One memory-family step on exactly the consumed arguments. -/
def stepArgs (o : GrowOracle) (s : Store H) (f : Frame) (args : List Val) (e : Admin) :
    Option (Config H) :=
  match e with
  | .plain (.intLoad t none x arg) => loadInt s f t x arg args
  | .plain (.intLoad t (some (sz, sx)) x arg) => loadPack s f t sz sx x arg args
  | .plain (.floatLoad t x arg) => loadFloat s f t x arg args
  | .plain (.vecLoad op x arg) => vecLoad s f op x arg args
  | .plain (.vecLoadLane sz x arg j) => vecLoadLane s f sz x arg j args
  | .plain (.intStore t none x arg) => storeInt s f t x arg args
  | .plain (.intStore t (some sz) x arg) => storePack s f t sz x arg args
  | .plain (.floatStore t x arg) => storeFloat s f t x arg args
  | .plain (.vecStore x arg) => vecStore s f x arg args
  | .plain (.vecStoreLane sz x arg j) => vecStoreLane s f sz x arg j args
  | .plain (.memorySize x) => memSize s f x args
  | .plain (.memoryGrow x) => memGrow s f o x args
  | .plain (.memoryFill x) => memFill s f x args
  | .plain (.memoryCopy x₁ x₂) => memCopy s f x₁ x₂ args
  | .plain (.memoryInit x y) => memInit s f x y args
  | .plain (.dataDrop y) => dataDrop s f y args
  | _ => none

/-! ## Soundness on exact arguments -/

set_option hygiene false in
/-- Turn decoded values into equations and substitute them. -/
macro "mem_decode" : tactic => `(tactic| (
  repeat (first
    | (obtain rfl := addrOf?_eq_some ‹addrOf? _ = some _›; simp only [addrOf?_aconst] at *)
    | (obtain rfl := intOf?_eq_some ‹intOf? _ _ = some _›; simp only [intOf?_self] at *)
    | (obtain rfl := i32Of?_eq_some ‹i32Of? _ = some _›; simp only [i32Of?_i32] at *)
    | (obtain rfl := floatOf?_eq_some ‹floatOf? _ _ = some _›; simp only [floatOf?_self] at *)
    | (obtain rfl := vecOf?_eq_some ‹vecOf? _ = some _›; simp only [vecOf?_vec] at *))))

/-- Split a per-instruction step and substitute its outcome. -/
macro "mem_split" h:ident : tactic => `(tactic| (
  repeat' split at $h:ident
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at $h:ident)
  all_goals (try contradiction)
  all_goals (mem_decode; subst $h:ident)))

variable {P : Profile} {s : Store H} {f : Frame} {args : List Val} {c : Config H}

theorem loadInt_sound {t x arg} (h : loadInt s f t x arg args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.intLoad t none x arg)]⟩ c := by
  unfold loadInt at h; mem_split h
  · exact .loadIntVal ‹_› ‹_›
  · exact .loadIntOob ‹_› (load_none ‹_›)

theorem loadPack_sound {t sz sx x arg} (h : loadPack s f t sz sx x arg args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.intLoad t (some (sz, sx)) x arg)]⟩ c := by
  unfold loadPack at h; mem_split h
  · exact .loadPackVal ‹_› ‹_›
  · exact .loadPackOob ‹_› (load_none ‹_›)

theorem loadFloat_sound {t x arg} (h : loadFloat s f t x arg args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.floatLoad t x arg)]⟩ c := by
  unfold loadFloat at h; mem_split h
  · exact .loadFloatVal ‹_› ‹_›
  · exact .loadFloatOob ‹_› (load_none ‹_›)

theorem vecLoad_sound {op x arg} (h : vecLoad s f op x arg args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.vecLoad op x arg)]⟩ c := by
  unfold vecLoad at h; mem_split h
  · exact .vecLoadVal ‹_› ‹_›
  · exact .vecLoadOob ‹_› (load_none ‹_›)

theorem vecLoadLane_sound {sz x arg j} (h : vecLoadLane s f sz x arg j args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.vecLoadLane sz x arg j)]⟩ c := by
  unfold vecLoadLane at h; mem_split h
  · exact .vecLoadLaneVal ‹_› ‹_›
  · exact .vecLoadLaneOob ‹_› (load_none ‹_›)

theorem storeInt_sound {t x arg} (h : storeInt s f t x arg args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.intStore t none x arg)]⟩ c := by
  unfold storeInt at h; mem_split h
  · exact .storeIntVal ‹_› ‹_›
  · exact .storeIntOob ‹_› (store_none ‹_›)

theorem storePack_sound {t sz x arg} (h : storePack s f t sz x arg args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.intStore t (some sz) x arg)]⟩ c := by
  unfold storePack at h; mem_split h
  · exact .storePackVal ‹_› ‹_›
  · exact .storePackOob ‹_› (store_none ‹_›)

theorem storeFloat_sound {t x arg} (h : storeFloat s f t x arg args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.floatStore t x arg)]⟩ c := by
  unfold storeFloat at h; mem_split h
  · exact .storeFloatVal ‹_› ‹_›
  · exact .storeFloatOob ‹_› (store_none ‹_›)

theorem vecStore_sound {x arg} (h : vecStore s f x arg args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.vecStore x arg)]⟩ c := by
  unfold vecStore at h; mem_split h
  · exact .vecStoreVal ‹_› ‹_›
  · exact .vecStoreOob ‹_› (store_none ‹_›)

theorem vecStoreLane_sound {sz x arg j} (h : vecStoreLane s f sz x arg j args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.vecStoreLane sz x arg j)]⟩ c := by
  unfold vecStoreLane at h; mem_split h
  · exact .vecStoreLaneVal ‹_› ‹_›
  · exact .vecStoreLaneOob ‹_› (store_none ‹_›)

theorem memSize_sound {x} (h : memSize s f x args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.memorySize x)]⟩ c := by
  unfold memSize at h; mem_split h
  exact .size ‹_›

theorem dataDrop_sound {y} (h : dataDrop s f y args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.dataDrop y)]⟩ c := by
  unfold dataDrop at h; mem_split h
  exact .dataDrop ‹_›

theorem memGrow_sound {o : GrowOracle} {x} (h : memGrow s f o x args = some c) :
    MemoryStep (profile o) ⟨s, f, vals args ++ [.plain (.memoryGrow x)]⟩ c := by
  unfold memGrow at h; mem_split h
  · exact .growFail ‹_› (.inl ‹_›)
  · refine .growSucceed ‹_› ‹_› ?_
    have hn := ‹¬ (profile o).growMayFail _ _ _ _›
    simp only [profile, growMayFail_det, Bool.not_eq_true] at hn
    simpa [profile] using hn
  · exact .growFail ‹_› (.inr ‹_›)

theorem memFill_sound {x} (h : memFill s f x args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.memoryFill x)]⟩ c := by
  unfold memFill at h; mem_split h
  · exact .fillOob ‹_› ‹_›
  · subst_vars; exact .fillZero ‹_› (by simp only [Nat.not_lt] at *; omega)
  · exact .fillSucc ‹_› (by omega) ‹_›

theorem memCopy_sound {x₁ x₂} (h : memCopy s f x₁ x₂ args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.memoryCopy x₁ x₂)]⟩ c := by
  unfold memCopy at h; mem_split h
  · exact .copyOob ‹_› ‹_› ‹_›
  · subst_vars; exact .copyZero ‹_› ‹_› (by simp only [not_or, Nat.not_lt] at *; omega)
  · exact .copyLe ‹_› ‹_› (by omega) ‹_› ‹_›
  · exact .copyGt ‹_› ‹_› (by omega) ‹_› (by omega)

theorem memInit_sound {x y} (h : memInit s f x y args = some c) :
    MemoryStep P ⟨s, f, vals args ++ [.plain (.memoryInit x y)]⟩ c := by
  unfold memInit at h; mem_split h
  · exact .initOob ‹_› ‹_› ‹_›
  · subst_vars; exact .initZero ‹_› ‹_› (by simp only [not_or, Nat.not_lt] at *; omega)
  · exact .initSucc ‹_› ‹_› (by omega) ‹_› ‹_›

theorem stepArgs_sound {o : GrowOracle} {e : Admin} (h : stepArgs o s f args e = some c) :
    MemoryStep (profile o) ⟨s, f, vals args ++ [e]⟩ c := by
  unfold stepArgs at h
  split at h
  · exact loadInt_sound h
  · exact loadPack_sound h
  · exact loadFloat_sound h
  · exact vecLoad_sound h
  · exact vecLoadLane_sound h
  · exact storeInt_sound h
  · exact storePack_sound h
  · exact storeFloat_sound h
  · exact vecStore_sound h
  · exact vecStoreLane_sound h
  · exact memSize_sound h
  · exact memGrow_sound h
  · exact memFill_sound h
  · exact memCopy_sound h
  · exact memInit_sound h
  · exact dataDrop_sound h
  · cases h

/-! ## Completeness on exact arguments -/

theorem args_eq {args : List Val} {e : Admin} {L : List Admin} (h : vals args ++ [e] = L) :
    args = L.dropLast.filterMap Admin.val? ∧ L.getLast? = some e := by
  subst h
  refine ⟨?_, by simp⟩
  simp only [List.dropLast_concat, vals, List.filterMap_map]
  have : (Admin.val? ∘ Val.toAdmin) = some := funext fun v => Admin.val?_toAdmin v
  rw [this, List.filterMap_some]

theorem stepArgs_complete {o : GrowOracle} {e : Admin} {l : List Admin}
    (h : MemoryStep (profile o) ⟨s, f, l⟩ c) (hl : vals args ++ [e] = l) :
    arity e = some args.length ∧ stepArgs o s f args e = some c := by
  cases h <;> (obtain ⟨rfl, he⟩ := args_eq hl; simp at he; subst he; refine ⟨by simp [arity], ?_⟩)
  case growFail =>
    rename_i x a n ma mi hp hm
    rcases hp with hp | hp
    · have hp' : o .memory ma mi.pages n.toNat = true := hp
      simp [stepArgs, memGrow, hm, profile, hp']
    · by_cases hf : o .memory ma mi.pages n.toNat = true <;>
        simp [stepArgs, memGrow, hm, profile, hp, hf]
  case growSucceed =>
    rename_i hg hp hm
    have hp' : o .memory _ _ _ = false := hp
    simp [stepArgs, memGrow, hm, profile, hp', hg]
  all_goals (try simp [packExt, -List.getD_eq_getElem?_getD, stepArgs, loadInt, loadPack, loadFloat, vecLoad, vecLoadLane, storeInt,
    storePack, storeFloat, vecStore, vecStoreLane, memSize, memFill, memCopy, memInit,
    dataDrop, load_of_lt, store_of_lt, *])
  all_goals first
    | (cases ‹Signedness› <;> rfl)
    | (split_ifs <;> (try rfl) <;> (try omega) <;> simp_all)
    | (split <;> simp_all)

end Mem

/-- The memory-family head step: consume the top `k` values of `vs`. -/
def memoryStep? (o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match Mem.arity e with
  | some k =>
    if k ≤ vs.length then (Mem.stepArgs o s f (vs.drop (vs.length - k)) e).map (k, ·) else none
  | none => none

theorem memoryStep?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {k : Nat} {c : Config H} (h : memoryStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  unfold memoryStep? at h
  split at h
  · split at h
    · rename_i k' _ hk
      obtain ⟨c', hc', hkc⟩ := Option.map_eq_some_iff.mp h
      cases hkc
      exact ⟨hk, .memory (Mem.stepArgs_sound hc')⟩
    · cases h
  · cases h

theorem memoryStep?_complete {o : GrowOracle} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {c : Config H} (h : Head (profile o) s f args e c) (hf : famOf e = .memory)
    (hv : ∃ q, vs = q ++ args) : memoryStep? o s f vs e = some (args.length, c) := by
  have hr := h.fam_inv (by rw [hf]; decide)
  rw [hf] at hr
  obtain ⟨ha, hs⟩ := Mem.stepArgs_complete hr rfl
  obtain ⟨q, rfl⟩ := hv
  have hd : (q ++ args).drop ((q ++ args).length - args.length) = args := by
    rw [List.length_append, Nat.add_sub_cancel]
    exact List.drop_left
  unfold memoryStep?
  rw [ha]
  dsimp only
  rw [ite_eq_left (by simp), hd, hs]
  rfl

end Silmaril.Wasm.SingleThreaded.Exec
