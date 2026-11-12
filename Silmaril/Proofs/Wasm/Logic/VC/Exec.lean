module

public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.Wasm.Logic.Words.Defs

/-!
# Evaluation lemmas for verification conditions over symbolic stores

`global.get` and `global.set` evaluated through the index view `globalVal`/`setGlobalIdx`
(`Silmaril.Wasm.Logic.VC.Defs`), and the **frame rule for globals**: setting global `x` of an
instance with distinct global addresses leaves every other global `y ≠ x`, the functions and
the memories unchanged. With these, `wat_vc` evaluates simulator code whose state lives in
globals without knowing the store (only hypotheses `globalVal s m x = some v`).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec1 popV popInt localVal?)

variable {H : Type} {s : Store H} {f : Frame} {m : ModuleInst} {x y : Nat} {v : Val}

theorem global?_map_value (s : Store H) (f : Frame) (x : GlobalIdx) :
    (s.global? f x).map (·.2.value) = globalVal s f.module x.toNat := by
  simp only [Store.global?, globalVal]
  cases ha : f.module.globals[x.toNat]? with
  | none => rfl
  | some a => cases hb : s.globals[a]? <;> simp [hb]

theorem global?_isSome (s : Store H) (f : Frame) (x : GlobalIdx) :
    (s.global? f x).isSome = (globalVal s f.module x.toNat).isSome := by
  rw [← global?_map_value, Option.isSome_map]

/-- `global.get x` through `globalVal`. -/
theorem exec1_globalGet_idx (rs : List Val) (x : GlobalIdx) :
    exec1 s f rs (.globalGet x) = (globalVal s f.module x.toNat).map fun v => (s, f, v :: rs) := by
  rw [← global?_map_value, Option.map_map]
  rfl

theorem setGlobal_of_global? {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : s.global? f x = some (a, g)) (v : Val) :
    s.setGlobal a v = setGlobalIdx s f.module x.toNat v := by
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨b, hb, g', -, hab⟩ := h
  simp only [Prod.mk.injEq] at hab
  obtain ⟨rfl, -⟩ := hab
  simp [setGlobalIdx, hb]

/-- `global.set x` through `setGlobalIdx`. -/
theorem exec1_globalSet_idx (rs : List Val) (x : GlobalIdx) :
    exec1 s f rs (.globalSet x) = (popV rs).bind fun (v, rs') =>
      (globalVal s f.module x.toNat).map fun _ => (setGlobalIdx s f.module x.toNat v, f, rs') := by
  simp only [exec1]
  cases popV rs with
  | none => rfl
  | some p =>
    obtain ⟨v, rs'⟩ := p
    simp only [Option.bind_some]
    cases hg : s.global? f x with
    | none =>
      have := global?_isSome s f x
      rw [hg] at this
      cases hv : globalVal s f.module x.toNat
      · rfl
      · rw [hv] at this; cases this
    | some p =>
      obtain ⟨a, g⟩ := p
      have := global?_map_value s f x
      rw [hg] at this
      rw [← this]
      simp [setGlobal_of_global? hg]

/-- `global.set x` through `setGlobalIdx`, the existence of the global as a condition (so that a
hypothesis `(globalVal s m x).isSome` suffices). -/
theorem exec1_globalSet_if (rs : List Val) (x : GlobalIdx) :
    exec1 s f rs (.globalSet x) = (popV rs).bind fun (v, rs') =>
      if (globalVal s f.module x.toNat).isSome then
        some (setGlobalIdx s f.module x.toNat v, f, rs') else none := by
  rw [exec1_globalSet_idx]
  cases popV rs with
  | none => rfl
  | some p => cases globalVal s f.module x.toNat <;> rfl

/-! ## The frame rule for globals -/

@[simp] theorem globalVal_setGlobalIdx_self :
    globalVal (setGlobalIdx s m x v) m x = (globalVal s m x).map fun _ => v := by
  unfold globalVal setGlobalIdx
  cases ha : m.globals[x]? with
  | none => rfl
  | some a =>
    simp only [Option.bind_some, Store.setGlobal, List.getElem?_modify, ↓reduceIte,
      Option.map_map]
    cases s.globals[a]? <;> rfl

theorem globalVal_setGlobalIdx_ne (hnd : m.globals.Nodup) (h : y ≠ x) :
    globalVal (setGlobalIdx s m x v) m y = globalVal s m y := by
  unfold globalVal setGlobalIdx
  cases ha : m.globals[x]? with
  | none => rfl
  | some a =>
    cases hb : m.globals[y]? with
    | none => rfl
    | some b =>
      have hab : a ≠ b := by
        rintro rfl
        have hy : y < m.globals.length := (List.getElem?_eq_some_iff.mp hb).1
        exact h (hnd.eq_of_getElem?_eq hy (hb.trans ha.symm))
      simp only [Option.bind_some, Store.setGlobal, List.getElem?_modify, hab, ↓reduceIte]
      cases s.globals[b]? <;> rfl

@[simp] theorem globalVal_setGlobalIdx_isSome :
    (globalVal (setGlobalIdx s m x v) m y).isSome = (globalVal s m y).isSome := by
  unfold globalVal setGlobalIdx
  cases ha : m.globals[x]? with
  | none => rfl
  | some a =>
    cases hb : m.globals[y]? with
    | none => rfl
    | some b =>
      simp only [Option.bind_some, Store.setGlobal, List.getElem?_modify]
      by_cases hab : a = b
      · subst hab; simp only [↓reduceIte]; cases s.globals[a]? <;> rfl
      · simp only [hab, ↓reduceIte]
        cases s.globals[b]? <;> rfl

@[simp] theorem setGlobalIdx_funcs : (setGlobalIdx s m x v).funcs = s.funcs := by
  unfold setGlobalIdx; split <;> rfl

@[simp] theorem setGlobalIdx_mems : (setGlobalIdx s m x v).mems = s.mems := by
  unfold setGlobalIdx; split <;> rfl

@[simp] theorem setGlobalIdx_globals_length :
    (setGlobalIdx s m x v).globals.length = s.globals.length := by
  unfold setGlobalIdx; split <;> simp [Store.setGlobal]

@[simp] theorem mem?_setGlobalIdx {f : Frame} {z : MemIdx} :
    (setGlobalIdx s m x v).mem? f z = s.mem? f z := by
  simp only [Store.mem?, setGlobalIdx_mems]

@[simp] theorem globalVal_setMem {a : Nat} {mi : MemInst} :
    globalVal (s.setMem a mi) m x = globalVal s m x := rfl

/-! ## `exec1`, one equation per instruction form

`wat_vc` rewrites with these instead of unfolding `exec1`, so `global.get`/`global.set` go
through `globalVal`/`setGlobalIdx` (and the instruction forms `exec1` does not evaluate stay
stuck, i.e. unprovable, as before). -/

section ExecEqs

variable (s : Store H) (f : Frame) (rs : List Val)

theorem vc_exec1_nop : exec1 s f rs .nop = some (s, f, rs) := rfl
theorem vc_exec1_drop : exec1 s f rs .drop = (popV rs).map fun (_, rs') => (s, f, rs') := rfl
theorem vc_exec1_intConst (t : IntType) (c : BitVec t.width) :
    exec1 s f rs (.intConst t c) = some (s, f, .num ⟨.int t, c⟩ :: rs) := rfl
theorem vc_exec1_i32Const (c : BitVec 32) :
    exec1 s f rs (.intConst .i32 c) = some (s, f, .num ⟨.int .i32, c⟩ :: rs) := rfl
theorem vc_exec1_i64Const (c : BitVec 64) :
    exec1 s f rs (.intConst .i64 c) = some (s, f, .num ⟨.int .i64, c⟩ :: rs) := rfl
theorem vc_exec1_localGet (x : LocalIdx) :
    exec1 s f rs (.localGet x) = (localVal? f x).map fun v => (s, f, v :: rs) := rfl
theorem vc_exec1_localSet (x : LocalIdx) :
    exec1 s f rs (.localSet x) = (popV rs).bind fun (v, rs') =>
      if x.toNat < f.locals.length then some (s, f.setLocal x v, rs') else none := rfl
theorem vc_exec1_localTee (x : LocalIdx) :
    exec1 s f rs (.localTee x) = (popV rs).bind fun (v, rs') =>
      if x.toNat < f.locals.length then some (s, f.setLocal x v, v :: rs') else none := rfl
theorem vc_exec1_intUnOp (t : IntType) (op : IntUnOp) :
    exec1 s f rs (.intUnOp t op) =
      (popInt t rs).map fun (x, rs₁) => (s, f, .num ⟨.int t, intUnOp t op x⟩ :: rs₁) := rfl
theorem vc_exec1_intBinOp (t : IntType) (op : IntBinOp) :
    exec1 s f rs (.intBinOp t op) =
      (popInt t rs).bind fun (y, rs₁) => (popInt t rs₁).bind fun (x, rs₂) =>
        match intBinOp t op x y with
        | .ok z => some (s, f, .num ⟨.int t, z⟩ :: rs₂)
        | .error _ => none := rfl
theorem vc_exec1_intTestOp (t : IntType) (op : IntTestOp) :
    exec1 s f rs (.intTestOp t op) =
      (popInt t rs).map fun (x, rs₁) => (s, f, Val.i32 (intTestOp t op x) :: rs₁) := rfl
theorem vc_exec1_intRelOp (t : IntType) (op : IntRelOp) :
    exec1 s f rs (.intRelOp t op) =
      (popInt t rs).bind fun (y, rs₁) => (popInt t rs₁).map fun (x, rs₂) =>
        (s, f, Val.i32 (intRelOp t op x y) :: rs₂) := rfl
theorem vc_exec1_intLoad (t : IntType) (x : MemIdx) (arg : MemArg) :
    exec1 s f rs (.intLoad t none x arg) =
      (popInt .i32 rs).bind fun (a, rs₁) => (s.mem? f x).bind fun (_, mi) =>
        (Memory.load mi.bytes (effAddr a.toNat arg) (t.width / 8)).map fun c =>
          (s, f, .num ⟨.int t, c.setWidth t.width⟩ :: rs₁) := rfl
theorem vc_exec1_intLoadPack (t : IntType) (sz : PackSize) (sx : Signedness) (x : MemIdx)
    (arg : MemArg) :
    exec1 s f rs (.intLoad t (some (sz, sx)) x arg) =
      (popInt .i32 rs).bind fun (a, rs₁) => (s.mem? f x).bind fun (_, mi) =>
        (Memory.load mi.bytes (effAddr a.toNat arg) (sz.width / 8)).map fun c =>
          (s, f, .num ⟨.int t, match sx with
            | .signed => c.signExtend t.width
            | .unsigned => c.setWidth t.width⟩ :: rs₁) := rfl
theorem vc_exec1_intStore (t : IntType) (x : MemIdx) (arg : MemArg) :
    exec1 s f rs (.intStore t none x arg) =
      (popInt t rs).bind fun (c, rs₁) => (popInt .i32 rs₁).bind fun (a, rs₂) =>
        (s.mem? f x).bind fun (ma, mi) =>
        (Memory.store mi.bytes (effAddr a.toNat arg) (count := t.width / 8)
          (c.setWidth _)).map fun b => (s.setMem ma { mi with bytes := b }, f, rs₂) := rfl
theorem vc_exec1_intStorePack (t : IntType) (sz : PackSize) (x : MemIdx) (arg : MemArg) :
    exec1 s f rs (.intStore t (some sz) x arg) =
      (popInt t rs).bind fun (c, rs₁) => (popInt .i32 rs₁).bind fun (a, rs₂) =>
        (s.mem? f x).bind fun (ma, mi) =>
        (Memory.store mi.bytes (effAddr a.toNat arg) (count := sz.width / 8)
          (c.setWidth _)).map fun b => (s.setMem ma { mi with bytes := b }, f, rs₂) := rfl

end ExecEqs

/-! ## Integer operations at `BitVec 32` and `BitVec 64`

The rest of the operations of `Silmaril.Wasm.Numerics.intBinOp`/`intUnOp` (the common ones are
in `Silmaril.Wasm.Logic.Arith.Thms`), typed at the concrete widths so that `simp` can match the
results in later instructions. -/

section Ops

variable (x y : BitVec 32) (u v : BitVec 64)

@[simp] theorem intBinOp_i32_shrS : intBinOp .i32 (.shr .signed) x y = .ok (x.sshiftRight (y.toNat % 32)) := rfl
@[simp] theorem intBinOp_i64_shrS : intBinOp .i64 (.shr .signed) u v = .ok (u.sshiftRight (v.toNat % 64)) := rfl
@[simp] theorem intBinOp_i32_divU :
    intBinOp .i32 (.div .unsigned) x y = if y = 0 then .error .divideByZero else .ok (x / y) := rfl
@[simp] theorem intBinOp_i64_divU :
    intBinOp .i64 (.div .unsigned) u v = if v = 0 then .error .divideByZero else .ok (u / v) := rfl
@[simp] theorem intBinOp_i32_remU :
    intBinOp .i32 (.rem .unsigned) x y = if y = 0 then .error .divideByZero else .ok (x % y) := rfl
@[simp] theorem intBinOp_i64_remU :
    intBinOp .i64 (.rem .unsigned) u v = if v = 0 then .error .divideByZero else .ok (u % v) := rfl
@[simp] theorem intBinOp_i32_remS :
    intBinOp .i32 (.rem .signed) x y = if y = 0 then .error .divideByZero else .ok (x.srem y) := rfl
@[simp] theorem intBinOp_i64_remS :
    intBinOp .i64 (.rem .signed) u v = if v = 0 then .error .divideByZero else .ok (u.srem v) := rfl
@[simp] theorem intBinOp_i32_divS : intBinOp .i32 (.div .signed) x y =
    if y = 0 then .error .divideByZero else if x = BitVec.intMin 32 ∧ y = -1 then .error .overflow
    else .ok (x.sdiv y) := rfl
@[simp] theorem intBinOp_i64_divS : intBinOp .i64 (.div .signed) u v =
    if v = 0 then .error .divideByZero else if u = BitVec.intMin 64 ∧ v = -1 then .error .overflow
    else .ok (u.sdiv v) := rfl

@[simp] theorem intUnOp_i32_clz : intUnOp .i32 .clz x = x.clz := rfl
@[simp] theorem intUnOp_i64_clz : intUnOp .i64 .clz u = u.clz := rfl
@[simp] theorem intUnOp_i32_ctz : intUnOp .i32 .ctz x = x.ctz := rfl
@[simp] theorem intUnOp_i64_ctz : intUnOp .i64 .ctz u = u.ctz := rfl
@[simp] theorem intUnOp_i32_popcnt : intUnOp .i32 .popcnt x = x.cpop := rfl
@[simp] theorem intUnOp_i64_popcnt : intUnOp .i64 .popcnt u = u.cpop := rfl
@[simp] theorem intUnOp_i32_extend (sz : PackSize) :
    intUnOp .i32 (.extend sz) x = (x.setWidth sz.width).signExtend 32 := rfl
@[simp] theorem intUnOp_i64_extend (sz : PackSize) :
    intUnOp .i64 (.extend sz) u = (u.setWidth sz.width).signExtend 64 := rfl

@[simp] theorem and_ones64 : u &&& 18446744073709551615#64 = u := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
@[simp] theorem ones64_and : 18446744073709551615#64 &&& u = u := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
@[simp] theorem and_ones32 : x &&& 4294967295#32 = x := by
  rw [show (4294967295#32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

@[simp] theorem wrap64_eq : wrap64 u = u.setWidth 32 := rfl
@[simp] theorem extendU32_eq : extendU32 x = x.setWidth 64 := rfl
@[simp] theorem extendS32_eq : extendS32 x = x.signExtend 64 := rfl

/-- `i32.wrap_i64` of `i64.extend_i32_u`/`_s` is the identity. -/
@[simp] theorem wrap64_extendU32 : wrap64 (extendU32 x) = x := by
  simp only [wrap64, extendU32]; bv_omega
@[simp] theorem wrap64_extendS32 : wrap64 (extendS32 x) = x := by
  simp only [wrap64, extendS32]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi]; omega

end Ops

/-! ## Memory

Loads and stores of a memory known through `Silmaril.Wasm.Logic.Words.MemAt` (memory `0` of the
instance is the store's memory `ma` holding the bytes `B`), with the results in the terms of
`Silmaril.Wasm.Logic.Memory` (`leNat`, `bytesAt`, `storeLE`): `mem?_memAt`, `load_ite`,
`store_ite`, `memAt_setMem`, `size_storeLE`, `load_storeLE_same`, and the memory unchanged by
`setGlobalIdx` (`memAt_setGlobalIdx`). -/

section Memory

open Silmaril.Wasm.Logic.Core (leNat bytesAt storeLE)
open Silmaril.Wasm.Logic.Words (MemAt)

variable {ma : Nat} {mt : MemoryType} {B : ByteArray}

theorem mem?_memAt (h : MemAt s m ma mt B) (ls : List (Option Val)) :
    s.mem? ⟨ls, m⟩ ⟨0⟩ = some (ma, ⟨mt, B⟩) := by
  simp [Store.mem?, Idx.toNat, h.1, h.2]

theorem load_ite (B : ByteArray) (a n : Nat) : Memory.load B a n =
    if a + n ≤ B.size then some (BitVec.ofNat (8 * n) (leNat (bytesAt B ⟨a, n⟩))) else none := by
  split
  · exact Silmaril.Wasm.Logic.Core.load_eq ‹_›
  · exact Silmaril.Wasm.Logic.Core.load_eq_none (by omega)

theorem store_ite (B : ByteArray) (a n : Nat) (w : BitVec (8 * n)) :
    Memory.store B a w = if a + n ≤ B.size then some (storeLE B a n w.toNat) else none := by
  split
  · exact Silmaril.Wasm.Logic.Core.store_eq w ‹_›
  · simp only [Memory.store, Memory.writeBytes, Memory.encodeLE_size]
    rw [ite_eq_right (by omega)]

theorem size_storeLE {a n : Nat} (v : Nat) (h : a + n ≤ B.size) :
    (storeLE B a n v).size = B.size := by
  have hw : Memory.writeBytes B a (Memory.encodeLE n v) = some (storeLE B a n v) := by
    simp only [Memory.writeBytes, storeLE, Memory.encodeLE_size, h, ↓reduceIte]
  exact Memory.writeBytes_size B _ _ a hw

theorem load_storeLE_same {a n : Nat} (w : BitVec (8 * n)) (h : a + n ≤ B.size) :
    Memory.load (storeLE B a n w.toNat) a n = some w :=
  Silmaril.Wasm.Logic.Core.load_store_same (Silmaril.Wasm.Logic.Core.store_eq w h)

theorem memAt_setMem (h : MemAt s m ma mt B) (B' : ByteArray) :
    MemAt (s.setMem ma ⟨mt, B'⟩) m ma mt B' := by
  refine ⟨h.1, ?_⟩
  have hlt : ma < s.mems.length := by
    by_contra hc
    have := h.2
    rw [List.getElem?_eq_none (by omega)] at this
    cases this
  simp [Store.setMem, hlt]

theorem memAt_setGlobalIdx (h : MemAt s m ma mt B) (m' : ModuleInst) (x : Nat) (v : Val) :
    MemAt (setGlobalIdx s m' x v) m ma mt B :=
  ⟨h.1, by rw [setGlobalIdx_mems]; exact h.2⟩

end Memory

end Silmaril.Wasm.Logic.VC
