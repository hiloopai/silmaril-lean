module

public import Silmaril.Wasm.Jco.Real.Step.Defs
public import Silmaril.Wasm.Jco.Basic.Thms

/-!
# The list memory of `CoreInst` against Core 3.0 byte arrays

`CoreInst` memories are lists of bytes (`Mem`, `Mem.read`, `Mem.write`, little-endian `leNat`,
`leBytes`); Core 3.0 memories are `ByteArray`s (`Memory.readBytes`, `writeBytes`, `decodeLE`,
`encodeLE`). This module relates them, and gives the inversion lemmas of `RM` used by the
agreement proofs.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Inversion of `RM` -/

theorem ok_bind {σ α β : Type} {m : RM σ α} {k : α → RM σ β} {s s'' : σ} {b : β}
    (h : (m >>= k) s (.ok b s'')) : ∃ a s', m s (.ok a s') ∧ k a s' (.ok b s'') := by
  rcases (RM.bind_apply m k s _).mp h with h | ⟨_, h⟩
  · exact h
  · cases h

theorem ok_pure {σ α : Type} {a b : α} {s s' : σ} (h : (pure a : RM σ α) s (.ok b s')) :
    b = a ∧ s' = s := by
  have h' : Out.ok b s' = Out.ok a s := (RM.pure_apply a s _).mp h
  cases h'
  exact ⟨rfl, rfl⟩

theorem ok_fail {σ α : Type} {b : α} {s s' : σ} (h : (RM.fail : RM σ α) s (.ok b s')) : False := by
  cases h

theorem ok_ofOption {σ α : Type} {x : Option α} {b : α} {s s' : σ}
    (h : (RM.ofOption x : RM σ α) s (.ok b s')) : x = some b ∧ s' = s := by
  cases x with
  | none => cases h
  | some a =>
    obtain ⟨rfl, rfl⟩ := ok_pure h
    exact ⟨rfl, rfl⟩

theorem ok_load {M : CoreInst} {a n : Nat} {bs : List UInt8} {s s' : M.St}
    (h : M.load a n s (.ok bs s')) : (M.mem s).read a n = some bs ∧ s' = s := by
  obtain ⟨s₀, s₁, hg, hr⟩ := ok_bind h
  have hg' : Out.ok s₀ s₁ = Out.ok s s := hg
  cases hg'
  exact ok_ofOption hr

theorem ok_store {M : CoreInst} {a : Nat} {bs : List UInt8} {u : Unit} {s s' : M.St}
    (h : M.store a bs s (.ok u s')) : ∃ m', (M.mem s).write a bs = some m' ∧ s' = M.setMem s m' := by
  obtain ⟨s₀, s₁, hg, hr⟩ := ok_bind h
  have hg' : Out.ok s₀ s₁ = Out.ok s s := hg
  cases hg'
  obtain ⟨m', s₃, hw, hs⟩ := ok_bind hr
  obtain ⟨hw', rfl⟩ := ok_ofOption hw
  have hs' : Out.ok u s' = Out.ok () (M.setMem _ m') := hs
  cases hs'
  exact ⟨m', hw', rfl⟩

/-! ## Bytes -/

theorem leNat_foldr : ∀ bs : List UInt8, leNat bs = bs.foldr (fun b r => b.toNat + 256 * r) 0
  | [] => rfl
  | b :: bs => by rw [leNat, leNat_foldr bs]; rfl

theorem decodeLE_eq (b : ByteArray) : Memory.decodeLE b = leNat b.data.toList := by
  rw [Memory.decodeLE, leNat_foldr, Array.foldr_toList]

theorem extract_toList (b : ByteArray) (p n : Nat) :
    (b.extract p (p + n)).data.toList = (b.data.toList.drop p).take n := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract]

theorem size_toList (b : ByteArray) : b.data.toList.length = b.size := Array.length_toList

theorem extract_toList' (b : ByteArray) (i j : Nat) :
    (b.extract i j).data.toList = (b.data.toList.drop i).take (j - i) := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract]

/-- A read of the list memory is a Core `readBytes`. -/
theorem read_readBytes (b : ByteArray) (p n : Nat) :
    Mem.read b.data.toList p n = (Memory.readBytes b p n).map (·.data.toList) := by
  unfold Mem.read Memory.readBytes
  rw [size_toList]
  split
  · simp
  · rfl

/-- A successful read of `realInst`'s memory is a successful Core `load` of the same bytes. -/
theorem memBytes_load {ma p n : Nat} {s : Store H} {bs : List UInt8} (hn : 0 < n)
    (h : (memBytes ma s).read p n = some bs) :
    ∃ m, s.mems[ma]? = some m ∧ Memory.load m.bytes p n = some (BitVec.ofNat (8 * n) (leNat bs)) := by
  unfold memBytes at h
  split at h
  · rename_i m hm
    refine ⟨m, hm, ?_⟩
    rw [read_readBytes] at h
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Memory.load, he, decodeLE_eq]
  · simp [Mem.read] at h
    omega

theorem encodeLE_toList : ∀ (n x : Nat), (Memory.encodeLE n x).data.toList = leBytes n x
  | 0, _ => rfl
  | n + 1, x => by
    have hb : (x % 256).toUInt8 = UInt8.ofNat x := by
      apply UInt8.toNat_inj.mp; simp [Nat.toUInt8]
    simp [Memory.encodeLE, leBytes, encodeLE_toList n (x / 256), hb]

theorem leBytes_mod : ∀ (n x : Nat), leBytes n (x % 256 ^ n) = leBytes n x
  | 0, _ => rfl
  | n + 1, x => by
    have h1 : x % 256 ^ (n + 1) % 256 = x % 256 := by
      rw [Nat.pow_succ', Nat.mod_mul_right_mod]
    have h2 : x % 256 ^ (n + 1) / 256 = x / 256 % 256 ^ n := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    simp only [leBytes, h1, h2, leBytes_mod n (x / 256)]

theorem length_leBytes : ∀ (n x : Nat), (leBytes n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp [leBytes, length_leBytes n]

/-- A successful write of `realInst`'s memory is a successful Core `store`, and the new state is
the Core store with the written memory. -/
theorem memBytes_store {ma p n : Nat} {s : Store H} {m' : List UInt8} {x : Nat} (hn : 0 < n)
    (h : (memBytes ma s).write p (leBytes n x) = some m') :
    ∃ m b, s.mems[ma]? = some m ∧
      Memory.store m.bytes p (BitVec.ofNat (8 * n) x) = some b ∧
      putBytes ma s m' = s.setMem ma { m with bytes := b } := by
  unfold memBytes at h
  split at h
  · rename_i m hm
    refine ⟨m, ⟨m'.toArray⟩, hm, ?_, by simp [putBytes, hm]⟩
    unfold Mem.write at h
    rw [length_leBytes, size_toList] at h
    split at h
    · rename_i hle
      cases h
      have hx : (BitVec.ofNat (8 * n) x).toNat = x % 256 ^ n := by
        rw [BitVec.toNat_ofNat, Nat.pow_mul]
      unfold Memory.store
      rw [hx, (Memory.writeBytes_eq_some_iff _ _ _ _).mpr]
      refine ⟨by simp [hle], ?_⟩
      apply ByteArray.ext
      apply Array.ext'
      simp only [ByteArray.data_append, Array.toList_append, extract_toList']
      simp [encodeLE_toList, leBytes_mod]
    · cases h
  · simp [Mem.write, length_leBytes] at h
    omega

end Silmaril.Proofs.Wasm.Jco.Real
