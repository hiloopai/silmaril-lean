module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Runtime
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Lime1 → Core step simulation: bulk memory

Lime1 performs `memory.fill`/`memory.copy` atomically (`Memory.fill`/`Memory.copy`);
Core iterates byte by byte (`fill-succ` emits a `store8`, `copy-le`/`copy-gt` a
`load8u`+`store8`, each followed by the recursive instruction with count `n - 1`).
We run the Core iteration by induction on the count and show, pointwise on the
byte array, that the final memory is the one computed by Lime1 (memmove semantics
for overlapping copies: `copy-gt` copies backwards).

The Core profile is written `Profile.spec` (= `coreProfile`, which lives in
`ToCore.Execution`, downstream of this file).
-/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution.ToCore

local notation "CStep" => Silmaril.Wasm.Execution.Core.Step
  Silmaril.Wasm.Numerics.Profile.spec
local notation "CSteps" => Silmaril.Wasm.Execution.Core.Steps
  Silmaril.Wasm.Numerics.Profile.spec

/-! ## Byte-level lemmas -/

section Bytes

open Silmaril.Wasm.Execution

theorem bulk_writeBytes_get {M B A : ByteArray} {st : Nat}
    (h : Memory.writeBytes M st B = some A) (j : Nat) :
    A.data[j]? = if st ≤ j ∧ j < st + B.size then B.data[j - st]? else M.data[j]? := by
  obtain ⟨hb, rfl⟩ := (Memory.writeBytes_eq_some_iff M B A st).mp h
  simp only [ByteArray.data_append, ByteArray.data_extract, Array.getElem?_append,
    Array.size_extract, Array.getElem?_extract, ByteArray.size_data, Array.size_append]
  have e1 : min st M.size - 0 = st := by omega
  have e2 : min M.size M.size - (st + B.size) = M.size - (st + B.size) := by omega
  simp only [e1, e2, Nat.zero_add]
  split_ifs <;> first | rfl | omega | (congr 1; omega) | (rw [Array.getElem?_eq_none (by simp only [ByteArray.size_data]; omega)])

theorem bulk_writeBytes_isSome {M B : ByteArray} {st : Nat} :
    (Memory.writeBytes M st B).isSome ↔ st + B.size ≤ M.size := by
  unfold Memory.writeBytes; split <;> simp_all

theorem bulk_fill_get {M A : ByteArray} {d n : Nat} {b : UInt8}
    (h : Memory.fill M d b n = some A) (j : Nat) :
    A.data[j]? = if d ≤ j ∧ j < d + n then some b else M.data[j]? := by
  rw [bulk_writeBytes_get h j]
  have hs : (⟨Array.replicate n b⟩ : ByteArray).size = n := Array.size_replicate
  simp only [hs]
  split_ifs with hj
  · change (Array.replicate n b)[j - d]? = _
    rw [Array.getElem?_replicate, ite_eq_left (by omega)]
  · rfl

theorem bulk_fill_none {M : ByteArray} {d n : Nat} {b : UInt8} :
    Memory.fill M d b n = none ↔ M.size < d + n := by
  have hs : (⟨Array.replicate n b⟩ : ByteArray).size = n := Array.size_replicate
  unfold Memory.fill Memory.writeBytes
  rw [hs]; split <;> simp <;> omega

theorem bulk_copy_get {M A : ByteArray} {d s n : Nat}
    (h : Memory.copy M d s n = some A) (j : Nat) :
    A.data[j]? = if d ≤ j ∧ j < d + n then M.data[s + (j - d)]? else M.data[j]? := by
  unfold Memory.copy at h
  cases hr : Memory.readBytes M s n with
  | none => simp [hr] at h
  | some B =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨hb, rfl⟩ := (Memory.readBytes_eq_some_iff M B s n).mp hr
    rw [bulk_writeBytes_get h j]
    have hs : (M.extract s (s + n)).size = n := by simp only [ByteArray.size_extract]; omega
    simp only [hs]
    split_ifs with hj
    · rw [ByteArray.data_extract, Array.getElem?_extract, ite_eq_left (by simp only [ByteArray.size_data]; omega)]
    · rfl

theorem bulk_copy_none {M : ByteArray} {d s n : Nat} :
    Memory.copy M d s n = none ↔ M.size < s + n ∨ M.size < d + n := by
  unfold Memory.copy
  cases hr : Memory.readBytes M s n with
  | none =>
    simp only [Option.bind_eq_bind, Option.bind_none, true_iff]
    unfold Memory.readBytes at hr; split at hr <;> simp_all
  | some B =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    obtain ⟨hb, rfl⟩ := (Memory.readBytes_eq_some_iff M B s n).mp hr
    have hs : (M.extract s (s + n)).size = n := by simp only [ByteArray.size_extract]; omega
    unfold Memory.writeBytes; rw [hs]; split <;> simp <;> omega

theorem bulk_store8 {M : ByteArray} {i : Nat} (w : BitVec 8) (hi : i + 1 ≤ M.size) :
    ∃ A, Memory.store M i (count := 1) w = some A ∧ A.size = M.size ∧
      ∀ j, A.data[j]? = if j = i then some (UInt8.ofNat w.toNat) else M.data[j]? := by
  have hsz : (Memory.encodeLE 1 w.toNat).size = 1 := Memory.encodeLE_size 1 _
  have hsome : (Memory.store M i (count := 1) w).isSome := by
    unfold Memory.store Memory.writeBytes; rw [hsz, ite_eq_left hi]; rfl
  obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨A, hA, Memory.writeBytes_size _ _ _ _ hA, fun j => ?_⟩
  rw [bulk_writeBytes_get hA j, hsz]
  by_cases hj : j = i
  · subst hj; rw [ite_eq_left ⟨Nat.le_refl _, by omega⟩, ite_eq_left rfl, Nat.sub_self]
    simp [Memory.encodeLE]
  · rw [ite_eq_right (by omega), ite_eq_right hj]

theorem bulk_load8 {M : ByteArray} {i : Nat} (hi : i + 1 ≤ M.size) :
    ∃ w : BitVec 8, Memory.load M i 1 = some w ∧ M.data[i]? = some (UInt8.ofNat w.toNat) := by
  have hr : Memory.readBytes M i 1 = some (M.extract i (i + 1)) := by
    unfold Memory.readBytes; rw [ite_eq_left hi]
  refine ⟨_, by unfold Memory.load; rw [hr]; rfl, ?_⟩
  have hlt : i < M.data.size := by simp only [ByteArray.size_data]; omega
  have hd : Memory.decodeLE (M.extract i (i + 1)) = (M.data[i]).toNat := by
    unfold Memory.decodeLE
    have : (M.extract i (i + 1)).data = #[M.data[i]] := by
      rw [ByteArray.data_extract]; apply Array.ext_getElem? ; intro k
      rw [Array.getElem?_extract]; rcases k with _ | k <;> simp [Array.getElem?_eq_getElem hlt] <;> omega
    rw [this]; simp
  rw [Array.getElem?_eq_getElem hlt]
  simp only [hd, BitVec.toNat_ofNat, Option.some.injEq]
  rw [Nat.mod_eq_of_lt (UInt8.toNat_lt _)]; simp

theorem bulk_ext {A B : ByteArray} (h : ∀ j : Nat, A.data[j]? = B.data[j]?) : A = B := by
  cases A; cases B; exact congrArg ByteArray.mk (Array.ext_getElem? h)

end Bytes

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
