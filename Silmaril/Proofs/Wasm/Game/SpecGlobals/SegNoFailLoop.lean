module

public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitTrap
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryAux

/-!
# The direct `table.init`/`memory.init` loops succeed in bounds

`tableInitLoop_some`, `memoryInitLoop_some`: once the table (memory) and the element (data)
segment are found through the frame and the initial bounds check passes, silmaril-lean's direct
loops succeed: every element (byte) read is in bounds, every write keeps the lengths.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem table?_setTable {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (h : s.table? f x = some (ta, ti)) (ti' : TableInst) :
    (s.setTable ta ti').table? f x = some (ta, ti') := by
  simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, t, ht, he⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hlt : a < s.tables.length := (List.getElem?_eq_some_iff.1 ht).1
  simp only [Store.table?, Store.setTable, ha, Option.bind_eq_bind, Option.bind_some,
    List.getElem?_set_self hlt, Option.pure_def]

theorem elem?_setTable {s : Store H} {f : Frame} {y : ElemIdx} (ta : Nat) (ti' : TableInst) :
    (s.setTable ta ti').elem? f y = s.elem? f y := rfl

theorem mem?_setMem {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (h : s.mem? f x = some (ma, mi)) (mi' : MemInst) :
    (s.setMem ma mi').mem? f x = some (ma, mi') := by
  simp only [Store.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, t, ht, he⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hlt : a < s.mems.length := (List.getElem?_eq_some_iff.1 ht).1
  simp only [Store.mem?, Store.setMem, ha, Option.bind_eq_bind, Option.bind_some,
    List.getElem?_set_self hlt, Option.pure_def]

theorem data?_setMem {s : Store H} {f : Frame} {y : DataIdx} (ma : Nat) (mi' : MemInst) :
    (s.setMem ma mi').data? f y = s.data? f y := rfl

theorem bv_succ_le {w : Nat} (i : BitVec w) : (i + 1).toNat ≤ i.toNat + 1 := by
  have h1 : (1 : BitVec w).toNat ≤ 1 := by
    show (BitVec.ofNat w 1).toNat ≤ 1
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_le _ _
  rw [BitVec.toNat_add]
  exact (Nat.mod_le _ _).trans (by omega)

theorem bv_pred {n : BitVec 32} (hn : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have h : n.toNat ≠ 0 := fun h => hn (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

/-- **The direct `table.init` loop succeeds in bounds.** -/
theorem tableInitLoop_some {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType} (n : Nat)
    (s : Store H) (i : BitVec a.intType.width) (j nb : BitVec 32) (hn : nb.toNat = n)
    (ta : Nat) (ti : TableInst) (ea : Nat) (ei : ElemInst) (ht : s.table? f x = some (ta, ti))
    (he : s.elem? f y = some (ea, ei)) (hi : i.toNat + nb.toNat ≤ ti.refs.length)
    (hj : j.toNat + nb.toNat ≤ ei.refs.length) :
    ∃ s', tableInitLoop s f x y a i j nb = some s' ∧ s'.elems = s.elems := by
  induction n generalizing s i j nb ti with
  | zero =>
    show ∃ s', tableInitLoop s f x y a i j nb = some s' ∧ s'.elems = s.elems
    have hz : nb = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    refine ⟨s, ?_, rfl⟩
    have hb : i.toNat + nb.toNat ≤ ti.refs.length ∧ j.toNat + nb.toNat ≤ ei.refs.length := ⟨hi, hj⟩
    rw [tableInitLoop, ht, he]
    simp only [hb, and_self, ite_true]
    simp only [hz, dite_true]
  | succ n ih =>
    show ∃ s', tableInitLoop s f x y a i j nb = some s' ∧ s'.elems = s.elems
    have hnz : nb ≠ 0 := fun h => by rw [h] at hn; simp at hn
    have hjl : j.toNat < ei.refs.length := by omega
    have hr : ei.refs[j.toNat]? = some ei.refs[j.toNat] := List.getElem?_eq_getElem hjl
    have hp : (nb - 1).toNat = n := by rw [bv_pred hnz]; omega
    have ht' : (s.setTable ta { ti with refs := ti.refs.set i.toNat ei.refs[j.toNat] }).table? f x =
        some (ta, { ti with refs := ti.refs.set i.toNat ei.refs[j.toNat] }) :=
      table?_setTable ht _
    have hi' : (i + 1).toNat + (nb - 1).toNat ≤ (ti.refs.set i.toNat ei.refs[j.toNat]).length := by
      have h1 : (i + 1).toNat ≤ i.toNat + 1 := bv_succ_le i
      rw [List.length_set, bv_pred hnz]; omega
    have hj' : (j + 1).toNat + (nb - 1).toNat ≤ ei.refs.length := by
      have h1 : (j + 1).toNat ≤ j.toNat + 1 := bv_succ_le j
      rw [bv_pred hnz]; omega
    have he' : (s.setTable ta { ti with refs := ti.refs.set i.toNat ei.refs[j.toNat] }).elem? f y =
        some (ea, ei) := he
    obtain ⟨s', hs', hel⟩ := ih _ (i + 1) (j + 1) (nb - 1) hp _ ht' he' hi' hj'
    refine ⟨s', ?_, hel⟩
    rw [tableInitLoop, ht, he]
    simp only [hi, hj, and_self, ite_true, hnz, dite_false, hr]
    exact hs'

/-- **The direct `memory.init` loop succeeds in bounds.** -/
theorem memoryInitLoop_some {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType} (n : Nat)
    (s : Store H) (i : BitVec a.intType.width) (j nb : BitVec 32) (hn : nb.toNat = n)
    (ma : Nat) (mi : MemInst) (da : Nat) (di : DataInst) (hm : s.mem? f x = some (ma, mi))
    (hd : s.data? f y = some (da, di)) (hi : i.toNat + nb.toNat ≤ mi.bytes.size)
    (hj : j.toNat + nb.toNat ≤ di.bytes.size) :
    ∃ s', memoryInitLoop s f x y a i j nb = some s' ∧ s'.datas = s.datas := by
  induction n generalizing s i j nb mi with
  | zero =>
    show ∃ s', memoryInitLoop s f x y a i j nb = some s' ∧ s'.datas = s.datas
    have hz : nb = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    refine ⟨s, ?_, rfl⟩
    have hb : i.toNat + nb.toNat ≤ mi.bytes.size ∧ j.toNat + nb.toNat ≤ di.bytes.size := ⟨hi, hj⟩
    rw [memoryInitLoop, hm, hd]
    simp only [hb, and_self, ite_true]
    simp only [hz, dite_true]
  | succ n ih =>
    show ∃ s', memoryInitLoop s f x y a i j nb = some s' ∧ s'.datas = s.datas
    have hnz : nb ≠ 0 := fun h => by rw [h] at hn; simp at hn
    have hjl : j.toNat < di.bytes.data.size := by
      have : di.bytes.size = di.bytes.data.size := rfl
      omega
    have hr : di.bytes.data[j.toNat]? = some di.bytes.data[j.toNat] :=
      Array.getElem?_eq_getElem hjl
    obtain ⟨b, hb⟩ := Memory.store_of_le (m := mi.bytes) (start := effAddr i.toNat memarg0)
      (count := PackSize.i8.width / 8)
      ((BitVec.ofNat 32 di.bytes.data[j.toNat].toNat).setWidth _)
      (by simp [effAddr, memarg0, PackSize.width]; omega)
    have hbs : b.size = mi.bytes.size := Memory.store_size hb
    have hp : (nb - 1).toNat = n := by rw [bv_pred hnz]; omega
    have hm' : (s.setMem ma { mi with bytes := b }).mem? f x = some (ma, { mi with bytes := b }) :=
      mem?_setMem hm _
    have hi' : (i + 1).toNat + (nb - 1).toNat ≤ b.size := by
      have h1 : (i + 1).toNat ≤ i.toNat + 1 := bv_succ_le i
      rw [hbs, bv_pred hnz]; omega
    have hj' : (j + 1).toNat + (nb - 1).toNat ≤ di.bytes.size := by
      have h1 : (j + 1).toNat ≤ j.toNat + 1 := bv_succ_le j
      rw [bv_pred hnz]; omega
    have hd' : (s.setMem ma { mi with bytes := b }).data? f y = some (da, di) := hd
    obtain ⟨s', hs', hel⟩ := ih _ (i + 1) (j + 1) (nb - 1) hp _ hm' hd' hi' hj'
    refine ⟨s', ?_, hel⟩
    rw [memoryInitLoop, hm, hd]
    simp only [hi, hj, and_self, ite_true, hnz, dite_false, hr, hb]
    exact hs'

end Silmaril.Proofs.Wasm.Game.SpecGlobals
