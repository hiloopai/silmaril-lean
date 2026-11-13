module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.BackLeaf

/-!
# Exception renaming, backward: the table and memory families

Most table rules read a table or element segment only through its length, which the renaming
keeps: `table_rn_back_len` and `elem_rn_back_len` pull a target lookup back together with that
length. The rules that read or write entries (`table.get`, `table.set`, `table.size`,
`table.grow`, `table.init`) use the renaming equation `rnTable n ti₀ = ti`, rewritten in the
goal. Memories and data segments are not renamed (`mem_rn_back`, `data_rn_back`).

Refined from the earlier `Silmaril.Raw.Wasm.Models.FXRenameSim.BackTable`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename

variable {H : Type} {P : Profile} {n : Nat} {s t : Store H} {f : Frame} {L : List Admin}

theorem rnTable_refs_get_back {ti : TableInst} {i : Nat} {r : Ref}
    (h : (rnTable n ti).refs[i]? = some r) : ∃ r₀, ti.refs[i]? = some r₀ ∧ rnRef n r₀ = r := by
  simpa [rnTable] using h

theorem rnElem_refs_get_back {ei : ElemInst} {i : Nat} {r : Ref}
    (h : (rnElem n ei).refs[i]? = some r) : ∃ r₀, ei.refs[i]? = some r₀ ∧ rnRef n r₀ = r := by
  simpa [rnElem] using h

theorem grow?_rn_back {ti : TableInst} {k : Nat} {r : Ref} {ti' : TableInst}
    (h : (rnTable n ti).grow? k (rnRef n r) = some ti') :
    ∃ ti₀, ti.grow? k r = some ti₀ ∧ rnTable n ti₀ = ti' := by
  rw [grow?_rn, Option.map_eq_some_iff] at h
  exact h

theorem grow?_rn_none {ti : TableInst} {k : Nat} {r : Ref}
    (h : (rnTable n ti).grow? k (rnRef n r) = none) : ti.grow? k r = none := by
  rw [grow?_rn, Option.map_eq_none_iff] at h
  exact h

section Back

variable (h : ExnRen n s t)
include h

/-- A target table lookup, pulled back with its length. -/
theorem table_rn_back_len {x : TableIdx} {a : Nat} {ti : TableInst}
    (hl : t.table? (rnFrame n f) x = some (a, ti)) :
    ∃ ti₀, s.table? f x = some (a, ti₀) ∧ ti₀.refs.length = ti.refs.length := by
  obtain ⟨ti₀, ht₀, hti⟩ := table_rn_back h hl
  have hlen : ti₀.refs.length = ti.refs.length := by rw [← hti, rnTable_refs_length]
  exact ⟨ti₀, ht₀, hlen⟩

/-- A target element segment lookup, pulled back with its length. -/
theorem elem_rn_back_len {y : ElemIdx} {a : Nat} {ei : ElemInst}
    (hl : t.elem? (rnFrame n f) y = some (a, ei)) :
    ∃ ei₀, s.elem? f y = some (a, ei₀) ∧ ei₀.refs.length = ei.refs.length := by
  obtain ⟨ei₀, he₀, hei⟩ := elem_rn_back h hl
  have hlen : ei₀.refs.length = ei.refs.length := by rw [← hei]; simp [rnElem]
  exact ⟨ei₀, he₀, hlen⟩

theorem tableGet_rn_back {x : TableIdx} {a : AddrType} {i : BitVec a.intType.width} {ta : Nat}
    {ti : TableInst} {r : Ref} (ht : t.table? (rnFrame n f) x = some (ta, ti))
    (hr : ti.refs[i.toNat]? = some r) :
    BackOf (TableStep P) n s f [aconst a i, .plain (.tableGet x)] ⟨t, rnFrame n f, [.ref r]⟩ := by
  obtain ⟨ti₀, ht₀, hti⟩ := table_rn_back h ht
  have hr' : (rnTable n ti₀).refs[i.toNat]? = some r := by rw [hti]; exact hr
  obtain ⟨r₀, hr₀, hrr⟩ := rnTable_refs_get_back hr'
  have hd : (⟨t, rnFrame n f, [.ref r]⟩ : Config H) = ⟨t, rnFrame n f, rnAdmins n [.ref r₀]⟩ := by
    rw [← hrr]; rn_fin
  exact backOf_intro (.getVal ht₀ hr₀) hd h

theorem tableSet_rn_back {x : TableIdx} {a : AddrType} {i : BitVec a.intType.width} {r : Ref}
    {ta : Nat} {ti : TableInst} (ht : t.table? (rnFrame n f) x = some (ta, ti))
    (hb : i.toNat < ti.refs.length) :
    BackOf (TableStep P) n s f [aconst a i, .ref r, .plain (.tableSet x)]
      ⟨t.setTable ta { ti with refs := ti.refs.set i.toNat (rnRef n r) }, rnFrame n f, []⟩ := by
  obtain ⟨ti₀, ht₀, hti⟩ := table_rn_back h ht
  have hb₀ : i.toNat < ti₀.refs.length := by simpa only [← hti, rnTable_refs_length] using hb
  refine backOf_intro (.setVal ht₀ hb₀) ?_ (setTable_rn h _ _)
  rw [rnTable_set, hti]; rn_fin

theorem tableSize_rn_back {x : TableIdx} {ta : Nat} {ti : TableInst}
    (ht : t.table? (rnFrame n f) x = some (ta, ti)) :
    BackOf (TableStep P) n s f [.plain (.tableSize x)]
      ⟨t, rnFrame n f, [aconst ti.type.address (BitVec.ofNat _ ti.refs.length)]⟩ := by
  obtain ⟨ti₀, ht₀, hti⟩ := table_rn_back h ht
  refine backOf_intro (.size ht₀) ?_ h
  rw [← hti]; rn_fin

theorem tableGrow_rn_back {x : TableIdx} {a : AddrType} {k : BitVec a.intType.width} {r : Ref}
    {ta : Nat} {ti ti' : TableInst} (ht : t.table? (rnFrame n f) x = some (ta, ti))
    (hg : ti.grow? k.toNat (rnRef n r) = some ti')
    (hp : P.growMaySucceed .table ta ti.refs.length k.toNat) :
    BackOf (TableStep P) n s f [.ref r, aconst a k, .plain (.tableGrow x)]
      ⟨t.setTable ta ti', rnFrame n f, [aconst a (BitVec.ofNat _ ti.refs.length)]⟩ := by
  obtain ⟨ti₀, ht₀, hti⟩ := table_rn_back h ht
  have hg' : (rnTable n ti₀).grow? k.toNat (rnRef n r) = some ti' := by rw [hti]; exact hg
  obtain ⟨ti₁, hg₁, hti'⟩ := grow?_rn_back hg'
  have hp₀ : P.growMaySucceed .table ta ti₀.refs.length k.toNat := by
    simpa only [← hti, rnTable_refs_length] using hp
  refine backOf_intro (.growSucceed ht₀ hg₁ hp₀) ?_ (setTable_rn h _ _)
  rw [← hti, ← hti']; rn_fin

theorem tableGrowFail_rn_back {x : TableIdx} {a : AddrType} {k : BitVec a.intType.width}
    {r : Ref} {ta : Nat} {ti : TableInst} (ht : t.table? (rnFrame n f) x = some (ta, ti))
    (hp : P.growMayFail .table ta ti.refs.length k.toNat ∨ ti.grow? k.toNat (rnRef n r) = none) :
    BackOf (TableStep P) n s f [.ref r, aconst a k, .plain (.tableGrow x)]
      ⟨t, rnFrame n f, [aconst a (BitVec.allOnes _)]⟩ := by
  obtain ⟨ti₀, ht₀, hti⟩ := table_rn_back h ht
  have hp' : P.growMayFail .table ta (rnTable n ti₀).refs.length k.toNat ∨
      (rnTable n ti₀).grow? k.toNat (rnRef n r) = none := by rw [hti]; exact hp
  have hp₀ : P.growMayFail .table ta ti₀.refs.length k.toNat ∨ ti₀.grow? k.toNat r = none :=
    hp'.imp (fun hp => by simpa using hp) grow?_rn_none
  exact backOf_intro (.growFail ht₀ hp₀) (by rn_fin) h

theorem tableInitSucc_rn_back {x : TableIdx} {y : ElemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j k : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
    {r : Ref} (ht : t.table? (rnFrame n f) x = some (ta, ti))
    (he : t.elem? (rnFrame n f) y = some (ea, ei))
    (hb : i.toNat + k.toNat ≤ ti.refs.length ∧ j.toNat + k.toNat ≤ ei.refs.length)
    (hk : k ≠ 0) (hr : ei.refs[j.toNat]? = some r) :
    BackOf (TableStep P) n s f [aconst a i, constI32 j, constI32 k, .plain (.tableInit x y)]
      ⟨t, rnFrame n f, [aconst a i, .ref r, .plain (.tableSet x),
        aconst a (i + 1), constI32 (j + 1), constI32 (k - 1), .plain (.tableInit x y)]⟩ := by
  obtain ⟨ti₀, ht₀, hlt⟩ := table_rn_back_len h ht
  obtain ⟨ei₀, he₀, hei⟩ := elem_rn_back h he
  have hr' : (rnElem n ei₀).refs[j.toNat]? = some r := by rw [hei]; exact hr
  obtain ⟨r₀, hr₀, hrr⟩ := rnElem_refs_get_back hr'
  have hle : ei₀.refs.length = ei.refs.length := by rw [← hei]; simp [rnElem]
  have hb₀ : i.toNat + k.toNat ≤ ti₀.refs.length ∧ j.toNat + k.toNat ≤ ei₀.refs.length := by
    rw [hlt, hle]; exact hb
  refine backOf_intro (.initSucc ht₀ he₀ hb₀ hk hr₀) ?_ h
  rw [← hrr]; rn_fin

end Back

theorem table_rn_back_of (h : ExnRen n s t) {c d : Config H} (step : TableStep P c d)
    (hc : (⟨t, rnFrame n f, rnAdmins n L⟩ : Config H) = c) : BackOf (TableStep P) n s f L d := by
  cases step with
  | getOob ht hb =>
    rn_inv hc
    obtain ⟨ti₀, ht₀, hl⟩ := table_rn_back_len h ht
    exact backOf_intro (.getOob ht₀ (hl ▸ hb)) (by rn_fin) h
  | getVal ht hr => rn_inv hc; exact tableGet_rn_back h ht hr
  | setOob ht hb =>
    rn_inv hc
    obtain ⟨ti₀, ht₀, hl⟩ := table_rn_back_len h ht
    exact backOf_intro (.setOob ht₀ (hl ▸ hb)) (by rn_fin) h
  | setVal ht hb => rn_inv hc; exact tableSet_rn_back h ht hb
  | size ht => rn_inv hc; exact tableSize_rn_back h ht
  | growSucceed ht hg hp => rn_inv hc; exact tableGrow_rn_back h ht hg hp
  | growFail ht hp => rn_inv hc; exact tableGrowFail_rn_back h ht hp
  | fillOob ht hb =>
    rn_inv hc
    obtain ⟨ti₀, ht₀, hl⟩ := table_rn_back_len h ht
    exact backOf_intro (.fillOob ht₀ (hl ▸ hb)) (by rn_fin) h
  | fillZero ht hb =>
    rn_inv hc
    obtain ⟨ti₀, ht₀, hl⟩ := table_rn_back_len h ht
    exact backOf_intro (.fillZero ht₀ (hl ▸ hb)) (by rn_fin) h
  | fillSucc ht hb hn =>
    rn_inv hc
    obtain ⟨ti₀, ht₀, hl⟩ := table_rn_back_len h ht
    exact backOf_intro (.fillSucc ht₀ (hl ▸ hb) hn) (by rn_fin) h
  | copyOob h₁ h₂ hb =>
    rn_inv hc
    obtain ⟨ti₁, ht₁, hl₁⟩ := table_rn_back_len h h₁
    obtain ⟨ti₂, ht₂, hl₂⟩ := table_rn_back_len h h₂
    exact backOf_intro (.copyOob ht₁ ht₂ (hl₁ ▸ hl₂ ▸ hb)) (by rn_fin) h
  | copyZero h₁ h₂ hb =>
    rn_inv hc
    obtain ⟨ti₁, ht₁, hl₁⟩ := table_rn_back_len h h₁
    obtain ⟨ti₂, ht₂, hl₂⟩ := table_rn_back_len h h₂
    exact backOf_intro (.copyZero ht₁ ht₂ (hl₁ ▸ hl₂ ▸ hb)) (by rn_fin) h
  | copyLe h₁ h₂ hb hn hle =>
    rn_inv hc
    obtain ⟨ti₁, ht₁, hl₁⟩ := table_rn_back_len h h₁
    obtain ⟨ti₂, ht₂, hl₂⟩ := table_rn_back_len h h₂
    exact backOf_intro (.copyLe ht₁ ht₂ (hl₁ ▸ hl₂ ▸ hb) hn hle) (by rn_fin) h
  | copyGt h₁ h₂ hb hn hgt =>
    rn_inv hc
    obtain ⟨ti₁, ht₁, hl₁⟩ := table_rn_back_len h h₁
    obtain ⟨ti₂, ht₂, hl₂⟩ := table_rn_back_len h h₂
    exact backOf_intro (.copyGt ht₁ ht₂ (hl₁ ▸ hl₂ ▸ hb) hn hgt) (by rn_fin) h
  | initOob ht he hb =>
    rn_inv hc
    obtain ⟨ti₀, ht₀, hlt⟩ := table_rn_back_len h ht
    obtain ⟨ei₀, he₀, hle⟩ := elem_rn_back_len h he
    exact backOf_intro (.initOob ht₀ he₀ (hlt ▸ hle ▸ hb)) (by rn_fin) h
  | initZero ht he hb =>
    rn_inv hc
    obtain ⟨ti₀, ht₀, hlt⟩ := table_rn_back_len h ht
    obtain ⟨ei₀, he₀, hle⟩ := elem_rn_back_len h he
    exact backOf_intro (.initZero ht₀ he₀ (hlt ▸ hle ▸ hb)) (by rn_fin) h
  | initSucc ht he hb hn hr => rn_inv hc; exact tableInitSucc_rn_back h ht he hb hn hr
  | elemDrop he =>
    rn_inv hc
    obtain ⟨ei₀, he₀, -⟩ := elem_rn_back h he
    exact backOf_intro (.elemDrop he₀) (by rn_fin) (setElem_rn h _ [])

theorem table_rn_back' (h : ExnRen n s t) {d : Config H}
    (step : TableStep P ⟨t, rnFrame n f, rnAdmins n L⟩ d) : BackOf (TableStep P) n s f L d :=
  table_rn_back_of h step rfl

/-- Memory and data-segment rules: the memories and data segments are not renamed, so every
premise carries over (`mem_rn_back`, `data_rn_back`). -/
theorem memory_rn_back_of (h : ExnRen n s t) {c d : Config H} (step : MemoryStep P c d)
    (hc : (⟨t, rnFrame n f, rnAdmins n L⟩ : Config H) = c) :
    BackOf (MemoryStep P) n s f L d := by
  cases step with
  | loadIntOob hm hb => rn_inv hc; exact backOf_intro (.loadIntOob (mem_rn_back h hm) hb) (by rn_fin) h
  | loadIntVal hm hl => rn_inv hc; exact backOf_intro (.loadIntVal (mem_rn_back h hm) hl) (by rn_fin) h
  | loadPackOob hm hb => rn_inv hc; exact backOf_intro (.loadPackOob (mem_rn_back h hm) hb) (by rn_fin) h
  | loadPackVal hm hl => rn_inv hc; exact backOf_intro (.loadPackVal (mem_rn_back h hm) hl) (by rn_fin) h
  | loadFloatOob hm hb =>
    rn_inv hc; exact backOf_intro (.loadFloatOob (mem_rn_back h hm) hb) (by rn_fin) h
  | loadFloatVal hm hl =>
    rn_inv hc; exact backOf_intro (.loadFloatVal (mem_rn_back h hm) hl) (by rn_fin) h
  | vecLoadOob hm hb => rn_inv hc; exact backOf_intro (.vecLoadOob (mem_rn_back h hm) hb) (by rn_fin) h
  | vecLoadVal hm hl => rn_inv hc; exact backOf_intro (.vecLoadVal (mem_rn_back h hm) hl) (by rn_fin) h
  | vecLoadLaneOob hm hb =>
    rn_inv hc; exact backOf_intro (.vecLoadLaneOob (mem_rn_back h hm) hb) (by rn_fin) h
  | vecLoadLaneVal hm hl =>
    rn_inv hc; exact backOf_intro (.vecLoadLaneVal (mem_rn_back h hm) hl) (by rn_fin) h
  | storeIntOob hm hb =>
    rn_inv hc; exact backOf_intro (.storeIntOob (mem_rn_back h hm) hb) (by rn_fin) h
  | storeIntVal hm hs =>
    rn_inv hc
    exact backOf_intro (.storeIntVal (mem_rn_back h hm) hs) (by rn_fin) (setMem_rn h _ _)
  | storePackOob hm hb =>
    rn_inv hc; exact backOf_intro (.storePackOob (mem_rn_back h hm) hb) (by rn_fin) h
  | storePackVal hm hs =>
    rn_inv hc
    exact backOf_intro (.storePackVal (mem_rn_back h hm) hs) (by rn_fin) (setMem_rn h _ _)
  | storeFloatOob hm hb =>
    rn_inv hc; exact backOf_intro (.storeFloatOob (mem_rn_back h hm) hb) (by rn_fin) h
  | storeFloatVal hm hs =>
    rn_inv hc
    exact backOf_intro (.storeFloatVal (mem_rn_back h hm) hs) (by rn_fin) (setMem_rn h _ _)
  | vecStoreOob hm hb =>
    rn_inv hc; exact backOf_intro (.vecStoreOob (mem_rn_back h hm) hb) (by rn_fin) h
  | vecStoreVal hm hs =>
    rn_inv hc
    exact backOf_intro (.vecStoreVal (mem_rn_back h hm) hs) (by rn_fin) (setMem_rn h _ _)
  | vecStoreLaneOob hm hb =>
    rn_inv hc; exact backOf_intro (.vecStoreLaneOob (mem_rn_back h hm) hb) (by rn_fin) h
  | vecStoreLaneVal hm hs =>
    rn_inv hc
    exact backOf_intro (.vecStoreLaneVal (mem_rn_back h hm) hs) (by rn_fin) (setMem_rn h _ _)
  | size hm => rn_inv hc; exact backOf_intro (.size (mem_rn_back h hm)) (by rn_fin) h
  | growSucceed hm hg hp =>
    rn_inv hc
    exact backOf_intro (.growSucceed (mem_rn_back h hm) hg hp) (by rn_fin) (setMem_rn h _ _)
  | growFail hm hp => rn_inv hc; exact backOf_intro (.growFail (mem_rn_back h hm) hp) (by rn_fin) h
  | fillOob hm hb => rn_inv hc; exact backOf_intro (.fillOob (mem_rn_back h hm) hb) (by rn_fin) h
  | fillZero hm hb => rn_inv hc; exact backOf_intro (.fillZero (mem_rn_back h hm) hb) (by rn_fin) h
  | fillSucc hm hb hn =>
    rn_inv hc; exact backOf_intro (.fillSucc (mem_rn_back h hm) hb hn) (by rn_fin) h
  | copyOob h₁ h₂ hb =>
    rn_inv hc
    exact backOf_intro (.copyOob (mem_rn_back h h₁) (mem_rn_back h h₂) hb) (by rn_fin) h
  | copyZero h₁ h₂ hb =>
    rn_inv hc
    exact backOf_intro (.copyZero (mem_rn_back h h₁) (mem_rn_back h h₂) hb) (by rn_fin) h
  | copyLe h₁ h₂ hb hn hle =>
    rn_inv hc
    exact backOf_intro (.copyLe (mem_rn_back h h₁) (mem_rn_back h h₂) hb hn hle) (by rn_fin) h
  | copyGt h₁ h₂ hb hn hgt =>
    rn_inv hc
    exact backOf_intro (.copyGt (mem_rn_back h h₁) (mem_rn_back h h₂) hb hn hgt) (by rn_fin) h
  | initOob hm hd hb =>
    rn_inv hc
    exact backOf_intro (.initOob (mem_rn_back h hm) (data_rn_back h hd) hb) (by rn_fin) h
  | initZero hm hd hb =>
    rn_inv hc
    exact backOf_intro (.initZero (mem_rn_back h hm) (data_rn_back h hd) hb) (by rn_fin) h
  | initSucc hm hd hb hn hby =>
    rn_inv hc
    exact backOf_intro (.initSucc (mem_rn_back h hm) (data_rn_back h hd) hb hn hby) (by rn_fin) h
  | dataDrop hd =>
    rn_inv hc
    exact backOf_intro (.dataDrop (data_rn_back h hd)) (by rn_fin) (setData_rn h _ _)

theorem memory_rn_back (h : ExnRen n s t) {d : Config H}
    (step : MemoryStep P ⟨t, rnFrame n f, rnAdmins n L⟩ d) : BackOf (MemoryStep P) n s f L d :=
  memory_rn_back_of h step rfl

end Silmaril.Proofs.Wasm.Models.FXRenameSim
