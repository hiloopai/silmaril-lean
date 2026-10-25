module

public import Silmaril.Wasm.Execution.Core.Exec.SegmentInit
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval

@[expose] public section

/-! # Element-segment initialisation: the contents of one table slot

The element segments of `$instantiate` (`runElem`) fill the tables by `table.init` and
then drop the segments. Their effect on the store is computed by `initElemList?`
(`Execution/Core/Exec/SegmentInit.lean`, with `initElemList?_steps` for its runs and
`initElemList?_complete` for the converse). This file follows one slot `k` of the table
at address `ta` through that computation:

* `tableInitLoop_slot`: after `table.init` of a table index that resolves to `ta`, a slot
  in the written range holds the segment's entry, and every other slot is unchanged;
* `initElemList?_slot`: after a list of segments with `i32.const` offsets, the slot holds
  the entry of the last active segment that covers it (`slotFold`), or its initial
  contents when no segment covers it.

This is the elem-init fact of Directize (`Pass/Directize.lean`): `Directize.slot?`
reads the same fold off the syntax.
-/

namespace Silmaril.Wasm.Binaryen

namespace ElemInit

open Execution.Core Numerics Validation

variable {H : Type}

/-- The reference in slot `k` of the table at address `ta`. -/
def slotAt (s : Store H) (ta k : Nat) : Option Ref := (s.tables[ta]?).bind (·.refs[k]?)

theorem slotAt_setTable (s : Store H) {ta' ta k : Nat} (ti : TableInst) :
    slotAt (s.setTable ta' ti) ta k =
      if ta' = ta ∧ ta < s.tables.length then ti.refs[k]? else slotAt s ta k := by
  unfold slotAt Store.setTable
  by_cases e : ta' = ta
  · subst e
    by_cases hl : ta' < s.tables.length
    · simp [hl]
    · simp [hl]
  · simp [e, List.getElem?_set_ne e]

theorem tableInitLoop_elems {x : TableIdx} {y : ElemIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f : Frame} {i : BitVec a.intType.width} {j : BitVec 32},
      tableInitLoop s f x y a i j n = some s' → s'.elems = s.elems ∧ s'.funcs = s.funcs := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s s' f i j hl
  rw [tableInitLoop] at hl
  split at hl
  · split at hl
    · split at hl
      · cases hl; exact ⟨rfl, rfl⟩
      · rename_i hn
        split at hl
        · obtain ⟨h1, h2⟩ := ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl hl
          exact ⟨h1, h2⟩
        · cases hl
    · cases hl
  · cases hl

theorem elem?_setTable (s : Store H) (f : Frame) (y : ElemIdx) (ta : Nat) (ti : TableInst) :
    (s.setTable ta ti).elem? f y = s.elem? f y := rfl

theorem bv_toNat_add_one {w : Nat} {i : BitVec w} (h : i.toNat + 1 < 2 ^ w) :
    (i + 1).toNat = i.toNat + 1 := by
  have h1 : (1 : BitVec w).toNat = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
  rw [BitVec.toNat_add, h1]
  exact Nat.mod_eq_of_lt h

theorem bv_toNat_add_one_le {w : Nat} (i : BitVec w) : (i + 1).toNat ≤ i.toNat + 1 := by
  rw [BitVec.toNat_add]
  refine (Nat.mod_le _ _).trans ?_
  have : (1 : BitVec w).toNat ≤ 1 := by simpa using Nat.mod_le 1 (2 ^ w)
  omega

theorem bv32_toNat_sub_one {n : BitVec 32} (hn : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

/-- **`table.init` writes its range of the table.** For a table index that resolves to
`ta`, a slot in `[i, i + n)` holds entry `j + (k - i)` of the segment; every other slot
of `ta` keeps its contents. -/
theorem tableInitLoop_slot {x : TableIdx} {y : ElemIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f : Frame} {i : BitVec a.intType.width} {j : BitVec 32},
      tableInitLoop s f x y a i j n = some s' →
      ∀ {ta k ea : Nat} {ei : ElemInst}, s.elem? f y = some (ea, ei) →
      (∀ ti, s.tables[ta]? = some ti → ti.refs.length ≤ 2 ^ a.intType.width) →
      j.toNat + n.toNat ≤ 2 ^ 32 →
      slotAt s' ta k =
        if f.module.tables[x.toNat]? = some ta ∧ i.toNat ≤ k ∧ k < i.toNat + n.toNat then
          ei.refs[j.toNat + (k - i.toNat)]?
        else slotAt s ta k := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ m ih =>
  intro s s' f i j hl ta k ea ei he hlen hj
  rw [← h]
  rw [tableInitLoop] at hl
  split at hl
  · rename_i ta' ti ea' ei' ht he'
    rw [he] at he'
    simp only [Option.some.injEq, Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    have hx : f.module.tables[x.toNat]? = some ta' ∧ s.tables[ta']? = some ti := by
      simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨a, hx, ti₀, hti, rfl, rfl⟩ := ht
      exact ⟨hx, hti⟩
    split at hl
    · rename_i hb
      split at hl
      · rename_i hn
        subst hn; cases hl
        exact (ite_eq_right_iff.mpr fun ⟨_, h1, h2⟩ => by simp at h2; omega).symm
      · rename_i hn
        split at hl
        · rename_i r hr
          have hn1 := bv32_toNat_sub_one hn
          have hnz : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
          have hj' : (j + 1).toNat + (n - 1).toNat ≤ 2 ^ 32 := by
            have := bv_toNat_add_one_le j
            rw [hn1]; omega
          have hlen' : ∀ ti₁, (s.setTable ta' { ti with refs := ti.refs.set i.toNat r }).tables[ta]? =
              some ti₁ → ti₁.refs.length ≤ 2 ^ a.intType.width := by
            intro ti₁ h₁
            simp only [Store.setTable, List.getElem?_set] at h₁
            by_cases e : ta' = ta
            · subst e
              simp only [ite_true, (List.getElem?_eq_some_iff.mp hx.2).1, Option.some.injEq] at h₁
              subst h₁
              simpa using hlen ti hx.2
            · simp only [e, ite_false] at h₁
              exact hlen ti₁ h₁
          rw [ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl hl he hlen' hj', slotAt_setTable]
          have hta' : ta' < s.tables.length := (List.getElem?_eq_some_iff.mp hx.2).1
          by_cases eq : ta' = ta
          · subst eq
            have hL := hlen ti hx.2
            simp only [hx.1, true_and, hta', and_true]
            by_cases hn2 : n.toNat = 1
            · -- the last write: the remaining range is empty
              have : (n - 1).toNat = 0 := by rw [hn1, hn2]
              simp only [this, Nat.add_zero]
              have hk : ¬ ((i + 1).toNat ≤ k ∧ k < (i + 1).toNat) := by omega
              simp only [hk, ite_false]
              by_cases hki : k = i.toNat
              · subst hki
                simp [hn2, hr, List.getElem?_set_self (by omega : i.toNat < ti.refs.length)]
              · have : ¬ (i.toNat ≤ k ∧ k < i.toNat + n.toNat) := by omega
                simp [this, List.getElem?_set_ne (Ne.symm hki), slotAt, hx.2]
            · have hi1 : (i + 1).toNat = i.toNat + 1 := bv_toNat_add_one (by omega)
              have hj1 : (j + 1).toNat = j.toNat + 1 := bv_toNat_add_one (by omega)
              rw [hi1, hj1, hn1]
              by_cases hki : k = i.toNat
              · subst hki
                have : ¬ (i.toNat + 1 ≤ i.toNat ∧ i.toNat < i.toNat + 1 + (n.toNat - 1)) := by
                  omega
                simp only [this, ite_false]
                simp [hr, List.getElem?_set_self (by omega : i.toNat < ti.refs.length),
                  show i.toNat < i.toNat + n.toNat by omega]
              · by_cases hin : i.toNat + 1 ≤ k ∧ k < i.toNat + 1 + (n.toNat - 1)
                · have : i.toNat ≤ k ∧ k < i.toNat + n.toNat := by omega
                  simp only [hin, this, and_self, ite_true]
                  congr 1; omega
                · have : ¬ (i.toNat ≤ k ∧ k < i.toNat + n.toNat) := by omega
                  simp [hin, this, List.getElem?_set_ne (Ne.symm hki), slotAt, hx.2]
          · have : ¬ (f.module.tables[x.toNat]? = some ta) := by
              rw [hx.1]; simpa using eq
            simp [this, eq]
        · cases hl
    · cases hl
  · cases hl

/-- The length of the table at address `ta`. -/
def tableLen (s : Store H) (ta : Nat) : Option Nat :=
  (s.tables[ta]?).map fun t : TableInst => t.refs.length

theorem tableInitLoop_len {x : TableIdx} {y : ElemIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f : Frame} {i : BitVec a.intType.width} {j : BitVec 32},
      tableInitLoop s f x y a i j n = some s' →
      ∀ ta, tableLen s' ta = tableLen s ta := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ m ih =>
  intro s s' f i j hl ta
  rw [tableInitLoop] at hl
  split at hl
  · rename_i ta' ti ea' ei' ht he'
    have hx : s.tables[ta']? = some ti := by
      simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨a, -, ti₀, hti, rfl, rfl⟩ := ht
      exact hti
    split at hl
    · split at hl
      · cases hl; rfl
      · rename_i hn
        split at hl
        · rw [ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl hl]
          simp only [tableLen, Store.setTable, List.getElem?_set]
          by_cases e : ta' = ta
          · subst e
            obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hx
            simp [hlt, heq]
          · simp [e]
        · cases hl
    · cases hl
  · cases hl

/-- An evaluator that reads an `i32.const` offset without changing the store. -/
def ConstOffsets (ev : Store H → Frame → Expr → Option (Store H × Val)) (f : Frame) : Prop :=
  ∀ (s : Store H) (o : BitVec 32), ev s f [.intConst .i32 o] = some (s, .num ⟨.int .i32, o⟩)

theorem evalConst?_constOffsets (f : Frame) : ConstOffsets (H := H) evalConst? f := by
  intro s o
  simp [evalConst?, constExpr?, constInstr?]

/-- The elem index of segment `x` in `$runelem_`. -/
abbrev eidx (x : Nat) : ElemIdx := ⟨Fin.ofNat _ x⟩

/-- Slot `k` of the table at address `ta` after segment `p` = (index, segment), whose
element instance holds `R p.1`: the entry of `p` when `p` is an active segment of a table
index that resolves to `ta` with an `i32.const` offset and covers `k`, and `acc` otherwise. -/
def segSlot (mi : ModuleInst) (R : Nat → List Ref) (ta k : Nat) (acc : Option Ref)
    (p : Nat × Elem) : Option Ref :=
  match p.2.mode with
  | .active y [.intConst .i32 o] =>
    if mi.tables[y.toNat]? = some ta ∧ o.toNat ≤ k ∧ k < o.toNat + p.2.init.length then
      (R p.1)[k - o.toNat]?
    else acc
  | _ => acc

/-- The facts on one segment that `initElemList?_slot` needs. -/
structure SegOk (s : Store H) (f : Frame) (R : Nat → List Ref) (p : Nat × Elem) (ea : Nat) : Prop where
  shape : ∀ y off, p.2.mode = .active y off → ∃ o : BitVec 32, off = [.intConst .i32 o]
  elem : f.module.elems[(eidx p.1).toNat]? = some ea
  inst : ∃ ei, s.elems[ea]? = some ei ∧ ei.refs = R p.1
  len : p.2.init.length < 2 ^ 32

theorem elem?_of_segOk {s : Store H} {f : Frame} {R : Nat → List Ref} {p : Nat × Elem} {ea : Nat}
    (h : SegOk s f R p ea) : ∃ ei, s.elem? f (eidx p.1) = some (ea, ei) ∧ ei.refs = R p.1 := by
  obtain ⟨ei, he, hr⟩ := h.inst
  exact ⟨ei, by simp [Store.elem?, h.elem, he], hr⟩

theorem setElem_tables (s : Store H) (ea : Nat) (rs : List Ref) :
    (s.setElem ea rs).tables = s.tables := rfl

theorem slotAt_setElem (s : Store H) (ea : Nat) (rs : List Ref) (ta k : Nat) :
    slotAt (s.setElem ea rs) ta k = slotAt s ta k := rfl

theorem tableLen_setElem (s : Store H) (ea : Nat) (rs : List Ref) (ta : Nat) :
    tableLen (s.setElem ea rs) ta = tableLen s ta := rfl

theorem elemDrop?_eq {s s' : Store H} {f : Frame} {x : ElemIdx} {ea : Nat}
    (hx : f.module.elems[x.toNat]? = some ea) (h : elemDrop? s f x = some s') :
    s' = s.setElem ea [] := by
  unfold elemDrop? at h
  cases he : s.elem? f x with
  | none => simp [he] at h
  | some q =>
    rcases q with ⟨ea', ei⟩
    simp only [he, Option.map_some, Option.some.injEq] at h
    simp only [Store.elem?, hx, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨_, -, rfl, -⟩ := he
    exact h.symm

theorem setElem_elems_ne (s : Store H) {ea ea' : Nat} (rs : List Ref) (h : ea' ≠ ea) :
    (s.setElem ea rs).elems[ea']? = s.elems[ea']? := by
  simp [Store.setElem, Ne.symm h]

/-- **One segment.** The slot follows `segSlot`; only the segment's own element instance
changes among the element instances, and no table changes length. -/
theorem initElemSeg?_slot {ev : Store H → Frame → Expr → Option (Store H × Val)} {f : Frame}
    (hev : ConstOffsets ev f) {s s' : Store H} {R : Nat → List Ref} {p : Nat × Elem} {ea : Nat}
    (hp : SegOk s f R p ea) (h : initElemSeg? ev s f p.1 p.2 = some s') {ta k : Nat}
    (hlen : ∀ ti, s.tables[ta]? = some ti → ti.refs.length ≤ 2 ^ 32) :
    slotAt s' ta k = segSlot f.module R ta k (slotAt s ta k) p ∧
      (∀ ea', ea' ≠ ea → s'.elems[ea']? = s.elems[ea']?) ∧
      (∀ ta, tableLen s' ta = tableLen s ta) := by
  unfold initElemSeg? at h
  split at h
  · rename_i hm
    cases h
    exact ⟨by simp [segSlot, hm], fun _ _ => rfl, fun _ => rfl⟩
  · rename_i hm
    rw [elemDrop?_eq hp.elem h]
    exact ⟨by simp [segSlot, hm, slotAt_setElem], fun _ e => setElem_elems_ne _ _ e,
      fun _ => rfl⟩
  · rename_i y off hm
    obtain ⟨o, rfl⟩ := hp.shape y off hm
    rw [hev s o] at h
    simp only [Val.addr?] at h
    split at h
    · cases h
    · rename_i s₂ hl
      rw [elemDrop?_eq hp.elem h]
      obtain ⟨ei, he, hr⟩ := elem?_of_segOk hp
      have hn : (BitVec.ofNat 32 p.2.init.length).toNat = p.2.init.length := by
        have := hp.len; simp; omega
      have hsl := tableInitLoop_slot (a := .i32) (k := k) _ hl he hlen (by simp; omega)
      have hel := (tableInitLoop_elems _ hl).1
      refine ⟨?_, fun ea' e => by rw [setElem_elems_ne _ _ e, hel], fun ta' => ?_⟩
      · rw [slotAt_setElem, hsl, hn]
        simp only [segSlot, hm, hr]
        congr 1
        congr 1
        exact Nat.zero_add _
      · rw [tableLen_setElem, tableInitLoop_len _ hl]

theorem len_of_tableLen {s s' : Store H} {ta : Nat} (e : tableLen s' ta = tableLen s ta)
    (h : ∀ ti, s.tables[ta]? = some ti → ti.refs.length ≤ 2 ^ 32) :
    ∀ ti, s'.tables[ta]? = some ti → ti.refs.length ≤ 2 ^ 32 := by
  intro ti hti
  unfold tableLen at e
  rw [hti] at e
  cases h' : s.tables[ta]? with
  | none => simp [h'] at e
  | some ti₀ =>
    simp only [h', Option.map_some, Option.some.injEq] at e
    rw [e]
    exact h ti₀ h'

/-- **The slot after all element segments**: the fold of `segSlot` over the segments, from
the slot's contents before them. `addr` gives each segment's element address; they are
distinct, so dropping one segment does not touch the others. -/
theorem initElemList?_slot {ev : Store H → Frame → Expr → Option (Store H × Val)} {f : Frame}
    (hev : ConstOffsets ev f) {R : Nat → List Ref} {ta k : Nat} (addr : Nat → Nat) :
    ∀ {L : List (Nat × Elem)} {s s' : Store H},
      initElemList? ev s f L = some s' →
      (∀ p ∈ L, SegOk s f R p (addr p.1)) →
      L.Pairwise (fun p q => addr p.1 ≠ addr q.1) →
      (∀ ti, s.tables[ta]? = some ti → ti.refs.length ≤ 2 ^ 32) →
      slotAt s' ta k = L.foldl (segSlot f.module R ta k) (slotAt s ta k)
  | [], s, s', h, _, _, _ => by
    simp only [initElemList?, Option.some.injEq] at h
    subst h; rfl
  | p :: L, s, s', h, hok, hpw, hlen => by
    simp only [initElemList?] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      obtain ⟨hsl, hel, htl⟩ := initElemSeg?_slot hev (hok p (by simp)) h₁ (k := k) hlen
      rw [List.foldl_cons, ← hsl]
      refine initElemList?_slot hev addr h (fun q hq => ?_) (List.pairwise_cons.mp hpw).2
        (len_of_tableLen (htl ta) hlen)
      have hq' := hok q (List.mem_cons_of_mem _ hq)
      have hne : addr q.1 ≠ addr p.1 := fun e => (List.pairwise_cons.mp hpw).1 q hq e.symm
      exact ⟨hq'.shape, hq'.elem, by rw [hel _ hne]; exact hq'.inst, hq'.len⟩

end ElemInit

end Silmaril.Wasm.Binaryen
