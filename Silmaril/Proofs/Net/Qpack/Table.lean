module

public import Silmaril.Net.Qpack.Table.Defs
public import Silmaril.Net.Hpack.Table.Thms

/-!
# QPACK dynamic table: proofs

For `Silmaril.Net.Qpack.Table.Thms` (RFC 9204 §3.2).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Qpack

open Silmaril.Net.Qpack
open Silmaril.Net.Hpack (Entry Entry.size tableSize fitPrefix tableSize_fitPrefix fitPrefix_prefix)

theorem tableSize_cons' (e : Entry) (es : List Entry) :
    tableSize (e :: es) = e.size + tableSize es := by
  simp [tableSize]

theorem fitPrefix_length_le (cap : Nat) (es : List Entry) : (fitPrefix cap es).length ≤ es.length :=
  (fitPrefix_prefix cap es).length_le

/-- Every entry has size at least 32 (§4.5.1.1), so a table of size `s` has at most `s / 32`
entries. -/
theorem length_mul_le_tableSize (es : List Entry) : 32 * es.length ≤ tableSize es := by
  induction es with
  | nil => simp [tableSize]
  | cons e es ih =>
    rw [tableSize_cons', List.length_cons]
    have : 32 ≤ e.size := by simp only [Entry.size]; omega
    omega

/-- Reading a surviving entry of a prefix. -/
theorem getElem?_of_prefix {l₁ l₂ : List Entry} (h : l₁ <+: l₂) {k : Nat} {x : Entry}
    (hk : l₁[k]? = some x) : l₂[k]? = some x := by
  obtain ⟨rest, rfl⟩ := h
  have hlt : k < l₁.length := by
    rcases List.getElem?_eq_some_iff.mp hk with ⟨h, -⟩; exact h
  rw [List.getElem?_append_left hlt, hk]

namespace DynTable

theorem insert_valid {t t' : DynTable} {e : Entry} (ht : t.Valid) (h : t.insert e = some t') :
    t'.Valid := by
  unfold DynTable.insert at h
  split at h
  · next he =>
    cases h
    refine ⟨?_, ht.2.1, ?_⟩
    · show tableSize (e :: _) ≤ t.capacity
      rw [tableSize_cons']
      have := tableSize_fitPrefix (t.capacity - e.size) t.entries
      omega
    · show (e :: _).length ≤ _ + 1
      have := fitPrefix_length_le (t.capacity - e.size) t.entries
      have := ht.2.2
      simp only [List.length_cons]; omega
  · cases h

theorem setCapacity_valid {t t' : DynTable} {c : Nat} (ht : t.Valid)
    (h : t.setCapacity c = some t') : t'.Valid := by
  unfold DynTable.setCapacity at h
  split at h
  · next hc =>
    cases h
    exact ⟨tableSize_fitPrefix _ _, hc,
      Nat.le_trans (fitPrefix_length_le _ _) ht.2.2⟩
  · cases h

theorem insert_eq {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    e.size ≤ t.capacity ∧
    t' = { t with entries := e :: fitPrefix (t.capacity - e.size) t.entries,
                  insertCount := t.insertCount + 1 } := by
  unfold DynTable.insert at h
  split at h
  · next he => cases h; exact ⟨he, rfl⟩
  · cases h

theorem insert_eq_none_iff {t : DynTable} {e : Entry} : t.insert e = none ↔ t.capacity < e.size := by
  unfold DynTable.insert
  split
  · next he => simp only [reduceCtorEq, false_iff]; omega
  · next he => simp only [true_iff]; omega

theorem insert_insertCount {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    t'.insertCount = t.insertCount + 1 := by
  obtain ⟨-, rfl⟩ := insert_eq h; rfl

theorem insert_maxCapacity {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    t'.maxCapacity = t.maxCapacity := by
  obtain ⟨-, rfl⟩ := insert_eq h; rfl

theorem insert_lookup_new {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    t'.lookupAbs t.insertCount = some e := by
  obtain ⟨-, rfl⟩ := insert_eq h
  simp [DynTable.lookupAbs]

theorem insert_lookup_old {t t' : DynTable} {e : Entry} (h : t.insert e = some t') {a : Nat}
    (ha : a < t.insertCount) {x : Entry} (hx : t'.lookupAbs a = some x) :
    t.lookupAbs a = some x := by
  obtain ⟨-, rfl⟩ := insert_eq h
  simp only [DynTable.lookupAbs, show a < t.insertCount + 1 by omega, ha, ↓reduceIte,
    show t.insertCount + 1 - 1 - a = (t.insertCount - 1 - a) + 1 by omega,
    List.getElem?_cons_succ] at hx ⊢
  exact getElem?_of_prefix (fitPrefix_prefix _ _) hx

theorem setCapacity_eq {t t' : DynTable} {c : Nat} (h : t.setCapacity c = some t') :
    c ≤ t.maxCapacity ∧ t' = { t with entries := fitPrefix c t.entries, capacity := c } := by
  unfold DynTable.setCapacity at h
  split at h
  · next hc => cases h; exact ⟨hc, rfl⟩
  · cases h

theorem setCapacity_lookup {t t' : DynTable} {c : Nat} (h : t.setCapacity c = some t') {a : Nat}
    {x : Entry} (hx : t'.lookupAbs a = some x) : t.lookupAbs a = some x := by
  obtain ⟨-, rfl⟩ := setCapacity_eq h
  simp only [DynTable.lookupAbs] at hx ⊢
  split at hx
  · next ha =>
    simp only [ha, ↓reduceIte]
    exact getElem?_of_prefix (fitPrefix_prefix _ _) hx
  · cases hx

theorem lookupAbs_isSome_iff (t : DynTable) (a : Nat) :
    (t.lookupAbs a).isSome ↔ t.dropped ≤ a ∧ a < t.insertCount := by
  simp only [DynTable.lookupAbs, DynTable.dropped]
  split
  · next ha =>
    rw [Option.isSome_iff_ne_none, ne_eq, List.getElem?_eq_none_iff]; omega
  · next ha => simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; omega

theorem insert_dropped {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    t.dropped ≤ t'.dropped ∧ t'.dropped ≤ t.insertCount := by
  obtain ⟨-, rfl⟩ := insert_eq h
  have := fitPrefix_length_le (t.capacity - e.size) t.entries
  simp only [DynTable.dropped, List.length_cons]
  omega

theorem setCapacity_dropped {t t' : DynTable} {c : Nat} (h : t.setCapacity c = some t') :
    t.dropped ≤ t'.dropped ∧ t'.dropped ≤ t.insertCount := by
  obtain ⟨-, rfl⟩ := setCapacity_eq h
  have := fitPrefix_length_le c t.entries
  simp only [DynTable.dropped]
  omega

theorem lookupRel_eq {t : DynTable} (ht : t.entries.length ≤ t.insertCount) (r : Nat) :
    t.lookupRel r = t.entries[r]? := by
  simp only [DynTable.lookupRel, DynTable.encoderRelToAbs]
  split
  · next hr =>
    simp only [Option.bind_some, DynTable.lookupAbs, show t.insertCount - 1 - r < t.insertCount by
      omega, ↓reduceIte, show t.insertCount - 1 - (t.insertCount - 1 - r) = r by omega]
  · next hr =>
    simp only [Option.bind_none]
    rw [List.getElem?_eq_none (by omega)]

theorem length_le_maxEntries {t : DynTable} (ht : t.Valid) : t.entries.length ≤ t.maxEntries := by
  have := length_mul_le_tableSize t.entries
  have := ht.1
  have := ht.2.1
  simp only [DynTable.maxEntries]
  omega

end DynTable

theorem relToAbs_absToRel {base a : Nat} (h : a < base) :
    relToAbs base (absToRel base a) = some a := by
  simp only [relToAbs, absToRel, show base - 1 - a < base by omega, ↓reduceIte,
    Option.some.injEq]; omega

theorem absToRel_relToAbs {base r a : Nat} (h : relToAbs base r = some a) :
    a < base ∧ absToRel base a = r := by
  unfold relToAbs at h
  by_cases hr : r < base
  · simp only [hr, ↓reduceIte, Option.some.injEq] at h; subst h; simp only [absToRel]; omega
  · simp only [hr, ↓reduceIte, reduceCtorEq] at h

end Silmaril.Proofs.Net.Qpack
