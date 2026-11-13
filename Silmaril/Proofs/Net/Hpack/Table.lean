module

public import Silmaril.Net.Hpack.Table.Defs

/-!
# HPACK indexing tables: proofs

For `Silmaril.Net.Hpack.Table.Thms` (RFC 7541 §4).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Hpack

open Silmaril.Net.Hpack

theorem tableSize_nil : tableSize [] = 0 := rfl

theorem tableSize_cons (e : Entry) (es : List Entry) :
    tableSize (e :: es) = e.size + tableSize es := by
  simp [tableSize]

theorem tableSize_fitPrefix (cap : Nat) (es : List Entry) : tableSize (fitPrefix cap es) ≤ cap := by
  induction es generalizing cap with
  | nil => simp [fitPrefix, tableSize]
  | cons e es ih =>
    simp only [fitPrefix]
    split
    · rw [tableSize_cons]; have := ih (cap - e.size); omega
    · simp [tableSize]

theorem fitPrefix_prefix (cap : Nat) (es : List Entry) : fitPrefix cap es <+: es := by
  induction es generalizing cap with
  | nil => simp [fitPrefix]
  | cons e es ih =>
    simp only [fitPrefix]
    split
    · exact List.cons_prefix_cons.mpr ⟨rfl, ih _⟩
    · exact List.nil_prefix

theorem fitPrefix_of_le (cap : Nat) (es : List Entry) (h : tableSize es ≤ cap) :
    fitPrefix cap es = es := by
  induction es generalizing cap with
  | nil => rfl
  | cons e es ih =>
    rw [tableSize_cons] at h
    simp only [fitPrefix, show e.size ≤ cap by omega, ↓reduceIte]
    rw [ih _ (by omega)]

/-- `fitPrefix` is the *longest* fitting prefix: the next entry would not fit. -/
theorem fitPrefix_maximal (cap : Nat) (es : List Entry) (e : Entry)
    (h : fitPrefix cap es ++ [e] <+: es) : cap < tableSize (fitPrefix cap es ++ [e]) := by
  induction es generalizing cap with
  | nil => simp [fitPrefix] at h
  | cons x xs ih =>
    simp only [fitPrefix] at h ⊢
    split at h
    · next hx =>
      simp only [hx, ↓reduceIte]
      rw [List.cons_append, List.cons_prefix_cons] at h
      have := ih (cap - x.size) h.2
      rw [List.cons_append, tableSize_cons]
      omega
    · next hx =>
      simp only [hx, ↓reduceIte]
      rw [List.nil_append, List.cons_prefix_cons] at h
      obtain ⟨rfl, -⟩ := h
      simp [tableSize]; omega

theorem insert_valid {t : DynTable} (ht : t.Valid) (e : Entry) : (t.insert e).Valid :=
  ⟨tableSize_fitPrefix _ _, ht.2⟩

theorem setMaxSize_valid {t t' : DynTable} {m : Nat} (h : t.setMaxSize m = some t') :
    t'.Valid := by
  unfold DynTable.setMaxSize at h
  split at h
  · cases h; exact ⟨tableSize_fitPrefix _ _, by assumption⟩
  · cases h

theorem insert_newest {t : DynTable} {e : Entry} (h : e.size ≤ t.maxSize) :
    (t.insert e).lookup (staticLength + 1) = some e := by
  simp [DynTable.insert, DynTable.lookup, fitPrefix, h, staticLength]

theorem insert_empty {t : DynTable} {e : Entry} (h : t.maxSize < e.size) :
    (t.insert e).entries = [] := by
  simp [DynTable.insert, fitPrefix, Nat.not_le.mpr h]

/-- Inserting shifts the surviving older entries one index up (§2.3.3). -/
theorem insert_shift {t : DynTable} {e : Entry} (i : Nat) (x : Entry)
    (hi : (t.insert e).lookup (staticLength + 2 + i) = some x) :
    t.lookup (staticLength + 1 + i) = some x := by
  simp only [DynTable.insert, DynTable.lookup, staticLength] at hi ⊢
  simp only [show ¬ (61 + 2 + i = 0) by omega, show ¬ (61 + 2 + i ≤ 61) by omega,
    ↓reduceIte, show 61 + 2 + i - 61 - 1 = i + 1 by omega] at hi
  simp only [show ¬ (61 + 1 + i = 0) by omega, show ¬ (61 + 1 + i ≤ 61) by omega,
    ↓reduceIte, show 61 + 1 + i - 61 - 1 = i by omega]
  have hp := fitPrefix_prefix t.maxSize (e :: t.entries)
  obtain ⟨rest, hr⟩ := hp
  have hlt : i + 1 < (fitPrefix t.maxSize (e :: t.entries)).length := by
    rcases List.getElem?_eq_some_iff.mp hi with ⟨h, -⟩; exact h
  have : (e :: t.entries)[i + 1]? = some x := by
    rw [← hr, List.getElem?_append_left hlt, hi]
  simpa using this

end Silmaril.Proofs.Net.Hpack
