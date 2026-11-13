module

public import Silmaril.Data.BytesTrie.Defs
import Init.Omega

/-!
# Byte tries: lookup specification and uniqueness of canonical forms
-/

@[expose] public section

namespace Silmaril.Proofs.Data.BytesTrie

open Silmaril.Data Silmaril.Data.BytesTrie

universe u

variable {α : Type u}

namespace Trie

open Silmaril.Data.BytesTrie.Trie

theorem toNat_ne {a b : UInt8} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (e ▸ rfl)

theorem eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) : a = b := UInt8.toNat_inj.mp h

theorem WF.mono {lo lo' : Nat} : ∀ {t : Trie α}, WF lo' t → lo ≤ lo' → WF lo t
  | .nil, _, _ => trivial
  | .node _ _ _ _, ⟨h1, h2, h3⟩, h => ⟨by omega, h2, h3⟩

theorem Canon.mono {lo lo' : Nat} : ∀ {t : Trie α}, Canon lo' t → lo ≤ lo' → Canon lo t
  | .nil, _, _ => trivial
  | .node _ _ _ _, ⟨h1, h2, h3, h4⟩, h => ⟨by omega, h2, h3, h4⟩

theorem Canon.wf : ∀ {lo : Nat} {t : Trie α}, Canon lo t → WF lo t
  | _, .nil, _ => trivial
  | _, .node _ _ _ _, ⟨h1, _, h3, h4⟩ => ⟨h1, Canon.wf h3, Canon.wf h4⟩

/-- Keys below the lower bound are absent. -/
theorem find?_lt : ∀ {lo : Nat} {t : Trie α} {k : UInt8} {ks : List UInt8},
    WF lo t → k.toNat < lo → t.find? k ks = none
  | _, .nil, _, _, _, _ => rfl
  | _, .node b _ _ n, k, ks, ⟨h1, _, h3⟩, hk => by
    have hne : k ≠ b := toNat_ne (by omega)
    simp only [Trie.find?, hne, ite_false]
    exact find?_lt h3 (by omega)

theorem find?_node_none (b : UInt8) (n : Trie α) (k : UInt8) (ks : List UInt8) :
    (node b none nil n).find? k ks = if k = b then none else n.find? k ks := by
  cases ks <;> simp [Trie.find?]

theorem find?_mkNode {b : UInt8} {v : Option α} {c n : Trie α} (hn : WF (b.toNat + 1) n)
    (k : UInt8) (ks : List UInt8) : (mkNode b v c n).find? k ks = (node b v c n).find? k ks := by
  unfold mkNode
  split
  · rw [find?_node_none]
    by_cases h : k = b
    · subst h; simp [Trie.find?_lt hn (Nat.lt_succ_self _)]
    · simp [h]
  · rfl

theorem wf_mkNode {lo : Nat} {b : UInt8} {v : Option α} {c n : Trie α} (h1 : lo ≤ b.toNat)
    (h2 : WF 0 c) (h3 : WF (b.toNat + 1) n) : WF lo (mkNode b v c n) := by
  unfold mkNode
  split
  · exact WF.mono h3 (by omega)
  · exact ⟨h1, h2, h3⟩

theorem canon_mkNode {lo : Nat} {b : UInt8} {v : Option α} {c n : Trie α} (h1 : lo ≤ b.toNat)
    (h2 : Canon 0 c) (h3 : Canon (b.toNat + 1) n) : Canon lo (mkNode b v c n) := by
  unfold mkNode
  split
  · exact Canon.mono h3 (by omega)
  · refine ⟨h1, ?_, h2, h3⟩
    cases v with
    | some _ => exact Or.inl rfl
    | none => cases c with
      | nil => rename_i hx; exact (hx rfl rfl).elim
      | node => exact Or.inr (by simp)

theorem wf_path {lo : Nat} {k : UInt8} : ∀ {ks : List UInt8} {v : Option α} {rest : Trie α},
    lo ≤ k.toNat → WF (k.toNat + 1) rest → WF lo (path k ks v rest)
  | [], _, _, h1, h2 => wf_mkNode h1 trivial h2
  | _ :: _, _, _, h1, h2 => wf_mkNode h1 (wf_path (Nat.zero_le _) trivial) h2

theorem canon_path {lo : Nat} {k : UInt8} : ∀ {ks : List UInt8} {v : Option α} {rest : Trie α},
    lo ≤ k.toNat → Canon (k.toNat + 1) rest → Canon lo (path k ks v rest)
  | [], _, _, h1, h2 => canon_mkNode h1 trivial h2
  | _ :: _, _, _, h1, h2 => canon_mkNode h1 (canon_path (Nat.zero_le _) trivial) h2

theorem find?_path {k : UInt8} : ∀ {ks : List UInt8} {v : Option α} {rest : Trie α},
    WF (k.toNat + 1) rest → ∀ j js,
      (path k ks v rest).find? j js = if j = k ∧ js = ks then v else rest.find? j js
  | [], v, rest, h, j, js => by
    rw [path, find?_mkNode h]
    by_cases hj : j = k
    · subst hj
      have hr : ∀ js, rest.find? j js = none := fun _ => find?_lt h (Nat.lt_succ_self _)
      cases js <;> simp [Trie.find?, hr]
    · simp [Trie.find?, hj]
  | k' :: ks, v, rest, h, j, js => by
    rw [path, find?_mkNode h]
    by_cases hj : j = k
    · subst hj
      have hr : ∀ js, rest.find? j js = none := fun _ => find?_lt h (Nat.lt_succ_self _)
      cases js with
      | nil => simp [Trie.find?, hr]
      | cons j' js' =>
        simp only [Trie.find?, ite_true, find?_path (ks := ks) (v := v) (rest := nil) trivial j' js']
        simp [hr]
    · simp [Trie.find?, hj]

/-- The `alter` specification, for sorted tries. -/
theorem find?_alter (f : Option α → Option α) : ∀ {lo : Nat} {t : Trie α} {k : UInt8}
    {ks : List UInt8}, WF lo t → lo ≤ k.toNat → ∀ j js,
      (t.alter f k ks).find? j js = if j = k ∧ js = ks then f (t.find? k ks) else t.find? j js
  | lo, .nil, k, ks, _, _, j, js => by
    rw [Trie.alter, find?_path (show WF (k.toNat + 1) (nil : Trie α) from trivial)]; simp [Trie.find?]
  | lo, .node b v c n, k, ks, ⟨h1, h2, h3⟩, hk, j, js => by
    unfold Trie.alter
    by_cases hkb : k = b
    · subst hkb
      cases ks with
      | nil =>
        simp only [ite_true]
        rw [find?_mkNode h3]
        by_cases hj : j = k
        · subst hj; cases js <;> simp [Trie.find?]
        · simp [Trie.find?, hj]
      | cons k' ks' =>
        simp only [ite_true]
        rw [find?_mkNode h3]
        by_cases hj : j = k
        · subst hj
          cases js with
          | nil => simp [Trie.find?]
          | cons j' js' =>
            simp only [Trie.find?, ite_true, find?_alter f h2 (Nat.zero_le _) j' js']
            simp
        · simp [Trie.find?, hj]
    · simp only [hkb, ite_false]
      split
      · rename_i hlt
        have hw : WF (k.toNat + 1) (node b v c n) := ⟨by omega, h2, h3⟩
        rw [find?_path hw, find?_lt hw (Nat.lt_succ_self _)]
      · rename_i hge
        have hlt : b.toNat < k.toNat :=
          Nat.lt_of_le_of_ne (by omega) (fun e => hkb (eq_of_toNat e).symm)
        by_cases hj : j = b
        · subst hj
          have hjk : j ≠ k := fun e => hkb e.symm
          simp [Trie.find?, hjk]
        · simp only [Trie.find?, hj, ite_false, hkb]
          exact find?_alter f h3 (by omega) j js

theorem wf_alter (f : Option α → Option α) : ∀ {lo : Nat} {t : Trie α} {k : UInt8}
    {ks : List UInt8}, WF lo t → lo ≤ k.toNat → WF lo (t.alter f k ks)
  | _, .nil, _, _, _, hk => wf_path hk trivial
  | lo, .node b v c n, k, ks, ⟨h1, h2, h3⟩, hk => by
    unfold Trie.alter
    by_cases hkb : k = b
    · subst hkb
      cases ks with
      | nil => simp only [↓reduceIte]; exact wf_mkNode h1 h2 h3
      | cons k' ks' => simp only [↓reduceIte]; exact wf_mkNode h1 (wf_alter f h2 (Nat.zero_le _)) h3
    · simp only [hkb, ite_false]
      split
      · exact wf_path hk ⟨by omega, h2, h3⟩
      · have hlt : b.toNat < k.toNat :=
          Nat.lt_of_le_of_ne (by omega) (fun e => hkb (eq_of_toNat e).symm)
        exact ⟨h1, h2, wf_alter f h3 (by omega)⟩

theorem canon_alter (f : Option α → Option α) : ∀ {lo : Nat} {t : Trie α} {k : UInt8}
    {ks : List UInt8}, Canon lo t → lo ≤ k.toNat → Canon lo (t.alter f k ks)
  | _, .nil, _, _, _, hk => canon_path hk trivial
  | lo, .node b v c n, k, ks, ⟨h1, h0, h2, h3⟩, hk => by
    unfold Trie.alter
    by_cases hkb : k = b
    · subst hkb
      cases ks with
      | nil => simp only [↓reduceIte]; exact canon_mkNode h1 h2 h3
      | cons k' ks' => simp only [↓reduceIte]; exact canon_mkNode h1 (canon_alter f h2 (Nat.zero_le _)) h3
    · simp only [hkb, ite_false]
      split
      · exact canon_path hk ⟨by omega, h0, h2, h3⟩
      · have hlt : b.toNat < k.toNat :=
          Nat.lt_of_le_of_ne (by omega) (fun e => hkb (eq_of_toNat e).symm)
        exact ⟨h1, h0, h2, canon_alter f h3 (by omega)⟩

theorem find?_node_self (b : UInt8) (v : Option α) (c n : Trie α) (k : UInt8) (ks : List UInt8) :
    (node b v c n).find? b (k :: ks) = c.find? k ks := by simp [Trie.find?]

/-- A canonical node stores some value under its own edge. -/
theorem exists_find?_node : ∀ {lo : Nat} {b : UInt8} {v : Option α} {c n : Trie α},
    Canon lo (node b v c n) → ∃ ks x, (node b v c n).find? b ks = some x
  | _, b, some x, _, _, _ => ⟨[], x, by simp [Trie.find?]⟩
  | _, b, none, .nil, _, ⟨_, h, _, _⟩ => by simp at h
  | _, b, none, .node b' v' c' n', _, ⟨_, _, hc, _⟩ => by
    obtain ⟨ks, x, hx⟩ := exists_find?_node hc
    exact ⟨b' :: ks, x, by rw [find?_node_self]; exact hx⟩

/-- **Uniqueness of canonical forms**: canonical tries with the same lookups
are equal. -/
theorem eq_of_find?_eq : ∀ {lo : Nat} {s t : Trie α}, Canon lo s → Canon lo t →
    (∀ k ks, s.find? k ks = t.find? k ks) → s = t
  | _, .nil, .nil, _, _, _ => rfl
  | _, .nil, .node b v c n, _, ht, h => by
    obtain ⟨ks, x, hx⟩ := exists_find?_node ht
    rw [← h] at hx; simp [Trie.find?] at hx
  | _, .node b v c n, .nil, hs, _, h => by
    obtain ⟨ks, x, hx⟩ := exists_find?_node hs
    rw [h] at hx; simp [Trie.find?] at hx
  | lo, .node b v c n, .node b' v' c' n', hs, ht, h => by
    have hb : b = b' := by
      apply eq_of_toNat
      apply Nat.le_antisymm
      · apply Nat.le_of_not_lt; intro hlt
        obtain ⟨ks, x, hx⟩ := exists_find?_node ht
        rw [← h] at hx
        have hne : b' ≠ b := toNat_ne (by omega)
        simp only [Trie.find?, hne, ite_false] at hx
        rw [find?_lt (Canon.wf hs.2.2.2) (by omega)] at hx; cases hx
      · apply Nat.le_of_not_lt; intro hlt
        obtain ⟨ks, x, hx⟩ := exists_find?_node hs
        rw [h] at hx
        have hne : b ≠ b' := toNat_ne (by omega)
        simp only [Trie.find?, hne, ite_false] at hx
        rw [find?_lt (Canon.wf ht.2.2.2) (by omega)] at hx; cases hx
    subst hb
    have hv : v = v' := by simpa [Trie.find?] using h b []
    have hc : c = c' := eq_of_find?_eq hs.2.2.1 ht.2.2.1 fun k ks => by
      simpa [Trie.find?] using h b (k :: ks)
    have hn : n = n' := eq_of_find?_eq hs.2.2.2 ht.2.2.2 fun k ks => by
      by_cases hk : k = b
      · subst hk
        rw [find?_lt (Canon.wf hs.2.2.2) (Nat.lt_succ_self _), find?_lt (Canon.wf ht.2.2.2) (Nat.lt_succ_self _)]
      · simpa [Trie.find?, hk] using h k ks
    rw [hv, hc, hn]

theorem canonB_iff : ∀ {lo : Nat} {t : Trie α}, t.canonB lo = true ↔ Canon lo t
  | _, .nil => by simp [Trie.canonB, Trie.Canon]
  | lo, .node b v c n => by
    have hc : (v.isSome || (match c with | nil => false | node .. => true)) = true ↔
        (v.isSome ∨ c ≠ nil) := by
      cases c <;> simp
    simp only [Trie.canonB, Trie.Canon, Bool.and_eq_true, Nat.ble_eq, canonB_iff, and_assoc]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, hc.mp h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, hc.mpr h2, h3⟩⟩

theorem beq_iff [DecidableEq α] : ∀ {s t : Trie α}, s.beq t = true ↔ s = t
  | .nil, .nil => by simp [Trie.beq]
  | .nil, .node .. => by simp [Trie.beq]
  | .node .., .nil => by simp [Trie.beq]
  | .node b v c n, .node b' v' c' n' => by
    have hb : Nat.beq b.toNat b'.toNat = true ↔ b = b' := by
      rw [Nat.beq_eq, UInt8.toNat_inj]
    have hv : (match v, v' with
        | none, none => true
        | some x, some y => decide (x = y)
        | _, _ => false) = true ↔ v = v' := by
      cases v <;> cases v' <;> simp
    simp only [Trie.beq, Bool.and_eq_true, hb, beq_iff, node.injEq, and_assoc]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, hv.mp h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, hv.mpr h2, h3⟩⟩

end Trie

/-! ## Tries with a root value -/

theorem Canon.wf {t : BytesTrie α} (h : t.Canon) : t.WF := Trie.Canon.wf h

theorem find?_alter {t : BytesTrie α} (h : t.WF) (ks : List UInt8) (f : Option α → Option α)
    (js : List UInt8) :
    (t.alter ks f).find? js = if js = ks then f (t.find? ks) else t.find? js := by
  cases ks with
  | nil => cases js <;> simp [BytesTrie.alter, BytesTrie.find?]
  | cons k ks =>
    cases js with
    | nil => simp [BytesTrie.alter, BytesTrie.find?]
    | cons j js =>
      simp only [BytesTrie.alter, BytesTrie.find?]
      rw [Trie.find?_alter f h (Nat.zero_le _)]
      simp

theorem wf_alter {t : BytesTrie α} (h : t.WF) (ks : List UInt8) (f : Option α → Option α) :
    (t.alter ks f).WF := by
  cases ks with
  | nil => exact h
  | cons k ks => exact Trie.wf_alter f h (Nat.zero_le _)

theorem canon_alter {t : BytesTrie α} (h : t.Canon) (ks : List UInt8) (f : Option α → Option α) :
    (t.alter ks f).Canon := by
  cases ks with
  | nil => exact h
  | cons k ks => exact Trie.canon_alter f h (Nat.zero_le _)

theorem eq_of_find?_eq {s t : BytesTrie α} (hs : s.Canon) (ht : t.Canon)
    (h : ∀ ks, s.find? ks = t.find? ks) : s = t := by
  obtain ⟨r, k⟩ := s
  obtain ⟨r', k'⟩ := t
  have hr : r = r' := h []
  have hk : k = k' := Trie.eq_of_find?_eq hs ht fun j js => h (j :: js)
  rw [hr, hk]

theorem canon_alterAll {t : BytesTrie α} (h : t.Canon) (keys : List (List UInt8))
    (f : List UInt8 → Option α) : (t.alterAll keys f).Canon := by
  induction keys generalizing t with
  | nil => exact h
  | cons ks keys ih => exact ih (canon_alter h ks _)

theorem find?_alterAll {t : BytesTrie α} (h : t.WF) (keys : List (List UInt8))
    (f : List UInt8 → Option α) (js : List UInt8) :
    (t.alterAll keys f).find? js = if js ∈ keys then f js else t.find? js := by
  induction keys generalizing t with
  | nil => simp [BytesTrie.alterAll]
  | cons ks keys ih =>
    show (alterAll (t.alter ks fun _ => f ks) keys f).find? js = _
    rw [ih (wf_alter h ks _), find?_alter h]
    by_cases h1 : js ∈ keys
    · simp [h1]
    · by_cases h2 : js = ks
      · subst h2; simp
      · simp [h1, h2]

theorem canon_empty : (empty : BytesTrie α).Canon := trivial

theorem find?_empty (ks : List UInt8) : (empty : BytesTrie α).find? ks = none := by
  cases ks <;> rfl

/-- Every finitely supported function is the lookup of a canonical trie. -/
theorem exists_of_finite (f : List UInt8 → Option α) (keys : List (List UInt8))
    (hf : ∀ ks, ks ∉ keys → f ks = none) :
    ∃ t : BytesTrie α, t.Canon ∧ ∀ ks, t.find? ks = f ks :=
  ⟨empty.alterAll keys f, canon_alterAll canon_empty keys f, fun ks => by
    rw [find?_alterAll (Canon.wf canon_empty), find?_empty]
    by_cases h : ks ∈ keys
    · simp [h]
    · simp [h, hf ks h]⟩

end Silmaril.Proofs.Data.BytesTrie
