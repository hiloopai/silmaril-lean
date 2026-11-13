module

public import Silmaril.Wasm.Wac.Nest.Defs
public import Silmaril.Proofs.Wasm.Wac.Graph

/-!
# The canonical import order

* `charsLe` is a total order on character lists (`charsLe_total`, `charsLe_trans`,
  `charsLe_antisymm`);
* `sortIface_eq_of_lookup`: two interfaces with distinct names and the same lookups have
  the same sorted form;
* `lookup_dedup`: merging duplicate imports keeps the first entry of every name.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

/-! ## The order -/

theorem charsLe_total : ∀ a b : List Char, charsLe a b = true ∨ charsLe b a = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | a :: as, b :: bs => by
    rcases Nat.lt_trichotomy a.toNat b.toNat with h | h | h
    · exact Or.inl (by simp [charsLe, h])
    · rcases charsLe_total as bs with h' | h'
      · exact Or.inl (by simp [charsLe, h, h'])
      · exact Or.inr (by simp [charsLe, h, h'])
    · exact Or.inr (by simp [charsLe, h])

theorem charsLe_cons {a b : Char} {as bs : List Char} :
    charsLe (a :: as) (b :: bs) = true ↔ a.toNat < b.toNat ∨ (a.toNat = b.toNat ∧ charsLe as bs = true) := by
  simp [charsLe]

theorem charsLe_trans : ∀ a b c : List Char, charsLe a b = true → charsLe b c = true →
    charsLe a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => absurd h (by simp [charsLe])
  | _ :: _, _ :: _, [], _, h => absurd h (by simp [charsLe])
  | a :: as, b :: bs, c :: cs, h₁, h₂ => by
    rw [charsLe_cons] at h₁ h₂ ⊢
    rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
    · exact Or.inl (Nat.lt_trans h₁ h₂)
    · exact Or.inl (e₂ ▸ h₁)
    · exact Or.inl (e₁ ▸ h₂)
    · exact Or.inr ⟨e₁.trans e₂, charsLe_trans as bs cs h₁ h₂⟩

theorem charsLe_antisymm : ∀ a b : List Char, charsLe a b = true → charsLe b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (by simp [charsLe])
  | _ :: _, [], h, _ => absurd h (by simp [charsLe])
  | a :: as, b :: bs, h₁, h₂ => by
    rw [charsLe_cons] at h₁ h₂
    rcases h₁ with h₁ | ⟨e₁, h₁⟩
    · rcases h₂ with h₂ | ⟨e₂, _⟩ <;> omega
    · rcases h₂ with h₂ | ⟨_, h₂⟩
      · omega
      · rw [Char.toNat_inj.1 e₁, charsLe_antisymm as bs h₁ h₂]

/-- Inserting two imports of different names commutes. -/
theorem insertIface_comm {p q : String × FuncTy} (h : p.1 ≠ q.1) :
    ∀ l : Iface, insertIface p (insertIface q l) = insertIface q (insertIface p l)
  | [] => by
    have hne : ¬ (charsLe p.1.toList q.1.toList = true ∧ charsLe q.1.toList p.1.toList = true) :=
      fun ⟨h₁, h₂⟩ => h (String.toList_inj.1 (charsLe_antisymm _ _ h₁ h₂))
    rcases charsLe_total p.1.toList q.1.toList with hpq | hqp
    · have hqp : charsLe q.1.toList p.1.toList = false := by simpa using fun h' => hne ⟨hpq, h'⟩
      simp [insertIface, hpq, hqp]
    · have hpq : charsLe p.1.toList q.1.toList = false := by simpa using fun h' => hne ⟨h', hqp⟩
      simp [insertIface, hpq, hqp]
  | r :: l => by
    have hne : ¬ (charsLe p.1.toList q.1.toList = true ∧ charsLe q.1.toList p.1.toList = true) :=
      fun ⟨h₁, h₂⟩ => h (String.toList_inj.1 (charsLe_antisymm _ _ h₁ h₂))
    have ih := insertIface_comm h l
    by_cases hp : charsLe p.1.toList r.1.toList = true <;>
      by_cases hq : charsLe q.1.toList r.1.toList = true
    · rcases charsLe_total p.1.toList q.1.toList with hpq | hqp
      · have hqp : charsLe q.1.toList p.1.toList = false := by simpa using fun h' => hne ⟨hpq, h'⟩
        simp [insertIface, hp, hq, hpq, hqp]
      · have hpq : charsLe p.1.toList q.1.toList = false := by simpa using fun h' => hne ⟨h', hqp⟩
        simp [insertIface, hp, hq, hpq, hqp]
    · have hqp : charsLe q.1.toList p.1.toList = false := by
        simpa using fun h' => hq (charsLe_trans _ _ _ h' hp)
      simp [insertIface, hp, hq, hqp]
    · have hpq : charsLe p.1.toList q.1.toList = false := by
        simpa using fun h' => hp (charsLe_trans _ _ _ h' hq)
      simp [insertIface, hp, hq, hpq]
    · simp [insertIface, hp, hq, ih]

/-- Sorting is invariant under permutations of interfaces with distinct names. -/
theorem sortIface_perm {l₁ l₂ : Iface} (hp : l₁.Perm l₂) (hn : (names l₁).Nodup) :
    sortIface l₁ = sortIface l₂ := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    have hn' : (names _).Nodup := (List.nodup_cons.1 hn).2
    simp only [sortIface, ih hn']
  | swap x y l =>
    have hxy : y.1 ≠ x.1 := fun h => (List.nodup_cons.1 hn).1 (by simp [h])
    simp only [sortIface]
    exact insertIface_comm hxy _
  | trans h₁₂ _ ih₁ ih₂ =>
    have hn₂ : (names _).Nodup := (h₁₂.map Prod.fst).nodup_iff.1 hn
    exact (ih₁ hn).trans (ih₂ hn₂)

theorem mem_iff_lookup : ∀ {l : Iface}, (names l).Nodup → ∀ p : String × FuncTy,
    p ∈ l ↔ l.lookup p.1 = some p.2
  | [], _, p => by simp
  | q :: l, hn, p => by
    have hq : q.1 ∉ names l := (List.nodup_cons.1 hn).1
    have ih := mem_iff_lookup (List.nodup_cons.1 hn).2 p
    by_cases h : p.1 = q.1
    · have hb : (p.1 == q.1) = true := beq_iff_eq.2 h
      have hnot : p ∉ l := fun hp => hq (h ▸ List.mem_map_of_mem hp)
      simp only [List.mem_cons, List.lookup, hb, hnot, or_false, Option.some.injEq]
      exact ⟨fun e => e ▸ rfl, fun e => Prod.ext h e.symm⟩
    · have hb : (p.1 == q.1) = false := beq_eq_false_iff_ne.2 h
      have hne : p ≠ q := fun e => h (e ▸ rfl)
      simp only [List.mem_cons, List.lookup, hb, hne, false_or]
      exact ih

/-- **Two interfaces with distinct names and the same lookups sort alike.** -/
theorem sortIface_eq_of_lookup {l₁ l₂ : Iface} (h₁ : (names l₁).Nodup) (h₂ : (names l₂).Nodup)
    (hl : ∀ x, l₁.lookup x = l₂.lookup x) : sortIface l₁ = sortIface l₂ := by
  have hp : l₁.Perm l₂ := (List.perm_ext_iff_of_nodup (List.Nodup.of_map _ h₁)
    (List.Nodup.of_map _ h₂)).2 fun p => by
      rw [mem_iff_lookup h₁, mem_iff_lookup h₂, hl]
  exact sortIface_perm hp h₁

/-! ## Deduplication -/

theorem lookup_filter_ne {x y : String} (h : x ≠ y) :
    ∀ l : Iface, (l.filter fun r => r.1 != y).lookup x = l.lookup x
  | [] => rfl
  | r :: l => by
    have ih := lookup_filter_ne h l
    by_cases hr : r.1 = y
    · have hxy : (x == y) = false := beq_eq_false_iff_ne.2 h
      simp [List.filter, hr, List.lookup, hxy, ih]
    · have hb : (r.1 != y) = true := by simpa using hr
      simp only [List.filter, hb, List.lookup, ih]

theorem lookup_dedup : ∀ (l : Iface) (x : String), (dedup l).lookup x = l.lookup x
  | [], _ => rfl
  | p :: l, x => by
    by_cases h : x = p.1
    · simp [dedup, List.lookup, h]
    · have hb : (x == p.1) = false := beq_eq_false_iff_ne.2 h
      simp only [dedup, List.lookup, hb, lookup_filter_ne h, lookup_dedup l x]

end Silmaril.Wasm.Wac.NestProof
