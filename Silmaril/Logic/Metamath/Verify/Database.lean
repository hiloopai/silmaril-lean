module

public import Silmaril.Logic.Metamath.Derivation

@[expose] public section

/-!
# Checked databases

A checked database is the sequence of its assertions (`$a` and `$p`
statements) with their extended frames. `Database.Sound` is the correctness
property the checker establishes: every assertion is well formed, and every
theorem is derivable from the assertions before it.

Derivability from earlier axioms and theorems becomes derivability from the
earlier axioms alone as soon as cut is admissible (`CutAdmissible`): theorems
may then be removed one at a time, latest first
(`Database.Sound.derivable_axioms`).
-/

namespace Silmaril.Logic.Metamath.Verify

universe u

/-- Whether an assertion is an axiom (`$a`) or a theorem (`$p`). -/
inductive Kind where
  | axiom
  | theorem
  deriving DecidableEq, Repr, Inhabited

/-- A checked assertion with its label. -/
structure Entry (C V : Type u) where
  label : String
  kind : Kind
  assertion : Assertion C V
  deriving Repr

/-- The assertions of a checked database, in order. -/
structure Database (C V : Type u) where
  entries : Array (Entry C V)
  deriving Inhabited

variable {C V : Type u}

namespace Database

/-- Append an entry. -/
def push (db : Database C V) (e : Entry C V) : Database C V := ⟨db.entries.push e⟩

@[simp] theorem entries_push (db : Database C V) (e : Entry C V) :
    (db.push e).entries = db.entries.push e := rfl

/-- The assertions before position `i`. -/
def before (db : Database C V) (i : Nat) : Set (Assertion C V) :=
  {B | ∃ j, ∃ hj : j < db.entries.size, j < i ∧ db.entries[j].assertion = B}

/-- The assertions of the given kind before position `i`. -/
def kindBefore (db : Database C V) (k : Kind) (i : Nat) : Set (Assertion C V) :=
  {B | ∃ j, ∃ hj : j < db.entries.size,
    j < i ∧ db.entries[j].kind = k ∧ db.entries[j].assertion = B}

/-- The axioms of the database. -/
def axioms (db : Database C V) : Set (Assertion C V) := db.kindBefore .axiom db.entries.size

/-- The database is correct: its assertions are well formed and each theorem
is derivable from the assertions before it. -/
structure Sound (db : Database C V) : Prop where
  wellFormed : ∀ i (hi : i < db.entries.size), db.entries[i].assertion.WellFormed
  derivable : ∀ i (hi : i < db.entries.size), db.entries[i].kind = .theorem →
    Derivable (db.before i) db.entries[i].assertion

theorem before_push (db : Database C V) (e : Entry C V) {i : Nat} (hi : i ≤ db.entries.size) :
    (db.push e).before i = db.before i := by
  ext B
  simp only [before, Set.mem_ofPred_eq, entries_push, Array.size_push]
  constructor
  · rintro ⟨j, hj, hji, rfl⟩
    exact ⟨j, by omega, hji, by rw [Array.getElem_push_lt (by omega)]⟩
  · rintro ⟨j, hj, hji, rfl⟩
    exact ⟨j, by omega, hji, by rw [Array.getElem_push_lt hj]⟩

theorem mem_before_size {db : Database C V} {e : Entry C V} (he : e ∈ db.entries) :
    e.assertion ∈ db.before db.entries.size := by
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
  exact ⟨j, hj, hj, rfl⟩

theorem before_mono (db : Database C V) {i j : Nat} (h : i ≤ j) : db.before i ⊆ db.before j := by
  rintro B ⟨l, hl, hli, rfl⟩
  exact ⟨l, hl, by omega, rfl⟩

theorem before_subset_push (db : Database C V) (e : Entry C V) :
    db.before db.entries.size ⊆ (db.push e).before (db.push e).entries.size := by
  rw [← before_push db e le_rfl]
  exact before_mono _ (by simp)

theorem mem_before_push (db : Database C V) (e : Entry C V) :
    e.assertion ∈ (db.push e).before (db.push e).entries.size :=
  ⟨db.entries.size, by simp, by simp, by simp⟩

theorem sound_empty : Sound (⟨#[]⟩ : Database C V) :=
  ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩

/-- Appending a well-formed assertion that is an axiom or is derivable from
the whole database keeps it sound. -/
theorem Sound.push {db : Database C V} (hdb : db.Sound) {e : Entry C V}
    (wf : e.assertion.WellFormed)
    (hd : e.kind = .theorem → Derivable (db.before db.entries.size) e.assertion) :
    (db.push e).Sound := by
  refine ⟨fun i hi => ?_, fun i hi hk => ?_⟩
  · simp only [entries_push] at hi ⊢
    rw [Array.getElem_push]
    split
    · exact hdb.wellFormed i ‹_›
    · exact wf
  · simp only [entries_push, Array.size_push] at hi hk ⊢
    rw [before_push db e (by omega)]
    rw [Array.getElem_push] at hk ⊢
    split at hk
    · rename_i h
      rw [dite_eq_left h]
      exact hdb.derivable i h hk
    · rename_i h
      rw [dite_eq_right h]
      obtain rfl : i = db.entries.size := by omega
      exact hd hk

theorem before_eq_union (db : Database C V) (i : Nat) :
    db.before i = db.kindBefore .axiom i ∪ db.kindBefore .theorem i := by
  ext B
  simp only [before, kindBefore, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, hji, rfl⟩
    cases h : db.entries[j].kind
    · exact Or.inl ⟨j, hj, hji, h, rfl⟩
    · exact Or.inr ⟨j, hj, hji, h, rfl⟩
  · rintro (⟨j, hj, hji, -, rfl⟩ | ⟨j, hj, hji, -, rfl⟩) <;> exact ⟨j, hj, hji, rfl⟩

theorem kindBefore_mono (db : Database C V) (k : Kind) {i j : Nat} (h : i ≤ j) :
    db.kindBefore k i ⊆ db.kindBefore k j := by
  rintro B ⟨l, hl, hli, hk, rfl⟩
  exact ⟨l, hl, by omega, hk, rfl⟩

theorem kindBefore_succ (db : Database C V) (k : Kind) (i : Nat) (hi : i < db.entries.size) :
    db.kindBefore k (i + 1) =
      if db.entries[i].kind = k then insert db.entries[i].assertion (db.kindBefore k i)
      else db.kindBefore k i := by
  ext B
  simp only [kindBefore, Set.mem_ofPred_eq]
  split
  · rename_i hk
    simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, hji, hjk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
      · exact Or.inr ⟨j, hj, hji, hjk, rfl⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨j, hj, hji, hjk, rfl⟩)
      · exact ⟨i, hi, by omega, hk, rfl⟩
      · exact ⟨j, hj, by omega, hjk, rfl⟩
  · rename_i hk
    constructor
    · rintro ⟨j, hj, hji, hjk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
      · exact ⟨j, hj, hji, hjk, rfl⟩
      · exact absurd hjk hk
    · rintro ⟨j, hj, hji, hjk, rfl⟩
      exact ⟨j, hj, by omega, hjk, rfl⟩

end Database

/-- Cut admissibility: a derivable well-formed assertion may be added to a set
of well-formed axioms without changing what is derivable. -/
def CutAdmissible (C V : Type u) : Prop :=
  ∀ (Γ : Set (Assertion C V)) (A B : Assertion C V), (∀ D ∈ Γ, D.WellFormed) →
    B.WellFormed → A.WellFormed → Derivable Γ B → Derivable (insert B Γ) A → Derivable Γ A

namespace Database

/-- With cut admissible, each theorem of a sound database is derivable from the
axioms before it. -/
theorem Sound.derivable_axioms (hcut : CutAdmissible C V) {db : Database C V}
    (hdb : db.Sound) :
    ∀ i (hi : i < db.entries.size), db.entries[i].kind = .theorem →
      Derivable (db.kindBefore .axiom i) db.entries[i].assertion := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hk
    have wfΓ : ∀ k, ∀ D ∈ db.kindBefore .axiom i ∪ db.kindBefore .theorem k,
        D.WellFormed := by
      rintro k D (⟨j, hj, -, -, rfl⟩ | ⟨j, hj, -, -, rfl⟩) <;> exact hdb.wellFormed j hj
    -- Remove the theorems before `i`, latest first.
    have key : ∀ n, n ≤ i →
        Derivable (db.kindBefore .axiom i ∪ db.kindBefore .theorem (i - n))
          db.entries[i].assertion := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [Nat.sub_zero, ← before_eq_union]
        exact hdb.derivable i hi hk
      | succ n ihn =>
        intro hn
        have h := ihn (by omega)
        obtain ⟨k, hk1, hk2⟩ : ∃ k, i - n = k + 1 ∧ i - (n + 1) = k := ⟨i - (n + 1), by omega, rfl⟩
        rw [hk1] at h
        rw [hk2]
        have hkd : k < db.entries.size := by omega
        rw [kindBefore_succ db _ k hkd] at h
        split at h
        · rename_i hkt
          have hB : Derivable (db.kindBefore .axiom i ∪ db.kindBefore .theorem k)
              db.entries[k].assertion :=
            (ih k (by omega) hkd hkt).mono
              (Set.subset_union_of_subset_left (kindBefore_mono db _ (by omega)) _)
          refine hcut _ _ _ (wfΓ k) (hdb.wellFormed k hkd) (hdb.wellFormed i hi) hB ?_
          rwa [Set.union_insert] at h
        · exact h
    have := key i le_rfl
    rw [Nat.sub_self] at this
    refine this.mono ?_
    rintro B (hB | ⟨j, hj, hj0, -, -⟩)
    · exact hB
    · omega

end Database

end Silmaril.Logic.Metamath.Verify
