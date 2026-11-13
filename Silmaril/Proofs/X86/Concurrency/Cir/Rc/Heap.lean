module

public import Silmaril.X86.Concurrency.Cir.Rc.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Thms

/-!
# Proofs: heap and ghost-cell lemmas

* the fixed-point helpers `safe_post`, `safe_intro` and the silent `safe_assign`, and the heap
  lemmas on `Heap.union`, `Heap.single` and `∗`, **restated** from
  `Proofs/…/Mutex/Frame.lean` (another topic's proofs module, not imported);
* the ghost cells: `slot` decodes `gA`/`gB`, the ledger's value at each cell, and how the ledger
  changes when a slot is taken into use or given back.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Rc
open Silmaril.X86.Sep.BI.SepAlg (pmapUnion pmapDisjoint)

/-! ## The fixed point, restated (as in the pool and mutex proofs) -/

theorem labOk_mono {I : HProp} {K K' : Heap → Prop} (hK : ∀ h, K h → K' h) {l : Lab} {h : Heap}
    (H : LabOk I K l h) : LabOk I K' l h := by
  obtain ⟨hm, hna, hat⟩ := H
  refine ⟨hm, fun hn => ⟨(hna hn).1, fun hok => hK _ ((hna hn).2 hok)⟩, fun hn hI hIi hd => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hat hn hI hIi hd
  refine ⟨h1, h2, fun hok => ?_⟩
  obtain ⟨h', hI', a, b, c, d, e⟩ := h3 hok
  exact ⟨h', hI', a, b, c, hK _ d, e⟩

theorem safeF_mono {I : HProp} {Q : Regs → HProp} {R R' : Stmt → Regs → Heap → Prop}
    (hR : ∀ s rs h, R s rs h → R' s rs h) {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q R s rs h) : SafeF I Q R' s rs h :=
  ⟨H.1, fun s' rs' hs => hR _ _ _ (H.2.1 s' rs' hs),
    fun l s' rs' hs => labOk_mono (hR _ _) (H.2.2 l s' rs' hs)⟩

theorem safe_post {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : Csl.Safe I Q s rs h) : SafeF I Q (Csl.Safe I Q) s rs h := by
  obtain ⟨R, hR, hpost⟩ := H
  exact safeF_mono (fun s rs h hr => ⟨R, hr, hpost⟩) (hpost _ _ _ hR)

theorem safe_intro {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q (Csl.Safe I Q) s rs h) : Csl.Safe I Q s rs h := by
  refine ⟨fun s' rs' h' => (s' = s ∧ rs' = rs ∧ h' = h) ∨ Csl.Safe I Q s' rs' h',
    Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
  rintro s' rs' h' (⟨rfl, rfl, rfl⟩ | hs)
  · exact safeF_mono (fun _ _ _ x => Or.inr x) H
  · exact safeF_mono (fun _ _ _ x => Or.inr x) (safe_post hs)

/-- **A silent register assignment.** -/
theorem safe_assign {I : HProp} {Q : Regs → HProp} {d : Reg} {e : Expr} {rs : Regs} {h : Heap}
    (hq : Q (rs.set d (e.eval rs)) h) : Csl.Safe I Q (.assign d e) rs h := by
  refine safe_intro ⟨(fun e => by cases e), (fun s' rs' hs => ?_), (fun l s' rs' hs => by cases hs)⟩
  cases hs
  exact safe_skip hq

/-! ## Heaps -/

theorem union_apply (h₁ h₂ : Heap) (a : Nat) :
    Heap.union h₁ h₂ a = match h₁ a with | some v => some v | none => h₂ a := by
  simp only [Heap.union, pmapUnion]; cases h₁ a <;> rfl

theorem single_apply (a v x : Nat) : Heap.single a v x = if x = a then some v else none := by
  simp only [Heap.single]

theorem union_none {h₁ h₂ : Heap} {a : Nat} (h : h₁ a = none) : Heap.union h₁ h₂ a = h₂ a := by
  simp [union_apply, h]

theorem union_some {h₁ h₂ : Heap} {a v : Nat} (h : h₁ a = some v) :
    Heap.union h₁ h₂ a = some v := by
  simp [union_apply, h]

theorem union_eq_none {h₁ h₂ : Heap} {a : Nat} :
    Heap.union h₁ h₂ a = none ↔ h₁ a = none ∧ h₂ a = none := by
  cases e : h₁ a <;> simp [union_apply, e]

theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext x; simp [union_apply, Heap.empty]

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext x; cases e : h x <;> simp [union_apply, e, Heap.empty]

theorem disjoint_empty (h : Heap) : Heap.Disjoint Heap.empty h := fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.Disjoint h Heap.empty := fun _ => Or.inr rfl

theorem disjoint_symm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) : Heap.Disjoint h₂ h₁ :=
  fun a => (d a).symm

theorem union_comm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  funext a
  rcases d a with e | e
  · rw [union_none e]; cases e' : h₂ a <;> simp [union_apply, e, e']
  · rw [union_none (h₁ := h₂) e]; cases e' : h₁ a <;> simp [union_apply, e, e']

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by
  funext a; simp only [union_apply]; cases h₁ a <;> rfl

/-- Disjointness from a union. -/
theorem disjoint_union_left {h₁ h₂ h : Heap} :
    Heap.Disjoint (Heap.union h₁ h₂) h ↔ Heap.Disjoint h₁ h ∧ Heap.Disjoint h₂ h := by
  constructor
  · intro d
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> rcases d a with e | e
    · exact Or.inl (union_eq_none.mp e).1
    · exact Or.inr e
    · exact Or.inl (union_eq_none.mp e).2
    · exact Or.inr e
  · rintro ⟨d₁, d₂⟩ a
    rcases d₁ a with e₁ | e₁
    · rcases d₂ a with e₂ | e₂
      · exact Or.inl (union_eq_none.mpr ⟨e₁, e₂⟩)
      · exact Or.inr e₂
    · exact Or.inr e₁

theorem disjoint_union_right {h₁ h₂ h : Heap} :
    Heap.Disjoint h (Heap.union h₁ h₂) ↔ Heap.Disjoint h h₁ ∧ Heap.Disjoint h h₂ := by
  constructor
  · intro d
    have := disjoint_union_left.mp (disjoint_symm d)
    exact ⟨disjoint_symm this.1, disjoint_symm this.2⟩
  · rintro ⟨d₁, d₂⟩
    exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm d₁, disjoint_symm d₂⟩)

theorem disjoint_single {a v b w : Nat} (h : a ≠ b) :
    Heap.Disjoint (Heap.single a v) (Heap.single b w) := by
  intro x
  by_cases hx : x = a
  · subst hx; exact Or.inr (by simp [single_apply, h])
  · exact Or.inl (by simp [single_apply, hx])

theorem disjoint_single_left {a v : Nat} {h : Heap} (e : h a = none) :
    Heap.Disjoint (Heap.single a v) h := by
  intro x
  by_cases hx : x = a
  · subst hx; exact Or.inr e
  · exact Or.inl (by simp [single_apply, hx])

/-- Disjoint heaps do not share a mapped cell. -/
theorem disjoint_some {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) {a : Nat}
    (e₁ : (h₁ a).isSome) (e₂ : (h₂ a).isSome) : False := by
  rcases d a with e | e <;> simp [e] at e₁ e₂

theorem sep_iff {P Q : HProp} {h : Heap} :
    (P ∗ Q) h ↔ ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P h₁ ∧ Q h₂ := Iff.rfl

theorem sep_comm {P Q : HProp} {h : Heap} (H : (P ∗ Q) h) : (Q ∗ P) h := by
  obtain ⟨h₁, h₂, d, rfl, p, q⟩ := sep_iff.mp H
  exact sep_iff.mpr ⟨h₂, h₁, disjoint_symm d, union_comm d, q, p⟩

theorem sep_emp {P : HProp} {h : Heap} (H : P h) : (P ∗ hemp) h :=
  sep_iff.mpr ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, H, rfl⟩

theorem le_union_left {h₁ h₂ : Heap} : Heap.Le h₁ (Heap.union h₁ h₂) :=
  fun _ _ e => union_some e

theorem le_union_right {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) :
    Heap.Le h₂ (Heap.union h₁ h₂) := by
  rw [union_comm d]; exact le_union_left


theorem touches_of_wval {l : Lab} {a : Nat} (h : (l.wval a).isSome) : l.Touches a := Or.inr h

theorem sep_assoc {P Q R : HProp} {h : Heap} : ((P ∗ Q) ∗ R) h ↔ (P ∗ Q ∗ R) h := by
  constructor
  · intro H
    obtain ⟨h12, h3, d, rfl, H12, r⟩ := sep_iff.mp H
    obtain ⟨h1, h2, d12, rfl, p, q⟩ := sep_iff.mp H12
    obtain ⟨d1, d2⟩ := disjoint_union_left.mp d
    exact sep_iff.mpr ⟨h1, Heap.union h2 h3, disjoint_union_right.mpr ⟨d12, d1⟩,
      union_assoc _ _ _, p, sep_iff.mpr ⟨h2, h3, d2, rfl, q, r⟩⟩
  · intro H
    obtain ⟨h1, h23, d, rfl, p, H23⟩ := sep_iff.mp H
    obtain ⟨h2, h3, d23, rfl, q, r⟩ := sep_iff.mp H23
    obtain ⟨d1, d2⟩ := disjoint_union_right.mp d
    exact sep_iff.mpr ⟨Heap.union h1 h2, h3, disjoint_union_left.mpr ⟨d2, d23⟩,
      (union_assoc _ _ _).symm, sep_iff.mpr ⟨h1, h2, d1, rfl, p, q⟩, r⟩

theorem sep_mono {P P' Q Q' : HProp} (hP : ∀ h, P h → P' h) (hQ : ∀ h, Q h → Q' h) {h : Heap}
    (H : (P ∗ Q) h) : (P' ∗ Q') h := by
  obtain ⟨h1, h2, d, rfl, p, q⟩ := sep_iff.mp H
  exact sep_iff.mpr ⟨h1, h2, d, rfl, hP _ p, hQ _ q⟩

theorem sep_comm_iff {P Q : HProp} {h : Heap} : (P ∗ Q) h ↔ (Q ∗ P) h :=
  ⟨sep_comm, sep_comm⟩

/-! ## Ghost cells -/

theorem gbase_pos : 0 < gbase := by unfold gbase; exact Nat.two_pow_pos 64

theorem gA_ge (l k : Nat) : gbase ≤ gA l k := by
  unfold gA
  exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right gbase (by omega))

theorem gB_ge (l k : Nat) : gbase ≤ gB l k := by
  unfold gB
  exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right gbase (by omega))

theorem gA_div {l k : Nat} (hl : l < gbase) : gA l k / gbase = 2 * k + 1 := by
  unfold gA; rw [Nat.mul_add_div gbase_pos, Nat.div_eq_of_lt hl]

theorem gB_div {l k : Nat} (hl : l < gbase) : gB l k / gbase = 2 * k + 2 := by
  unfold gB; rw [Nat.mul_add_div gbase_pos, Nat.div_eq_of_lt hl]

theorem gA_mod {l k : Nat} (hl : l < gbase) : gA l k % gbase = l := by
  unfold gA; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hl]

theorem gB_mod {l k : Nat} (hl : l < gbase) : gB l k % gbase = l := by
  unfold gB; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hl]

theorem slot_gA {l k : Nat} (hl : l < gbase) : slot l (gA l k) = some (k, false) := by
  unfold slot
  rw [ite_eq_left ⟨gA_ge l k, gA_mod hl⟩, gA_div hl]
  simp

theorem slot_gB {l k : Nat} (hl : l < gbase) : slot l (gB l k) = some (k, true) := by
  unfold slot
  rw [ite_eq_left ⟨gB_ge l k, gB_mod hl⟩, gB_div hl]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · omega
  · simp

theorem slot_lt {l x : Nat} (hx : x < gbase) : slot l x = none := by
  unfold slot; rw [ite_eq_right (by omega)]

/-- A decoded ghost cell is the token or blank cell of its slot. -/
theorem slot_inv {l x k : Nat} {b : Bool} (h : slot l x = some (k, b)) :
    x = if b then gB l k else gA l k := by
  unfold slot at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have e := Nat.div_add_mod x gbase
    have q1 : 1 ≤ x / gbase := (Nat.le_div_iff_mul_le gbase_pos).mpr (by omega)
    have := Nat.div_add_mod (x / gbase - 1) 2
    have := Nat.mod_lt (x / gbase - 1) (show 0 < 2 by decide)
    by_cases hb : (x / gbase - 1) % 2 = 1
    · simp only [hb, beq_self_eq_true, ite_true, gB]
      rw [hc.2] at e
      have : x / gbase = 2 * ((x / gbase - 1) / 2) + 2 := by omega
      rw [← this]; omega
    · have hb' : ((x / gbase - 1) % 2 == 1) = false := by simp [hb]
      simp only [hb', Bool.false_eq_true, ite_false, gA]
      rw [hc.2] at e
      have : x / gbase = 2 * ((x / gbase - 1) / 2) + 1 := by omega
      rw [← this]; omega
  · cases h

theorem gA_ne_gB (l k j : Nat) (hl : l < gbase) : gA l k ≠ gB l j := by
  intro e
  have h1 : 2 * k + 1 = 2 * j + 2 := by rw [← gA_div hl, ← gB_div hl, e]
  clear e hl
  omega

theorem gA_inj {l k j : Nat} (hl : l < gbase) (e : gA l k = gA l j) : k = j := by
  have h1 : 2 * k + 1 = 2 * j + 1 := by rw [← gA_div hl, ← gA_div hl, e]
  clear e hl
  omega

theorem gB_inj {l k j : Nat} (hl : l < gbase) (e : gB l k = gB l j) : k = j := by
  have h1 : 2 * k + 2 = 2 * j + 2 := by rw [← gB_div hl, ← gB_div hl, e]
  clear e hl
  omega

theorem gA_ne_lt {l k x : Nat} (hx : x < gbase) : gA l k ≠ x := by
  have := gA_ge l k; omega

theorem gB_ne_lt {l k x : Nat} (hx : x < gbase) : gB l k ≠ x := by
  have := gB_ge l k; omega

theorem ledger_apply (l : Nat) (S : List Nat) (x : Nat) : ledger l S x =
    match slot l x with
    | some (k, b) => if k < M ∧ b = decide (k ∈ S) then some 0 else none
    | none => none := rfl

theorem ghosts_apply (l : Nat) (x : Nat) : ghosts l x =
    match slot l x with
    | some (k, _) => if k < M then some 0 else none
    | none => none := rfl

/-! The big constants `M` and `gbase` are generalized away before `simp`: otherwise the kernel
unfolds `slot` or `Nat.ble` on `2 ^ 32 - 1` and recurses for minutes. -/

theorem ledger_gA {l k : Nat} (S : List Nat) (hl : l < gbase) (hk : k < M) :
    ledger l S (gA l k) = if k ∈ S then none else some 0 := by
  rw [ledger_apply]
  have e := slot_gA (k := k) hl
  generalize slot l (gA l k) = o at e ⊢
  subst e
  generalize M = m at hk ⊢
  by_cases h : k ∈ S <;> simp [h, hk]

theorem ledger_gB {l k : Nat} (S : List Nat) (hl : l < gbase) (hk : k < M) :
    ledger l S (gB l k) = if k ∈ S then some 0 else none := by
  rw [ledger_apply]
  have e := slot_gB (k := k) hl
  generalize slot l (gB l k) = o at e ⊢
  subst e
  generalize M = m at hk ⊢
  by_cases h : k ∈ S <;> simp [h, hk]

theorem ghosts_gA {l k : Nat} (hl : l < gbase) (hk : k < M) : ghosts l (gA l k) = some 0 := by
  rw [ghosts_apply]
  have e := slot_gA (k := k) hl
  generalize slot l (gA l k) = o at e ⊢
  subst e
  generalize M = m at hk ⊢
  simp [hk]

theorem ghosts_gB {l k : Nat} (hl : l < gbase) (hk : k < M) : ghosts l (gB l k) = some 0 := by
  rw [ghosts_apply]
  have e := slot_gB (k := k) hl
  generalize slot l (gB l k) = o at e ⊢
  subst e
  generalize M = m at hk ⊢
  simp [hk]

theorem ledger_lt {l x : Nat} (S : List Nat) (hx : x < gbase) : ledger l S x = none := by
  rw [ledger_apply]
  have e := slot_lt (l := l) hx
  generalize slot l x = o at e ⊢
  subst e; rfl

theorem ghosts_lt {l x : Nat} (hx : x < gbase) : ghosts l x = none := by
  rw [ghosts_apply]
  have e := slot_lt (l := l) hx
  generalize slot l x = o at e ⊢
  subst e; rfl

/-- The ledger depends only on which slots are in use. -/
theorem ledger_congr {l : Nat} {S S' : List Nat} (h : ∀ k, k ∈ S ↔ k ∈ S') :
    ledger l S = ledger l S' := by
  funext x; rw [ledger_apply, ledger_apply]
  cases slot l x with
  | none => rfl
  | some p => obtain ⟨k, b⟩ := p; simp only [h k]

/-- **The ledger off one slot**: at cells that are not slot `k`'s, the ledger does not depend on
whether `k` is in use. -/
theorem ledger_off {l k x : Nat} {S S' : List Nat} (hS : ∀ j, j ≠ k → (j ∈ S ↔ j ∈ S'))
    (hA : x ≠ gA l k) (hB : x ≠ gB l k) : ledger l S x = ledger l S' x := by
  rw [ledger_apply, ledger_apply]
  cases e : slot l x with
  | none => rfl
  | some p =>
    obtain ⟨j, b⟩ := p
    have hx := slot_inv e
    have hj : j ≠ k := by
      rintro rfl; cases b <;> simp_all
    simp only [hS j hj]

/-- The ledger cells are ghost cells. -/
theorem ledger_le_ghosts (l : Nat) (S : List Nat) : Heap.Le (ledger l S) (ghosts l) := by
  intro x v h
  rw [ledger_apply] at h; rw [ghosts_apply]
  generalize slot l x = o at h ⊢
  cases o with
  | none => cases h
  | some p =>
    obtain ⟨k, b⟩ := p
    generalize M = m at h ⊢
    simp only at h ⊢
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h; simp [hc.1]
    · cases h

/-- A nodup list of slots below `M` has at most `M` elements. -/
theorem length_le_M {S : List Nat} (hn : S.Nodup) (hb : ∀ k ∈ S, k < M) : S.length ≤ M := by
  have : S.Subperm (List.range M) := hn.subperm (fun k hk => List.mem_range.mpr (hb k hk))
  simpa using this.length_le

end Silmaril.Proofs.X86.Concurrency.Cir.Rc
