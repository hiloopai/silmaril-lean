module

public import Silmaril.Logic.SAT.LRAT.Defs
public import Silmaril.Logic.SAT.CNF.Thms

@[expose] public section

/-!
# A reference LRAT checker: soundness

`Lit.eval_neg`: negation flips a nonzero literal. `Agrees τ σ`: every literal of the partial
assignment `σ` is nonzero and true under `τ`. `rup_sound`: a successful propagation contradicts
every `τ` satisfying `F` and agreeing with `σ`, when every database clause is implied by `F`;
`addOk_implies`: a valid RUP addition is implied by `F`. The run (RUP and RAT) is in
`Silmaril.Proofs.Logic.SAT.LRAT.Rat`.
-/

namespace Silmaril.Logic.SAT

/-- Negation flips the value of a nonzero literal. -/
theorem Lit.eval_neg (τ : Assignment) {l : Int} (hl : l ≠ 0) : Lit.eval τ (-l) = !Lit.eval τ l := by
  have hpos : decide (0 < -l) = !decide (0 < l) := by
    by_cases h : 0 < l
    · have h' : ¬ 0 < -l := by omega
      simp only [h, h', decide_true, decide_false, Bool.not_true]
    · have h' : 0 < -l := by omega
      simp only [h, h', decide_true, decide_false, Bool.not_false]
  have hvar : (-l).natAbs = l.natAbs := Int.natAbs_neg l
  show (τ (-l).natAbs == decide (0 < -l)) = !(τ l.natAbs == decide (0 < l))
  rw [hpos, hvar]
  cases τ l.natAbs <;> cases decide (0 < l) <;> rfl

end Silmaril.Logic.SAT

namespace Silmaril.Logic.SAT.LRAT

/-- The total assignment `τ` agrees with the partial assignment `σ`. -/
def Agrees (τ : Assignment) (σ : List Lit) : Prop := ∀ l ∈ σ, l ≠ 0 ∧ l.eval τ = true

/-- Every clause of the database is implied by `F`. -/
def Implied (F : CNF) (db : DB) : Prop := ∀ p ∈ db, F.Implies p.2

theorem lookup_mem {db : DB} {i : Nat} {D : Clause} (h : lookup db i = some D) : (i, D) ∈ db := by
  induction db with
  | nil => cases h
  | cons p db ih =>
    obtain ⟨j, C⟩ := p
    by_cases hj : j = i
    · subst hj
      have hC : C = D := by simpa [lookup] using h
      subst hC
      exact List.mem_cons_self
    · have h' : lookup db i = some D := by simpa [lookup, hj] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem mem_init {n : Nat} {G : CNF} {p : Nat × Clause} (h : p ∈ init n G) : p.2 ∈ G := by
  induction G generalizing n with
  | nil => cases h
  | cons C G ih =>
    rcases List.mem_cons.1 h with h | h
    · subst h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem implied_init (F : CNF) : Implied F (init 1 F) :=
  fun _ hp => CNF.Implies.of_mem (mem_init hp)

theorem Implied.delete {F : CNF} {db : DB} (h : Implied F db) (ids : List Nat) :
    Implied F (delete db ids) :=
  fun p hp => h p (List.mem_filter.1 hp).1

theorem Implied.cons {F : CNF} {db : DB} (h : Implied F db) {id : Nat} {C : Clause}
    (hC : F.Implies C) : Implied F ((id, C) :: db) := by
  intro p hp
  rcases List.mem_cons.1 hp with hp | hp
  · subst hp
    exact hC
  · exact h p hp

/-- A literal outside `unfalsified σ D` is false under every `τ` agreeing with `σ`. -/
theorem eval_of_not_mem_unfalsified {τ : Assignment} {σ : List Lit} (hτ : Agrees τ σ)
    {D : Clause} {l : Lit} (hl : l ∈ D) (hu : l ∉ unfalsified σ D) : l.eval τ = false := by
  have hneg : -l ∈ σ := Classical.byContradiction fun hn =>
    hu (List.mem_filter.2 ⟨hl, by simpa using hn⟩)
  have hσ := hτ (-l) hneg
  have hl0 : l ≠ 0 := fun h => hσ.1 (by simp [h])
  have hflip := Lit.eval_neg τ hl0
  rw [hσ.2] at hflip
  revert hflip
  cases l.eval τ <;> decide

/-- A clause true under `τ` agreeing with `σ` has a true literal left by `unfalsified`. -/
theorem exists_unfalsified {τ : Assignment} {σ : List Lit} (hτ : Agrees τ σ) {D : Clause}
    (hD : D.eval τ = true) : ∃ l ∈ unfalsified σ D, l.eval τ = true := by
  obtain ⟨l, hl, hlt⟩ := (Clause.eval_eq_true_iff τ D).1 hD
  refine ⟨l, Classical.byContradiction fun hu => ?_, hlt⟩
  have hf := eval_of_not_mem_unfalsified hτ hl hu
  rw [hlt] at hf
  cases hf

theorem Agrees.cons {τ : Assignment} {σ : List Lit} (hτ : Agrees τ σ) {u : Lit} (h0 : u ≠ 0)
    (hu : u.eval τ = true) : Agrees τ (u :: σ) := by
  intro x hx
  rcases List.mem_cons.1 hx with hx | hx
  · exact hx ▸ ⟨h0, hu⟩
  · exact hτ x hx

/-- **RUP soundness**: successful propagation along hint clauses implied by `F` contradicts every
assignment satisfying `F` and agreeing with the starting partial assignment. -/
theorem rup_sound {F : CNF} {db : DB} (hdb : Implied F db) {hs : List Nat} :
    ∀ {σ : List Lit}, rup db σ hs = true →
      ∀ τ : Assignment, F.eval τ = true → Agrees τ σ → False := by
  induction hs with
  | nil => intro σ h; cases h
  | cons h hs ih =>
    intro σ hr τ hF hτ
    show False
    cases hl : lookup db h with
    | none => simp [rup, hl] at hr
    | some D =>
      have hD : D.eval τ = true := hdb (h, D) (lookup_mem hl) τ hF
      obtain ⟨l, hlu, hlt⟩ := exists_unfalsified hτ hD
      match hu : unfalsified σ D, hlu with
      | [u], hlu =>
        have hlu' : l = u := List.mem_singleton.1 hlu
        have hr' : (u != 0 && rup db (u :: σ) hs) = true := by simpa [rup, hl, hu] using hr
        have ⟨h0, hrest⟩ := Bool.and_eq_true _ _ ▸ hr'
        exact ih hrest τ hF (hτ.cons (by simpa using h0) (hlu' ▸ hlt))
      | _ :: _ :: _, _ => simp [rup, hl, hu] at hr

/-- **A valid RUP addition is implied by `F`**, when every database clause is. -/
theorem addOk_implies {F : CNF} {db : DB} (hdb : Implied F db) {lits : Clause}
    {hints : List Nat} (h : addOk db lits hints = true) : F.Implies lits := by
  have ⟨h0, hr⟩ := Bool.and_eq_true _ _ ▸ h
  have hnz : ∀ l ∈ lits, l ≠ 0 := fun l hl hl0 => by subst hl0; simp_all
  intro τ hF
  refine Classical.byContradiction fun hc => ?_
  have hfalse : ∀ l ∈ lits, l.eval τ = false :=
    (Clause.eval_eq_false_iff τ lits).1 (by simpa using hc)
  have hτ : Agrees τ (lits.map (- ·)) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    have hneg := Lit.eval_neg τ (hnz l hl)
    exact ⟨by simpa using hnz l hl, by simp [hneg, hfalse l hl]⟩
  exact rup_sound hdb hr τ hF hτ

end Silmaril.Logic.SAT.LRAT
