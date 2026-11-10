module

public import Silmaril.Calculi.PCF.BoundedEval

/-! # Exact representation of partial recursive functions

Unlike `Realizes`, `ExactRealizes` requires the converse implication as well:
the PCF term returns a numeral exactly when the partial function returns it.
Composition forces every intermediate result, matching Mathlib's strict
partial-function composition while retaining PCF's call-by-name semantics.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF

open TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

namespace Term

/-- Evaluate each natural-number argument before continuing with `body`. -/
def forceAll {p : Bool} {Γ : Ctx Base} {τ : Ty} : {n : ℕ} →
    (Fin n → Term p Γ .nat) → Term p Γ τ → Term p Γ τ
  | 0, _, body => body
  | _ + 1, us, body =>
      ite (isZero (us 0)) (forceAll (Fin.tail us) body) (forceAll (Fin.tail us) body)

@[simp] theorem subst_forceAll {p : Bool} {Γ Δ : Ctx Base} {τ : Ty}
    (s : Subst (sig p) Γ Δ) : {n : ℕ} → (us : Fin n → Term p Γ .nat) →
    (body : Term p Γ τ) →
    (forceAll us body).subst s = forceAll (fun i => (us i).subst s) (body.subst s)
  | 0, _, _ => rfl
  | _ + 1, us, body => by
      simp only [forceAll, subst_ite, subst_isZero, subst_forceAll]
      rfl

end Term

namespace Eval

variable {p : Bool} {τ : Ty}

theorem forceAll_iff : {n : ℕ} → (us : Fin n → Closed p .nat) →
    (body v : Closed p τ) →
    Term.forceAll us body ⇓ v ↔ (∀ i, ∃ m, us i ⇓ Term.num m) ∧ body ⇓ v
  | 0, _, _, _ => by simp [Term.forceAll]
  | n + 1, us, body, v => by
      rw [Term.forceAll, Eval.ite_iff, forceAll_iff]
      constructor
      · rintro (⟨hb, hus, hv⟩ | ⟨hb, hus, hv⟩)
        · exact ⟨Fin.cases ⟨0, Eval.isZero_tt_iff.mp hb⟩ hus, hv⟩
        · obtain ⟨w, hw⟩ := Eval.isZero_ff_iff.mp hb
          obtain ⟨m, hm⟩ := hw.value.eq_num
          exact ⟨Fin.cases ⟨m, hm ▸ hw⟩ hus, hv⟩
      · rintro ⟨hus, hv⟩
        obtain ⟨m, hm⟩ := hus 0
        cases m with
        | zero => exact Or.inl ⟨.isZeroZ' hm, (fun i => hus i.succ), hv⟩
        | succ m => exact Or.inr ⟨.isZeroS' hm, (fun i => hus i.succ), hv⟩

theorem apps_lams_iff {Γ : Ctx Base} {n : ℕ}
    (b : Term p (ctxN n Γ) .nat) (s : Subst (sig p) Γ [])
    (us : Fin n → Closed p .nat) {v : Closed p .nat} :
    Term.apps ((Term.lams n b).subst s) us ⇓ v ↔
      b.subst (Subst.extendN n s us) ⇓ v := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_within
    obtain ⟨_, _, hb, _⟩ := hk.apps_lams_inv b s us
    exact hb.toEval
  · intro h
    exact Expands.apps_lams b s us h

theorem apps_lams_closed_iff {n : ℕ} (b : Term p (ctxN n []) .nat)
    (us : Fin n → Closed p .nat) {v : Closed p .nat} :
    Term.apps (Term.lams n b) us ⇓ v ↔
      b.subst (Subst.extendN n (Subst.id []) us) ⇓ v := by
  simpa using apps_lams_iff b (Subst.id []) us

end Eval

/-- Exact equality of results on all arguments evaluating to numerals. -/
def ExactRealizes {p : Bool} {n : ℕ} (t : Closed p (Ty.arrows n))
    (f : List.Vector ℕ n →. ℕ) : Prop :=
  ∀ (us : Fin n → Closed p .nat) (v : List.Vector ℕ n),
    (∀ i, us i ⇓ Term.num (v.get i)) → ∀ y,
      Term.apps t us ⇓ Term.num y ↔ y ∈ f v

namespace ExactRealizes

variable {p : Bool}

theorem mem_mOfFn_of_forall : {n : ℕ} → {g : Fin n → Part ℕ} →
    (w : List.Vector ℕ n) → (∀ i, w.get i ∈ g i) → w ∈ List.Vector.mOfFn g
  | 0, _, w, _ => by simp [List.Vector.mOfFn, List.Vector.eq_nil w]
  | n + 1, g, w, h => by
      rw [List.Vector.mOfFn, Part.bind_eq_bind, Part.mem_bind_iff]
      refine ⟨w.head, ?_, ?_⟩
      · simpa only [List.Vector.get_zero] using h 0
      · rw [Part.bind_eq_bind, Part.mem_bind_iff]
        refine ⟨w.tail, mem_mOfFn_of_forall w.tail (fun i => ?_), ?_⟩
        · simpa only [List.Vector.get_tail_succ] using h i.succ
        · simp

theorem toRealizes {n : ℕ} {t : Closed p (Ty.arrows n)} {f : List.Vector ℕ n →. ℕ}
    (h : ExactRealizes t f) : Realizes t f := fun us v hv y hy => (h us v hv y).mpr hy

/-- Undefined inputs have no evaluation result, including non-numeral values. -/
theorem noResult_iff {n : ℕ} {t : Closed p (Ty.arrows n)}
    {f : List.Vector ℕ n →. ℕ} (h : ExactRealizes t f)
    (us : Fin n → Closed p .nat) (v : List.Vector ℕ n)
    (hv : ∀ i, us i ⇓ Term.num (v.get i)) :
    Diverges (Term.apps t us) ↔ ¬ (f v).Dom := by
  constructor
  · intro hn hd
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    exact hn _ ((h us v hv y).mpr hy)
  · intro hn w he
    obtain ⟨y, rfl⟩ := he.value.eq_num
    exact hn ((h us v hv y).mp he).1

/-- For total functions, defined-result simulation is already exact. -/
theorem of_total {n : ℕ} {t : Closed p (Ty.arrows n)} {f : List.Vector ℕ n → ℕ}
    (h : Realizes t (f : List.Vector ℕ n →. ℕ)) :
    ExactRealizes t (f : List.Vector ℕ n →. ℕ) := by
  intro us v hv y
  constructor
  · intro he
    have hy := Term.num_injective (he.det (h.total hv))
    simpa [PFun.coe_val, Part.mem_some_iff] using hy
  · exact h us v hv y

/-- Strict composition: force every inner result before applying the outer term. -/
def compTerm {m n : ℕ} (f' : Closed p (Ty.arrows n))
    (g' : Fin n → Closed p (Ty.arrows m)) : Closed p (Ty.arrows m) :=
  Term.lams m (Term.forceAll
    (fun i => Term.apps (TypedLambda.Term.ofClosed (g' i)) (Term.args m))
    (Term.apps (TypedLambda.Term.ofClosed f') fun i =>
      Term.apps (TypedLambda.Term.ofClosed (g' i)) (Term.args m)))

theorem comp {m n : ℕ} {f : List.Vector ℕ n →. ℕ}
    {g : Fin n → List.Vector ℕ m →. ℕ} {f' : Closed p (Ty.arrows n)}
    {g' : Fin n → Closed p (Ty.arrows m)}
    (hf : ExactRealizes f' f) (hg : ∀ i, ExactRealizes (g' i) (g i)) :
    ExactRealizes (compTerm f' g') fun v => (List.Vector.mOfFn fun i => g i v) >>= f := by
  classical
  intro us v hv y
  rw [compTerm, Eval.apps_lams_closed_iff]
  simp only [Term.subst_forceAll, Term.subst_apps, TypedLambda.Term.ofClosed_subst,
    TypedLambda.Term.ofClosed_nil, Term.args, TypedLambda.Term.subst_var, Subst.extendN_argVar]
  rw [Eval.forceAll_iff]
  constructor
  · rintro ⟨hgs, hres⟩
    choose w hw using hgs
    apply Part.mem_bind_iff.mpr
    refine ⟨List.Vector.ofFn w, ?_, ?_⟩
    · exact mem_mOfFn_of_forall _ fun i => by
        simpa using (hg i us v hv (w i)).mp (hw i)
    · exact (hf _ (List.Vector.ofFn w) (by simpa using hw) y).mp hres
  · intro h
    obtain ⟨w, hw, hy⟩ := Part.mem_bind_iff.mp h
    have hgs : ∀ i, Term.apps (g' i) us ⇓ Term.num (w.get i) :=
      fun i => (hg i us v hv _).mpr (Realizes.mem_mOfFn hw i)
    exact ⟨fun i => ⟨w.get i, hgs i⟩, (hf _ w hgs y).mpr hy⟩

end ExactRealizes

namespace Realizes

/-- A terminating search returns its first zero, including the converse
direction needed when the searched partial function is undefined. -/
theorem rfind_eval_inv {p : Bool} {n : ℕ} {k' : Closed p (Ty.arrows (n + 1))}
    {us : Fin n → Closed p .nat} (c : ℕ → ℕ)
    (hc : ∀ z {u : Closed p .nat}, u ⇓ Term.num z →
      Term.apps k' (Fin.cons u us) ⇓ Term.num (c z)) (k : ℕ) :
    ∀ z {u : Closed p .nat} {y : ℕ}, u ⇓ Term.num z →
      EvalWithin k (Term.apps (.app (rfindAux k') u) us) (Term.num y) →
      c y = 0 ∧ z ≤ y ∧ ∀ a, z ≤ a → a < y → c a ≠ 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro z u y hu he
      rw [← Term.apps_cons] at he
      obtain ⟨l, hl, hb⟩ := EvalWithin.apps_fix_lams_inv (by omega)
        (rfindBody k') (Fin.cons u us) he
      simp [rfindBody, Subst.single] at hb
      obtain ⟨m, hm, hcases⟩ := hb.ite_inv
      rcases hcases with ⟨hcond, hout⟩ | ⟨hcond, hrec⟩
      ·
          have hzy := Term.num_injective (hu.det hout.toEval)
          subst y
          have hzero : Term.apps k' (Fin.cons u us) ⇓ Term.num 0 :=
            Eval.isZero_tt_iff.mp hcond.toEval
          have hcz := Term.num_injective ((hc z hu).det hzero)
          exact ⟨hcz, le_rfl, fun a hza haz => by omega⟩
      ·
          have hcz : c z ≠ 0 := by
            intro hz
            have hc0 := hc z hu
            rw [hz] at hc0
            cases (Eval.isZeroZ' hc0).det hcond.toEval
          obtain ⟨hcy, hzy, hmin⟩ := ih m (by omega) (z + 1) (Eval.succ' hu) hrec
          refine ⟨hcy, by omega, fun a hza hay => ?_⟩
          rcases Nat.eq_or_lt_of_le hza with rfl | hza
          · exact hcz
          · exact hmin a (by omega) hay

end Realizes

namespace ExactRealizes

variable {p : Bool}

theorem rfind {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    {k' : Closed p (Ty.arrows (n + 1))}
    (hf : ExactRealizes k' (f : List.Vector ℕ (n + 1) →. ℕ)) :
    ExactRealizes (Realizes.rfindTerm k') fun v =>
      Nat.rfind fun y => Part.some (decide (f (y ::ᵥ v) = 0)) := by
  intro us v hv y
  constructor
  · intro he
    obtain ⟨k, hk⟩ := he.exists_within
    have hk' : EvalWithin k
        (Term.apps ((Term.lams n (Term.apps
          (.app (TypedLambda.Term.ofClosed (Realizes.rfindAux k')) Term.zero)
          (Term.args n))).subst (Subst.id [])) us) (Term.num y) := by
      simpa [Realizes.rfindTerm] using hk
    obtain ⟨l, _, hb, _⟩ := EvalWithin.apps_lams_inv _ _ us hk'
    simp at hb
    have hc : ∀ z {u : Closed p .nat}, u ⇓ Term.num z →
        Term.apps k' (Fin.cons u us) ⇓ Term.num (f (z ::ᵥ v)) := fun z u hu =>
      hf.toRealizes.total fun i =>
        Fin.cases (by simpa using hu) (fun i => by simpa using hv i) i
    obtain ⟨hy, _, hmin⟩ := Realizes.rfind_eval_inv _ hc l 0 (Eval.num 0) hb
    apply Nat.mem_rfind.mpr
    exact ⟨by simpa using hy, fun {a} ha => by simpa using hmin a (Nat.zero_le _) ha⟩
  · exact Realizes.rfind hf.toRealizes us v hv y

end ExactRealizes

/-- Every partial recursive function has an exact PCF representation. -/
theorem exists_exactRealizes {p : Bool} {n : ℕ} {f : List.Vector ℕ n →. ℕ}
    (hf : Nat.Partrec' f) : ∃ t : Closed p (Ty.arrows n), ExactRealizes t f := by
  induction hf with
  | prim hf =>
      obtain ⟨t, ht⟩ := exists_realizes_of_primrec' hf
      exact ⟨t, ExactRealizes.of_total ht⟩
  | comp g _ _ ihf ihg =>
      obtain ⟨f', hf'⟩ := ihf
      choose g' hg' using ihg
      exact ⟨_, ExactRealizes.comp hf' hg'⟩
  | rfind _ ih =>
      obtain ⟨k', hk'⟩ := ih
      exact ⟨_, ExactRealizes.rfind hk'⟩

/-- Exact representation on numeral inputs, for any finite arity. -/
theorem partrec'_definable_exact {n : ℕ} {f : List.Vector ℕ n →. ℕ}
    (hf : Nat.Partrec' f) : ∃ t : Closed false (Ty.arrows n), ∀ v y,
      Term.apps t (fun i => Term.num (v.get i)) ⇓ Term.num y ↔ y ∈ f v := by
  obtain ⟨t, ht⟩ := exists_exactRealizes hf
  exact ⟨t, fun v y => ht _ v (fun i => Eval.num _) y⟩

/-- PCF represents every partial recursive function, with the same defined
results and no extra results at undefined inputs. -/
theorem partrec_definable_exact {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ t : Closed false (Ty.nat ⤳ Ty.nat), ∀ n y,
      .app t (Term.num n) ⇓ Term.num y ↔ y ∈ f n := by
  obtain ⟨t, ht⟩ := partrec'_definable_exact (Nat.Partrec'.part_iff₁.mpr hf)
  exact ⟨t, fun n y => ht (n ::ᵥ List.Vector.nil) y⟩

/-- The exact representation has the same domain as the source function. -/
theorem partrec_definable_exact_with_domain {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ t : Closed false (Ty.nat ⤳ Ty.nat),
      (∀ n y, .app t (Term.num n) ⇓ Term.num y ↔ y ∈ f n) ∧
      (∀ n, Diverges (.app t (Term.num n)) ↔ ¬ (f n).Dom) := by
  obtain ⟨t, ht⟩ := exists_exactRealizes (p := false) (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨t, fun n y => ht _ (n ::ᵥ List.Vector.nil) (fun i => Eval.num _) y, ?_⟩
  intro n
  exact ht.noResult_iff _ (n ::ᵥ List.Vector.nil) (fun i => Eval.num _)

/-- `Realizes` alone admits a terminating term for the nowhere-defined
function. This is a counterexample to replacing it by an exact contract. -/
theorem realizes_does_not_imply_exact :
    ∃ t : Closed false (Ty.arrows 1),
      Realizes t (fun _ => Part.none) ∧ ¬ ExactRealizes t (fun _ => Part.none) := by
  refine ⟨.lam Term.zero, ?_, ?_⟩
  · intro us v hv y hy
    exact hy.1.elim
  · intro h
    have he : Term.apps (n := 1) (.lam Term.zero : Closed false (Ty.arrows 1))
        (fun _ => Term.zero) ⇓ Term.num 0 := by
      apply Expands.beta (Term.zero : Term false [Ty.nat] .nat) Term.zero
      simpa [TypedLambda.Term.subst1] using (Eval.num (p := false) 0)
    have hy := (h _ (0 ::ᵥ List.Vector.nil) (fun i => by fin_cases i; exact Eval.num 0) 0).mp he
    exact hy.1

/-- Ordinary call-by-name composition can ignore a divergent inner result. -/
theorem nonStrict_comp_ignores_undefined :
    .app (Realizes.compTerm (m := 1) (n := 1) (.lam Term.zero : Closed false (Ty.arrows 1))
      (fun _ : Fin 1 => .lam (Term.omega .nat))) Term.zero ⇓ Term.zero := by
  apply Realizes.comp_expands (m := 1) (n := 1) _ _ (fun _ => Term.zero)
  apply Expands.beta (Term.zero : Term false [Ty.nat] .nat) _
  simpa [TypedLambda.Term.subst1] using (Eval.num (p := false) 0)

end Silmaril.Calculi.PCF
