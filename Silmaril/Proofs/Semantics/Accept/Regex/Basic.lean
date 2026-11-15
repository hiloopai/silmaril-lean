module

public import Silmaril.Semantics.Accept.Regex.Defs
public import Silmaril.Semantics.Accept.Defs
public import Mathlib.Computability.DFA
import Cslib.Computability.Languages.RegularLanguage
import Cslib.Computability.Languages.RegularExpressions

/-!
# Regular-expression presentations: proofs

Proofs for `Silmaril.Semantics.Accept.Regex.Thms`. Nothing imports this module except that
header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Proofs.Semantics.Accept.Regex

open Silmaril.Accept Silmaril.Accept.Regex Silmaril.Accept.Regex.Expr
open scoped Computability

universe u v w

variable {α : Type u} {ι : Type v} {κ : Type w}

/-! ## Derived operations -/

theorem mem_letters_iff {p : α → Prop} {w : List α} : w ∈ letters p ↔ ∃ a, p a ∧ w = [a] :=
  Iff.rfl

theorem mem_rep_iff {L : Language α} {m n : ℕ} {w : List α} :
    w ∈ rep L m n ↔ ∃ k, m ≤ k ∧ k ≤ n ∧ w ∈ L ^ k := Iff.rfl

theorem kstar_letters (p : α → Prop) : (letters p)∗ = {w | ∀ a ∈ w, p a} := by
  ext w
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨S, rfl, hS⟩ a ha
    obtain ⟨y, hy, hay⟩ := List.mem_flatten.1 ha
    obtain ⟨b, hb, rfl⟩ := hS y hy
    rwa [List.mem_singleton.1 hay]
  · intro h
    refine ⟨w.map fun a => [a], ?_, ?_⟩
    · clear h
      induction w with
      | nil => rfl
      | cons a w ih => simpa using ih
    · simp only [List.mem_map]
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, h a ha, rfl⟩

/-! ## Evaluation of derived expressions -/

theorem mem_eval_sum (ρ : ι → Language α) (es : List (Expr ι α)) (w : List α) :
    w ∈ eval ρ (sum es) ↔ ∃ e ∈ es, w ∈ eval ρ e := by
  induction es with
  | nil => simp [sum, eval, Language.notMem_zero]
  | cons e es ih =>
    cases es with
    | nil => simp [sum]
    | cons f fs =>
      simp only [sum, eval, Language.mem_add] at ih ⊢
      rw [ih]
      simp

theorem eval_word (ρ : ι → Language α) (w : List α) : eval ρ (Expr.word w) = Regex.word w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    ext x
    simp only [Expr.word, eval, ih, Language.mem_mul, Regex.word]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      change u = [a] at hu; change v = w at hv
      subst hu hv
      rfl
    · intro hx
      exact ⟨[a], rfl, w, rfl, by simpa using hx.symm⟩

theorem eval_pow (ρ : ι → Language α) (e : Expr ι α) (n : ℕ) :
    eval ρ (pow e n) = eval ρ e ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow, eval, ih, pow_succ']

theorem eval_rep (ρ : ι → Language α) (e : Expr ι α) (m n : ℕ) :
    eval ρ (Expr.rep e m n) = Regex.rep (eval ρ e) m n := by
  ext w
  simp only [Expr.rep, mem_eval_sum, List.mem_map, List.mem_range, mem_rep_iff]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, hw⟩
    exact ⟨m + j, by omega, by omega, by rwa [eval_pow] at hw⟩
  · rintro ⟨k, hmk, hkn, hw⟩
    exact ⟨_, ⟨k - m, by omega, rfl⟩, by rwa [eval_pow, Nat.add_sub_cancel' hmk]⟩

/-! ## Congruence, monotonicity, substitution -/

theorem eval_congr {ρ ρ' : ι → Language α} :
    ∀ {e : Expr ι α}, (∀ i ∈ e.leaves, ρ i = ρ' i) → eval ρ e = eval ρ' e
  | .zero, _ | .one, _ | .char _, _ | .cls _, _ => rfl
  | .leaf i, h => h i rfl
  | .plus e f, h => by
    simp only [eval]
    rw [eval_congr fun i hi => h i (Or.inl hi), eval_congr fun i hi => h i (Or.inr hi)]
  | .comp e f, h => by
    simp only [eval]
    rw [eval_congr fun i hi => h i (Or.inl hi), eval_congr fun i hi => h i (Or.inr hi)]
  | .star e, h => congrArg KStar.kstar (eval_congr (e := e) h)

theorem eval_mono {ρ ρ' : ι → Language α} :
    ∀ {e : Expr ι α}, (∀ i ∈ e.leaves, ρ i ≤ ρ' i) → eval ρ e ≤ eval ρ' e
  | .zero, _ | .one, _ | .char _, _ | .cls _, _ => le_rfl
  | .leaf i, h => h i rfl
  | .plus _ _, h =>
    add_le_add (eval_mono fun i hi => h i (Or.inl hi)) (eval_mono fun i hi => h i (Or.inr hi))
  | .comp _ _, h =>
    mul_le_mul' (eval_mono fun i hi => h i (Or.inl hi)) (eval_mono fun i hi => h i (Or.inr hi))
  | .star _, h => kstar_mono (eval_mono h)

theorem eval_bind (ρ : κ → Language α) (σ : ι → Expr κ α) :
    ∀ e : Expr ι α, eval ρ (Expr.bind σ e) = eval (fun i => eval ρ (σ i)) e
  | .zero | .one | .char _ | .cls _ | .leaf _ => rfl
  | .plus e f => by simp only [Expr.bind, eval, eval_bind ρ σ e, eval_bind ρ σ f]
  | .comp e f => by simp only [Expr.bind, eval, eval_bind ρ σ e, eval_bind ρ σ f]
  | .star e => by simp only [Expr.bind, eval, eval_bind ρ σ e]

theorem leaves_bind (σ : ι → Expr κ α) :
    ∀ e : Expr ι α, (Expr.bind σ e).leaves = ⋃ i ∈ e.leaves, (σ i).leaves
  | .zero | .one | .char _ | .cls _ => by simp [Expr.bind, leaves]
  | .leaf i => by simp [Expr.bind, leaves]
  | .plus e f | .comp e f => by
    simp only [Expr.bind, leaves, leaves_bind σ e, leaves_bind σ f, Set.biUnion_union]
  | .star e => by simp only [Expr.bind, leaves, leaves_bind σ e]

theorem bind_leaf : ∀ e : Expr ι α, Expr.bind leaf e = e
  | .zero | .one | .char _ | .cls _ | .leaf _ => rfl
  | .plus e f | .comp e f => by simp only [Expr.bind, bind_leaf e, bind_leaf f]
  | .star e => by simp only [Expr.bind, bind_leaf e]

theorem bind_bind {μ : Type w} (σ : ι → Expr κ α) (τ : κ → Expr μ α) :
    ∀ e : Expr ι α, Expr.bind τ (Expr.bind σ e) = Expr.bind (fun i => Expr.bind τ (σ i)) e
  | .zero | .one | .char _ | .cls _ | .leaf _ => rfl
  | .plus e f | .comp e f => by simp only [Expr.bind, bind_bind σ τ e, bind_bind σ τ f]
  | .star e => by simp only [Expr.bind, bind_bind σ τ e]

theorem eval_ofRegex (ρ : ι → Language α) :
    ∀ r : RegularExpression α, eval ρ (ofRegex r) = r.matches'
  | .zero | .epsilon | .char _ => rfl
  | .plus r s | .comp r s => by
    simp only [ofRegex, eval, eval_ofRegex ρ r, eval_ofRegex ρ s]; rfl
  | .star r => by simp only [ofRegex, eval, eval_ofRegex ρ r]; rfl

theorem leaves_ofRegex : ∀ r : RegularExpression α, (ofRegex r : Expr ι α).leaves = ∅
  | .zero | .epsilon | .char _ => rfl
  | .plus r s | .comp r s => by simp only [ofRegex, leaves, leaves_ofRegex r, leaves_ofRegex s,
      Set.union_self]
  | .star r => by simp only [ofRegex, leaves, leaves_ofRegex r]

/-! ## Leaf-free expressions are regular expressions -/

theorem eval_cls_eq_sum [Fintype α] (p : α → Bool) :
    (letters fun a => p a = true : Language α) =
      (((Finset.univ.filter fun a => p a = true).toList.map RegularExpression.char).sum).matches' := by
  ext w
  rw [RegularExpression.mem_sum_matches']
  simp only [mem_letters_iff, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, hw⟩
    exact ⟨a, ha, by simpa [RegularExpression.matches'_char] using hw⟩

theorem matches'_toRegex [Fintype α] (ρ : Empty → Language α) :
    ∀ e : Expr Empty α, (toRegex e).matches' = eval ρ e
  | .zero | .one | .char _ => rfl
  | .cls p => (eval_cls_eq_sum p).symm
  | .leaf i => i.elim
  | .plus e f => by
    simp only [toRegex, eval, RegularExpression.matches'_add, matches'_toRegex ρ e,
      matches'_toRegex ρ f]
  | .comp e f => by
    simp only [toRegex, eval, RegularExpression.matches'_mul, matches'_toRegex ρ e,
      matches'_toRegex ρ f]
  | .star e => by simp only [toRegex, eval, RegularExpression.matches'_star, matches'_toRegex ρ e]

/-- A three-state DFA (`none` start, `some true` accept, `some false` dead) for a class. -/
def classDFA (p : α → Prop) [DecidablePred p] : DFA α (Option Bool) where
  step s a := match s with
    | none => some (decide (p a))
    | some _ => some false
  start := none
  accept := {some true}

theorem classDFA_evalFrom_dead (p : α → Prop) [DecidablePred p] :
    ∀ w : List α, (classDFA p).evalFrom (some false) w = some false
  | [] => rfl
  | _ :: w => by rw [DFA.evalFrom_cons]; exact classDFA_evalFrom_dead p w

theorem classDFA_evalFrom_acc (p : α → Prop) [DecidablePred p] :
    ∀ w : List α, (classDFA p).evalFrom (some true) w = some true ↔ w = []
  | [] => by simp
  | _ :: w => by
    rw [DFA.evalFrom_cons]
    refine ⟨fun h => ?_, fun h => nomatch h⟩
    rw [show (classDFA p).step (some true) _ = some false from rfl, classDFA_evalFrom_dead] at h
    cases h

theorem isRegular_letters (p : α → Prop) : (letters p).IsRegular := by
  classical
  refine ⟨Option Bool, inferInstance, classDFA p, ?_⟩
  ext w
  rw [DFA.mem_accepts]
  cases w with
  | nil => simp [mem_letters_iff, DFA.eval, classDFA]
  | cons a w =>
    rw [DFA.eval, DFA.evalFrom_cons]
    by_cases ha : p a
    · have : (classDFA p).step (classDFA p).start a = some true := by simp [classDFA, ha]
      rw [this]
      change _ ∈ ({some true} : Set (Option Bool)) ↔ _
      rw [Set.mem_singleton_iff, classDFA_evalFrom_acc]
      simp [mem_letters_iff, ha]
    · have : (classDFA p).step (classDFA p).start a = some false := by simp [classDFA, ha]
      rw [this, classDFA_evalFrom_dead]
      simp [mem_letters_iff, ha, classDFA]

theorem isRegular_eval {ρ : ι → Language α} :
    ∀ {e : Expr ι α}, (∀ i ∈ e.leaves, (ρ i).IsRegular) → (eval ρ e).IsRegular
  | .zero, _ => Cslib.Language.IsRegular.zero
  | .one, _ => Cslib.Language.IsRegular.one
  | .char a, _ => Cslib.Language.IsRegular.char a
  | .cls _, _ => isRegular_letters _
  | .leaf i, h => h i rfl
  | .plus _ _, h => Cslib.Language.IsRegular.add (isRegular_eval fun i hi => h i (Or.inl hi))
      (isRegular_eval fun i hi => h i (Or.inr hi))
  | .comp _ _, h => Cslib.Language.IsRegular.mul (isRegular_eval fun i hi => h i (Or.inl hi))
      (isRegular_eval fun i hi => h i (Or.inr hi))
  | .star _, h => Cslib.Language.IsRegular.kstar (isRegular_eval h)

theorem isRegular_iff_exists_expr [Finite α] {L : Language α} :
    L.IsRegular ↔ ∃ e : Expr Empty α, eval Empty.elim e = L := by
  constructor
  · intro h
    obtain ⟨r, rfl⟩ := Cslib.Language.IsRegular.iff_regex.1 h
    exact ⟨ofRegex r, eval_ofRegex _ r⟩
  · rintro ⟨e, rfl⟩
    exact isRegular_eval fun i _ => i.elim

/-! ## The Bool matcher -/

theorem any_splits {w : List α} {p : List α × List α → Bool} :
    (splits w).any p = true ↔ ∃ u v, u ++ v = w ∧ p (u, v) = true := by
  simp only [splits, List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨n, -, h⟩
    exact ⟨_, _, List.take_append_drop n w, h⟩
  · rintro ⟨u, v, rfl, h⟩
    exact ⟨u.length, by simp, by simpa using h⟩

/-- One unfolding of the star: a word of `L∗` is empty or a nonempty word of `L` followed by a
word of `L∗`. -/
theorem mem_kstar_iff_cons {L : Language α} {w : List α} :
    w ∈ L∗ ↔ w = [] ∨ ∃ u v, u ≠ [] ∧ u ∈ L ∧ v ∈ L∗ ∧ u ++ v = w := by
  constructor
  · intro h
    rw [Language.mem_kstar_iff_exists_nonempty] at h
    obtain ⟨S, rfl, hS⟩ := h
    cases S with
    | nil => exact Or.inl rfl
    | cons u S =>
      refine Or.inr ⟨u, S.flatten, (hS u (by simp)).2, (hS u (by simp)).1, ?_, rfl⟩
      exact Language.join_mem_kstar fun y hy => (hS y (by simp [hy])).1
  · rintro (rfl | ⟨u, v, -, hu, hv, rfl⟩)
    · exact Language.nil_mem_kstar L
    · obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.1 hv
      exact Language.mem_kstar.2 ⟨u :: S, rfl, by simpa [hu] using hS⟩

theorem starB_iff {L : Language α} {m : List α → Bool} (hm : Decides m L) :
    ∀ (k : ℕ) (w : List α), w.length ≤ k → (starB m k w = true ↔ w ∈ L∗)
  | 0, w, hw => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hw)]
    simp [starB, Language.nil_mem_kstar]
  | k + 1, w, hw => by
    rw [mem_kstar_iff_cons]
    simp only [starB, Bool.or_eq_true, List.isEmpty_iff, List.any_eq_true, List.mem_range,
      Bool.and_eq_true]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨n, hn, hu, hv⟩
      refine ⟨w.take (n + 1), w.drop (n + 1), ?_, (hm _).1 hu, ?_, List.take_append_drop _ w⟩
      · rw [Ne, List.take_eq_nil_iff]; rintro (h | rfl) <;> simp_all
      · exact (starB_iff hm k _ (by simp; omega)).1 hv
    · rintro ⟨u, v, hu0, hu, hv, rfl⟩
      have hlen : 0 < u.length := List.length_pos_iff.2 hu0
      refine ⟨u.length - 1, by simp; omega, ?_, ?_⟩
      · rw [Nat.sub_add_cancel hlen, List.take_left']
        exact (hm _).2 hu
        rfl
      · rw [Nat.sub_add_cancel hlen, List.drop_left']
        exact (starB_iff hm k _ (by simp at hw; omega)).2 hv
        rfl

theorem decides_matchB [DecidableEq α] {check : ι → List α → Bool} {ρ : ι → Language α}
    (h : ∀ i, Decides (check i) (ρ i)) : ∀ e : Expr ι α, Decides (matchB check e) (eval ρ e)
  | .zero, w => ⟨nofun, fun hw => (Language.notMem_zero w hw).elim⟩
  | .one, w => by
    simp only [matchB, eval, List.isEmpty_iff]; exact (Language.mem_one w).symm
  | .char a, w => by simp only [matchB, eval, beq_iff_eq]; rfl
  | .cls p, w => by
    match w with
    | [] => simp [matchB, eval, letters]
    | [a] => simp [matchB, eval, letters]
    | _ :: _ :: _ => simp [matchB, eval, letters]
  | .leaf i, w => h i w
  | .plus e f, w => by
    simp only [matchB, eval, Bool.or_eq_true]
    exact or_congr (decides_matchB h e w) (decides_matchB h f w)
  | .comp e f, w => by
    simp only [matchB, eval, any_splits, Bool.and_eq_true,
      decides_matchB h e _, decides_matchB h f _]
    constructor
    · rintro ⟨u, v, rfl, hu, hv⟩; exact ⟨u, hu, v, hv, rfl⟩
    · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, v, rfl, hu, hv⟩
  | .star e, w => by
    simp only [matchB, eval]
    exact starB_iff (decides_matchB h e) _ w le_rfl

theorem decides_rmatch [DecidableEq α] (r : RegularExpression α) :
    Decides r.rmatch r.matches' := fun w => RegularExpression.rmatch_iff_matches' r w

end Silmaril.Proofs.Semantics.Accept.Regex
