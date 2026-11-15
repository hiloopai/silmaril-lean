module

public import Silmaril.Semantics.Accept.Regex.Defs
public import Silmaril.Semantics.Accept.Defs
public import Mathlib.Computability.DFA
import Silmaril.Proofs.Semantics.Accept.Regex.Basic

/-!
# Regular-expression presentations of acceptor sets: laws

* membership in the derived operations (`mem_letters`, `mem_word`, `mem_opt`, `mem_rep`, …);
* evaluation of each constructor and of the derived expressions (`eval_sum`, `eval_word`,
  `eval_pow`, `eval_opt`, `eval_oneOrMore`, `eval_rep`, `eval_repAtLeast`);
* **congruence** `eval_congr` (only the leaves that occur matter), **monotonicity**
  `eval_mono`/`eval_monotone` (in the leaf languages), **substitution** `eval_bind`,
  `eval_mapLeaves`, `leaves_bind`, `bind_leaf`, `bind_bind`;
* **regularity** — only under hypotheses on the leaves: `isRegular_eval` (every leaf that
  occurs is regular), `isRegular_eval_of_leaves_eq_empty`, and over a finite alphabet
  `isRegular_iff_exists_expr` (regular ⇔ the value of a leaf-free expression, via CSLib's
  Kleene theorem). Without such hypotheses nothing is claimed: `eval_leaf` shows that a single
  leaf presents *every* language;
* **Mathlib regular expressions**: `eval_ofRegex`, `leaves_ofRegex`, `matches'_toRegex`;
* **checkers** (`Silmaril.Accept.Decides`): `decides_matchB` (Bool leaf checkers give a Bool
  matcher for the whole expression), `decides_matchB_ofBool`, `decides_rmatch` (Mathlib's
  derivative matcher);
* **bytes**: `eval_byteRange`, `eval_byteLit`, `isRegular_range`.
-/

@[expose] public section

namespace Silmaril.Accept.Regex

open scoped Computability

universe u v w

variable {α : Type u}

/-! ## Derived operations -/

section Ops

variable {L : Language α} {w : List α}

@[simp] theorem mem_letter {a : α} : w ∈ letter a ↔ w = [a] := Iff.rfl

@[simp] theorem mem_letters {p : α → Prop} : w ∈ letters p ↔ ∃ a, p a ∧ w = [a] := Iff.rfl

@[simp] theorem mem_anyLetter : w ∈ (anyLetter : Language α) ↔ w.length = 1 := by
  simp only [anyLetter, mem_letters, true_and, List.length_eq_one_iff]

@[simp] theorem mem_word {v : List α} : w ∈ word v ↔ w = v := Iff.rfl

theorem mem_opt : w ∈ opt L ↔ w = [] ∨ w ∈ L := Iff.rfl

theorem mem_rep {m n : ℕ} : w ∈ rep L m n ↔ ∃ k, m ≤ k ∧ k ≤ n ∧ w ∈ L ^ k := Iff.rfl

theorem letter_eq_word (a : α) : letter a = word [a] := rfl

theorem letters_mono {p q : α → Prop} (h : ∀ a, p a → q a) : letters p ≤ letters q :=
  fun _ ⟨a, ha, hw⟩ => ⟨a, h a ha, hw⟩

theorem oneOrMore_eq_kstar_mul (L : Language α) : oneOrMore L = L∗ * L :=
  (Language.mul_self_kstar_comm L).symm

theorem one_add_oneOrMore (L : Language α) : 1 + oneOrMore L = L∗ :=
  Language.one_add_self_mul_kstar_eq_kstar L

theorem rep_self (L : Language α) (n : ℕ) : rep L n n = L ^ n := by
  ext w; exact ⟨fun ⟨k, h1, h2, hw⟩ => (le_antisymm h2 h1) ▸ hw, fun hw => ⟨n, le_rfl, le_rfl, hw⟩⟩

theorem rep_le_kstar (L : Language α) (m n : ℕ) : rep L m n ≤ L∗ :=
  fun _ ⟨k, _, _, hw⟩ => by rw [Language.kstar_eq_iSup_pow]; exact Language.mem_iSup.2 ⟨k, hw⟩

/-- A character class is regular, over any alphabet. -/
theorem isRegular_letters (p : α → Prop) : (letters p).IsRegular :=
  Proofs.Semantics.Accept.Regex.isRegular_letters p

/-- The star of a character class: the words all of whose letters are in the class. -/
theorem kstar_letters (p : α → Prop) : (letters p)∗ = {w | ∀ a ∈ w, p a} :=
  Proofs.Semantics.Accept.Regex.kstar_letters p

theorem mem_kstar_letters {p : α → Prop} : w ∈ (letters p)∗ ↔ ∀ a ∈ w, p a := by
  rw [kstar_letters]; rfl

end Ops

/-! ## Evaluation -/

namespace Expr

variable {ι : Type v} {κ : Type w} (ρ : ι → Language α)

@[simp] theorem eval_zero : eval ρ (zero : Expr ι α) = 0 := rfl
@[simp] theorem eval_one : eval ρ (one : Expr ι α) = 1 := rfl
@[simp] theorem eval_char (a : α) : eval ρ (char a) = letter a := rfl
@[simp] theorem eval_cls (p : α → Bool) : eval ρ (cls p) = letters fun a => p a = true := rfl
@[simp] theorem eval_leaf (i : ι) : eval ρ (leaf i) = ρ i := rfl
@[simp] theorem eval_plus (e f : Expr ι α) : eval ρ (plus e f) = eval ρ e + eval ρ f := rfl
@[simp] theorem eval_comp (e f : Expr ι α) : eval ρ (comp e f) = eval ρ e * eval ρ f := rfl
@[simp] theorem eval_star (e : Expr ι α) : eval ρ (star e) = (eval ρ e)∗ := rfl

/-- The value of a union of expressions. -/
theorem mem_eval_sum (es : List (Expr ι α)) (w : List α) :
    w ∈ eval ρ (sum es) ↔ ∃ e ∈ es, w ∈ eval ρ e :=
  Proofs.Semantics.Accept.Regex.mem_eval_sum ρ es w

@[simp] theorem eval_word (w : List α) : eval ρ (Expr.word w) = Regex.word w :=
  Proofs.Semantics.Accept.Regex.eval_word ρ w

@[simp] theorem eval_pow (e : Expr ι α) (n : ℕ) : eval ρ (pow e n) = eval ρ e ^ n :=
  Proofs.Semantics.Accept.Regex.eval_pow ρ e n

@[simp] theorem eval_opt (e : Expr ι α) : eval ρ (Expr.opt e) = Regex.opt (eval ρ e) := rfl

@[simp] theorem eval_oneOrMore (e : Expr ι α) :
    eval ρ (Expr.oneOrMore e) = Regex.oneOrMore (eval ρ e) := rfl

@[simp] theorem eval_rep (e : Expr ι α) (m n : ℕ) :
    eval ρ (Expr.rep e m n) = Regex.rep (eval ρ e) m n :=
  Proofs.Semantics.Accept.Regex.eval_rep ρ e m n

@[simp] theorem eval_repAtLeast (e : Expr ι α) (m : ℕ) :
    eval ρ (Expr.repAtLeast e m) = Regex.repAtLeast (eval ρ e) m := by
  simp only [Expr.repAtLeast, eval_comp, eval_pow, eval_star, Regex.repAtLeast]

/-! ## Congruence, monotonicity and substitution -/

variable {ρ}

/-- Evaluation depends only on the leaves that occur. -/
theorem eval_congr {ρ' : ι → Language α} {e : Expr ι α} (h : ∀ i ∈ e.leaves, ρ i = ρ' i) :
    eval ρ e = eval ρ' e :=
  Proofs.Semantics.Accept.Regex.eval_congr h

/-- Evaluation is monotone in the languages of the leaves that occur. -/
theorem eval_mono {ρ' : ι → Language α} {e : Expr ι α} (h : ∀ i ∈ e.leaves, ρ i ≤ ρ' i) :
    eval ρ e ≤ eval ρ' e :=
  Proofs.Semantics.Accept.Regex.eval_mono h

theorem eval_monotone (e : Expr ι α) : Monotone fun ρ : ι → Language α => eval ρ e :=
  fun _ _ h => eval_mono fun i _ => h i

/-- A leaf-free expression has the same value in every environment. -/
theorem eval_of_leaves_eq_empty {e : Expr ι α} (h : e.leaves = ∅) (ρ' : ι → Language α) :
    eval ρ e = eval ρ' e :=
  eval_congr fun i hi => by simp [h] at hi

variable (ρ)

/-- Substitution evaluates compositionally: substitute, then evaluate, is evaluating in the
environment of the substituted expressions. -/
theorem eval_bind (ρ : κ → Language α) (σ : ι → Expr κ α) (e : Expr ι α) :
    eval ρ (bind σ e) = eval (fun i => eval ρ (σ i)) e :=
  Proofs.Semantics.Accept.Regex.eval_bind ρ σ e

theorem eval_mapLeaves (ρ : κ → Language α) (f : ι → κ) (e : Expr ι α) :
    eval ρ (mapLeaves f e) = eval (ρ ∘ f) e :=
  eval_bind ρ _ e

theorem leaves_bind (σ : ι → Expr κ α) (e : Expr ι α) :
    (bind σ e).leaves = ⋃ i ∈ e.leaves, (σ i).leaves :=
  Proofs.Semantics.Accept.Regex.leaves_bind σ e

@[simp] theorem bind_leaf (e : Expr ι α) : bind leaf e = e :=
  Proofs.Semantics.Accept.Regex.bind_leaf e

theorem bind_bind {μ : Type w} (σ : ι → Expr κ α) (τ : κ → Expr μ α) (e : Expr ι α) :
    bind τ (bind σ e) = bind (fun i => bind τ (σ i)) e :=
  Proofs.Semantics.Accept.Regex.bind_bind σ τ e

/-- Equal leaf languages, substituted into the same context, give equal languages: language
equality is a congruence for every expression context. -/
theorem eval_bind_congr (ρ : κ → Language α) {σ τ : ι → Expr κ α} (e : Expr ι α)
    (h : ∀ i ∈ e.leaves, eval ρ (σ i) = eval ρ (τ i)) :
    eval ρ (bind σ e) = eval ρ (bind τ e) := by
  rw [eval_bind, eval_bind]; exact eval_congr h

/-! ## Mathlib regular expressions -/

@[simp] theorem eval_ofRegex (r : RegularExpression α) : eval ρ (ofRegex r) = r.matches' :=
  Proofs.Semantics.Accept.Regex.eval_ofRegex ρ r

@[simp] theorem leaves_ofRegex (r : RegularExpression α) : (ofRegex r : Expr ι α).leaves = ∅ :=
  Proofs.Semantics.Accept.Regex.leaves_ofRegex r

/-- A leaf-free expression over a finite alphabet denotes the language of its Mathlib regular
expression. -/
theorem matches'_toRegex [Fintype α] (ρ : Empty → Language α) (e : Expr Empty α) :
    (toRegex e).matches' = eval ρ e :=
  Proofs.Semantics.Accept.Regex.matches'_toRegex ρ e

/-! ## Regularity -/

/-- An expression is regular when every leaf that occurs in it is. -/
theorem isRegular_eval {e : Expr ι α} (h : ∀ i ∈ e.leaves, (ρ i).IsRegular) :
    (eval ρ e).IsRegular :=
  Proofs.Semantics.Accept.Regex.isRegular_eval h

theorem isRegular_eval_of_leaves_eq_empty {e : Expr ι α} (h : e.leaves = ∅) :
    (eval ρ e).IsRegular :=
  isRegular_eval ρ fun i hi => by simp [h] at hi

/-- Kleene's theorem for expressions (CSLib): over a finite alphabet a language is regular
exactly when it is the value of a leaf-free expression. -/
theorem isRegular_iff_exists_expr [Finite α] {L : Language α} :
    L.IsRegular ↔ ∃ e : Expr Empty α, eval Empty.elim e = L :=
  Proofs.Semantics.Accept.Regex.isRegular_iff_exists_expr

/-- A leaf presents any language at all: regularity is never automatic for expressions with
leaves. -/
theorem exists_eval_leaf (L : Language α) : ∃ ρ : Unit → Language α, eval ρ (leaf ()) = L :=
  ⟨fun _ => L, rfl⟩

/-! ## Checkers -/

/-- Bool checkers deciding the leaf languages give a matcher deciding the expression. -/
theorem decides_matchB [DecidableEq α] {check : ι → List α → Bool}
    (h : ∀ i, Accept.Decides (check i) (ρ i)) (e : Expr ι α) :
    Accept.Decides (matchB check e) (eval ρ e) :=
  Proofs.Semantics.Accept.Regex.decides_matchB h e

/-- The matcher decides the expression whose leaves are the checkers' own languages. -/
theorem decides_matchB_ofBool [DecidableEq α] (check : ι → List α → Bool) (e : Expr ι α) :
    Accept.Decides (matchB check e) (eval (fun i => Accept.ofBool (check i)) e) :=
  decides_matchB _ (fun _ _ => Iff.rfl) e

end Expr

/-- Mathlib's derivative matcher decides the language of a regular expression. -/
theorem decides_rmatch [DecidableEq α] (r : RegularExpression α) :
    Accept.Decides r.rmatch r.matches' :=
  Proofs.Semantics.Accept.Regex.decides_rmatch r

/-! ## Bytes -/

namespace Expr

variable {ι : Type v} (ρ : ι → Language UInt8)

@[simp] theorem eval_byteRange (lo hi : UInt8) : eval ρ (byteRange lo hi) = Bytes.range lo hi := by
  simp only [byteRange, eval_cls, decide_eq_true_eq]; rfl

@[simp] theorem eval_byteLit (s : String) : eval ρ (byteLit s) = Bytes.lit s :=
  eval_word ρ _

end Expr

theorem Bytes.mem_range {lo hi : UInt8} {w : List UInt8} :
    w ∈ Bytes.range lo hi ↔ ∃ b, (lo ≤ b ∧ b ≤ hi) ∧ w = [b] := Iff.rfl

theorem Bytes.isRegular_range (lo hi : UInt8) : (Bytes.range lo hi).IsRegular :=
  isRegular_letters _

theorem Bytes.isRegular_lit (s : String) : (Bytes.lit s).IsRegular := by
  rw [← Expr.eval_byteLit (ι := Empty) Empty.elim]
  exact Expr.isRegular_eval _ fun i _ => i.elim

end Silmaril.Accept.Regex
