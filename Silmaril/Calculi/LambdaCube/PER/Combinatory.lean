module

public import Mathlib.Logic.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence

@[expose] public section

set_option autoImplicit true

/-! # Total combinatory algebras as realizer domains

The PER models of System F and Fω only need a *total* combinatory algebra:
application with `K` and `S` (Schönfinkel). The arrow PER is extensional, so
βη-soundness holds in every such algebra; no λ-model (Meyer/Scott) axioms are
needed. This file supplies

* `CombAlg`: carrier, application, `K`, `S` and their two equations;
* combinatory terms `CTerm` over de Bruijn variables, their evaluation, and
  bracket abstraction `CTerm.abs` with its β-law `CTerm.eval_abs`;
* untyped de Bruijn λ-terms `ULam` (the target of type erasure), compiled to
  combinators, with the β-law `ULam.eval_lam` and the renaming law
  `ULam.eval_rename` (substitution holds only up to PERs, see below);
* the one-point algebra `CombAlg.unit` (sound but degenerate) and the term
  model `termModel` of closed CSLib locally nameless λ-terms modulo
  βη-conversion, which is nontrivial by CSLib's βη-confluence
  (`termModel_k_ne_s`).

Kleene's first algebra is *partial*; it is deliberately not used here (a
partial-combinatory-algebra generalization is a follow-up issue).
-/

namespace Silmaril.Calculi.LambdaCube.PERModel

/-- Extend an environment by a newest entry. -/
def scons {α : Sort _} (x : α) (ρ : ℕ → α) : ℕ → α
  | 0 => x
  | n + 1 => ρ n

@[simp] theorem scons_zero {α : Sort _} (x : α) (ρ : ℕ → α) : scons x ρ 0 = x := rfl
@[simp] theorem scons_succ {α : Sort _} (x : α) (ρ : ℕ → α) (n : ℕ) :
    scons x ρ (n + 1) = ρ n := rfl

/-- A total combinatory algebra. -/
structure CombAlg where
  D : Type u
  app : D → D → D
  k : D
  s : D
  k_app : ∀ x y, app (app k x) y = x
  s_app : ∀ x y z, app (app (app s x) y) z = app (app x z) (app y z)

namespace CombAlg

/-- The degenerate one-point algebra: every PER model over it is sound and trivial. -/
def unit : CombAlg.{u} where
  D := PUnit
  app _ _ := PUnit.unit
  k := PUnit.unit
  s := PUnit.unit
  k_app _ _ := rfl
  s_app _ _ _ := rfl

/-- The identity combinator `S K K`. -/
def i (M : CombAlg) : M.D := M.app (M.app M.s M.k) M.k

theorem i_app (M : CombAlg) (x : M.D) : M.app M.i x = x := by
  simp only [i]
  rw [M.s_app, M.k_app]

end CombAlg

/-- Combinatory terms with de Bruijn variables. -/
inductive CTerm where
  | var (n : ℕ)
  | k
  | s
  | app (a b : CTerm)
  deriving DecidableEq

namespace CTerm

/-- Evaluation in an environment. -/
def eval (M : CombAlg) (ρ : ℕ → M.D) : CTerm → M.D
  | var n => ρ n
  | k => M.k
  | s => M.s
  | app a b => M.app (eval M ρ a) (eval M ρ b)

/-- Bracket abstraction of variable `0`; the other variables are lowered. -/
def abs : CTerm → CTerm
  | var 0 => app (app s k) k
  | var (n + 1) => app k (var n)
  | k => app k k
  | s => app k s
  | app a b => app (app s (abs a)) (abs b)

/-- The β-law of bracket abstraction, valid in every combinatory algebra. -/
theorem eval_abs (M : CombAlg) (ρ : ℕ → M.D) (t : CTerm) (x : M.D) :
    M.app ((abs t).eval M ρ) x = t.eval M (scons x ρ) := by
  induction t with
  | var n =>
    cases n with
    | zero => exact M.i_app x
    | succ n => exact M.k_app _ _
  | k => exact M.k_app _ _
  | s => exact M.k_app _ _
  | app a b iha ihb =>
    simp only [abs, eval]
    rw [M.s_app, iha, ihb]

/-- Renaming of combinatory terms. -/
def rename (r : ℕ → ℕ) : CTerm → CTerm
  | var n => var (r n)
  | k => k
  | s => s
  | app a b => app (rename r a) (rename r b)

theorem eval_rename (M : CombAlg) (ρ : ℕ → M.D) (r : ℕ → ℕ) (t : CTerm) :
    (t.rename r).eval M ρ = t.eval M (ρ ∘ r) := by
  induction t with
  | var n => rfl
  | k => rfl
  | s => rfl
  | app a b iha ihb => simp only [rename, eval, iha, ihb]

/-- Bracket abstraction commutes with renaming (lifted under the binder). -/
theorem abs_rename (r : ℕ → ℕ) (t : CTerm) :
    abs (t.rename (scons 0 (Nat.succ ∘ r))) = (abs t).rename r := by
  induction t with
  | var n =>
    cases n with
    | zero => rfl
    | succ n => rfl
  | k => rfl
  | s => rfl
  | app a b iha ihb => simp only [rename, abs, iha, ihb]

end CTerm

/-- Untyped de Bruijn λ-terms: the target of type erasure. -/
inductive ULam where
  | var (n : ℕ)
  | app (a b : ULam)
  | lam (t : ULam)
  deriving DecidableEq

namespace ULam

/-- Renaming. -/
def rename (ρ : ℕ → ℕ) : ULam → ULam
  | var n => var (ρ n)
  | app a b => app (rename ρ a) (rename ρ b)
  | lam t => lam (rename (scons 0 (Nat.succ ∘ ρ)) t)

/-- Lift a substitution under a binder. -/
def liftSub (σ : ℕ → ULam) : ℕ → ULam := scons (var 0) (fun n => rename Nat.succ (σ n))

/-- Simultaneous substitution. -/
def subst (σ : ℕ → ULam) : ULam → ULam
  | var n => σ n
  | app a b => app (subst σ a) (subst σ b)
  | lam t => lam (subst (liftSub σ) t)

/-- Substitute for variable `0` and lower the others. -/
def substOne (t u : ULam) : ULam := subst (scons u var) t

/-- Compilation to combinators by bracket abstraction. -/
def toComb : ULam → CTerm
  | var n => .var n
  | app a b => .app (toComb a) (toComb b)
  | lam t => CTerm.abs (toComb t)

/-- Evaluation in a combinatory algebra. -/
def eval (M : CombAlg) (ρ : ℕ → M.D) (t : ULam) : M.D := (toComb t).eval M ρ

@[simp] theorem eval_var (M : CombAlg) (ρ : ℕ → M.D) (n : ℕ) :
    (var n).eval M ρ = ρ n := rfl

@[simp] theorem eval_app (M : CombAlg) (ρ : ℕ → M.D) (a b : ULam) :
    (app a b).eval M ρ = M.app (a.eval M ρ) (b.eval M ρ) := rfl

/-- β for compiled abstractions. -/
theorem eval_lam (M : CombAlg) (ρ : ℕ → M.D) (t : ULam) (x : M.D) :
    M.app ((lam t).eval M ρ) x = t.eval M (scons x ρ) :=
  CTerm.eval_abs M ρ (toComb t) x

/-- Compilation commutes with renaming. -/
theorem toComb_rename (r : ℕ → ℕ) (t : ULam) : (t.rename r).toComb = t.toComb.rename r := by
  induction t generalizing r with
  | var n => rfl
  | app a b iha ihb => simp only [rename, toComb, CTerm.rename, iha, ihb]
  | lam t ih => simp only [rename, toComb, ih, CTerm.abs_rename]

theorem eval_rename (M : CombAlg) (ρ : ℕ → M.D) (r : ℕ → ℕ) (t : ULam) :
    (t.rename r).eval M ρ = t.eval M (ρ ∘ r) := by
  simp only [eval, toComb_rename, CTerm.eval_rename]

/-! Substitution is *not* sound for equality in an arbitrary combinatory
algebra (no ξ-rule): `(λ. x₁)[a b / x₀]` compiles to `S (K a) (K b)` but
`λ. x₁` under `x₀ ↦ a b` evaluates to `K (a b)`, distinct normal forms of weak
combinatory logic. The PER models only need substitution up to the PER
(`SystemF.Typed.subst_sound`), which holds because the arrow PER is
extensional. -/

end ULam

/-! ## The closed λ-term model modulo βη (via CSLib) -/

open Cslib.LambdaCalculus.LocallyNameless.Untyped

/-- Closed, locally closed λ-terms over CSLib's locally nameless syntax. -/
def ClosedTerm : Type := {t : Term ℕ // t.LC ∧ t.fv = ∅}

/-- One-step full βη-reduction between closed terms. -/
def ClosedTerm.Step (a b : ClosedTerm) : Prop := Term.FullBetaEta a.1 b.1

/-- Closed λ-terms modulo βη-conversion (`Quot` takes the equivalence closure). -/
def TermModelD : Type := Quot ClosedTerm.Step

namespace ClosedTerm

/-- A term is locally closed when it is `LcAt 0`. -/
theorem lc_of_lcAt {t : Term ℕ} (h : t.LcAt 0 = true) : t.LC := (Term.lcAt_iff_LC t).mp h

/-- A locally closed term is `LcAt k` for every `k`. -/
theorem lcAt_of_lc {t : Term ℕ} (h : t.LC) (k : ℕ) : t.LcAt k = true :=
  Term.lcAt_le t 0 k (Nat.zero_le _) ((Term.lcAt_iff_LC t).mpr h)

/-- One βη-step preserves closedness. -/
theorem closed_of_step {t u : Term ℕ} (h : Term.FullBetaEta t u) (ht : t.LC ∧ t.fv = ∅) :
    u.LC ∧ u.fv = ∅ := by
  rcases (show Term.FullBeta t u ∨ Term.FullEta t u from h) with h | h
  · have hfv := Term.FullBeta.step_not_fv h
    rw [ht.2] at hfv
    exact ⟨Term.FullBeta.step_lc_r h, Finset.subset_empty.mp hfv⟩
  · exact ⟨Term.FullEta.step_lc_r h, (Term.FullEta.step_not_fv h).symm.trans ht.2⟩

/-- βη-reducts of a closed term are closed and equal to it in the term model. -/
theorem mk_eq_of_reflTransGen (a : ClosedTerm) {t : Term ℕ}
    (h : Relation.ReflTransGen Term.FullBetaEta a.1 t) :
    ∃ ht, (Quot.mk ClosedTerm.Step a : TermModelD) = Quot.mk _ ⟨t, ht⟩ := by
  induction h with
  | refl => exact ⟨a.2, rfl⟩
  | tail _ hst ih =>
    obtain ⟨hb, e⟩ := ih
    exact ⟨closed_of_step hst hb, e.trans (Quot.sound hst)⟩

theorem mk_eq_of_steps (a b : ClosedTerm)
    (h : Relation.ReflTransGen Term.FullBetaEta a.1 b.1) :
    (Quot.mk ClosedTerm.Step a : TermModelD) = Quot.mk _ b := by
  obtain ⟨_, e⟩ := mk_eq_of_reflTransGen a h
  exact e

/-- A β-redex contracted to a given term. -/
theorem betaXi {M N P : Term ℕ} (hM : (Term.abs M).LC) (hN : N.LC) (e : Term.open' M N = P) :
    Term.Xi Term.Beta (.app (.abs M) N) P :=
  e ▸ Term.Xi.base (Term.Beta.beta hM hN)

end ClosedTerm

open ClosedTerm in
/-- `λx.λy.x`. -/
def closedK : ClosedTerm := ⟨.abs (.abs (.bvar 1)), lc_of_lcAt rfl, by simp⟩

open ClosedTerm in
/-- `λx.λy.λz. x z (y z)`. -/
def closedS : ClosedTerm :=
  ⟨.abs (.abs (.abs (.app (.app (.bvar 2) (.bvar 0)) (.app (.bvar 1) (.bvar 0))))),
    lc_of_lcAt rfl, by simp⟩

/-- Application of closed terms. -/
def closedApp (a b : ClosedTerm) : ClosedTerm :=
  ⟨.app a.1 b.1, Term.LC.app a.2.1 b.2.1, by simp [a.2.2, b.2.2]⟩

namespace ClosedTerm

theorem k_steps (x y : ClosedTerm) :
    Relation.ReflTransGen Term.FullBetaEta (closedApp (closedApp closedK x) y).1 x.1 := by
  have hx := x.2.1
  have hy := y.2.1
  have h1 : Term.FullBetaEta (closedApp (closedApp closedK x) y).1 (.app (.abs x.1) y.1) :=
    Or.inl (Term.Xi.appR hy (betaXi closedK.2.1 hx rfl))
  have h2 : Term.FullBetaEta (.app (.abs x.1) y.1) x.1 :=
    Or.inl (betaXi (lc_of_lcAt (by simp [lcAt_of_lc hx])) hy (Term.open_lc 0 y.1 x.1 hx))
  exact (Relation.ReflTransGen.single h1).tail h2

theorem s_steps (x y z : ClosedTerm) :
    Relation.ReflTransGen Term.FullBetaEta
      (closedApp (closedApp (closedApp closedS x) y) z).1
      (closedApp (closedApp x z) (closedApp y z)).1 := by
  have hx := x.2.1
  have hy := y.2.1
  have hz := z.2.1
  have h1 : Term.FullBetaEta (closedApp (closedApp (closedApp closedS x) y) z).1
      (.app (.app (.abs (.abs (.app (.app x.1 (.bvar 0)) (.app (.bvar 1) (.bvar 0))))) y.1) z.1) :=
    Or.inl (Term.Xi.appR hz (Term.Xi.appR hy (betaXi closedS.2.1 hx rfl)))
  have h2 : Term.FullBetaEta
      (.app (.app (.abs (.abs (.app (.app x.1 (.bvar 0)) (.app (.bvar 1) (.bvar 0))))) y.1) z.1)
      (.app (.abs (.app (.app x.1 (.bvar 0)) (.app y.1 (.bvar 0)))) z.1) :=
    Or.inl (Term.Xi.appR hz (betaXi (lc_of_lcAt (by simp [lcAt_of_lc hx])) hy
      (by simp [Term.open', Term.openRec, Term.open_lc _ _ _ hx])))
  have h3 : Term.FullBetaEta (.app (.abs (.app (.app x.1 (.bvar 0)) (.app y.1 (.bvar 0)))) z.1)
      (closedApp (closedApp x z) (closedApp y z)).1 :=
    Or.inl (betaXi (lc_of_lcAt (by simp [lcAt_of_lc hx, lcAt_of_lc hy])) hz
      (by simp [Term.open', Term.openRec, Term.open_lc _ _ _ hx, Term.open_lc _ _ _ hy,
        closedApp]))
  exact ((Relation.ReflTransGen.single h1).tail h2).tail h3

/-! ### Normal forms: a syntactic redex detector -/

/-- Is the term an abstraction? -/
def isAbsB : Term ℕ → Bool
  | .abs _ => true
  | _ => false

/-- Is the term of the shape `M (bvar 0)` (the body of an η-redex)? -/
def etaShape : Term ℕ → Bool
  | .app _ (.bvar 0) => true
  | _ => false

/-- Does the term contain a β- or η-redex pattern? -/
def hasRedex : Term ℕ → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .app a b => isAbsB a || hasRedex a || hasRedex b
  | .abs t => etaShape t || hasRedex t

theorem isAbsB_open (a : Term ℕ) (k : ℕ) (x : ℕ) :
    isAbsB (Term.openRec k (.fvar x) a) = isAbsB a := by
  cases a with
  | bvar i =>
    simp only [Term.openRec]
    split_ifs <;> rfl
  | _ => rfl

theorem etaShape_open (t : Term ℕ) (k : ℕ) (x : ℕ) :
    etaShape (Term.openRec (k + 1) (.fvar x) t) = etaShape t := by
  cases t with
  | app a b =>
    cases b with
    | bvar i =>
      simp only [Term.openRec]
      split_ifs with h
      · cases i with
        | zero => omega
        | succ i => rfl
      · cases i <;> rfl
    | _ => rfl
  | bvar i =>
    simp only [Term.openRec]
    split_ifs <;> rfl
  | _ => rfl

theorem hasRedex_open (t : Term ℕ) (k : ℕ) (x : ℕ)
    (h : hasRedex (Term.openRec k (.fvar x) t) = true) : hasRedex t = true := by
  induction t generalizing k with
  | bvar i =>
    simp only [Term.openRec] at h
    split_ifs at h <;> simp [hasRedex] at h
  | fvar => simp [Term.openRec, hasRedex] at h
  | app a b iha ihb =>
    simp only [Term.openRec, hasRedex, isAbsB_open, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (iha k h))
    · exact Or.inr (ihb k h)
  | abs t ih =>
    simp only [Term.openRec, hasRedex, etaShape_open, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ih (k + 1) h)

theorem hasRedex_of_xi {R : Term ℕ → Term ℕ → Prop} (hR : ∀ t u, R t u → hasRedex t = true)
    {t u : Term ℕ} (h : Term.Xi R t u) : hasRedex t = true := by
  induction h with
  | base h => exact hR _ _ h
  | appL _ _ ih => simp [hasRedex, ih]
  | appR _ _ ih => simp [hasRedex, ih]
  | abs xs _ ih =>
    obtain ⟨x, hx⟩ := Cslib.HasFresh.fresh_exists xs
    simp [hasRedex, hasRedex_open _ 0 x (ih x hx)]

theorem hasRedex_of_step {t u : Term ℕ} (h : Term.FullBetaEta t u) : hasRedex t = true := by
  rcases (show Term.FullBeta t u ∨ Term.FullEta t u from h) with h | h
  · exact hasRedex_of_xi (fun _ _ hb => by cases hb; simp [hasRedex, isAbsB]) h
  · exact hasRedex_of_xi (fun _ _ he => by cases he; simp [hasRedex, etaShape]) h

theorem normal_of_hasRedex {t : Term ℕ} (h : hasRedex t = false) :
    Relation.Normal Term.FullBetaEta t := by
  rintro ⟨u, hu⟩
  simp [hasRedex_of_step hu] at h

theorem eqvGen_val {a b : ClosedTerm} (h : Relation.EqvGen ClosedTerm.Step a b) :
    Relation.EqvGen Term.FullBetaEta a.1 b.1 := by
  induction h with
  | rel _ _ h => exact .rel _ _ h
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end ClosedTerm

open ClosedTerm in
/-- The term model: closed λ-terms modulo βη, a total combinatory algebra. -/
def termModel : CombAlg.{0} where
  D := TermModelD
  app := Quot.lift₂ (fun a b => Quot.mk _ (closedApp a b))
    (fun a _ _ h => Quot.sound (by
      rcases (show Term.FullBeta _ _ ∨ Term.FullEta _ _ from h) with h | h
      · exact Or.inl (Term.Xi.appL a.2.1 h)
      · exact Or.inr (Term.Xi.appL a.2.1 h)))
    (fun _ _ b h => Quot.sound (by
      rcases (show Term.FullBeta _ _ ∨ Term.FullEta _ _ from h) with h | h
      · exact Or.inl (Term.Xi.appR b.2.1 h)
      · exact Or.inr (Term.Xi.appR b.2.1 h)))
  k := Quot.mk _ closedK
  s := Quot.mk _ closedS
  k_app := by
    intro x y
    induction x using Quot.ind
    induction y using Quot.ind
    exact mk_eq_of_steps _ _ (k_steps _ _)
  s_app := by
    intro x y z
    induction x using Quot.ind
    induction y using Quot.ind
    induction z using Quot.ind
    exact mk_eq_of_steps _ _ (s_steps _ _ _)

/-- Nontriviality of the term model, from CSLib's βη-confluence
(`Term.confluent_beta_eta`): `K` and `S` are distinct βη-normal forms. -/
theorem termModel_k_ne_s : termModel.k ≠ termModel.s := by
  intro h
  have hE := ClosedTerm.eqvGen_val
    (Quot.eqvGen_exact (r := ClosedTerm.Step) (a := closedK) (b := closedS) h)
  have := Relation.ChurchRosser.normal_eq
    (Relation.Confluent.to_churchRosser Term.confluent_beta_eta)
    (ClosedTerm.normal_of_hasRedex (t := closedK.1) rfl)
    (ClosedTerm.normal_of_hasRedex (t := closedS.1) rfl) hE
  simp [closedK, closedS] at this

end Silmaril.Calculi.LambdaCube.PERModel
