module

public import Silmaril.Logic.SAT.Institution.Defs
import Silmaril.Logic.ManyValued.Thms

public section

namespace Silmaril.Proofs.Logic.SAT.Institution

open Silmaril.Logic.SAT.Institution Silmaril.Logic.ManyValued

universe u v w x
variable {A : Type u} {B : Type v}

theorem rename_id : Problem.rename (id : A → A) = id := by
  funext F
  have h : Literal.rename (id : A → A) = id := by funext l; cases l; rfl
  simp [Problem.rename, h]

theorem rename_comp {D : Type w} (f : A → B) (g : B → D) :
    Problem.rename (g ∘ f) = Problem.rename g ∘ Problem.rename f := by
  funext F
  simp [Problem.rename, List.map_map, Function.comp_def, Literal.rename]

theorem evalWith_rename {V : Type w} (top bot : V) (neg : V → V) (conj disj : V → V → V)
    (f : A → B) (v : B → V) (F : Problem A) :
    (F.rename f).evalWith top bot neg conj disj v = F.evalWith top bot neg conj disj (reduct f v) := by
  simp only [Problem.rename, Problem.evalWith, Clause.evalWith, List.foldr_map]
  rfl

private theorem evalWith_bool (v : TotalValuation A) (F : Problem A) :
    F.evalWith true false Bool.not Bool.and Bool.or v = F.eval v := by
  have clause (C : Clause A) :
      Clause.evalWith false Bool.not Bool.or v C = C.any (fun l => v l.atom == l.positive) := by
    induction C with
    | nil => rfl
    | cons l C ih =>
      have literal : l.evalWith Bool.not v = (v l.atom == l.positive) := by
        cases l with
        | mk a positive => cases positive <;> cases h : v a <;> simp [Literal.evalWith, h]
      simpa only [Clause.evalWith, List.foldr_cons, List.any_cons, literal] using
        congrArg (Bool.or (v l.atom == l.positive)) ih
  induction F with
  | nil => rfl
  | cons C F ih =>
    simpa only [Problem.evalWith, Problem.eval, List.foldr_cons, List.all_cons, clause] using
      congrArg (Bool.and (C.any fun l => v l.atom == l.positive)) ih

theorem eval_rename (f : A → B) (v : TotalValuation B) (F : Problem A) :
    (F.rename f).eval v = F.eval (reduct f v) := by
  simp only [Problem.rename, Problem.eval, List.all_map, List.any_map,
    Function.comp_def, Literal.rename, reduct]

theorem eval_ofCNF (v : TotalValuation Nat) (F : Silmaril.Logic.SAT.CNF) :
    (Problem.ofCNF F).eval v = Silmaril.Logic.SAT.CNF.eval v F := by
  simp only [Problem.ofCNF, Problem.eval, Silmaril.Logic.SAT.CNF.eval, List.all_map,
    List.any_map, Function.comp_def]
  rfl

private theorem evalWith_rel {V : Type w} {W : Type x} (R : V → W → Prop)
    {top bot : V} {top' bot' : W} {neg : V → V} {neg' : W → W}
    {conj disj : V → V → V} {conj' disj' : W → W → W}
    (htop : R top top') (hbot : R bot bot')
    (hneg : ∀ {a a'}, R a a' → R (neg a) (neg' a'))
    (hconj : ∀ {a a' b b'}, R a a' → R b b' → R (conj a b) (conj' a' b'))
    (hdisj : ∀ {a a' b b'}, R a a' → R b b' → R (disj a b) (disj' a' b'))
    {v : A → V} {v' : A → W} (hv : ∀ a, R (v a) (v' a)) (F : Problem A) :
    R (F.evalWith top bot neg conj disj v) (F.evalWith top' bot' neg' conj' disj' v') := by
  apply List.foldr_rel htop
  intro C _ acc acc' hacc
  refine hconj ?_ hacc
  apply List.foldr_rel hbot
  intro l _ rest rest' hrest
  refine hdisj ?_ hrest
  unfold Literal.evalWith
  split
  · exact hv l.atom
  · exact hneg (hv l.atom)

theorem evalK3Option_eq_evalWith (v : PartialValuation A) (F : Problem A) :
    F.evalK3Option v =
      F.evalWith (some true) (some false) (Option.map Bool.not)
        (fun a b => if a = some false ∨ b = some false then some false
          else if a = some true ∧ b = some true then some true else none)
        (fun a b => if a = some true ∨ b = some true then some true
          else if a = some false ∧ b = some false then some false else none) v := by
  refine evalWith_rel (fun k o => K3.toOptionBool k = o) rfl rfl ?_ ?_ ?_ ?_ F
  · rintro a _ rfl
    exact K3.toOptionBool_neg a
  · rintro a _ b _ rfl rfl
    cases a <;> cases b <;> rfl
  · rintro a _ b _ rfl rfl
    cases a <;> cases b <;> rfl
  · intro a
    exact K3.toOptionBool_ofOptionBool (v a)

theorem evalK3_total (v : TotalValuation A) (F : Problem A) :
    F.evalK3 (K3.ofBool ∘ v) = K3.ofBool (F.eval v) := by
  rw [← evalWith_bool v F]
  symm
  refine evalWith_rel (fun b k => K3.ofBool b = k) rfl rfl ?_ ?_ ?_ (fun _ => rfl) F
  · rintro b _ rfl
    exact K3.ofBool_not b
  · rintro b _ c _ rfl rfl
    exact K3.ofBool_and b c
  · rintro b _ c _ rfl rfl
    exact K3.ofBool_or b c

theorem evalEvidence_bits (v : EvidenceValuation A) (F : Problem A) :
    ((F.evalEvidence v).support, (F.evalEvidence v).refute) =
      F.evalWith (true, false) (false, true) Prod.swap
        (fun a b => (a.1 && b.1, a.2 || b.2))
        (fun a b => (a.1 || b.1, a.2 && b.2))
        (fun a => ((v a).support, (v a).refute)) := by
  refine evalWith_rel (fun e p => (FDE.support e, FDE.refute e) = p) rfl rfl
    ?_ ?_ ?_ (fun _ => rfl) F
  · rintro a _ rfl
    simp only [FDE.support_neg, FDE.refute_neg, Prod.swap]
  · rintro a _ b _ rfl rfl
    simp only [FDE.conj, FDE.support_ofBits, FDE.refute_ofBits]
  · rintro a _ b _ rfl rfl
    simp only [FDE.disj, FDE.support_ofBits, FDE.refute_ofBits]

theorem evalEvidence_ofK3 (v : K3Valuation A) (F : Problem A) :
    F.evalEvidence (K3.toFDE ∘ v) = (F.evalK3 v).toFDE := by
  symm
  refine evalWith_rel (fun k e => K3.toFDE k = e) rfl rfl ?_ ?_ ?_ (fun _ => rfl) F
  · rintro a _ rfl
    exact K3.toFDE_neg a
  · rintro a _ b _ rfl rfl
    exact K3.toFDE_inf a b
  · rintro a _ b _ rfl rfl
    exact K3.toFDE_sup a b

theorem evalEvidence_informationLE {v v' : EvidenceValuation A}
    (hv : ∀ a, (⟨v a⟩ : FDE.Information) ≤ ⟨v' a⟩) (F : Problem A) :
    (⟨F.evalEvidence v⟩ : FDE.Information) ≤ ⟨F.evalEvidence v'⟩ := by
  refine evalWith_rel (fun a b => (⟨a⟩ : FDE.Information) ≤ ⟨b⟩)
    le_rfl le_rfl ?_ ?_ ?_ hv F
  · intro a a' h
    exact (FDE.Information.neg_le_neg_iff ⟨a⟩ ⟨a'⟩).2 h
  · intro a a' b b' ha hb
    simp only [FDE.Information.le_iff_bits, FDE.conj, FDE.support_ofBits,
      FDE.refute_ofBits, Bool.le_iff_imp, Bool.and_eq_true, Bool.or_eq_true] at *
    exact ⟨And.imp ha.1 hb.1, Or.imp ha.2 hb.2⟩
  · intro a a' b b' ha hb
    simp only [FDE.Information.le_iff_bits, FDE.disj, FDE.support_ofBits,
      FDE.refute_ofBits, Bool.le_iff_imp, Bool.and_eq_true, Bool.or_eq_true] at *
    exact ⟨Or.imp ha.1 hb.1, And.imp ha.2 hb.2⟩

theorem evalK3_informationLE {v v' : K3Valuation A}
    (hv : ∀ a, (⟨v a⟩ : K3.Information) ≤ ⟨v' a⟩) (F : Problem A) :
    (⟨F.evalK3 v⟩ : K3.Information) ≤ ⟨F.evalK3 v'⟩ := by
  apply (K3.Information.toFDE_le_iff _ _).1
  change (⟨(F.evalK3 v).toFDE⟩ : FDE.Information) ≤ ⟨(F.evalK3 v').toFDE⟩
  rw [← evalEvidence_ofK3 v F, ← evalEvidence_ofK3 v' F]
  exact evalEvidence_informationLE (fun a => (K3.Information.toFDE_le_iff _ _).2 (hv a)) F

end Silmaril.Proofs.Logic.SAT.Institution
