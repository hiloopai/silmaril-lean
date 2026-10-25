module

public import Silmaril.Logic.HOLLight.Consilience.Logic

@[expose] public section

/-!
# Explicit sound natural-number arithmetic in HOL Light

Four monomorphic constants denote zero, successor, addition and multiplication
on HOL's individual carrier. The additional theory consists of seven schematic
Robinson equations/axioms, alongside the exactly matched classical axioms.
A standard Nat model validates this explicit theory. This is arithmetic
interpretation evidence, not a Q/PA derivation translation: quantifier and
equality transport from a separate first-order calculus are separate obligations.
-/
namespace Silmaril.Logic.HOLLight.Consilience.NatArithmetic

universe u

def signature : Signature := ⟨[],
  [⟨0, .ind⟩, ⟨0, .arr .ind .ind⟩,
   ⟨0, .arr .ind (.arr .ind .ind)⟩, ⟨0, .arr .ind (.arr .ind .ind)⟩]⟩

theorem signature_valid : signature.Valid := by
  simp [signature, Signature.Valid, Scheme.WellFormed, Ty.WellFormed, Ty.Scoped]

def zero : Term := .user 0 []
def succ (t : Term) : Term := .app (.user 1 []) t
def add (s t : Term) : Term := .app (.app (.user 2 []) s) t
def mul (s t : Term) : Term := .app (.app (.user 3 []) s) t

def numeral : Nat → Term
  | 0 => zero
  | n + 1 => succ (numeral n)

/-- The raw HOL theory uses schematic free variables at individual type. -/
def arithmeticAxioms : Theory :=
  let x := Term.free 0 .ind
  let y := Term.free 1 .ind
  [Term.neg (Term.equal .ind (succ x) zero),
   Term.imp (Term.equal .ind (succ x) (succ y)) (Term.equal .ind x y),
   Term.imp (Term.neg (Term.equal .ind x zero))
     (Term.ex .ind (.lam .ind (Term.equal .ind x.weaken (succ (.bound 0))))),
   Term.equal .ind (add x zero) x,
   Term.equal .ind (add x (succ y)) (succ (add x y)),
   Term.equal .ind (mul x zero) zero,
   Term.equal .ind (mul x (succ y)) (add (mul x y) x)]

def theory : Theory := Consilience.classicalTheory ++ arithmeticAxioms

/-- Actual constant interpretation, including the scheme lookup checks. -/
def model : Model.{u} signature where
  toTypeModel := TypeModel.standard
  constant := by
    intro c s lookup args
    cases c with
    | zero =>
      have hs : s = ⟨0, .ind⟩ := (Option.some.inj lookup).symm
      subst s
      exact ULift.up 0
    | succ c =>
      cases c with
      | zero =>
        have hs : s = ⟨0, .arr .ind .ind⟩ := (Option.some.inj lookup).symm
        subst s
        exact fun x => ULift.up (x.down + 1)
      | succ c =>
        cases c with
        | zero =>
          have hs : s = ⟨0, .arr .ind (.arr .ind .ind)⟩ := (Option.some.inj lookup).symm
          subst s
          exact fun x y => ULift.up (x.down + y.down)
        | succ c =>
          cases c with
          | zero =>
            have hs : s = ⟨0, .arr .ind (.arr .ind .ind)⟩ := (Option.some.inj lookup).symm
            subst s
            exact fun x y => ULift.up (x.down * y.down)
          | succ c => simp [signature] at lookup

theorem ind_wf : Ty.ind.WellFormed signature.tyOps := trivial

theorem scheme_wf (A : Ty) (hA : A.WellFormed []) (closed : A.Scoped 0) :
    (Scheme.mk 0 A).WellFormed signature.tyOps := ⟨hA, closed⟩

theorem zeroTyped (Γ : List Ty) : Typed signature Γ zero .ind :=
  .user rfl (scheme_wf .ind trivial trivial) rfl (by simp)

theorem succTyped {Γ t} (ht : Typed signature Γ t .ind) : Typed signature Γ (succ t) .ind :=
  .app (.user rfl (scheme_wf (.arr .ind .ind) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩) rfl (by simp)) ht

theorem addTyped {Γ s t} (hs : Typed signature Γ s .ind) (ht : Typed signature Γ t .ind) :
    Typed signature Γ (add s t) .ind :=
  .app (.app (.user rfl (scheme_wf (.arr .ind (.arr .ind .ind)) ⟨trivial, trivial, trivial⟩ ⟨trivial, trivial, trivial⟩)
    rfl (by simp)) hs) ht

theorem mulTyped {Γ s t} (hs : Typed signature Γ s .ind) (ht : Typed signature Γ t .ind) :
    Typed signature Γ (mul s t) .ind :=
  .app (.app (.user rfl (scheme_wf (.arr .ind (.arr .ind .ind)) ⟨trivial, trivial, trivial⟩ ⟨trivial, trivial, trivial⟩)
    rfl (by simp)) hs) ht

namespace Evaluation

variable {ρ : TypeValuation.{u}} {ν : FreeEnv model ρ} {Γ : List Ty}
  {η : BoundEnv model ρ Γ}

/-- Each constant is evaluated by its declared monomorphic scheme. -/
theorem zero : Eval model ρ ν η NatArithmetic.zero.encode .ind (ULift.up 0) := by
  exact .const η (.user (name := 0) rfl (scheme_wf .ind trivial trivial) rfl (by simp))

theorem succ {t : Term} {x : Value model ρ .ind}
    (ht : Eval model ρ ν η t.encode .ind x) :
    Eval model ρ ν η (NatArithmetic.succ t).encode .ind (ULift.up (x.down + 1)) := by
  exact .app (.const η (.user (name := 1) rfl (scheme_wf (.arr .ind .ind) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩)
    rfl (by simp))) ht

theorem add {s t : Term} {x y : Value model ρ .ind}
    (hs : Eval model ρ ν η s.encode .ind x) (ht : Eval model ρ ν η t.encode .ind y) :
    Eval model ρ ν η (NatArithmetic.add s t).encode .ind (ULift.up (x.down + y.down)) := by
  exact .app (.app (.const η (.user (name := 2) rfl
    (scheme_wf (.arr .ind (.arr .ind .ind)) ⟨trivial, trivial, trivial⟩ ⟨trivial, trivial, trivial⟩) rfl (by simp))) hs) ht

theorem mul {s t : Term} {x y : Value model ρ .ind}
    (hs : Eval model ρ ν η s.encode .ind x) (ht : Eval model ρ ν η t.encode .ind y) :
    Eval model ρ ν η (NatArithmetic.mul s t).encode .ind (ULift.up (x.down * y.down)) := by
  exact .app (.app (.const η (.user (name := 3) rfl
    (scheme_wf (.arr .ind (.arr .ind .ind)) ⟨trivial, trivial, trivial⟩ ⟨trivial, trivial, trivial⟩) rfl (by simp))) hs) ht

theorem numeral (n : Nat) : Eval model ρ ν η (NatArithmetic.numeral n).encode .ind (ULift.up n) := by
  induction n with
  | zero => exact zero
  | succ n ih => exact succ ih

end Evaluation

theorem arithmeticAxioms_typed : ∀ p ∈ arithmeticAxioms, Typed signature [] p .bool := by
  intro p hp
  simp only [arithmeticAxioms, List.mem_cons, List.not_mem_nil, or_false] at hp
  have hx : Typed signature [] (.free 0 .ind) .ind := .free 0 ind_wf
  have hy : Typed signature [] (.free 1 .ind) .ind := .free 1 ind_wf
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ((succTyped hx).equal ind_wf (zeroTyped [])).neg
  · exact ((succTyped hx).equal ind_wf (succTyped hy)).imp (hx.equal ind_wf hy)
  · exact (hx.equal ind_wf (zeroTyped [])).neg.imp
      (Typed.ex ind_wf (.lam ind_wf
        (Typed.equal ind_wf (.free 0 ind_wf) (succTyped (.bound rfl ind_wf)))))
  · exact (addTyped hx (zeroTyped [])).equal ind_wf hx
  · exact (addTyped hx (succTyped hy)).equal ind_wf (succTyped (addTyped hx hy))
  · exact (mulTyped hx (zeroTyped [])).equal ind_wf (zeroTyped [])
  · exact (mulTyped hx (succTyped hy)).equal ind_wf (addTyped (mulTyped hx hy) hx)

theorem theory_typed : ∀ p ∈ theory, Typed signature [] p .bool := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · apply Typed.encode_iff.mp
    apply classicalTheory_wellFormed signature p.encode
    rw [← encode_classicalTheory]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · exact arithmeticAxioms_typed p hp

/-- Each listed arithmetic axiom has an actual proof in the explicitly named theory. -/
def axiomProof (p : Term) (hp : p ∈ arithmeticAxioms) : Proof signature theory ∅ p :=
  .ax (List.mem_append.mpr (.inr hp)) (arithmeticAxioms_typed p hp)

def assign (x y : Term) (n : Nat) (A : Ty) : Term :=
  if A = .ind then if n = 0 then x else if n = 1 then y else .free n A else .free n A

theorem assignTyped {x y : Term} (hx : Typed signature [] x .ind) (hy : Typed signature [] y .ind)
    (n : Nat) (A : Ty) (wf : A.WellFormed signature.tyOps) :
    Typed signature [] (assign x y n A) A := by
  unfold assign
  split
  · rename_i hA
    subst A
    split
    · exact hx
    · split
      · exact hy
      · exact .free n wf
  · exact .free n wf

/-- Instantiate the addition-zero axiom at an arbitrary typed term. -/
def addZero {x : Term} (hx : Typed signature [] x .ind) :
    Proof signature theory ∅ (Term.equal .ind (add x zero) x) := by
  have base := axiomProof (Term.equal .ind (add (.free 0 .ind) zero) (.free 0 .ind))
    (by simp [arithmeticAxioms])
  simpa [Term.equal, Term.freeSubst, add, zero, assign] using
    Proof.subst (assign x zero) (assignTyped hx (zeroTyped [])) base

def addSucc {x y : Term} (hx : Typed signature [] x .ind) (hy : Typed signature [] y .ind) :
    Proof signature theory ∅ (Term.equal .ind (add x (succ y)) (succ (add x y))) := by
  have base := axiomProof
    (Term.equal .ind (add (.free 0 .ind) (succ (.free 1 .ind))) (succ (add (.free 0 .ind) (.free 1 .ind))))
    (by simp [arithmeticAxioms])
  simpa [Term.equal, Term.freeSubst, add, succ, assign] using
    Proof.subst (assign x y) (assignTyped hx hy) base

def mulZero {x : Term} (hx : Typed signature [] x .ind) :
    Proof signature theory ∅ (Term.equal .ind (mul x zero) zero) := by
  have base := axiomProof (Term.equal .ind (mul (.free 0 .ind) zero) zero)
    (by simp [arithmeticAxioms])
  simpa [Term.equal, Term.freeSubst, mul, zero, assign] using
    Proof.subst (assign x zero) (assignTyped hx (zeroTyped [])) base

def mulSucc {x y : Term} (hx : Typed signature [] x .ind) (hy : Typed signature [] y .ind) :
    Proof signature theory ∅ (Term.equal .ind (mul x (succ y)) (add (mul x y) x)) := by
  have base := axiomProof
    (Term.equal .ind (mul (.free 0 .ind) (succ (.free 1 .ind)))
      (add (mul (.free 0 .ind) (.free 1 .ind)) (.free 0 .ind)))
    (by simp [arithmeticAxioms])
  simpa [Term.equal, Term.freeSubst, add, mul, succ, assign] using
    Proof.subst (assign x y) (assignTyped hx hy) base

/-- A concrete computation proof combines axiom instantiation, congruence and transitivity. -/
def one_add_one : Proof signature theory ∅
    (Term.equal .ind (add (numeral 1) (numeral 1)) (numeral 2)) := by
  have h1 : Typed signature [] (numeral 1) .ind := succTyped (zeroTyped [])
  have step := addSucc h1 (zeroTyped [])
  have hs : Typed signature [] (.user 1 []) (.arr .ind .ind) :=
    .user rfl (scheme_wf (.arr .ind .ind) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩) rfl (by simp)
  have congruence := Proof.app (Proof.refl (theory := theory) hs) (addZero h1)
  have result := Proof.trans step congruence
  simpa only [Finset.empty_union, numeral, succ] using result

/-- Transport the concrete computation into the native sound kernel. -/
theorem native_one_add_one : Derives signature (encodeTheory theory) ∅
    (Tm.equal .ind (add (numeral 1) (numeral 1)).encode (numeral 2).encode) := by
  simpa using one_add_one.encode

-- Carrier abbreviations reduce through the semantic type interpretation.
set_option backward.isDefEq.respectTransparency false in
/-- The seven additional arithmetic object axioms hold at every valuation. -/
theorem model_arithmetic : HOLLight.Models model.{u} (encodeTheory arithmeticAxioms) := by
  intro p hp ρ ν
  change p ∈ arithmeticAxioms.map Term.encode at hp
  obtain ⟨p, hmember, rfl⟩ := List.mem_map.mp hp
  simp only [arithmeticAxioms, List.mem_cons, List.not_mem_nil, or_false] at hmember
  have hx : Eval model ρ ν BoundEnv.empty (Term.free 0 .ind).encode .ind (ν 0 .ind) :=
    .fvar _ 0 ind_wf
  have hy : Eval model ρ ν BoundEnv.empty (Term.free 1 .ind).encode .ind (ν 1 .ind) :=
    .fvar _ 1 ind_wf
  rcases hmember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨Carrier.neg (Carrier.eq.{u} Carrier.ind.{u} (ULift.up ((ν 0 .ind).down + 1)) (ULift.up 0)), ?_, ?_⟩
    · simp only [Term.encode_neg, Term.encode_equal]
      exact Eval.neg ((Evaluation.succ hx).equal Evaluation.zero)
    · simp [Carrier.truth_neg, Carrier.truth_eq, ULift.ext_iff]
  · refine ⟨Carrier.imp (Carrier.eq.{u} Carrier.ind.{u} (ULift.up ((ν 0 .ind).down + 1)) (ULift.up ((ν 1 .ind).down + 1))) (Carrier.eq.{u} Carrier.ind.{u} (ν 0 .ind) (ν 1 .ind)), ?_, ?_⟩
    · simp only [Term.encode_imp, Term.encode_equal]
      exact Eval.imp ((Evaluation.succ hx).equal (Evaluation.succ hy)) (hx.equal hy)
    · simp only [Carrier.truth_imp, Carrier.truth_eq, ULift.ext_iff, Nat.add_right_cancel_iff]
      exact fun h => h
  · have hP : Eval model ρ ν BoundEnv.empty
        (Term.lam .ind (Term.equal .ind (Term.free 0 .ind).weaken (succ (.bound 0)))).encode
        (.arr .ind .bool)
        (fun z => Carrier.eq.{u} Carrier.ind.{u} (ν 0 .ind) (ULift.up (z.down + 1))) := by
      apply Eval.lam ind_wf
      intro z
      exact Eval.equal (.fvar _ 0 ind_wf) (Evaluation.succ (.bvar _ rfl ind_wf))
    refine ⟨Carrier.imp (Carrier.neg (Carrier.eq.{u} Carrier.ind.{u} (ν 0 .ind) (ULift.up 0))) (Carrier.ex.{u} Carrier.ind.{u} (fun z => Carrier.eq.{u} Carrier.ind.{u} (ν 0 .ind) (ULift.up (z.down + 1)))), ?_, ?_⟩
    · simp only [Term.encode_imp, Term.encode_neg, Term.encode_equal, Term.encode_ex]
      exact Eval.imp (Eval.neg (hx.equal Evaluation.zero)) (Eval.ex ind_wf hP)
    · simp only [Carrier.truth_imp, Carrier.truth_neg, Carrier.truth_eq, Carrier.truth_ex]
      intro hn
      have hn' : (ν 0 .ind).down ≠ 0 := by
        intro h
        apply hn
        exact ULift.ext h
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn'
      exact ⟨ULift.up k, ULift.ext hk⟩
  · refine ⟨Carrier.eq.{u} Carrier.ind.{u} (ULift.up ((ν 0 .ind).down + 0)) (ν 0 .ind), ?_, ?_⟩
    · simp only [Term.encode_equal]
      exact (Evaluation.add hx Evaluation.zero).equal hx
    · simp only [Carrier.truth_eq, ULift.ext_iff, Nat.add_zero]
  · refine ⟨Carrier.eq.{u} Carrier.ind.{u} (ULift.up ((ν 0 .ind).down + ((ν 1 .ind).down + 1))) (ULift.up (((ν 0 .ind).down + (ν 1 .ind).down) + 1)), ?_, ?_⟩
    · simp only [Term.encode_equal]
      exact (Evaluation.add hx (Evaluation.succ hy)).equal (Evaluation.succ (Evaluation.add hx hy))
    · simp [Carrier.truth_eq, Nat.add_assoc]
  · refine ⟨Carrier.eq.{u} Carrier.ind.{u} (ULift.up ((ν 0 .ind).down * 0)) (ULift.up 0), ?_, ?_⟩
    · simp only [Term.encode_equal]
      exact (Evaluation.mul hx Evaluation.zero).equal Evaluation.zero
    · simp only [Carrier.truth_eq, Nat.mul_zero]
  · refine ⟨Carrier.eq.{u} Carrier.ind.{u} (ULift.up ((ν 0 .ind).down * ((ν 1 .ind).down + 1))) (ULift.up (((ν 0 .ind).down * (ν 1 .ind).down) + (ν 0 .ind).down)), ?_, ?_⟩
    · simp only [Term.encode_equal]
      exact (Evaluation.mul hx (Evaluation.succ hy)).equal (Evaluation.add (Evaluation.mul hx hy) hx)
    · simp [Carrier.truth_eq, Nat.mul_add]

/-- This explicitly extended classical theory has a genuine sound HOL model. -/
theorem model_theory : HOLLight.Models model.{u} (encodeTheory theory) := by
  intro p hp
  change p ∈ encodeTheory Consilience.classicalTheory ++ encodeTheory arithmeticAxioms at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact model.models_classical p (by simpa using hp)
  · exact model_arithmetic p hp

theorem model_simple_theory : Consilience.Models model.{u} theory :=
  models_encode_iff.mp model_theory

theorem theory_consistent : ¬ Derives signature (encodeTheory theory) ∅ Tm.falsity :=
  consistent_of_model model.{0} model_theory

end Silmaril.Logic.HOLLight.Consilience.NatArithmetic
