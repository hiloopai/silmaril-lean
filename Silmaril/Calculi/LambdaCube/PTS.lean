module

public import Silmaril.Prelude.DeBruijn
public import Silmaril.Logic.Metatheory.InferenceSystemCat
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

set_option autoImplicit true

/-! # Pure type systems and the eight cube specifications

One shared de Bruijn syntax; conversion is the compatible equivalence generated
by β. Context entries are stored relative to their older tail. No normalization
or subject reduction is assumed in the definition of typing.
-/

namespace Silmaril.Calculi.LambdaCube

/-- A PTS specification, with no functionality assumptions on its relations. -/
structure Specification where
  Sorts : Type
  Ax : Sorts → Sorts → Prop
  Rule : Sorts → Sorts → Sorts → Prop

/-- Pseudo-terms: types and terms share syntax. -/
inductive Pseudo (S : Type) where
  | sort : S → Pseudo S
  | var : Nat → Pseudo S
  | app : Pseudo S → Pseudo S → Pseudo S
  | lam : Pseudo S → Pseudo S → Pseudo S
  | pi : Pseudo S → Pseudo S → Pseudo S
  deriving DecidableEq

namespace Pseudo

/-- Capture-avoiding renaming, reusing the shared binder lifting operation. -/
def rename (ρ : Nat → Nat) : Pseudo S → Pseudo S
  | .sort s => .sort s
  | .var n => .var (ρ n)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .lam A b => .lam (rename ρ A) (rename (DeBruijn.lift ρ) b)
  | .pi A B => .pi (rename ρ A) (rename (DeBruijn.lift ρ) B)

/-- Lift a simultaneous substitution under a binder. -/
def liftSub (σ : Nat → Pseudo S) : Nat → Pseudo S
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Capture-avoiding simultaneous substitution. -/
def subst (σ : Nat → Pseudo S) : Pseudo S → Pseudo S
  | .sort s => .sort s
  | .var n => σ n
  | .app f a => .app (subst σ f) (subst σ a)
  | .lam A b => .lam (subst σ A) (subst (liftSub σ) b)
  | .pi A B => .pi (subst σ A) (subst (liftSub σ) B)

/-- Substitute for the newest variable and discharge its binder. -/
def substOne (b a : Pseudo S) : Pseudo S :=
  subst (fun | 0 => a | n + 1 => .var n) b

/-- Untyped β-convertibility, including congruence in annotations. -/
inductive Conv : Pseudo S → Pseudo S → Prop where
  | refl (t) : Conv t t
  | symm : Conv t u → Conv u t
  | trans : Conv t u → Conv u v → Conv t v
  | beta (A b a) : Conv (.app (.lam A b) a) (substOne b a)
  | app : Conv f g → Conv a b → Conv (.app f a) (.app g b)
  | lam : Conv A B → Conv t u → Conv (.lam A t) (.lam B u)
  | pi : Conv A B → Conv t u → Conv (.pi A t) (.pi B u)

end Pseudo

open Pseudo

/-- The usual seven PTS rules (start, variable, weakening, product,
abstraction, application, conversion). The two weakening operations shift
all free indices, including those occurring in the type. -/
inductive HasType (P : Specification) : List (Pseudo P.Sorts) →
    Pseudo P.Sorts → Pseudo P.Sorts → Prop where
  | start : P.Ax s t → HasType P [] (.sort s) (.sort t)
  | var : HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weak : HasType P Γ t A → HasType P Γ B (.sort s) →
      HasType P (B :: Γ) (t.rename Nat.succ) (A.rename Nat.succ)
  | pi : HasType P Γ A (.sort s₁) → HasType P (A :: Γ) B (.sort s₂) →
      P.Rule s₁ s₂ s₃ → HasType P Γ (.pi A B) (.sort s₃)
  | lam : HasType P (A :: Γ) b B → HasType P Γ (.pi A B) (.sort s) →
      HasType P Γ (.lam A b) (.pi A B)
  | app : HasType P Γ f (.pi A B) → HasType P Γ a A →
      HasType P Γ (.app f a) (B.substOne a)
  | conv : HasType P Γ t A → Conv A B → HasType P Γ B (.sort s) → HasType P Γ t B

/-- Inclusion of specifications on the same sorts preserves every derivation. -/
theorem HasType.mono {P Q : Specification} (e : P.Sorts = Q.Sorts)
    (ax : ∀ s t, P.Ax s t → Q.Ax (e ▸ s) (e ▸ t))
    (rule : ∀ s t u, P.Rule s t u → Q.Rule (e ▸ s) (e ▸ t) (e ▸ u))
    {Γ t A} (h : HasType P Γ t A) :
    HasType Q (e ▸ Γ) (e ▸ t) (e ▸ A) := by
  cases P with
  | mk S PA PR =>
    cases Q with
    | mk T QA QR =>
      cases e
      induction h with
      | start h => exact .start (ax _ _ h)
      | var _ ih => exact .var ih
      | weak _ _ ih₁ ih₂ => exact .weak ih₁ ih₂
      | pi _ _ h ih₁ ih₂ => exact .pi ih₁ ih₂ (rule _ _ _ h)
      | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
      | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
      | conv _ h _ ih₁ ih₂ => exact .conv ih₁ h ih₂

/-- The two sorts of the cube. -/
inductive CubeSort where
  | star
  | box
  deriving DecidableEq

/-- The three independent dependencies beyond the common arrow rule. -/
structure Corner where
  polymorphism : Bool
  constructors : Bool
  dependent : Bool
  deriving DecidableEq

namespace Corner

open CategoryTheory

def stlc : Corner := ⟨false, false, false⟩
def systemF : Corner := ⟨true, false, false⟩
def omega : Corner := ⟨false, true, false⟩
def systemFOmega : Corner := ⟨true, true, false⟩
def lambdaP : Corner := ⟨false, false, true⟩
def lambdaP2 : Corner := ⟨true, false, true⟩
def lambdaPOmega : Corner := ⟨false, true, true⟩
def cc : Corner := ⟨true, true, true⟩

/-- Componentwise inclusion of the three rule switches. -/
def Includes (c d : Corner) : Prop :=
  (c.polymorphism = true → d.polymorphism = true) ∧
  (c.constructors = true → d.constructors = true) ∧
  (c.dependent = true → d.dependent = true)

instance : PartialOrder Corner where
  le := Includes
  le_refl _ := ⟨id, id, id⟩
  le_trans _ _ _ h k := ⟨k.1 ∘ h.1, k.2.1 ∘ h.2.1, k.2.2 ∘ h.2.2⟩
  le_antisymm := by
    intro c d h k
    cases c with
    | mk a b c =>
      cases d with
      | mk x y z =>
        simp only [Includes] at h k
        cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> cases z <;> simp_all

/-- Axiom `* : □`; rules `(s₁,s₂,s₂)` for the enabled dependencies. -/
def specification (c : Corner) : Specification where
  Sorts := CubeSort
  Ax s t := s = .star ∧ t = .box
  Rule s t u := u = t ∧
    ((s = .star ∧ t = .star) ∨
     (s = .box ∧ t = .star ∧ c.polymorphism = true) ∨
     (s = .box ∧ t = .box ∧ c.constructors = true) ∨
     (s = .star ∧ t = .box ∧ c.dependent = true))

/-- Cube inclusions act literally as identity on syntax and contexts. -/
theorem typing_inclusion {c d : Corner} (h : c ≤ d) {Γ t A}
    (ht : HasType c.specification Γ t A) : HasType d.specification Γ t A := by
  apply HasType.mono (P := c.specification) (Q := d.specification) rfl (fun _ _ => id) ?_ ht
  intro s t u hr
  rcases hr with ⟨hu, harrow | hpoly | hcon | hdep⟩
  · exact ⟨hu, Or.inl harrow⟩
  · exact ⟨hu, Or.inr (Or.inl ⟨hpoly.1, hpoly.2.1, h.1 hpoly.2.2⟩)⟩
  · exact ⟨hu, Or.inr (Or.inr (Or.inl ⟨hcon.1, hcon.2.1, h.2.1 hcon.2.2⟩))⟩
  · exact ⟨hu, Or.inr (Or.inr (Or.inr ⟨hdep.1, hdep.2.1, h.2.2 hdep.2.2⟩))⟩

theorem stlc_le_systemF : stlc ≤ systemF := by
  exact ⟨by simp [stlc], by simp [stlc], by simp [stlc]⟩

/-- The closed polymorphic identity type `Π A : *. A → A`. -/
def polymorphicIdentityType : Pseudo CubeSort :=
  .pi (.sort .star) (.pi (.var 0) (.var 1))

/-- Its Church-style inhabitant `λ A : *. λ x : A. x`. -/
def polymorphicIdentity : Pseudo CubeSort :=
  .lam (.sort .star) (.lam (.var 0) (.var 0))

/-- A concrete System F derivation exercising the polymorphic product rule. -/
theorem systemF_identity_type :
    HasType systemF.specification [] polymorphicIdentityType (.sort .star) := by
  have hs : HasType systemF.specification [] (.sort .star) (.sort .box) :=
    .start ⟨rfl, rfl⟩
  have ha : HasType systemF.specification [.sort .star] (.var 0) (.sort .star) := .var hs
  have hb : HasType systemF.specification [.var 0, .sort .star]
      (.var 1) (.sort .star) := .weak ha ha
  have hp : HasType systemF.specification [.sort .star]
      (.pi (.var 0) (.var 1)) (.sort .star) :=
    .pi ha hb ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  exact .pi hs hp ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩

/-- Polymorphic identity is typable in System F. -/
theorem systemF_identity :
    HasType systemF.specification [] polymorphicIdentity polymorphicIdentityType := by
  have hs : HasType systemF.specification [] (.sort .star) (.sort .box) :=
    .start ⟨rfl, rfl⟩
  have ha : HasType systemF.specification [.sort .star] (.var 0) (.sort .star) := .var hs
  have hp : HasType systemF.specification [.sort .star]
      (.pi (.var 0) (.var 1)) (.sort .star) :=
    .pi ha (.weak ha ha) ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  exact .lam (.lam (.var ha) hp) systemF_identity_type

/-- System F adds no PTS β-equations between terms already typed in STLC.
The conversion relation is shared by the cube; this does not reflect typing
of arbitrary System F terms, nor assert an intrinsic-STLC/PTS translation.

This statement is nearly tautological: under the hypotheses `ht` and `hu`, both
sides are equivalent to `Pseudo.Conv t u`, because conversion is untyped and
shared by every corner. Its only content is `typing_inclusion`. Reflection of arbitrary System F typing into STLC is not proved here. -/
theorem systemF_conservative {Γ t u A}
    (ht : HasType stlc.specification Γ t A)
    (hu : HasType stlc.specification Γ u A) :
    (HasType systemF.specification Γ t A ∧
      HasType systemF.specification Γ u A ∧ Pseudo.Conv t u) ↔
    (HasType stlc.specification Γ t A ∧
      HasType stlc.specification Γ u A ∧ Pseudo.Conv t u) := by
  constructor
  · intro h
    exact ⟨ht, hu, h.2.2⟩
  · intro h
    exact ⟨typing_inclusion stlc_le_systemF h.1,
      typing_inclusion stlc_le_systemF h.2.1, h.2.2⟩

/-- The existing category of inference systems, with proposition-valued
PTS derivations lifted to types; this introduces no new proof calculus. -/
def inferenceSystem (c : Corner) : Silmaril.Logic.Metatheory.InferenceSystemCat where
  Conclusion := List (Pseudo CubeSort) × Pseudo CubeSort × Pseudo CubeSort
  Derivation j := PLift (HasType c.specification j.1 j.2.1 j.2.2)

/-- The cube's thin category maps to the existing category of inference
systems. Identity and composition are literal on syntax; proof irrelevance
identifies derivation maps, because this PTS presentation is Prop-valued. -/
def inferenceFunctor : Corner ⥤ Silmaril.Logic.Metatheory.InferenceSystemCat where
  obj := inferenceSystem
  map f :=
    { map := id
      mapDerivation d := ⟨typing_inclusion (CategoryTheory.leOfHom f) d.down⟩ }
  map_id _ := rfl
  map_comp _ _ := rfl

end Corner
end Silmaril.Calculi.LambdaCube
