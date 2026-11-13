module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlCoherence
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Typing

/-! # Naturality of categorical interpretation

A structure-preserving categorical map induces an operation-algebra map.
Naturality of interpretation is then the shared fold theorem, including the
quantity-valid context maps and the retained loop environment.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory Silmaril.Logic.Metatheory.TheoryModel
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData.HomMap
variable {M N : SeqData.{u,v,w,r} τ Φ ε}

theorem tensor (φ : M.HomMap N) {A B D E : τ} (f : M.Hom A B) (g : M.Hom D E) :
    φ.map (M.tensor f g) = N.tensor (φ.map f) (φ.map g) := by
  unfold SeqData.tensor
  rw [φ.compose, φ.left, φ.right]
end SeqData.HomMap

namespace Denotation
variable {M N : SeqData.{u,v,w,r} τ Φ ε} {F : Fragment}

/-- Preservation of just the control operations permitted by the fragment. -/
structure ControlMap (φ : M.HomMap N) (K : ControlData M F) (L : ControlData N F) : Prop where
  inl (h : F.HasCase) (A B : τ) : φ.map (K.inl h A B) = L.inl h A B
  inr (h : F.HasCase) (A B : τ) : φ.map (K.inr h A B) = L.inr h A B
  desc (h : F.HasCase) {A B D : τ} (f : M.Hom A D) (g : M.Hom B D) :
    φ.map (K.desc h f g) = L.desc h (φ.map f) (φ.map g)
  abort (h : F.HasCase) (A : τ) : φ.map (K.abort h A) = L.abort h A
  distribute (h : F.HasCase) (D A B : τ) : φ.map (K.distribute h D A B) = L.distribute h D A B
  iterate (h : F.HasIter) {A B : τ} (f : M.Hom A (coprod B A)) :
    φ.map (K.iterate h f) = L.iterate h (φ.map f)

namespace ControlMap

theorem seq {M N : SeqModel.{u,v,w,r} τ Φ ε} (φ : M ⟶ N) :
    ControlMap φ (ControlData.seq M) (ControlData.seq N) where
  inl h := False.elim h
  inr h := False.elim h
  desc h := False.elim h
  abort h := False.elim h
  distribute h := False.elim h
  iterate h := False.elim h

theorem ofCase {M N : CaseData.{u,v,w,r} τ Φ ε} (φ : M.HomMap N) (F : Fragment)
    (itM : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B)
    (itN : F.HasIter → ∀ {A B : τ}, N.Hom A (coprod B A) → N.Hom A B)
    (hi : ∀ h {A B : τ} (f : M.Hom A (coprod B A)), φ.map (itM h f) = itN h (φ.map f)) :
    ControlMap φ.toHomMap (ControlData.ofCase M F itM) (ControlData.ofCase N F itN) where
  inl _ := φ.inl
  inr _ := φ.inr
  desc _ := φ.desc
  abort _ := φ.abort
  distribute _ := φ.distribute
  iterate := hi

theorem case {M N : CaseModel.{u,v,w,r} τ Φ ε} (φ : M ⟶ N) :
    ControlMap φ.toHomMap (ControlData.case M) (ControlData.case N) :=
  ofCase φ .case (fun h => False.elim h) (fun h => False.elim h) (fun h => False.elim h)

theorem iter {M N : IterModel.{u,v,w,r} τ Φ ε} (φ : M ⟶ N) :
    ControlMap φ.toCaseHom.toHomMap (ControlData.iter M) (ControlData.iter N) :=
  ofCase φ.toCaseHom .iter (fun _ => M.iterate) (fun _ => N.iterate) (fun _ => φ.iterate)

variable {φ : M.HomMap N} {K : ControlData M F} {L : ControlData N F}

theorem iterateWithContext (P : ControlMap φ K L) (h : F.HasIter) (D : τ)
    (hc : Quantity.relevant ≤ quantity D) (hd : Quantity.affine ≤ quantity D)
    {A B : τ} (body : M.Hom (product D A) (coprod B A)) :
    φ.map (K.iterateWithContext h D hc hd body) = L.iterateWithContext h D hc hd (φ.map body) := by
  unfold ControlData.iterateWithContext ControlData.contextStep
  rw [P.iterate]
  simp only [φ.compose, φ.right, φ.copy, φ.associator, φ.left, P.distribute,
    P.desc, φ.discard, φ.leftUnitor, P.inl, P.inr]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Categorical structure maps preserve every quantitative constructor operation. -/
def algebraMap (P : ControlMap φ K L) : Algebra.Hom (algebra M K) (algebra N L) where
  map {i} a := φ.map (A := packed i.context) (B := i.result) a
  comm o args := by
    cases o <;> dsimp only [algebra, signature, Operation.argSort, Operation.arity] at args ⊢
    · exact map_variable φ _ _
    · rw [φ.compose, φ.instruction]
    · rw [φ.compose, map_split, φ.compose, φ.left]
    · exact map_discard φ _
    · rw [φ.compose, map_split, φ.tensor]
    · rw [φ.compose, map_split, φ.compose, φ.left, φ.compose, φ.associatorInv]
    · rw [φ.compose, P.inl]
    · rw [φ.compose, P.inr]
    · rw [φ.compose, map_split, φ.compose, φ.left, φ.compose, P.distribute, P.desc]
    · rw [φ.compose, P.abort]
    · rw [φ.compose, map_split, φ.compose, φ.left, P.iterateWithContext]

theorem denote (P : ControlMap φ K L) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType F Γ e t A) :
    φ.map (Denotation.denote M K h) = Denotation.denote N L h :=
  Models.denote_naturality P.algebraMap h

end ControlMap

theorem denoteSeq_naturality {M N : SeqModel.{u,v,w,r} τ Φ ε} (φ : M ⟶ N)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ} (h : HasType .seq Γ e t A) :
    φ.map (denoteSeq M h) = denoteSeq N h := (ControlMap.seq φ).denote h

theorem denoteCase_naturality {M N : CaseModel.{u,v,w,r} τ Φ ε} (φ : M ⟶ N)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ} (h : HasType .case Γ e t A) :
    φ.map (denoteCase M h) = denoteCase N h := (ControlMap.case φ).denote h

theorem denoteIter_naturality {M N : IterModel.{u,v,w,r} τ Φ ε} (φ : M ⟶ N)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ} (h : HasType .iter Γ e t A) :
    φ.map (denoteIter M h) = denoteIter N h := (ControlMap.iter φ).denote h

/-- Sequential categorical models yield constructor algebras functorially. -/
def seqAlgebraFunctor : SeqModel.{u,v,w,r} τ Φ ε ⥤
    Algebra.{u, max u w, v} (signature (τ := τ) Φ .seq) where
  obj M := algebra M.toSeqData (ControlData.seq M)
  map φ := (ControlMap.seq φ).algebraMap
  map_id _ := Algebra.Hom.ext (fun _ => rfl)
  map_comp _ _ := Algebra.Hom.ext (fun _ => rfl)

def caseAlgebraFunctor : CaseModel.{u,v,w,r} τ Φ ε ⥤
    Algebra.{u, max u w, v} (signature (τ := τ) Φ .case) where
  obj M := algebra M.toSeqData (ControlData.case M)
  map φ := (ControlMap.case φ).algebraMap
  map_id _ := Algebra.Hom.ext (fun _ => rfl)
  map_comp _ _ := Algebra.Hom.ext (fun _ => rfl)

def iterAlgebraFunctor : IterModel.{u,v,w,r} τ Φ ε ⥤
    Algebra.{u, max u w, v} (signature (τ := τ) Φ .iter) where
  obj M := algebra M.toSeqData (ControlData.iter M)
  map φ := (ControlMap.iter φ).algebraMap
  map_id _ := Algebra.Hom.ext (fun _ => rfl)
  map_comp _ _ := Algebra.Hom.ext (fun _ => rfl)

end Denotation
end Silmaril.Isotope.Refinement.Models
