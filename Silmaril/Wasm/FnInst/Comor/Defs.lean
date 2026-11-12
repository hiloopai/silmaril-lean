module

public import Silmaril.Wasm.FnInst.Core.Defs

/-!
# Comorphisms between the one-, several-, all-function and hole institutions

All are the identity on models (handlers over the same context), so all are model-expansive
(`Silmaril.Wasm.FnInst.Comor.Thms`) and borrowing applies: a sentence is valid in the source iff
its translation is valid in the target.

* `oneToSet`: the focus `i` becomes the focus `{i}`;
* `setToAll`: the focus is forgotten, a focus member is read as a function index;
* `holeToAll`: the hole type becomes the type of `seg` atoms;
* `oneToAll := oneToSet ≫ᶜ setToAll`.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst

open CategoryTheory Silmaril.Inst

variable {L : Lang} {W : Type}

theorem Formula.map_map_eq {α β β' γ : Type} {f₁ : α → β} {g₁ : β → γ} {f₂ : α → β'}
    {g₂ : β' → γ} (h : ∀ a, g₁ (f₁ a) = g₂ (f₂ a)) (φ : Formula α) :
    (φ.map f₁).map g₁ = (φ.map f₂).map g₂ := by
  rw [Formula.map_map, Formula.map_map]
  exact congrArg (fun f => φ.map f) (funext h)

/-- Changing the focus type of an atom without renaming code. -/
def FnAtom.reindex {C : Ctx} {I I' : Type} (f : I → I') : FnAtom L C I → FnAtom L C I'
  | .seg τ b b' => .seg τ b b'
  | .fn i b b' => .fn (f i) b b'

theorem FnAtom.holds_reindex {C : Ctx} {I I' : Type} (f : I → I') (ix : I → C.Idx .func)
    (ix' : I' → C.Idx .func) (hix : ∀ i, ix' (f i) = ix i) (h : Handler L W C)
    (a : FnAtom L C I) : (a.reindex f).Holds ix' h ↔ a.Holds ix h := by
  cases a with
  | seg τ b b' => exact Iff.rfl
  | fn i b b' =>
    show FnEq h (C.fty (ix' (f i))) b b' ↔ FnEq h (C.fty (ix i)) b b'
    rw [hix i]

theorem FnAtom.reindex_rename {C C' : Ctx} {I I' J J' : Type} (σ : C ⟶ C') (f : I → I')
    (g : J → J') (r : I → J) (r' : I' → J') (hr : ∀ i, r' (f i) = g (r i)) (a : FnAtom L C I) :
    (a.rename σ f).reindex r' = (a.reindex r).rename σ g := by
  cases a with
  | seg τ b b' => rfl
  | fn i b b' => exact congrArg (fun j => FnAtom.fn j _ _) (hr i)

/-- The signature functor one ⥤ several: the focus `i` becomes `{i}`. -/
def OneSig.toSet : OneSig ⥤ SetSig where
  obj S := ⟨S.C, {S.f}⟩
  map σ := ⟨OneSig.Hom.emb σ, fun i hi => by
    rw [Set.mem_singleton_iff] at hi ⊢
    rw [hi]
    exact OneSig.Hom.f σ⟩
  map_id _ := SetSig.Hom.ext rfl
  map_comp _ _ := SetSig.Hom.ext rfl

/-- The signature functor several ⥤ all: forget the focus. -/
def SetSig.toAll : SetSig ⥤ Ctx where
  obj S := S.C
  map σ := SetSig.Hom.emb σ

/-- The signature functor hole ⥤ all: forget the hole. -/
def HoleSig.toAll : HoleSig ⥤ Ctx where
  obj S := S.C
  map σ := HoleSig.Hom.emb σ

variable (L W)

/-- one → several. -/
def oneToSet : Comorphism (oneInst L W) (setInst L W) :=
  Comorphism.ofPlain (P := (onePres L W).toPlain) (Q := (setPres L W).toPlain) OneSig.toSet
    (fun S φ => Formula.map (FnAtom.reindex fun _ => ⟨S.f, rfl⟩) φ)
    (fun _ h => h)
    (fun S h φ => (Formula.holds_map _ _ φ).trans
      (Formula.holds_congr (fun a => FnAtom.holds_reindex _ (fun _ => S.f) Subtype.val (fun _ => rfl) h a) φ))
    (fun σ φ => Formula.map_map_eq (fun a =>
      FnAtom.reindex_rename _ _ _ _ _ (fun _ => Subtype.ext (OneSig.Hom.f σ).symm) a) φ)
    (fun _ _ => rfl)

/-- several → all. -/
def setToAll : Comorphism (setInst L W) (allInst L W) :=
  Comorphism.ofPlain (P := (setPres L W).toPlain) (Q := (allPres L W).toPlain) SetSig.toAll
    (fun _ φ => Formula.map (FnAtom.reindex Subtype.val) φ)
    (fun _ h => h)
    (fun _ h φ => (Formula.holds_map _ _ φ).trans
      (Formula.holds_congr (fun a => FnAtom.holds_reindex Subtype.val Subtype.val id (fun _ => rfl) h a) φ))
    (fun σ φ => Formula.map_map_eq (fun a =>
      FnAtom.reindex_rename (SetSig.Hom.emb σ) (SetSig.Hom.focus σ) (Ctx.Hom.map (SetSig.Hom.emb σ) .func)
        Subtype.val Subtype.val (fun _ => rfl) a) φ)
    (fun _ _ => rfl)

/-- hole → all: a hole equation becomes a `seg` atom at the hole type. -/
def holeToAll : Comorphism (holeInst L W) (allInst L W) :=
  Comorphism.ofPlain (P := (holePres L W).toPlain) (Q := (allPres L W).toPlain) HoleSig.toAll
    (fun S φ => Formula.map (fun p : L.Code S.C × L.Code S.C => FnAtom.seg S.ty p.1 p.2) φ)
    (fun _ h => h)
    (fun S h φ => Formula.holds_map (fun p : L.Code S.C × L.Code S.C => FnAtom.seg S.ty p.1 p.2) (FnAtom.Holds id h) φ)
    (fun σ φ => Formula.map_map_eq (fun p => by
      show FnAtom.seg _ _ _ = FnAtom.seg _ _ _
      rw [HoleSig.Hom.ty σ]
      rfl) φ)
    (fun _ _ => rfl)

/-- one → all. -/
def oneToAll : Comorphism (oneInst L W) (allInst L W) := oneToSet L W ≫ᶜ setToAll L W

end Silmaril.Wasm.FnInst
