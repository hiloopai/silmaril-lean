module

public import Silmaril.Raw.SSA.Isotope.Morphism.Instructions.Signature
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.ModelReindex

@[expose] public section

/-!
# The category of primitive instruction signatures

An instruction signature over a fixed type universe `τ` and effect universe `ε` is a type of
primitive instructions with source, target and effect assignments. Its morphisms are the
existing primitive `Morphism.SignatureMap`s whose type and effect components are identities
(`InstrSig.Hom.toSignatureMap`): they relabel instructions while preserving sources, targets
and effects.

The type-changing maps of `SignatureMap` (`ty ≠ id`) also act on contexts and bound contexts,
and their reducts compose only up to the propositional equation `BoundCtx.mapTypes_comp`; they
are deferred to an indexed (Grothendieck) construction over type universes.

This file also contains `castOp`, the transport of an operation symbol along an equation of
sorts, used to send an instruction `f` to the target instruction `g f`, whose result type agrees
with that of `f` only propositionally.
-/

namespace Silmaril.Isotope.Institution

open CategoryTheory
open Silmaril.Isotope.Morphism
open Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel

universe u a b

/-- A primitive instruction signature over types `τ` and effects `ε`. -/
structure InstrSig (τ : Type u) (ε : Type u) where
  /-- The primitive instructions. -/
  Instr : Type u
  [hasTy : HasTy Instr τ]
  [hasEff : HasEff Instr ε]

attribute [instance] InstrSig.hasTy InstrSig.hasEff

namespace InstrSig

variable {τ : Type u} {ε : Type u}

/-- A relabelling of primitive instructions preserving sources, targets and effects. -/
structure Hom (P Q : InstrSig τ ε) where
  /-- The instruction map. -/
  instr : P.Instr → Q.Instr
  source : ∀ f, instrSrc (τ := τ) (instr f) = instrSrc f
  target : ∀ f, instrTrg (τ := τ) (instr f) = instrTrg f
  effect : ∀ f, instrEff (ε := ε) (instr f) = instrEff f

@[ext] theorem Hom.ext {P Q : InstrSig τ ε} {f g : Hom P Q} (h : f.instr = g.instr) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

instance category : Category.{u} (InstrSig τ ε) where
  Hom := Hom
  id _ := ⟨id, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  comp f g := ⟨g.instr ∘ f.instr, fun x => (g.source _).trans (f.source x),
    fun x => (g.target _).trans (f.target x), fun x => (g.effect _).trans (f.effect x)⟩

@[simp] theorem id_instr (P : InstrSig τ ε) : Hom.instr (𝟙 P) = id := rfl

@[simp] theorem comp_instr {P Q R : InstrSig τ ε} (f : P ⟶ Q) (g : Q ⟶ R) :
    Hom.instr (f ≫ g) = g.instr ∘ f.instr := rfl

/-- The underlying primitive signature map, with identity type and effect components. -/
def Hom.toSignatureMap {P Q : InstrSig τ ε} (g : Hom P Q) :
    SignatureMap P.Instr Q.Instr τ τ ε ε where
  instr := g.instr
  ty := id
  eff := id
  source := g.source
  target := g.target
  effect := g.effect

instance {P Q : InstrSig τ ε} [HasProduct τ] [HasUnit τ] (g : Hom P Q) :
    g.toSignatureMap.PreservesProducts where
  unit := rfl
  product _ _ := rfl

instance {P Q : InstrSig τ ε} [HasCoproduct τ] [HasEmpty τ] (g : Hom P Q) :
    g.toSignatureMap.PreservesSums where
  empty := rfl
  coprod _ _ := rfl

theorem toSignatureMap_id (P : InstrSig τ ε) :
    Hom.toSignatureMap (𝟙 P) = SignatureMap.id := rfl

theorem toSignatureMap_comp {P Q R : InstrSig τ ε} (f : P ⟶ Q) (g : Q ⟶ R) :
    Hom.toSignatureMap (f ≫ g) = g.toSignatureMap.comp f.toSignatureMap := rfl

end InstrSig

/-! ### Transport of operation symbols along equations of sorts -/

section CastOp

variable {I : Type a} (S : Silmaril.Logic.Metatheory.TheoryModel.Signature.{a, b} I)

/-- Transport an operation symbol along an equation of result sorts. -/
def castOp {i j : I} (h : i = j) (o : S.Op i) : S.Op j := h ▸ o

@[simp] theorem castOp_rfl {i : I} (o : S.Op i) : castOp S rfl o = o := rfl

theorem arity_castOp {i j : I} (h : i = j) (o : S.Op i) :
    S.arity (castOp S h o) = S.arity o := by
  subst h
  rfl

theorem argSort_castOp {i j : I} (h : i = j) (o : S.Op i) (k : Fin (S.arity (castOp S h o))) :
    S.argSort (castOp S h o) k = S.argSort o (Fin.cast (arity_castOp S h o) k) := by
  subst h
  rfl

end CastOp

end Silmaril.Isotope.Institution
