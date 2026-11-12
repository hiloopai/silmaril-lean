module

public import Silmaril.Wasm.SpecTec.Institution.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Juxtaposing institutions: SpecTec specifications with grammars

An IL script has two kinds of inductive definitions, relations (`relD`) and grammars (`gramD`),
and neither mentions the other: rule premises name relations only, and productions name
nonterminals only (both may call functions, which models read through the evaluator). So the
institution of whole scripts is the **juxtaposition** of an institution of relations and an
institution of grammars:

* `juxt A B`: signatures are pairs, sentences are `Sen_A ⊕ Sen_B`, models are pairs (the
  product model category), and a model satisfies `inl φ` (`inr ψ`) when its first (second)
  component does. Translation and reduct act componentwise.
* `inl A B T₀`, `inr A B S₀`: the inclusion comorphisms `A → juxt A B` (at a fixed `B`-signature
  `T₀`) and `B → juxt A B` (at a fixed `A`-signature `S₀`). Their model maps are the projections,
  so the satisfaction condition holds by `Iff.rfl`.
* `withGrammars G`: the relational institution `inst backend` juxtaposed with a grammar
  institution `G`; `grammarInclusion G`: the inclusion of `G`, at the empty relational signature.
  `G` is meant to be `Silmaril.Wasm.SpecTec.GrammarInst.inst A` (branch
  `si-p1-grammar-inst`, not yet on `main`); nothing here depends on it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u₁ v₁ u₂ v₂ w m₁ m₂

namespace Juxt

/-- The juxtaposition of two rooms: disjoint sentences, paired models. -/
def room (R₁ R₂ : Room.{w, m₁, m₂}) : Room.{w, m₁, m₂} :=
  ⟨R₁.Sen ⊕ R₂.Sen, Cat.of (R₁.Mod × R₂.Mod), fun M φ => Sum.elim (R₁.Sat M.1) (R₂.Sat M.2) φ⟩

/-- The juxtaposition of two corridors. -/
def corridor {R₁ R₂ S₁ S₂ : Room.{w, m₁, m₂}} (c₁ : R₁ ⟶ S₁) (c₂ : R₂ ⟶ S₂) :
    room R₁ R₂ ⟶ room S₁ S₂ :=
  ⟨Sum.map c₁.sen c₂.sen, c₁.mod.prod c₂.mod, fun M φ => by
    cases φ with
    | inl φ => exact c₁.sat M.1 φ
    | inr φ => exact c₂.sat M.2 φ⟩

theorem corridor_id (R₁ R₂ : Room.{w, m₁, m₂}) : corridor (𝟙 R₁) (𝟙 R₂) = 𝟙 (room R₁ R₂) := by
  apply Corridor.ext
  · funext φ
    cases φ <;> rfl
  · rfl

theorem corridor_comp {R₁ R₂ S₁ S₂ T₁ T₂ : Room.{w, m₁, m₂}} (c₁ : R₁ ⟶ S₁) (c₂ : R₂ ⟶ S₂)
    (d₁ : S₁ ⟶ T₁) (d₂ : S₂ ⟶ T₂) :
    corridor (c₁ ≫ d₁) (c₂ ≫ d₂) = corridor c₁ c₂ ≫ corridor d₁ d₂ := by
  apply Corridor.ext
  · funext φ
    cases φ <;> rfl
  · rfl

end Juxt

/-- **The juxtaposition of two institutions**. -/
def juxt (A : Inst.{u₁, v₁, w, m₁, m₂}) (B : Inst.{u₂, v₂, w, m₁, m₂}) :
    Inst.{max u₁ u₂, max v₁ v₂, w, m₁, m₂} where
  Sign := A.Sign × B.Sign
  I :=
    { obj := fun S => Juxt.room (A.I.obj S.1) (B.I.obj S.2)
      map := fun f => Juxt.corridor (A.I.map f.1) (B.I.map f.2)
      map_id := fun S => by
        change Juxt.corridor (A.I.map (𝟙 S.1)) (B.I.map (𝟙 S.2)) = _
        rw [A.I.map_id, B.I.map_id]
        exact Juxt.corridor_id _ _
      map_comp := fun f g => by
        change Juxt.corridor (A.I.map (f.1 ≫ g.1)) (B.I.map (f.2 ≫ g.2)) = _
        rw [A.I.map_comp, B.I.map_comp]
        exact Juxt.corridor_comp _ _ _ _ }

/-- **The inclusion of the second institution**, at a fixed signature `S₀` of the first. -/
def juxt.inr (A : Inst.{u₁, v₁, w, m₁, m₂}) (B : Inst.{u₂, v₂, w, m₁, m₂}) (S₀ : A.Sign) :
    Inst.CoHom B (juxt A B) where
  Φ := ((Functor.const B.Sign).obj S₀).prod' (𝟭 B.Sign)
  ρ :=
    { app := fun _ => ⟨Sum.inr, CategoryTheory.Prod.snd _ _, fun _ _ => Iff.rfl⟩
      naturality := fun _ _ _ => rfl }

/-- **The inclusion of the first institution**, at a fixed signature `T₀` of the second. -/
def juxt.inl (A : Inst.{u₁, v₁, w, m₁, m₂}) (B : Inst.{u₂, v₂, w, m₁, m₂}) (T₀ : B.Sign) :
    Inst.CoHom A (juxt A B) where
  Φ := (𝟭 A.Sign).prod' ((Functor.const A.Sign).obj T₀)
  ρ :=
    { app := fun _ => ⟨Sum.inl, CategoryTheory.Prod.fst _ _, fun _ _ => Iff.rfl⟩
      naturality := fun _ _ _ => rfl }

/-- The empty IL signature. -/
def Sig.empty : Sig := ⟨∅, ∅, ∅⟩

/-- **SpecTec specifications with grammars**: the relational institution at the backend reading,
juxtaposed with a grammar institution `G`. -/
def withGrammars (G : Inst.{u₂, v₂, 0, 0, 0}) : Inst.{max 0 u₂, max 0 v₂, 0, 0, 0} :=
  juxt (inst backend) G

/-- **Grammars as a sub-institution** of SpecTec specifications: the inclusion comorphism, at the
empty relational signature. -/
def grammarInclusion (G : Inst.{u₂, v₂, 0, 0, 0}) : Inst.CoHom G (withGrammars G) :=
  juxt.inr (inst backend) G Sig.empty

/-- The relational institution as a sub-institution, at a fixed grammar signature `T₀`. -/
def relationInclusion (G : Inst.{u₂, v₂, 0, 0, 0}) (T₀ : G.Sign) :
    Inst.CoHom (inst backend) (withGrammars G) :=
  juxt.inl (inst backend) G T₀

end Silmaril.Wasm.SpecTec.Institution
