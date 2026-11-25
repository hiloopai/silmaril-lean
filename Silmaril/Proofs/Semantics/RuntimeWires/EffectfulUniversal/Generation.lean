module

public import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulUniversal.Generators
public import Silmaril.Semantics.RuntimeWires.ZeroRuntimeEquivalence.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulUniversal

open CategoryTheory MonoidalCategory Presentation RuntimeCoherence Position
open scoped MonoidalCategory SameArrow RuntimeCoherence

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "P" => pureValues G
local notation "J" => pureInclusion G
local notation "V" => valueWord (G := G)

/-- Closure of pure arrows and effect generators under the computation operations. -/
inductive Generated : {A B : Computations G} → (A ⟶ B) → Prop
  | id (A : Computations G) : Generated (𝟙 A)
  | effect (e : G.effect.Edge) : Generated (effectGenerator G e)
  | pure {X Y : Pure G} (p : X ⟶ Y) : Generated ((J).map p)
  | comp {A B C : Computations G} {f : A ⟶ B} {g : B ⟶ C} :
      Generated f → Generated g → Generated (f ≫ g)
  | tensor {A B C D : Computations G} {f : A ⟶ B} {g : C ⟶ D} :
      Generated f → Generated g → Generated (f ⊗ₘ g)
  | related {A B C D : Computations G} {f : A ⟶ B} {g : C ⟶ D} :
      underlying f ≈ₐ underlying g → Generated g → Generated f

private def present {A B : List (Wire G.Obj)} (f : Diagram (signature G) A B) :
    (⟨A⟩ : Runtime G) ⟶ ⟨B⟩ :=
  Diagram.Presented.ofTerm f

private def recast {A B X Y : Runtime G} (p : X = A) (q : Y = B) (f : A ⟶ B) : X ⟶ Y :=
  Diagram.Interpretation.transport p.symm q.symm f

private theorem recast_rel {A B X Y : Runtime G} (p : X = A) (q : Y = B) (f : A ⟶ B) :
    recast p q f ≈ₐ f :=
  DiagramInterpretation.transport_eq p.symm q.symm f

private theorem pure_rep {A B : List (Wire G.Obj)} (f : Diagram (signature G) A B)
    (h : runtimeCount A = 0) :
    ∃ p : (⟨eraseBoundary A⟩ : Pure G) ⟶ ⟨eraseBoundary B⟩, (P).map p ≈ₐ present f := by
  let X : Pure G := ⟨eraseBoundary A⟩
  let Y : Pure G := ⟨eraseBoundary B⟩
  have ea : (P).obj X = ⟨A⟩ := word_ext (values_eraseBoundary h)
  have eb : (P).obj Y = ⟨B⟩ := word_ext (values_eraseBoundary ((preservesRuntime f).symm.trans h))
  let p := recast ea eb (present f)
  exact ⟨eraseValueMorphism p, (SameArrow.of_eq ((zeroRuntimeHomEquiv X Y).right_inv p)).trans
    (recast_rel ea eb (present f))⟩

private theorem append_ambient (X : Position G) (A : List G.Obj) :
    (X.append A).ambient = X.ambient ⊗ V A := by
  apply word_ext
  change values X.before ++ none :: values (X.after ++ A) =
    (values X.before ++ none :: values X.after) ++ values A
  simp only [values, List.map_append, List.append_assoc, List.cons_append]

private theorem prepend_ambient (A : List G.Obj) (X : Position G) :
    (X.prepend A).ambient = V A ⊗ X.ambient := by
  apply word_ext
  change values (A ++ X.before) ++ none :: values X.after =
    values A ++ (values X.before ++ none :: values X.after)
  simp only [values, List.map_append, List.append_assoc]

private theorem normalize_of_id {X Y : Position G} (f : X.ambient ⟶ Y.ambient)
    {A : Runtime G} (h : f ≈ₐ 𝟙 A) : Generated (normalize f) := by
  have p := ambient_injective (h.source.trans h.target.symm)
  subst p
  have h' : f = 𝟙 X.ambient := (h.trans (.id h.source.symm)).eq
  rw [h', normalize_id]
  exact .id _

private theorem normalize_of_gen (e : Edge G) {X Y : Position G} (f : X.ambient ⟶ Y.ambient)
    (h : f ≈ₐ present (Diagram.gen (S := signature G) e)) : Generated (normalize f) := by
  cases e with
  | pure e =>
    have n := (congrArg (fun A : Runtime G => runtimeCount A.word) h.source).symm.trans (count_ambient X)
    change runtimeCount (values (G.pure.source e)) = 1 at n
    rw [runtimeCount_values] at n
    exact Nat.noConfusion n
  | effect e =>
    let g := effectGenerator G e
    have hr : f ≈ₐ underlying g := h
    exact .related ((normalize_congr hr).trans (normalize_leftmost g)) (.effect e)
  | moveRight x =>
    have hr : f ≈ₐ (crossing x).hom := h
    exact .related ((normalize_congr hr).trans (normalize_crossRight x)) (.id ⟨[x]⟩)
  | moveLeft x =>
    have hr : f ≈ₐ (crossing x).inv := h
    exact .related ((normalize_congr hr).trans (normalize_crossLeft x)) (.id ⟨[x]⟩)

private theorem normalize_term {A B : List (Wire G.Obj)} (t : Diagram (signature G) A B)
    {X Y : Position G} (r : X.ambient ⟶ Y.ambient) (hr : r ≈ₐ present t) :
    Generated (normalize r) := by
  induction t generalizing X Y with
  | id A => exact normalize_of_id r (show r ≈ₐ 𝟙 (⟨A⟩ : Runtime G) from hr)
  | gen e => exact normalize_of_gen e r hr
  | @comp A B D f g hf hg =>
    have ha : runtimeCount A = 1 :=
      (congrArg (fun W : Runtime G => runtimeCount W.word) hr.source).symm.trans (count_ambient X)
    let M := find (G := G) B
    have hm : M.ambient = ⟨B⟩ := ambient_find ((preservesRuntime f).symm.trans ha)
    let p := recast hr.source hm (present f)
    let q := recast hm hr.target (present g)
    have hp := recast_rel hr.source hm (present f)
    have hq := recast_rel hm hr.target (present g)
    have e : r ≈ₐ p ≫ q := hr.trans (hp.comp hq).symm
    exact .related ((normalize_congr e).trans (.of_eq (congrArg underlying (normalize_comp p q))))
      (.comp (hf p hp) (hg q hq))
  | @tensor A B C D f g hf hg =>
    have ha : runtimeCount (A ++ C) = 1 :=
      (congrArg (fun W : Runtime G => runtimeCount W.word) hr.source).symm.trans (count_ambient X)
    rcases runtimeCount_one_tensor A C ha with ⟨h1, h0⟩ | ⟨h0, h1⟩
    · let L := find (G := G) A
      let R := find (G := G) B
      have hL : L.ambient = ⟨A⟩ := ambient_find h1
      have hR : R.ambient = ⟨B⟩ := ambient_find ((preservesRuntime f).symm.trans h1)
      let q := recast hL hR (present f)
      have hq := recast_rel hL hR (present f)
      obtain ⟨p, hp⟩ := pure_rep g h0
      have e : q ⊗ₘ (P).map p ≈ₐ present (.tensor f g) := hq.tensor hp
      let a := append_ambient L (eraseBoundary C)
      let b := append_ambient R (eraseBoundary D)
      let s := recast a b (q ⊗ₘ (P).map p)
      have hs := recast_rel a b (q ⊗ₘ (P).map p)
      exact .related ((normalize_congr (hr.trans (hs.trans e).symm)).trans
        (normalize_append_tensor q p s hs)) (.tensor (hf q hq) (.pure p))
    · let L := find (G := G) C
      let R := find (G := G) D
      have hL : L.ambient = ⟨C⟩ := ambient_find h1
      have hR : R.ambient = ⟨D⟩ := ambient_find ((preservesRuntime g).symm.trans h1)
      let q := recast hL hR (present g)
      have hq := recast_rel hL hR (present g)
      obtain ⟨p, hp⟩ := pure_rep f h0
      have e : (P).map p ⊗ₘ q ≈ₐ present (.tensor f g) := hp.tensor hq
      let a := prepend_ambient (eraseBoundary A) L
      let b := prepend_ambient (eraseBoundary B) R
      let s := recast a b ((P).map p ⊗ₘ q)
      have hs := recast_rel a b ((P).map p ⊗ₘ q)
      exact .related ((normalize_congr (hr.trans (hs.trans e).symm)).trans
        (normalize_prepend_tensor q p s hs)) (.tensor (.pure p) (hg q hq))

/-- Every leftmost quotient arrow is generated by the pure image and effect generators. -/
theorem generated {A B : Computations G} (f : A ⟶ B) : Generated f := by
  have h (q : (leftmost A).ambient ⟶ (leftmost B).ambient) : Generated (normalize q) :=
    Quotient.inductionOn q (fun t => normalize_term t (present t) (.refl _))
  exact .related (normalize_leftmost f).symm (h (underlying f))

end Silmaril.RuntimeWires.Proofs.EffectfulUniversal
