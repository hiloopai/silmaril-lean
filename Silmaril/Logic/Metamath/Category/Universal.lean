module

public import Silmaril.Logic.Metamath.Category.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.Logic.Function.Basic
public import Mathlib.CategoryTheory.Skeletal

@[expose] public section

/-!
# Universal objects

Which universal objects does `GAxSet` have?

* The empty language with no axioms is initial (`GAxSet.isInitialEmpty`).
* There is no terminal object (`GAxSet.not_hasTerminal`). Templates are data:
  a candidate terminal object receives, from a language with a constant `c`
  and a unary rule `f` of the same sort, one morphism sending `f x` to `x` and
  one sending `f x` to the image of `c`, and these differ because the image of
  `c` is a closed tree. The argument does not involve variables.
* Binary coproducts need not exist (`GAxSet.not_hasBinaryCoproduct`): morphisms
  rename variables injectively, so a cocone under two copies of a
  one-variable object with the same leg into itself has a single variable, and
  cannot separate two different legs into a two-variable object.
* Binary products need not exist either (`GAxSet.not_hasBinaryProduct`): for
  the object with two variables and nothing else, the projections of a product
  are injective renamings, so the pairings of `(id, id)` and `(id, swap)` would
  agree after the first projection and hence be equal.

In the preorder of reachability (`GAxSet.Reaches X Y`: there is a morphism
`X ⟶ Y`, that is, `Y` interprets `X`) the empty object is least. The
inconsistent object `GAxSet.top W` over a variable type `W`, whose axioms are
all well-formed assertions of a one-sort language with one constant, lies
above exactly the objects whose variables embed into `W`
(`GAxSet.reaches_top_iff`). By Cantor's theorem there is no greatest element
(`GAxSet.not_exists_top`): the obstruction is again the injective renaming of
variables. The same holds in Mathlib's thin reflection `ThinSkeleton GAxSet`,
which has a least element and no greatest one
(`GAxSet.thinSkeleton_not_exists_top`).
-/

namespace Silmaril.Logic.Metamath.GAxSet

open CategoryTheory CategoryTheory.Limits Grammar

universe u

/-! ### Bare objects -/

/-- The grammar with no constants and no rules over the variables `W`. -/
def bareGrammar (W : Type u) : Grammar PEmpty.{u + 1} PEmpty.{u + 1} W where
  sorts := ∅
  prov _ := none
  rule l := l.elim
  rule_tc l := l.elim
  rule_args l := l.elim
  prov_sort h := by cases h
  prov_not_sort h := by cases h

/-- The object with variables `W`, no constants, no rules and no axioms. -/
abbrev bare (W : Type u) [DecidableEq W] : GAxSet.{u} := GAxSet.of (bareGrammar W) ∅ (by simp)

/-- There are no tree assertions over the empty set of constants. -/
theorem bare_assertion_elim {W : Type u} (A : TAssertion PEmpty.{u + 1} PEmpty.{u + 1} W) :
    False := A.concl.tc.elim

variable {W : Type u} [DecidableEq W]

/-- A morphism out of a bare object is a renaming of variables. -/
def bareHom (X : GAxSet.{u}) (e : W ↪ X.V) : bare W ⟶ X where
  tc c := c.elim
  var := e
  tmpl l := l.elim
  sort_mem s := s.elim
  prov_eq {c} := c.elim
  tmpl_sort l := l.elim
  map_derivable A := (bare_assertion_elim A).elim

@[simp] theorem bareHom_var (X : GAxSet.{u}) (e : W ↪ X.V) : (bareHom X e).var = e := rfl

theorem bare_hom_ext {X : GAxSet.{u}} {f g : bare W ⟶ X} (h : f.var = g.var) : f = g :=
  hom_ext (funext fun c => c.elim) h (funext fun l => l.elim)

/-- Morphisms out of a bare object are the renamings of variables. -/
def bareHomEquiv (X : GAxSet.{u}) : (bare W ⟶ X) ≃ (W ↪ X.V) where
  toFun f := f.var
  invFun e := bareHom X e
  left_inv _ := bare_hom_ext rfl
  right_inv _ := rfl

/-! ### The initial object -/

/-- The empty language with no axioms. -/
abbrev empty : GAxSet.{u} := bare PEmpty.{u + 1}

/-- The unique morphism out of the empty object. -/
def fromEmpty (X : GAxSet.{u}) : empty ⟶ X := bareHom X ⟨PEmpty.elim, fun a => a.elim⟩

/-- The empty language with no axioms is initial. -/
def isInitialEmpty : IsInitial (empty : GAxSet.{u}) :=
  IsInitial.ofUniqueHom fromEmpty fun _ _ =>
    bare_hom_ext (Function.Embedding.ext fun v => v.elim)

instance : HasInitial GAxSet.{u} := isInitialEmpty.hasInitial

/-! ### No terminal object -/

namespace Probe

/-- A constant (`false`) and a unary rule (`true`), both of the only sort. -/
def rules : ULift.{u} Bool → SyntaxRule PUnit.{u + 1} PUnit.{u + 1}
  | ⟨false⟩ => ⟨PUnit.unit, [], [], .nil, .nil⟩
  | ⟨true⟩ => ⟨PUnit.unit, [(PUnit.unit, PUnit.unit)], [.var PUnit.unit], by simp,
      by simp [Str.vars]⟩

/-- The grammar of the probe. -/
def grammar : Grammar (ULift.{u} Bool) PUnit.{u + 1} PUnit.{u + 1} where
  sorts := Set.univ
  prov _ := none
  rule := rules
  rule_tc _ := trivial
  rule_args _ _ _ := trivial
  prov_sort h := by cases h
  prov_not_sort h := by cases h

/-- A language with a constant and a unary rule, and no axioms. -/
def obj : GAxSet.{u} := GAxSet.of grammar ∅ (by simp)

/-- A morphism out of the probe with given data; its constraint is vacuous
because the probe has no provable typecodes. -/
def hom (T : GAxSet.{u}) (h : obj ⟶ T) (t : Tree T.L T.V)
    (ht : T.G.HasSort (fun w s => (s, w) = (h.tc PUnit.unit, h.var PUnit.unit)) t
      (h.tc PUnit.unit)) : obj ⟶ T where
  tc := h.tc
  var := h.var
  tmpl
    | ⟨false⟩ => h.tmpl ⟨false⟩
    | ⟨true⟩ => t
  sort_mem := h.sort_mem
  prov_eq := h.prov_eq
  tmpl_sort
    | ⟨false⟩ => h.tmpl_sort ⟨false⟩
    | ⟨true⟩ => ht.mono fun w s hw => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
      exact List.mem_map.2 ⟨_, List.mem_cons_self .., rfl⟩
  map_derivable A hA _ := by
    obtain ⟨s, hs, -⟩ := hA.concl_wellTyped
    simp [obj, grammar] at hs

theorem hom_tmpl_true (T : GAxSet.{u}) (h : obj ⟶ T) (t : Tree T.L T.V)
    (ht : T.G.HasSort (fun w s => (s, w) = (h.tc PUnit.unit, h.var PUnit.unit)) t
      (h.tc PUnit.unit)) : (hom T h t ht).tmpl ⟨true⟩ = t := rfl

end Probe

/-- No object is terminal. -/
theorem not_isTerminal (T : GAxSet.{u}) : IsEmpty (IsTerminal T) := by
  refine ⟨fun hT => ?_⟩
  let h := hT.from Probe.obj
  have hc : T.G.HasSort (fun w s => (s, w) = (h.tc PUnit.unit, h.var PUnit.unit))
      (h.tmpl ⟨false⟩) (h.tc PUnit.unit) :=
    (h.tmpl_sort ⟨false⟩).mono fun w s hw => by simp [Probe.obj, Probe.grammar, Probe.rules] at hw
  have hx : T.G.HasSort (fun w s => (s, w) = (h.tc PUnit.unit, h.var PUnit.unit))
      (.var (h.var PUnit.unit)) (h.tc PUnit.unit) := .var rfl
  have e := hT.hom_ext (Probe.hom T h _ hc) (Probe.hom T h _ hx)
  have e' := congrArg (fun k : Probe.obj ⟶ T => k.tmpl ⟨true⟩) e
  rw [Probe.hom_tmpl_true, Probe.hom_tmpl_true] at e'
  have hcl := h.tmpl_sort ⟨false⟩
  rw [e', HasSort.var_iff] at hcl
  simp [Probe.obj, Probe.grammar, Probe.rules] at hcl

/-- `GAxSet` has no terminal object. -/
theorem not_hasTerminal : ¬ HasTerminal GAxSet.{u} :=
  fun _ => (not_isTerminal (⊤_ GAxSet.{u})).false terminalIsTerminal

/-! ### No binary coproduct of a one-variable object with itself -/

/-- One variable, nothing else. -/
abbrev point : GAxSet.{u} := bare PUnit.{u + 1}

/-- `point ⨿ point` does not exist. -/
theorem not_hasBinaryCoproduct : ¬ HasBinaryCoproduct (point : GAxSet.{u}) point := by
  intro hc
  let two : GAxSet.{u} := bare (ULift.{u} Bool)
  let f : point ⟶ two := bareHom two ⟨fun _ => ⟨true⟩, fun _ _ _ => rfl⟩
  let g : point ⟶ two := bareHom two ⟨fun _ => ⟨false⟩, fun _ _ _ => rfl⟩
  have hsub : (coprod.inl : point ⟶ point ⨿ point).var PUnit.unit =
      (coprod.inr : point ⟶ point ⨿ point).var PUnit.unit :=
    (coprod.desc (𝟙 point) (𝟙 point)).var.injective rfl
  have h₁ : (coprod.desc f g).var ((coprod.inl : point ⟶ point ⨿ point).var PUnit.unit) =
      ⟨true⟩ := congrArg (fun k : point ⟶ two => k.var PUnit.unit) (coprod.inl_desc f g)
  have h₂ : (coprod.desc f g).var ((coprod.inr : point ⟶ point ⨿ point).var PUnit.unit) =
      ⟨false⟩ := congrArg (fun k : point ⟶ two => k.var PUnit.unit) (coprod.inr_desc f g)
  rw [hsub] at h₁
  exact Bool.noConfusion (congrArg ULift.down (h₁.symm.trans h₂))

/-! ### No binary product of a two-variable object with itself -/

/-- Two variables, nothing else. -/
abbrev twoPoints : GAxSet.{u} := bare (ULift.{u} Bool)

/-- `twoPoints ⨯ twoPoints` does not exist. -/
theorem not_hasBinaryProduct : ¬ HasBinaryProduct (twoPoints : GAxSet.{u}) twoPoints := by
  intro hp
  let f : twoPoints ⟶ twoPoints := bareHom twoPoints (Function.Embedding.refl _)
  let g : twoPoints ⟶ twoPoints := bareHom twoPoints
    ⟨fun b => ⟨!b.down⟩, fun a b h => by
      cases a; cases b; simpa using congrArg ULift.down h⟩
  let fst : twoPoints ⨯ twoPoints ⟶ twoPoints := prod.fst
  let snd : twoPoints ⨯ twoPoints ⟶ twoPoints := prod.snd
  have key : ∀ (a b : twoPoints ⟶ twoPoints) (x : ULift.{u} Bool),
      fst.var ((prod.lift a b).var x) = a.var x ∧ snd.var ((prod.lift a b).var x) = b.var x :=
    fun a b x => ⟨congrArg (fun k : twoPoints ⟶ twoPoints => k.var x) (prod.lift_fst a b),
      congrArg (fun k : twoPoints ⟶ twoPoints => k.var x) (prod.lift_snd a b)⟩
  have e : (prod.lift f g).var ⟨true⟩ = (prod.lift f f).var ⟨true⟩ :=
    fst.var.injective ((key f g ⟨true⟩).1.trans (key f f ⟨true⟩).1.symm)
  have h := (key f g ⟨true⟩).2.symm.trans ((congrArg snd.var e).trans (key f f ⟨true⟩).2)
  exact Bool.noConfusion (congrArg ULift.down h)

/-! ### The reachability preorder -/

/-- `X` reaches `Y` when there is a morphism `X ⟶ Y`: `Y` interprets `X`. -/
def Reaches (X Y : GAxSet.{u}) : Prop := Nonempty (X ⟶ Y)

theorem Reaches.refl (X : GAxSet.{u}) : Reaches X X := ⟨𝟙 X⟩

theorem Reaches.trans {X Y Z : GAxSet.{u}} (h₁ : Reaches X Y) (h₂ : Reaches Y Z) :
    Reaches X Z :=
  let ⟨f⟩ := h₁; let ⟨g⟩ := h₂; ⟨f ≫ g⟩

/-- Reachability requires the variables to embed. -/
theorem Reaches.embedding {X Y : GAxSet.{u}} (h : Reaches X Y) : Nonempty (X.V ↪ Y.V) :=
  let ⟨f⟩ := h; ⟨f.var⟩

theorem empty_reaches (X : GAxSet.{u}) : Reaches empty X := ⟨fromEmpty X⟩

theorem bare_reaches_iff (X : GAxSet.{u}) : Reaches (bare W) X ↔ Nonempty (W ↪ X.V) :=
  ⟨Reaches.embedding, fun ⟨e⟩ => ⟨bareHom X e⟩⟩

/-- Typecodes of the collapsing language. -/
inductive TopC : Type u
  | star
  | turnstile

/-- One sort `star`, the provable typecode `turnstile`, and one constant. -/
def topGrammar (W : Type u) : Grammar PUnit.{u + 1} TopC.{u} W where
  sorts := {.star}
  prov
    | .turnstile => some .star
    | .star => none
  rule _ := ⟨.star, [], [], .nil, .nil⟩
  rule_tc _ := rfl
  rule_args _ _ h := by simp at h
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; simp

/-- The inconsistent object over `W`: every well-formed assertion is an axiom. -/
abbrev top (W : Type u) [DecidableEq W] : GAxSet.{u} :=
  GAxSet.of (topGrammar W) {A | A.WellFormed (topGrammar W)} fun _ h => h

/-- Every well-formed assertion of `top W` is a theorem. -/
theorem top_tderivable {A : TAssertion PUnit.{u + 1} TopC.{u} W}
    (hA : A.WellFormed (topGrammar W)) : TDerivable (topGrammar W) (top W).axioms A :=
  TDerivable.of_mem hA hA

open Classical in
/-- The collapsing rewrite: sorts go to `star`, other typecodes to `turnstile`,
every rule to the constant. -/
noncomputable def toTop (X : GAxSet.{u}) (e : X.V ↪ W) : X ⟶ top W where
  tc c := (if c ∈ X.G.sorts then .star else .turnstile : TopC)
  var := e
  tmpl _ := .node PUnit.unit []
  sort_mem s hs := by
    change (if s ∈ X.G.sorts then .star else .turnstile : TopC) = .star
    rw [ite_eq_left hs]
  prov_eq h := by
    change (topGrammar W).prov (if _ ∈ X.G.sorts then .star else .turnstile : TopC) =
      some (if _ ∈ X.G.sorts then .star else .turnstile : TopC)
    rw [ite_eq_right (X.G.prov_not_sort h), ite_eq_left (X.G.prov_sort h)]
    rfl
  tmpl_sort l := by
    rw [ite_eq_left (X.G.rule_tc l)]
    exact .node rfl (by simp)
  map_derivable A hA _ := top_tderivable (Rewrite.wellFormed hA)

/-- `top W` lies above exactly the objects whose variables embed into `W`. -/
theorem reaches_top_iff (X : GAxSet.{u}) : Reaches X (top W) ↔ Nonempty (X.V ↪ W) :=
  ⟨Reaches.embedding, fun ⟨e⟩ => ⟨toTop X e⟩⟩

/-- The reachability preorder has no greatest element. -/
theorem not_exists_top : ¬ ∃ T : GAxSet.{u}, ∀ X, Reaches X T := by
  classical
  rintro ⟨T, hT⟩
  obtain ⟨e⟩ := (hT (bare (Set T.V))).embedding
  exact Function.cantor_injective e e.injective

/-- The order of the thin reflection is reachability. -/
theorem thinSkeleton_mk_le_iff {X Y : GAxSet.{u}} :
    ThinSkeleton.mk X ≤ ThinSkeleton.mk Y ↔ Reaches X Y := Iff.rfl

/-- The empty object is least in the thin reflection. -/
instance : OrderBot (ThinSkeleton GAxSet.{u}) where
  bot := ThinSkeleton.mk empty
  bot_le := Quotient.ind fun X => empty_reaches X

/-- The thin reflection has no greatest element. -/
theorem thinSkeleton_not_exists_top : ¬ ∃ T : ThinSkeleton GAxSet.{u}, ∀ q, q ≤ T := by
  rintro ⟨T, hT⟩
  induction T using Quotient.inductionOn with
  | h T => exact not_exists_top ⟨T, fun X => hT (ThinSkeleton.mk X)⟩

end Silmaril.Logic.Metamath.GAxSet
