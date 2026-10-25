module

public import Silmaril.Logic.Metamath.Category.Functor
public import Silmaril.Logic.Metamath.Category.Universal

@[expose] public section

/-!
# Interpretations and conservative morphisms

`X` interprets `Y` (`GAxSet.Interprets X Y`) when there is a morphism
`Y ⟶ X`: a syntax rewrite of `Y`'s language into `X`'s that sends theorems to
theorems. Relative interpretability is a preorder across languages
(`GAxSet.InterpOrder`), the reachability preorder of
`Silmaril.Logic.Metamath.Category.Universal`.

A morphism is conservative when it also reflects derivability of well-formed
assertions: `GAxSet.Hom.Conservative f` is conservativity of
`toPropSystems.map f` in the sense of `Silmaril.Logic.Metatheory.Conservative`,
equivalently of `toInferenceSystemCat.map f`. Conservative morphisms contain
the identities, are closed under composition and left cancellation, and
include every morphism with a retraction (`GAxSet.Hom.conservative_of_comp_eq_id`).

The elimination criterion (`GAxSet.Hom.conservative_of_elimination`): if a
rewrite `r` back satisfies `f ≫ r = id` on the level of rewrites and sends
every axiom of `Y` to a theorem of `X`, then `f` is conservative.

The definitional extension theorem (`GAxSet.definitional_extension`): adding a
syntax rule `r` to a grammar, together with axioms `defs` over the extended
grammar, is conservative over the old language when the elimination rewrite
(identity on the old rules, the definiens `δ` on the new rule) sends each
member of `defs` to a theorem of the old axioms. Variables must be infinite
(for cut admissibility).
-/

namespace Silmaril.Logic.Metamath

open CategoryTheory Grammar Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.InferenceSystemCat

universe u

namespace GAxSet

variable {X Y Z : GAxSet.{u}}

/-! ### Interpretations -/

/-- `X` interprets `Y`: there is a morphism `Y ⟶ X`. -/
def Interprets (X Y : GAxSet.{u}) : Prop := Reaches Y X

theorem Interprets.refl (X : GAxSet.{u}) : Interprets X X := Reaches.refl X

theorem Interprets.trans {X Y Z : GAxSet.{u}} (h₁ : Interprets X Y) (h₂ : Interprets Y Z) :
    Interprets X Z := Reaches.trans h₂ h₁

/-- Grammatical axiom sets ordered by relative interpretability: `X ≤ Y` when
`Y` interprets `X`. -/
def InterpOrder : Type (u + 1) := GAxSet.{u}

/-- View a grammatical axiom set in the interpretability order. -/
def InterpOrder.of (X : GAxSet.{u}) : InterpOrder.{u} := X

instance : Preorder InterpOrder.{u} where
  le X Y := Reaches (X : GAxSet.{u}) Y
  le_refl X := Reaches.refl (X : GAxSet.{u})
  le_trans _ _ _ := Reaches.trans

theorem InterpOrder.of_le_of_iff {X Y : GAxSet.{u}} :
    InterpOrder.of X ≤ InterpOrder.of Y ↔ Interprets Y X := Iff.rfl

/-- The empty language is interpreted by everything. -/
theorem InterpOrder.of_empty_le (X : GAxSet.{u}) : InterpOrder.of empty ≤ InterpOrder.of X :=
  empty_reaches X

/-- Relative interpretability has no greatest element. -/
theorem InterpOrder.not_exists_top : ¬ ∃ T : InterpOrder.{u}, ∀ X, X ≤ T :=
  GAxSet.not_exists_top

/-! ### Conservative morphisms -/

/-- A conservative morphism reflects derivability of well-formed assertions. -/
def Hom.Conservative (f : X ⟶ Y) : Prop := PropSystems.Conservative (toPropSystems.map f)

namespace Hom

theorem conservative_iff (f : X ⟶ Y) :
    f.Conservative ↔ ∀ A, A.WellFormed X.G →
      TDerivable Y.G Y.axioms (f.assertion A) → TDerivable X.G X.axioms A :=
  ⟨fun h A hA => h ⟨A, hA⟩, fun h A => h A.1 A.2⟩

/-- Conservativity is the same in `InferenceSystemCat`. -/
theorem conservative_iff_inferenceSystemCat (f : X ⟶ Y) :
    InferenceSystemCat.Conservative (toInferenceSystemCat.{u, u}.map f) ↔ f.Conservative :=
  PropSystems.conservative_toCoherent_iff (toPropSystems.map f)

theorem conservative_id (X : GAxSet.{u}) : (𝟙 X : X ⟶ X).Conservative := by
  rw [Hom.Conservative, toPropSystems.map_id]
  exact PropSystems.conservative_id _

theorem Conservative.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : f.Conservative) (hg : g.Conservative) :
    (f ≫ g).Conservative := by
  rw [Hom.Conservative, toPropSystems.map_comp]
  exact PropSystems.Conservative.comp hf hg

/-- Left cancellation: if `f ≫ g` is conservative, so is `f`. -/
theorem Conservative.of_comp {f : X ⟶ Y} {g : Y ⟶ Z} (h : (f ≫ g).Conservative) :
    f.Conservative := by
  rw [Hom.Conservative, toPropSystems.map_comp] at h
  exact PropSystems.Conservative.of_comp h

/-- A morphism with a retraction is conservative. -/
theorem conservative_of_comp_eq_id (f : X ⟶ Y) (r : Y ⟶ X) (h : f ≫ r = 𝟙 X) :
    f.Conservative :=
  Conservative.of_comp (h ▸ conservative_id X)

/-- The elimination criterion: a rewrite back that undoes `f` on rewrites and
sends every axiom of `Y` to a theorem of `X` makes `f` conservative. -/
theorem conservative_of_elimination [Infinite X.V] (f : X ⟶ Y) (r : Rewrite Y.G X.G)
    (hfr : f.toRewrite.comp r = Rewrite.id X.G)
    (hr : ∀ B ∈ Y.axioms, TDerivable X.G X.axioms (r.assertion B)) : f.Conservative :=
  conservative_of_comp_eq_id f (ofAxioms r hr) (Hom.ext' hfr)

/-- Conservative morphisms reflect derivability of the images. -/
theorem Conservative.tderivable {f : X ⟶ Y} (hf : f.Conservative)
    {A : TAssertion X.L X.C X.V} (hA : A.WellFormed X.G) :
    TDerivable Y.G Y.axioms (f.assertion A) ↔ TDerivable X.G X.axioms A :=
  ⟨(conservative_iff f).1 hf A hA, f.map_derivable A hA⟩

end Hom

/-- The functor to derivability forgets templates that no well-formed assertion
sees: on the probe language of `Silmaril.Logic.Metamath.Category.Universal`,
which has no provable typecode, the identity and the morphism sending the
unary rule to the constant have the same (empty) action. -/
theorem not_faithful_toPropSystems : ¬ (toPropSystems.{u}).Faithful := by
  intro hF
  let X := Probe.obj.{u}
  have hc : X.G.HasSort (fun w s => (s, w) = ((𝟙 X : X ⟶ X).tc PUnit.unit,
      (𝟙 X : X ⟶ X).var PUnit.unit)) ((𝟙 X : X ⟶ X).tmpl ⟨false⟩) ((𝟙 X : X ⟶ X).tc PUnit.unit) :=
    ((𝟙 X : X ⟶ X).tmpl_sort ⟨false⟩).mono fun w s hw => by
      simp only [X, Probe.obj, Probe.grammar, Probe.rules, List.map_nil] at hw
      cases hw
  have e : 𝟙 X = Probe.hom X (𝟙 X) _ hc := toPropSystems.map_injective <|
    PropSystems.hom_ext <| funext fun A => by
      obtain ⟨s, hs, -⟩ := A.2.concl_wellTyped
      simp [X, Probe.obj, Probe.grammar] at hs
  have e' := congrArg (fun k : X ⟶ X => k.tmpl ⟨true⟩) e
  rw [Probe.hom_tmpl_true] at e'
  simp [X, Probe.obj, Probe.grammar, Rewrite.id] at e'

end GAxSet

/-! ### Definitional extensions -/

namespace Grammar

variable {L C V : Type u}

/-- The grammar `G` with one more syntax rule `r`, labelled `none`. -/
def addRule (G : Grammar L C V) (r : SyntaxRule C V) (hr : r.tc ∈ G.sorts)
    (ha : ∀ p ∈ r.args, p.1 ∈ G.sorts) : Grammar (Option L) C V where
  sorts := G.sorts
  prov := G.prov
  rule
    | none => r
    | some l => G.rule l
  rule_tc
    | none => hr
    | some l => G.rule_tc l
  rule_args
    | none => ha
    | some l => G.rule_args l
  prov_sort := G.prov_sort
  prov_not_sort := G.prov_not_sort

variable {G : Grammar L C V} {r : SyntaxRule C V} {hr : r.tc ∈ G.sorts}
  {ha : ∀ p ∈ r.args, p.1 ∈ G.sorts}

variable (G r hr ha) in
/-- The inclusion of the old grammar into the extended one. -/
def inclRule : Rewrite G (G.addRule r hr ha) where
  tc c := c
  var := Function.Embedding.refl V
  tmpl l := .node (some l) ((G.rule l).args.map fun p => .var p.2)
  sort_mem _ h := h
  prov_eq h := h
  tmpl_sort l := by
    refine .node (by simp [addRule]) fun q hq => ?_
    obtain ⟨t, p⟩ := q
    obtain rfl := mem_zip_map_self hq
    exact .var (List.mem_map.2 ⟨p, (List.of_mem_zip hq).2, rfl⟩)

variable (G r hr ha) in
/-- The elimination rewrite: identity on the old rules, the definiens `δ` on
the new rule. -/
def elimRule (δ : Tree L V) (hδ : G.HasSort (fun w s => (s, w) ∈ r.args) δ r.tc) :
    Rewrite (G.addRule r hr ha) G where
  tc c := c
  var := Function.Embedding.refl V
  tmpl
    | none => δ
    | some l => .node l ((G.rule l).args.map fun p => .var p.2)
  sort_mem _ h := h
  prov_eq h := h
  tmpl_sort
    | none => hδ.mono fun w s h => by simpa [addRule] using h
    | some l => by
      refine .node (by simp) fun q hq => ?_
      obtain ⟨t, p⟩ := q
      obtain rfl := mem_zip_map_self hq
      exact .var (by simpa [addRule] using (List.of_mem_zip hq).2)

/-- Eliminating after including is the identity rewrite. -/
theorem inclRule_comp_elimRule [DecidableEq V] (δ : Tree L V)
    (hδ : G.HasSort (fun w s => (s, w) ∈ r.args) δ r.tc) :
    (inclRule G r hr ha).comp (elimRule G r hr ha δ hδ) = Rewrite.id G := by
  ext l
  · rfl
  · rfl
  · change (elimRule G r hr ha δ hδ).tree (.node (some l) _) = (Rewrite.id G).tmpl l
    rw [Rewrite.tree_node]
    conv_rhs => rw [← Tree.subst_var ((Rewrite.id G).tmpl l)]
    apply Tree.subst_congr
    intro w hw
    obtain ⟨p, hp, rfl⟩ := (Rewrite.id G).mem_vars_tmpl hw
    exact (elimRule G r hr ha δ hδ).argSubst_map (G := G.addRule r hr ha) (l := some l)
      (elimRule G r hr ha δ hδ).tree (mem_zip_map_self_of_mem (fun p : C × V => Tree.var p.2) hp)

end Grammar

namespace GAxSet

variable (X : GAxSet.{u}) (r : SyntaxRule X.C X.V) (hr : r.tc ∈ X.G.sorts)
  (ha : ∀ p ∈ r.args, p.1 ∈ X.G.sorts) (defs : Set (TAssertion (Option X.L) X.C X.V))
  (hdefs : ∀ B ∈ defs, B.WellFormed (X.G.addRule r hr ha))

/-- The extension of `X` by the syntax rule `r` and the axioms `defs`. -/
abbrev extend : GAxSet.{u} :=
  GAxSet.of (X.G.addRule r hr ha) ((inclRule X.G r hr ha).assertion '' X.axioms ∪ defs) (by
    rintro B (⟨A, hA, rfl⟩ | hB)
    · exact Rewrite.wellFormed (X.wf A hA)
    · exact hdefs B hB)

/-- The inclusion of `X` into its extension. -/
def extendIncl : X ⟶ X.extend r hr ha defs hdefs :=
  Hom.ofImage (inclRule X.G r hr ha) fun A hA => Or.inl ⟨A, hA, rfl⟩

@[simp] theorem extendIncl_toRewrite :
    (X.extendIncl r hr ha defs hdefs).toRewrite = inclRule X.G r hr ha := rfl

/-- The definitional extension theorem: if eliminating the new rule by its
definiens sends every new axiom to a theorem of `X`, the extension is
conservative over the language of `X`. -/
theorem extendIncl_conservative [Infinite X.V] (δ : Tree X.L X.V)
    (hδ : X.G.HasSort (fun w s => (s, w) ∈ r.args) δ r.tc)
    (helim : ∀ B ∈ defs, TDerivable X.G X.axioms ((elimRule X.G r hr ha δ hδ).assertion B)) :
    (X.extendIncl r hr ha defs hdefs).Conservative := by
  refine Hom.conservative_of_elimination _ (elimRule X.G r hr ha δ hδ)
    (inclRule_comp_elimRule δ hδ) ?_
  rintro B (⟨A, hA, rfl⟩ | hB)
  · rw [← Rewrite.comp_assertion _ _ (X.wf A hA), inclRule_comp_elimRule δ hδ,
      Rewrite.id_assertion (X.wf A hA)]
    exact TDerivable.of_mem hA (X.wf A hA)
  · exact helim B hB

include hdefs in
/-- The definitional extension theorem, spelled out: a well-formed assertion
of the old language derivable in the extension is derivable in `X`. -/
theorem definitional_extension [Infinite X.V] (δ : Tree X.L X.V)
    (hδ : X.G.HasSort (fun w s => (s, w) ∈ r.args) δ r.tc)
    (helim : ∀ B ∈ defs, TDerivable X.G X.axioms ((elimRule X.G r hr ha δ hδ).assertion B))
    {A : TAssertion X.L X.C X.V} (hA : A.WellFormed X.G)
    (h : TDerivable (X.G.addRule r hr ha) ((inclRule X.G r hr ha).assertion '' X.axioms ∪ defs)
      ((inclRule X.G r hr ha).assertion A)) : TDerivable X.G X.axioms A :=
  (Hom.conservative_iff _).1 (extendIncl_conservative X r hr ha defs hdefs δ hδ helim) A hA h

end GAxSet

end Silmaril.Logic.Metamath
