module

public import Silmaril.Logic.Institution.Hets.Calculus
public import Silmaril.Logic.Institution.Hets.Heterogeneous

@[expose] public section

/-!
# Heterogeneous proofs: borrowing along comorphisms as development-graph rules

A heterogeneous development graph is a development graph over the Grothendieck institution
`flat F` of a logic graph `F` (Mossakowski, Definition 6.25), so the calculus of
`Hets/Calculus.lean` applies to it unchanged, and its soundness is Theorem 6.26 (soundness
part). What is specific to the heterogeneous case is that a Grothendieck signature morphism
`(d, σ)` has a model-expansive corridor as soon as the comorphism of `d` and the reduct along
`σ` are model-expansive (`modelExpansive_flat_map`); then:

* `Derivable.modelExpansion_comorphism`: the rule Model-Expansion of Fig. 6.1 ("if `d` is
  marked as model-expansive and `K` is isolated");
* `Derivable.hetBorrowing`: heterogeneous borrowing as a derived rule: to prove `K ⇢σ N`, move
  `N` along a model-expansive comorphism into an isolated node `N'` and prove `K' ⇢σ' N'` there
  (Borrowing with Model-Expansion);
* `Derivable.hetSound`: soundness for heterogeneous development graphs.

## References

* `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Definition 6.25, Figure
  6.1 and Theorem 6.26 (printed pages 161–163, PDF pages 163–165); §5.6.2, rule Borrowing
  (printed page 140, PDF page 142).
* `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
  Definition 3.6 and Proposition 3.7: model expansion and borrowing.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe n u₀ v₀ u v w m₁ m₂

namespace IndexedCoInst

variable {Ind : Type u₀} [Category.{v₀} Ind] (F : Ind ⥤ CoIns.{u, v, w, m₁, m₂})

/-- A Grothendieck signature morphism `(d, σ)` has a model-expansive corridor when the
comorphism of `d` and the reduct along `σ` are model-expansive.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6; `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3,
Definition 3.1 (PDF page 4: the corridor `ρᵈ_Σ ; Iʲ(σ)`). -/
theorem modelExpansive_flat_map {X Y : FlatSig F} (f : X ⟶ Y)
    (hb : (coHom F f.base).ModelExpansive)
    (hf : Corridor.ModelExpansive ((inst F Y.base).I.map f.fiber)) :
    Corridor.ModelExpansive ((flat F).map f) :=
  Corridor.ModelExpansive.comp (hb X.fiber) hf

end IndexedCoInst

namespace DevGraph

open IndexedCoInst

variable {Ind : Type u₀} [Category.{v₀} Ind] {F : Ind ⥤ CoIns.{u, v, w, m₁, m₂}}
  {R : Set Rule} {ent : ∀ S : FlatSig F, Set ((flat F).obj S).Sen → ((flat F).obj S).Sen → Prop}

/-- **Model-Expansion** for comorphisms: a link `N ⟶(d, σ) K` into an isolated node, whose
comorphism `d` and fiber reduct are model-expansive, is conservative.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Figure 6.1 (rule
Model-Expansion) and Theorem 6.26 (printed pages 162–163, PDF pages 164–165). -/
theorem Derivable.modelExpansion_comorphism {G : DevGraph.{n} (flat F)} {N K : G.Node}
    {σ : G.sig N ⟶ G.sig K} (hr : Rule.modelExpansion ∈ R)
    (hb : (coHom F σ.base).ModelExpansive)
    (hf : Corridor.ModelExpansive ((inst F (G.sig K).base).I.map σ.fiber))
    (hiso : G.IsolatedBy K (G.linkFrom N σ)) : Derivable R ent G (.cons N K σ) :=
  .modelExpansion hr (modelExpansive_flat_map F σ hb hf) hiso

/-- **Heterogeneous borrowing** as a derived rule: if `N ⟶θ' N'` moves `N` along a
model-expansive comorphism into an isolated node `N'`, then `K ⇢σ N` follows from `K ⇢θ K'`
and `K' ⇢σ' N'` whenever `θ ; σ' = σ ; θ'`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.2, rule Borrowing
(printed page 140, PDF page 142), with Model-Expansion (§6.4, Figure 6.1, printed page 162,
PDF page 164). -/
theorem Derivable.hetBorrowing {G : DevGraph.{n} (flat F)} {K K' N N' : G.Node}
    {σ : G.sig K ⟶ G.sig N} {θ : G.sig K ⟶ G.sig K'} {σ' : G.sig K' ⟶ G.sig N'}
    {θ' : G.sig N ⟶ G.sig N'} (hrb : Rule.borrowing ∈ R) (hrm : Rule.modelExpansion ∈ R)
    (hcomm : θ ≫ σ' = σ ≫ θ') (hb : (coHom F θ'.base).ModelExpansive)
    (hf : Corridor.ModelExpansive ((inst F (G.sig N').base).I.map θ'.fiber))
    (hiso : G.IsolatedBy N' (G.linkFrom N θ')) (hθ : Derivable R ent G (.glob K K' θ))
    (h : Derivable R ent G (.glob K' N' σ')) : Derivable R ent G (.glob K N σ) :=
  .borrowing hrb hcomm hθ (.modelExpansion_comorphism hrm hb hf hiso) h

/-- **Soundness for heterogeneous development graphs** (Theorem 6.26, soundness part).

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Theorem 6.26
(printed pages 162–163, PDF pages 164–165). -/
theorem Derivable.hetSound (hent : ∀ S Γ φ, ent S Γ φ → ((flat F).obj S).Entails Γ φ)
    {G : DevGraph.{n} (flat F)} {L : G.ThmLink} (h : Derivable R ent G L) : L.Holds :=
  h.sound hent

end DevGraph

end Silmaril.Logic.Institution
