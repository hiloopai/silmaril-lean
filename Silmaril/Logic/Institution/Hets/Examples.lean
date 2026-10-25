module

public import Silmaril.Logic.Institution.Hets.Heterogeneous
public import Silmaril.Logic.Institution.Hets.Decomposition
public import Silmaril.Logic.Institution.Grothendieck.Examples.Het

@[expose] public section

/-!
# A worked heterogeneous example over `PL → FOL ← EQ`

Over the logic graph `hetLogic` (`PL → FOL ← EQ`, from the Grothendieck track) we build a small
heterogeneous development graph with six nodes:

* `plAx` (in PL, signature `P`, axioms `Γ`) and `plGoal` (in PL, signature `P`, axioms `Δ`);
* `folOfPl` (in FOL, the translated signature, no axioms), with a heterogeneous global definition
  link `plAx ⟶(inl, id) folOfPl` along the comorphism `PL → FOL`;
* `eqAx`, `eqGoal` and `folOfEq` likewise for EQ, with the link `eqAx ⟶(inr, id) folOfEq`.

The proof obligation is the heterogeneous global theorem link `plGoal ⇢(inl, id) folOfPl`
(respectively `eqGoal ⇢(inr, id) folOfEq`): the FOL view of `Γ` proves the goals `Δ`. By
Glob-Decomposition, Local Inference and Basic Inference it reduces to first-order consequence
`(inl, id)(Γ) ⊨ (inl, id)(φ)` for `φ ∈ Δ`; because `PL → FOL` is model-expansive, that is
borrowed from (and equivalent to) propositional consequence `Γ ⊨ φ` (`entails_lift_iff`). The
theorems `plGoal_globalThm_iff` and `eqGoal_globalThm_iff` state the resulting equivalence, and
`modusPonens_globalThm` discharges a concrete instance: `{p, p → q}` proves `q`.

## References

* `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Definition 6.25 and
  Figure 6.1 (printed pages 161–162, PDF pages 163–164): heterogeneous development graphs and
  internalized borrowing.
* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2 and
  Proposition 13 (PDF pages 13–15): the decomposition rules.
* `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4) and
  Fig. 2: the Hets logic graph.
-/

namespace Silmaril.Logic.Institution.Hets.Example

open CategoryTheory Limits Examples IndexedCoInst

/-- The nodes of the example graph. -/
inductive Node : Type
  | plAx
  | plGoal
  | folOfPl
  | eqAx
  | eqGoal
  | folOfEq

variable (P : Type) (Sg : EQ.Signature)

/-- The PL signature `(left, P)`. -/
abbrev plSig : FlatSig hetLogic := mkSig hetLogic WalkingCospan.left P

/-- The FOL signature `(one, Φ(P))` of the propositional variables `P`. -/
abbrev folSigOfPl : FlatSig hetLogic :=
  mkSig hetLogic WalkingCospan.one ((coHom hetLogic WalkingCospan.Hom.inl).Φ.obj P)

/-- The heterogeneous signature morphism `(inl, id) : (left, P) ⟶ (one, Φ(P))`. -/
abbrev liftPl : plSig P ⟶ folSigOfPl P := lift hetLogic WalkingCospan.Hom.inl P

/-- The EQ signature `(right, Sg)`. -/
abbrev eqSig : FlatSig hetLogic := mkSig hetLogic WalkingCospan.right Sg

/-- The FOL signature `(one, Φ(Sg))` of the equational signature `Sg`. -/
abbrev folSigOfEq : FlatSig hetLogic :=
  mkSig hetLogic WalkingCospan.one ((coHom hetLogic WalkingCospan.Hom.inr).Φ.obj Sg)

/-- The heterogeneous signature morphism `(inr, id) : (right, Sg) ⟶ (one, Φ(Sg))`. -/
abbrev liftEq : eqSig Sg ⟶ folSigOfEq Sg := lift hetLogic WalkingCospan.Hom.inr Sg

/-- The signatures of the nodes. -/
def sig : Node → FlatSig hetLogic
  | .plAx => plSig P
  | .plGoal => plSig P
  | .folOfPl => folSigOfPl P
  | .eqAx => eqSig Sg
  | .eqGoal => eqSig Sg
  | .folOfEq => folSigOfEq Sg

/-- The local axioms of the nodes. -/
def axioms (Γ Δ : Set (PL.Formula P)) (Γe Δe : Set (EQ.Equation Sg)) :
    (N : Node) → Set ((flat hetLogic).obj (sig P Sg N)).Sen
  | .plAx => Γ
  | .plGoal => Δ
  | .folOfPl => ∅
  | .eqAx => Γe
  | .eqGoal => Δe
  | .folOfEq => ∅

/-- The global definition links: `plAx ⟶(inl, id) folOfPl` and `eqAx ⟶(inr, id) folOfEq`. -/
def globalDef : (M N : Node) → Set (sig P Sg M ⟶ sig P Sg N)
  | .plAx, .folOfPl => {liftPl P}
  | .eqAx, .folOfEq => {liftEq Sg}
  | _, _ => ∅

/-- The rank of a node: the FOL nodes lie above the others. -/
def rank : Node → ℕ
  | .folOfPl => 1
  | .folOfEq => 1
  | _ => 0

theorem wf : WellFounded fun M N : Node =>
    (globalDef P Sg M N).Nonempty ∨ (∅ : Set (sig P Sg M ⟶ sig P Sg N)).Nonempty ∨
      (∅ : Set (sig P Sg N ⟶ sig P Sg M)).Nonempty := by
  refine Subrelation.wf ?_ (InvImage.wf rank wellFounded_lt)
  intro M N h
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · cases M <;> cases N <;> first | exact Nat.zero_lt_one | exact (hσ : False).elim
  · exact (hσ : False).elim
  · exact (hσ : False).elim

/-- The heterogeneous development graph of the example.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Definition 6.25
(printed page 161, PDF page 163). -/
def graph (Γ Δ : Set (PL.Formula P)) (Γe Δe : Set (EQ.Equation Sg)) :
    DevGraph (flat hetLogic) where
  Node := Node
  sig := sig P Sg
  axioms := axioms P Sg Γ Δ Γe Δe
  globalDef := globalDef P Sg
  localDef _ _ := ∅
  hidingDef _ _ := ∅
  wf := wf P Sg

variable {P Sg}

/-- **The PL theorem link, discharged by borrowing**: `plGoal ⇢(inl, id) folOfPl` holds iff
every goal in `Δ` is a propositional consequence of `Γ`. The proof route is Glob-Decomposition,
Local Inference and Basic Inference down to the first-order goals `(inl, id)(Γ) ⊨ (inl, id)(φ)`,
which `entails_lift_iff` borrows from PL (the comorphism `PL → FOL` is model-expansive,
`plToFol_modelExpansive`); model expansion also gives the converse.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4 (printed page 161,
PDF page 163: internalized borrowing, "Shifting of proof goals is sound if the involved
comorphism admit model expansion");
`mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2 and
Proposition 13 (PDF pages 13–15). -/
theorem plGoal_globalThm_iff (Γ Δ : Set (PL.Formula P)) (Γe Δe : Set (EQ.Equation Sg)) :
    (graph P Sg Γ Δ Γe Δe).GlobalThm .plGoal .folOfPl (liftPl P) ↔
      ∀ φ ∈ Δ, (PL.institution.obj P).Entails Γ φ := by
  have hexp : Corridor.ModelExpansive ((flat hetLogic).map (liftPl P)) := by
    exact (congrArg Corridor.ModelExpansive (flat_map_lift hetLogic WalkingCospan.Hom.inl P)).mpr
      (plToFol_modelExpansive P)
  have hAx : ∀ n, n ∈ (graph P Sg Γ Δ Γe Δe).models .plAx ↔
      ∀ ψ ∈ Γ, (PL.institution.obj P).Sat n ψ := by
    intro n
    refine (DevGraph.mem_models_iff _ _ _).trans ?_
    refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_, ?_⟩⟩ <;>
      · intro K σ hσ
        cases K <;> exact (hσ : False).elim
  have hGoal : ∀ n, n ∈ (graph P Sg Γ Δ Γe Δe).models .plGoal ↔
      ∀ ψ ∈ Δ, (PL.institution.obj P).Sat n ψ := by
    intro n
    refine (DevGraph.mem_models_iff _ _ _).trans ?_
    refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_, ?_⟩⟩ <;>
      · intro K σ hσ
        cases K <;> exact (hσ : False).elim
  have hFol : ∀ m, m ∈ (graph P Sg Γ Δ Γe Δe).models .folOfPl ↔
      DevGraph.reduct (liftPl P) m ∈ (graph P Sg Γ Δ Γe Δe).models .plAx := by
    intro m
    refine (DevGraph.mem_models_iff _ _ _).trans ?_
    refine ⟨fun h => h.2.1 .plAx (liftPl P) rfl, fun h => ⟨fun ψ hψ => (hψ : False).elim, ?_,
      ?_, ?_⟩⟩
    · intro K σ hσ
      cases K
      all_goals first
        | exact (hσ : False).elim
        | (obtain rfl : σ = liftPl P := hσ; exact h)
    all_goals
      intro K σ hσ
      cases K <;> exact (hσ : False).elim
  constructor
  · intro h φ hφ n hn
    obtain ⟨m, rfl⟩ := hexp n
    exact (hGoal _).1 (h m ((hFol m).2 ((hAx _).2 hn))) φ hφ
  · intro h m hm
    exact (hGoal _).2 fun φ hφ => h φ hφ _ ((hAx _).1 ((hFol m).1 hm))

/-- **The EQ theorem link, discharged by borrowing**: `eqGoal ⇢(inr, id) folOfEq` holds iff
every equation in `Δe` is an equational consequence of `Γe` (the comorphism `EQ → FOL` is
model-expansive, `eqToFol_modelExpansive`).

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4 (printed page 161,
PDF page 163); `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`,
§5.2 and Proposition 13 (PDF pages 13–15). -/
theorem eqGoal_globalThm_iff (Γ Δ : Set (PL.Formula P)) (Γe Δe : Set (EQ.Equation Sg)) :
    (graph P Sg Γ Δ Γe Δe).GlobalThm .eqGoal .folOfEq (liftEq Sg) ↔
      ∀ e ∈ Δe, (EQ.institution.obj Sg).Entails Γe e := by
  have hexp : Corridor.ModelExpansive ((flat hetLogic).map (liftEq Sg)) := by
    exact (congrArg Corridor.ModelExpansive (flat_map_lift hetLogic WalkingCospan.Hom.inr Sg)).mpr
      (eqToFol_modelExpansive Sg)
  have hAx : ∀ n, n ∈ (graph P Sg Γ Δ Γe Δe).models .eqAx ↔
      ∀ ψ ∈ Γe, (EQ.institution.obj Sg).Sat n ψ := by
    intro n
    refine (DevGraph.mem_models_iff _ _ _).trans ?_
    refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_, ?_⟩⟩ <;>
      · intro K σ hσ
        cases K <;> exact (hσ : False).elim
  have hGoal : ∀ n, n ∈ (graph P Sg Γ Δ Γe Δe).models .eqGoal ↔
      ∀ ψ ∈ Δe, (EQ.institution.obj Sg).Sat n ψ := by
    intro n
    refine (DevGraph.mem_models_iff _ _ _).trans ?_
    refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_, ?_⟩⟩ <;>
      · intro K σ hσ
        cases K <;> exact (hσ : False).elim
  have hFol : ∀ m, m ∈ (graph P Sg Γ Δ Γe Δe).models .folOfEq ↔
      DevGraph.reduct (liftEq Sg) m ∈ (graph P Sg Γ Δ Γe Δe).models .eqAx := by
    intro m
    refine (DevGraph.mem_models_iff _ _ _).trans ?_
    refine ⟨fun h => h.2.1 .eqAx (liftEq Sg) rfl, fun h => ⟨fun ψ hψ => (hψ : False).elim, ?_,
      ?_, ?_⟩⟩
    · intro K σ hσ
      cases K
      all_goals first
        | exact (hσ : False).elim
        | (obtain rfl : σ = liftEq Sg := hσ; exact h)
    all_goals
      intro K σ hσ
      cases K <;> exact (hσ : False).elim
  constructor
  · intro h φ hφ n hn
    obtain ⟨m, rfl⟩ := hexp n
    exact (hGoal _).1 (h m ((hFol m).2 ((hAx _).2 hn))) φ hφ
  · intro h m hm
    exact (hGoal _).2 fun φ hφ => h φ hφ _ ((hAx _).1 ((hFol m).1 hm))

/-- A concrete instance: in the FOL view of `{p, p → q}`, the PL goal `q` holds.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4 (printed page 161,
PDF page 163). -/
theorem modusPonens_globalThm (Γe Δe : Set (EQ.Equation Sg)) :
    (graph (Fin 2) Sg {.var 0, .imp (.var 0) (.var 1)} {.var 1} Γe Δe).GlobalThm
      .plGoal .folOfPl (liftPl (Fin 2)) := by
  refine (plGoal_globalThm_iff _ _ _ _).2 ?_
  rintro φ rfl M hM
  exact hM (PL.Formula.imp (PL.Formula.var 0) (PL.Formula.var 1)) (Set.mem_insert_of_mem _ rfl)
    (hM (PL.Formula.var 0) (Set.mem_insert _ _))

/-- Heterogeneous borrowing for a structured specification: a PL presentation entails `φ` iff
its translation to FOL entails the translation of `φ`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, Proposition 5.2(2)
and Theorem 5.3 (printed pages 126–127, PDF pages 128–129), §6.11 (printed page 180, PDF
page 182). -/
theorem pl_entails_iff_translateAlong (Γ : Set (PL.Formula P)) (φ : PL.Formula P) :
    (basicIn hetLogic WalkingCospan.left P Γ).Entails φ ↔
      (translateAlong hetLogic WalkingCospan.Hom.inl
          (basicIn hetLogic WalkingCospan.left P Γ)).Entails
        (((coHom hetLogic WalkingCospan.Hom.inl).ρ.app P).sen φ) :=
  entails_translateAlong_iff hetLogic WalkingCospan.Hom.inl plToFol_modelExpansive _ φ

end Silmaril.Logic.Institution.Hets.Example
