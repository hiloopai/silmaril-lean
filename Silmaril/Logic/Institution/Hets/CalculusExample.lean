module

public import Silmaril.Logic.Institution.Hets.HetCalculus
public import Silmaril.Logic.Institution.Hets.Examples

@[expose] public section

/-!
# Worked derivations in the development-graph calculus

Two small heterogeneous development graphs over the logic graph `PL → FOL ← EQ`:

1. The graph `Hets.Example.graph` of `Hets/Examples.lean` (a PL presentation translated to FOL
   along the comorphism `PL → FOL`). `modusPonens_derivable` derives its theorem link
   `plGoal ⇢(inl, id) folOfPl` for `{p, p → q} ⊢ q` with the decomposition rules alone
   (Glob-Decomposition, Local Inference, Basic Inference), with semantic consequence `semEnt`
   as the entailment system; soundness then gives the theorem link
   (`modusPonens_globalThm_of_derivable`), independently of `modusPonens_globalThm`.
2. A graph with hiding (`HideExample.graph`): `full` is the PL presentation `{p₀, p₀ → p₁}` over
   two variables, `visible` hides `p₀` (a hiding link along `p ↦ p₁ : {p} → {p₀, p₁}`), and
   `goal` is the presentation `{p}`; `fol` is the FOL view of `visible` along `PL → FOL`. The
   theorem links `goal ⇢id visible` and `goal ⇢(inl, id) fol` are derived using
   Theorem-Hide-Shift within `Rule.mah`, which excludes Borrowing (`hide_derivable`,
   `hideFol_derivable`). Soundness gives them (`hide_globalThm`, `hideFol_globalThm`).

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5 and §6
  (PDF pages 10–16: the rules and the worked example of Fig. 5).
* `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4 (printed pages 161–163,
  PDF pages 163–165).
-/

namespace Silmaril.Logic.Institution.Hets.CalculusExample

open CategoryTheory Limits Examples IndexedCoInst DevGraph

/-- Semantic consequence, as a (sound and complete) entailment system. -/
def semEnt {Sign : Type*} [Category Sign] (I : Sign ⥤ Room.{0, 0, 1}) :
    ∀ S : Sign, Set (I.obj S).Sen → (I.obj S).Sen → Prop :=
  fun S Γ φ => (I.obj S).Entails Γ φ

/-! ### Generic helpers -/

section Helpers

universe n u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

/-- A node without incoming global definition links is globally reachable only from itself,
along the identity. -/
theorem globReach_eq_of_globalDef_empty {G : DevGraph.{n} I} {N : G.Node}
    (hg : ∀ K, G.globalDef K N = ∅) {M : G.Node} {τ : G.sig M ⟶ G.sig N}
    (h : G.GlobReach M N τ) : ∃ e : M = N, τ = eqToHom (congrArg G.sig e) := by
  revert hg
  induction h with
  | refl M => exact fun _ => ⟨rfl, rfl⟩
  | step hσ _ ih =>
    intro hg
    obtain ⟨rfl, -⟩ := ih hg
    rw [hg] at hσ
    simp at hσ

/-- A node without incoming global or local definition links is locally reachable only from
itself, along the identity. -/
theorem locReach_eq_of_def_empty {G : DevGraph.{n} I} {N : G.Node}
    (hg : ∀ K, G.globalDef K N = ∅) (hl : ∀ K, G.localDef K N = ∅) {M : G.Node}
    {τ : G.sig M ⟶ G.sig N} (h : G.LocReach M N τ) :
    ∃ e : M = N, τ = eqToHom (congrArg G.sig e) := by
  rcases h with h | ⟨K, σ', σ'', hσ', hg', rfl⟩
  · exact globReach_eq_of_globalDef_empty hg h
  · obtain ⟨rfl, -⟩ := globReach_eq_of_globalDef_empty hg hg'
    rw [hl] at hσ'
    simp at hσ'

/-- A global theorem link out of a node without incoming definition links is derivable with the
decomposition rules (Glob-Decomposition, Local Inference, Basic Inference) as soon as the
translated local axioms of the source are entailed by the theory of the target. -/
theorem derivable_glob_of_def_empty {R : Set Rule}
    {ent : ∀ S : Sign, Set (I.obj S).Sen → (I.obj S).Sen → Prop} {G : DevGraph.{n} I}
    {N M : G.Node} (σ : G.sig N ⟶ G.sig M) (hR : Rule.decomposition ⊆ R)
    (hg : ∀ K, G.globalDef K N = ∅) (hl : ∀ K, G.localDef K N = ∅)
    (hh : ∀ K, G.hidingDef K N = ∅)
    (hent : ∀ φ ∈ (I.map σ).sen '' G.axioms N, ent (G.sig M) (G.theory M) φ) :
    Derivable R ent G (.glob N M σ) := by
  refine .globDecomposition σ (hR (by simp [Rule.decomposition])) ?_ ?_
  · intro K τ hτ
    obtain ⟨rfl, rfl⟩ := locReach_eq_of_def_empty hg hl hτ
    rw [eqToHom_refl, Category.id_comp]
    exact .localInference σ (hR (by simp [Rule.decomposition]))
      (.basicInference (hR (by simp [Rule.decomposition])) hent)
  · intro L K θ τ hθ hτ
    obtain ⟨rfl, -⟩ := globReach_eq_of_globalDef_empty hg hτ
    rw [hh] at hθ
    simp at hθ

/-- The reduct along a signature morphism with an invertible model reduct is injective. -/
theorem reduct_injective_of_isIso {S S' : Sign} (σ : S ⟶ S') [IsIso (modHom I σ)] :
    Function.Injective (reduct (I := I) σ) := by
  intro a b h
  have ha : (inv (modHom I σ)).toFunctor.obj ((modHom I σ).toFunctor.obj a) = a :=
    congrArg (fun F : (I.obj S').Mod ⟶ (I.obj S').Mod => F.toFunctor.obj a)
      (IsIso.hom_inv_id (modHom I σ))
  have hb : (inv (modHom I σ)).toFunctor.obj ((modHom I σ).toFunctor.obj b) = b :=
    congrArg (fun F : (I.obj S').Mod ⟶ (I.obj S').Mod => F.toFunctor.obj b)
      (IsIso.hom_inv_id (modHom I σ))
  exact ha.symm.trans ((congrArg (inv (modHom I σ)).toFunctor.obj h).trans hb)

end Helpers

/-! ### The PL → FOL example, derived -/

variable (Sg : EQ.Signature)

/-- The theorem link of `Hets.Example.modusPonens_globalThm`, derived with the decomposition
rules.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF pages 13–14). -/
theorem modusPonens_derivable (Γe Δe : Set (EQ.Equation Sg)) :
    Derivable Rule.decomposition (semEnt (flat hetLogic))
      (Example.graph (Fin 2) Sg {.var 0, .imp (.var 0) (.var 1)} {.var 1} Γe Δe)
      (.glob .plGoal .folOfPl (Example.liftPl (Fin 2))) := by
  refine derivable_glob_of_def_empty _ subset_rfl (fun K => by cases K <;> rfl) (fun _ => rfl)
    (fun _ => rfl) ?_
  rintro φ ⟨ψ, hψ, rfl⟩ m hm
  obtain rfl : ψ = PL.Formula.var (1 : Fin 2) := hψ
  have hreach : (Example.graph (Fin 2) Sg {.var 0, .imp (.var 0) (.var 1)} {.var 1} Γe
      Δe).LocReach .plAx .folOfPl (Example.liftPl (Fin 2)) :=
    Or.inl (DevGraph.GlobReach.of_globalDef rfl)
  have h0 := hm _ (Or.inr ⟨.plAx, _, hreach,
    (PL.Formula.var 0 : PL.Formula (Fin 2)), Set.mem_insert _ _, rfl⟩)
  have h01 := hm _ (Or.inr ⟨.plAx, _, hreach,
    (PL.Formula.imp (.var 0) (.var 1) : PL.Formula (Fin 2)),
    Set.mem_insert_of_mem _ rfl, rfl⟩)
  exact (((flat hetLogic).map (Example.liftPl (Fin 2))).sat m _).2
    ((((flat hetLogic).map (Example.liftPl (Fin 2))).sat m _).1 h01
      ((((flat hetLogic).map (Example.liftPl (Fin 2))).sat m _).1 h0))

/-- Soundness turns the derivation into the theorem link. -/
theorem modusPonens_globalThm_of_derivable (Γe Δe : Set (EQ.Equation Sg)) :
    (Example.graph (Fin 2) Sg {.var 0, .imp (.var 0) (.var 1)} {.var 1} Γe Δe).GlobalThm
      .plGoal .folOfPl (Example.liftPl (Fin 2)) :=
  (modusPonens_derivable Sg Γe Δe).sound fun _ _ _ h => h

/-! ### An example with hiding -/

namespace HideExample

/-- The nodes. -/
inductive Node : Type
  | full
  | visible
  | goal
  | fol

/-- The PL signature `(left, Fin k)`. -/
abbrev plSig (k : ℕ) : FlatSig hetLogic := mkSig hetLogic WalkingCospan.left (Fin k)

/-- The FOL signature of the propositional variables `Fin 1`. -/
abbrev folSig : FlatSig hetLogic :=
  mkSig hetLogic WalkingCospan.one ((coHom hetLogic WalkingCospan.Hom.inl).Φ.obj (Fin 1))

/-- The hiding morphism `p ↦ p₁ : {p} → {p₀, p₁}`. -/
def hideMor : plSig 1 ⟶ plSig 2 :=
  (ι hetLogic WalkingCospan.left).Φ.map (TypeCat.ofHom fun _ : Fin 1 => (1 : Fin 2))

/-- The comorphism link `(inl, id) : (left, Fin 1) ⟶ (one, Φ(Fin 1))`. -/
abbrev liftVis : plSig 1 ⟶ folSig := lift hetLogic WalkingCospan.Hom.inl (Fin 1)

/-- Node signatures. -/
def sig : Node → FlatSig hetLogic
  | .full => plSig 2
  | .visible => plSig 1
  | .goal => plSig 1
  | .fol => folSig

/-- Local axioms: `{p₀, p₀ → p₁}` at `full` and `{p}` at `goal`. -/
def axioms : (N : Node) → Set ((flat hetLogic).obj (sig N)).Sen
  | .full => ({.var 0, .imp (.var 0) (.var 1)} : Set (PL.Formula (Fin 2)))
  | .visible => ∅
  | .goal => ({.var 0} : Set (PL.Formula (Fin 1)))
  | .fol => ∅

/-- The global definition link `visible ⟶(inl, id) fol`. -/
def globalDef : (M N : Node) → Set (sig M ⟶ sig N)
  | .visible, .fol => {liftVis}
  | _, _ => ∅

/-- The hiding link `full ⟶hideMor,h visible`. -/
def hidingDef : (M N : Node) → Set (sig N ⟶ sig M)
  | .full, .visible => {hideMor}
  | _, _ => ∅

/-- The rank of a node: links go from lower to higher rank. -/
def rank : Node → ℕ
  | .full => 0
  | .goal => 0
  | .visible => 1
  | .fol => 2

theorem wf : WellFounded fun M N : Node =>
    (globalDef M N).Nonempty ∨ (∅ : Set (sig M ⟶ sig N)).Nonempty ∨
      (hidingDef M N).Nonempty := by
  refine Subrelation.wf ?_ (InvImage.wf rank wellFounded_lt)
  intro M N h
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · cases M <;> cases N <;> first | exact (hσ : False).elim | (show rank _ < rank _; decide)
  · exact (hσ : False).elim
  · cases M <;> cases N <;> first | exact (hσ : False).elim | (show rank _ < rank _; decide)

/-- The development graph with hiding. -/
def graph : DevGraph (flat hetLogic) where
  Node := Node
  sig := sig
  axioms := axioms
  globalDef := globalDef
  localDef _ _ := ∅
  hidingDef := hidingDef
  wf := wf

/-! #### A cocone for Theorem-Hide-Shift

One cocone serves the unfoldings below `visible` and below `fol`: its apex is the FOL signature
`(one, Φ(Fin 2))`, with injections `lift2 : full ⟶ apex`, `hideMor ; lift2 : visible ⟶ apex`
and `μfol = Φ(p ↦ p₁) : fol ⟶ apex` (naturality of the comorphism lift, `liftVis_comp_μfol`).
It is weakly amalgamable because the model reduct of PL → FOL is an isomorphism. -/

/-- The function `p ↦ p₁ : {p} → {p₀, p₁}` of propositional variables. -/
def hideFun : Fin 1 ⟶ Fin 2 := TypeCat.ofHom fun _ : Fin 1 => (1 : Fin 2)

/-- The apex `(one, Φ(Fin 2))`. -/
abbrev folSig2 : FlatSig hetLogic :=
  mkSig hetLogic WalkingCospan.one ((coHom hetLogic WalkingCospan.Hom.inl).Φ.obj (Fin 2))

/-- The comorphism link `(inl, id) : (left, Fin 2) ⟶ (one, Φ(Fin 2))`. -/
abbrev lift2 : plSig 2 ⟶ folSig2 := lift hetLogic WalkingCospan.Hom.inl (Fin 2)

/-- The FOL renaming `Φ(p ↦ p₁) : (one, Φ(Fin 1)) ⟶ (one, Φ(Fin 2))`. -/
def μfol : folSig ⟶ folSig2 :=
  (ι hetLogic WalkingCospan.one).Φ.map ((coHom hetLogic WalkingCospan.Hom.inl).Φ.map hideFun)

/-- Naturality of the lift along `PL → FOL`. -/
theorem liftVis_comp_μfol : liftVis ≫ μfol = hideMor ≫ lift2 :=
  ((CategoryTheory.Grothendieck.ιNatTrans (F := sign hetLogic) WalkingCospan.Hom.inl).naturality
    hideFun).symm

/-- The injections of the cocone, by node. -/
def mu : (K : Node) → (sig K ⟶ folSig2)
  | .full => lift2
  | .visible => hideMor ≫ lift2
  | .goal => hideMor ≫ lift2
  | .fol => μfol

theorem mu_globalDef {K M : Node} {σ : sig K ⟶ sig M} (hσ : σ ∈ globalDef K M) :
    σ ≫ mu M = mu K := by
  cases K <;> cases M <;> try exact (hσ : False).elim
  obtain rfl : σ = liftVis := hσ
  exact liftVis_comp_μfol

theorem mu_hidingDef {K M : Node} {σ : sig M ⟶ sig K} (hσ : σ ∈ hidingDef K M) :
    mu M = σ ≫ mu K := by
  cases K <;> cases M <;> try exact (hσ : False).elim
  obtain rfl : σ = hideMor := hσ
  rfl

/-- The cocone over the unfolding below any node. -/
def cocone (N : graph.Node) : graph.UCocone N where
  apex := folSig2
  μ := fun {K} _ => mu K
  glob_comm _ hσ _ := (mu_globalDef hσ).symm
  loc_comm _ hσ _ := (hσ : False).elim
  hide_comm _ hσ _ := mu_hidingDef hσ

theorem rank_lt_of_globalDef {K M : Node} {σ : sig K ⟶ sig M} (hσ : σ ∈ globalDef K M) :
    rank K < rank M := by
  cases K <;> cases M <;> first | exact (hσ : False).elim | decide

theorem rank_lt_of_hidingDef {K M : Node} {σ : sig M ⟶ sig K} (hσ : σ ∈ hidingDef K M) :
    rank K < rank M := by
  cases K <;> cases M <;> first | exact (hσ : False).elim | decide

theorem rank_le_of_npath {N K : graph.Node} (p : graph.NPath N K) : rank K ≤ rank N := by
  induction p with
  | nil => exact le_rfl
  | glob σ hσ _ ih => exact (rank_lt_of_globalDef hσ).le.trans ih
  | hide σ hσ _ ih => exact (rank_lt_of_hidingDef hσ).le.trans ih

/-- Global definition links start at `visible`. -/
theorem globalDef_src {K M : Node} {σ : sig K ⟶ sig M} (hσ : σ ∈ globalDef K M) :
    K = .visible := by
  cases K <;> cases M <;> first | exact (hσ : False).elim | rfl

/-- Hiding definition links start at `full`. -/
theorem hidingDef_src {K M : Node} {σ : sig M ⟶ sig K} (hσ : σ ∈ hidingDef K M) :
    K = .full := by
  cases K <;> cases M <;> first | exact (hσ : False).elim | rfl

/-- There is at most one global definition link out of a node. -/
theorem globalDef_unique {K M M' : Node} {σ : sig K ⟶ sig M} {σ' : sig K ⟶ sig M'}
    (hσ : σ ∈ globalDef K M) (hσ' : σ' ∈ globalDef K M') : M = M' ∧ HEq σ σ' := by
  cases K <;> cases M <;> cases M' <;>
    first
      | exact (hσ : False).elim
      | exact (hσ' : False).elim
      | (obtain rfl : σ = liftVis := hσ
         obtain rfl : σ' = liftVis := hσ'
         exact ⟨rfl, HEq.rfl⟩)

/-- There is at most one hiding definition link out of a node. -/
theorem hidingDef_unique {K M M' : Node} {σ : sig M ⟶ sig K} {σ' : sig M' ⟶ sig K}
    (hσ : σ ∈ hidingDef K M) (hσ' : σ' ∈ hidingDef K M') : M = M' ∧ HEq σ σ' := by
  cases K <;> cases M <;> cases M' <;>
    first
      | exact (hσ : False).elim
      | exact (hσ' : False).elim
      | (obtain rfl : σ = hideMor := hσ
         obtain rfl : σ' = hideMor := hσ'
         exact ⟨rfl, HEq.rfl⟩)

/-- Paths of the unfolding are unique: the graph is a tree below every node. -/
theorem npath_eq {N : graph.Node} : ∀ {K : graph.Node} (p q : graph.NPath N K), p = q := by
  intro K p
  induction p with
  | nil =>
    intro q
    cases q with
    | nil => rfl
    | glob σ hσ q => exact absurd (rank_le_of_npath q) (not_le.2 (rank_lt_of_globalDef hσ))
    | hide σ hσ q => exact absurd (rank_le_of_npath q) (not_le.2 (rank_lt_of_hidingDef hσ))
  | glob σ hσ p ih =>
    intro q
    cases q with
    | nil => exact absurd (rank_le_of_npath p) (not_le.2 (rank_lt_of_globalDef hσ))
    | glob σ' hσ' q =>
      obtain ⟨rfl, h⟩ := globalDef_unique hσ hσ'
      cases eq_of_heq h
      cases ih q
      rfl
    | hide σ' hσ' q => cases (globalDef_src hσ).symm.trans (hidingDef_src hσ')
  | hide σ hσ p ih =>
    intro q
    cases q with
    | nil => exact absurd (rank_le_of_npath p) (not_le.2 (rank_lt_of_hidingDef hσ))
    | glob σ' hσ' q => cases (globalDef_src hσ').symm.trans (hidingDef_src hσ)
    | hide σ' hσ' q =>
      obtain ⟨rfl, h⟩ := hidingDef_unique hσ hσ'
      cases eq_of_heq h
      cases ih q
      rfl

/-- Objects of the unfolding are unique (there are no local links). -/
theorem uobj_eq {N K : graph.Node} (i j : graph.UObj N K) : i = j := by
  rcases i with ⟨p⟩ | ⟨σ, hσ, p⟩
  · rcases j with ⟨q⟩ | ⟨σ', hσ', q⟩
    · rw [npath_eq p q]
    · exact (hσ' : False).elim
  · exact (hσ : False).elim

/-- A path of the unfolding below `N` starts at `N`, at `visible` or at `full`. -/
theorem npath_src {N K : graph.Node} (p : graph.NPath N K) :
    K = N ∨ K = .visible ∨ K = .full := by
  cases p with
  | nil => exact Or.inl rfl
  | glob σ hσ _ => exact Or.inr (Or.inl (globalDef_src hσ))
  | hide σ hσ _ => exact Or.inr (Or.inr (hidingDef_src hσ))

/-- No path of the unfolding below `visible` or `fol` starts at `goal`. -/
theorem not_uobj_goal {N : graph.Node} (hN : N = .visible ∨ N = .fol) (i : graph.UObj N .goal) :
    False := by
  rcases i with ⟨p⟩ | ⟨σ, hσ, p⟩
  · rcases npath_src p with h | h | h
    · rcases hN with rfl | rfl <;> cases h
    · cases h
    · cases h
  · exact (hσ : False).elim

/-- No path of the unfolding below `visible` starts at `fol`. -/
theorem not_uobj_visible_fol (i : graph.UObj .visible .fol) : False := by
  rcases i with ⟨p⟩ | ⟨σ, hσ, p⟩
  · rcases npath_src p with h | h | h <;> cases h
  · exact (hσ : False).elim

/-- The model reduct along `PL → FOL` is surjective. -/
theorem reduct_lift2_surjective : Function.Surjective (reduct (I := flat hetLogic) lift2) :=
  (congrArg Corridor.ModelExpansive (flat_map_lift hetLogic WalkingCospan.Hom.inl (Fin 2))).mpr
    (plToFol_modelExpansive (Fin 2))

/-- The model reduct along `PL → FOL` is injective. -/
theorem reduct_liftVis_injective : Function.Injective (reduct (I := flat hetLogic) liftVis) := by
  have : IsIso (modHom (flat hetLogic) liftVis) :=
    Het.isIso_modHom_flat liftVis (by exact IsIso.id _)
  exact reduct_injective_of_isIso liftVis

/-- The path `full ⟶hideMor,h visible` into `visible`. -/
def pathFullVis : graph.NPath .visible .full :=
  .hide (G := graph) (K := Node.full) (M := Node.visible) hideMor (Set.mem_singleton _) .nil

/-- The path `visible ⟶ fol` into `fol`. -/
def pathVisFol : graph.NPath .fol .visible :=
  .glob (G := graph) (K := Node.visible) (M := Node.fol) liftVis (Set.mem_singleton _) .nil

/-- The path `full ⟶hideMor,h visible ⟶ fol` into `fol`. -/
def pathFullFol : graph.NPath .fol .full :=
  .hide (G := graph) (K := Node.full) (M := Node.visible) hideMor (Set.mem_singleton _) pathVisFol

theorem cocone_visible_weaklyAmalgamable : (cocone .visible).WeaklyAmalgamable := by
  intro f
  obtain ⟨m, hm⟩ := reduct_lift2_surjective (f.mod (.npath pathFullVis))
  refine ⟨m, fun K i => ?_⟩
  cases K
  · rw [uobj_eq i (.npath pathFullVis)]
    exact hm
  · rw [uobj_eq i (.npath .nil)]
    show reduct (hideMor ≫ lift2) m = _
    rw [reduct_comp, hm]
    exact f.hide_eq (K := Node.full) (M := Node.visible) hideMor (Set.mem_singleton _) .nil
  · exact (not_uobj_goal (Or.inl rfl) i).elim
  · exact (not_uobj_visible_fol i).elim

theorem cocone_fol_weaklyAmalgamable : (cocone .fol).WeaklyAmalgamable := by
  intro f
  obtain ⟨m, hm⟩ := reduct_lift2_surjective (f.mod (.npath pathFullFol))
  have hvis : reduct (hideMor ≫ lift2) m = f.mod (.npath pathVisFol) := by
    rw [reduct_comp, hm]
    exact f.hide_eq (K := Node.full) (M := Node.visible) hideMor (Set.mem_singleton _) pathVisFol
  refine ⟨m, fun K i => ?_⟩
  cases K
  · rw [uobj_eq i (.npath pathFullFol)]
    exact hm
  · rw [uobj_eq i (.npath pathVisFol)]
    exact hvis
  · exact (not_uobj_goal (Or.inr rfl) i).elim
  · rw [uobj_eq i (.npath .nil)]
    show reduct μfol m = _
    refine reduct_liftVis_injective (?_ : reduct liftVis (reduct μfol m) = reduct liftVis _)
    rw [← reduct_comp, liftVis_comp_μfol, hvis]
    exact f.glob_eq (K := Node.visible) (M := Node.fol) liftVis (Set.mem_singleton _) .nil

/-- `sen(hideMor)(p) = p₁`. -/
theorem sen_hideMor :
    ((flat hetLogic).map hideMor).sen (PL.Formula.var 0) = PL.Formula.var (1 : Fin 2) := by
  rfl

/-- The premise of Theorem-Hide-Shift: in the graph extended by the node `C` over the cocone,
`goal ⇢(hideMor ; lift2) C` is derivable with the decomposition rules (the theory of `C`
contains `lift2(p₀)` and `lift2(p₀ → p₁)` along the local link from `full`). -/
theorem derivable_thsNode {N : graph.Node} (p : graph.NPath N .full) (τ : plSig 1 ⟶ folSig2)
    (hτ : τ = hideMor ≫ lift2) :
    Derivable Rule.mah (semEnt (flat hetLogic)) (graph.addNode (graph.thsNode (cocone N)))
      (.glob (some .goal) none τ) := by
  subst hτ
  refine derivable_glob_of_def_empty _ Set.subset_union_left
    (fun K => by rcases K with _ | (_ | _ | _ | _) <;> rfl)
    (fun K => by rcases K with _ | (_ | _ | _ | _) <;> rfl)
    (fun K => by rcases K with _ | (_ | _ | _ | _) <;> rfl) ?_
  rintro φ ⟨ψ, hψ, rfl⟩ m hm
  obtain rfl : ψ = PL.Formula.var (0 : Fin 1) := hψ
  have hloc : lift2 ∈ (graph.addNode (graph.thsNode (cocone N))).localDef (some .full) none :=
    ⟨.npath p, rfl⟩
  have hreach : (graph.addNode (graph.thsNode (cocone N))).LocReach (some .full) none lift2 :=
    Or.inr ⟨none, lift2, 𝟙 _, hloc, .refl _, (Category.comp_id _).symm⟩
  have h0 := hm _ (Or.inr ⟨some .full, _, hreach,
    (PL.Formula.var 0 : PL.Formula (Fin 2)), Set.mem_insert _ _, rfl⟩)
  have h01 := hm _ (Or.inr ⟨some .full, _, hreach,
    (PL.Formula.imp (.var 0) (.var 1) : PL.Formula (Fin 2)),
    Set.mem_insert_of_mem _ rfl, rfl⟩)
  have h0' := (((flat hetLogic).map lift2).sat m _).1 h0
  have h01' := (((flat hetLogic).map lift2).sat m _).1 h01
  have e : ((flat hetLogic).map (hideMor ≫ lift2)).sen (PL.Formula.var 0 : PL.Formula (Fin 1)) =
      ((flat hetLogic).map lift2).sen (PL.Formula.var (1 : Fin 2)) :=
    (map_comp_sen (I := flat hetLogic) hideMor lift2 _).trans (congrArg _ sen_hideMor)
  have key : ((flat hetLogic).obj folSig2).Sat m
      (((flat hetLogic).map lift2).sen (PL.Formula.var (1 : Fin 2))) :=
    (((flat hetLogic).map lift2).sat m _).2 (h01' h0')
  exact (congrArg (fun φ => ((flat hetLogic).obj folSig2).Sat m φ) e).mpr key

/-- `goal ⇢id visible` is derivable with the rules of `Rule.mah` (with Theorem-Hide-Shift over the cocone
`({p₀, p₁}; hideMor, id)` of the unfolding of `visible`).

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1
(PDF pages 10–12). -/
theorem hide_derivable :
    Derivable Rule.mah (semEnt (flat hetLogic)) graph (.glob .goal .visible (𝟙 _)) :=
  .theoremHideShift (cocone .visible) (by simp [Rule.mah]) cocone_visible_weaklyAmalgamable
    (derivable_thsNode pathFullVis _ (Category.id_comp _))

/-- `goal ⇢(inl, id) fol` is derivable with the rules of `Rule.mah` (Theorem-Hide-Shift over a
cocone with apex `(one, Φ(Fin 2))`; amalgamation uses that PL → FOL model translation is an
isomorphism). -/
theorem hideFol_derivable :
    Derivable Rule.mah (semEnt (flat hetLogic)) graph (.glob .goal .fol liftVis) :=
  .theoremHideShift (cocone .fol) (by simp [Rule.mah]) cocone_fol_weaklyAmalgamable
    (derivable_thsNode pathFullFol _ liftVis_comp_μfol)

theorem hide_globalThm : graph.GlobalThm .goal .visible (𝟙 _) :=
  hide_derivable.sound fun _ _ _ h => h

theorem hideFol_globalThm : graph.GlobalThm .goal .fol liftVis :=
  hideFol_derivable.sound fun _ _ _ h => h

end HideExample

end Silmaril.Logic.Institution.Hets.CalculusExample
