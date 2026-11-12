module

public import Silmaril.Wasm.SpecTec.GrammarInst.Defs

/-!
# The institution of grammars: least models

A production table `P` over the attribute algebra `A` is the Horn theory `prodAxioms P`. Its
models are the interpretations closed under the productions, and `Grammar.denote ⟨A, P⟩` is
the least of them (`leastModel_sat`, `leastModel_le`). Hence a derivability assertion is a
consequence of the theory exactly when it holds in `denote` (`entails_derives_iff`): the
step-indexed denotation of the grammar framework *is* semantic consequence in the institution.
-/

public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec.Grammar

variable {N α : Type}

/-! ## Monotonicity of interpretation -/

theorem appendAll_le_of_forall₂ {A : Attr α} :
    ∀ {Es Fs : List (EncRel Bytes α)}, List.Forall₂ (· ≤ ·) Es Fs →
      appendAll A Es ≤ appendAll A Fs
  | _, _, .nil => le_rfl
  | _, _, .cons h hs => appendRel_mono h (appendAll_le_of_forall₂ hs)

theorem supList_le_of_forall₂ {σ : Type} :
    ∀ {Es Fs : List (EncRel σ α)}, List.Forall₂ (· ≤ ·) Es Fs → supList Es ≤ supList Fs
  | _, _, .nil => le_rfl
  | _, _, .cons h hs => sup_le_sup h (supList_le_of_forall₂ hs)

mutual

/-- Interpretation is monotone in the model. -/
theorem interp_mono (A : Attr α) {I J : N → EncRel Bytes α} (h : ∀ x, I x ≤ J x) :
    ∀ g : Sym N α, interp A I g ≤ interp A J g
  | .eps => le_rfl
  | .byte _ => le_rfl
  | .range _ _ => le_rfl
  | .bytes _ => le_rfl
  | .nt x => h x
  | .seq gs => appendAll_le_of_forall₂ (interps_mono A h gs)
  | .alt gs => supList_le_of_forall₂ (interps_mono A h gs)
  | .star g => kleene_mono (interp_mono A h g)
  | .plus g => appendRel_mono (interp_mono A h g) (kleene_mono (interp_mono A h g))
  | .opt g => sup_le_sup_left (interp_mono A h g) _
  | .count g k => powRel_mono (interp_mono A h g) k
  | .attr _ g => mapPartial_mono (interp_mono A h g)

/-- `interp_mono` on lists. -/
theorem interps_mono (A : Attr α) {I J : N → EncRel Bytes α} (h : ∀ x, I x ≤ J x) :
    ∀ gs : List (Sym N α), List.Forall₂ (· ≤ ·) (interps A I gs) (interps A J gs)
  | [] => .nil
  | g :: gs => .cons (interp_mono A h g) (interps_mono A h gs)

end

/-! ## `denote` is `interp` in the least model -/

mutual

/-- Interpreting a symbol in the least model of a grammar is its denotation. -/
theorem interp_leastModel (G : Gram N α) :
    ∀ g : Sym N α, interp G.alg (leastModel G).rel g = denote G g
  | .eps => (denote_eps G).symm
  | .byte b => (denote_byte G b).symm
  | .range lo hi => (denote_range G lo hi).symm
  | .bytes l => (denote_bytes G l).symm
  | .nt _ => rfl
  | .seq gs => (congrArg (appendAll G.alg) (interps_leastModel G gs)).trans (denote_seq G gs).symm
  | .alt gs => (congrArg supList (interps_leastModel G gs)).trans (denote_alt G gs).symm
  | .star g => (congrArg (kleene G.alg) (interp_leastModel G g)).trans (denote_star G g).symm
  | .plus g =>
      (congrArg (fun E => appendRel G.alg E (kleene G.alg E)) (interp_leastModel G g)).trans
        (denote_plus G g).symm
  | .opt g => (congrArg (epsRel G.alg.nil ⊔ ·) (interp_leastModel G g)).trans (denote_opt G g).symm
  | .count g k => (congrArg (powRel G.alg · k) (interp_leastModel G g)).trans
        (denote_count G g k).symm
  | .attr f g => (congrArg (EncRel.mapPartial f) (interp_leastModel G g)).trans
        (denote_attr G f g).symm

/-- `interp_leastModel` on lists. -/
theorem interps_leastModel (G : Gram N α) :
    ∀ gs : List (Sym N α), interps G.alg (leastModel G).rel gs = gs.map (denote G)
  | [] => rfl
  | g :: gs => congrArg₂ List.cons (interp_leastModel G g) (interps_leastModel G gs)

end

/-! ## The least model -/

/-- Satisfaction of every production, unfolded. -/
theorem sat_prodAxioms_iff (A : Attr α) (P : N → List (Sym N α)) (M : Model N α) :
    (∀ φ ∈ prodAxioms P, (room A N).Sat M φ) ↔ ∀ x, ∀ g ∈ P x, interp A M.rel g ≤ M.rel x := by
  constructor
  · intro h x g hg
    exact h (.prod x g) ⟨x, g, hg, rfl⟩
  · rintro h φ ⟨x, g, hg, rfl⟩
    exact h x g hg

/-- **The least model is a model** of the grammar's theory. -/
theorem leastModel_sat (A : Attr α) (P : N → List (Sym N α)) :
    ∀ φ ∈ prodAxioms P, (room A N).Sat (leastModel ⟨A, P⟩) φ := by
  refine (sat_prodAxioms_iff A P _).mpr fun x g hg => ?_
  have hint : interp A (leastModel ⟨A, P⟩).rel g = denote ⟨A, P⟩ g :=
    interp_leastModel ⟨A, P⟩ g
  have hnt : denote ⟨A, P⟩ (.nt x) = supList ((P x).map (denote ⟨A, P⟩)) := denote_nt _ x
  intro bs a hd
  show denote ⟨A, P⟩ (.nt x) bs a
  rw [hnt, supList_apply]
  exact ⟨denote ⟨A, P⟩ g, List.mem_map_of_mem hg, hint ▸ hd⟩

/-- In a model of the theory, one unfolding step of the grammar stays inside the model's
interpretation of each symbol. -/
theorem step_le_interp (A : Attr α) (P : N → List (Sym N α)) (M : Model N α)
    (hM : ∀ x, ∀ g ∈ P x, interp A M.rel g ≤ M.rel x) :
    ∀ g, step ⟨A, P⟩ (interp A M.rel) g ≤ interp A M.rel g
  | .eps => le_rfl
  | .byte _ => le_rfl
  | .range _ _ => le_rfl
  | .bytes _ => le_rfl
  | .nt x => by
      intro bs a h
      obtain ⟨E, hE, hEa⟩ := supList_apply.mp h
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
      exact hM x g hg bs a hEa
  | .seq gs => le_of_eq (congrArg (appendAll A) (interps_eq_map A M.rel gs).symm)
  | .alt gs => le_of_eq (congrArg supList (interps_eq_map A M.rel gs).symm)
  | .star _ => le_rfl
  | .plus _ => le_rfl
  | .opt _ => le_rfl
  | .count _ _ => le_rfl
  | .attr _ _ => le_rfl

/-- Every derivation of the grammar is a derivation in every model of its theory. -/
theorem denote_le_interp (A : Attr α) (P : N → List (Sym N α)) (M : Model N α)
    (hM : ∀ φ ∈ prodAxioms P, (room A N).Sat M φ) (g : Sym N α) :
    denote ⟨A, P⟩ g ≤ interp A M.rel g :=
  denote_le_of_step _ (step_le_interp A P M ((sat_prodAxioms_iff A P M).mp hM)) g

/-- **The least model lies below every model** of the grammar's theory. -/
theorem leastModel_le (A : Attr α) (P : N → List (Sym N α)) (M : Model N α)
    (hM : ∀ φ ∈ prodAxioms P, (room A N).Sat M φ) (x : N) :
    (leastModel ⟨A, P⟩).rel x ≤ M.rel x :=
  denote_le_interp A P M hM (.nt x)

/-- **Derivability is semantic consequence**: the theory of a grammar entails "`g` derives `bs`
with an attribute satisfying `Q`" iff the grammar's denotation says so. -/
theorem entails_derives_iff (A : Attr α) (P : N → List (Sym N α)) (g : Sym N α) (bs : Bytes)
    (Q : α → Prop) :
    (room A N).Entails (prodAxioms P) (.derives g bs Q) ↔ ∃ a, denote ⟨A, P⟩ g bs a ∧ Q a := by
  constructor
  · intro h
    obtain ⟨a, ha, hQ⟩ := h (leastModel ⟨A, P⟩) (leastModel_sat A P)
    have hint : interp A (leastModel ⟨A, P⟩).rel g = denote ⟨A, P⟩ g :=
      interp_leastModel ⟨A, P⟩ g
    exact ⟨a, hint ▸ ha, hQ⟩
  · rintro ⟨a, ha, hQ⟩ M hM
    exact ⟨a, denote_le_interp A P M hM g bs a ha, hQ⟩

/-- A nonterminal's derivations, as consequences: the least-model reading of `entails_derives_iff`
at `.nt x`. -/
theorem entails_derives_nt_iff (A : Attr α) (P : N → List (Sym N α)) (x : N) (bs : Bytes)
    (Q : α → Prop) :
    (room A N).Entails (prodAxioms P) (.derives (.nt x) bs Q) ↔
      ∃ a, (leastModel ⟨A, P⟩).rel x bs a ∧ Q a :=
  entails_derives_iff A P (.nt x) bs Q

/-! ## Consequence between theories -/

/-- More axioms, more consequences. -/
theorem entails_mono {A : Attr α} {Γ Δ : Set (Sen N α)} (h : Γ ⊆ Δ) {φ : Sen N α}
    (hφ : (room A N).Entails Γ φ) : (room A N).Entails Δ φ :=
  fun M hM => hφ M fun ψ hψ => hM ψ (h hψ)

/-- A fragment of a grammar's theory is contained in it. -/
theorem prodAxiomsWhere_subset (p : N → Prop) (P : N → List (Sym N α)) :
    prodAxiomsWhere p P ⊆ prodAxioms P := by
  rintro φ ⟨x, g, -, hg, rfl⟩
  exact ⟨x, g, hg, rfl⟩

/-- If `Γ` entails `φ` and `Δ` does not, then `Δ` does not entail all of `Γ`: there is no theory
morphism from `Γ` to `Δ` along the identity. -/
theorem not_entailsAll_of_separates {A : Attr α} {Γ Δ : Set (Sen N α)} {φ : Sen N α}
    (hΓ : (room A N).Entails Γ φ) (hΔ : ¬ (room A N).Entails Δ φ) :
    ¬ ∀ ψ ∈ Γ, (room A N).Entails Δ ψ :=
  fun h => hΔ fun M hM => hΓ M fun ψ hψ => h ψ hψ M hM

/-! ## Renamings of grammars are theory morphisms -/

/-- A declaration-preserving renaming that sends every production of `P` to a production of `P'`
is a (syntactic) presentation morphism between the two grammar theories. -/
def presentationHomOfRename {D : Type} {A : Attr α} {S S' : Sig D} (σ : S ⟶ S')
    {P : S.N → List (Sym S.N α)} {P' : S'.N → List (Sym S'.N α)}
    (h : ∀ x, ∀ g ∈ P x, renameSym σ.map g ∈ P' (σ.map x)) :
    presentation A S P ⟶ presentation A S' P' where
  sig := σ
  mapsTo := by
    rintro φ ⟨x, g, hg, rfl⟩
    exact ⟨σ.map x, renameSym σ.map g, h x g hg, rfl⟩

/-- Along such a renaming, consequences of the source grammar are consequences of the target
grammar, translated. -/
theorem entails_rename {A : Attr α} {N' : Type} (f : N → N') {P : N → List (Sym N α)}
    {P' : N' → List (Sym N' α)} (h : ∀ x, ∀ g ∈ P x, renameSym f g ∈ P' (f x)) {φ : Sen N α}
    (hφ : (room A N).Entails (prodAxioms P) φ) :
    (room A N').Entails (prodAxioms P') (φ.rename f) := by
  intro M hM
  have hred : ∀ ψ ∈ prodAxioms P, (room A N).Sat ((Model.reduct f).obj M) ψ := by
    rintro ψ ⟨x, g, hg, rfl⟩
    exact (Sen.holds_rename A M.rel f (.prod x g)).mp (hM _ ⟨f x, renameSym f g, h x g hg, rfl⟩)
  exact (Sen.holds_rename A M.rel f φ).mpr (hφ _ hred)

end Silmaril.Wasm.SpecTec.GrammarInst
