module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Least

/-!
# Closed fragments of a grammar theory

A set `R` of nonterminals is **closed** under a production table `P` when every production of a
nonterminal in `R` mentions only nonterminals in `R` (`ClosedUnder`). If `R` is contained in the
nonterminals a fragment `prodAxiomsWhere p P` keeps, then the fragment has the same least model
as the whole theory on `R` (`leastModel_restrict_eq`). So it has the same consequences about
symbols over `R` (`entails_fragment_iff`). The whole theory is then a conservative extension of
the fragment on `R`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec.Grammar

variable {N α : Type}

mutual

/-- Every nonterminal the symbol mentions is in `R`. -/
def SymIn (R : N → Prop) : Sym N α → Prop
  | .eps => True
  | .byte _ => True
  | .range _ _ => True
  | .bytes _ => True
  | .nt x => R x
  | .seq gs => SymsIn R gs
  | .alt gs => SymsIn R gs
  | .star g => SymIn R g
  | .plus g => SymIn R g
  | .opt g => SymIn R g
  | .count g _ => SymIn R g
  | .attr _ g => SymIn R g

/-- `SymIn` on lists. -/
def SymsIn (R : N → Prop) : List (Sym N α) → Prop
  | [] => True
  | g :: gs => SymIn R g ∧ SymsIn R gs

end

/-- `R` is closed under `P`: the productions of a nonterminal in `R` mention only `R`. -/
def ClosedUnder (R : N → Prop) (P : N → List (Sym N α)) : Prop :=
  ∀ x, R x → ∀ g ∈ P x, SymIn R g

mutual

/-- Interpretation only reads the nonterminals a symbol mentions. -/
theorem interp_congr (A : Attr α) {R : N → Prop} {I J : N → EncRel Bytes α}
    (h : ∀ x, R x → I x = J x) : ∀ g : Sym N α, SymIn R g → interp A I g = interp A J g
  | .eps, _ => rfl
  | .byte _, _ => rfl
  | .range _ _, _ => rfl
  | .bytes _, _ => rfl
  | .nt x, hx => h x hx
  | .seq gs, hg => congrArg (appendAll A) (interps_congr A h gs hg)
  | .alt gs, hg => congrArg supList (interps_congr A h gs hg)
  | .star g, hg => congrArg (kleene A) (interp_congr A h g hg)
  | .plus g, hg => congrArg (fun E => appendRel A E (kleene A E)) (interp_congr A h g hg)
  | .opt g, hg => congrArg (epsRel A.nil ⊔ ·) (interp_congr A h g hg)
  | .count g k, hg => congrArg (powRel A · k) (interp_congr A h g hg)
  | .attr f g, hg => congrArg (EncRel.mapPartial f) (interp_congr A h g hg)

/-- `interp_congr` on lists. -/
theorem interps_congr (A : Attr α) {R : N → Prop} {I J : N → EncRel Bytes α}
    (h : ∀ x, R x → I x = J x) : ∀ gs : List (Sym N α), SymsIn R gs →
      interps A I gs = interps A J gs
  | [], _ => rfl
  | g :: gs, ⟨hg, hgs⟩ => congrArg₂ List.cons (interp_congr A h g hg) (interps_congr A h gs hgs)

end

/-- The production table of a fragment: the productions of the nonterminals satisfying `p`. -/
noncomputable def restrictProds (p : N → Prop) (P : N → List (Sym N α)) : N → List (Sym N α) := by
  classical
  exact fun x => if p x then P x else []

theorem mem_restrictProds {p : N → Prop} {P : N → List (Sym N α)} {x : N} {g : Sym N α} :
    g ∈ restrictProds p P x ↔ p x ∧ g ∈ P x := by
  classical
  unfold restrictProds
  by_cases hx : p x
  · simp only [hx, ite_true, true_and]
  · simp only [hx, ite_false, false_and, List.not_mem_nil]

/-- A fragment is the theory of the restricted production table. -/
theorem prodAxiomsWhere_eq (p : N → Prop) (P : N → List (Sym N α)) :
    prodAxiomsWhere p P = prodAxioms (restrictProds p P) := by
  ext φ
  constructor
  · rintro ⟨x, g, hx, hg, rfl⟩
    exact ⟨x, g, mem_restrictProds.mpr ⟨hx, hg⟩, rfl⟩
  · rintro ⟨x, g, hg, rfl⟩
    obtain ⟨hx, hg'⟩ := mem_restrictProds.mp hg
    exact ⟨x, g, hx, hg', rfl⟩

/-- The model that agrees with the fragment's least model on `R` and is everything elsewhere. -/
noncomputable def extendTop (R : N → Prop) (M : Model N α) : Model N α := by
  classical
  exact ⟨fun x => if R x then M.rel x else ⊤⟩

theorem extendTop_of_mem {R : N → Prop} (M : Model N α) {x : N} (hx : R x) :
    (extendTop R M).rel x = M.rel x := by
  classical
  simp only [extendTop, hx, ite_true]

/-- If `R` is closed, extending the fragment's least model by `⊤` outside `R` gives a model of the
whole theory. -/
theorem extendTop_sat (A : Attr α) {R p : N → Prop} {P : N → List (Sym N α)}
    (hR : ClosedUnder R P) (hp : ∀ x, R x → p x) :
    ∀ φ ∈ prodAxioms P, (room A N).Sat (extendTop R (leastModel ⟨A, restrictProds p P⟩)) φ := by
  classical
  refine (sat_prodAxioms_iff A P _).mpr fun x g hg => ?_
  by_cases hx : R x
  · have hcongr : interp A (extendTop R (leastModel ⟨A, restrictProds p P⟩)).rel g =
        interp A (leastModel ⟨A, restrictProds p P⟩).rel g :=
      interp_congr A (fun y hy => extendTop_of_mem _ hy) g (hR x hx g hg)
    have hsat : interp A (leastModel ⟨A, restrictProds p P⟩).rel g ≤
        (leastModel ⟨A, restrictProds p P⟩).rel x :=
      (sat_prodAxioms_iff A _ _).mp (leastModel_sat A _) x g
        (mem_restrictProds.mpr ⟨hp x hx, hg⟩)
    rw [hcongr, extendTop_of_mem _ hx]
    exact hsat
  · show _ ≤ (if R x then _ else ⊤)
    simp only [hx, ite_false]
    exact le_top

/-- **A closed fragment has the whole theory's least model on its nonterminals.** -/
theorem leastModel_restrict_eq (A : Attr α) {R p : N → Prop} {P : N → List (Sym N α)}
    (hR : ClosedUnder R P) (hp : ∀ x, R x → p x) {x : N} (hx : R x) :
    (leastModel ⟨A, restrictProds p P⟩).rel x = (leastModel ⟨A, P⟩).rel x := by
  apply le_antisymm
  · refine leastModel_le A _ (leastModel ⟨A, P⟩) ?_ x
    intro φ hφ
    rw [← prodAxiomsWhere_eq] at hφ
    exact leastModel_sat A P φ (prodAxiomsWhere_subset p P hφ)
  · have h := leastModel_le A P _ (extendTop_sat A hR hp) x
    rwa [extendTop_of_mem _ hx] at h

/-- **Conservativity**: about a symbol over a closed `R`, the fragment and the whole theory have
the same consequences. -/
theorem entails_fragment_iff (A : Attr α) {R p : N → Prop} {P : N → List (Sym N α)}
    (hR : ClosedUnder R P) (hp : ∀ x, R x → p x) {g : Sym N α} (hg : SymIn R g) (bs : Bytes)
    (Q : α → Prop) :
    (room A N).Entails (prodAxiomsWhere p P) (.derives g bs Q) ↔
      (room A N).Entails (prodAxioms P) (.derives g bs Q) := by
  have hrel : interp A (leastModel ⟨A, restrictProds p P⟩).rel g =
      interp A (leastModel ⟨A, P⟩).rel g :=
    interp_congr A (fun y hy => leastModel_restrict_eq A hR hp hy) g hg
  rw [prodAxiomsWhere_eq, entails_derives_iff, entails_derives_iff,
    ← interp_leastModel ⟨A, restrictProds p P⟩, ← interp_leastModel ⟨A, P⟩]
  show (∃ a, interp A (leastModel ⟨A, restrictProds p P⟩).rel g bs a ∧ Q a) ↔
    ∃ a, interp A (leastModel ⟨A, P⟩).rel g bs a ∧ Q a
  rw [hrel]

end Silmaril.Wasm.SpecTec.GrammarInst
