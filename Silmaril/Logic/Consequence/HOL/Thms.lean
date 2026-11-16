module

public import Silmaril.Logic.Consequence.HOL.Defs
public import Silmaril.Logic.Consequence.Institution.Thms
public import Silmaril.Logic.HOLLight.Soundness.Thms
import Silmaril.Proofs.Logic.Consequence.HOL.Basic
import Silmaril.Proofs.Logic.Consequence.HOL.Kernel

/-!
# HOL propositions as consequence systems: laws

**Agreement with HOL Light and the institution.**

* `seq_iff_entails`: `seq S Γ p` iff `HOLLight.Entails M Γ p` in every model `M`.
* `seq_iff_valid_toSeq`: iff the sentence `Γ ⊢ p` is valid in the HOL institution
  (`Room.Entails ∅`). `globalSeq_iff_roomSeq`: model-wise consequence is `roomSeq` of the room on
  the hypothesis-free sentences `⊢ p`.
* `logic_listSys_le_roomSeq`: at the level of sequent *sentences*, HOL derivability
  (`Metatheory.HOL.logic`) is below the institution's `roomSeq`.
* `derives_le_seq`: the HOL Light kernel is sound for `seq` (from `HOLLight.Derives.sound`; pure
  logic, no object theory). `derives_le_globalSeq`: with an object theory `Δ`, closed theorems
  are model-wise consequences of `Δ` (not point-wise ones: the kernel instantiates axioms).
* `gentzen_iff_seq_disjList`: `Γ ⊢ Δ` in `gentzen` iff `Γ ⊢ ⋁Δ` in `seq`, with HOL's defined
  disjunction. This is the precise sense in which `gentzen` is the classical (LK) reading.

**Derivability.** `kernelFrom_closed`, `kernelFrom_substitutive_ty`,
`kernelFrom_substitutive_free`: the kernel as a consequence system satisfies identity, weakening,
cut and substitution. `kernel_le_seq`: pure HOL is sound for `seq`. Completeness is not claimed.

**Substitution laws.** `seq_substitutive_ty`, `seq_substitutive_free`: `Structural.Substitutive`
forms of `seq_tySubst` and `seq_freeSubst`.

**Closure (each a theorem about `seq` and `gentzen`).**

| operation | `seq` (`HOLProp* ⊢ HOLProp`) | `gentzen` (`HOLProp* ⊢ HOLProp*`) |
|---|---|---|
| reflexivity, weakening along `⊆`, cut | `seq_closed` (`Structural.tarskiRules`: multi-cut) | `gentzen_closed` (`Gentzen.defaultRules`) |
| exchange, contraction | `seq_exchange`, `seq_contraction` | from `⊆`-weakening |
| signature extension `S ≤ T` | `seq_map` | `gentzen_map` |
| type instantiation (`INST_TYPE`) | `seq_tySubst` | `gentzen_tySubst` |
| term instantiation (`INST`) | `seq_freeSubst` | `gentzen_freeSubst` |

The same structural closure holds for `globalSeq`/`globalGentzen` (`globalSeq_closed`,
`globalGentzen_closed`), and `seq ≤ globalSeq` (`seq_le_globalSeq`). `gentzen_single`: the
singleton-succedent part of `gentzen` is `seq`.
-/

@[expose] public section

namespace Silmaril.Consequence.HOL

open Silmaril.Logic.HOLLight Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Metatheory (HolSig)

universe u

variable {S T : HolSig}

/-! ## Agreement -/

theorem seq_iff_entails (Γ : List (HOLProp S)) (p : HOLProp S) :
    seq.{u} S Γ p ↔ ∀ M : Model.{u} S.sig, Entails M (Γ.map Subtype.val).toFinset p.1 :=
  Proofs.Logic.Consequence.HOL.seq_iff_entails Γ p

theorem seq_iff_valid_toSeq (Γ : List (HOLProp S)) (p : HOLProp S) :
    seq.{u} S Γ p ↔ (Metatheory.HOL.room.{u} S).Entails ∅ (toSeq Γ p) :=
  (seq_iff_entails Γ p).trans ⟨fun h M _ => h M.as, fun h M => h ⟨M⟩ fun _ h => h.elim⟩

theorem globalSeq_iff_roomSeq (Γ : List (HOLProp S)) (p : HOLProp S) :
    globalSeq.{u} S Γ p ↔ roomSeq (Metatheory.HOL.room.{u} S) (Γ.map closedSen) (closedSen p) :=
  Proofs.Logic.Consequence.HOL.globalSeq_iff_roomSeq Γ p

/-- The kernel derives only `seq`-consequences. -/
theorem derives_le_seq {Γ : List (HOLProp S)} {p : HOLProp S}
    (d : Derives S.sig [] (Γ.map Subtype.val).toFinset p.1) : seq.{u} S Γ p :=
  (seq_iff_entails Γ p).2 fun M => d.sound M fun _ h => nomatch h

/-- **Sequent level**: HOL derivability between sentences `H ⊢ p` (`HOL.logic`) is below the
institution's semantic consequence, from `HOLLight.Derives.sound`. -/
theorem logic_listSys_le_roomSeq (S : HolSig) :
    LogicalSystem.listSys Metatheory.HOL.logic.{u} S ≤ roomSeq (Metatheory.HOL.logic.{u}.I.obj S) :=
  listSys_le_roomSeq Metatheory.HOL.logic_sound S

/-- **Kernel with axioms is sound for model-wise consequence**: a closed theorem of the axioms
`Δ` is valid in every model where `Δ` is valid. (Not for `seq`: the kernel instantiates axioms,
which a point-wise hypothesis does not license.) -/
theorem derives_le_globalSeq {Δ : List (HOLProp S)} {p : HOLProp S}
    (d : Derives S.sig (Δ.map Subtype.val) ∅ p.1) : globalSeq.{u} S Δ p :=
  Proofs.Logic.Consequence.HOL.derives_le_globalSeq d

/-- **Classical collapse**: a Gentzen sequent is the single-conclusion sequent of the disjunction
of its succedents (HOL's defined `∨`, `⊥` for an empty succedent). -/
theorem gentzen_iff_seq_disjList (Γ Δ : List (HOLProp S)) :
    gentzen.{u} S Γ Δ ↔ seq.{u} S Γ (HOLProp.disjList Δ) :=
  Proofs.Logic.Consequence.HOL.gentzen_iff_seq_disjList Γ Δ

/-! ## Structural closure -/

theorem seq_closed : Structural.Closed Structural.tarskiRules (seq.{u} S) :=
  entails_localSat_closed _

theorem seq_exchange : Structural.Exchange (seq.{u} S) :=
  Structural.WeakSubset.exchange seq_closed.weak

theorem seq_contraction : Structural.Contraction (seq.{u} S) :=
  Structural.WeakSubset.contraction seq_closed.weak

theorem gentzen_closed : Gentzen.Closed Gentzen.defaultRules (gentzen.{u} S) :=
  valid_localSat_closed _

theorem gentzen_single : (gentzen.{u} S).single = seq.{u} S :=
  funext fun _ => funext fun _ => propext Gentzen.entails_iff_valid.symm

theorem globalSeq_closed : Structural.Closed Structural.tarskiRules (globalSeq.{u} S) :=
  Refutation.entails_closed

theorem globalGentzen_closed : Gentzen.Closed Gentzen.defaultRules (globalGentzen.{u} S) :=
  Gentzen.valid_closed

theorem seq_le_globalSeq : seq.{u} S ≤ globalSeq.{u} S := entails_localSat_le_validIn _

/-! ## Signature extension -/

theorem gentzen_map (h : S ≤ T) {Γ Δ : List (HOLProp S)} (hv : gentzen.{u} S Γ Δ) :
    gentzen.{u} T (Γ.map (HOLProp.map h)) (Δ.map (HOLProp.map h)) :=
  valid_map_of_sat (HOLProp.map h) (fun x => ⟨Metatheory.HOL.Model.reduct h x.1, x.2⟩)
    (fun x q => (Metatheory.HOL.holds_reduct_iff h x.1 x.2.1 x.2.2 q.2).symm) hv

theorem seq_map (h : S ≤ T) {Γ : List (HOLProp S)} {p : HOLProp S} (hs : seq.{u} S Γ p) :
    seq.{u} T (Γ.map (HOLProp.map h)) (HOLProp.map h p) :=
  entails_map_of_sat (HOLProp.map h) (fun x => ⟨Metatheory.HOL.Model.reduct h x.1, x.2⟩)
    (fun x q => (Metatheory.HOL.holds_reduct_iff h x.1 x.2.1 x.2.2 q.2).symm) hs

/-! ## Instantiation -/

section TySubst

variable (σ : Nat → Ty) (hσ : ∀ i, (σ i).WellFormed S.sig.tyOps)

theorem gentzen_tySubst {Γ Δ : List (HOLProp S)} (hv : gentzen.{u} S Γ Δ) :
    gentzen.{u} S (Γ.map (HOLProp.tySubst σ hσ)) (Δ.map (HOLProp.tySubst σ hσ)) :=
  valid_map_of_sat (HOLProp.tySubst σ hσ)
    (fun x => ⟨x.1, TypeSubstitution.valuation x.1 x.2.1 σ, TypeSubstitution.freeEnv σ x.2.2⟩)
    (fun _ q => Holds.tySubst_iff q.2 σ hσ) hv

theorem seq_tySubst {Γ : List (HOLProp S)} {p : HOLProp S} (hs : seq.{u} S Γ p) :
    seq.{u} S (Γ.map (HOLProp.tySubst σ hσ)) (HOLProp.tySubst σ hσ p) :=
  entails_map_of_sat (HOLProp.tySubst σ hσ)
    (fun x => ⟨x.1, TypeSubstitution.valuation x.1 x.2.1 σ, TypeSubstitution.freeEnv σ x.2.2⟩)
    (fun _ q => Holds.tySubst_iff q.2 σ hσ) hs

end TySubst

section FreeSubst

variable (σ : Nat → Ty → Tm) (hσ : ∀ n B, B.WellFormed S.sig.tyOps → HasType S.sig [] (σ n B) B)

theorem gentzen_freeSubst {Γ Δ : List (HOLProp S)} (hv : gentzen.{u} S Γ Δ) :
    gentzen.{u} S (Γ.map (HOLProp.freeSubst σ hσ)) (Δ.map (HOLProp.freeSubst σ hσ)) :=
  valid_map_of_sat (HOLProp.freeSubst σ hσ)
    (fun x => ⟨x.1, x.2.1, Proofs.Logic.Consequence.HOL.substEnv x.1 x.2.1 x.2.2 σ hσ⟩)
    (fun x q => Holds.freeSubst_iff q.2 σ _
      (Proofs.Logic.Consequence.HOL.eval_substEnv x.1 x.2.1 x.2.2 σ hσ)) hv

theorem seq_freeSubst {Γ : List (HOLProp S)} {p : HOLProp S} (hs : seq.{u} S Γ p) :
    seq.{u} S (Γ.map (HOLProp.freeSubst σ hσ)) (HOLProp.freeSubst σ hσ p) :=
  entails_map_of_sat (HOLProp.freeSubst σ hσ)
    (fun x => ⟨x.1, x.2.1, Proofs.Logic.Consequence.HOL.substEnv x.1 x.2.1 x.2.2 σ hσ⟩)
    (fun x q => Holds.freeSubst_iff q.2 σ _
      (Proofs.Logic.Consequence.HOL.eval_substEnv x.1 x.2.1 x.2.2 σ hσ)) hs

end FreeSubst

/-! ## Substitution laws -/

/-- `seq` is substitutive along well-formed type instantiations (`INST_TYPE`). -/
theorem seq_substitutive_ty :
    Structural.Substitutive
      (fun σ : {σ : Nat → Ty // ∀ i, (σ i).WellFormed S.sig.tyOps} => HOLProp.tySubst σ.1 σ.2)
      (seq.{u} S) :=
  fun σ _ _ h => seq_tySubst σ.1 σ.2 h

/-- `seq` is substitutive along type-respecting term instantiations (`INST`). -/
theorem seq_substitutive_free :
    Structural.Substitutive
      (fun σ : {σ : Nat → Ty → Tm //
          ∀ n B, B.WellFormed S.sig.tyOps → HasType S.sig [] (σ n B) B} =>
        HOLProp.freeSubst σ.1 σ.2)
      (seq.{u} S) :=
  fun σ _ _ h => seq_freeSubst σ.1 σ.2 h

/-! ## The kernel -/

/-- Kernel derivability satisfies identity, weakening and cut. -/
theorem kernelFrom_closed (Δ : Theory) :
    Structural.Closed Structural.tarskiRules (kernelFrom S Δ) :=
  Proofs.Logic.Consequence.HOL.kernelFrom_closed Δ

/-- Kernel derivability is substitutive along type instantiations (`INST_TYPE`). -/
theorem kernelFrom_substitutive_ty (Δ : Theory) :
    Structural.Substitutive
      (fun σ : {σ : Nat → Ty // ∀ i, (σ i).WellFormed S.sig.tyOps} => HOLProp.tySubst σ.1 σ.2)
      (kernelFrom S Δ) :=
  fun σ _ _ h => Proofs.Logic.Consequence.HOL.kernelFrom_tySubst Δ σ.1 σ.2 h

/-- Kernel derivability is substitutive along term instantiations (`INST`). -/
theorem kernelFrom_substitutive_free (Δ : Theory) :
    Structural.Substitutive
      (fun σ : {σ : Nat → Ty → Tm //
          ∀ n B, B.WellFormed S.sig.tyOps → HasType S.sig [] (σ n B) B} =>
        HOLProp.freeSubst σ.1 σ.2)
      (kernelFrom S Δ) :=
  fun σ _ _ h => Proofs.Logic.Consequence.HOL.kernelFrom_freeSubst Δ σ.1 σ.2 h

/-- **Soundness of pure HOL**: kernel derivability is below `seq`. -/
theorem kernel_le_seq : kernel S ≤ seq.{u} S := fun _ _ d => derives_le_seq d

end Silmaril.Consequence.HOL
