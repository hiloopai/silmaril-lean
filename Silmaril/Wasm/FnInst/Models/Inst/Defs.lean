module

public import Silmaril.Wasm.FnInst.Models.Base.Thms
public import Silmaril.Logic.Inst.Builders.Core.Defs

/-!
# The function-level equivalence institutions with three kinds of models

Built with the facade builder `Silmaril.Inst.Plain` (discrete model categories). All three share
signatures (`Sig L`: a module context and a focus function, morphisms embed contexts and map the
focus) and sentences (`Sen L n`: equations between candidate bodies for the focus, conjunction):

* `semInst S`: models (c), sets of environments (abstract behaviours of every function, imports
  and unknown functions included); satisfaction: the sentence holds in every environment;
* `bodyInst S`: models (a), partial modules containing the context (`PMod`), read through
  their denotation `PMod.den` into (c);
* `kInst sems`: models (b), a partial module and a choice `k` among a family of semantics
  `sems : K → FnSem L` over the same syntax.

Comorphisms (identity on signatures and sentences):

* `semToBody S : semInst S → bodyInst S`: models map by the denotation `PMod.den`;
* `kToBody sems k : kInst sems → bodyInst (sems k)`: a partial module is read in semantics `k`.

Theorems (`Thms`): validity agrees across the three (`valid_body_iff`, `valid_sem_iff`,
`valid_k_iff`), monotonicity in information (`sat_mono`) and the transfer of a sentence valid
at the least informative model along every signature morphism into every model (`transfer`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models

open CategoryTheory Silmaril.Inst

variable {L : FnSyntax}

/-- The plain presentation of the semantic-model institution (c). -/
def semPlain (S : FnSem L) : Plain (Sig L) where
  Sen T := Sen L T.n
  map σ φ := Sen.map (Sig.Hom.c σ).f φ
  map_id _ φ := Sen.map_id φ
  map_comp σ τ φ := Sen.map_comp (Sig.Hom.c σ).f (Sig.Hom.c τ).f φ
  Mod T := Set (Env S T.n)
  reduct σ E := semReduct S (Sig.Hom.c σ).f E
  reduct_id _ E := semReduct_id S E
  reduct_comp σ τ E := semReduct_comp S (Sig.Hom.c σ).f (Sig.Hom.c τ).f E
  Sat E φ := SemSat S E φ
  sat_map σ E φ := semSat_reduct_iff S (Sig.Hom.c σ).f E φ

/-- The institution with semantic models (c). -/
abbrev semInst (S : FnSem L) : Institution₀ := (semPlain S).toInst

/-- The plain presentation of the partial-body institution (a). -/
def bodyPlain (S : FnSem L) : Plain (Sig L) where
  Sen T := Sen L T.n
  map σ φ := Sen.map (Sig.Hom.c σ).f φ
  map_id _ φ := Sen.map_id φ
  map_comp σ τ φ := Sen.map_comp (Sig.Hom.c σ).f (Sig.Hom.c τ).f φ
  Mod T := PMod T
  reduct σ M := PMod.reduct σ M
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M φ := SemSat S (M.den S) φ
  sat_map σ M φ := by
    show SemSat S (M.den S) (Sen.map (Sig.Hom.c σ).f φ) ↔ SemSat S ((M.reduct σ).den S) φ
    rw [PMod.den_reduct]
    exact semSat_reduct_iff S _ _ φ

/-- The institution with partial bodies (a). -/
abbrev bodyInst (S : FnSem L) : Institution₀ := (bodyPlain S).toInst

/-- The plain presentation of the institution of bodies with a choice of semantics (b). -/
def kPlain {K : Type} (sems : K → FnSem L) : Plain (Sig L) where
  Sen T := Sen L T.n
  map σ φ := Sen.map (Sig.Hom.c σ).f φ
  map_id _ φ := Sen.map_id φ
  map_comp σ τ φ := Sen.map_comp (Sig.Hom.c σ).f (Sig.Hom.c τ).f φ
  Mod T := KMod sems T
  reduct σ M := ⟨M.k, M.m.reduct σ⟩
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M φ := SemSat (sems M.k) (M.m.den (sems M.k)) φ
  sat_map σ M φ := (bodyPlain (sems M.k)).sat_map σ M.m φ

/-- The institution of bodies with a choice of semantics (b). -/
abbrev kInst {K : Type} (sems : K → FnSem L) : Institution₀ := (kPlain sems).toInst

/-- The denotation as a comorphism (c) → (a): a partial module is read as its set of
environments. -/
def semToBody (S : FnSem L) : Comorphism (semInst S) (bodyInst S) :=
  Comorphism.ofPlain (P := semPlain S) (Q := bodyPlain S) (𝟭 _) (fun _ φ => φ)
    (fun _ M => M.den S) (fun _ _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun σ M => (PMod.den_reduct S σ M).symm)

/-- Reading a module of (b) in a fixed semantics `k`: a comorphism (b) → (a). -/
def kToBody {K : Type} (sems : K → FnSem L) (k : K) :
    Comorphism (kInst sems) (bodyInst (sems k)) :=
  Comorphism.ofPlain (P := kPlain sems) (Q := bodyPlain (sems k)) (𝟭 _) (fun _ φ => φ)
    (fun _ M => ⟨k, M⟩) (fun _ _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end Silmaril.Wasm.FnInst.Models
