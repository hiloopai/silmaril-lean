module

public import Silmaril.Wasm.Unified.Component.Open.Defs
public import Silmaril.Wasm.Unified.Component.Inst.Thms

/-!
# Core modules with imports: the open component institution `cinstO`

* `den_eq_denC`, `obs_eq_obsC`: the closed semantics is the generic one at `coreSem M`.
* `coreSemO_reduct`: the core semantics of the reduct of an open model is the pulled-back one;
  `denO_reduct`, `obsO_reduct`, and **`osat_map_iff`**: the satisfaction condition of
  `cinstO` (signatures `CSig`, sentences `CSen`, models `OModel`).
* **`coreSemO_toOpen`**: a closed model seen as an open one has the same core semantics
  (simulations in both directions between `coreRedO M.toOpen m` and `coreRed M m`), hence
  `osat_toOpen`: the same sentences hold.
* **`ofClosed : Inst.CoHom cinstO cinst`**: identity on signatures and sentences, closed models
  to open ones; `entails_of_open`: a consequence in `cinstO` (over all open models) is a
  consequence in `cinst`. The converse fails in general: open models can call imports.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm.Atlas Silmaril.Wasm.Resource
open Silmaril.Wasm.Component Silmaril.Wasm.Unified
open Silmaril.Games (Strategy Prog Reduction)

variable {S S' : FSig}

theorem den_eq_denC (M : PModel S) (x : CProg S) : den M x = denC (coreSem M) x := by
  cases x <;> rfl

theorem obs_eq_obsC (M : PModel S) : obs M = obsC (coreSem M) := by
  funext x
  rcases x with ⟨x, j, p⟩
  cases x <;> rfl

/-! ## Reducts -/

theorem coreRedO_reduct (σ : S ⟶ S') (M : OModel S') (m : UMod S) :
    coreRedO (M.reduct σ) m = coreRedO M (m.map σ) := by
  have h : ∀ (j : Nat) (p : Payload),
      (M.reduct σ).obs (m.code j, p) = M.obs ((m.map σ).code j, p) :=
    fun j p => Model.obs_reduct σ M (m.code j) p
  unfold coreRedO stepO
  simp only [h]
  rfl

theorem coreSemO_reduct (σ : S ⟶ S') (M : OModel S') :
    coreSemO (M.reduct σ) = pullC (coreSemO M) σ := by
  unfold coreSemO pullC
  simp only [coreRedO_reduct]
  rfl

theorem denC_pull (C : CoreSem (UMod S')) (σ : S ⟶ S') (x : CProg S) :
    denC (pullC C σ) x = denC C (x.map σ) := by
  cases x with
  | core m => rfl
  | comp c => rw [denC, CProg.map, denC, denU_mapComp]

theorem obsC_pull (C : CoreSem (UMod S')) (σ : S ⟶ S') (x : CProg S) (j : Nat) (p : Payload) :
    obsC (pullC C σ) (x, j, p) = obsC C (x.map σ, j, p) := by
  cases x with
  | core m => rfl
  | comp c => rw [obsC, CProg.map, obsC, denU_mapComp]

theorem denO_reduct (σ : S ⟶ S') (M : OModel S') (x : CProg S) :
    denO (M.reduct σ) x = denO M (x.map σ) := by
  rw [denO, coreSemO_reduct, denC_pull]

theorem obsO_reduct (σ : S ⟶ S') (M : OModel S') (x : CProg S) (j : Nat) (p : Payload) :
    obsO (M.reduct σ) (x, j, p) = obsO M (x.map σ, j, p) := by
  rw [obsO, coreSemO_reduct, obsC_pull]

/-- **The satisfaction condition** of the open component institution. -/
theorem osat_map_iff {T T' : CSig} (f : T ⟶ T') (M : OModel T'.1) (φ : CSen T) :
    CSatO M (φ.map f) ↔ CSatO (M.reduct f.1) φ := by
  induction φ with
  | beh φ =>
    have h : ∀ x : CCall T, obsO M ((CCall.map f x).1.1, (CCall.map f x).2) =
        obsO (M.reduct f.1) (x.1.1, x.2) := fun x => (obsO_reduct f.1 M x.1.1 x.2.1 x.2.2).symm
    exact (BSen.sat_rename _ _ φ).trans (BSen.sat_congr h φ)
  | res x d hd r =>
    show (∀ s ∈ denO M (x.1.map f.1), _) ↔ ∀ s ∈ denO (M.reduct f.1) x.1, _
    rw [denO_reduct]
  | and φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

/-- The room of a signature. -/
def oroom (T : CSig) : Room.{0, 0, 1} := ⟨CSen T, Cat.of (OModel T.1), CSatO⟩

/-- The corridor of a signature morphism. -/
def ocorridor {T T' : CSig} (f : T ⟶ T') : oroom T ⟶ oroom T' :=
  ⟨CSen.map f, reductF f.1, fun M φ => osat_map_iff f M φ⟩

/-- **The open component institution**, as a functor into rooms. -/
def cinstitutionO : CSig ⥤ Room.{0, 0, 1} where
  obj := oroom
  map := ocorridor
  map_id _ := Room.hom_ext (funext fun φ => CSen.map_id φ)
    (CategoryTheory.Functor.ext (fun M => Model.reduct_id M) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (funext fun φ => CSen.map_comp f g φ)
    (CategoryTheory.Functor.ext (fun M => Model.reduct_comp f.1 g.1 M) (fun _ _ _ => rfl))

/-- The open component institution, bundled. -/
def cinstO : Inst.{0, 0, 0, 0, 1} := ⟨CSig, cinstitutionO⟩

/-! ## Closed models are open models -/

theorem mem_toOpen_obs (M : PModel S) (c : S.Code) (p : Payload) (P : Prog sigU (Option Payload)) :
    P ∈ M.toOpen.obs (c, p) ↔ ∃ r ∈ M.obs (c, p), P = .pure r :=
  ⟨fun ⟨hok, r, hr, he⟩ => ⟨r, ⟨hok, hr⟩, he.symm⟩, fun ⟨r, ⟨hok, hr⟩, he⟩ => ⟨hok, r, hr, he.symm⟩⟩

theorem stepO_start {M : OModel S} {m : UMod S} {n : Nat} {q : Nat × Payload} {c' : OConf}
    (h : stepO M m n q .start c') : ∃ P, c' = .run P ∧ P ∈ M.obs (m.code q.1, q.2) := by
  cases c' with
  | start => exact (h : False).elim
  | run P => exact ⟨P, rfl, h⟩

theorem not_stepO_pure {M : OModel S} {m : UMod S} {n : Nat} {q : Nat × Payload}
    {r : Option Payload} {c' : OConf} : ¬ stepO M m n q (.run (.pure r)) c' := by
  cases c' <;> exact fun h => h

theorem not_callO_pure {n : Nat} {r : Option Payload} {i : Fin n} {a : Payload}
    {k : Option Payload → OConf} : ¬ callO n (.run (.pure r)) i a k := by
  rintro ⟨k', hk', -⟩
  cases hk'

/-- The open run of a closed model simulates the closed one. -/
def simOC (M : PModel S) (m : UMod S) : (coreRedO M.toOpen m).Simulation (coreRed M m) where
  rel {q} c _ := c = .start ∨ ∃ r, c = .run (.pure r) ∧ r ∈ M.obs (m.code q.1.val, q.2)
  start _ := .inl rfl
  step := by
    rintro q c c' d (rfl | ⟨r, rfl, -⟩) hs
    · obtain ⟨P, rfl, hP⟩ := stepO_start hs
      obtain ⟨r, hr, rfl⟩ := (mem_toOpen_obs M _ _ P).1 hP
      exact ⟨d, .refl, .inr ⟨r, rfl, hr⟩⟩
    · have hs' : stepO M.toOpen m (CoreModule.imports m).length (q.1.val, q.2) (.run (.pure r)) c' :=
        hs
      exact (not_stepO_pure hs').elim
  call := by
    rintro q c d m' k (rfl | ⟨r, rfl, -⟩) hc
    · obtain ⟨k', hk', -⟩ := hc
      cases hk'
    · exact absurd hc not_callO_pure
  done := by
    rintro q c d r (rfl | ⟨r', rfl, hr'⟩) hd
    · cases hd
    · have hr : r' = r := by cases hd; rfl
      exact ⟨d, .refl, hr ▸ hr'⟩

/-- The closed run is simulated by the open one (one choice step before answering). -/
def simCO (M : PModel S) (m : UMod S) : (coreRed M m).Simulation (coreRedO M.toOpen m) where
  rel _ c := c = .start
  start _ := rfl
  step _ h := h.elim
  call _ h := h.elim
  done := by
    rintro q c d r rfl hd
    have hs : stepO M.toOpen m (CoreModule.imports m).length (q.1.val, q.2) .start
        (.run (.pure r)) := (mem_toOpen_obs M _ _ _).2 ⟨r, hd, rfl⟩
    exact ⟨.run (.pure r), .single hs, rfl⟩

/-- **A closed model has the same core semantics as an open one.** -/
theorem coreSemO_toOpen (M : PModel S) : coreSemO M.toOpen = coreSem M := by
  have h : ∀ m : UMod S, Strategy.ofReduction (coreRedO M.toOpen m) =
      Strategy.ofReduction (coreRed M m) := fun m =>
    le_antisymm (simOC M m).ofReduction_le (simCO M m).ofReduction_le
  unfold coreSemO coreSem
  simp only [h]

theorem denO_toOpen (M : PModel S) (x : CProg S) : denO M.toOpen x = den M x := by
  rw [denO, coreSemO_toOpen, den_eq_denC]

theorem obsO_toOpen (M : PModel S) : obsO M.toOpen = obs M := by
  rw [obsO, coreSemO_toOpen, obs_eq_obsC]

/-- A closed model satisfies a sentence iff it does as an open model. -/
theorem osat_toOpen {T : CSig} (M : PModel T.1) (φ : CSen T) : CSatO M.toOpen φ ↔ CSat M φ := by
  induction φ with
  | beh φ =>
    show φ.Sat (fun x => obsO M.toOpen (x.1.1, x.2)) ↔ φ.Sat (fun x => obs M (x.1.1, x.2))
    rw [obsO_toOpen]
  | res x d hd r =>
    show (∀ s ∈ denO M.toOpen x.1, _) ↔ ∀ s ∈ den M x.1, _
    rw [denO_toOpen]
  | and φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

/-- Closed models as open models, a functor. -/
def toOpenF (S : FSig) : PModel S ⥤ OModel S where
  obj := Model.toOpen
  map h := ⟨congrArg Model.toOpen h.down⟩

/-- The corridor of `ofClosed` at a signature. -/
def ofClosedCorridor (T : CSig) : cinstitutionO.obj T ⟶ cinstitution.obj T :=
  ⟨id, toOpenF T.1, fun M φ => (osat_toOpen M φ).symm⟩

/-- **Closed models are open models**: a comorphism `cinstO → cinst`, identity on signatures
and sentences. -/
def ofClosed : Inst.CoHom cinstO cinst where
  Φ := 𝟭 CSig
  ρ :=
    { app := ofClosedCorridor
      naturality := fun {_ _} _ => Room.hom_ext rfl
        (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)) }

/-- A consequence over all open models is a consequence over the closed ones. -/
theorem entails_of_open {T : CSig} {Γ : Set (CSen T)} {φ : CSen T}
    (h : (cinstitutionO.obj T).Entails Γ φ) : (cinstitution.obj T).Entails Γ φ :=
  fun M hΓ => (osat_toOpen M φ).1 (h M.toOpen fun ψ hψ => (osat_toOpen M ψ).2 (hΓ ψ hψ))

end Silmaril.Wasm.Unified.Component
