module

public import Silmaril.Wasm.Tools.Gen.Sem.Defs
public import Silmaril.Wasm.Tools.Gen.Core.Thms
public import Silmaril.Wasm.Binaryen.Pipeline.Thms

/-!
# Optimisation stages as semantics-preserving mutators

* `coreEquiv_refl`, `coreEquiv_trans`, `coreEquiv_symm`: `CoreEquiv P H` is an equivalence;
* `optRun_valid`, `optRun_equiv`: on a valid module, `optRun stages` gives a valid module
  export-equivalent to it, at every profile (from `extraSelectedP`, the composite pass);
* `optSem P H : SemMutator ⟨Module, ModuleValid⟩ (CoreEquiv P H)`: seeded selections;
* `featSem P H S`: its restriction to the language of the feature set `S`, checked
  (`SemMutator.guarded`), so a `SemMutator (coreModel P H S).toLang (CoreEquiv P H)`
  (`coreSem`), for 1.0 and 3.0 (`v10Sem`, `v30Sem`);
* **`optRunIn_inFeat`**: the stage-by-stage run `optRunIn S` stays inside `S` (by
  construction: a stage whose output leaves `S` is skipped), with `optRunIn_valid` and
  `optRunIn_equiv`; `featSemIn P H S`, the semantics-preserving mutator built on it, needs no
  checker at all (validity in `S` and equivalence are proved for every output).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Sem

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Models Silmaril.Wasm.Binaryen.Pipeline
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Tools.Gen.Core
open Silmaril.Wasm.Numerics (Profile)

theorem coreEquiv_refl (P : Profile) (H : Type) (m : Module) : CoreEquiv P H m m :=
  Contract.equiv_refl Contract.Rel.eq m

theorem coreEquiv_trans {P : Profile} {H : Type} {a b c : Module} (h : CoreEquiv P H a b)
    (h' : CoreEquiv P H b c) : CoreEquiv P H a c :=
  Contract.equiv_trans Contract.Rel.eq h h'

theorem coreEquiv_symm {P : Profile} {H : Type} {a b : Module} (h : CoreEquiv P H a b) :
    CoreEquiv P H b a :=
  Contract.equiv_symm_of_symm (fun _ _ h => h.symm) h

/-- The composite pass of a selection. -/
def passOf (P : Profile) (H : Type) (stages : List ExtraStage) :
    ArbitraryProfile.EquivPass P (closedHost (H := H)) :=
  extraSelectedP P stages fun s _ => ExtraStage.anyProfile_all s

theorem passOf_run (P : Profile) (H : Type) (stages : List ExtraStage) (m : BModule) :
    (passOf P H stages).run m = extraSelectedRound stages m :=
  extraSelectedP_run P stages _ m

theorem lift_ok {m : Module} (hm : Validation.ModuleValid m) : (Exe.checkedLift m).1.Ok := by
  show ∃ t, Validation.ModuleOk (Exe.checkedLift m).1.lower t
  rw [Exe.checkedLift_lower]; exact hm

/-- **The stages keep validity.** -/
theorem optRun_valid (stages : List ExtraStage) {m : Module} (hm : Validation.ModuleValid m) :
    Validation.ModuleValid (optRun stages m) := by
  have h := (passOf Silmaril.Wasm.Numerics.Profile.spec Unit stages).inv_run (lift_ok hm)
  rw [passOf_run] at h
  exact h

/-- **The stages preserve the semantics**: export equivalence at every profile. -/
theorem optRun_equiv (P : Profile) (H : Type) (stages : List ExtraStage) {m : Module}
    (hm : Validation.ModuleValid m) : CoreEquiv P H (optRun stages m) m := by
  have h := (passOf P H stages).sound (lift_ok hm)
  rw [passOf_run] at h
  have h' : ExportEquiv (· = ·) P (closedHost (H := H)) (optRun stages m)
      (Exe.checkedLift m).1.lower := h
  rwa [Exe.checkedLift_lower] at h'

/-- **Seeded optimisation as a semantics-preserving mutator** of valid Core 3.0 modules. -/
def optSem (P : Profile) (H : Type) :
    SemMutator ⟨Module, Validation.ModuleValid⟩ (CoreEquiv P H) where
  run r m := optRun (Rand.run pickStages r) m
  valid _ _ hm := optRun_valid _ hm
  equiv _ _ hm := optRun_equiv P H _ hm

/-- **At a feature set**: checked (the input when the output leaves `S`). -/
def featSem (P : Profile) (H : Type) (S : FeatureSet) :
    SemMutator (featLang S).toLang (CoreEquiv P H) :=
  SemMutator.guarded (featLang S) (coreEquiv_refl P H) (optSem P H) fun _ h => h.1

/-- What `featSem` runs (the executables run this function without importing the proofs). -/
theorem featSem_run (P : Profile) (H : Type) (S : FeatureSet) (r : Rng) (m : Module) :
    (featSem P H S).run r m =
      if featCheck S (optRun (Rand.run pickStages r) m) then optRun (Rand.run pickStages r) m
      else m := rfl

/-- The semantics-preserving mutator of `coreModel P H S`. -/
def coreSem (P : Profile) (H : Type) (S : FeatureSet) :
    SemMutator (coreModel P H S).toLang (CoreEquiv P H) := featSem P H S

def v10Sem (P : Profile) (H : Type) : SemMutator (coreModel P H v10).toLang (CoreEquiv P H) :=
  coreSem P H v10

def v30Sem (P : Profile) (H : Type) : SemMutator (coreModel P H v30).toLang (CoreEquiv P H) :=
  coreSem P H v30

/-! ## Inside the feature set, by construction -/

/-- **Optimised output stays inside the feature set**: every stage `optRunIn S` keeps is
inside `S`. -/
theorem optRunIn_inFeat (S : FeatureSet) :
    ∀ (ss : List ExtraStage) {m : Module}, Module.InFeat S m → Module.InFeat S (optRunIn S ss m)
  | [], _, h => h
  | s :: ss, m, h => by
    by_cases hf : Module.inFeatB S (optRun [s] m) = true
    · rw [optRunIn, ite_eq_left hf]; exact optRunIn_inFeat S ss hf
    · rw [optRunIn, ite_eq_right hf]; exact optRunIn_inFeat S ss h

/-- `optRunIn` keeps validity. -/
theorem optRunIn_valid (S : FeatureSet) :
    ∀ (ss : List ExtraStage) {m : Module}, Validation.ModuleValid m →
      Validation.ModuleValid (optRunIn S ss m)
  | [], _, h => h
  | s :: ss, m, h => by
    by_cases hf : Module.inFeatB S (optRun [s] m) = true
    · rw [optRunIn, ite_eq_left hf]; exact optRunIn_valid S ss (optRun_valid [s] h)
    · rw [optRunIn, ite_eq_right hf]; exact optRunIn_valid S ss h

/-- `optRunIn` preserves the semantics: export equivalence at every profile. -/
theorem optRunIn_equiv (P : Profile) (H : Type) (S : FeatureSet) :
    ∀ (ss : List ExtraStage) {m : Module}, Validation.ModuleValid m →
      CoreEquiv P H (optRunIn S ss m) m
  | [], m, _ => coreEquiv_refl P H m
  | s :: ss, m, h => by
    by_cases hf : Module.inFeatB S (optRun [s] m) = true
    · rw [optRunIn, ite_eq_left hf]
      exact coreEquiv_trans (optRunIn_equiv P H S ss (optRun_valid [s] h))
        (optRun_equiv P H [s] h)
    · rw [optRunIn, ite_eq_right hf]; exact optRunIn_equiv P H S ss h

/-- `optRunIn` keeps validity in `S`. -/
theorem optRunIn_validIn (S : FeatureSet) (ss : List ExtraStage) {m : Module}
    (h : ValidIn S m) : ValidIn S (optRunIn S ss m) :=
  ⟨optRunIn_valid S ss h.1, optRunIn_inFeat S ss h.2⟩

/-- **The semantics-preserving mutator of a feature set, without a checker**: seeded stage
selections run by `optRunIn S`; validity in `S` and equivalence are proved for every output. -/
def featSemIn (P : Profile) (H : Type) (S : FeatureSet) :
    SemMutator (featLang S).toLang (CoreEquiv P H) where
  run r m := optRunIn S (Rand.run pickStages r) m
  valid _ _ hm := optRunIn_validIn S _ hm
  equiv _ _ hm := optRunIn_equiv P H S _ hm.1

/-- What `featSemIn` runs (the executables run this function without importing the proofs). -/
theorem featSemIn_run (P : Profile) (H : Type) (S : FeatureSet) (r : Rng) (m : Module) :
    (featSemIn P H S).run r m = optRunIn S (Rand.run pickStages r) m := rfl

/-- Iterated semantic mutation stays equivalent (`SemMutator.seq`). -/
def featSemIter (P : Profile) (H : Type) (S : FeatureSet) :
    Nat → SemMutator (featLang S).toLang (CoreEquiv P H)
  | 0 => SemMutator.id _ _ (coreEquiv_refl P H)
  | n + 1 => SemMutator.seq coreEquiv_trans (featSem P H S) (featSemIter P H S n)

end Silmaril.Wasm.Tools.Gen.Sem
