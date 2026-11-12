module

public import Silmaril.Wasm.Tools.Gen.Core.Defs
public import Silmaril.Wasm.Tools.Gen.API.Thms
public import Silmaril.Wasm.Tools.Gen.Model.Defs
public import Silmaril.Wasm.Models.Model.Thms
public import Silmaril.Wasm.Models.FX.Thms
public import Silmaril.Wasm.Perf.ValidateR.Thms

/-!
# Core instances: Wasm 1.0, 3.0 and WasmFX, and restriction along the feature lattice

* the verified objects over `Defs`: `featCheck_iff` (the checker decides `ValidIn S`),
  `featLang S`, `empty_validIn`, `featGen S` and `featMut S`, which compute `featGenRun S` and
  `featMutRun S` (`featGen_run_eq`, `featMut_run_eq`);
* `coreModel_toLang`, `fxModel_toLang`: the module languages of the restricted Core models and
  of CoreFX are the feature-set languages `featLang S` and `featLang wasmFX` (by definition);
* `coreGen P H S`, `coreMut P H S`: the generator and mutator of `coreModel P H S`; the named
  instances `v10Gen`, `v30Gen`, `fxGen` (and mutators);
* **restriction along feature inclusions**: `featGen_mono` (a generator of `S` is one of `T ≥ S`
  through the conservative `coreEmb`, with the same outputs: `featGen_mono_run`),
  `fxGen_of_v30` (through `fxEmb`); `Mutator.restrictFeat` (a mutator of `T` that keeps `S`
  modules in `S` is one of `S`), `Generator.restrictFeat` (a generator of `T` whose outputs are
  in `S` is one of `S`);
* `featShrink_spec`: checked shrinking at `S` keeps validity in `S` and the predicate, does not
  grow the module and ends in a local minimum.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Core

open Silmaril.Wasm Silmaril.Wasm.Models
open Silmaril.Wasm.Numerics (Profile)

/-! ## The verified objects -/

theorem featCheck_iff (S : FeatureSet) (m : Module) : featCheck S m = true ↔ ValidIn S m := by
  rw [featCheck, Silmaril.Wasm.Perf.ValidateR.validateR_eq, Bool.and_eq_true,
    Silmaril.Wasm.Validation.validate?_isSome_iff]
  rfl

/-- **The language of a point of the feature lattice**: Core 3.0 modules valid in `S`. -/
def featLang (S : FeatureSet) : DecLang where
  Syn := Module
  Valid := ValidIn S
  check := featCheck S
  check_iff := featCheck_iff S

/-- The empty module is valid at every feature set. -/
theorem empty_validIn (S : FeatureSet) : ValidIn S ({} : Module) := by
  refine ⟨Silmaril.Wasm.Validation.validate?_isSome_iff.1 (by decide +kernel), ?_⟩
  simp [Module.InFeat, Module.inFeatB]

/-- **The generator of a feature set**: the raw generator, checked; the empty module
otherwise. -/
def featGen (S : FeatureSet) : Generator (featLang S).toLang :=
  Generator.guarded (featLang S) (fun r n => Rand.run (Raw.module S n) r) {} (empty_validIn S)

/-- **The mutator of a feature set**: the raw mutation, checked; the input otherwise. -/
def featMut (S : FeatureSet) : Mutator (featLang S).toLang :=
  Mutator.guarded (featLang S) (Raw.mutate S)

/-- The verified generator computes `featGenRun`. -/
theorem featGen_run_eq (S : FeatureSet) : (featGen S).run = featGenRun S := rfl

/-! ## The Core models -/

theorem coreModel_toLang (P : Profile) (H : Type) (S : FeatureSet) :
    (coreModel P H S).toLang = (featLang S).toLang := rfl

theorem fxModel_toLang (P : Profile) (H : Type) :
    (Silmaril.Wasm.Models.FX.fxModel P H).toLang = (featLang wasmFX).toLang := rfl

/-- The generator of `coreModel P H S`. -/
def coreGen (P : Profile) (H : Type) (S : FeatureSet) : Generator (coreModel P H S).toLang :=
  featGen S

/-- The mutator of `coreModel P H S`. -/
def coreMut (P : Profile) (H : Type) (S : FeatureSet) : Mutator (coreModel P H S).toLang :=
  featMut S

/-- **Wasm 1.0** (Core 3.0 restricted to `v10`). -/
def v10Gen (P : Profile) (H : Type) : Generator (coreModel P H v10).toLang := coreGen P H v10

/-- **Wasm 3.0**. -/
def v30Gen (P : Profile) (H : Type) : Generator (coreModel P H v30).toLang := coreGen P H v30

def v10Mut (P : Profile) (H : Type) : Mutator (coreModel P H v10).toLang := coreMut P H v10
def v30Mut (P : Profile) (H : Type) : Mutator (coreModel P H v30).toLang := coreMut P H v30

/-- **WasmFX** (CoreFX, `Silmaril.Wasm.Models.FX.fxModel`). -/
def fxGen (P : Profile) (H : Type) : Generator (Silmaril.Wasm.Models.FX.fxModel P H).toLang :=
  featGen wasmFX

def fxMut (P : Profile) (H : Type) : Mutator (Silmaril.Wasm.Models.FX.fxModel P H).toLang :=
  featMut wasmFX

/-! ## Restriction along the feature lattice -/

/-- **A generator of `S` is a generator of `T ≥ S`**, through the embedding `coreEmb`. -/
def featGen_mono (P : Profile) (H : Type) {S T : FeatureSet} (h : S ≤ T)
    (g : Generator (coreModel P H S).toLang) : Generator (coreModel P H T).toLang :=
  g.mapEmb (coreEmb P H h)

theorem featGen_mono_run (P : Profile) (H : Type) {S T : FeatureSet} (h : S ≤ T)
    (g : Generator (coreModel P H S).toLang) : (featGen_mono P H h g).run = g.run := rfl

theorem coreEmb_conservative_on (P : Profile) (H : Type) {S T : FeatureSet} (h : S ≤ T)
    {m : Module} (hm : Module.InFeat S m) :
    ValidIn T m → ValidIn S m := coreEmb_reflect P H h hm

/-- **The 1.0 generator is a 3.0 generator** with the same outputs. -/
def v10Gen_in_v30 (P : Profile) (H : Type) : Generator (coreModel P H v30).toLang :=
  featGen_mono P H (le_trans v10_le_v20 v20_le_v30) (v10Gen P H)

/-- **A 3.0 generator is a WasmFX generator**, through `fxEmb`. -/
def fxGen_of_v30 (P : Profile) (H : Type) (g : Generator (coreModel P H v30).toLang) :
    Generator (Silmaril.Wasm.Models.FX.fxModel P H).toLang :=
  g.mapEmb (Silmaril.Wasm.Models.FX.fxEmb P H)

theorem fxGen_of_v30_run (P : Profile) (H : Type) (g : Generator (coreModel P H v30).toLang)
    (r : Rng) (n : Nat) :
    (fxGen_of_v30 P H g).run r n = (Silmaril.Wasm.Models.FX.fxEmb P H).mod (g.run r n) :=
  Generator.mapEmb_run _ g r n

/-- **A mutator of `T` that keeps `S` modules in `S` is a mutator of `S`.** -/
def _root_.Silmaril.Wasm.Tools.Gen.Mutator.restrictFeat {S T : FeatureSet} (h : S ≤ T)
    (μ : Mutator (featLang T).toLang)
    (hS : ∀ r m, Module.InFeat S m → Module.InFeat S (μ.run r m)) :
    Mutator (featLang S).toLang where
  run := μ.run
  valid r m hm := ⟨(μ.valid r m (validIn_mono h hm)).1, hS r m hm.2⟩

/-- **A generator of `T` whose outputs are in `S` is a generator of `S`.** -/
def _root_.Silmaril.Wasm.Tools.Gen.Generator.restrictFeat {S T : FeatureSet}
    (g : Generator (featLang T).toLang) (hS : ∀ r n, Module.InFeat S (g.run r n)) :
    Generator (featLang S).toLang where
  run := g.run
  valid r n := ⟨(g.valid r n).1, hS r n⟩

/-- **A byte-seeded generator of `S` is one of `T ≥ S`** (same outputs). -/
def _root_.Silmaril.Wasm.Tools.Gen.ByteGen.liftFeat {S T : FeatureSet} (h : S ≤ T)
    (g : ByteGen (featLang S).toLang) : ByteGen (featLang T).toLang :=
  ⟨g.gen, fun seed => validIn_mono h (g.valid seed)⟩

@[simp] theorem _root_.Silmaril.Wasm.Tools.Gen.ByteGen.liftFeat_gen {S T : FeatureSet}
    (h : S ≤ T) (g : ByteGen (featLang S).toLang) : (g.liftFeat h).gen = g.gen := rfl

/-- **A partial mutator of `T` restricts to `S ≤ T`** when its outputs on valid modules of `S`
stay inside the capabilities of `S`. -/
def _root_.Silmaril.Wasm.Tools.Gen.PMutator.restrictFeat {S T : FeatureSet} (h : S ≤ T)
    (μ : PMutator (featLang T).toLang)
    (keep : ∀ seed m m', ValidIn S m → μ.mutate seed m = some m' → Module.InFeat S m') :
    PMutator (featLang S).toLang :=
  ⟨μ.mutate, fun seed m m' hm hmut =>
    ⟨(μ.valid seed m m' (validIn_mono h hm) hmut).1, keep seed m m' hm hmut⟩⟩

/-- A checked partial mutation that passes at `S` passes at every `T ≥ S`. -/
theorem _root_.Silmaril.Wasm.Tools.Gen.PMutator.guardedRun_mono {S T : FeatureSet} (h : S ≤ T)
    {raw : UInt64 → Module → Option Module} {seed : UInt64} {m m' : Module}
    (hs : PMutator.guardedRun (featLang S) raw seed m = some m') :
    PMutator.guardedRun (featLang T) raw seed m = some m' := by
  unfold PMutator.guardedRun at hs ⊢
  cases hr : raw seed m with
  | none => rw [hr] at hs; exact absurd hs (by simp)
  | some x =>
    rw [hr] at hs
    have hv : featCheck S x = true := by
      cases hc : featCheck S x
      · have hs' : (if featCheck S x = true then some x else none) = some m' := hs
        rw [hc] at hs'
        exact absurd hs' (by simp)
      · rfl
    have hx : x = m' := by
      have hs' : (if featCheck S x = true then some x else none) = some m' := hs
      rw [hv, ite_eq_left rfl] at hs'
      exact Option.some.inj hs'
    have hT : featCheck T x = true :=
      (featCheck_iff T x).mpr (validIn_mono h ((featCheck_iff S x).mp hv))
    show (if featCheck T x = true then some x else none) = some m'
    rw [hT, ite_eq_left rfl, hx]

/-- A mutator of `S` lifts to `T ≥ S` on `S`-modules only; on a `T`-module outside `S` the
checked mutator `featMut T` is the one to use. Both agree with their raw rewrite whenever the
check passes (`Mutator.guarded_run_of_check`). -/
theorem featMut_run (S : FeatureSet) (r : Rng) (m : Module) :
    (featMut S).run r m = if featCheck S (Raw.mutate S r m) then Raw.mutate S r m else m := rfl

/-- The verified mutator computes `featMutRun`. -/
theorem featMut_run_eq (S : FeatureSet) : (featMut S).run = featMutRun S := rfl

/-! ## Shrinking -/

/-- **Checked shrinking at `S`**: validity in `S` and the predicate are kept, the size does not
grow, and no strictly smaller candidate of the result is valid and satisfies the predicate. -/
theorem featShrink_spec (S : FeatureSet) (p : Module → Bool) {m : Module} (hv : ValidIn S m)
    (hp : p m = true) :
    ValidIn S (featShrink S p m) ∧ p (featShrink S p m) = true ∧
      Raw.size (featShrink S p m) ≤ Raw.size m ∧
      ∀ c ∈ Raw.cands (featShrink S p m), Raw.size c < Raw.size (featShrink S p m) →
        (featCheck S c && p c) = false := by
  obtain ⟨h₁, h₂⟩ := Shrinker.shrink_valid (featLang S) featShrinker p hv hp
  exact ⟨h₁, h₂, featShrinker.shrink_size_le _ m, featShrinker.shrink_local_min _ m⟩

end Silmaril.Wasm.Tools.Gen.Core
