module

public import Silmaril.X86.Model.Sem
public import Silmaril.X86.Features.Lattice.Wire

/-!
# x86 models and the maps between them

A `Model` is one x86 machine: a state type, a step (`Sem`, with chaos and
upgradeable outcomes collapsed to `unsettled`), and its flag policy. A map
`M ⟶ N` (`Model.Hom`) is a state map along which `N` agrees with `M` at every
settled step; `M ≤ N` when such a map exists. Everything in `Model/Sem.lean`
transfers along a map, and the configuration lattice of `X86.Features`
embeds into this order (`Hom.ofLe`).

## The named models

| Model | State | Step |
|---|---|---|
| `Model.ext` | `X86.MState` | `X86.Ext.step` |
| `Model.ofConfig c` | `Features.MState` | `Features.step c.features c.exts` |
| `Model.features F` | `Features.MState` | `ofConfig (Config.base F)`: the integer decoder only |
| `Model.float F` | `Features.MState` | `ofConfig (floatConfig F)`: `X86.Float`'s scalar SSE |
| `Model.wire F p` | `Features.MState` | `ofConfig (wireConfig F p)`: `X86.Ext.Wire` with platform `p` |
| `Model.ext8` | `X86.MState` | `X86.Ext8.step` (in `Model/Ext8.lean`) |

and the maps `Hom.ofLe` (any `c ≤ d`), `Hom.extToConfig` (`Model.ext` into
every configuration with LZCNT, BMI1 and POPCNT, from any vector state),
`Hom.featuresToWire`, and `Hom.extToExt8` (in `Model/Ext8.lean`).

## Agreement with the existing judgments

`Model.ext`'s runs and returns are `X86.Ext`'s (`ext_run`, `ext_returns_iff`);
`Model.ofConfig c`'s are `Config.run` and `Config.Returns`
(`ofConfig_run`, `ofConfig_returns_iff`). So `Ext.Returns` facts (the
`sha256_compress` contracts and the like) enter this order as
`Model.ext.sem.Returns` facts and leave it, at a configuration, as
`Config.Returns` facts.
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86.Features (Config FeatureSet baseFeatures)
open Silmaril.X86.Model (Sem Step)

/-- How a model treats status flags the SDM leaves undefined. -/
inductive Model.FlagPolicy where
  /-- Undefined flags are unknown, and a condition on one is chaos
  (`Cond.eval` in three-valued logic). Every model in this file. -/
  | sdm
  /-- Undefined flags are resolved by a per-processor oracle. No machine has
  this policy yet; such a machine refines its `sdm` counterpart, since the
  `sdm` machine is chaos wherever the oracle decides. -/
  | oracle
  deriving DecidableEq, Repr

/-- An x86 model. -/
structure Model where
  name : String
  State : Type
  sem : Sem State
  flags : Model.FlagPolicy := .sdm

namespace Model

/-- A map from `M` to `N`: `N` takes the image step at every settled step of `M`. -/
abbrev Hom (M N : Model) : Type := Sem.Hom M.sem N.sem

@[inherit_doc] scoped infixr:10 " ⟶ " => Hom

/-- `M ≤ N`: some map from `M` to `N` exists. -/
instance : Preorder Model where
  le M N := Nonempty (Hom M N)
  le_refl M := ⟨Sem.Hom.id M.sem⟩
  le_trans _ _ _ := fun ⟨φ⟩ ⟨ψ⟩ => ⟨φ.comp ψ⟩

theorem Hom.le {M N : Model} (φ : Hom M N) : M ≤ N := ⟨φ⟩

/-! ## `X86.Ext` -/

/-- An integer-machine outcome as a refinement step. -/
def ofExtOutcome : Ext.Outcome → Step X86.MState
  | .retired next => .retired next
  | .returned final => .returned final
  | .trapped => .halted
  | .divideFault => .halted
  | .dataFault _ => .halted
  | .undefinedCondition _ => .unsettled
  | .fetchFault => .unsettled
  | .undecodable => .unsettled

/-- The integer machine `X86.Ext`. -/
abbrev ext : Model where
  name := "X86.Ext"
  State := X86.MState
  sem := ⟨fun exit m => ofExtOutcome (Ext.step exit m)⟩

theorem ext_stepOpt (exit : Word) (m : X86.MState) : ext.sem.stepOpt exit m = Ext.stepOpt exit m := by
  cases h : Ext.step exit m <;> simp [Sem.stepOpt, Ext.stepOpt, ofExtOutcome, h]

theorem ext_run (exit : Word) (n : Nat) (m : X86.MState) :
    ext.sem.run exit n m = Machine.Execution.run (Ext.stepOpt exit) n m := by
  unfold Sem.run
  congr 1
  funext m
  exact ext_stepOpt exit m

theorem ext_returns_iff {exit : Word} {initial final : X86.MState} :
    ext.sem.Returns exit initial final ↔ Ext.Returns exit initial final := by
  unfold Sem.Returns Ext.Returns
  constructor
  · rintro ⟨n, mid, hr, hs⟩
    refine ⟨n, mid, by rw [← ext_run]; exact hr, ?_⟩
    change ofExtOutcome (Ext.step exit mid) = _ at hs
    cases h : Ext.step exit mid <;> rw [h] at hs <;> cases hs
    rfl
  · rintro ⟨n, mid, hr, hs⟩
    exact ⟨n, mid, by rw [ext_run]; exact hr, by change ofExtOutcome _ = _; rw [hs]; rfl⟩

/-! ## Configurations of the feature machine -/

/-- A feature-machine outcome as a refinement step. A missing feature, a
feature alias, a fetch fault, undecodable bytes, an unmodelled instruction and
a condition on an undefined flag are unsettled. -/
def ofOutcome : Features.Outcome → Step Features.MState
  | .retired next => .retired next
  | .returned final => .returned final
  | .fault _ => .halted
  | .featureUD _ => .unsettled
  | .featureAlias _ => .unsettled
  | .undefinedCondition _ => .unsettled
  | .fetchFault => .unsettled
  | .undecodable => .unsettled
  | .unmodeled => .unsettled

theorem settled_of_ofOutcome {o : Features.Outcome} (h : ofOutcome o ≠ .unsettled) : o.Settled := by
  cases o <;> simp_all [ofOutcome]

/-- The feature machine of a configuration. -/
abbrev ofConfig (c : Config) : Model where
  name := "X86.Features"
  State := Features.MState
  sem := ⟨fun exit m => ofOutcome (c.step exit m)⟩

theorem ofConfig_stepOpt (c : Config) (exit : Word) (m : Features.MState) :
    (ofConfig c).sem.stepOpt exit m = c.stepOpt exit m := by
  have e : Features.step c.features c.exts exit m = c.step exit m := rfl
  cases h : c.step exit m <;>
    simp [Sem.stepOpt, Config.stepOpt, Features.stepOpt, ofOutcome, e, h]

theorem ofConfig_run (c : Config) (exit : Word) (n : Nat) (m : Features.MState) :
    (ofConfig c).sem.run exit n m = c.run exit n m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Sem.run_succ, Config.run_succ', ofConfig_stepOpt]
    cases c.stepOpt exit m with
    | none => rfl
    | some next => exact ih next

theorem ofConfig_returns_iff {c : Config} {exit : Word} {initial final : Features.MState} :
    (ofConfig c).sem.Returns exit initial final ↔ c.Returns exit initial final := by
  unfold Sem.Returns Config.Returns Features.Returns
  constructor
  · rintro ⟨n, mid, hr, hs⟩
    refine ⟨n, mid, by rw [ofConfig_run] at hr; exact hr, ?_⟩
    change ofOutcome (c.step exit mid) = _ at hs
    cases h : c.step exit mid <;> rw [h] at hs <;> cases hs
    exact h
  · rintro ⟨n, mid, hr, hs⟩
    refine ⟨n, mid, by rw [ofConfig_run]; exact hr, ?_⟩
    change ofOutcome (c.step exit mid) = _
    unfold Config.step
    rw [hs]; rfl

/-- The integer decoder alone, on a processor with features `F`. -/
def features (F : FeatureSet) : Model := ofConfig (Config.base F)

/-- `X86.Float`'s scalar SSE machine. -/
def float (F : FeatureSet) : Model := ofConfig (Features.Config.floatConfig F)

/-- `X86.Ext.Wire` with platform `p`. -/
def wire (F : FeatureSet) (p : Ext.Wire.Platform) : Model := ofConfig (Features.wireConfig F p)

/-! ## Maps -/

/-- The configuration order is a map (identity on states). -/
def Hom.ofLe {c d : Config} (h : c ≤ d) : ofConfig c ⟶ ofConfig d :=
  Sem.Hom.ofAgree fun exit m hs => by
    change ofOutcome (d.step exit m) = ofOutcome (c.step exit m)
    rw [Config.step_le h (settled_of_ofOutcome hs)]

theorem le_of_le {c d : Config} (h : c ≤ d) : ofConfig c ≤ ofConfig d := (Hom.ofLe h).le

theorem ofOutcome_ofBase (v : Features.State) (o : Ext.Outcome) :
    ofOutcome (Features.Outcome.ofBase v o) = (ofExtOutcome o).map (Config.lift v) := by
  cases o <;> rfl

/-- `X86.Ext` maps into every configuration with LZCNT, BMI1 and POPCNT, with
the vector state `v` (`Config.lift v`). -/
def Hom.extToConfig {c : Config} (hF : baseFeatures ⊆ c.features) (v : Features.State) :
    ext ⟶ ofConfig c where
  map := Config.lift v
  step exit m hs := by
    change ofExtOutcome (Ext.step exit m) ≠ .unsettled at hs
    change ofOutcome (c.step exit (Config.lift v m)) = (ofExtOutcome (Ext.step exit m)).map _
    cases hf : Ext.fetch m.memory m.core.rip.toNat with
    | undecodable => exfalso; apply hs; simp [Ext.step, hf, ofExtOutcome]
    | truncated => exfalso; apply hs; simp [Ext.step, hf, ofExtOutcome]
    | decoded i n =>
      rw [Config.step_of_base hF (m := Config.lift v m) hf, Config.lift_toBase,
        Config.lift_state, ofOutcome_ofBase]
      cases Ext.step exit m <;> rfl

theorem ext_le_features {F : FeatureSet} (hF : baseFeatures ⊆ F) (v : Features.State) :
    ext ≤ features F :=
  (Hom.extToConfig (c := Config.base F) hF v).le

/-- The integer decoder maps into `Wire`. -/
def Hom.featuresToWire (F : FeatureSet) (p : Ext.Wire.Platform) : features F ⟶ wire F p :=
  Hom.ofLe (Features.base_le_wireConfig F p)

/-- The integer decoder maps into `X86.Float`'s machine. -/
def Hom.featuresToFloat (F : FeatureSet) : features F ⟶ float F :=
  Hom.ofLe (Config.base_le_floatConfig F)

/-- More features: a map. -/
def Hom.featuresMono {F G : FeatureSet} (h : F ⊆ G) : features F ⟶ features G :=
  Hom.ofLe (Config.base_mono h)

end Model

end Silmaril.X86
