module

public import Silmaril.Wasm.Tools.Gen.API.Thms
public import Silmaril.Wasm.Tools.Gen.Core.Thms
public import Silmaril.Wasm.Tools.Gen.Cmd.Smith.Thms
public import Silmaril.Wasm.Tools.Gen.Cmd.Mutate.Thms
public import Silmaril.Wasm.Tools.Gen.Cmd.Shrink.Thms

/-!
# The subcommands as instances of the generic API

The generic generator, mutator and shrinker API of the genapi track
(`Silmaril.Wasm.Tools.Gen.API`, the language `Core.featLang S` of a point `S` of the feature
lattice: Core 3.0 modules valid in `S`) has the subcommand cores as instances:

* `smithGen S cfg : Generator (featLangW S).toLang`: `wasm-tools smith`'s generator, the size
  being the length of the seed (drawn from the API's SplitMix64 state, `ByteGen.toGenerator`), in the
  language `featLangW S` of modules valid in `S` up to the Wasm 1.0 spellings (`Norm`);
  `toW` embeds generators of `Core.featLang S` into it and `liftW` restricts along `S ≤ T`;
* `mutateMut S cfg o : Mutator (featLang S).toLang`: `wasm-tools mutate`, the input when no
  mutation applies;
* `extendMut S cfg : SemMutator (featLang S).toLang Extends`: the `--preserve-semantics`
  mutations, in the class of extensions (`Extends a b`: `a` is `b` with types, functions and
  globals appended, `Mutate.Thms.extend_*`);
* `shrinkSh S seed : Shrinker Module`: `wasm-tools shrink`'s candidates; with the API's
  `Shrinker.shrink` it keeps validity in `S` (`shrinkSh_validIn`), the predicate
  (`API.Thms.shrink_pred`), never grows (`shrink_size_le`) and stops at a local minimum
  (`shrink_local_min`). The CLI runs the API's `Shrinker.shrinkM` with the predicate script.

So the restriction laws of the API apply to them: `Generator.restrictFeat` and
`Mutator.restrictFeat` (`Core.Thms`) along `S ≤ T`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Inst

open Silmaril.Wasm Silmaril.Wasm.Models

/-- **The language of `ValidInW S`**: Core 3.0 modules valid in `S` up to the Wasm 1.0
spellings (`Norm`), decided by `validInWB S`. -/
def featLangW (S : FeatureSet) : Silmaril.Wasm.Tools.Gen.DecLang where
  Syn := Module
  Valid := ValidInW S
  check := validInWB S
  check_iff _ := validInWB_iff

/-- A generator of `featLang S` is one of `featLangW S` (`validIn_validInW`), with the same
outputs. -/
def toW {S : FeatureSet} (g : Silmaril.Wasm.Tools.Gen.Generator (Core.featLang S).toLang) :
    Silmaril.Wasm.Tools.Gen.Generator (featLangW S).toLang :=
  ⟨g.run, fun r n => validIn_validInW (g.valid r n)⟩

/-- Restriction along `S ≤ T` in `featLangW`: same outputs. -/
def liftW {S T : FeatureSet} (h : S ≤ T)
    (g : Silmaril.Wasm.Tools.Gen.Generator (featLangW S).toLang) :
    Silmaril.Wasm.Tools.Gen.Generator (featLangW T).toLang :=
  ⟨g.run, fun r n => ⟨(g.valid r n).1, module_mono h _ (g.valid r n).2⟩⟩

/-- `wasm-tools smith` as a byte-seeded generator (`ByteGen`) of the API, in the language
`featLangW S`. -/
def smithByteGen (S : FeatureSet) (cfg : Smith.Config) :
    Silmaril.Wasm.Tools.Gen.ByteGen (featLangW S).toLang :=
  ⟨Smith.smith S cfg, Smith.smith_validInW S cfg⟩

/-- **`wasm-tools smith` as a generator of the API** (language `featLangW S`): the seed is
drawn from the SplitMix64 state (`ByteGen.toGenerator`). -/
def smithGen (S : FeatureSet) (cfg : Smith.Config) :
    Silmaril.Wasm.Tools.Gen.Generator (featLangW S).toLang :=
  (smithByteGen S cfg).toGenerator

/-- **`wasm-tools mutate` as a mutator of the API.** -/
def mutateMut (S : FeatureSet) (cfg : Smith.Config) (o : Mutate.Opts) :
    Mutator (Core.featLang S).toLang :=
  (Mutate.mutator S cfg o).toMutator

/-- `a` extends `b`: `b` with function types, functions and globals appended. -/
def Extends (a b : Module) : Prop := ∃ d, a = Mutate.extend b d

/-- **The `--preserve-semantics` mutations as a semantics-preserving mutator of the API**, for
the class of extensions. -/
def extendMut (S : FeatureSet) (cfg : Smith.Config) :
    SemMutator (Core.featLang S).toLang Extends where
  toMutator := (Mutate.preserving S cfg).toPMutator.toMutator
  equiv r m _ := by
    show Extends ((Mutate.mutateExtend S cfg r.state m).getD m) m
    cases h : Mutate.mutateExtend S cfg r.state m with
    | none => exact ⟨{}, (Mutate.extend_empty m).symm⟩
    | some m' => exact Mutate.mutateExtend_extends h

/-- **`wasm-tools shrink`'s candidates as a shrinker of the API** (`Shrink.shrinker`). -/
abbrev shrinkSh (S : FeatureSet) (seed : Nat) : Shrinker Module := Shrink.shrinker S seed

/-- Shrinking with the API's loop keeps validity in `S`. -/
theorem shrinkSh_validIn (S : FeatureSet) (seed : Nat) (p : Module → Bool) {m : Module}
    (hm : ValidIn S m) : ValidIn S ((shrinkSh S seed).shrink p m) :=
  Shrink.shrink_validIn hm

end Silmaril.Wasm.Tools.Gen.Cmd.Inst
