module

public import Silmaril.Wasm.Models.Features.Defs

/-!
# The model selected by `wasm-tools smith`'s feature flags

`wasm-smith`'s `--*-enabled` flags (and `--allow-floats`, `--max-memories`) select a point of
the capability lattice (`Silmaril.Wasm.Models.Features`): `model flag maxMemories` starts from
Wasm 3.0 plus the extensions whose flags are on, and removes (`FeatureSet.remove`, which also
removes what depends on it) the capabilities of every flag that is off. Upstream defaults
(`--help`): everything on except custom page sizes, wide arithmetic and
shared-everything threads; `max-memories` 1, so multi-memory is off by default.

* `flagCaps`: each flag and the capabilities it controls (`callIndirectOverlong` goes with
  reference types, as wasmparser's overlong `call_indirect` encoding does);
* `model get maxMemories`: `get` answers the value given for a flag, if any;
* `Thms`: the default model is below `v30`, and the model with every 2.0 and 3.0 flag off is
  below `v10`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Model

open Silmaril.Wasm.Models

/-- Each feature flag, its default, and the capabilities it controls. -/
def flagCaps : List (String × Bool × List Cap) :=
  [("sign-extension-ops-enabled", true, [.signExt]),
   ("saturating-float-to-int-enabled", true, [.satConv]),
   ("multi-value-enabled", true, [.multiValue]),
   ("reference-types-enabled", true, [.refTypes, .callIndirectOverlong]),
   ("bulk-memory-enabled", true, [.bulkMemory, .bulkMemoryOpt]),
   ("simd-enabled", true, [.simd]),
   ("relaxed-simd-enabled", true, [.relaxedSimd]),
   ("allow-floats", true, [.floatNum]),
   ("tail-call-enabled", true, [.tailCall]),
   ("extended-const-enabled", true, [.extConst]),
   ("gc-enabled", true, [.gcImm, .gcMut, .typedFuncRef]),
   ("exceptions-enabled", true, [.exn]),
   ("memory64-enabled", true, [.memory64]),
   ("custom-page-sizes-enabled", false, [.customPageSizes]),
   ("wide-arithmetic-enabled", false, [.wideArith])]

/-- Remove a list of capabilities. -/
def removeAll (S : FeatureSet) (cs : List Cap) : FeatureSet := cs.foldl FeatureSet.remove S

/-- **The model of the flags**. -/
def model (get : String → Option Bool) (maxMemories : Nat) : FeatureSet :=
  let on (f : String × Bool × List Cap) : Bool := (get f.1).getD f.2.1
  let base := FeatureSet.ofList (mvpCaps ++ caps20 ++ caps30 ++
    (flagCaps.filter on).flatMap (·.2.2))
  let S := removeAll base ((flagCaps.filter (!on ·)).flatMap (·.2.2))
  if maxMemories ≤ 1 then S.remove .multiMemory else S

/-- The default model (no flags). -/
def default : FeatureSet := model (fun _ => none) 1

/-- Every 2.0 and 3.0 flag off. -/
def mvpFlags (s : String) : Option Bool :=
  if s == "allow-floats" then none else some false

end Silmaril.Wasm.Tools.Gen.Cmd.Model
