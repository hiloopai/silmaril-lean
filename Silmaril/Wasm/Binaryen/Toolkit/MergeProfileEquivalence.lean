module

public import Silmaril.Wasm.Binaryen.MergeProfileEquivalence
public import Silmaril.Wasm.Binaryen.Toolkit.MergeSound

@[expose] public section

/-! # Exact arbitrary-profile semantics for the existing merge byte artifact

The byte decoder, actual checked merge, output validation and encoder retain
their existing guards. The semantic equality holds independently at every
numerical profile; it does not change the executable interpreter's oracle or
extend the accepted linker fragment.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core Numerics

/-- The actual retained inputs and merged module have exactly the same
separate/merged results and divergence at every numerical profile. Original
input and output byte provenance is supplied by `mergeBytes_sound`. -/
theorem mergeBytes_semantics_profile {H : Type} {inputs : List (String × ByteArray)}
    {artifact : MergedArtifact} (h : mergeBytes inputs = .ok artifact) (P : Profile)
    {n x : String} {vs : List Val}
    (hx : ∃ p ∈ artifact.inputs, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    Program.beh P (SingleThreaded.Det.noHost (H := H)) artifact.inputs n x vs =
      (moduleEntryPoints P (SingleThreaded.Det.noHost (H := H)) closedEnv).beh
        artifact.merged x vs :=
  checkedMerge?_sound_profile (mergeBytes_sound h).2.1 P hx

end Silmaril.Wasm.Binaryen.Toolkit
