module

public import Silmaril.Wasm.Binaryen.Toolkit.Link
public import Silmaril.Wasm.Binaryen.Toolkit.ByteInputSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Link.Recipe

/-! # Specification guarantee for byte-input GC linking

Success proves the exact binary meaning of both inputs and the output, actual
execution of `Link.GC.link?`, validation of the linked module, and an assembly
recipe for the existing semantic linking theorems. This does not assert
unconditional contextual equivalence or general N-ary Binaryen `wasm-merge`.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

theorem linkModules_sound {namespaceName : String} {provider consumer linked : Wasm.Module}
    (h : linkModules namespaceName provider consumer = .ok linked) :
    Link.GC.link? namespaceName provider consumer = some linked := by
  unfold linkModules at h
  split at h
  · cases h
    assumption
  · cases h

/-- All three byte streams are related to their actual modules by the binary
specification. The result is the valid output of the existing partial linker. -/
theorem linkBytes_sound {namespaceName : String} {providerBytes consumerBytes : ByteArray}
    {artifact : LinkedArtifact}
    (h : linkBytes namespaceName providerBytes consumerBytes = .ok artifact) :
    Binary.Core.Encodes providerBytes.data.toList artifact.provider ∧
    Binary.Core.Encodes consumerBytes.data.toList artifact.consumer ∧
    Link.GC.link? namespaceName artifact.provider artifact.consumer = some artifact.linked ∧
    Validation.ModuleValid artifact.linked ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.linked := by
  unfold linkBytes at h
  obtain ⟨provider, hp, h⟩ := Exe.bind_ok h
  obtain ⟨consumer, hc, h⟩ := Exe.bind_ok h
  obtain ⟨linked, hl, h⟩ := Exe.bind_ok h
  obtain ⟨bytes, hb, h⟩ := Exe.bind_ok h
  cases Except.ok.inj h
  have actual := linkModules_sound hl
  exact ⟨decodeInput_sound hp, decodeInput_sound hc, actual,
    Link.GC.link?_valid actual, Exe.encodeModule_sound hb⟩

/-- Extract the existing semantic linker interface from a successful byte run.
`PreparedObservation.separate_linked_result` and `separate_linked_agreement`
apply with this recipe and the actual-link equation in `linkBytes_sound`. -/
theorem linkBytes_recipe {namespaceName : String} {providerBytes consumerBytes : ByteArray}
    {artifact : LinkedArtifact}
    (h : linkBytes namespaceName providerBytes consumerBytes = .ok artifact) :
    Nonempty (Link.GC.Recipe.Assembly namespaceName
      artifact.provider artifact.consumer artifact.linked) :=
  Link.GC.link?_recipe (linkBytes_sound h).2.2.1

end Silmaril.Wasm.Binaryen.Toolkit
