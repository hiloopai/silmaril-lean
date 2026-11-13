module

public import Silmaril.Wasm.Tools.Gen.Cmd.Smith.Defs
public import Silmaril.Wasm.Tools.Gen.Cmd.Norm.Thms
public import Silmaril.Wasm.Tools.Gen.Cmd.Sections.Thms
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

/-!
# `wasm-tools smith`: specification

* `smith_validInW`: every module `smith S cfg seed` is valid in the model `S` up to the Wasm
  1.0 spellings (`Norm.ValidInW`: Core 3.0 valid, `Silmaril.Wasm.Validation.ModuleValid`, and
  inside the capabilities of `S` once implicit table initialisers and function-index segments
  are erased);
* `smith_validInW_mono`: the output for a smaller model is valid in every larger one;
* `smithBytes_spec`: **the bytes `wasm-tools smith` writes encode such a module** in the
  Core 3.0 binary grammar (`Silmaril.Wasm.Binary.Core.Encodes`);
* `smith_eq_raw`: when the check accepts the raw module, `smith` is the raw module (the
  fallback does not fire).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Smith

open Silmaril.Wasm Silmaril.Wasm.Models

/-- **Every generated module is valid in the model** (up to the Wasm 1.0 spellings). -/
theorem smith_validInW (S : FeatureSet) (cfg : Config) (seed : ByteArray) :
    ValidInW S (smith S cfg seed) :=
  checkedGenW_validInW S (rawModule S cfg) seed

/-- Restriction along a feature inclusion: an output for `S` is valid in every `T ≥ S`. -/
theorem smith_validInW_mono {S T : FeatureSet} (h : S ≤ T) (cfg : Config) (seed : ByteArray) :
    ValidInW T (smith S cfg seed) :=
  ⟨(smith_validInW S cfg seed).1, module_mono h _ (smith_validInW S cfg seed).2⟩

theorem smith_eq_raw {S : FeatureSet} {cfg : Config} {seed : ByteArray}
    (h : smithRaw? S cfg seed = true) : smith S cfg seed = rawModule S cfg seed :=
  checkedGenW_of_valid h

theorem encode_empty : Binaryen.Exe.encodeModule? ({} : Module) = .ok emptyBytes := by
  rfl

/-- **The bytes of `wasm-tools smith` encode a valid module of `S`.** -/
theorem smithBytes_spec (S : FeatureSet) (cfg : Config) (seed : ByteArray) :
    ∃ m, Binary.Core.Encodes (smithBytes S cfg seed) m ∧ ValidInW S m := by
  unfold smithBytes
  split
  · next bs h => exact ⟨_, Binaryen.Exe.encodeModuleWith?_sound h, smith_validInW S cfg seed⟩
  · exact ⟨{}, Binaryen.Exe.encodeModule?_sound encode_empty, emptyModule_validInW S⟩

/-- **With `--generate-custom-sections`**, the bytes are those of `smithBytes`, or its header
followed by its non-custom sections, in order, with the generated custom sections (in their
order) between them. -/
theorem smithBytesC_spec (S : FeatureSet) (cfg : Config) (seed : ByteArray) :
    smithBytesC S cfg seed = smithBytes S cfg seed ∨
      ∃ secs out, Sections.split ⟨(smithBytes S cfg seed).toArray⟩ = some secs ∧
        smithBytesC S cfg seed =
          (Sections.join ((⟨(smithBytes S cfg seed).toArray⟩ : ByteArray).extract 0 8) out).data.toList ∧
        out.filter (fun s => !s.isCustom) = secs.filter (fun s => !s.isCustom) ∧
        out.filter Sections.Sec.isCustom = (rawCustoms S cfg seed).map (·.2) := by
  unfold smithBytesC
  split
  · rcases Sections.restore_spec' (rawCustoms S cfg seed) ⟨(smithBytes S cfg seed).toArray⟩
        (fun c hc => (List.mem_filter.mp hc).2) with h | ⟨secs, out, h1, h2, h3, h4⟩
    · exact .inl (by rw [h])
    · exact .inr ⟨secs, out, h1, by rw [h2], h3, h4⟩
  · exact .inl rfl

end Silmaril.Wasm.Tools.Gen.Cmd.Smith
