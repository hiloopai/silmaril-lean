module

public import Silmaril.Wasm.Tools.Validate.Defs
public import Silmaril.Wasm.Tools.Features.Thms
public import Silmaril.Wasm.Models.Syntax.Thms
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binary.Core.CompactImportsDecodeSound
public import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# `wasm-tools validate` for core modules: correctness

* `decodeW_sound`: the decoder is sound for the grammar `Enc F` (silmaril-lean's
  `decodeModule_sound`, plain or compact imports);
* `Enc_functional`: the grammar determines the module;
* **`check_ok_iff`**: `check F b = .ok ()` iff the encoding gates pass and the decoder returns
  some `m` with `ValidW F m` (validity by `validate?_isSome_iff`, sound and complete);
* **`check_sound`**: an accepted binary is in `Accepts F` (it encodes a valid module of `F`);
* **`check_complete`**: if the decoder reads `b` at all, `check F b` accepts exactly when
  `Accepts F b` (functionality of the grammar: no other module is encoded by `b`);
* `check_mono`: enabling capabilities (with the same compact-imports flag and encoding gates)
  never rejects more; `binGates_dflt`: the default features open every encoding gate.

The decoder's completeness (every `Enc F` byte string is read) is not proved by silmaril-lean;
a decoder rejection is therefore reported as malformed without a theorem that the bytes encode
no module (see Known limitations in `tools/wasm-tools/README.md`).

New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Validate

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models Silmaril.Wasm.Tools.Features

theorem decodeW_sound {F : WFeatures} {b : ByteArray} {m : Module} (h : decodeW F b = .ok m) :
    Enc F b.data.toList m := by
  unfold decodeW at h
  unfold Enc
  split at h
  · rename_i hc
    simp only [hc, ↓reduceIte]
    exact Core.CompactImports.Decode.decodeModule_sound h
  · rename_i hc
    simp only [hc]
    exact Core.Decode.decodeModule_sound h

theorem Enc_functional {F : WFeatures} {b : List UInt8} {m m' : Module} (h : Enc F b m)
    (h' : Enc F b m') : m = m' := by
  unfold Enc at h h'
  split at h
  · rename_i hc
    simp only [hc, ↓reduceIte] at h'
    exact Core.CompactImports.functional h h'
  · rename_i hc
    simp only [hc] at h'
    exact Core.functional h h'

/-- The Boolean feature check decides `InFeatW`. -/
theorem inFeatW_iff {F : WFeatures} {m : Module} : inFeatWB F m = true ↔ InFeatW F m := by
  simp [inFeatWB, InFeatW, Module.InFeat, and_assoc]

theorem of_check_ok {F : WFeatures} {b : ByteArray} (h : check F b = .ok ()) :
    binGates F b.data.toList = true ∧ ∃ m, decodeW F b = .ok m ∧ ValidW F m := by
  have hg : binGates F b.data.toList = true := by
    unfold check at h
    cases hb : binGates F b.data.toList <;> simp_all
  obtain ⟨m, hm⟩ : ∃ m, decodeW F b = .ok m := by
    unfold check at h
    cases hd : decodeW F b <;> simp_all
  obtain ⟨mt, hmt⟩ : ∃ mt, Validation.validate? m = some mt := by
    unfold check at h
    cases hval : Validation.validate? m <;> simp_all
  have hf : inFeatWB F m = true := by
    unfold check at h
    simp_all
  have hv : Validation.ModuleValid m := Validation.validate?_isSome_iff.mp (by simp [hmt])
  exact ⟨hg, m, hm, hv, inFeatW_iff.mp hf⟩

theorem check_ok_of {F : WFeatures} {b : ByteArray} {m : Module}
    (hg : binGates F b.data.toList = true) (hm : decodeW F b = .ok m) (hv : ValidW F m) :
    check F b = .ok () := by
  have hs : (Validation.validate? m).isSome = true := Validation.validate?_isSome_iff.mpr hv.1
  obtain ⟨mt, hmt⟩ : ∃ mt, Validation.validate? m = some mt := Option.isSome_iff_exists.mp hs
  have hb : (!binGates F b.data.toList) = false := by simp [hg]
  have hfB : inFeatWB F m = true := inFeatW_iff.mpr hv.2
  simp only [check, hb, Bool.false_eq_true, ↓reduceIte, hm, hmt, hfB]

/-- **The validator, exactly**: accepted iff the encoding gates pass and the decoder returns a
valid module of `F`. -/
theorem check_ok_iff {F : WFeatures} {b : ByteArray} :
    check F b = .ok () ↔
      binGates F b.data.toList = true ∧ ∃ m, decodeW F b = .ok m ∧ ValidW F m :=
  ⟨of_check_ok, fun ⟨hg, _, hm, hv⟩ => check_ok_of hg hm hv⟩

/-- **Soundness**: an accepted binary passes the encoding gates and encodes a valid module of
`F`. -/
theorem check_sound {F : WFeatures} {b : ByteArray} (h : check F b = .ok ()) :
    Accepts F b.data.toList := by
  obtain ⟨hg, m, hm, hv⟩ := check_ok_iff.mp h
  exact ⟨hg, m, decodeW_sound hm, hv⟩

/-- **Completeness relative to the decoder**: once the decoder reads `b`, `check` accepts exactly
the binaries of `Accepts F`. -/
theorem check_complete {F : WFeatures} {b : ByteArray} {m : Module} (hd : decodeW F b = .ok m) :
    check F b = .ok () ↔ Accepts F b.data.toList := by
  refine ⟨check_sound, fun ⟨hg, m', he, hv⟩ => ?_⟩
  have := Enc_functional (decodeW_sound hd) he
  subst this
  exact check_ok_iff.mpr ⟨hg, m, hd, hv⟩

/-- A rejection by the decoder (after the gates) is the only way `check` reports a malformed
binary. -/
theorem check_malformed {F : WFeatures} {b : ByteArray} {e : String} :
    check F b = .error (.malformed e) ↔
      binGates F b.data.toList = true ∧ decodeW F b = .error e := by
  unfold check
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hg
      refine ⟨by simpa using hg, ?_⟩
      split at h
      · cases h; assumption
      · split at h
        · cases h
        · split at h <;> cases h
  · rintro ⟨hg, h⟩
    have hg' : (!binGates F b.data.toList) = false := by simp [hg]
    simp only [hg', Bool.false_eq_true, ↓reduceIte, h]

theorem constGlobalsB_mono {S T : FeatureSet} (hle : S ≤ T) {m : Module}
    (h : constGlobalsB S m = true) : constGlobalsB T m = true := by
  unfold constGlobalsB at *
  rcases Bool.or_eq_true_iff.mp h with h | h
  · simp [(le_iff.mp hle) _ h]
  · simp [h]

/-- **More capabilities never reject more** (same grammar; encoding and mutable-global gates
at least as open). -/
theorem check_mono {F G : WFeatures} (hc : compact F = compact G)
    (hle : WFeatures.toFS F ≤ WFeatures.toFS G) {b : ByteArray}
    (hg : binGates F b.data.toList = true → binGates G b.data.toList = true)
    (hmut : ∀ {m}, mutGlobalIOB F m = true → mutGlobalIOB G m = true)
    (h : check F b = .ok ()) : check G b = .ok () := by
  obtain ⟨hgF, m, hm, hv, hf, hcg, hmg⟩ := check_ok_iff.mp h
  have hdec : decodeW G b = .ok m := by
    unfold decodeW at hm ⊢
    rw [← hc]
    exact hm
  exact check_ok_iff.mpr ⟨hg hgF, m, hdec, hv, module_mono hle _ hf, constGlobalsB_mono hle hcg,
    hmut hmg⟩

/-- With every encoding gate open (the default features have them), the gates pass. -/
theorem binGates_dflt (b : List UInt8) : binGates WFeatures.dflt b = true := by
  unfold binGates
  have h1 : WFeatures.hasFlag WFeatures.dflt "bulk-memory" = true := by decide
  have h2 : WFeatures.hasFlag WFeatures.dflt "exceptions" = true := by decide
  have h3 : WFeatures.hasFlag WFeatures.dflt "gc" = true := by decide
  have h4 : WFeatures.hasFlag WFeatures.dflt "function-references" = true := by decide
  simp [h1, h2, h3, h4]

end Silmaril.Wasm.Tools.Validate
