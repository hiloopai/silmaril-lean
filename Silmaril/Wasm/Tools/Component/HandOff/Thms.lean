module

public import Silmaril.Wasm.Tools.Component.HandOff.Defs
public import Silmaril.Wasm.Tools.Component.Validate.Thms
public import Silmaril.Wasm.Tools.Component.Wat.Thms
public import Silmaril.Wasm.Tools.Component.Layout.Thms

/-!
# The hand-off functions: specification theorems

* `validateFeat_sound`, `validate_sound`: a component accepted by the hand-off is accepted by
  `Validate.Accepts` (the binary grammar, the reference validity, the extra and gate rules) at
  the flags the `--features` arguments project to;
* `classify_component`: a binary with the component preamble is handed off;
* `printPlain_read`: the verified reader reads the text `printPlain` wrote to the normal form
  of the decoding.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.HandOff

open Silmaril.Wasm.Component

theorem validateFeat_sound {f : Features.Feat} {b : ByteArray} (h : validateFeat f b = .ok) :
    ∃ F c ct, Features.toCFlags f = some F ∧ Validate.Accepts F b c ct := by
  unfold validateFeat at h
  split at h
  · cases h
  · next F hF =>
    split at h
    · next ct hc =>
      obtain ⟨c, hacc⟩ := Validate.check_sound hc
      exact ⟨F, c, ct, hF, hacc⟩
    · cases h

/-- **Soundness of the hand-off of `validate`** on a component binary. -/
theorem validate_sound {fs : List String} {b : ByteArray}
    (hk : Validate.kindOf b = .component) (h : validate fs b = .ok) :
    ∃ f, features fs = .ok f ∧ ∃ F c ct, Features.toCFlags f = some F ∧
      Validate.Accepts F b c ct := by
  unfold validate at h
  split at h
  · cases h
  · next f hf =>
    rw [hk] at h
    exact ⟨f, hf, validateFeat_sound (by simpa using h)⟩

theorem classify_component {b : ByteArray} (hk : Validate.kindOf b = .component) :
    classify b = .component := by
  simp [classify, hk]

/-- **The reader reads `printPlain`'s text** back to the normal form of the binary's
decoding (wasmprinter's layout and index comments are invisible to the reader). -/
theorem printPlain_read {b : ByteArray} {s : String} (h : printPlain b = .ok s) :
    ∃ c, BinaryP3.parse b = .ok c ∧ Wat.read s = some (Wat.norm c) := by
  unfold printPlain at h
  split at h
  · next c hc => cases h; exact ⟨c, hc, Layout.read_printW c⟩
  · cases h

end Silmaril.Wasm.Tools.Component.HandOff
