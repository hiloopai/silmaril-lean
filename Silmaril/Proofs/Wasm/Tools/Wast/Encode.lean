module

public import Silmaril.Wasm.Tools.Wast.Encode.Defs
public import Silmaril.Wasm.Tools.Text.Thms
public import Silmaril.Wasm.Tools.Layout.Thms

/-!
# The checked text encoder: proofs

Proofs for `Silmaril.Wasm.Tools.Wast.Encode.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril Silmaril.Wasm

theorem acceptsNorm_sound {dc : Bool} {m : Wasm.Module} {cand : List UInt8}
    (h : acceptsNorm dc m cand = true) :
    ∃ m', Binary.Core.Encodes cand m' ∧ normElems m' = normElems m := by
  unfold acceptsNorm at h
  split at h
  · rename_i m' hd
    split at h
    · rename_i a b ha hb
      have hab : a = b := by simpa using h
      subst hab
      refine ⟨m', ?_, ?_⟩
      · simpa using Binary.Core.Decode.decodeModule_sound hd
      · exact Binary.Core.functional (Binaryen.Exe.encodeModuleWith?_sound ha)
          (Binaryen.Exe.encodeModuleWith?_sound hb)
    · cases h
  · cases h

theorem checkedCore_sound_raw {src : String} {cand : Except String ByteArray} {b : ByteArray}
    {x : Text.SExp} {m : Wasm.Module} {canon : List UInt8} (ht : Text.textTree? src = .ok (x, m))
    (hcanon : Binaryen.Exe.encodeModuleWith? (Binaryen.Exe.usesDataIdx m) m = .ok canon)
    (h : checkedCore src cand = .ok b) :
    ∃ m', Binary.Core.Encodes b.data.toList m' ∧ normElems m' = normElems m := by
  have hm : Text.Core.Encodes (Silmaril.Wasm.Tools.Annot.stripTrivia src) m := Text.textTree?_sound ht
  have fallback : ∀ {b' : ByteArray}, Text.textToBinary src = .ok b' →
      ∃ m', Binary.Core.Encodes b'.data.toList m' ∧ normElems m' = normElems m := by
    intro b' h'
    obtain ⟨m', ht', hb⟩ := Text.textToBinary_sound h'
    have hmm : m' = m := Text.Core.encodes_functional ht' hm
    exact ⟨m', hmm ▸ hb, by rw [hmm]⟩
  -- with the text read and the canonical encoding computed, `checkedCore` is a choice on `cand`
  have hred : checkedCore src cand =
      (match (generalizing := false) cand with
       | .ok c =>
         if Layout.accepts (Binaryen.Exe.usesDataIdx m) canon c.data.toList then .ok c
         else if acceptsNorm (Binaryen.Exe.usesDataIdx m) m c.data.toList then .ok c
         else Text.textToBinary src
       | .error _ => Text.textToBinary src) := by
    unfold checkedCore
    simp only [ht, hcanon]
    cases cand <;> rfl
  have h' : _ = (Except.ok b : Except String ByteArray) := hred.symm.trans h
  cases hc : cand with
  | error e =>
    have hb : Text.textToBinary src = .ok b := by simpa only [hc] using h'
    exact fallback hb
  | ok c =>
    show ∃ m', Binary.Core.Encodes b.data.toList m' ∧ normElems m' = normElems m
    have hif : (if Layout.accepts (Binaryen.Exe.usesDataIdx m) canon c.data.toList then .ok c
        else if acceptsNorm (Binaryen.Exe.usesDataIdx m) m c.data.toList then .ok c
        else Text.textToBinary src) = (Except.ok b : Except String ByteArray) := by
      simpa only [hc] using h'
    by_cases hacc : Layout.accepts (Binaryen.Exe.usesDataIdx m) canon c.data.toList = true
    · have hcb : c = b := by simpa only [hacc, ↓reduceIte, Except.ok.injEq] using hif
      exact ⟨m, hcb ▸ Layout.accepts_sound (Binaryen.Exe.encodeModuleWith?_sound hcanon) hacc, rfl⟩
    · by_cases hn : acceptsNorm (Binaryen.Exe.usesDataIdx m) m c.data.toList = true
      · have hcb : c = b := by
          simpa only [hacc, hn, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] using hif
        exact hcb ▸ acceptsNorm_sound hn
      · have hb : Text.textToBinary src = .ok b := by
          simpa only [hacc, hn, Bool.false_eq_true, ↓reduceIte] using hif
        exact fallback hb

end Silmaril.Wasm.Tools.Wast
