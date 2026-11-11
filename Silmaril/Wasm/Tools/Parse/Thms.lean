module

public import Silmaril.Wasm.Tools.Parse.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

/-!
# `wasm-tools parse`: specification theorems

* `textModule_sound`: the module read from a text is the one the Core 3.0 text grammar gives;
* `parseModule_sound`: text and output bytes encode the same module;
* `parseModule_functional`: that module is unique (both grammars are functional), so two
  successful runs on texts denoting the same module give bytes of the same module.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Parse

open Silmaril Silmaril.Wasm

theorem textModule_sound {s : String} {m : Wasm.Module} (h : textModule s = .ok m) :
    Text.Core.Encodes s m := by
  unfold textModule at h
  split at h
  · cases h
  · rename_i x hx
    split at h
    · cases h
    · rename_i c _
      cases h
      exact ⟨x, Formats.SExpEncoding.Wat.sexpWat_of_fullExec hx, c.2⟩

theorem parseModule_sound {s : String} {b : ByteArray} (h : parseModule s = .ok b) :
    ∃ m, Text.Core.Encodes s m ∧ Binary.Core.Encodes b.data.toList m := by
  unfold parseModule at h
  cases ht : textModule s with
  | error e => simp [ht, bind, Except.bind] at h
  | ok m =>
    simp only [ht, bind, Except.bind, Except.mapError] at h
    split at h
    · cases h
    · rename_i b' he
      cases h
      exact ⟨m, textModule_sound ht, Binaryen.Exe.encodeModule_sound he⟩

/-- The module that a successful `parseModule` run encodes is determined by the text. -/
theorem parseModule_module_unique {s : String} {b : ByteArray} {m : Wasm.Module}
    (h : parseModule s = .ok b) (hm : Text.Core.Encodes s m) :
    Binary.Core.Encodes b.data.toList m := by
  obtain ⟨m', h₁, h₂⟩ := parseModule_sound h
  rw [Text.Core.encodes_functional h₁ hm] at h₂
  exact h₂

end Silmaril.Wasm.Tools.Parse
