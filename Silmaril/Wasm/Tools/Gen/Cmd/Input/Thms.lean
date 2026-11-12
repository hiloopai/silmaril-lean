module

public import Silmaril.Wasm.Tools.Gen.Cmd.Input.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Thms
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Encoding.TextExtras
public import Silmaril.Wasm.Tools.Gen.Cmd.WatLex.Thms
public import Silmaril.Wasm.Tools.Gen.Cmd.WatFast.Thms

/-!
# Reading the input: specification

`readModule_sound`: a binary input encodes the returned module in the binary grammar of
Core 3.0 (`Binary.Core.Encodes`); a text input is UTF-8 text that encodes it in the text
grammar (`Text.Core.Encodes`: the WAT S-expression grammar composed with the module
syntax).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Input

open Silmaril Silmaril.Wasm

theorem lexAny_sound {s : String} {tree}
    (h : (WatLex.lexFull? .core3 s <|> Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 s) =
      some tree) : Formats.SExpEncoding.Wat.sexpWat .core3 s tree := by
  cases hf : WatLex.lexFull? .core3 s with
  | some t =>
    have e : t = tree := by simpa [hf] using h
    exact e ▸ WatLex.lexFull?_sound hf
  | none =>
    have e : Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 s = some tree := by
      simpa [hf] using h
    exact Formats.SExpEncoding.Wat.sexpWat_of_fullExec e

theorem textModule?_sound {s : String} {m : Wasm.Module} (h : textModule? s = .ok m) :
    Text.Core.Encodes s m := by
  unfold textModule? at h
  split at h
  · cases h
  · rename_i tree htree
    split at h
    · cases h
    · rename_i m' hm
      cases h
      exact ⟨tree, lexAny_sound htree,
        WatFast.parseF?_sound hm⟩

/-- **The input encodes the module read.** -/
theorem readModule_sound {b : ByteArray} {m : Wasm.Module} (h : readModule b = .ok m) :
    (isBinary b = true ∧ Binary.Core.Encodes b.data.toList m) ∨
      (isBinary b = false ∧ ∃ s, String.fromUTF8? b = some s ∧ Text.Core.Encodes s m) := by
  unfold readModule at h
  split at h
  · rename_i hb
    split at h
    · rename_i m' hd
      cases h
      rw [Silmaril.Wasm.Perf.CoreDecode.decodeF_eq] at hd
      exact .inl ⟨hb, Binary.Core.decode?_sound hd⟩
    · cases h
  · rename_i hb
    split at h
    · cases h
    · rename_i s hs
      exact .inr ⟨by simpa using hb, s, hs, textModule?_sound h⟩

end Silmaril.Wasm.Tools.Gen.Cmd.Input
