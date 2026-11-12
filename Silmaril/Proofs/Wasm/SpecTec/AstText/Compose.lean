module

public import Silmaril.Wasm.SpecTec.AstText.Defs

/-!
# `--ast` text to IL: composing the reader with the decoder

The verified reader `parseStream?` is sound and complete for `streamRel`
(`SExp/ParseVerified.lean`), and `decodeScript?` is sound and complete for `IL.scriptRel`
(`IL/Encoding.lean`); their composite `importAstText?` is therefore sound and complete for the
composite relation `AstTextRel`. Both layers are functional, so a text spells at most one
script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.AstText

open Silmaril (EncRel)
open Silmaril.SpecTec
open Silmaril.SpecTec.SExp (parseStream? astFile PrintableList)

theorem astTextRel_iff {s : String} {sc : IL.Script} :
    AstTextRel s sc ↔ streamRel s (IL.scriptS sc) :=
  ⟨fun ⟨_, h, he⟩ => he ▸ h, fun h => ⟨_, h, rfl⟩⟩

/-- `AstTextRel` is the existing composite `IL.astRel`. -/
theorem astTextRel_eq_astRel : AstTextRel = IL.astRel := rfl

theorem importAstText?_eq_some_iff {s : String} {sc : IL.Script} :
    importAstText? s = some sc ↔ ∃ es, parseStream? s = some es ∧ IL.decodeScript? es = some sc := by
  simp [importAstText?, Option.bind_eq_some_iff]

theorem importAstText?_sound : AstTextRel.DecoderSound importAstText? := by
  intro s sc h
  obtain ⟨es, hp, hd⟩ := importAstText?_eq_some_iff.mp h
  exact ⟨es, SExp.streamRel_decoderSound s es hp, IL.decodeScript?_sound es sc hd⟩

theorem importAstText?_complete : AstTextRel.DecoderComplete importAstText? := by
  rintro s sc ⟨es, hs, hsc⟩
  exact importAstText?_eq_some_iff.mpr
    ⟨es, SExp.streamRel_decoderComplete s es hs, IL.decodeScript?_complete es sc hsc⟩

theorem astTextRel_eq_ofDecoder : AstTextRel = EncRel.ofDecoder importAstText? := by
  funext s sc
  exact propext ⟨importAstText?_complete s sc, importAstText?_sound s sc⟩

theorem astTextRel_functional : AstTextRel.Functional := by
  rintro s sc sc' ⟨es, hs, hsc⟩ ⟨es', hs', hsc'⟩
  have hes : es = es' := streamRel_functional hs hs'
  exact IL.scriptS_injective (hsc.trans (hes.trans hsc'.symm))

theorem astTextRel_astFile_of_printable (w : Nat) (sc : IL.Script)
    (h : PrintableList (IL.scriptS sc)) : AstTextRel (astFile w (IL.scriptS sc)) sc :=
  ⟨_, streamRel_astFile w _ h, rfl⟩

theorem importAstText?_astFile_of_printable (w : Nat) (sc : IL.Script)
    (h : PrintableList (IL.scriptS sc)) : importAstText? (astFile w (IL.scriptS sc)) = some sc :=
  importAstText?_complete _ _ (astTextRel_astFile_of_printable w sc h)

theorem astTextRel_astFile (w : Nat) (sc : IL.Script) (h : IL.AllToken (IL.realsScript sc)) :
    AstTextRel (astFile w (IL.scriptS sc)) sc :=
  astTextRel_astFile_of_printable w sc (IL.printableList_scriptS sc h)

theorem importAstText?_astFile (w : Nat) (sc : IL.Script) (h : IL.AllToken (IL.realsScript sc)) :
    importAstText? (astFile w (IL.scriptS sc)) = some sc :=
  importAstText?_astFile_of_printable w sc (IL.printableList_scriptS sc h)

/-- Whatever the reader returns satisfies the printability side condition, so the round trip
applies to it with no further obligation. -/
theorem allToken_of_importAstText? {s : String} {sc : IL.Script}
    (h : importAstText? s = some sc) : IL.AllToken (IL.realsScript sc) := by
  obtain ⟨es, hp, hd⟩ := importAstText?_eq_some_iff.mp h
  exact IL.allToken_realsScript_of_lexesStream (SExp.streamRel_decoderSound s es hp) hd

/-- Reading an imported text, printing it at any width and reading again gives the same script. -/
theorem importAstText?_reprint {s : String} {sc : IL.Script} (w : Nat)
    (h : importAstText? s = some sc) : importAstText? (astFile w (IL.scriptS sc)) = some sc :=
  importAstText?_astFile w sc (allToken_of_importAstText? h)

theorem importAstBytes?_sound : AstBytesRel.DecoderSound importAstBytes? := by
  intro b sc h
  cases hs : String.fromUTF8? b with
  | none => simp [importAstBytes?, hs] at h
  | some s =>
    simp only [importAstBytes?, hs] at h
    exact ⟨s, hs, importAstText?_sound s sc h⟩

theorem importAstBytes?_complete : AstBytesRel.DecoderComplete importAstBytes? := by
  rintro b sc ⟨s, hs, hr⟩
  simp [importAstBytes?, hs, importAstText?_complete s sc hr]

theorem astBytesRel_functional : AstBytesRel.Functional := by
  rintro b sc sc' ⟨s, hs, hr⟩ ⟨s', hs', hr'⟩
  rw [hs] at hs'
  cases hs'
  exact astTextRel_functional hr hr'

end Silmaril.Wasm.SpecTec.AstText
