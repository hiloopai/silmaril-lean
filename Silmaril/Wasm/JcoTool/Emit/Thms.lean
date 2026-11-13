module

public import Silmaril.Wasm.JcoTool.Emit.Defs

/-!
# Output components without built-ins are in the verified grammar

`XAst.encode_toAst`: when an output component has no section of async built-ins
(`XAst.toAst c = some a`), its bytes are the encoding of `a` by the verified grammar's
encoder, so the verified parser reads them back as `a` (`Binary.parse_encode`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool

open Silmaril.Wasm.Component.Binary

theorem encodeAll_toSections : ∀ {xs : List XSection} {ss : List Section},
    XSection.toSections xs = some ss → XSection.encodeAll xs = Encode.sections ss
  | [], ss, h => by
    have e : ss = [] := by simpa [XSection.toSections] using h.symm
    rw [e]
    simp [XSection.encodeAll, Encode.sections]
  | .sec s :: xs, ss, h => by
    cases hx : XSection.toSections xs with
    | none => simp [XSection.toSections, hx] at h
    | some ss' =>
      have e : ss = s :: ss' := by simpa [XSection.toSections, hx] using h.symm
      rw [e]
      simp [XSection.encodeAll, Encode.sections, XSection.encode, encodeAll_toSections hx]
  | .builtins _ :: _, _, h => by simp [XSection.toSections] at h

/-- Without built-ins, the output's bytes are those of the verified encoder. -/
theorem XAst.encode_toAst {c : XAst} {a : Ast} (h : c.toAst = some a) : c.encode = Silmaril.Wasm.Component.Binary.encode a := by
  cases hs : XSection.toSections c.sections with
  | none => simp [XAst.toAst, hs] at h
  | some ss =>
    have e : a = .mk ss := by simpa [XAst.toAst, hs] using h.symm
    rw [e]
    simp only [XAst.encode, Silmaril.Wasm.Component.Binary.encode, Encode.ast, encodeAll_toSections hs]
    cases Encode.sections ss <;> rfl

end Silmaril.Wasm.JcoTool
