module

public import Silmaril.Wasm.Component.BinaryAsync.Defs
public import Silmaril.Proofs.Wasm.Component.BinaryAsync.RoundTrip
public import Silmaril.Proofs.Wasm.Component.BinaryAsync.Lawful

/-!
# Component binaries with the async built-ins: verified parsing

* `parseX_encodeX : encodeX c = some b → parseX b = .ok c` (round trip);
* `parseX_sound`: the parser's result is related to the whole input by the grammar;
* `componentXG_functional`: the grammar is unambiguous;
* `encodeX_ofAst`: on a base component the extended encoder is the base encoder, so
  `parseX_encode : encode c = some b → parseX b = .ok (AstX.ofAst c)`: every binary the base
  encoder writes is read by `parseX` as the same component;
* `encodeX_section_ofSection`: the same, section by section;
* `erase_ofAst`: erasing the built-ins of a base component gives it back;
* `parseX_xast`: the bytes `wasm-jco` writes with built-ins (`JcoTool.XAst.encode`) parse
  back to its component.

Proofs in `Silmaril.Proofs.Wasm.Component.BinaryAsync.RoundTrip`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryAsync

open Silmaril.Parse.ByteParse (GrammarE)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.JcoTool (XAst)

/-- **Round trip**: an extended component that the encoder can write is read back. -/
theorem parseX_encodeX {c : AstX} {b : ByteArray} (h : encodeX c = some b) : parseX b = .ok c := by
  unfold encodeX at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, rfl⟩ := h
  unfold parseX
  rw [Silmaril.Parse.ByteParse.size_ofList]
  exact GrammarE.runAll_complete _ (RoundTripX.astX_G _ hl (Nat.lt_succ_self _))

/-- **Soundness**: the parser's result is related to the input by the grammar. -/
theorem parseX_sound {b : ByteArray} {c : AstX} (h : parseX b = .ok c) :
    (componentXG (b.size + 1)).G b.data.toList c :=
  GrammarE.runAll_sound _ h

/-- **Unambiguity**: the grammar relates any input to at most one component. -/
theorem componentXG_functional {k : Nat} {l : Silmaril.Parse.ByteParse.Bytes} {c c' : AstX}
    (h : (componentXG k).G l c) (h' : (componentXG k).G l c') : c = c' := by
  have e := GrammarE.runAll_complete _ h
  rw [GrammarE.runAll_complete _ h'] at e
  cases e; rfl

/-- On base components the extended encoder is the base encoder. -/
theorem encodeX_ofAst (c : Ast) : encodeX (AstX.ofAst c) = encode c := by
  simp only [encodeX, encode, RoundTripX.ast_ofAst]

/-- **Every binary the base encoder writes is read by `parseX`**, as the same component. -/
theorem parseX_encode {c : Ast} {b : ByteArray} (h : encode c = some b) :
    parseX b = .ok (AstX.ofAst c) :=
  parseX_encodeX ((encodeX_ofAst c).trans h)

/-- On a base section the extended encoder is the base encoder. -/
theorem encodeX_section_ofSection (s : Section) :
    EncodeX.section_ (SectionX.ofSection s) = Encode.section_ s :=
  RoundTripX.section_ofSection s

/-- On a base component the extended encoder is the base encoder (as bytes lists). -/
theorem encodeXAst_ofAst (c : Ast) : EncodeX.ast (AstX.ofAst c) = Encode.ast c :=
  RoundTripX.ast_ofAst c

/-- Erasing the built-ins of a base section gives it back. -/
theorem eraseSec_ofSection (s : Section) : (SectionX.ofSection s).erase = s :=
  RoundTripX.erase_ofSection s

/-- Erasing the built-ins of a base component gives it back. -/
theorem erase_ofAst (c : Ast) : (AstX.ofAst c).erase = c := RoundTripX.erase_ofAst c

/-- **The bytes `wasm-jco` writes with built-ins parse back** to its component. -/
theorem parseX_xast {c : XAst} {b : ByteArray} (h : c.encode = some b) :
    parseX b = .ok (ofXAst c) :=
  parseX_encodeX ((xast_encode c).symm.trans h)

end Silmaril.Wasm.Component.BinaryAsync
