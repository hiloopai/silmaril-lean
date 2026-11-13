module

public import Silmaril.Wasm.JcoTool.KCoreEmit.Defs

/-!
# Core WAT with a certificate: the text, the module it denotes and its bytes

Some of the core modules the tools print are written by text templates that no theorem covers
(`Streams.Kernel.KM.coreWat`, the tee template of `wasm-streams-gen`). Proving each template
correct for all inputs would need a proof per template; instead every text such a tool prints
carries a certificate checked when it is printed:

* **`certify t`**: silmaril's sound WAT reader (`KCoreEmit.parseWat`: the full lexer, then
  `Wat.parseSupported?`) reads `t` as a Core 3.0 module `m`, and silmaril's verified encoder
  (`Binaryen.Exe.encodeModule?`) encodes `m`; the result is `m` and its bytes, or an error.

`WatCert.Thms`: the text denotes `m` in the Core 3.0 text grammar, the bytes encode `m` in the
Core 3.0 binary grammar, and whatever silmaril's decoder reads from the bytes is `m`. A tool
that prints a text only after `certify` accepted it, and writes the bytes `certify` returned,
prints and writes one module, fixed by the grammars. This is translation validation per
output: a template whose text falls outside the reader's fragment is refused, not proved.
What the module *does* is a separate question (the realise part of `docs/projects/wasm-components.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.WatCert

open Silmaril.Wasm

/-- **The certificate of a core WAT text**: the module silmaril's sound reader reads from it,
and that module's bytes by silmaril's verified encoder. -/
def certify (t : String) : Except String (Module × ByteArray) :=
  match KCoreEmit.parseWat t with
  | none => .error "the text is outside the fragment of silmaril's WAT reader"
  | some m =>
    match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
    | .ok bs => .ok (m, ⟨bs.toArray⟩)
    | .error e => .error ("the module does not encode: " ++ e)

/-- The text, if it has a certificate. -/
def checkedText (t : String) : Except String String :=
  (fun _ => t) <$> certify t

/-- The bytes of the module the text denotes, if it has a certificate. -/
def checkedBytes (t : String) : Except String ByteArray :=
  (·.2) <$> certify t

end Silmaril.Wasm.JcoTool.WatCert
