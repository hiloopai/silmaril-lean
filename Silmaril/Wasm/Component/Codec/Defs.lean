module

public import Silmaril.Wasm.Component.BinaryP3.Strict.Defs
public import Silmaril.Wasm.Component.BinaryP3.Encode.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
# The component binary codec

One entry point for reading and writing component binaries. The codec is the grammar of
`design/mvp/Binary.md` at component-model `d095e2f` (`Silmaril.Wasm.Component.BinaryP3`), every
canonical built-in included, with the three extra rules `wasm-tools` 1.262.0 enforces
(`BinaryP3.StrictOk`: core module sections decode, `outer` alias sorts, attribute
uniqueness):

* `Codec.Ast`: component syntax (`BinaryP3.Ast`);
* `Codec.decode`: strict parsing (`BinaryP3.parseStrict`), the decoder the facade recommends;
  `Codec.decodeLax`: the grammar alone (`BinaryP3.parse`);
* `Codec.encode`: the encoder (`BinaryP3.encode`; fails only on numbers or lengths of `2 ^ 32`
  or more).

The component tools read binaries through `Codec.decodeLax` (`Silmaril.Wasm.Tools.Component`).
WIT package binaries, whose type sections the WIT decoder reads in the syntax of `Binary.md` at
`8505ba7`, go through `Codec.decodeMvp` and `Codec.encodeMvp` (the `mvp` variant below, which
`decodeLax` extends: `Codec.decodeLax_of_mvp`).
This module imports only the grammar of `Binary.md` and its encoder, so a tool that decodes
through the facade does not depend on the other decoders. Those are **variants**
(`Codec.Variant`, in `Silmaril.Wasm.Component.Codec.Variant.Defs`), each a verified parser for its
own grammar, kept because tools and proofs use them:

* `mvp`: `Binary.parse`, `Binary.md` at `8505ba7` without the async built-ins (reported as
  unknown `canon` tags), with its encoder `Binary.encode`;
* `async`: `BinaryAsync.parseX`, `mvp` plus the built-ins that `wasm-jco` writes
  (`BinaryAsync.CanonX`), with its encoder `BinaryAsync.encodeX`;
* `lax` and `strict`: `Codec.decodeLax` and `Codec.decode`;
* `gc`: `BinaryGC.parse`, WebAssembly 3.0 core types (`core:rectype`, sub types) and wasmtime's
  GC canonical options, read into the reference syntax; no encoder.

`Variant.accepts v b` says whether variant `v` reads `b`. How the variants relate is in
`Silmaril.Wasm.Component.Codec.Thms`: proved are `mvp ⊆ lax` (with the embedding `Ast.ofV0`),
`strict ⊆ lax`, and that `async` and `lax` read every binary `Binary.encode` writes (as the
embedded component). Refuted, each by a six-byte section that one reads and the other rejects:
`async ⊆ lax` (`dropAsyncBytes`: `wasm-jco`'s `resource.drop async`, tag `0x07`, which
`Binary.md` at `d095e2f` no longer has) and `lax ⊆ gc` (`resourceF32Bytes`: a resource type
represented as `f32`, which the grammar admits and the reference syntax of `gc` cannot hold).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Codec

/-- Component syntax: the abstract syntax of `Binary.md` at component-model `d095e2f`. -/
abbrev Ast : Type := BinaryP3.Ast

/-- Decoding errors. -/
abbrev Error : Type := Silmaril.Parse.ByteParse.Error

/-- **The decoder**: the grammar of `Binary.md`, then the rules `BinaryP3.StrictOk`. -/
def decode (b : ByteArray) : Except Error Ast := BinaryP3.parseStrict b

/-- The grammar of `Binary.md` alone, without the rules of `decode`. -/
def decodeLax (b : ByteArray) : Except Error Ast := BinaryP3.parse b

/-- **The encoder.** -/
def encode (c : Ast) : Option ByteArray := BinaryP3.encode c

/-- The `mvp` variant's decoder (`Binary.parse`): `Binary.md` at `8505ba7`, without the async
built-ins; the syntax the WIT package decoder reads. -/
def decodeMvp (b : ByteArray) : Except Error Binary.Ast := Binary.parse b

/-- The `mvp` variant's encoder (`Binary.encode`). -/
def encodeMvp (c : Binary.Ast) : Option ByteArray := Binary.encode c

end Silmaril.Wasm.Component.Codec
