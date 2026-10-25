# WebAssembly specification notices and provenance

This software includes material copied from or derived from the
[WebAssembly Specification](https://github.com/WebAssembly/spec/tree/608711107b7f1edb13efd57b7d79b49477462d36).
The formalization source revision is
`608711107b7f1edb13efd57b7d79b49477462d36`; the public source paths and SHA-256
hashes are retained in [the Core 2.0](../../specs/wasm/core-2.0.json) and
[Core 3.0](../../specs/wasm/core-3.0.json) source inventories. The original
specification files and the SpecTec implementation are not bundled.

Upstream document attribution: **Copyright (c) 2017-2025, WebAssembly Community Group**;
editor Andreas Rossberg. This is the attribution recorded in the pinned
[`document/core/conf.py`](https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/document/core/conf.py).

The W3C [short-notice form](https://www.w3.org/Consortium/Legal/2015/copyright-software-short-notice)
also states:

> This work is distributed under the W3C® Software and Document License [1]
> in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
> the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
>
> [1] http://www.w3.org/Consortium/Legal/copyright-software

The specification and its document use the **W3C Software and Document Notice
and License**, retained in full as [core-LICENSE.txt](core-LICENSE.txt).
[document-LICENSE.txt](document-LICENSE.txt) is the upstream document license
pointer. [LICENSE.txt](LICENSE.txt) is the unmodified root license index at the
formalization source revision.

That index omitted the then-new `specification/` directory. Upstream explicitly
clarified its existing document license in merged
[PR #2277](https://github.com/WebAssembly/spec/pull/2277), on 2026-10-13:
`specification/` contains material formerly in the document and uses the same
W3C license. [clarified-LICENSE.txt](clarified-LICENSE.txt) retains the exact
index from merge commit
[`c794c6a678858b9c6be9f055c0abee51fe0b8ba6`](https://github.com/WebAssembly/spec/blob/c794c6a678858b9c6be9f055c0abee51fe0b8ba6/LICENSE).
This later license clarification does **not** change the formalization source
revision. SpecTec specification files are distinct from the Apache-licensed
SpecTec implementation.

The included Lean files explicitly identifying direct specification
transcriptions or generated tables include:

| Included path prefix | Files | Upstream material |
| --- | --- | --- |
| `Silmaril/Wasm/Binary/Core/` | `Opcodes.lean` (mechanically generated), `Instructions.lean`, `Types.lean`, `Modules.lean` | Core 3.0 `5.2-binary.types`, `5.3-binary.instructions`, `5.4-binary.modules` |
| `Silmaril/Wasm/V2/` | `Types.lean`, `Ops.lean`, `Instructions.lean`, `Modules.lean` | Core 2.0 `1-syntax.spectec` |
| `Silmaril/Wasm/V2/Validation/` | `Context.lean`, `Types.lean`, `Instructions.lean`, `Modules.lean` | Core 2.0 `6-typing.spectec` |
| `Silmaril/Wasm/Validation/` | `DefTypes.lean`, `Context.lean` | Core 3.0 `1.2-syntax.types`, `2.0-validation.contexts` |
| `Silmaril/Wasm/Execution/Core/` | `Runtime.lean`, `Store.lean`, `Typing/Config.lean`, `Exec/ConstEval.lean` | Core 3.0 execution configurations, accessors, typing and instruction rules |
| `Silmaril/Wasm/Numerics/` | `Vector.lean`, `Relaxed.lean` | Specification vector functions and numeric prose |
| `Silmaril/Wasm/Text/Core/` | `Types.lean` | Core 3.0 text grammar and identifier contexts |
| `Silmaril/Formats/SExp/` | `EncodingWatDefs.lean` | Core 3.0 lexical grammar and Wasm 1.0 text specification |

The source headers document further specification references and deviations.
The Lean versions change the representation language, flatten indexed syntax,
make contexts and side conditions explicit, and add executable checks and
proofs. Corrections and differing interpretations are documented in the source.
**Copyright (c) 2026 Silmaril contributors** for these modifications and original
contributions. MIT applies to original contributions; it does not replace the
upstream rights and notices attached to specification-derived material.

[APACHE.txt](APACHE.txt) retains the exact Apache 2.0 text from the pinned
[`interpreter/LICENSE`](https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/interpreter/LICENSE).
It applies to the reference-interpreter material, including the quoted
`interpreter/valid/valid.ml` extracts in
`Silmaril/Wasm/V2/Validation/Instructions.lean`; it is not substituted for the
W3C license of the specification. No upstream interpreter implementation or
paper PDF is bundled.
