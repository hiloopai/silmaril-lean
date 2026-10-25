# Binaryen source-derived definitions

The following Lean files explicitly identify their Binaryen sources at
version_133, commit
[`fba5005a132d85d578be5bd010e0487ed8e2ce3e`](https://github.com/WebAssembly/binaryen/tree/fba5005a132d85d578be5bd010e0487ed8e2ce3e):

| Included Lean file | Upstream source | Original copyright notice |
| --- | --- | --- |
| `Silmaril/Wasm/Binaryen/Effects.lean` | [`src/ir/effects.h`](https://github.com/WebAssembly/binaryen/blob/fba5005a132d85d578be5bd010e0487ed8e2ce3e/src/ir/effects.h) | Copyright 2017 WebAssembly Community Group participants |
| `Silmaril/Wasm/Binaryen/Named.lean` | [`src/wasm.h`](https://github.com/WebAssembly/binaryen/blob/fba5005a132d85d578be5bd010e0487ed8e2ce3e/src/wasm.h) | Copyright 2015 WebAssembly Community Group participants |

Both upstream source headers carry the following notice:

> Licensed under the Apache License, Version 2.0 (the "License");
> you may not use this file except in compliance with the License.
> You may obtain a copy of the License at
>
> http://www.apache.org/licenses/LICENSE-2.0
>
> Unless required by applicable law or agreed to in writing, software
> distributed under the License is distributed on an "AS IS" BASIS,
> WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
> See the License for the specific language governing permissions and
> limitations under the License.

[LICENSE.txt](LICENSE.txt) is the exact upstream root license at that revision.
Its final FP16 dependency note concerns upstream Binaryen; no FP16 source is
bundled here.

The Lean transcriptions change the representation and implementation language,
restrict the supported profile and add semantic definitions, executable checks
and correctness proofs. Those changes are documented in the source headers.
Copyright (c) 2026 Silmaril contributors for modifications and original
contributions. MIT applies to original contributions and does not replace the
upstream rights and notices attached to Binaryen-derived material.

The full Binaryen C++ implementation and upstream fixture corpus are not
bundled. The separately installed Binaryen executables are optional independent
test oracles.
