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

## Verified stages and the SSA optimizer

The following Lean files name Binaryen passes and describe the rewrites of those passes that
they verify. They contain no Binaryen source: each is an original Lean implementation of a
restricted subrule, with its own soundness proof.

| Included Lean files | Binaryen pass named | Relation to upstream |
| --- | --- | --- |
| `Silmaril/Wasm/Binaryen/NeutralOps/{Defs,Thms}.lean`, `Silmaril/Wasm/Binaryen/EqzPair/{Defs,Thms}.lean` | `OptimizeInstructions` (`src/passes/OptimizeInstructions.cpp`) | one subrule each, reimplemented |
| `Silmaril/Wasm/Binaryen/TeeForm/{Defs,Thms}.lean` | `SimplifyLocals` | one subrule, reimplemented |
| `Silmaril/Wasm/Binaryen/DropGet/{Defs,Thms}.lean` | `Vacuum` | one subrule, reimplemented |
| `Silmaril/Wasm/Binaryen/RseLine/{Defs,Thms}.lean` | `RedundantSetElimination` | one subrule, reimplemented |
| `Silmaril/Wasm/Binaryen/Coverage/Defs.lean` | the default `-O2`/`-Os` pass list of version_133 | a status table that names upstream passes |
| `Silmaril/Wasm/Binaryen/{Pipeline,Driver,DriverSpec}/{Defs,Thms}.lean` | `wasm-opt` presets and pass names | slot positions of the stages in the presets |
| `Silmaril/Wasm/FnInst/Opt/**` | `OptimizeInstructions`, `Vacuum`, `SimplifyLocals` | rule tables that name the pass each rule comes from |

## Test data produced with Binaryen version_123

`tools/wasm-egraph/corpus/*.binaryen-{O1,O2,O3,Os}.wasm` and the `*.<pass>.wasm` files next
to them are outputs of Binaryen's `wasm-opt` version_123 on the inputs in the same
directory. That release binary is
`binaryen-version_123-x86_64-linux.tar.gz`, archive SHA-256
`e959f2170af4c20c552e9de3a0253704d6a9d2766e8fdb88e4d6ac4bae9388fe`, `bin/wasm-opt` SHA-256
`d66c6724c07334155720eb2def29c434dcaaf741ce859b4f7f389e22674f9c4a`. The translation-validation
tests check them. `tools/wasm-egraph/tests/gen-tv.sh` regenerates them when that binary is
installed. It is the only use of version_123; every other Binaryen reference here is to
version_133, as above.
