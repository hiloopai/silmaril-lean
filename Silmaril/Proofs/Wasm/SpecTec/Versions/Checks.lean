module

public import Silmaril.Proofs.Wasm.SpecTec.Versions.Import
public import Silmaril.Wasm.SpecTec.AstText.Thms
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Valid
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Valid
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Crosscheck
import all Silmaril.Proofs.Wasm.SpecTec.Versions.Import

/-!
# The main streams through the pinned streams' build-time checks

The checks the pinned streams pass, run unchanged on the streams of `WebAssembly/spec@e7a9df7c`.
Each is compiled code run at elaboration time (a failure fails the build), not a kernel theorem:

* `spectec_check_stream`: the **verified** reader (`importAstText?_sound`/`_complete`) reads each
  file as the imported script, and `astFile 80` reprints it byte for byte;
* `Sem.checkStreamFile`: the (typing-free) well-formedness checker of `Sem/Valid.lean` accepts
  each stream (scope, kind, arity, shape, declarations);
* `spectec_crosscheck`: the instruction constructors of the main wasm-3.0 stream are the 116
  `(tag, payload)` shapes of `Silmaril.Wasm.SpecTec.{instruction,administrative}Schemas`, which
  `sil spectec` generated from the *pinned* stream: the instruction syntax did not change.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Versions

open Silmaril.SpecTec

spectec_check_stream Specs.mainWasm10 against "specs/spectec/e7a9df7c/wasm-1.0.ast"
spectec_check_stream Specs.mainWasm20 against "specs/spectec/e7a9df7c/wasm-2.0.ast"
spectec_check_stream Specs.mainWasm30 against "specs/spectec/e7a9df7c/wasm-3.0.ast"

#eval Silmaril.SpecTec.Sem.checkStreamFile "specs/spectec/e7a9df7c/wasm-1.0.ast"
#eval Silmaril.SpecTec.Sem.checkStreamFile "specs/spectec/e7a9df7c/wasm-2.0.ast"
#eval Silmaril.SpecTec.Sem.checkStreamFile "specs/spectec/e7a9df7c/wasm-3.0.ast"

spectec_crosscheck "specs/spectec/e7a9df7c/wasm-3.0.ast"
  with Silmaril.Wasm.SpecTec.instructionSchemas
  and Silmaril.Wasm.SpecTec.administrativeSchemas

end Silmaril.Wasm.SpecTec.Versions
