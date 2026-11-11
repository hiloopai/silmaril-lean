module

public import Silmaril.Wasm.FX.Asyncify.Tool.Run.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Bytes

/-!
# The verified asyncify tool: theorems

Proofs in `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.*`, all in Isar style (the Isar lint
passes; nothing is left in `Silmaril/Raw`); no `sorry`, no axiom beyond Lean's
(`propext`, `Classical.choice`, `Quot.sound`).

* `asyncify_beh` (`…Tool.Main`): **correctness of the pass**. For a well-formed source program
  `P` (`Prog.WF`), a call of a defined function with the right number of arguments, every
  deterministic host `H` and every source run whose stack keeps the shadow stack below `2 ^ 32`
  (`DepthBound`), the behaviours (`beh`: results with the final host state, traps, divergence) of
  the source system `srcStep P.env H` (suspending import calls answered by the host) and of the
  target system `tgtStep (asyncifyProg P) H` (the asyncified program under the host protocol)
  are equal. Proved by a stuttering simulation (`isSim`, `beh_eq_of_sim`); a suspension is
  matched by unwinding every frame to the shadow stack (`unwind`), the host's answer, and
  rewinding the chain from the export call (`rewinds_base`, `rewinds_step`, `rewinds_chain`).
* `recognize_sound`: the recogniser returns a well-formed program whose machine program is the
  module's (`envOf m = some P.env`).
* `asyncify_eq`, `envOfLax_asyncifyModule`, `globalsOfLax_asyncifyModule`,
  `exportFunc_asyncifyModule`: the output module is read back as `asyncifyProg P`, with the
  protocol's initial globals and the same exported functions.
* `asyncifyBytes_spec`, `asyncifyBytes_correct`: **the tool on bytes**. When `asyncifyBytes`
  succeeds, the input decodes soundly (silmaril-lean's `Binary.Core.decode?_sound`) to a module
  of the fragment, the output bytes encode the output module for the same binary grammar
  (`Binaryen.Exe.encodeModule?_sound`), and `asyncify_beh` holds between them.

What is not proved: that the frame machine (`Silmaril.Wasm.FX.Asyncify.Tool.Machine`) agrees with
silmaril-lean's Core 3.0 `Step` on the fragment (the differential suite checks it against Node),
and the shadow stack's fit in the declared memory (the theorem uses a word memory without bounds;
`DepthBound` only excludes 32-bit wrap-around). See `docs/projects/wasm-binaryen-tooling.md`.
-/
