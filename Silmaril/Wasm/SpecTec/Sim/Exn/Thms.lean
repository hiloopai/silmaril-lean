module

public import Silmaril.Wasm.SpecTec.Sim.Exn.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.Fields
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.BackwardBlock

/-!
# SpecTec ↔ Core 3.0, family X (exceptions): what is proved

All thirteen exception rules are covered in both directions. The proofs assume the family's
hypotheses `Typing`, `Helpers` and `Decoders` (`Exn/Defs.lean`), which are not discharged here.

**Forward** (Core → SpecTec), at `simEnv B`, from `TypingFacts`, `Typing` and, where store
helpers are called, `Helpers`. Each theorem's type is the matching `Forward` field:
`fwd_throw`, `fwd_throwRefNull`, `fwd_throwRefInstrs`, `fwd_throwRefLabel`, `fwd_throwRefFrame`,
`fwd_throwRefHandlerEmpty`, `fwd_throwRefHandlerCatch`, `fwd_throwRefHandlerCatchRef`,
`fwd_throwRefHandlerCatchAll`, `fwd_throwRefHandlerCatchAllRef`, `fwd_throwRefHandlerNext`,
`fwd_tryTable`, `fwd_handlerVals`. The `otherwise` premise of `throw_ref-handler-next` is
discharged by `otherwiseAt_handlerNext`: none of `Step_read` rules 0–20 fires on a handler whose
first clause does not match.

**Backward** (SpecTec → Core), for any `env` containing the rules. Each theorem has the type of
the matching `Backward` field at its index:

* `Step_read`: `bwd_read_throwRefNull` (12), `bwd_read_throwRefInstrs` (13),
  `bwd_read_throwRefLabel` (14), `bwd_read_throwRefFrame` (15),
  `bwd_read_throwRefHandlerEmpty` (16), `bwd_read_throwRefHandlerCatch` (17),
  `bwd_read_throwRefHandlerCatchRef` (18), `bwd_read_throwRefHandlerCatchAll` (19),
  `bwd_read_throwRefHandlerCatchAllRef` (20), `bwd_read_throwRefHandlerNext` (21),
  `bwd_read_tryTable` (22);
* `Step_pure`: `bwd_pure_handlerVals` (25);
* `Step`: `bwd_step_throw` (10).

The coverage table is in `docs/projects/spectec/README.md`, under family X.
-/
