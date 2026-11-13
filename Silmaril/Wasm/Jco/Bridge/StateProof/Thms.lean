module

public import Silmaril.Wasm.Jco.Bridge.StateFix.Thms
public import Silmaril.Wasm.Jco.Bridge.Thms
public import Silmaril.Games.Answer.Thms
import Silmaril.Proofs.Wasm.Jco.Bridge.StateProof.Basic

/-!
# The stateful component bridge: proved

**`simpleComp_stateS`** proves the restated target `SimpleCompStateS`
(`Silmaril.Wasm.Jco.Bridge.StateFix`): on memory-free worlds the IR strategy of the adaptor-style
component `Fuse.simpleComp [] (Meta.iface md) m` over a stateful module `m` is the strategy of
the machine `compLTSS md m`, which answers each question by `compAnsS md m` and keeps the state
the core instance has after the call (also when the result does not lift).

Consequences:

* **`simpleComp_state_lift`**: the original statement of `SimpleCompState` holds on every
  module whose returned calls lift (`LiftTotal`), through `simpleComp_state_of_S`.
* **`not_simpleComp_state`**: the original `SimpleCompState` is false (the counterexample
  `bumpMod`, through `not_simpleComp_state_of_S`). It stays frozen, unchanged, as the
  documented mis-statement.

The proof (`Silmaril.Proofs.Wasm.Jco.Bridge.StateProof.Basic`):

1. the strategy is the module's machine between the forwarding of the empty imports and one
   handler `topH` (glue code and `canon lift`s): the first environment extension is a right
   projection of a pairing (`Strategy.pair_comp_ofHom_inr`), the rest are handler identities
   (`simpleComp_denU_state`);
2. the module's machine `SMod.lts` is the answering machine of `SMod.ans` (`lts_eq`), so with
   the handler above it is the answering machine of `topH.overAns m.ans`
   (`Strategy.ofAns_comp_ofHandler`) and the forwarding below it disappears
   (`Strategy.ofHandler_comp_ofAns`);
3. `topH.overAns m.ans = compAnsS md m` by evaluation (`overAns_eq`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Bridge

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco (Meta)

open Silmaril.Proofs.Wasm.Jco.Bridge.StateProof in
/-- **The stateful component bridge** (`SimpleCompStateS`, proved). -/
theorem simpleComp_stateS : SimpleCompStateS := by
  intro σ md m hf
  rw [simpleComp_denU_state, lts_eq, Strategy.ofAns_comp_ofHandler,
    Strategy.ofHandler_comp_ofAns, overAns_eq md m (memFree_result hf), compLTSS, ansLTS_eq]

/-- **The original statement on modules whose results lift.** -/
theorem simpleComp_state_lift {σ : Type} (md : Meta) (m : SMod σ) (hf : md.memFree = true)
    (hl : LiftTotal md m) :
    (Silmaril.Wasm.Jco.Fuse.simpleComp [] (Meta.iface md) m).denU
        (Silmaril.Wasm.Jco.Fuse.baseSem (smodSem σ)) = Strategy.ofLTS (compLTS md m) :=
  simpleComp_state_of_S simpleComp_stateS md m hf hl

/-- **The original target is false.** -/
theorem not_simpleComp_state : ¬ SimpleCompState :=
  not_simpleComp_state_of_S simpleComp_stateS

end Silmaril.Wasm.Jco.Bridge

/--
info: 'Silmaril.Wasm.Jco.Bridge.simpleComp_stateS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Bridge.simpleComp_stateS

/--
info: 'Silmaril.Wasm.Jco.Bridge.not_simpleComp_state' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Bridge.not_simpleComp_state
