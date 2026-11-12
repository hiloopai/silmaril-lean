module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Script

/-!
# Round 7, REH route 2: the soundness of the flow check (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow`; see `docs/projects/spectec/README.md`. Definitions are in `Round7/NxFlow/Defs.lean`; the proofs are unrefined copies in
`Silmaril/Raw/…/Round7/NxFlow/`, and the kernel checks in `Silmaril/Proofs/…/Round7/NxFlow/`.

* **`flowSound : NxSound.Task.flowSound`**: in `utf8Env B` with conforming primitives, every
  definition with a parameter entry in `NxTyped.tsigFixed`, applied to conforming arguments,
  returns a conforming value at every fuel.
* The proof, in order:
  * `expAt : ∀ k, ExpAt env k`: the expression members of the evaluator give values satisfying
    `EOk` (inferred type, `nxD`, every `ckE` type) in conforming scopes, given `CallH`;
  * `matchAt : ∀ k, MatchAt env k`: patterns that pass `NxTyped.patTy` keep scopes
    conforming;
  * `callH_clause`: inside a clause, calls conform, given `NxSound.DefsVT` below the fuel; the
    static mode of a generic call is its runtime mode (`tpFill_eq`), and conformance agrees
    between a clause's signature and `sigX` (`vtB_clauseSig`);
  * `entry_go`, `prems_ok`, `clause_ok`, `tryClauses_ok`: a clause's arguments, premises and
    body;
  * `defsVT_all`: by induction on fuel, for every environment with `EnvFacts`;
  * `envFacts_utf8Env`: `utf8Env B` has them, from `NxTyped.flowItems_fixed` and the side
    conditions below.
* **Side conditions** the flow check does not state, checked in the kernel on the fixed script
  (`auxItems_fixed`, ten slices) and on the signatures (`sigsAux_fixed`): iteration domains bind
  distinct variables; type arguments are a single name or free of `X`; clause patterns align
  with parameters; reachable definitions have no grammar parameter and at most the type
  parameter `X`; generic definitions have no definition parameters and pass none; no type is
  named `X`; the signature entries do not mention `X`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

/-- **`Round7.NxSound.Task.flowSound` holds.** -/
theorem flowSound : NxSound.Task.flowSound := flowSound'

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.flowSound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms flowSound

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.auxItems_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms auxItems_fixed

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
