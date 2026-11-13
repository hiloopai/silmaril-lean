module

public import Silmaril.Wasm.Spec.Env.Defs
public import Silmaril.Proofs.Wasm.Spec.Env.Basic

@[expose] public section

/-!
# Model variants: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Env.Basic`.

* `withEnv_traces`: a program with an environment (b) has the traces of the program (a) that the
  environment (c) allows: (b) is the product of (a) and (c).
* `Semantics.chaosEnv S : SemMap S S.withEnv` (a program against the chaotic environment) gives
  the comorphism `S.chaosEnv.coHom L : Inst.CoHom (inst L S.withEnv) (inst L S)` (sentences
  unchanged, models of (a) mapped to models of (b)); `models_assume_top_iff`.
* `models_assume_iff`: **assume-guarantee sentences** `(K, φ)` about programs are exactly the
  sentences `φ` about programs with environment `K`; `assume_ofTrace_iff`: for per-trace
  logics, `(K, φ)` is the per-trace implication "if the import events are allowed by `K` then
  `φ`".
* Transfer, for antitone logics (e.g. every per-trace logic): `models_withEnv_of_models`
  (verified for every environment ⇒ verified against `K`) and `models_withEnv_of_envSem`
  (an environment property holds of every program run against that environment).
* Environments (c): `envSem_iretPost_iff` (an environment property is a property of its
  import-event sequences), `agreeEnv_iretPost` (a host machine all of whose answers to `i` satisfy
  `Q` meets "import `i` only returns `Q`").
* **Closed-world grounding of assume-guarantee specifications** (every profile):
  `retPost_closed_world_env`: if a Wasm program meets the return postcondition of export `j`
  against the environment specification of a host machine `L` (variant (b)), every terminating
  Core behaviour of a call of `j` against `L` (product of Core reduction with `L`'s host
  machine) satisfies it.
-/
