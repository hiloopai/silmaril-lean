module

public import Silmaril.Proofs.Wasm.Logic.Core.Call
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.Wasm.Logic.Arith.Thms

/-!
# A weakest-precondition calculus for Wasm Core 3.0 code: rules

`WP P host s f code Q` (`Silmaril.Wasm.Logic.Core.Defs`) is the existential
weakest precondition: some run of `code` from `s, f` reaches a final form whose
outcome (`normal`, `br`, `ret`, `trap`, `throw`, `tail`) satisfies `Q`. Every rule
holds for **every profile** `P` (deterministic or not) and **every host
relation** `host`; nothing assumes a deterministic numeric profile.

The rules (proofs in `Silmaril.Proofs.Wasm.Logic.Core.{Context,Rules,Straight,Call}`):

* runs in contexts: `Step.ctx`, `Steps.ctx`, `Steps.append`, `Steps.label`,
  `Steps.handler`, `Steps.frame`;
* structural: `WP.mono`, `WP.steps`, `WP.step`, `wp_vals`, `wp_seq` (Wasm Logic
  `[seq]`), `wp_prefix` (stack framing);
* final forms: `wp_br`, `wp_return`, `wp_trap`, `wp_throwing`;
* control: `wp_brIf_true`, `wp_brIf_false`, `wp_brIf_bool32`, `wp_brTable_lt`,
  `wp_brTable_ge`, `wp_label`, `wp_block` (`[block]`), `wp_loop` (`[loop]`, total
  correctness with a measure-indexed invariant), `wp_if_true`, `wp_if_false`, and
  the `_cons` forms used by the tactics;
* exceptions: `wp_throw`, `wp_throwRef_null`, `wp_handler`, `wp_tryTable`,
  `wp_tryTable_cons`;
* straight-line code: `exec1_spec`, `exec_sound`, `wp_exec`, `wp_exec₀`,
  `wp_exec_all`, `wp_exec_vals`;
* functions: `FuncSpec.of_body` (`[call]`/`callcl`), `wp_call` (the call rule),
  `wp_callRef`, `wp_callRef_null`, `wp_callIndirect`, `wp_returnCall`,
  `wp_returnCallRef`, `funcPost_tail` (tail calls), `FuncSpec.invoke`,
  `FuncSpec.conseq`;
* memory: `load_eq`, `store_eq`, `load_store_same`, `load_store_disjoint`,
  `bytesAt_store_disjoint` (`Silmaril.Wasm.Logic.Memory.Thms`); arithmetic simp
  lemmas (`Silmaril.Wasm.Logic.Arith.Thms`).

Soundness is by construction: `WP` is defined from silmaril-lean's small-step
relation `Silmaril.Wasm.Execution.Core.Steps`, so each rule is a lemma about
runs. The adequacy statement a client uses is `FuncSpec.invoke`: a specification
proved by these rules yields a run of `$invoke` to the specified results.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Adequacy of function specifications.** A specification proved from the body
with the rules of the calculus gives a run of the embedder's `$invoke` to results
satisfying the postcondition, in every profile and for every host. -/
theorem funcSpec_invoke_of_body {a : Nat} {fi : FuncInst H} {code : Func}
    {ps rs : Ty (.list .val)} {Pre : Store H → List Val → Prop}
    {Post : Store H → List Val → Store H → List Val → Prop}
    (hfi : ∀ s args, Pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hlen : ∀ s args, Pre s args → args.length = ps.length)
    (hbody : ∀ s args, Pre s args →
      WP P host s (Frame.forCall fi.module args code.locals) (expression code.body)
        (funcPost P host rs.length (Post s args)))
    {s : Store H} {args : List Val} (hpre : Pre s args) :
    ∃ s' res, Steps P host (invoke s a args) ⟨s', {}, vals res⟩ ∧ Post s args s' res :=
  (FuncSpec.of_body hfi hcode he hlen hbody).invoke hpre

end Silmaril.Wasm.Logic.Core
