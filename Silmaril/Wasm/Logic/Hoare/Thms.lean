module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Module

/-!
# An every-run program logic for Wasm Core 3.0: rules and soundness

The logic (`Silmaril.Wasm.Logic.Hoare.Defs`) is a step-indexed every-run weakest
precondition `HWP P host s f code Q` over pinned silmaril-lean's Core 3.0
small-step semantics `Silmaril.Wasm.Execution.Core.Step`, for **every profile**
`P` and **every host relation** `host`. Postconditions are indexed by outcome
(`normal`, `br`, `ret`, `trap`, `throw`, `tail`).

Soundness (`Silmaril.Proofs.Wasm.Logic.Hoare.Adequacy`):

* `HWP.sound`: partial correctness and safety (every reachable configuration can
  step or has exited with an outcome satisfying the postcondition);
  `HWP.sound_vals`, `HWP.sound_trap`, `HWP.sound_throw` for terminal runs;
* `TSafe.not_diverges`: total correctness (no infinite run) for the inductive
  `TWP`; `TWP.hwp`;
* `FSpecValid.invoke_vals`, `FSpecValid.invoke_trap`, `FSpecValid.invoke_safe`:
  valid function specifications hold for every run of the embedder's `$invoke`.

Structural rules: `Safe.seq`/`HWP.seq` (sequencing), `Safe.label`/`HWP.label`,
`Safe.handler`/`HWP.handler` (exception handlers with catch-clause dispatch),
`Safe.frame` (function frames, including tail calls out of the frame),
`Safe.post_mono`/`HWP.mono` (consequence), `Safe.mono` (index), `Safe.step_inv`.

Instruction rules: `Safe.head`/`HWP.head` for every inert plain instruction
(through silmaril-lean's `Det.Head` relation), and dedicated rules `HWP.localGet`,
`HWP.localSet`, `HWP.intBinOp`, `HWP.refNull`, `HWP.structNew`, `HWP.structGet`,
`HWP.structGet_null`, `HWP.structSet`, `HWP.memoryGrow`, `Safe.block`/`HWP.block`,
`HWP.loop`, `HWP.if_`, `HWP.brIf`, `HWP.brOnNull`, `HWP.throw`, `HWP.tryTable`.

Calls and contexts: `FSpecAt.of_body` (a specification from the body),
`Safe.call`/`Safe.callIdx` (the call rule, for every `CALL_REF` form),
`framePostK_tail`/`Safe.returnCallIdx` (tail calls), `Ctx.valid_of_step` (mutual
recursion by Löb induction), `CtxSat`, `CtxSat.valid`, `CtxSat.link` (guarded
validity of specification contexts over the closed-world store semantics; open
modules are `Silmaril.Wasm.Logic.Open`).

All proofs are in `Silmaril/Proofs/Wasm/Logic/Hoare`; they are Silmaril additions built
on silmaril-lean's step inversions (`Sim.Step.split_head`,
`Sim.Closure.Step.label_inv`, `Sim.Step.handler_inv`,
`Sim.Closure.Step.frame_redex_aux`, `SingleThreaded.inert_head_inv`,
`SingleThreaded.Step.split_host`).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Soundness of the every-run logic** (partial correctness and safety): from a
code with an every-run weakest precondition, every reachable configuration can
step, or has exited with an outcome satisfying the postcondition. -/
theorem hwp_sound {s : Store H} {f : Frame} {code : List Admin} {Q : Post H} {c' : Config H}
    (h : HWP P host s f code Q) (hs : Steps P host ⟨s, f, code⟩ c') :
    (∃ c'', Step P host c' c'') ∨ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o :=
  h.sound hs

/-- **Soundness of total correctness**: no infinite run. -/
theorem twp_terminates {s : Store H} {f : Frame} {code : List Admin} {Q : Post H}
    (h : TWP P host s f code Q) : ¬ Diverges P host ⟨s, f, code⟩ :=
  TSafe.not_diverges h

/-- **Soundness of guarded context validity**: if `Γe` is valid relative to `Γi`
and `Γi` is valid (both over the closed-world semantics), every run of `$invoke`
of a function of `Γe` that returns values satisfies its postcondition. -/
theorem ctxSat_invoke_sound {Γi Γe : Ctx H} (hm : CtxSat P host Γi Γe)
    (hi : Ctx.Valid P host Γi) {a : Nat} {S : FSpec H} (hS : Γe a = some S) {s s' : Store H}
    {f' : Frame} {args res : List Val} (hpre : S.pre s args)
    (hs : Steps P host (invoke s a args) ⟨s', f', vals res⟩) : S.post s args s' (.normal res) :=
  FSpecValid.invoke_vals (fun n => hm.valid hi n a S hS) hpre hs

end Silmaril.Wasm.Logic.Hoare
