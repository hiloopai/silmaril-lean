module

public import Silmaril.Wasm.SpecTec.Sim.Round4Read.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4Read.Dispatch

/-!
# SpecTec ↔ Core 3.0, round 4, track r4-read: what is proved

* `Round4Read.read_doneV`: for every `B` with `NoAcc B`, every `Step_read` rule in `readDoneV`
  (27, 29–37, 38, 40, 52, 54–62, 63, 64, 81, 83) has its backward lemma from every typed
  source satisfying `ReadValid` (store bounds and index resolution). Nothing else is assumed: the decoders are
  proved, and `NoAcc` holds for the concrete `B` (`BwdRead.noAcc_builtins`). Round 3 had argued
  27, 31, 35, 52, 56, 60, 81 false without validity; under `ReadValid` they hold.
* `Round4Read.backward_upToV`: the generic backward recursion of round 1, relativised to any
  configuration predicate closed under the context decompositions (`CtxClosed`);
  `readValid_ctxClosed`: `ReadValid` is one.
* `Round4Read.backward_valid`, `backward_validConcrete`: the backward simulation from typed
  `ReadValid` sources, with the open rules `RemainingV` (`Integrate.RemainingW` with validity
  added and `readDoneV` removed; `remainingV_of_w`).

What is not discharged here: `ReadValid` from `ConfigOk` and `Round4.Bounded` (track
r4-validity's definitions), `Typed` from them (gap 3), the family structures `Bwd.BwdHyps` (whose
`CtrlCall.valtypes` round 3 refuted, `ConfigOk.not_ctrlCall`), and the rules left in
`RemainingV`. See `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Read.read_doneV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Read.read_doneV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Read.backward_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Read.backward_valid

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Read.backward_validConcrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4Read.backward_validConcrete

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4Read.readValid_ctxClosed' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Round4Read.readValid_ctxClosed
