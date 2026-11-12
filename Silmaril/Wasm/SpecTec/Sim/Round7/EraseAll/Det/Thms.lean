module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Det

/-!
# Round 7, the export swap: rule quantifiers in the swap set (round 3, pass 3, proved)

Definitions are in `Round7/EraseAll/Det/Defs.lean`; see `docs/projects/spectec/README.md`.

* `dderivesB_AI`: in `utf8Env B`, under `Hyps Q grE gdE (utf8Env B)`, a `DDerivesB` derivation of a
  checked relation (`grE`) at a value whose input is in the swap set binds every quantifier of
  every rule instance to a swap-set value (`DDerivesBQ (AllIn Q)`), and its value is in the swap
  set. It is the `AllIn` analogue of `Round7.Determ.dderivesB_E`, and reuses its kernel-checked mode
  check.
* `dderivesB_AI_BI`: the same at round 6's primitives and the swap set `QC c` of a configuration
  with `StripInj c` (through `hyps_BI`), with nothing left open.
* Ingredients (unrefined, in `Raw/…/Round7/EraseAll/Det*.lean`): `ai_inv` (inverting the
  evaluator on swap-set values), `nx_of_hasTyp_A` (values typed over `tyA` have no `EXPORTS`
  record), `ai_eval_on` (the evaluator-level erasure on scopes that are in the swap set only on
  the free variables: the locality lemma, through `Silmaril.SpecTec.Sem.evalExp_agreeOn`), and
  `aiOn_ruleK` (the mode check keeps the swap set).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (AllIn QC)

/-- **Rule quantifiers in the swap set, at round 6's primitives.** -/
theorem dderivesB_AI_BI {H : Type} {c : Silmaril.Wasm.Execution.Core.Config H} (hinj : StripInj c)
    (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {O : ElseI} {x : Silmaril.SpecTec.IL.Id}
    {op : Silmaril.SpecTec.IL.MixopS} {args : List ArgV} {v : Value} (hx : grE x = true)
    (hin : InAI (QC c) v)
    (h : Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host)) O x op args v) :
    DDerivesBQ (AllIn (QC c)) (utf8Env (Round4Int.BI P hn host)) (ElseAI (QC c) O) x op args v ∧
      AllIn (QC c) v :=
  dderivesB_AI (hyps_BI hinj P hn host) hx hin h

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.dderivesB_AI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_AI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.dderivesB_AI_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_AI_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.nx_of_hasTyp_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nx_of_hasTyp_A

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
