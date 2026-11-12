module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.PrimsCall

/-!
# Round 7, the whole-evaluator erasure: `BIErase` at round 6's primitives (round 3, pass 3, proved)

See `docs/projects/spectec/README.md`.

* `biErase_BI`: in `utf8Env (Round4Int.BI P hn host)`, the builtins of every `gd` name commute
  with erasure and keep the swap set, whenever `gd` names neither `$hostcall` nor `$blocktype_`.
  This discharges the last hypothesis of `hyps_utf8Env`.
* `hyps_BI : StripInj c → Hyps (QC c) grE gdE (utf8Env (Round4Int.BI P hn host))`. So
  `Round7.EraseAll.eraseAt` holds, at every fuel, for the checked part of the wasm-3.0 script in
  the round-7 environment at round 6's primitives.

The argument is strictness (`OKS`): every primitive other than `$hostcall`, `$blocktype_` and
`$sx` answers only at export-free arguments, with an export-free value; `eraseV` keeps an `EXPORTS`
record (`nxB_eraseV`), so at other arguments both sides fail. `$sx` (`[.val _] => ε`) ignores its
argument and is compared directly. The proof walks the decision trees of the primitives, as
`Round7.Determ.builtinsEF_BI` does, and is kept unrefined in `Raw/…/Round7/EraseAll/Prims*.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.biErase_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms biErase_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.hyps_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyps_BI

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
