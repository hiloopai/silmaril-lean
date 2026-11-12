module

public import Silmaril.Wasm.SpecTec.Sim.Control.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.CallFunc
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Otherwise
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.BackwardCall

/-!
# SpecTec ↔ Core 3.0, family C (control and calls): what is proved

Forward obligations (`Forward` fields, at `env := simEnv B`, under `TypingFacts (simEnv B) hn`
and `CtrlTyping (simEnv B)`), each through a `Step_pure` derivation lifted by `Step/pure`:
`fwd_ifTrue`, `fwd_ifFalse`, `fwd_labelVals`, `fwd_brLabelZero`, `fwd_brLabelSucc`,
`fwd_brHandler`, `fwd_brIfTrue`, `fwd_brIfFalse`, `fwd_brTableLt`, `fwd_brTableGe`,
`fwd_brOnNullNull`, `fwd_brOnNonNullNull`, `fwd_callIndirect`, `fwd_returnCallIndirect`,
`fwd_frameVals`, `fwd_returnFrame`, `fwd_returnLabel`, `fwd_returnHandler`, `fwd_trapInstrs`,
`fwd_trapLabel`, `fwd_trapHandler`, `fwd_trapFrame`.

The underlying constructions `spure_*` hold for arbitrary values of the rules' IL types. Coverage,
open fields and the decision on Core's `return_call_ref` deviation are in
`docs/projects/spectec/README.md`, section "Family C".
-/
