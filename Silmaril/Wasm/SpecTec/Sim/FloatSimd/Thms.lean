module

public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Float
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Lanes
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Iter
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Splat
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Backward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.BackwardRules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Assembly

/-!
# SpecTec ↔ Core 3.0, family V (vector/relaxed): what is proved

* `Sim.Vec.vecInstrV?` (`Sim/VecEncoding/Defs.lean`): the non-memory SIMD instructions encoded
  against the IL type `instr`, replacing the schema reading for them in `Sim.instrToV`.
* `spure_vvunop`, `spure_vvbinop`, `spure_vvternop`, `spure_vvtestop`, `spure_vunopVal`,
  `spure_vunopTrap`, `spure_vbinopVal`, `spure_vbinopTrap`, `spure_vternopVal`,
  `spure_vternopTrap`, `spure_vtestop`, `spure_vrelop`, `spure_vshiftop`, `spure_vbitmask`,
  `spure_vswizzlop`, `spure_vshuffle`, `spure_vsplat`, `spure_vextractLaneNum`,
  `spure_vextractLanePack`, `spure_vreplaceLane`, `spure_vextunop`, `spure_vextbinop`,
  `spure_vextternop`, `spure_vnarrow`, `spure_vcvtop`: all 25 vector rules of `Step_pure`
  (54–78), constructed under the declarative reading for arbitrary IL values of their types, from
  the denotations (`Applies`) of the operator calls in their premises. `vtestop`, `vsplat` and
  `vreplace_lane`, dead under the evaluator reading, fire under this one.
* `fwd_vec*`: all 29 constructors of Core's `VectorStep`, forward, under `VecTyping`, `VecAgree`
  and `FloatTyping`; `fwd_vector` has the type of `Forward.vector`, and `simEnv_fwd_vector`
  discharges the rule provenance in `simEnv B`.
* `spure_unopVal`, `spure_binopVal`, `spure_relop`, `spure_cvtopVal`, `spure_cvtopTrap` and
  `fwd_floatUnOp`, `fwd_floatBinOp`, `fwd_floatRelOp`, `fwd_convert`, `fwd_convertTrap`: the float
  and conversion constructors of `NumericStep`, forward, under `FloatTyping` and `FloatAgree`.
* `bwd_vvunop`, …, `bwd_vcvtop` and the dispatcher `bwd_vectorRules`: `Backward.pure i` for 20
  of the 25 vector rules (all but 64, 70–73), under `HasVectorRules`, `VecDecode` and `VecAgree`.

Open: the interfaces `VecTyping`, `VecAgree`, `VecDecode`, `FloatTyping`, `FloatAgree` themselves;
backward for rules 64 and 70–73 and for the scalar float/conversion rules. See the family V section
of `docs/projects/spectec/README.md`.
-/
