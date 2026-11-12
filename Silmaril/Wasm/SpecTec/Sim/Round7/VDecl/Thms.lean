module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.Rest
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.FiresB
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.VDecl.Step

/-!
# Round 7, memory SIMD: the declarative `$vbytes_` transfer

`OpenRMRest` is stated at `BM = withVBytes (Prims.builtins …)`; round 6 works at
`BI = Prims.builtins …`. `Round7.VAgree` proved that the fuelled evaluators of `simEnv B₁` and
`simEnv B₂` agree on syntax that never reaches `$vbytes_`, `Step` or `Step_read`, for any builtins
that agree off `$vbytes_` (`AgreeOff`). This header carries the agreement to the declarative
readings:

* **Typing** (`hasTyp_eq`, `hasTyp_iff`, `quantsOk_iff`, `typedV_iff`): at a type whose references
  are all reachable from `Step` and none is `$vbytes_`, `Step` or `Step_read` (`RG`), the two
  environments type every value alike. `typedD_withVBytes_iff`, `typedD_iff`: `TypedD` reads
  alike at every configuration (no type `Step` reaches refers to `$vbytes_`, so no condition on
  the value is needed, unlike `$utf8`).
* **Derivations** (`dderives_agree`, `dderivesB_agree`): a `DDerives`/`DDerivesB` derivation of a
  `GoodRel` relation (reachable, not `Step` or `Step_read`) moves from `B₁` to `B₂`, given
  `otherwise` readings related on `GoodRel` relations; with SpecTec's reading of `otherwise`:
  `dderives_otherwise`, `dderivesB_otherwise`.
* **`otherwise`** (`otherwiseAt_goodRel`, `otherwiseAt_read`, and `B` forms): the `otherwise`
  premises of every `GoodRel` relation move across; those of `Step_read` move up to rule 43, and
  after 43 on left-hand sides not ending in `VLOAD`. **The semantic half of `Round7.VElse`**:
  rule 43 fires only on left-hand sides ending in `VLOAD` (`lhsAtom_of_read43`,
  `lhsAtom_of_read43B`, from `lhsAtom_of_eval`), and every `otherwise` rule after 43 derives only
  values whose left-hand side ends in another atom (`read_else_atom`, `read_else_altAtom`).
* **Single rules** (`fires_*_withVBytes_iff`, `firesB_*_withVBytes_iff`): every rule of
  `Step_pure`, every rule of `Step_read` but 43 and every rule of `Step` but 1–5 and 23 fires
  alike at `withVBytes B` and at `B`, under both readings.
* **`OpenRMRest.rest`** (`backwardUpToDRestS_withVBytes_iff`): the per-rule backward obligations
  off memory SIMD are the same at `withVBytes B` and at `B`, for every predicate `V`.

Kernel facts (`decide +kernel`, kernel reduction, no native code): `relFacts_fixed` (five chunks; the relations
`Step` reaches have no parameters, and `RG` quantifier types and conclusion alternatives),
`read_elseDeep`, `step_elseDeep` (`otherwise` at any depth), `read_elseAltsOk` (the atoms of the
conclusion alternatives of rule 43 and the later `otherwise` rules).

* **The whole step, under a value invariant** (`sstep_withVBytes_iff`, `sstep_agree`,
  `sread_agree`): `Step` rules 1–5 call `Step` and `Step_read` on configurations built from their
  own, so a derivation of `Step` may reach rules 43 and 23, which do fire on memory SIMD code.
  For a predicate `Q` on values that keeps rules 43 and 23 silent and passes from the conclusion
  of a context rule to its `Step` and `Step_read` premises (`StepInv`), `SStep` reads alike at
  `withVBytes B` and at `B` on `Q` values. `stepInv_of_lhsAtom`: the silence holds as soon as `Q`
  values end in neither `VLOAD` nor `VSTORE` (rule 23 ends in `VSTORE`: `step_ctxOk`). The
  passage through the context rules (`StepInv.ctx`) is a hypothesis: no concrete `Q` is
  constructed here.

Not shown here: a concrete `StepInv` (for instance "no memory SIMD instruction in the code, at any
depth", which needs the five context rules' conclusions read on values), and the backend
reading `SStepB` of the whole step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.relFacts_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relFacts_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.read_elseAltsOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_elseAltsOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.typedD_withVBytes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedD_withVBytes_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.dderivesB_otherwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_otherwise

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.fires_read_withVBytes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_read_withVBytes_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.firesB_read_withVBytes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesB_read_withVBytes_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.backwardUpToDRestS_withVBytes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backwardUpToDRestS_withVBytes_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.sstep_withVBytes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_withVBytes_iff

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
