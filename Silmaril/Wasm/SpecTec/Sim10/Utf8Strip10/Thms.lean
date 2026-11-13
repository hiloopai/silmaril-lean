module

public import Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Step
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Inv
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Typ
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Fwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Mods
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Unstrip
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Run

/-!
# Removing export lists from V1 configurations: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10`; see `docs/projects/spectec/README.md`, "utf8
". The 1.0 form 's 2.0 decomposition `Sim20.Utf8Strip`, in the fixed script
`Utf8Fix.fixedU10`.

* `Utf8Strip10Step`: **`step_strip10`**: on a store without host functions, a V1 step
  `c → c'` gives `stripConfig10 c → stripConfig10 c'`.
* `Utf8Strip10Inv`: stripping keeps `Whole.Plain10`, `Whole.MemsAligned10` and `GSetOk`
  (`plain10_strip`, `memsAligned10_strip`, `gSetOk_strip10`).
* `Utf8Strip10Typ`: **`typed10_strip`** (leg 2): a configuration typed in `utf8Env10T B`, with
  its exports removed, is typed in `simEnv10T B`. The 1.0 runtime structures are typed field by
  field in either environment (`typed10_iffE`, …).
* `Utf8Strip10Fwd`: **`stepFwd10U_strip`** (unconditional): a V1 step from a configuration typed
  in `utf8Env10T`, with round 4's other invariants, strips to a step of `utf8Env10T` between the
  stripped images; **`stepFwd10U_of_unstrip`**: with leg 3 (`Task.unstripStep10`), the step
  itself is one.
* `Utf8Strip10Mods`: **`modsQ10_step`**: a V1 step on a host-free store keeps any property of
  all module instances.
* `Utf8Strip10Unstrip`: **`typed10_unstrip`**, **`typed10U_succ`**: the exports can be put back
  in `utf8Env10T`, so the successor of a step is typed there.
* `Utf8Strip10Run`: **`stepFwd10U_typed`** (unconditional) and **`wholeRunFwd10U_of_unstrip`**:
  round 4's forward run theorem in `fixedU10` at non-empty export names, from leg 3.

Open: `Task.unstripStep10` (leg 3 for 1.0), as `Sim20.Utf8Strip.Task.unstripStep20` for 2.0.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.step_strip10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.step_strip10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.gSetOk_strip10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.gSetOk_strip10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.typed10_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.typed10_strip

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.stepFwd10U_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.stepFwd10U_strip

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.typed10U_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.typed10U_succ

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.stepFwd10U_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.stepFwd10U_typed

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.wholeRunFwd10U_of_unstrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.wholeRunFwd10U_of_unstrip
