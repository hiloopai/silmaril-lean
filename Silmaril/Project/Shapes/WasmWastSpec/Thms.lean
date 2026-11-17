module

public import Silmaril.Project.Shapes.WasmWastSpec.Defs
import Silmaril.Proofs.Project.Shapes.WasmWastSpec

/-!
# Standard problem shapes: WAST commands under the specification profile (transfer lemmas)

* `ScriptHoldsS.of_kernel h`: every command of the script `m`, `cmds` holds under
  `Profile.spec nd r`, for **every** `nd` and `r`, from one kernel evaluation
  `h : scriptSK m cmds = true` (`decide +kernel`). For each command: its expectation at every
  host-free normal form, with a run reaching it (`returns_allowed_all` / `traps_all`), and
  termination of every run (`terminates_all`).
* `ScriptHoldsS.returnsAllowedAll`, `.trapsAll`, `.terminatesAll`: the rows of command `k`.
* `ReturnsAllowedAll.exists`: the weaker existence shape.
* `numericSet?_sound`: every result of `NumericStep (Profile.spec nd r) (vals args ++ [op])` is in
  the class `numericSet? op args` (and there is a result). The classes follow
  `floatUnOpRel`/`floatBinOpRel`/`convertRel`: when the float result is a NaN, the canonical NaNs
  if every NaN operand is canonical, the arithmetic NaNs otherwise.
* `arithmeticBits_of_canonicalBits`: `nan:canonical` is contained in `nan:arithmetic`.
* `Reaches.spec`, `Returns.allowedExists`: **refinement**, from the deterministic profile to the
  specification profile: a run at `profile o` to a result is a run at `Profile.spec nd {}`
  (`Steps.deterministic_refines_spec`), so each `returns_only` row of `….WasmWast` gives the
  existence shape `returns_allowed_exists` with exact patterns. Only existence transfers this
  way: the deterministic profile's uniqueness of outcomes (`Only`) and termination
  (`Reaches.always`) are about `profile o`, not about the larger set of runs of
  `Profile.spec`.

Proofs: `Silmaril.Proofs.Project.Shapes.WasmWastSpec`, from the run theorems of
`Silmaril.Wasm.Execution.StraightLine.Thms`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWastSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics Silmaril.Project.Shapes.WasmWast

variable {nd : Bool} {r : RelaxedChoice} {m : Module}

/-- **Every command of a script, under every specification profile, from one kernel
evaluation.** -/
theorem ScriptHoldsS.of_kernel {cmds : List CmdS} (h : scriptSK m cmds = true) :
    ScriptHoldsS nd r m cmds :=
  Silmaril.Proofs.Project.Shapes.WasmWastSpec.scriptHoldsS_of_kernel h

/-- The row of an `assert_return` command `k`: every normal form returns allowed values. -/
theorem ScriptHoldsS.returnsAllowedAll {cmds : List CmdS} (h : ScriptHoldsS nd r m cmds)
    (k : Nat) {act : Action} {ps : List ValPat} (hk : cmds[k]? = some ⟨act, some (.values ps)⟩) :
    ReturnsAllowedAll nd r m (preS cmds k) act ps :=
  (h k _ hk).1

/-- The row of an `assert_trap` command `k`: every normal form is a trap. -/
theorem ScriptHoldsS.trapsAll {cmds : List CmdS} (h : ScriptHoldsS nd r m cmds) (k : Nat)
    {act : Action} (hk : cmds[k]? = some ⟨act, some .trap⟩) : TrapsAll nd r m (preS cmds k) act :=
  (h k _ hk).1

/-- The termination row of command `k`: no run is infinite. -/
theorem ScriptHoldsS.terminatesAll {cmds : List CmdS} (h : ScriptHoldsS nd r m cmds) (k : Nat)
    {cmd : CmdS} (hk : cmds[k]? = some cmd) : TerminatesAll nd r m (preS cmds k) cmd.act :=
  Silmaril.Proofs.Project.Shapes.WasmWastSpec.terminatesAll_of h k hk

theorem ReturnsAllowedAll.exists {pre : List Action} {act : Action} {ps : List ValPat}
    (h : ReturnsAllowedAll nd r m pre act ps) : ReturnsAllowedExists nd r m pre act ps :=
  h.1

/-- The class of the specification's results of a numeric step. -/
theorem numericSet?_sound {op : Instr} {args : List Val} {S : NumSet}
    (h : numericSet? op args = some S) :
    (∀ is', NumericStep (Profile.spec nd r) (vals args ++ [.plain op]) is' → S.Mem is') ∧
      ∃ is', NumericStep (Profile.spec nd r) (vals args ++ [.plain op]) is' :=
  Silmaril.Proofs.Project.Shapes.WasmWastSpec.numericSet?_sound h

/-- Every canonical NaN is an arithmetic NaN. -/
theorem arithmeticBits_of_canonicalBits {t : FloatType} {n : Nat} (h : CanonicalBits t n) :
    ArithmeticBits t n :=
  ⟨h.1, h.2 ▸ le_rfl⟩

/-- **Refinement**: a run at `profile o` to a result is a run at `Profile.spec nd {}`. -/
theorem _root_.Silmaril.Project.Shapes.WasmWast.Reaches.spec {o : GrowOracle} {pre : List Action}
    {act : Action} {res : Result} (h : Reaches o m pre act res) (nd : Bool) :
    ReachesS nd {} m pre act (· = res) :=
  Silmaril.Proofs.Project.Shapes.WasmWastSpec.reaches_spec nd h

/-- A `returns` row at `profile o` gives the existence shape at `Profile.spec nd {}`, with
exact patterns. -/
theorem _root_.Silmaril.Project.Shapes.WasmWast.Returns.allowedExists {o : GrowOracle}
    {pre : List Action} {act : Action} {vs : List Val} (h : Returns o m pre act vs) (nd : Bool) :
    ReturnsAllowedExists nd {} m pre act (vs.map .exact) :=
  Silmaril.Proofs.Project.Shapes.WasmWastSpec.returnsAllowedExists_of_returns nd h

end Silmaril.Project.Shapes.WasmWastSpec

end
