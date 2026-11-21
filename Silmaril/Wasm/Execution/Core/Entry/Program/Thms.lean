module

public import Silmaril.Wasm.Execution.Core.Entry.Program.Defs
public import Silmaril.Wasm.Execution.Core.Entry.Thms
public import Silmaril.Semantics.Operational.Program.Thms
import Silmaril.Proofs.Wasm.Execution.Core.Entry.Program
import Silmaril.Wasm.Execution.Core.Intrinsic.Pure.Thms

public section

namespace Silmaril.Wasm.Execution.Core.Entry

open Validation Numerics SingleThreaded SingleThreaded.Det Semantics.Operational
open Intrinsic (DirectCall Values World stackTypes)

variable {H : Type} {P : Profile} {host : HostSemantics H} {interface : CModuleType}

/-- The intrinsic-to-checked-to-raw triangle commutes with the same Core
initialization and policy, before any comparison of execution states. -/
theorem checkedModule_erasure (P : Profile) (host : HostSemantics H) (interface : CModuleType) :
    (checkedModule P host interface).precompose TypedModuleInput.checked =
      (rawModule P host).precompose (TypedModuleInput.erase (interface := interface)) := rfl

theorem checkedModule_lift {raw : ModuleInput H} (valid : raw.CheckedAt interface) :
    ∃ input : TypedModuleInput H interface, input.erase = raw :=
  Proofs.Wasm.Execution.Core.Entry.Program.checkedModule_lift valid

theorem typedModule_erase : OpSim (typedModule P host interface).semantics (rawModule P host).semantics
    (fun typed raw => typed.val = raw) := WithUB.restrict_sim _ _

theorem typedModule_readback (hostOk : HostOk host) :
    OpSim (rawModule P host).semantics (typedModule P host interface).semantics
      (fun raw typed => typed.val = raw) := Proofs.Wasm.Execution.Core.Entry.Program.typedModule_readback hostOk

/-- Both directions use matching initial states. The reverse direction needs
the stated host typing, not a deterministic host or a fuel bound. -/
theorem typedModule_equivalent_raw (hostOk : HostOk host) (input : TypedModuleInput H interface) :
    (typedModule P host interface).Equivalent input (rawModule P host) input.erase :=
  Proofs.Wasm.Execution.Core.Entry.Program.typedModule_equivalent_raw hostOk input

theorem typedModule_equivalent_checked (hostOk : HostOk host) (input : TypedModuleInput H interface) :
    (typedModule P host interface).Equivalent input (checkedModule P host interface) input.checked :=
  typedModule_equivalent_raw hostOk input

variable {context : Context} {world : World H context} {parameters results : List IntType}
  {call : DirectCall world parameters results} {oracle : GrowOracle}

/-- For a resolved typed integer call with a finite answer, compare the
intrinsic body machine to the actual ready-store named export under the
existing Core result observer. This is not a primitive simulation theorem. -/
theorem ResolvedExport.equivalent_of_runFor (entry : ResolvedExport call) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer) :
    entry.opSem.Equivalent args (rawExport (profile oracle) noHost (stackTypes results)) (entry.rawInput args) :=
  Proofs.Wasm.Execution.Core.Entry.Program.resolved_equivalent entry args ran

/-- The intrinsic integer/local body and the actual named Core invocation
agree on finite observations and reachable UB. The proof supplies its own
checked structural budget; clients compare the unfuelled relations. -/
theorem ResolvedExport.equivalent (entry : ResolvedExport call) (args : Values parameters) :
    entry.opSem.Equivalent args (rawExport (profile oracle) noHost (stackTypes results)) (entry.rawInput args) :=
  entry.equivalent_of_runFor args (Intrinsic.Pure.run_eval
    ⟨args.append (Values.zeros call.declaredLocals)⟩ call.body .nil)

end Silmaril.Wasm.Execution.Core.Entry
