module

public import Silmaril.Wasm.Execution.Core.Entry.Program.Defs
public import Silmaril.Wasm.Execution.Core.Entry.Thms
import Silmaril.Semantics.Operational.Program.Thms
import Silmaril.Wasm.Validation.Intrinsic.Thms
import Silmaril.Wasm.Execution.Core.Soundness

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Entry.Program

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Entry
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.Validation Silmaril.Semantics.Operational

variable {H : Type} {P : Profile} {host : HostSemantics H} {interface : CModuleType}

theorem typedModule_readback (hostOk : HostOk host) :
    OpSim (rawModule P host).semantics (typedModule P host interface).semantics
      (fun raw typed => typed.val = raw) :=
  WithUB.restrict_readback (fun {_ _} typed edge => (Step.preservation hostOk typed edge.2).1)

theorem typedModule_equivalent_raw (hostOk : HostOk host) (input : TypedModuleInput H interface) :
    (typedModule P host interface).Equivalent input (rawModule P host) input.erase :=
  ⟨HasOpSem.refines_of_sim (WithUB.restrict_sim (policy P host []) _) (fun {_} init => ⟨_, init, rfl⟩),
    HasOpSem.refines_of_sim (typedModule_readback hostOk) (fun {_} init => (typedModule_lift hostOk).mp init)⟩

theorem checkedModule_lift {raw : ModuleInput H} (valid : raw.CheckedAt interface) :
    ∃ input : TypedModuleInput H interface, input.erase = raw := by
  obtain ⟨module_, erased⟩ := Validation.Intrinsic.Module.lift_erase valid.1
  exact ⟨⟨raw.store, module_, raw.imports, valid.2.1, valid.2.2⟩,
    congrArg (fun body => ModuleInput.mk raw.store body raw.imports) erased⟩

variable {context : Context} {world : World H context} {parameters results : List IntType}
  {call : DirectCall world parameters results} {oracle : GrowOracle}

theorem resolved_equivalent (entry : ResolvedExport call) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer) :
    entry.opSem.Equivalent args (rawExport (profile oracle) noHost (stackTypes results)) (entry.rawInput args) := by
  apply HasOpSem.equivalent_iff.mpr
  have initial := entry.raw_initial_iff (P := profile oracle) (host := noHost) (types := stackTypes results) args
  refine ⟨Set.ext fun outcome => ?_, iff_of_false ?_ ?_⟩
  · change entry.opSem.May args outcome ↔
      (rawExport (profile oracle) noHost (stackTypes results)).May (entry.rawInput args) outcome
    constructor
    · rintro ⟨state, equal, seen⟩
      change state = call.start args at equal
      subst state
      exact ⟨_, (initial _).mpr rfl, (entry.may_iff args ran outcome).mp seen⟩
    · rintro ⟨state, init, seen⟩
      cases (initial state).mp init
      exact ⟨_, rfl, (entry.may_iff args ran outcome).mpr seen⟩
  · rintro ⟨state, _, ub⟩
    exact WithUB.ofOpSem_safe _ state ub
  · rintro ⟨state, init, ub⟩
    exact invoke_noUB call args ((initial state).mp init ▸ ub)

end Silmaril.Proofs.Wasm.Execution.Core.Entry.Program
