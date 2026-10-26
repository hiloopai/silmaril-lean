module

public import Silmaril.Process.LPS.Machines.X86FlagOracle
public import Silmaril.Process.LPS.Machines.X86RepStosq

/-! # Shared flag-oracle instances for Wire and optional DF=0 REP STOSQ

These options reuse the generic native syscall/return/memory interface. They
retain the underlying instruction behavior away from SYSCALL. Coverage of all
undefined-flag choices requires universal quantification over the oracle.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines
namespace X86FlagOracle

open Silmaril.X86
open X86FlagChoices (Choice completeState lift)

/-- An exact SYSCALL fetch cannot simultaneously be the new REP spelling. -/
theorem syscall_not_rep (state : X86State)
    (fetched : state.m.memory.fetchBytes state.m.core.rip.toNat 2 = some [0x0f, 0x05]) :
    state.m.memory.fetchBytes state.m.core.rip.toNat 3 ≠ some X86RepStosq.bytes := by
  intro rep
  have first := Silmaril.X86.Memory.readWith_slice rep 0 2 (by decide) (by decide)
  change state.m.memory.fetchBytes state.m.core.rip.toNat 2 = some [0xf3, 0x48] at first
  rw [fetched] at first
  contradiction

/-- Native syscall behavior, including an undefined-flags model gap, is shared. -/
theorem rep_syscall_agreement (platform : Ext.Wire.Platform) (state : X86State)
    (fetched : state.m.memory.fetchBytes state.m.core.rip.toNat 2 = some [0x0f, 0x05]) :
    X86RepStosq.step platform state = x86NativeStep state :=
  X86RepStosq.step_eq_native platform state (syscall_not_rep state fetched) (.inl fetched)

theorem rep_every_oracle_syscall (platform : Ext.Wire.Platform)
    (oracle : Nat → Choice) (state : X86FlagChoices.State)
    (fetched : state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 =
      some [0x0f, 0x05]) :
    stepUsing (X86RepStosq.step platform) oracle state =
      .ok ⟨⟨{ completeState state.native (oracle state.counter) with
          pending := some (state.native.m.core.read .rax) }, state.counter + 1⟩,
        [(state.native.m.core.rip, 2)]⟩ :=
  every_oracle_syscall _ (rep_syscall_agreement platform) oracle state fetched

end X86FlagOracle

def x86WireWithFlagOracle (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) : UserIsa :=
  X86FlagOracle.withFlagOracleUsing (x86WireStep platform) (x86Wire platform).entryFetchable true oracle

def x86WireDf0RepStosqWithFlagOracle (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) : UserIsa :=
  X86FlagOracle.withFlagOracleUsing (X86RepStosq.step platform)
    (x86WireDf0RepStosq platform).entryFetchable true oracle

end Silmaril.Process.LPS.Machines
