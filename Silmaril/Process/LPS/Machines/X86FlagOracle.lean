module

public import Silmaril.Process.LPS.Machines.X86FlagChoices

/-!
# Reusable syscall-flag oracle for native x86 steppers

The existing canonical oracle is preserved. `stepUsing` factors the same
operation over any native `X86State` stepper: only a fetched SYSCALL completes
undefined flags and advances the private oracle counter. Known flags remain
unchanged. Away from SYSCALL the underlying instruction and counter are used
unchanged, including REP microsteps.

`withFlagOracleUsing` packages such steppers with the common native syscall,
memory-effect and loader interface. Its Wire and DF=0 REP STOSQ instances live in
`X86WireFlagOracle`, keeping this generic import independent of those options.
Clients claiming all undefined-flag choices must quantify universally over the
oracle. None of these definitions establishes hardware
refinement or a complete musl execution proof.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86FlagOracle

open Silmaril.X86
open X86FlagChoices (Choice completeState lift Defined)

def stepUsing (baseStep : X86State → MachineResult (AccessReport X86State))
    (oracle : Nat → Choice) (state : X86FlagChoices.State) : MachineResult (AccessReport X86FlagChoices.State) :=
  if state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    lift (state.counter + 1) (baseStep (completeState state.native (oracle state.counter)))
  else lift state.counter (baseStep state.native)

/-- The refactoring agrees with the unchanged original canonical option. -/
theorem canonical_agreement (oracle : Nat → Choice) (state : X86FlagChoices.State) :
    stepUsing x86NativeStep oracle state = X86FlagChoices.step oracle state := rfl

theorem not_syscall (baseStep : X86State → MachineResult (AccessReport X86State))
    (oracle : Nat → Choice) (state : X86FlagChoices.State)
    (other : state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 ≠
      some [0x0f, 0x05]) :
    stepUsing baseStep oracle state = lift state.counter (baseStep state.native) := by
  rw [stepUsing, ite_eq_right other]

/-- For every underlying stepper, defined flags are preserved exactly. -/
theorem defined_syscall (baseStep : X86State → MachineResult (AccessReport X86State))
    (oracle : Nat → Choice) (state : X86FlagChoices.State)
    (fetched : state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 =
      some [0x0f, 0x05]) (defined : Defined state.native.m.core.flags) :
    stepUsing baseStep oracle state = lift (state.counter + 1) (baseStep state.native) := by
  rw [stepUsing, ite_eq_left fetched]
  have unchanged : completeState state.native (oracle state.counter) = state.native := by
    unfold completeState
    rw [X86FlagChoices.completeFlags_eq_self _ _ defined]
  rw [unchanged]

theorem every_oracle_syscall
    (baseStep : X86State → MachineResult (AccessReport X86State))
    (agrees : ∀ state : X86State,
      state.m.memory.fetchBytes state.m.core.rip.toNat 2 = some [0x0f, 0x05] →
        baseStep state = x86NativeStep state)
    (oracle : Nat → Choice) (state : X86FlagChoices.State)
    (fetched : state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 =
      some [0x0f, 0x05]) :
    stepUsing baseStep oracle state =
      .ok ⟨⟨{ completeState state.native (oracle state.counter) with
          pending := some (state.native.m.core.read .rax) }, state.counter + 1⟩,
        [(state.native.m.core.rip, 2)]⟩ := by
  rw [stepUsing, ite_eq_left fetched,
    agrees (completeState state.native (oracle state.counter)) fetched,
    x86NativeStep_syscall (completeState state.native (oracle state.counter)) fetched
      (X86FlagChoices.completeFlags_rflagsImage _ _)]
  rfl

/-- Shared native x86 syscall/memory/launch methods around a chosen stepper. -/
def withFlagOracleUsing (baseStep : X86State → MachineResult (AccessReport X86State))
    (fetchable : List Segment → Nat → Bool) (reports : Bool) (oracle : Nat → Choice) : UserIsa where
  State := X86FlagChoices.State
  step _ := stepUsing baseStep oracle
  svcPending state := x86ExtNative.svcPending state.native
  syscallArgs state := x86ExtNative.syscallArgs state.native
  readByte segments state := x86ExtNative.readByte segments state.native
  writableByte segments state := x86ExtNative.writableByte segments state.native
  applyEffect state effect := ⟨x86ExtNative.applyEffect state.native effect, state.counter⟩
  advancePastSvc state := ⟨x86ExtNative.advancePastSvc state.native, state.counter⟩
  init segments pc sp stack := ⟨x86ExtNative.init segments pc sp stack, 0⟩
  reportsAccesses := reports
  entryFetchable := fetchable
  addressSpace := x86ExtNative.addressSpace

theorem canonical_isa_agreement (oracle : Nat → Choice) :
    withFlagOracleUsing x86NativeStep x86ExtNative.entryFetchable true oracle =
      x86WithFlagOracle oracle := rfl

end X86FlagOracle

end Silmaril.Process.LPS.Machines
