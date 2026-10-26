module

public import Silmaril.Process.LPS.Machines.X86

/-! # Explicit choices for undefined x86 syscall flags

The native deterministic adapter declines a syscall if any status flag is
undefined, since SYSCALL copies the RFLAGS image to R11. This additive option
chooses values only for undefined flags, using a supplied total Boolean oracle.
The completed flags remain in machine state and supply R11 on return.

A theorem covering every possible completion must quantify over every oracle;
a theorem for one oracle alone covers only that choice. This option does not
claim a hardware refinement, change legacy behavior, or add Wire decoding.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86FlagChoices

open Silmaril.X86

structure Choice where
  carry : Bool
  parity : Bool
  adjust : Bool
  zero : Bool
  sign : Bool
  overflow : Bool
  deriving DecidableEq

def Choice.flags (choice : Choice) : Flags :=
  ⟨some choice.carry, some choice.parity, some choice.adjust, some choice.zero,
    some choice.sign, some choice.overflow⟩

def Compatible (prior : Flags) (choice : Choice) : Prop :=
  (∀ value, prior.carry = some value → value = choice.carry) ∧
  (∀ value, prior.parity = some value → value = choice.parity) ∧
  (∀ value, prior.adjust = some value → value = choice.adjust) ∧
  (∀ value, prior.zero = some value → value = choice.zero) ∧
  (∀ value, prior.sign = some value → value = choice.sign) ∧
  (∀ value, prior.overflow = some value → value = choice.overflow)

def completeFlag (prior : Option Bool) (choice : Bool) : Option Bool :=
  some (prior.getD choice)

def completeFlags (prior : Flags) (choice : Choice) : Flags :=
  ⟨completeFlag prior.carry choice.carry, completeFlag prior.parity choice.parity,
    completeFlag prior.adjust choice.adjust, completeFlag prior.zero choice.zero,
    completeFlag prior.sign choice.sign, completeFlag prior.overflow choice.overflow⟩

def Defined (flags : Flags) : Prop :=
  flags.carry.isSome = true ∧ flags.parity.isSome = true ∧ flags.adjust.isSome = true ∧
    flags.zero.isSome = true ∧ flags.sign.isSome = true ∧ flags.overflow.isSome = true

theorem completeFlag_known (value choice : Bool) : completeFlag (some value) choice = some value := rfl

theorem completeFlag_unknown (choice : Bool) : completeFlag none choice = some choice := rfl

theorem completeFlag_preserves (prior : Option Bool) (value choice : Bool)
    (known : prior = some value) : completeFlag prior choice = some value := by
  rw [known]
  rfl

/-- Arbitrary known/unknown flags always admit a consistent total valuation.
This witness is an existence proof, not the oracle selected by the machine. -/
theorem compatible_exists (prior : Flags) : ∃ choice, Compatible prior choice := by
  refine ⟨⟨prior.carry.getD false, prior.parity.getD false, prior.adjust.getD false,
    prior.zero.getD false, prior.sign.getD false, prior.overflow.getD false⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro value known
    rw [known]
    rfl

theorem completeFlags_defined (prior : Flags) (choice : Choice) :
    Defined (completeFlags prior choice) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem completeFlags_rflagsImage (prior : Flags) (choice : Choice) :
    (rflagsImage (completeFlags prior choice)).isSome = true := rfl

theorem completeFlags_eq_self (flags : Flags) (choice : Choice) (defined : Defined flags) :
    completeFlags flags choice = flags := by
  rcases flags with ⟨carry, parity, adjust, zero, sign, overflow⟩
  cases carry <;> cases parity <;> cases adjust <;> cases zero <;> cases sign <;> cases overflow <;>
    simp_all [Defined, completeFlags, completeFlag]

/-- Completing a prior flag valuation can realize any requested total
valuation that agrees with its known flags. -/
theorem completeFlag_realizes (prior : Option Bool) (value : Bool)
    (agrees : ∀ known, prior = some known → known = value) :
    completeFlag prior value = some value := by
  cases prior with
  | none => rfl
  | some known => rw [← agrees known rfl]; rfl

/-- Every total flag valuation agreeing with known flags is available as an
oracle choice; no undefined flag is forced to a particular Boolean. -/
theorem completeFlags_realizes (prior : Flags) (choice : Choice)
    (compatible : Compatible prior choice) : completeFlags prior choice = choice.flags := by
  unfold completeFlags Choice.flags
  rw [completeFlag_realizes _ _ compatible.1, completeFlag_realizes _ _ compatible.2.1,
    completeFlag_realizes _ _ compatible.2.2.1, completeFlag_realizes _ _ compatible.2.2.2.1,
    completeFlag_realizes _ _ compatible.2.2.2.2.1,
    completeFlag_realizes _ _ compatible.2.2.2.2.2]

def completeState (state : X86State) (choice : Choice) : X86State :=
  { state with m := { state.m with core :=
      { state.m.core with flags := completeFlags state.m.core.flags choice } } }

structure State where
  native : X86State
  counter : Nat

def lift (counter : Nat) : MachineResult (AccessReport X86State) → MachineResult (AccessReport State)
  | .ok report => .ok ⟨⟨report.value, counter⟩, report.accessed⟩
  | .fault => .fault
  | .unmodeled => .unmodeled

def step (oracle : Nat → Choice) (state : State) : MachineResult (AccessReport State) :=
  if state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    lift (state.counter + 1) (x86NativeStep (completeState state.native (oracle state.counter)))
  else lift state.counter (x86NativeStep state.native)

theorem step_not_syscall (oracle : Nat → Choice) (state : State)
    (other : state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 ≠ some [0x0f, 0x05]) :
    step oracle state = lift state.counter (x86NativeStep state.native) := by
  rw [step, ite_eq_right other]

theorem step_syscall (oracle : Nat → Choice) (state : State)
    (fetched : state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 = some [0x0f, 0x05]) :
    step oracle state =
      .ok ⟨⟨{ completeState state.native (oracle state.counter) with
          pending := some (state.native.m.core.read .rax) }, state.counter + 1⟩,
        [(state.native.m.core.rip, 2)]⟩ := by
  rw [step, ite_eq_left fetched]
  rw [x86NativeStep_syscall (completeState state.native (oracle state.counter)) fetched
    (completeFlags_rflagsImage _ _)]
  rfl

/-- On fully defined syscall flags, the projected machine behavior is exactly
native behavior; only the private oracle counter advances. -/
theorem step_defined_syscall (oracle : Nat → Choice) (state : State)
    (fetched : state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 = some [0x0f, 0x05])
    (defined : Defined state.native.m.core.flags) :
    step oracle state = lift (state.counter + 1) (x86NativeStep state.native) := by
  rw [step, ite_eq_left fetched]
  have unchanged : completeState state.native (oracle state.counter) = state.native := by
    unfold completeState
    rw [completeFlags_eq_self _ _ defined]
  rw [unchanged]

end X86FlagChoices

/-- An explicit oracle option: full choice coverage requires universal
quantification over `oracle` in the client proposition. -/
def x86WithFlagOracle (oracle : Nat → X86FlagChoices.Choice) : UserIsa where
  State := X86FlagChoices.State
  step _ := X86FlagChoices.step oracle
  svcPending state := x86ExtNative.svcPending state.native
  syscallArgs state := x86ExtNative.syscallArgs state.native
  readByte segments state := x86ExtNative.readByte segments state.native
  writableByte segments state := x86ExtNative.writableByte segments state.native
  applyEffect state effect := ⟨x86ExtNative.applyEffect state.native effect, state.counter⟩
  advancePastSvc state := ⟨x86ExtNative.advancePastSvc state.native, state.counter⟩
  init segments pc sp stack := ⟨x86ExtNative.init segments pc sp stack, 0⟩
  reportsAccesses := true
  entryFetchable := x86ExtNative.entryFetchable
  addressSpace := x86ExtNative.addressSpace

end Silmaril.Process.LPS.Machines
