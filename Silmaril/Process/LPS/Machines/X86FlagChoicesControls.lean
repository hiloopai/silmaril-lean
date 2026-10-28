module

public import Silmaril.Process.LPS.Machines.X86FlagChoices
public import Silmaril.Process.LPS.Machines.X86WireControls

/-! # Undefined AF syscall choices

Logical XOR leaves AF undefined in the local executor. These controls isolate
that resulting flag state at actual fetched SYSCALL bytes: the deterministic
native option declines, while both possible AF choices execute and give
different R11 images. All already-defined status flags remain false even if
the oracle asks for true. This is a syscall fragment, not a whole-program proof.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86FlagChoices.Controls

open Silmaril.X86

def native : X86State :=
  { X86WireControls.syscallState with m :=
    { X86WireControls.syscallState.m with core :=
      { X86WireControls.syscallState.m.core with flags :=
        { X86WireControls.syscallState.m.core.flags with adjust := none } } } }

def initial : State := ⟨native, 0⟩

def low : Choice := ⟨false, false, false, false, false, false⟩
def high : Choice := ⟨true, true, true, true, true, true⟩

theorem fetched : native.m.memory.fetchBytes native.m.core.rip.toNat 2 = some [0x0f, 0x05] :=
  X86WireControls.syscall_fetched

theorem deterministic_native_declines : x86NativeStep native = .unmodeled := by
  rw [x86NativeStep, ite_eq_left fetched]
  rfl

def pending (choice : Choice) : State :=
  ⟨{ completeState native choice with pending := some 39 }, 1⟩

theorem every_oracle_executes (oracle : Nat → Choice) :
    step oracle initial = .ok ⟨pending (oracle 0), [(0x1000, 2)]⟩ :=
  step_syscall oracle initial fetched

theorem defined_flags_preserved :
    completeFlags native.m.core.flags high =
      ⟨some false, some false, some true, some false, some false, some false⟩ := rfl

theorem low_af_false : (pending low).native.m.core.flags.adjust = some false := rfl
theorem high_af_true : (pending high).native.m.core.flags.adjust = some true := rfl

def returned (choice : Choice) : State :=
  (x86WithFlagOracle (fun _ => choice)).advancePastSvc
    ((x86WithFlagOracle (fun _ => choice)).applyEffect (pending choice) (mkEffect 7 [] []))

theorem low_r11 : (returned low).native.m.core.read .r11 = 0x202 := rfl
theorem high_r11 : (returned high).native.m.core.read .r11 = 0x212 := rfl

theorem distinct_r11 : (returned low).native.m.core.read .r11 ≠
    (returned high).native.m.core.read .r11 := by decide +kernel

theorem choices_still_return_syscall_result (choice : Choice) :
    (returned choice).native.m.core.read .rax = 7 := rfl

theorem choices_advance_once (choice : Choice) :
    (returned choice).counter = 1 ∧ (returned choice).native.m.core.rip = 0x1002 ∧
      (returned choice).native.pending = none := ⟨rfl, rfl, rfl⟩

theorem fully_defined_equivalence (oracle : Nat → Choice) :
    step oracle ⟨X86WireControls.syscallState, 0⟩ =
      lift 1 (x86NativeStep X86WireControls.syscallState) :=
  step_defined_syscall oracle _ X86WireControls.syscall_fetched
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Silmaril.Process.LPS.Machines.X86FlagChoices.Controls
