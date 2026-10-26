module

public import Silmaril.Process.LPS.Machines.X86WireFlagOracle
public import Silmaril.Process.LPS.Machines.X86FlagChoicesControls
public import Silmaril.Process.LPS.Machines.X86RepStosqControls

/-! Fetched syscall and REP controls for the additive shared flag oracle. -/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86FlagOracleControls

open Silmaril.X86
open X86FlagChoices (Choice)

/-- The deterministic extended adapter still declines the unknown AF state. -/
theorem deterministic_declines (platform : Ext.Wire.Platform) :
    X86RepStosq.step platform X86FlagChoices.Controls.native = .unmodeled := by
  rw [X86FlagOracle.rep_syscall_agreement platform _ X86FlagChoices.Controls.fetched]
  exact X86FlagChoices.Controls.deterministic_native_declines

/-- Every oracle, not just a selected Boolean, can execute this fetched syscall. -/
theorem rep_every_oracle (platform : Ext.Wire.Platform) (oracle : Nat → Choice) :
    (x86WireDf0RepStosqWithFlagOracle platform oracle).step [] X86FlagChoices.Controls.initial =
      .ok ⟨X86FlagChoices.Controls.pending (oracle 0), [(0x1000, 2)]⟩ :=
  X86FlagOracle.rep_every_oracle_syscall platform oracle _ X86FlagChoices.Controls.fetched

theorem wire_every_oracle (platform : Ext.Wire.Platform) (oracle : Nat → Choice) :
    (x86WireWithFlagOracle platform oracle).step [] X86FlagChoices.Controls.initial =
      .ok ⟨X86FlagChoices.Controls.pending (oracle 0), [(0x1000, 2)]⟩ := by
  exact X86FlagOracle.every_oracle_syscall _
    (fun state fetched => X86Wire.common_result platform state (.inl fetched))
    oracle X86FlagChoices.Controls.initial X86FlagChoices.Controls.fetched

def returned (platform : Ext.Wire.Platform) (choice : Choice) : X86FlagChoices.State :=
  (x86WireDf0RepStosqWithFlagOracle platform (fun _ => choice)).advancePastSvc
    ((x86WireDf0RepStosqWithFlagOracle platform (fun _ => choice)).applyEffect
      (X86FlagChoices.Controls.pending choice) (mkEffect 7 [] []))

/-- Shared native memory/return hooks reuse the original R11 and result proofs. -/
theorem returned_agreement (platform : Ext.Wire.Platform) (choice : Choice) :
    returned platform choice = X86FlagChoices.Controls.returned choice := rfl

theorem distinct_r11 (platform : Ext.Wire.Platform) :
    (returned platform X86FlagChoices.Controls.low).native.m.core.read .r11 ≠
      (returned platform X86FlagChoices.Controls.high).native.m.core.read .r11 :=
  X86FlagChoices.Controls.distinct_r11

theorem defined_flags_preserved :
    X86FlagChoices.completeFlags X86FlagChoices.Controls.native.m.core.flags
      X86FlagChoices.Controls.high =
      ⟨some false, some false, some true, some false, some false, some false⟩ :=
  X86FlagChoices.Controls.defined_flags_preserved

theorem rep_not_syscall :
    (X86RepStosqControls.state 1 0x4000).m.memory.fetchBytes 0x1000 2 ≠
      some [0x0f, 0x05] := by
  have first := Silmaril.X86.Memory.readWith_slice (X86RepStosqControls.fetched true)
    0 2 (by decide) (by decide)
  intro syscall
  change (X86RepStosqControls.memory true).fetchBytes 0x1000 2 = some [0xf3, 0x48] at first
  change (X86RepStosqControls.memory true).fetchBytes 0x1000 2 = some [0x0f, 0x05] at syscall
  rw [first] at syscall
  contradiction

/-- REP does not consume a syscall choice or alter even undefined flags. -/
theorem rep_iteration_no_choice (platform : Ext.Wire.Platform) (oracle : Nat → Choice) :
    (x86WireDf0RepStosqWithFlagOracle platform oracle).step []
        ⟨X86RepStosqControls.state 1 0x4000, 7⟩ =
      .ok ⟨⟨X86RepStosqControls.next 1, 7⟩, [(0x1000, 3), (0x4000, 8)]⟩ := by
  change X86FlagOracle.stepUsing (X86RepStosq.step platform) oracle
    ⟨X86RepStosqControls.state 1 0x4000, 7⟩ = _
  rw [X86FlagOracle.not_syscall _ oracle
    ⟨X86RepStosqControls.state 1 0x4000, 7⟩ rep_not_syscall]
  have executed : X86RepStosq.step platform (X86RepStosqControls.state 1 0x4000) =
      .ok ⟨X86RepStosqControls.next 1, [(0x1000, 3), (0x4000, 8)]⟩ :=
    X86RepStosqControls.one_element platform
  rw [executed]
  rfl

end Silmaril.Process.LPS.Machines.X86FlagOracleControls
