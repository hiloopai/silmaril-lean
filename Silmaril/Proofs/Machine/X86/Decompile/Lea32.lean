module

public import Silmaril.Machine.X86.Decompile.Lea32.Defs
public import Silmaril.Machine.X86.Decompile.Features.Thms

@[expose] public section
namespace Silmaril.Machine.X86.Decompile.Lea32
open Silmaril Silmaril.X86
open Silmaril.Machine.X86.Decompile.Features (lift)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem decoded {bytes : List Byte} {destination : Reg} {address : Ext.Mem} {length : Nat}
    (accepted : check bytes destination address length = true) :
    Ext.decode bytes = some (.lea .d destination address, length) := by
  exact of_decide_eq_true accepted

/-- The decoder check and actual loaded bytes determine the real retirement.
No successful execution, data access, or symbolic-address premise is assumed. -/
theorem step_sound {base exit : Word} {bytes : List Byte} {machine : X86.MState}
    {offset length : Nat} {destination : Reg} {address : Ext.Mem}
    (original : Silmaril.X86.Features.State)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (loaded : Ext.Loaded machine.memory base bytes)
    (pc : machine.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + length ≤ bytes.length)
    (accepted : check ((bytes.drop offset).take length) destination address length = true) :
    Silmaril.X86.Features.step featureSet extensions exit (lift original machine) =
      .retired (lift original (next machine destination address length)) := by
  have actualDecode : Ext.decode ((bytes.drop offset).take length) =
      some (.lea .d destination address, length) := decoded accepted
  have instructionLength : (Ext.Instr.lea .d destination address).length = length :=
    (Ext.decode_length actualDecode).1.symm
  have executed : Ext.exec (.lea .d destination address) machine.core machine.memory =
      .ok (next machine destination address length).core machine.memory := by
    change Ext.exec (.lea .d destination address) machine.core machine.memory =
      .ok { machine.core.write destination
        (((address.addr machine.core (machine.core.rip + BitVec.ofNat 64 length)).setWidth 32).setWidth 64)
        with rip := machine.core.rip + BitVec.ofNat 64 length } machine.memory
    simp only [Ext.exec, instructionLength]
    rfl
  have actualStep : Ext.stepOpt exit machine = some (next machine destination address length) :=
    Ext.stepOpt_of_loaded loaded pc fits actualDecode (by simp) executed
  exact Silmaril.Machine.X86.Decompile.Features.retire_of_loaded original featureSet extensions
    loaded pc fits actualDecode (by rfl) actualStep

theorem run_sound {base exit : Word} {bytes : List Byte} {machine : X86.MState}
    {offset length : Nat} {destination : Reg} {address : Ext.Mem}
    (original : Silmaril.X86.Features.State)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (loaded : Ext.Loaded machine.memory base bytes)
    (pc : machine.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + length ≤ bytes.length)
    (accepted : check ((bytes.drop offset).take length) destination address length = true) :
    Silmaril.X86.Features.run featureSet extensions exit 1 (lift original machine) =
      some (lift original (next machine destination address length)) := by
  have retired : Silmaril.X86.Features.step featureSet extensions exit (lift original machine) =
      .retired (lift original (next machine destination address length)) :=
    step_sound original featureSet extensions loaded pc fits accepted
  rw [Silmaril.X86.Features.run_succ, Silmaril.X86.Features.stepOpt_eq_some_iff.mpr retired]
  rfl

end Silmaril.Machine.X86.Decompile.Lea32
