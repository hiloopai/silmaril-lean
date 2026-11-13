module

public import Silmaril.Machine.X86.Decompile.Returns.Defs

@[expose] public section
namespace Silmaril.Machine.X86.Decompile.Returns
open Silmaril Silmaril.X86
open Silmaril.Machine.X86.Decompile.Features (lift)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Actual fetched RET bytes and the actual stack return word complete a call.
Neither a successful execution nor any auxiliary control-state field is assumed. -/
theorem from_stack {base exit : Word} {bytes : List Byte} {machine : X86.MState}
    {offset len : Nat} (original : Silmaril.X86.Features.State)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (loaded : Ext.Loaded machine.memory base bytes)
    (pc : machine.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : Ext.decode ((bytes.drop offset).take len) = some (.ret, len))
    (held : Ext.HoldsLE machine.memory (machine.core.read .rsp).toNat 8 exit) :
    Silmaril.X86.Features.step featureSet extensions exit (lift original machine) =
      .returned (lift original
        ⟨{ machine.core.write .rsp (machine.core.read .rsp + 8) with rip := exit }, machine.memory⟩) := by
  have fetched : Ext.fetch machine.memory machine.core.rip.toNat = .decoded .ret len := by
    apply Ext.fetch_eq_decoded_iff.mpr
    refine ⟨(bytes.drop offset).take len, ?_, decoded⟩
    rw [pc, loaded.toNat_add (by have := (Ext.decode_length decoded).2.1; omega)]
    exact loaded.fetchBytes_sub (Ext.decode_length decoded).2.1 fits
  have baseStep := Silmaril.X86.Features.step_of_base
    (m := lift original machine) (F := featureSet) (exts := extensions) (exit := exit) fetched
  rw [baseStep]
  have returned := Ext.step_returned_ret_mk (exit := exit) (base := base) (bytes := bytes)
    (m := machine) (offset := offset) (len := len) loaded pc fits decoded held
  change Silmaril.X86.Features.Outcome.ofBase (original.setCore machine.core)
    (Ext.step exit machine) = _
  rw [returned]
  rfl

end Silmaril.Machine.X86.Decompile.Returns
