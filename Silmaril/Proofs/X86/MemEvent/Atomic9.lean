module

public import Silmaril.Proofs.X86.MemEvent.Ext9

/-!
# Locality of `Atomic9`

The atomic forms are built from `Ext`'s helpers (`aluStep`, `readRM`, `writeRM`, `storeN`)
and `Ext8`'s (`alu8`, `RM8.read`, `RM8.write`), so after unfolding the step helpers
(`xaddStep`, `cmpxchgStep`, ...) each constructor is one `mev_rel`. A memory `cmpxchg` writes
on both outcomes (the failed comparison writes the old value back), so its access list is one
`rmw` event whatever the comparison; a fence is one `fence` event of size 0 that reads and
writes nothing.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemEvent

open Silmaril.X86 (State MState Word Reg Byte)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.Ext (Result retire loadN storeN RM Sz readRM writeRM)
open Silmaril.X86.Atomic9 (New execNew xaddStep cmpxchgStep cmpxchg8Step xchgStep
  xchg8Step incDecStep btsStep)
open Silmaril.X86.MemEvent

section
attribute [local irreducible] Silmaril.X86.pushWord Silmaril.X86.popWord
  Silmaril.X86.Ext.writeRM Silmaril.X86.Ext.writeNarrow Silmaril.X86.Ext.writeRM8 storeN loadN
  Silmaril.X86.Ext.aluStep Silmaril.X86.Ext.aluStepR Silmaril.X86.Ext.readRM
  Silmaril.X86.Ext.readNarrow Silmaril.X86.Ext8.RM8.read Silmaril.X86.Ext8.RM8.write
  Silmaril.X86.Ext8.alu8

/-- **`Atomic9.execNew` is local** for `atomic9NewAccesses`. -/
theorem atomic9_execNew_local (i : New) (s : State) (next : Word) :
    Local extView (fun m => execNew i s m next) (atomic9NewAccesses i s next) := by
  constructor
  intro m m' hA
  cases i <;>
    (simp only [execNew, atomic9NewAccesses, xaddStep, cmpxchgStep, cmpxchg8Step, xchgStep,
      xchg8Step, incDecStep, btsStep] at hA ⊢; mev_rel hA)

end

/-- **`Atomic9.exec` is local** for `atomic9Accesses`. -/
theorem atomic9_local (i : Silmaril.X86.Atomic9.Instr) (s : State) (len : Nat) :
    Local extView (fun m => Silmaril.X86.Atomic9.exec i s m len)
      (atomic9Accesses i s len) := by
  cases i with
  | open9 i => exact ext9_local i s len
  | new i => exact atomic9_execNew_local i s _

end Silmaril.Proofs.X86.MemEvent
