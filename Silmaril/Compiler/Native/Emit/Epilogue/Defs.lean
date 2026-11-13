module

public import Silmaril.Compiler.Native.Emit.Prologue.Defs
public import Silmaril.Machine.C.Api.SysV.Defs
/-! The actual unoptimized addition scalar return suffix. Decoded instruction
execution and integer-state return discipline are separate from GNU as. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.Epilogue
open Silmaril Silmaril.X86

def instructions : List Ext.Instr :=
  [.load .q .rax (Prologue.slot 10), .leave, .ret]

def code : List Byte := instructions.flatMap Ext.encode

def render : String := Asm.read 10 ++ "  leave\n  ret\n"

/-- Independently readable input words at the real result, saved-BP and caller
return locations. No actual suffix execution or post-state is an input. -/
structure Entry (caller before : X86.MState) (value exit : Word) : Prop where
  base : before.core.read .rbp = caller.core.read .rsp - 8
  result : before.memory.readBytes (caller.core.read .rsp - 96).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [value])
  saved : before.memory.readBytes (caller.core.read .rsp - 8).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [caller.core.read .rbp])
  returnAddress : before.memory.readBytes (caller.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [exit])

structure Ready (caller before final : X86.MState) (value exit : Word) : Prop where
  pc : final.core.rip = exit
  stack : final.core.read .rsp = caller.core.read .rsp + 8
  base : final.core.read .rbp = caller.core.read .rbp
  result : final.core.read .rax = value
  registers : ∀ register, register ≠ .rsp → register ≠ .rbp → register ≠ .rax →
    final.core.read register = before.core.read register
  flags : final.core.flags = before.core.flags
  fsBase : final.core.fsBase = before.core.fsBase
  memory : final.memory = before.memory

end Silmaril.Compiler.Native.Emit.Epilogue
