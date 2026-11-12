module

public import Silmaril.Compiler.Native.Emit.AdditionBody.Defs
public import Silmaril.Compiler.Native.Emit.Defs
/-! Actual unoptimized addition function path: activated physical frame,
intervening next-block jump, scalar body and return. Canonical decoded bytes
and exact emitted assembly text remain separate from assembler adequacy. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.AdditionFunction
open Silmaril Silmaril.X86

abbrev plan : Prologue.Plan := ⟨96, 64⟩

def instructions (left right : Word) : List Ext.Instr :=
  plan.activate 0 ++ [.jmp8 0] ++ AdditionBody.instructions left right ++ Epilogue.instructions

def code (left right : Word) : List Byte := (instructions left right).flatMap Ext.encode

/-- Both real prologue stores and all nine real scalar slots; the eight-byte
unused gap below reserved slot zero remains outside the write footprint. -/
def footprint (stack : Word) (address : Nat) : Prop :=
  Prologue.footprint stack address ∨ Scalar.footprint stack address

def signature : C.Api.Signature := ⟨[], some .int32⟩

/-- Independent standard INTEGER-state SysV call entry and frame permissions.
Only the caller return word must already have backing; saved BP, reserved
frame address and scalar slots are created by the actual emitted stores. -/
structure Entry (caller : X86.MState) (exit : Word) : Prop where
  abi : C.Api.SysV.Entry signature .nil ⟨caller.core.rip, exit, caller⟩
  lower : 176 ≤ (caller.core.read .rsp).toNat
  readable : caller.memory.Permitted .read ((caller.core.read .rsp).toNat - 96) 96
  writable : caller.memory.Permitted .write ((caller.core.read .rsp).toNat - 96) 96

structure Ready (caller final : X86.MState) (left right exit : Word) : Prop where
  returned : C.Api.SysV.Return ⟨caller.core.rip, exit, caller⟩ final
  result : final.core.read .rax = Correctness.AdditionLower.bodyValue left right
  frame : caller.memory.WritesWithin final.memory (footprint (caller.core.read .rsp))
  fsBase : final.core.fsBase = caller.core.fsBase
  saved : final.memory.readBytes (caller.core.read .rsp - 8).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [caller.core.read .rbp])
  reserved : final.memory.readBytes ((caller.core.read .rsp).toNat - 16) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [Prologue.frameAddress plan (caller.core.read .rsp)])

/-- Complete actual emitted function text, including the unreachable fallback
block retained by the real unoptimized lowerer. -/
def render (unit index : Nat) (left right : Word) : String :=
  ".text\n" ++ s!".globl {Asm.symbol "main"}\n" ++
    s!".type {Asm.symbol "main"}, @function\n{Asm.symbol "main"}:\n" ++ plan.render ++
    s!"{Emit.label unit index 0}:\n" ++ Prologue.renderFrame 0 ++
    s!"  jmp {Emit.label unit index 1}\n{Emit.label unit index 1}:\n" ++ AdditionBody.render left right ++
    Epilogue.render ++ s!"{Emit.label unit index 2}:\n" ++
    (Scalar.Operation.constant 0 0).render ++ Asm.read 2 ++ "  leave\n  ret\n" ++
    s!".size {Asm.symbol "main"}, . - {Asm.symbol "main"}\n"

end Silmaril.Compiler.Native.Emit.AdditionFunction
