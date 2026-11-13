module

public import Silmaril.X86.Ext.SymExec
public import Silmaril.X86.Ext.Encoding
/-! Compositional lifting of actual decoded execution to canonical loaded-byte
fetching. Trace annotations record real PC progress and per-step memory frames;
they are proved separately from any loaded-image or decoder premise. -/
@[expose] public section
namespace Silmaril.X86.FetchTrace
open Silmaril Silmaril.X86

/-- Exact actual decoded steps, annotated with sequential PC movement and a
common memory write footprint. RET is handled by the terminal return lemma. -/
inductive Trace (inside : Nat → Prop) : List Ext.Instr → X86.MState → X86.MState → Prop
  | nil (state) : Trace inside [] state state
  | cons (instruction : Ext.Instr) (rest : List Ext.Instr) (before middle after : X86.MState)
      (notRet : instruction ≠ .ret)
      (executed : Ext.exec instruction before.core before.memory = .ok middle.core middle.memory)
      (pc : middle.core.rip = before.core.rip + BitVec.ofNat 64 instruction.length)
      (memory : before.memory.WritesWithin middle.memory inside)
      (later : Trace inside rest middle after) : Trace inside (instruction :: rest) before after

def code (instructions : List Ext.Instr) : List Byte := instructions.flatMap Ext.encode

/-- Every loaded code byte lies outside the declared store footprint. -/
def Disjoint (base : Word) (bytes : List Byte) (inside : Nat → Prop) : Prop :=
  ∀ offset < bytes.length, ¬ inside (base.toNat + offset)

end Silmaril.X86.FetchTrace
