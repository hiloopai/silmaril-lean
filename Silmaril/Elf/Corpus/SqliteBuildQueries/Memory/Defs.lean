module

public import Silmaril.Elf.Corpus.SqliteBuildQueries.Defs
public import Silmaril.Process.BlockRead.Defs
public import Silmaril.X86.MemoryModel.Refinement.Defs

/-! # A memory contract for the pinned `sqlite3_threadsafe`

The literal move has no data-memory effect; `ret` reads an eight-byte caller
object. The observation is shared by the block read, flat read and machine.
It is a compile-option getter, not a concurrent API or mutex operation.
-/

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Memory

open Silmaril.Process
open Silmaril.X86
open Silmaril.Machine.LittleEndian (encodeWords)

structure Observation where
  value : Word
  target : Option Word
  popped : Prop
  unchanged : Prop

/-- What this getter promises, stated once without an ISA, layout, or consistency model. -/
def returns (caller : Word) (out : Observation) : Prop :=
  out.value = 1 ∧ out.target = some caller ∧ out.popped ∧ out.unchanged

def fromBytes (bytes : List X86.Byte) : Observation := ⟨1, wordOfBytes? bytes, True, True⟩

def observe (start stop : MState) : Observation :=
  ⟨stop.core.read .rax, some stop.core.rip, stop.core.read .rsp = start.core.read .rsp + 8, stop.memory = start.memory⟩

def stackObject (caller : Word) : BlockRead.Request Unit := ⟨fun _ => some (encodeWords [caller]), (), 0, 8⟩

def stackRead (start : MState) : BlockRead.FlatRequest := ⟨start.memory, (start.core.read .rsp).toNat, 8⟩

def objectModel := (BlockRead.objects Unit).map fromBytes
def flatModel := BlockRead.flat.map fromBytes
def sequential := MemoryModel.Refinement.sequential Open.step 2 observe
def machine (model : MemoryModel.Axiomatic.Exec → Prop) :=
  MemoryModel.Refinement.under Open.step (fun s => Concurrency.Lift.flat s.memory) Concurrency.Lift.openActs model 2 observe

/-- The only relation needed to decode a flat read as this call. It does not assume a run. -/
def Fetched (req : BlockRead.FlatRequest) (start : MState) : Prop :=
  req = stackRead start ∧ Ext.Loaded start.memory start.core.rip Getter.threadsafe.code

end Silmaril.Elf.Corpus.SqliteBuildQueries.Memory
