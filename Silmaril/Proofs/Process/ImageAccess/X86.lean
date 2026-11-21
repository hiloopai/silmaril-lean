module

public import Silmaril.Process.ImageAccess.Thms
public import Silmaril.Process.ImageAccess.X86.Defs

@[expose] public section

namespace Silmaril.Proofs.Process.ImageAccess.X86

open Silmaril.Process (Memory)
open Silmaril.Process.ImageAccess
open Silmaril.Process.ImageAccess.X86 (load)
open Silmaril.X86 (Reg State)
open Silmaril.X86.Ext (Mem Sz exec readRM loadN)

theorem load_full (size : Sz) (dest : Reg) (src : Mem) (core : State)
    (memory : Memory) (length : Nat) :
    (match (load size dest src core length).run (Image.full memory).localReader with
      | .ok after => some (Silmaril.X86.Ext.Result.ok after memory)
      | .error .fault => some .dataFault
      | .error _ => none) = some (exec (.load size dest src) core memory length) := by
  simp only [load, Program.run, Image.localReader, Image.reader,
    Image.full, exec, readRM, loadN, Memory.readBytes]
  cases memory.readWith .read (src.addr core (core.rip + BitVec.ofNat 64 length)).toNat
    size.bytes <;> rfl

theorem load_exec_of_wp {size : Sz} {dest : Reg} {src : Mem} {core : State}
    {memory : Memory} {length : Nat} {source : Reader} {post : State → Prop}
    (refines : Reader.Refines (Image.full memory).localReader source)
    (safe : (load size dest src core length).wp source post) :
    ∃ after, exec (.load size dest src) core memory length = .ok after memory ∧ post after := by
  obtain ⟨after, run, holds⟩ := (Program.wp_iff_run _).mp (Program.wp_transfer refines _ safe)
  exact ⟨after, Option.some.inj (by simpa only [run] using
    (load_full size dest src core memory length).symm), holds⟩

end Silmaril.Proofs.Process.ImageAccess.X86
