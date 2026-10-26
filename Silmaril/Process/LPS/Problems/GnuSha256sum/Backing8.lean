module

public import Silmaril.Process.LPS.Problems.Sha256Cli.ReadSim
public import Silmaril.Process.CLI.X86Linux8

/-! # The `Ext8` forms keep the memory map and only add backing (VERIFIED)

`execNew_grows`: a retiring 8-bit form of `X86.Ext8` keeps `regions` and every backed byte
(the `X86.Ext` proof is `Ext.Backing.exec_grows`). `grows_of_step8`: so does every retiring
step of `Process.CLI.X86Linux8`; hence `Below` and `Backed` survive instructions.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.X86.Ext8.Backing

open Silmaril.X86 (State Word)
open Silmaril.X86.Ext.Backing (Grows KeepsGrows keeps_same keeps_store keeps_map retire_grows)
open Silmaril.Process (Memory)

theorem keeps_write (op : RM8) (v : BitVec 8) (s : State) (m : Memory) (next : Word) :
    KeepsGrows m (op.write v s m next) := by
  cases op with
  | reg r => exact keeps_same _ _
  | mem a => exact keeps_store _

theorem keeps_alu8 (op : Silmaril.X86.AluOp) (dst : RM8) (y : BitVec 8) (s : State) (m : Memory)
    (next : Word) : KeepsGrows m (alu8 op dst y s m next) := by
  unfold alu8
  split
  · rintro _ _ ⟨⟩
  · split
    · exact keeps_same _ _
    · exact keeps_map (keeps_write dst _ s m next) _

theorem keeps_map_same {α : Type} (m : Memory) (o : Option α) (f : α → State) :
    KeepsGrows m (o.map fun x => (f x, m)) := Silmaril.X86.Ext.Backing.keeps_map_same m o f

/-- **An 8-bit form keeps the map and the backing.** -/
theorem execNew_grows {i : New} {s : State} {m : Memory} {next : Word} {core : State}
    {m' : Memory} (h : execNew i s m next = .ok core m') : Grows m m' := by
  cases i with
  | alu op dst src => exact retire_grows (keeps_alu8 _ _ _ _ _ _) h
  | aluR op dst src =>
    simp only [execNew] at h
    split at h
    · cases h
    · exact retire_grows (keeps_alu8 _ _ _ _ _ _) h
  | aluA op imm => exact retire_grows (keeps_alu8 _ _ _ _ _ _) h
  | aluI op dst imm => exact retire_grows (keeps_alu8 _ _ _ _ _ _) h
  | test dst src => exact retire_grows (keeps_map_same _ _ _) h
  | shift op dst count =>
    simp only [execNew] at h
    split at h
    · cases h
    · split at h
      · exact retire_grows (keeps_same _ _) h
      · exact retire_grows (keeps_map (keeps_write _ _ _ _ _) _) h
  | mov dst src => exact retire_grows (keeps_write _ _ _ _ _) h
  | movR dst src => exact retire_grows (keeps_map_same _ _ _) h
  | movx sx sz dst src => exact retire_grows (keeps_map_same _ _ _) h
  | setcc c dst =>
    simp only [execNew] at h
    split at h
    · cases h
    · exact retire_grows (keeps_write _ _ _ _ _) h

end Silmaril.X86.Ext8.Backing

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

/-- A retiring step of `X86Linux8` keeps the map and the backing. -/
theorem grows_of_step8 {core core' : Silmaril.X86.State} {m m' : Silmaril.Process.Memory}
    (h : CLI.X86Linux8.step core m = .retired core' m') : Silmaril.X86.Ext.Backing.Grows m m' := by
  unfold CLI.X86Linux8.step at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · unfold CLI.X86Linux.execResult at h
      split at h
      · cases h
        exact Silmaril.X86.Ext.Backing.exec_grows ‹_›
      all_goals cases h
    · unfold CLI.X86Linux.execResult at h
      split at h
      · cases h
        exact Silmaril.X86.Ext8.Backing.execNew_grows ‹_›
      all_goals cases h

end Silmaril.Process.LPS.Problems.GnuSha256sum
