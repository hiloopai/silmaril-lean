module

public import Silmaril.Elf.Corpus.SqliteBuildQueries.Memory.Defs
public import Silmaril.Elf.Corpus.SqliteBuildQueries.Thms
public import Silmaril.Elf.BindEq.Thms
public import Silmaril.Process.BlockRead.Thms
public import Silmaril.X86.Open.Thms

/-! # The two retirements and the placement witnesses for the SQLite memory contract -/

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteBuildQueries.Memory

open Silmaril.Elf Silmaril.Elf.Corpus.SqliteBuildQueries Silmaril.Elf.Corpus.SqliteBuildQueries.Memory
open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Semantics.MemoryRefinement
open Silmaril.X86
open Silmaril.Process

theorem object_wp (caller : Word) : objectModel.wp (returns caller) (stackObject caller) := by
  apply (wp_map _ _ _ _).2
  apply (BlockRead.wp_iff _ _).2
  refine ⟨encodeWords [caller], rfl, by simp [stackObject], by simp [stackObject], ?_⟩
  simp [stackObject, fromBytes, returns, List.take_of_length_le]

theorem placed (s : MState) (caller : Word)
    (slot : s.memory.readBytes (s.core.read .rsp).toNat 8 = some (encodeWords [caller])) :
    BlockRead.Placed (fun _ => (s.core.read .rsp).toNat) (stackObject caller) (stackRead s) := by
  refine ⟨⟨?_, fun _ _ _ _ ne => False.elim (ne (Subsingleton.elim ..))⟩, rfl, rfl⟩
  rintro _ _ ⟨⟩
  simpa [stackRead] using slot

theorem image {base : Word} {s : MState} (position : Placement F base.toNat)
    (image : Link.ElfBind.RoLoaded F base s.memory)
    (pc : s.core.rip = base + BitVec.ofNat 64 Getter.threadsafe.address) :
    Ext.Loaded s.memory s.core.rip Getter.threadsafe.code := by
  rw [pc]
  exact (Proofs.Elf.BindEq.directCall_of_roLoaded' parses rfl rfl threadsafe_at position image).1

theorem two_steps {s : MState} {bytes : List X86.Byte}
    (loaded : Ext.Loaded s.memory s.core.rip Getter.threadsafe.code)
    (read : s.memory.readBytes (s.core.read .rsp).toNat 8 = some bytes) :
    (run Open.step 2 s).map (observe s) = some (fromBytes bytes) := by
  obtain ⟨addr, decoded⟩ := wordOfBytes?_isSome (Process.Memory.readWith_length read)
  let mid : MState := ⟨{ s.core.write .rax 1 with rip := s.core.rip + 5 }, s.memory⟩
  have mov : Open.step s = some mid :=
    Open.step_of_listed (o := 0) (l := 5) (i := .base (.movI32 .rax 1)) loaded
      (by simp) (by decide) (by decide +kernel) rfl
  have sp : mid.core.read .rsp = s.core.read .rsp := by simp [mid, State.read_write_other]
  have pop : popWord mid.core mid.memory = some (addr, mid.core.write .rsp (s.core.read .rsp + 8)) := by
    simp [popWord, sp, show mid.memory = s.memory from rfl, read, decoded]
  let stop : MState := ⟨{ mid.core.write .rsp (s.core.read .rsp + 8) with rip := addr }, s.memory⟩
  have ret : Open.step mid = some stop :=
    Open.step_of_listed (o := 5) (l := 1) (i := .base .ret) (m := mid) loaded
      rfl (by decide) (by decide +kernel) (by simp only [Ext8.exec, Ext.exec, pop]; rfl)
  have done : run Open.step 2 s = some stop := by simp only [run, mov, ret, Option.bind_some]
  rw [done]
  simp [observe, fromBytes, decoded, stop, mid, State.read_write_other]

theorem fetch_sound {req : BlockRead.FlatRequest} {start : MState} (entry : Fetched req start) :
    SoundAt flatModel sequential req start := by
  obtain ⟨rfl, loaded⟩ := entry
  intro safe
  obtain ⟨bytes, read⟩ := Option.ne_none_iff_exists'.mp safe
  have ran := two_steps loaded read
  exact ⟨fun bad => Option.some_ne_none _ (ran.symm.trans bad),
    fun _ allowed => ⟨bytes, read, Option.some.inj (ran.symm.trans allowed)⟩⟩

end Silmaril.Proofs.Elf.Corpus.SqliteBuildQueries.Memory
