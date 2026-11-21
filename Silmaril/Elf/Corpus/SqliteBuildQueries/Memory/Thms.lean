module

public import Silmaril.Elf.Corpus.SqliteBuildQueries.Memory.Defs
public import Silmaril.Process.BlockRead.Thms
public import Silmaril.X86.MemoryModel.Refinement.Thms
public import Silmaril.Elf.Link.ElfBind.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteBuildQueries.Memory

/-! # The getter's object-level WP, transported to one x86 thread under XL -/

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Memory

open Silmaril.Semantics.MemoryRefinement
open Silmaril.Process
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.X86.MemoryModel
open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So (F)

theorem object_wp (caller : Word) : objectModel.wp (returns caller) (stackObject caller) :=
  Proofs.Elf.Corpus.SqliteBuildQueries.Memory.object_wp caller

theorem fetch_sound {req : BlockRead.FlatRequest} {start : MState} (entry : Fetched req start) :
    SoundAt flatModel sequential req start := Proofs.Elf.Corpus.SqliteBuildQueries.Memory.fetch_sound entry

def fetched : Hom flatModel sequential := ⟨Fetched, fetch_sound⟩

/-- Keep the three adapters separate: placing objects, executing code, interpreting memory events. -/
def toXL (stackBase : Nat) : Hom objectModel (machine Lattice.xl) :=
  ((BlockRead.layout (fun _ : Unit => stackBase)).map fromBytes).comp
    (fetched.comp (Refinement.singleThread Concurrency.Lift.openFlatStep Lattice.sc_le_xl (Lattice.Model.le_refl _) 2 observe))

/-- The direct-call interface: use any image loader that establishes this code placement. -/
theorem wp_of_fetched {caller : Word} {start : MState} (code : Ext.Loaded start.memory start.core.rip Getter.threadsafe.code)
    (slot : start.memory.readBytes (start.core.read .rsp).toNat 8 = some (encodeWords [caller])) :
    (machine Lattice.xl).wp (returns caller) start :=
  (toXL (start.core.read .rsp).toNat).transport
    ⟨stackRead start, Proofs.Elf.Corpus.SqliteBuildQueries.Memory.placed start caller slot,
      start, ⟨rfl, code⟩, rfl⟩ (object_wp caller)

/-- For this exact file, at any permitted placement, with any readable caller return slot.
In particular a two-step run and an admissible XL trace exist; this is not a conditional on return. -/
theorem threadsafe_xl {base caller : Word} {start : MState} (position : Placement F base.toNat)
    (image : Link.ElfBind.RoLoaded F base start.memory)
    (pc : start.core.rip = base + BitVec.ofNat 64 Getter.threadsafe.address)
    (slot : start.memory.readBytes (start.core.read .rsp).toNat 8 = some (encodeWords [caller])) :
    (machine Lattice.xl).wp (returns caller) start :=
  wp_of_fetched (Proofs.Elf.Corpus.SqliteBuildQueries.Memory.image position image pc) slot

/-- The runtime reading of the WP: the two instructions retire, and the one-thread XL trace can only
produce the returned memory. Neither successful execution nor race freedom is an entry hypothesis. -/
theorem threadsafe_returns_xl {base caller : Word} {start : MState} (position : Placement F base.toNat)
    (image : Link.ElfBind.RoLoaded F base start.memory)
    (pc : start.core.rip = base + BitVec.ofNat 64 Getter.threadsafe.address)
    (slot : start.memory.readBytes (start.core.read .rsp).toNat 8 = some (encodeWords [caller])) :
    ∃ stop, Machine.Execution.run Open.step 2 start = some stop ∧
      Concurrency.Lift.RunUnder Lattice.xl Open.step (fun s => Concurrency.Lift.flat s.memory)
        Concurrency.Lift.openActs start stop ∧
      stop.core.read .rax = 1 ∧ stop.core.rip = caller ∧
      stop.core.read .rsp = start.core.read .rsp + 8 ∧ stop.memory = start.memory :=
  let ⟨stop, ran, cert, ok⟩ := Refinement.wp_under_iff.mp (threadsafe_xl position image pc slot)
  ⟨stop, ran, cert, ok.1, Option.some.inj ok.2.1, ok.2.2⟩

end Silmaril.Elf.Corpus.SqliteBuildQueries.Memory
