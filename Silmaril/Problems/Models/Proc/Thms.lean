module

public import Silmaril.Problems.Models.Proc.Defs

/-!
# `musl-str9`: the static loader and the loader before erebor-lean #70

`Load` is `LoadLoose` plus `X86Linux.Static`, so `model ≼ modelLoose` (`le_loose`):

* universal statements move from `modelLoose` to `model` (`agrees_of_loose`,
  `covered_of_loose`, `halts_of_loose`, `bounded_of_loose`): every result proved over
  the old loader still holds;
* existential statements move the other way (`exitsOn_loose`): a nonvacuity witness
  over `model` is one over `modelLoose`, not conversely. Witnesses proved over the old
  loader must be re-proved with a static launch (in erebor-lean, the `ExitsOn`
  companions and any launch built for `Proc.Load`).

`load_headers`: in every launch of `model`, the table musl's startup reads at `AT_PHDR`
holds the file's program-header bytes (`X86Linux.LoadedStatic.headers`).
-/

@[expose] public section

namespace Silmaril.Problems.Models.Proc

open Silmaril.Process.CLI
open Silmaril.X86 (State)
open Silmaril.Process (Memory)

theorem Load.loose {image : Image} {input : ProcInput} {core : State} {memory : Memory}
    (h : Load image input core memory) : LoadLoose image input core memory := h.1

theorem Load.loadedStatic {image : Image} {input : ProcInput} {core : State} {memory : Memory}
    (h : Load image input core memory) : X86Linux.LoadedStatic image input core memory :=
  ⟨h.1.1, h.2⟩

/-- **The static loader refines the old one.** -/
theorem le_loose : model.Le modelLoose :=
  ⟨{ isa := Isa.Sim.id isa
     env := Env.Sim.id Env.linux
     envInit := fun {_ _ s} init => ⟨s, init, rfl⟩
     load := fun {_ _ c _} load => ⟨c, load.1, rfl⟩ }⟩

theorem agrees_of_loose {image : Image} {S : CliSpec} (h : Agrees modelLoose image S) :
    Agrees model image S := Agrees.mono le_loose h

theorem covered_of_loose {image : Image} (h : Covered modelLoose image) : Covered model image :=
  Covered.mono le_loose h

theorem halts_of_loose {image : Image} {domain : ProcInput → Prop}
    (h : Halts modelLoose image domain) : Halts model image domain := Halts.mono le_loose h

theorem bounded_of_loose {image : Image} {domain : ProcInput → Prop} {budget : ProcInput → Nat}
    {perRefusal : Nat} (h : Bounded modelLoose image domain budget perRefusal) :
    Bounded model image domain budget perRefusal := Bounded.mono le_loose h

/-- A nonvacuity witness of `model` is one of `modelLoose` (same runs, a stricter launch). -/
theorem exitsOn_loose {image : Image} {stdin : List Silmaril.Process.Byte}
    (h : ExitsOn model image stdin) : ExitsOn modelLoose image stdin := by
  obtain ⟨input, x, events, y, valid, stdinEq, ⟨m, load, init⟩, run, stop⟩ := h
  exact ⟨input, x, events, y, valid, stdinEq, ⟨m, load.1, init⟩, run, stop⟩

/-- **Startup reads the file's program headers.** -/
theorem load_headers {image : Image} {input : ProcInput} {core : State} {memory : Memory}
    (h : Load image input core memory) :
    ∃ table, image.StaticTable table ∧
      (BitVec.ofNat 64 table.address).toNat = table.address ∧
      memory.readBytes table.address table.size = some table.bytes ∧
      ∀ argv envp auxv, X86Linux.StackVectors input memory (core.read .rsp).toNat argv envp auxv →
        X86Linux.AuxvPinned table auxv :=
  h.loadedStatic.headers

end Silmaril.Problems.Models.Proc
