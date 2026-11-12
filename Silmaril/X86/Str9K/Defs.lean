module

public import Silmaril.X86.Sys.Defs
public import Silmaril.X86.Str9G.Thms

/-!
# `Str9K`: `Str9G` with Linux memory system calls

`Str9K.isa` is `Sys.isa Str9G.isa`: the `Str9G` machine (`Str9` with FS-relative operands,
sequential atomics, SSE data movement and SSE2 integer forms, `rep stosd`, `rdtsc` and the
CET hints) plus the `syscall` step of `Silmaril.X86.Sys` (`brk`, `mmap`, `munmap`,
`mprotect`, `mremap`, `madvise`, `prctl(PR_SET_VMA)`, `getrandom`), with the kernel's decisions read
from the answer stream in the state.

It extends every machine below it (`extendsStr9G`, `extendsStr9FsX`, `extendsSse9`,
`extendsStr9Fs`, `extendsStr9`, `extendsOpen9`, `extendsOpen`), so their runs and contracts
lift unchanged.
-/

@[expose] public section

namespace Silmaril.X86.Str9K

open Silmaril.X86.SegVC (Isa)

/-- The state: a `Str9G` state, the kernel and the answer stream. -/
abbrev KState := Sys.SysState Str9G.GState

/-- `Str9G`'s invariant (`True`) survives any change of core and memory. -/
theorem live_upd : ∀ s c m, Str9G.isa.live s → Str9G.isa.live (Str9G.isa.upd s c m) :=
  fun _ _ _ _ => trivial

/-- **`Str9K`**: `Str9G` with the `syscall` step. -/
@[reducible] def isa : Isa KState := Sys.isa Str9G.isa live_upd

@[simp] theorem isa_step : isa.step = Sys.step Str9G.isa := rfl

@[reducible] def extendsStr9G : Str9G.isa.Extends isa := Sys.extends Str9G.isa _

@[reducible] def extendsStr9FsX : Str9FsX.isa.Extends isa := Str9G.extendsStr9FsX.trans extendsStr9G

@[reducible] def extendsSse9 : Silmaril.X86.Sse9.isa.Extends isa :=
  Str9G.extendsSse9.trans extendsStr9G

@[reducible] def extendsStr9Fs : Str9Fs.isa.Extends isa := Str9G.extendsStr9Fs.trans extendsStr9G

@[reducible] def extendsStr9 : Silmaril.X86.Str9.isa.Extends isa :=
  Str9G.extendsStr9.trans extendsStr9G

@[reducible] def extendsOpen9 : Silmaril.X86.Open9.isa.Extends isa :=
  Str9G.extendsOpen9.trans extendsStr9G

@[reducible] def extendsOpen : Silmaril.X86.Open.isa.Extends isa :=
  Str9G.extendsOpen.trans extendsStr9G

/-- **Every `Str9G` step is a `Str9K` step.** -/
theorem step_of_g {x : KState} {g : Str9G.GState} (h : Str9G.step x.s = some g) :
    Sys.step Str9G.isa x = some { x with s := g } := by
  simp [Sys.step, h]

/-- **The `syscall` law**: where `Str9G` has no step and the kernel answers, one step. -/
theorem step_of_sys {x y : KState} (hg : Str9G.step x.s = none)
    (h : Sys.sysStep Str9G.isa x = some y) : Sys.step Str9G.isa x = some y := by
  simp [Sys.step, hg, h]

end Silmaril.X86.Str9K
