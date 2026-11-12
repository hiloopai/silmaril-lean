module

public import Silmaril.Problems.Models.Proc.Defs
public import Silmaril.X86.Str9FsXN.Defs

/-!
# `musl-str9fsx`: the musl process model with the XMM file, SSE moves and atomics

`musl-str9` (`Models.Proc`) stops with the `unmodeled` fault at the first SSE instruction. In a
static musl executable that is `vfprintf`'s prologue (`pxor xmm0, xmm0`, `movaps` and `movups`
stores of zeroed XMM registers, `movdqu` of the `va_list`), so every run through `printf`,
`snprintf` or `fprintf` ends there. musl's `__lock`, `__lockfile` and `__unlockfile` also use
`lock cmpxchg`, `lock xadd` and `xchg m32, r32`, which `Str9` does not decode either.

`model` is `musl-str9` with one change: the instruction step is `Silmaril.X86.Str9FsX.step`
over the core and **sixteen XMM registers**, instead of `Str9.step` over the core. `Str9FsX`
is `Str9` followed by `Str9Fs`'s atomic and FS-segment forms, `Sse9`'s SSE data-movement
subset (`movups`/`movaps`/`movdqu`/`movdqa` both ways, `movd`/`movq`, `pxor`, `xorps`,
`punpckl{dq,qdq}`) and `rep stosd`. The step is `Silmaril.X86.Str9FsXN.step`: `Str9FsX` followed
by the `Narrow9` forms (`rol`/`ror`/`shl`/`shr`/`sar r/m16`, `rol`/`ror r/m8`, `adc`/`sbb` at 8
and 16 bits), which zlib's compressor needs (`shr r/m16, imm8` in `deflate_fast`,
`deflate_slow`, `_tr_align`, `_tr_flush_bits`; `sbb r/m8, imm8` in `deflate`). `Str9FsXN`
extends `Str9FsX` on the same states (`Str9FsXN.extendsStr9FsX`). Everything else is
`musl-str9`'s:

* `syscall` (`0F 05`) is recognised first; `none` from `Str9FsXN.step` is `unmodeled`;
* the startup calls (`arch_prctl (ARCH_SET_FS)`, `set_tid_address`) retire silently as in
  `Proc.Startup`; they and every other system call leave the XMM file unchanged (the Linux
  `syscall` ABI preserves the vector registers);
* the request decoder, the resume (`X86Linux.Resume`), the environment `Env.linux`, its
  initial state and the loader `Proc.Load` act on the integer core. The loader leaves the
  initial XMM file **arbitrary**, as `X86Linux.Loaded` leaves the general registers other than
  `rsp` and `rdx` arbitrary (Linux zeroes them at `execve`; the model does not rely on it).

**Relation to `musl-str9`** (`Thms`). Every step of `musl-str9` that is not the `unmodeled`
fault is a step here with the XMM file as a frame (`userStep_of_proc`), so
`Proc.model.GapLe model` (`gapLe`): `Agrees`, `Halts` and `Bounded` statements proved here hold
for `musl-str9` (`agrees_proc`, `halts_proc`, `bounded_proc`), and every nonvacuity witness of
`musl-str9` is one here (`exitsOn_of_proc`). The converse does not hold: a run that `musl-str9`
stops at an SSE instruction continues here.

**Trust.** A model, not a theorem: `musl-str9`'s trust base, and the handwritten `Atomic9`,
`Str9Fs`, `Sse9` and `Narrow9` semantics (written from the Intel SDM and differentially tested against
the host CPU outside this repository, not proved to correspond to hardware). MXCSR, x87, the
upper YMM/ZMM halves and the direction flag are not modelled (no instruction here reads or
writes them; DF is clear, as in `Str9`). Whether every instruction on a witness path is
decoded is **not checked** here.
-/

@[expose] public section

namespace Silmaril.Problems.Models.ProcX

open Silmaril.Process.CLI
open Silmaril.X86 (State MState)
open Silmaril.X86.Sse9 (XState XFile)
open Silmaril.Process (Memory)

/-- The user-mode core: the integer core and the XMM file. -/
structure Core where
  core : State
  xmm : XFile

/-- One user-mode step: `syscall` traps; otherwise one `Str9FsXN` step (`none`: unmodeled). -/
def userStep (c : Core) (memory : Memory) : Step Core :=
  if memory.fetchBytes c.core.rip.toNat 2 = some X86Linux.syscallBytes then
    .syscall { c with core := { c.core with rip := c.core.rip + 2 } }
  else
    match Silmaril.X86.Str9FsXN.step ⟨⟨c.core, memory⟩, c.xmm⟩ with
    | some next => .retired ⟨next.m.core, next.xmm⟩ next.m.memory
    | none => .fault .unmodeled

/-- A `musl-str9` step result with the XMM file `x` as a frame. -/
def liftStep (x : XFile) : Step State → Step Core
  | .retired c m => .retired ⟨c, x⟩ m
  | .syscall c => .syscall ⟨c, x⟩
  | .fault f => .fault f

/-- The core after a silently answered startup call: `Proc.Startup`, XMM file unchanged. -/
def Startup (trapped core' : Core) : Prop :=
  Proc.Startup trapped.core core'.core ∧ core'.xmm = trapped.xmm

/-- **The instruction-set model**: `userStep`, with the startup calls retired silently. -/
def isa : Isa where
  Core := Core
  step c memory o :=
    match userStep c memory with
    | .syscall trapped =>
      if Proc.isStartup trapped.core then ∃ c', Startup trapped c' ∧ o = .retired c' memory
      else o = .syscall trapped
    | r => o = r
  request c := X86Linux.request c.core
  resume c result c' := X86Linux.Resume c.core result c'.core ∧ c'.xmm = c.xmm

/-- **The loader**: `Proc.Load` on the integer core; the XMM file is arbitrary. -/
def Load (image : Image) (input : ProcInput) (c : Core) (memory : Memory) : Prop :=
  Proc.Load image input c.core memory

/-- **`musl-str9fsx`**: `isa` in the Linux environment `Env.linux`, loaded by `Load`. -/
def model : Model where
  isa := isa
  env := Env.linux
  envInit := linuxInit
  load := Load

end Silmaril.Problems.Models.ProcX
