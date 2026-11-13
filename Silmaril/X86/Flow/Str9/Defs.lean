module

public import Silmaril.X86.Flow.X64.Defs
public import Silmaril.X86.Str9.Defs

/-!
# The single-threaded `Str9` machine as a flow machine, and its flow-law obligation

`Str9` (the open machine over `Ext9` with the string forms) is the base user machine of the
effects layer: one thread, no system-call step (a `syscall` is the kernel arm of the process,
`Silmaril.Elf.Effects.Step.sys`). `str9` views it as a `UMach`.

`Task.flowLaw_str9` is the obligation that ties the `X64` classification to `Str9`'s steps:
from bytes `X64.dec` reads as `i`, every `Str9` step is admitted by `i`'s kind and keeps its
`rax` transfer. It is open. The effect theorems take it as a hypothesis (`Setting.law`).
-/

@[expose] public section

namespace Silmaril.X86.Flow

open Silmaril.X86 (MState)

/-- **`Str9` as a flow machine.** -/
def str9 : UMach MState where
  step s t := Str9.step s = some t
  core := MState.core
  mem := MState.memory

/-- **The flow law of `Str9` for `X64`** (open). -/
def Task.flowLaw_str9 : Prop := FlowLaw str9 X64.dec

end Silmaril.X86.Flow
