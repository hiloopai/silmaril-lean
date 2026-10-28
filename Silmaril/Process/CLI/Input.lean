module

public import Silmaril.Process.CLI.Env

/-! # Process inputs and executable images

`ProcInput` is what whoever runs the program chooses: the argument and
environment strings and standard input. It is the counterpart of LPS's
`State.ProcInput` restricted to a CLI filter (no file system, credentials,
network or signal mask yet; see `docs` in the research note). `Launch`-like
choices the program cannot control (stack address, `AT_RANDOM` bytes, extra
mappings, register garbage) are *not* inputs: statements quantify over them in
the loader relation (`CLI.X86Linux.Loaded`), so a proof cannot depend on them.

`Image` is the loadable part of a static `ET_EXEC` ELF: the entry address and
the `PT_LOAD` segments, as the Rust lifter emits them. File bytes are explicit;
the rest of each segment up to `memSize` is zero (`.bss`).
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall

structure ProcInput where
  argv : List (List Byte)
  envp : List (List Byte)
  stdin : InputStream

/-- Strings passed through `execve` cannot contain NUL. -/
def ProcInput.Valid (input : ProcInput) : Prop :=
  (∀ arg ∈ input.argv, (0 : Byte) ∉ arg) ∧ (∀ var ∈ input.envp, (0 : Byte) ∉ var)

/-- A `PT_LOAD` segment. -/
structure Segment where
  vaddr : Nat
  memSize : Nat
  permissions : Permissions
  fileBytes : List Byte

/-- The segment's full contents: file bytes, then zero fill. -/
def Segment.contents (segment : Segment) : List Byte :=
  segment.fileBytes ++ List.replicate (segment.memSize - segment.fileBytes.length) 0

def Segment.region (segment : Segment) : Region :=
  ⟨segment.vaddr, segment.memSize, segment.permissions⟩

structure Image where
  entry : Nat
  segments : List Segment

/-- Each segment's file bytes fit in its memory size, and no segment wraps. -/
def Image.WF (image : Image) : Prop :=
  ∀ segment ∈ image.segments,
    segment.fileBytes.length ≤ segment.memSize ∧ segment.vaddr + segment.memSize ≤ addressLimit

/-- The image is mapped: every segment's region is a mapping with its contents.
Other mappings (stack, vDSO, vvar) may exist. -/
def Image.Mapped (image : Image) (memory : Memory) : Prop :=
  ∀ segment ∈ image.segments, segment.region ∈ memory.regions ∧
    ∀ index (bound : index < segment.contents.length),
      memory.bytes.get? (segment.vaddr + index) = some segment.contents[index]

/-- The standard descriptors of a filter: stdin readable from the input stream,
stdout and stderr writable and empty. Other inherited descriptors are arbitrary. -/
def StdDescriptors (input : ProcInput) (descriptors : Nat → Option Descriptor) : Prop :=
  descriptors 0 = some ⟨true, false, input.stdin, 0, []⟩ ∧
  descriptors 1 = some ⟨false, true, .ofList [], 0, []⟩ ∧
  descriptors 2 = some ⟨false, true, .ofList [], 0, []⟩

/-- Initial states of the `Process.Syscall` environments. -/
def linuxInit (input : ProcInput) (memory : Memory) (state : Syscall.State) : Prop :=
  state.memory = memory ∧ state.exited = none ∧ StdDescriptors input state.descriptors

end Silmaril.Process.CLI
