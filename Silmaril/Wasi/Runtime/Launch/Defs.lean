module

public import Silmaril.Wasi.Runtime.Defs

@[expose] public section

/-!
# `hello`'s x86 runtime at an ELF launch (Part D of `docs/projects/wasm-wasi.md`)

`Silmaril.Wasi.Runtime` proves the program `helloCode` a runtime of `hello` from `helloStart`,
whose memory `helloMem` holds only the code and `hi` (no stack, its own two mappings). Its
process-safety theorem `helloImg_psafe8` assumes an LPS configuration aligned with
`helloStart`, and LPS never launches one. This module states the same program at a real
launch:

* `HelloMem M`: the memory `M` holds `helloCode` fetchable at `codeBase` and `hi` readable at
  `dataBase`. `RegsAtM`, `helloInvM`, `helloFinM`: `RegsAt`, `helloInv`, `helloFin` over any
  such memory (the memory is fixed along the run; the other registers, the stack and the flags
  are free).
* The ELF image `helloImage`: an `rx` segment with `helloCode` at `0x401000` (the entry
  point) and an `r` segment with `hi` at `0x402000`. `helloPhdrs` places the two-entry program
  header table inside the `r` segment, padded to `2 * 56` bytes after `hi` (`helloDataSeg`), so
  the table is readable as `X86Launch.ValidSnapshot` asks.
* `helloSnapshot`: the image with an ELF header and two `PT_LOAD` program headers matching it,
  as silmaril's parsed records (`X86Launch.Snapshot`); no ELF file bytes are given, and the
  table room holds zeros, not the encoded headers. `helloEn`, `helloInp`: a launch entry and
  input for which the snapshot passes LPS's launch check `X86Launch.ValidEntry`.

The launch state `launchState snapshot en inp` (`Silmaril.Machine.Process.LpsBridge`) of every
snapshot of `helloImage` then runs the program (`Silmaril.Proofs.Wasi.Runtime.Launch`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Runtime.Launch

open Silmaril.Process.LPS
open Silmaril.X86 (MState)
open Silmaril.Process (Memory)
open Silmaril.Wasi.Runtime (codeBase dataBase helloCode)
open Silmaril.Wasi.Examples (hiBytes)

/-- **The memory holds the program**: `helloCode` fetchable at `codeBase`, `hi` readable at
`dataBase`. -/
structure HelloMem (M : Memory) : Prop where
  loaded : Silmaril.X86.Ext.Loaded M codeBase helloCode
  data0 : Machines.viewByte M .read dataBase = some 0x68
  data1 : Machines.viewByte M .read (dataBase + 1#64) = some 0x69

/-- `m` runs the program at offset `o` in memory `M`, with `rax, rdi, rsi, rdx = a, d, s, x`. -/
def RegsAtM (M : Memory) (o : Nat) (a d s x : Word) (m : MState) : Prop :=
  m.memory = M ∧ m.core.rip = codeBase + BitVec.ofNat 64 o ∧ m.core.read .rax = a ∧
    m.core.read .rdi = d ∧ m.core.read .rsi = s ∧ m.core.read .rdx = x

/-- The loop invariant in memory `M`. -/
def helloInvM (M : Memory) (bs : List Byte) (m : MState) : Prop :=
  ∃ j, j < 2 ∧ bs = hiBytes.drop j ∧
    RegsAtM M 20 1#64 1#64 (dataBase + BitVec.ofNat 64 j) (BitVec.ofNat 64 (2 - j)) m

/-- The loop has finished, in memory `M`. -/
def helloFinM (M : Memory) (m : MState) : Prop := ∃ a d s x, RegsAtM M 30 a d s x m

/-- The size of an ELF64 program header. -/
def phent : Nat := 56

/-- The code segment: `helloCode` at `0x401000`, read-execute. -/
def helloCodeSeg : Segment := ⟨0x401000, 42, "rx", helloCode⟩

/-- The bytes of the data segment: `hi`, then the two program headers' room (zeros). -/
def helloDataBytes : List Byte := hiBytes ++ List.replicate (2 * phent) 0

/-- The data segment: `hi` at `0x402000`, then room for the program header table; read-only. -/
def helloDataSeg : Segment := ⟨0x402000, 2 + 2 * phent, "r", helloDataBytes⟩

/-- The program header table: two entries at `0x402002`. -/
def helloPhdrs : PhdrInfo := ⟨0x402002, phent, 2⟩

/-- **The image**: the two segments, entry point `0x401000`. -/
def helloImage : Image := ⟨[helloCodeSeg, helloDataSeg], 0x401000, helloPhdrs⟩

/-- The `PT_LOAD` header of a segment with flags `fl` (`1` execute, `2` write, `4` read). -/
def loadPh (seg : Segment) (fl : Nat) : Silmaril.Formats.ELF.ProgramHeader :=
  { kind := 1, flags := fl, offset := 0, virtualAddress := seg.base, physicalAddress := seg.base,
    fileSize := seg.size, memorySize := seg.size, alignment := 0x1000 }

/-- The ELF header: `ET_EXEC` for x86-64, entry `0x401000`, two program headers. -/
def helloHeader : Silmaril.Formats.ELF.Header :=
  { fileType := 2, machine := 62, version := 1, osABI := 0, abiVersion := 0, entry := 0x401000,
    programOffset := 64, sectionOffset := 0, flags := 0, headerSize := 64,
    programEntrySize := 56, programCount := 2, sectionEntrySize := 64, sectionCount := 0,
    sectionNameIndex := 0 }

/-- **The ELF snapshot** of `hello`'s runtime. -/
def helloSnapshot : Machines.X86Launch.Snapshot :=
  ⟨helloHeader, [loadPh helloCodeSeg 5, loadPh helloDataSeg 4], helloImage⟩

/-- A launch input: `argv = ["a"]`, empty environment and file system, stdin at end of file. -/
def helloInp : ProcInput where
  argv := [[97]]
  envp := []
  imageFs := []
  stdin := InputStream.eof
  uid := 1000
  gid := 100
  groups := []
  net := netSilent
  nofile := 1024
  sigmask := 0
  hwcap := 0
  abortTerminal := false
  vaSize := .sv48
  urandom := InputStream.defaultUrandom
  tmp := []

/-- A launch entry: `sp = 0x7fffffffe000`, `brk = 0x403000`, `mmapBase = 0x40000000`. -/
def helloEn : ExecEntry := ⟨0x7fffffffe000, 0x403000, 0x40000000, ⟨0, fun _ => 0⟩⟩

end Silmaril.Wasi.Runtime.Launch
