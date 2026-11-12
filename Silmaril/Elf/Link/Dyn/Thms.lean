module

public import Silmaril.Elf.Link.Dyn.Pin.Defs
public import Silmaril.Elf.Link.Dyn.Loader.Thms
public import Silmaril.Elf.Link.Dyn.Image.Thms
public import Silmaril.Elf.Link.Dyn.Glibc.Thms
public import Silmaril.Elf.Link.Dyn.Imports.Defs
public import Silmaril.Elf.Link.Dyn.Proc.Thms
public import Silmaril.Elf.Link.Dyn.ProcG.Thms
public import Silmaril.Elf.Link.Dyn.ProcX.Thms
public import Silmaril.Raw.Elf.Link.Dyn.ProcX.Inst
public import Silmaril.Elf.Link.Dyn.Cert.Thms
public import Silmaril.Elf.Link.Dyn.Stdio.Thms
public import Silmaril.Elf.Link.Dyn.Stdio.Contracts
public import Silmaril.Elf.Link.Dyn.Streams.Thms
public import Silmaril.Elf.Link.Dyn.Crt.Thms
public import Silmaril.Elf.Link.Dyn.Hello.Thms
public import Silmaril.Elf.Link.Dyn.Small.Thms
public import Silmaril.Elf.Link.Dyn.Program.Thms
public import Silmaril.Elf.Link.Dyn.Program.Glibc
public import Silmaril.Elf.Link.Dyn.Program.Examples.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Witness
public import Silmaril.Raw.Elf.Link.Dyn.Proc.RunInv
public import Silmaril.Raw.Elf.Link.Dyn.Proc.StepFrame
public import Silmaril.Raw.Elf.Link.Dyn.Cert.CodeRO
public import Silmaril.Raw.Elf.Link.Dyn.Cert.Frame

/-!
# Dynamic linking against glibc: x86-64 executables, end to end

A model of a dynamically linked x86-64 Linux process and proofs about real executables in it.
The guide is `docs/projects/dyn.md`.

* **Loader** (`Loader`, `Image`, `Glibc`, `Elf` in `Silmaril.Elf.Link.DynElf`): `ExeLoaded`,
  a relation between the files (executable, `libc.so.6`, `ld.so`, …) and a post-load memory,
  transcribing glibc 2.39's `ld.so` (search scope, GNU-hash lookup with symbol versions,
  `RELATIVE`/`GLOB_DAT`/`JUMP_SLOT`/`IRELATIVE` relocations, eager and lazy binding, RELRO).
  The shared objects enter only through sparse chunks (`Glibc.libcChunks`, `ldChunks`): every
  theorem holds for every file agreeing with them.
* **Process** (`Proc`, `ProcG`, `ProcX`): `Proc.proc W`, silmaril's `Open9` inside the
  executable's image and, outside it, glibc's functions as one atomic step each, by contract
  (`World`: start-up, `exit`, the callback gate, `puts`/`printf`/`scanf`/stdio streams).
  `ProcG` lifts it to any image ISA extending `Open9` (SSE, `Str9G`).
* **Block certificates** (`Cert`, with `Silmaril.X86.Bir9X`): straight-line blocks of the
  executable checked once by `decide +kernel` and replayed as single steps.
* **C runtime** (`Crt`): `_start`, `_init`, `frame_dummy`, `__do_global_dtors_aux`, `_fini` of a
  gcc or clang PIE over any layout, composed around a contract for `main`.
* **Examples** (`Hello`, `Small`): hello world, `return 0`, `return 42` and a `scanf`/`printf`
  adder, for gcc and clang (eager and lazy binding), with non-vacuity witnesses.
* **Program API** (`Program`): `Program.Verified exe libc ld spec tier`, the end-to-end
  statement for a GNU-style tool (spec over argv, files, stdin; stdout, stderr, status), proved
  from a contract for `main`; hello and `cat` (stdin) through it.

The executables are committed in `examples/dyn/pinned/`, pinned by sha256 in
`examples/dyn/pins.txt`, and read with `include_bytes` (`Pin.Bytes`, `Pin`).

**Trusted**: silmaril's `Open9` semantics, the loader relation (`ExeLoaded`, a transcription of `ld.so`), the glibc contracts of
`Proc.World` (and the per-program `World.atMain`), the `include_bytes` elaborator and the sha256
check of the pinned files.
-/
