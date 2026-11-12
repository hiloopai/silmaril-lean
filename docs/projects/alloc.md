# C library contracts and allocators over ELF files

The `Libc` region states what it means for a C library, and in particular for the allocator a
shared object exports, to be correct. Everything here is definitions, statements and the
structural theorems about them (reducts, monotonicity, non-vacuity at the abstract level); no
allocator row is proved.

| Piece | Module | What it gives |
| --- | --- | --- |
| Contract institution | `Silmaril.Libc.Contract.{Sig,Spec,Inv,Inst,Libc,Alloc,Stdio,Diagram}` | Signatures of C library functions and their morphisms, contracts with reducts, invariants as a monoidal category (the tensor of two libraries), the institution on `Room`, the allocator chain `allocSig 1..4`, the stdio contracts, and the generated contract diagram |
| Abstract heap | `Silmaril.Libc.Alloc` | `Heap` (block start to requested size) and the loose and strict allocator relations |
| Signature hierarchy | `Silmaril.Libc.AllocSig` | `mf ⊂ mfc ⊂ mfcr ⊂ full`, valid POSIX use (`Valid`), the POSIX-safe relation `loose`, abstract models and `SafeOn.reduct`; `bottom_safe` (the always-failing allocator) shows non-vacuity |
| Abstract allocator institution | `Silmaril.Libc.AllocInst`, `Silmaril.Libc.X86Alloc.*` | Abstract allocators as models, the strengths safe/live/functional, the bump reference model |
| Contract over an ELF file | `Silmaril.Libc.AllocElf` | `Contract T LM s F S` and `PosixSafe`: the exports of `F` are bound by ld.so's lookup, and for some witness (ghost heap, owned regions, invariant) every valid call returns as `T` allows, within its frame, over a loading model `LM` |
| Concrete loading model | `Silmaril.Libc.AllocLoad` | `model E` and `Row s F S` (below) |
| Problem shapes | `Silmaril.Libc.Shapes` | `silmaril.shapes.alloc.elf.{contract,posix_safe,loaded}` and their four levels |

## The concrete loading model

`AllocLoad.Row s F S` says: **for every environment `E` whose bound imports satisfy their named
contracts (`E.Ok`), `F` is POSIX-safe at `s` in `AllocLoad.model E`**. In that model

* the library's `PT_LOAD` segments are mapped at a page-aligned base as the file says
  (`Dyn.ImageOk`), with eager binding: `RELATIVE` and `DT_RELR` positions relocated,
  `GLOB_DAT`/`JUMP_SLOT`/`R_X86_64_64` bound to the file's own definition when it has one and to
  the environment's address otherwise, `TPOFF64` to the environment's TLS offset; the TLS block
  and the TCB are in place and `errno` is a writable word;
* a step at an address of the environment is one atomic step of that function; every other step
  is the `Str9` x86-64 machine;
* the import contracts (`AllocLoad.contractList`) cover `mmap`, `munmap`, `mprotect`, `madvise`,
  `memset`, `memcpy`, `memmove`, `__errno_location`, the mutex and key functions of a
  single-threaded process, clocks, and pure functions; `getenv` and `secure_getenv` return
  `NULL`. An import without a named contract may do anything, including stop.

Not modelled: constructors (the started state is the loaded image), threads and signals, TLS
relocations other than `TPOFF64`, `COPY`, interposition of the names the file defines, which
implementation an IFUNC selects, and instructions `Str9` does not decode (they stop, so a row
over code that executes one is not provable at this model).

Build: `lake build Silmaril.Libc.Shapes.Defs Silmaril.Libc.AllocLoad.Thms Silmaril.Libc.Contract.Diagram.Thms`.
