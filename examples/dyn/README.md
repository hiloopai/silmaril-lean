# Dynamically linked executables of the process proofs

C sources (written for this repository) of the executables that `Silmaril.Elf.Link.Dyn` reasons
about: `hello` (gcc and clang), `ret0`, `ret42`, `adder` (gcc and clang), and the first rungs of
a ladder of small GNU-style tools, `cat-stdin` and `cat-file` (gcc). Each is compiled with
`-O2` (default PIE, dynamically linked against glibc 2.39). The executables are committed in
`pinned/` and read by `Silmaril.Elf.Link.Dyn.Pin.Bytes` with `include_bytes`; `pins.txt` names
their sha256 and the toolchain on which the build is byte-for-byte reproducible.

    examples/dyn/pin.sh --check          # the committed files have the pinned sha256
    examples/dyn/pin.sh --build [NAME]   # rebuild (needs the toolchain of pins.txt)

The proofs trust only that the bytes are these files; every fact about them (layout, the C
runtime's placement, relocations, block certificates) is generated outside Lean and re-checked
in Lean by `decide +kernel`.

## Licences of the executables

The executables contain, from the toolchain:

* glibc 2.39 crt start-up code (`Scrt1.o`, `crti.o`, `crtn.o`): LGPL-2.1-or-later, with the
  exception that permits linking into executables;
* GCC 13.3 `crtbeginS.o`/`crtendS.o`: GPL-3.0-or-later with the GCC Runtime Library Exception.

No glibc library code is linked into them. The proofs read `libc.so.6` and `ld.so` only through
small byte ranges (the dynamic tables symbol lookup reads) transcribed in
`Silmaril.Elf.Link.Dyn.Glibc`, `Silmaril.Elf.Link.Dyn.Small.Libc`,
`Silmaril.Elf.Link.Dyn.Program.Glibc` and `Silmaril.Elf.Link.Dyn.Program.StdExe.Bins.Glibc`;
see [`NOTICES/glibc`](../../NOTICES/glibc/README.md).
