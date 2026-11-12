# glibc byte ranges

The modules `Silmaril.Elf.Link.Dyn.Glibc.Defs`, `Silmaril.Elf.Link.Dyn.Small.Libc`,
`Silmaril.Elf.Link.Dyn.Program.Glibc` and `Silmaril.Elf.Link.Dyn.Program.StdExe.Bins.Glibc`
contain short byte ranges (a few kilobytes in all: the ELF and program headers, the dynamic
section, and the parts of the symbol, string, version and GNU hash tables that symbol lookup reads)
of two files of the GNU C Library 2.39 as packaged by Ubuntu (`libc6` 2.39-0ubuntu8.9, amd64):

| file | size | sha256 |
|---|---|---|
| `libc.so.6` | 2129424 | `3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf` |
| `ld-linux-x86-64.so.2` | 236616 | `c20a2dc8917c755f02b94049356320fe1f62ac7d9f8994731f807d9df39302da` |

The GNU C Library is free software, licensed under the GNU Lesser General Public License,
version 2.1 or (at your option) any later version (https://www.gnu.org/licenses/lgpl-2.1.html).
Its complete corresponding source is the Ubuntu source package `glibc` 2.39-0ubuntu8.9
(https://launchpad.net/ubuntu/+source/glibc/2.39-0ubuntu8.9) and the upstream release
(https://ftp.gnu.org/gnu/glibc/glibc-2.39.tar.xz).

The executables in `examples/dyn/pinned/` contain glibc's crt start-up objects (LGPL-2.1-or-later
with the linking exception) and GCC's `crtbeginS.o`/`crtendS.o` (GPL-3.0-or-later with the GCC
Runtime Library Exception); see `examples/dyn/README.md`.
