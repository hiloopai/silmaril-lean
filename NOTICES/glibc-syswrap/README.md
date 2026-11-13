# glibc system call wrapper code bytes

The generated modules `Silmaril.Libc.SysWrap.Glibc.V236.Defs`, `Silmaril.Libc.SysWrap.Glibc.V239.Defs`
and `Silmaril.Libc.SysWrap.Glibc.V240.Defs` contain short byte ranges (35714 bytes in all: 11418,
12128 and 12168) of the machine code of the system call wrappers (`close`, `read`, `dup`,
`getpid`, ...) of three builds of the GNU C Library's `libc.so.6`, one range per wrapper address,
from the address to the end of the wrapper's last checked instruction:

| package | size | sha256 |
|---|---|---|
| Debian `libc6` 2.36-9+deb12u14 (amd64) | 1926232 | `6b4a45352fd0c540a9c7c718f35ce8c8e46a4e482f9d3885a910c32d1a0e1421` |
| Ubuntu `libc6` 2.39-0ubuntu8.9 (amd64) | 2129424 | `3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf` |
| Ubuntu `libc6` 2.40-1ubuntu3.1 (amd64) | 2182752 | `132ba50d4abaeff314e64f5d84daa4e4e6d9b227135bc035fde1b69a81aab204` |

`scripts/syswrap/gen.sh DIR --check` regenerates the modules from the files (checking their
sha256) and fails if they differ.

The GNU C Library is free software, licensed under the GNU Lesser General Public License,
version 2.1 or (at your option) any later version (https://www.gnu.org/licenses/lgpl-2.1.html).
Its complete corresponding source is the distribution source package `glibc` of the same version
(https://snapshot.debian.org/package/glibc/2.36-9%2Bdeb12u14/,
https://launchpad.net/ubuntu/+source/glibc/2.39-0ubuntu8.9,
https://launchpad.net/ubuntu/+source/glibc/2.40-1ubuntu3.1) and the upstream releases
(https://ftp.gnu.org/gnu/glibc/).

`tools/syswrap-gen/data/x86_64-syscalls.tsv` lists the number, name and argument count of each
x86-64 Linux system call, taken from strace v6.11 (`src/linux/x86_64/syscallent.h`,
`src/linux/generic/syscallent-common.h`; strace is LGPL-2.1-or-later, https://strace.io); the
numbers agree with Linux's `asm/unistd_64.h`.
