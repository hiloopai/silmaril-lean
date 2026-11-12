# glibc allocator code bytes

The modules `Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.Code`,
`Silmaril.Proofs.Libc.Ptmalloc.Versions.V240.Code` and
`Silmaril.Proofs.Libc.Ptmalloc.Versions.V236.Code` contain short byte ranges (4866 bytes in all)
of the machine code of `__libc_malloc`, `__libc_free` and `_int_free` from three builds of the
GNU C Library's `libc.so.6`:

| package | size | sha256 |
|---|---|---|
| Ubuntu `libc6` 2.39-0ubuntu8.9 (amd64) | 2129424 | `3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf` |
| Ubuntu `libc6` 2.40-1ubuntu3.1 (amd64) | 2182752 | `132ba50d4abaeff314e64f5d84daa4e4e6d9b227135bc035fde1b69a81aab204` |
| Debian `libc6` 2.36-9+deb12u14 (amd64) | 1926232 | `6b4a45352fd0c540a9c7c718f35ce8c8e46a4e482f9d3885a910c32d1a0e1421` |

`scripts/ptmalloc/check-code.py` checks the ranges against the files.

The GNU C Library is free software, licensed under the GNU Lesser General Public License,
version 2.1 or (at your option) any later version (https://www.gnu.org/licenses/lgpl-2.1.html).
Its complete corresponding source is the distribution source package `glibc` of the same version
(https://launchpad.net/ubuntu/+source/glibc/2.39-0ubuntu8.9,
https://launchpad.net/ubuntu/+source/glibc/2.40-1ubuntu3.1,
https://snapshot.debian.org/package/glibc/2.36-9%2Bdeb12u14/) and the upstream releases
(https://ftp.gnu.org/gnu/glibc/).
