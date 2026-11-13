# Machine code in the effects examples

The generated modules `Silmaril.Elf.Effects.Example.{Strlen,CoreutilsTrue,Sha256sum}.Defs`
(written by `tools/cfg-cert`, regenerated and checked by `scripts/cfg-cert/gen.sh`) contain the
bytes of the basic blocks of the certified functions:

| module | file | package | sha256 | bytes |
|---|---|---|---|---|
| `Strlen` | `libc.so.6` | Ubuntu `libc6` 2.39-0ubuntu8.9 (amd64) | `3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf` | 1497 |
| `CoreutilsTrue` | `/usr/bin/true` | Ubuntu `coreutils` 9.4-3ubuntu6.3 (amd64) | `8a63c98320173f79e263115e10cefc170155e47d1fd4b5a70e4429d2699cae28` | 3202 |
| `Sha256sum` | `/usr/bin/sha256sum` | Ubuntu `coreutils` 9.4-3ubuntu6.3 (amd64) | `4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60` | 17524 |

The GNU C Library is licensed under the GNU Lesser General Public License, version 2.1 or (at
your option) any later version (https://www.gnu.org/licenses/lgpl-2.1.html); its corresponding
source is https://launchpad.net/ubuntu/+source/glibc/2.39-0ubuntu8.9.

GNU coreutils is licensed under the GNU General Public License, version 3 or (at your option) any
later version (see `NOTICES/GPLv3`); its corresponding source is
https://launchpad.net/ubuntu/+source/coreutils/9.4-3ubuntu6.3 and https://ftp.gnu.org/gnu/coreutils/.
