# GNU sha256sum-min

`sha256sum-min` is a libc-free reimplementation of GNU coreutils 9.4
`sha256sum` (x86-64 Linux, stdin tier). Its source, its generated
help/version/strerror tables and the Lean development built on them follow
coreutils, gnulib and glibc structure and texts. These files are distributed
under the GNU General Public License, version 3 or later; the licence text is
in [`COPYING`](COPYING).

Covered paths:

- `apps/sha256sum-min/**` (C and assembly source, generated tables, build
  recipe, build receipt);
- `Silmaril/Apps/Sha256sum/**` (executable specification, transcribed image
  and proofs about it);
- `Silmaril/Process/LPS/Problems/GnuSha256sum/**`, including `Elf.lean`, the
  35,512-byte executable (SHA-256
  `22fa6345cc5bed08f07d4d5a0836885118259a73402470e4d7f7a7a81ad42817`);
- `problems/sha256/gnu-sha256sum-x86-64/**` (problem records and checks);
- `scripts/sha256sum/recovered-provenance.json` (build provenance record).

`apps/sha256sum-min/`, `Silmaril/Apps/Sha256sum/` and
`Silmaril/Process/LPS/Problems/GnuSha256sum/` each carry a `README.md` pointing here.

The freestanding `apps/sha256-cli` filter, its image
`Silmaril/Process/CLI/Sha256Cli/Binary.lean` and the rest of the repository
are separate works under the repository's own licence and are not covered by
this notice.
