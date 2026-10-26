# ELF process support

ELF syntax and loaded-image facts are exposed through
`Silmaril.Formats.ELF.Cst.Defs` and `Silmaril.Formats.ELF.Cst.Thms`. The CST
layer validates the header and program-header shape used by the x86-64 and
RV64 launch models, while the process headers connect those facts to startup
and syscall proofs.

The process release checks ELF bytes in three places:

1. the freestanding `sha256-cli` image;
2. the static-musl checksum image and its launch facts;
3. the 49 small x86-64 probe images, each rebuilt from assembly and compared
   with `SHA256SUMS` before its generated Lean module is accepted.

The build recipes and hashes are kept beside the verification projects so a
fresh clone can replay the byte-level checks without relying on an untracked
binary.
