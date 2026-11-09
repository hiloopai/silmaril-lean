# Pinned executable

The `-O2` executable built by `../build.sh` (GCC 13.3.0, GNU ld 2.42; flags in
`../../common/flags.sh`), committed so that the Lean transcriptions of its code
(`Silmaril.X86.Ladder.LibMini.Transcript`, `StrlenTranscript`) can be checked against the file.
A rebuild with that toolchain reproduces it byte for byte (`mem-loops.sha256`).

Licence: this repository's MIT licence.
