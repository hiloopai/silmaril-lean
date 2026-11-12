module

public import Silmaril.Wasm.SpecTec.Sim10.Encode.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.EncodeCheck

/-!
# The 1.0 encoding, checked against the wasm-1.0 IL types

`Silmaril.Proofs.Wasm.SpecTec.Sim10.EncodeCheck` runs the IL type checker on the images of a corpus
covering every V1 instruction, administrative instruction and runtime structure, at build time,
and records which encodings the checker rejects and why (`knownRejectedInstrs`: every `STORE`,
for the same reason in the checker as in 2.0).
-/
