module

public import Silmaril.Wasm.SpecTec.Sim20.Encode.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.EncodeCheck

/-!
# The 2.0 encoding, checked against the wasm-2.0 IL types

`Silmaril.Proofs.Wasm.SpecTec.Sim20.EncodeCheck` runs the IL type checker on the images of a corpus
covering every V2 instruction, administrative instruction and runtime structure, at build time,
and records which encodings the checker rejects and why (`knownRejectedInstrs`).
-/
