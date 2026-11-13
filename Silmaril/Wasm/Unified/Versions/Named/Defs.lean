module

public import Silmaril.Wasm.Unified.Core30.Defs
public import Silmaril.Wasm.Models.Syntax.Defs

/-!
# Version signatures inside the 3.0 signature

The feature signatures of the Wasm versions as sub-signatures of the unified core's 3.0
signature (`Silmaril.Wasm.Unified.Core30.sig30`, opcodes named after silmaril's instruction
constructors with their operator parameters). An opcode is in the signature of a feature set
`S` when some Core 3.0 instruction with that opcode needs only capabilities of `S` at its head
(`Silmaril.Wasm.Models.Instr.headB`, the capability table of `Silmaril.Wasm.Models.Syntax`).

* `nsig S`: **the named signature of `S`**, with the typing of `sig30`;
* `n10`, `n20`, `nLime1`, `nWasmi`, and `sig30` itself for 3.0 (`nsig v30 = sig30` up to
  opcodes no instruction of 3.0 lacks, `Thms`);
* the binary presentation of the same feature signatures is `Silmaril.Wasm.Unified.Versions.vsig`
  (`Versions.Sig`); relating the two is a renaming morphism of the unified core (in progress).

Choices worth recording: an opcode is in `nsig S` when *some* instruction with it is in `S`.
Opcodes whose immediates decide the capability (`select` with or without a type, a memory index
other than 0) are therefore in the signature, and the immediates are checked by validation (a
model's `ok`), as in the binary presentation.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm.Models Silmaril.Wasm.Unified.Core30

/-- **The named signature of a feature set**: the 3.0 opcodes some instruction of `S` has. -/
def nsig (S : FeatureSet) : FSig :=
  ⟨{o | ∃ i : Silmaril.Wasm.Instr, head i = o ∧ Instr.headB S i = true}, arity30⟩

/-- Wasm 1.0, as a sub-signature of 3.0. -/
abbrev n10 : FSig := nsig v10
/-- Wasm 2.0, as a sub-signature of 3.0. -/
abbrev n20 : FSig := nsig v20
/-- Lime1, as a sub-signature of 3.0. -/
abbrev nLime1 : FSig := nsig lime1
/-- wasmi 2.0.0 restricted to Core 3.0 syntax. -/
abbrev nWasmi : FSig := nsig wasmi200

end Silmaril.Wasm.Unified.Versions
