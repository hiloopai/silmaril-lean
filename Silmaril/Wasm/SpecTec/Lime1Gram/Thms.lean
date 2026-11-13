module

public import Silmaril.Proofs.Wasm.SpecTec.Lime1Gram.Instr
public import Silmaril.Wasm.Models.BinWitV1.Thms

/-!
# Lime1 against the SpecTec binary grammars

Lime1 has no SpecTec script, and its binary grammar is a relational Lean grammar
(`Lime1.Binary.Encodes`), not a `GramD` of a script. So there is no grammar-institution
comorphism from a "Lime1 script" to state. What can be stated is a relation between Lime1 bytes
and the SpecTec scripts' grammars, through the copied agreements.

**Instructions: a positive relation** (`Silmaril.Proofs.Wasm.SpecTec.Lime1Gram`).

* `plain_binstr`: every Lime1 opcode without immediates (Lime1-only ones such as
  `i32.extend8_s`, `extend8_binstr`, included) is derived by the corrected wasm-3.0 `Binstr`,
  with the SpecTec value `instrV` of its Core image;
* `row_binstr`: the same for the bytes of a Lime1 instruction at an index row (`call`, `br`,
  `br_if`, `local.*`, `global.*`, `memory.size`, `memory.grow`); `v1_row_binstr` for 1.0 bytes.

**Modules: a refutation.** The wasm-1.0 and wasm-2.0 `Bmodule` derives nothing, pinned or
corrected (`GrammarInst.bmodule_not_entailed`: `func*` is left unbound). So the module-level
relation "valid 1.0 bytes are `Bmodule` sentences of the wasm-1.0 grammar theory" fails, and not
vacuously: the 22 bytes `witBytes` are valid 1.0 bytes (`BinWitV1.wit1_profile`) and valid
Lime1 bytes.

* **`v10_bmodule_false`**, **`lime1_bmodule20_false`**: the refutations, at the corrected
  wasm-1.0 and wasm-2.0 theories (the pinned theories alike, `wit_bmodule_none`).
* Restatement: the module-level relation goes through Core's hand-written grammar
  (`Lime1Bin.lime1BinCore`, `BinProfile.coreBinR`), and the SpecTec grammar is reached at the
  instruction level above. The wasm-3.0 `Bmodule` has a different shape (its premises are not
  `BmoduleShape`), and whether it derives anything is not decided here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Lime1Gram

open Silmaril.SpecTec Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts Silmaril.Wasm.SpecTec.GrammarInst
open Silmaril.Wasm.Models.Lime1Bin
open Silmaril.Proofs.Wasm.Models.Lime1Bin (witBytes)

/-- **No wasm-1.0 or wasm-2.0 grammar theory entails a `Bmodule` sentence about the witness.** -/
theorem wit_bmodule_none (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Bmodule" [] ρ witBytes v) ∧
      ¬ Entails (scriptAxioms Wasm10.envFixed) (derivesNT "Bmodule" [] ρ witBytes v) ∧
      ¬ Entails (scriptAxioms Wasm20.envOriginal) (derivesNT "Bmodule" [] ρ witBytes v) ∧
      ¬ Entails (scriptAxioms Wasm20.envFixed) (derivesNT "Bmodule" [] ρ witBytes v) :=
  bmodule_not_entailed ρ witBytes v

/-- **Refutation**: valid 1.0 bytes are not, in general, `Bmodule` sentences of the corrected
wasm-1.0 grammar theory. -/
theorem v10_bmodule_false :
    ¬ ∀ b, ValidV1 b → ∃ ρ v, Entails (scriptAxioms Wasm10.envFixed) (derivesNT "Bmodule" [] ρ b v) :=
  fun h => by
    obtain ⟨ρ, v, he⟩ := h witBytes Silmaril.Wasm.Models.BinWitV1.wit1_profile.2.2.2.1
    exact (wit_bmodule_none ρ v).2.1 he

/-- **Refutation**: valid Lime1 bytes are not, in general, `Bmodule` sentences of the corrected
wasm-2.0 grammar theory. -/
theorem lime1_bmodule20_false :
    ¬ ∀ b, ValidL b → ∃ ρ v, Entails (scriptAxioms Wasm20.envFixed) (derivesNT "Bmodule" [] ρ b v) :=
  fun h => by
    obtain ⟨ρ, v, he⟩ := h witBytes (Silmaril.Proofs.Wasm.Models.BinProfile.wit_profile).1
    exact (wit_bmodule_none ρ v).2.2.2 he

end Silmaril.Wasm.SpecTec.Lime1Gram

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.Lime1Gram.plain_binstr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.Lime1Gram.plain_binstr

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.Lime1Gram.row_binstr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.Lime1Gram.row_binstr

/-- info: 'Silmaril.Wasm.SpecTec.Lime1Gram.v10_bmodule_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Lime1Gram.v10_bmodule_false
