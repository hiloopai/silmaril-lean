module

public import Silmaril.Wasm.SpecTec.GrammarInst.Thms
public import Silmaril.Wasm.SpecTec.BinaryAgree.Thms

/-!
# Lime1 instruction bytes in the corrected wasm-3.0 `Binstr`

Lime1 has no SpecTec script. Its binary grammar (`Lime1.Binary.Instr ov`) is related to the
corrected wasm-3.0 script's `Binstr` by composing two copied results: the Lime1 → Core agreement
(`Silmaril.Wasm.Binary.lime1_instr_core`, `BinaryAgree`) and the Core → SpecTec rows of
`Equiv/BinaryInstr` (`binstr_plain`, `binstr_call`, …), which are equalities of relations.

* `plain_core`: a Lime1 opcode with no immediates is a Core one, at the Core image
  (`Lime1.Binary.PlainOp c i → Core.PlainOp c i.toCore`, one constructor per case);
* **`plain_binstr`**: so the corrected wasm-3.0 `Binstr` derives `[c]` with value
  `instrV i.toCore`, for every Lime1 plain opcode, Lime1-only ones (sign extension) included;
* **`row_binstr`**: for an opcode with an index row (`Binstr` at `c :: r` is exactly
  `Core.Instr Forms.all` at `c :: r`), Lime1 bytes `c :: r` of an instruction `i` are derived
  with value `instrV i.toCore` (under `alignsBelow64`, which holds for every instruction without a
  memory argument);
* `call_binstr`, `localGet_binstr`, …: the rows instantiated;
* `v1_row_binstr`: 1.0 instruction bytes, through `v1_instr_lime1`.

New proofs over the copied agreements.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.Lime1Gram

open Silmaril.SpecTec Silmaril.SpecTec.Sem Silmaril.SpecTec.Equiv
open Silmaril.Wasm Silmaril.Wasm.Binary

/-- **Lime1 opcodes with no immediates are Core ones**, at the Core image. -/
theorem plain_core {c : UInt8} {i : Lime1.Instr} (h : Lime1.Binary.PlainOp c i) :
    Core.PlainOp c i.toCore := by
  cases h <;> constructor

/-- **The corrected wasm-3.0 `Binstr` derives every Lime1 plain opcode**, with the value of the
Core image. -/
theorem plain_binstr {c : UInt8} {i : Lime1.Instr} (h : Lime1.Binary.PlainOp c i) (ρ : VarEnv) :
    gramRelSup envC ρ (.varG "Binstr" []) [c] (instrV i.toCore) :=
  (binstr_plain (plain_core h) ρ [] _).mpr ⟨rfl, rfl⟩

/-- An index row of `Binstr`: at `c :: r` it is exactly the hand-written Core grammar. -/
def Row (c : UInt8) : Prop :=
  ∀ (ρ : VarEnv) (r : Grammar.Bytes) (v : Value),
    gramRelSup envC ρ (.varG "Binstr" []) (c :: r) v ↔
      ∃ i, Core.Instr Core.Forms.all (c :: r) i ∧ v = instrV i

/-- **Lime1 bytes at an index row are `Binstr` derivations of the Core image.** -/
theorem row_binstr {c : UInt8} (hc : Row c) {ov : Bool} {r : Bytes} {i : Lime1.Instr}
    (h : Lime1.Binary.Instr ov (c :: r) i) (ha : i.alignsBelow64 = true) (ρ : VarEnv) :
    gramRelSup envC ρ (.varG "Binstr" []) (c :: r) (instrV i.toCore) :=
  (hc ρ r _).mpr ⟨_, Core.Instr.mono (Core.Forms.le_all _) (lime1_instr_core h ha), rfl⟩

/-- **1.0 bytes at an index row are `Binstr` derivations of the Core image of the Lime1 image.** -/
theorem v1_row_binstr {c : UInt8} (hc : Row c) {r : Bytes} {i : V1.Instr}
    (h : V1.Binary.Instr (c :: r) i) (ha : i.toLime.alignsBelow64 = true) (ρ : VarEnv) :
    gramRelSup envC ρ (.varG "Binstr" []) (c :: r) (instrV i.toLime.toCore) :=
  row_binstr hc (v1_instr_lime1 h) ha ρ

theorem row_call : Row 0x10 := binstr_call
theorem row_br : Row 0x0C := binstr_br
theorem row_brIf : Row 0x0D := binstr_brIf
theorem row_localGet : Row 0x20 := binstr_localGet
theorem row_localSet : Row 0x21 := binstr_localSet
theorem row_localTee : Row 0x22 := binstr_localTee
theorem row_globalGet : Row 0x23 := binstr_globalGet
theorem row_globalSet : Row 0x24 := binstr_globalSet
theorem row_memorySize : Row 0x3F := binstr_memorySize
theorem row_memoryGrow : Row 0x40 := binstr_memoryGrow

/-- `call`: Lime1 bytes `10 x` are `Binstr` derivations. -/
theorem call_binstr {ov : Bool} {r : Bytes} {i : Lime1.Instr}
    (h : Lime1.Binary.Instr ov (0x10 :: r) i) (ha : i.alignsBelow64 = true) (ρ : VarEnv) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x10 :: r) (instrV i.toCore) :=
  row_binstr row_call h ha ρ

/-- `local.get`: Lime1 bytes `20 x` are `Binstr` derivations. -/
theorem localGet_binstr {ov : Bool} {r : Bytes} {i : Lime1.Instr}
    (h : Lime1.Binary.Instr ov (0x20 :: r) i) (ha : i.alignsBelow64 = true) (ρ : VarEnv) :
    gramRelSup envC ρ (.varG "Binstr" []) (0x20 :: r) (instrV i.toCore) :=
  row_binstr row_localGet h ha ρ

/-- A Lime1-only instruction: `i32.extend8_s` (`C0`, not in 1.0) is in the wasm-3.0 `Binstr`. -/
theorem extend8_binstr (ρ : VarEnv) :
    gramRelSup envC ρ (.varG "Binstr" []) [0xC0]
      (instrV (Lime1.Instr.intUnOp .i32 (.extend .i8)).toCore) :=
  plain_binstr .rxC0 ρ

end Silmaril.Proofs.Wasm.SpecTec.Lime1Gram
