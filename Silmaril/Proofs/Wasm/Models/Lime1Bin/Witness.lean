module

public import Silmaril.Proofs.Wasm.Models.Lime1Bin.Decode

/-!
# A concrete witness for the decoding square and its refutation

`witMod`: one table (`min 0`) and one legacy element segment `(elem (i32.const 0))` with no
functions. `witBytes` is its encoding by the copied Lime1 encoder, 22 bytes:
`00 61 73 6d 01 00 00 00` (header), `04 04 01 70 00 00` (table section),
`09 06 01 00 41 00 0b 00` (element section: segment kind `0`, offset `i32.const 0`, no
functions). Kernel evaluation (`decide +kernel`) checks the encoder's output.

* `wit_valid`: `witMod` is a valid Lime1 module;
* `wit_square`: Lime1 decodes `witBytes` to `witMod`, Core 3.0 to `witMod.toCoreBinary`, and
  **not** to `witMod.toCore`. So `decodeC_ne_toCore` is not vacuous.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Bin

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models.Lime1Bin

/-- One table and one legacy element segment at offset `0`, with no functions. -/
def witMod : Lime1.Module :=
  { tables := [⟨⟨0, none⟩⟩], elems := [{ table := ⟨0⟩, offset := [.intConst .i32 0], init := [] }] }

/-- Its encoding. -/
def witBytes : Bytes :=
  [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x04, 0x04, 0x01, 0x70, 0x00, 0x00,
    0x09, 0x06, 0x01, 0x00, 0x41, 0x00, 0x0b, 0x00]

/-- The bytes of a successful encoding. -/
def okBytes : Except String Bytes → Option Bytes
  | .ok b => some b
  | .error _ => none

/-- The encoder's output, read as an option (kernel evaluation). -/
theorem wit_okBytes : okBytes (Lime1.Binary.Encoder.encModule witMod) = some witBytes := by
  decide +kernel

/-- The encoder produces `witBytes`. -/
theorem wit_enc : Lime1.Binary.Encoder.encModule witMod = .ok witBytes := by
  have h := wit_okBytes
  revert h
  cases Lime1.Binary.Encoder.encModule witMod with
  | ok b => intro h; exact congrArg Except.ok (Option.some.inj h)
  | error e => intro h; exact absurd h (by simp [okBytes])

theorem wit_encodes : Lime1.Binary.Encodes witBytes witMod :=
  Lime1.Binary.Encoder.encModule_sound _ _ wit_enc

/-- The offset `i32.const 0` is a constant expression of type `i32`. -/
theorem wit_offset (C : Lime1.Validation.Context) :
    Lime1.Validation.ConstExprType C [.intConst .i32 0] .i32 :=
  ⟨.cons (.intConst .i32 0) (.nil _), fun i hi => by
    rw [List.mem_singleton.mp hi]; exact .intConst .i32 0⟩

/-- The table of `witMod` is valid. -/
theorem wit_tables : ∀ tt ∈ witMod.tables, Lime1.Validation.TableTypeValid tt := by
  intro tt htt
  have h : tt = ⟨⟨0, none⟩⟩ := by simpa [witMod] using htt
  rw [h]
  exact ⟨by decide, by simp⟩

/-- The element segment of `witMod` is valid. -/
theorem wit_elems :
    ∀ e ∈ witMod.elems, Lime1.Validation.ElemValid (Lime1.Validation.moduleContext witMod) e := by
  intro e he
  have h : e = { table := ⟨0⟩, offset := [.intConst .i32 0], init := [] } := by
    simpa [witMod] using he
  rw [h]
  exact ⟨⟨⟨⟨0, none⟩⟩, rfl⟩, wit_offset _, by simp⟩

/-- **`witMod` is a valid Lime1 module.** -/
theorem wit_valid : Lime1.Validation.ModuleValid witMod where
  types := by simp [witMod]
  imports := by simp [witMod]
  functions := by simp [witMod]
  tables := wit_tables
  memories := by simp [witMod]
  globals := by simp [witMod]
  elements := wit_elems
  data := by simp [witMod]
  start := by simp [witMod, Lime1.Validation.StartValid]
  exports := by simp [witMod]
  uniqueExports := by simp [witMod]
  singleTable := by decide
  singleMemory := by decide

/-- **The square at the witness**: Lime1 decodes the bytes to `witMod`, Core 3.0 to its
binary-faithful image, and not to `toCore`. -/
theorem wit_square :
    decodeL witBytes = some witMod ∧ decodeC witBytes = some witMod.toCoreBinary ∧
      decodeC witBytes ≠ some witMod.toCore :=
  ⟨(square wit_encodes wit_valid).1, (square wit_encodes wit_valid).2,
    decodeC_ne_toCore wit_encodes wit_valid (by simp [witMod])⟩

end Silmaril.Proofs.Wasm.Models.Lime1Bin
