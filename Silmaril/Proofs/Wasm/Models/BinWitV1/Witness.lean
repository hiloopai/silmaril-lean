module

public import Silmaril.Proofs.Wasm.Models.BinWitV1.Encoder

/-!
# A 1.0-bytes witness for `BinProfile.not_validC_v1`

`witMod1`: the Wasm 1.0 module with one table (`min 0`) and one element segment
`(elem (i32.const 0))` with no functions, the 1.0 preimage of `Lime1Bin`'s `witMod`
(`witMod1_toLime`). Its bytes are `Lime1Bin`'s 22-byte `witBytes`:

* `wit1_encodesWith`: the copied encoder's output is a strict (`overlong = false`) Lime1 encoding
  (`encModule_soundW`);
* **`wit1_encodes`**: so it is a **1.0** encoding of `witMod1` (`v1_iff_lime1`);
* `wit1_valid`: `witMod1` is a valid 1.0 module, and its segment offset reads no global
  (`wit1_offsets`), so `witBytes` are valid 1.0 bytes (`wit1_validV1`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.BinWitV1

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models.Lime1Bin
open Silmaril.Proofs.Wasm.Models.Lime1Bin (witMod witBytes wit_enc)

/-- One table and one element segment at offset `0`, with no functions, in Wasm 1.0. -/
def witMod1 : V1.Module :=
  { tables := [⟨⟨0, none⟩⟩], elems := [{ table := ⟨0⟩, offset := [.intConst .i32 0], init := [] }] }

/-- Its Lime1 image is `Lime1Bin`'s witness. -/
theorem witMod1_toLime : witMod1.toLime = witMod := rfl

/-- The witness bytes are a strict Lime1 encoding. -/
theorem wit1_encodesWith : Lime1.Binary.EncodesWith false witBytes witMod :=
  encModule_soundW false witMod witBytes wit_enc

/-- **The witness bytes are a Wasm 1.0 encoding of `witMod1`.** -/
theorem wit1_encodes : V1.Binary.Encodes witBytes witMod1 :=
  v1_iff_lime1.mpr wit1_encodesWith

/-- The offset `i32.const 0` is a 1.0 constant expression of type `i32`. -/
theorem wit1_offset (C : V1.Validation.Context) :
    V1.Validation.ConstExprType C [.intConst .i32 0] .i32 :=
  ⟨.cons (.intConst .i32 0) (.nil _), fun i hi => by
    rw [List.mem_singleton.mp hi]; exact .intConst .i32 0⟩

/-- The table of `witMod1` is valid. -/
theorem wit1_tables : ∀ tt ∈ witMod1.tables, V1.Validation.TableTypeValid tt := by
  intro tt htt
  have h : tt = ⟨⟨0, none⟩⟩ := by simpa [witMod1] using htt
  rw [h]
  exact ⟨by decide, by simp⟩

/-- The element segment of `witMod1` is valid. -/
theorem wit1_elems :
    ∀ e ∈ witMod1.elems, V1.Validation.ElemValid (V1.Validation.moduleContext witMod1) e := by
  intro e he
  have h : e = { table := ⟨0⟩, offset := [.intConst .i32 0], init := [] } := by
    simpa [witMod1] using he
  rw [h]
  exact ⟨⟨⟨⟨0, none⟩⟩, rfl⟩, wit1_offset _, by simp⟩

/-- **`witMod1` is a valid Wasm 1.0 module.** -/
theorem wit1_valid : V1.Validation.ModuleValid witMod1 where
  types := by simp [witMod1]
  imports := by simp [witMod1]
  functions := by simp [witMod1]
  tables := wit1_tables
  memories := by simp [witMod1]
  globals := by simp [witMod1]
  elements := wit1_elems
  data := by simp [witMod1]
  start := by simp [witMod1, V1.Validation.StartValid]
  exports := by simp [witMod1]
  uniqueExports := by simp [witMod1]
  singleTable := by decide
  singleMemory := by decide

/-- Its segment offset reads no global. -/
theorem wit1_offsets : Lime1.Validation.Module.SegmentOffsetsImported witMod1.toLime := by
  refine ⟨fun e he x hx => ?_, fun d hd => by simp [witMod1_toLime, witMod] at hd⟩
  have h : e = { table := ⟨0⟩, offset := [.intConst .i32 0], init := [] } := by
    simpa [witMod1_toLime, witMod] using he
  subst h
  simp at hx

/-- **The witness bytes are valid 1.0 bytes.** -/
theorem wit1_validV1 : ValidV1 witBytes :=
  ⟨witMod1, wit1_encodes, wit1_valid, wit1_offsets⟩

end Silmaril.Proofs.Wasm.Models.BinWitV1
