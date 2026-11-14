module

public import Silmaril.Compiler.Native.Initialization.Defs
public import Silmaril.Compiler.Native.Types.Registered.Thms
public import Init.Data.ByteArray.Lemmas
public import Init.Data.Range.Lemmas

@[expose] public section
namespace Silmaril.Compiler.Native.Initialization
open Silmaril.Compile
open Silmaril.Cerberus
open Silmaril.Cerberus.Ail

private theorem writeLE_eq_foldl (image : ByteArray) (offset width value : Nat) :
    Mir.writeLE image offset width value = (List.range width).foldl
      (fun image index => image.set! (offset + index) (byte value index)) image := by
  simp [Mir.writeLE, byte, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range']

private theorem writeLE_succ (image : ByteArray) (offset width value : Nat) :
    Mir.writeLE image offset (width + 1) value =
      (Mir.writeLE image offset width value).set! (offset + width) (byte value width) := by
  simp [writeLE_eq_foldl, List.range_succ, List.foldl_append]

/-- The actual byte-array writer implements little-endian storage at every
address under an explicit image-fit premise. -/
theorem writeLE_encodes (image : ByteArray) (offset width value : Nat)
    (fits : offset + width ≤ image.size) :
    EncodesLE image (Mir.writeLE image offset width value) offset width value := by
  induction width with
  | zero => simp [EncodesLE, writeLE_eq_foldl]
  | succ width previous =>
    obtain ⟨size, bytes⟩ := previous (by omega)
    rw [writeLE_succ]
    refine ⟨by simp [size], ?_⟩
    intro address
    by_cases last : address = offset + width
    · subst address
      rw [ByteArray.getElem!_set!_self _ _ _ (by omega)]
      simp
    · rw [ByteArray.getElem!_set!_ne _ _ _ _ (Ne.symm last), bytes]
      have interval : (offset ≤ address ∧ address < offset + (width + 1)) ↔
          (offset ≤ address ∧ address < offset + width) := by omega
      simp only [interval]

/-- Reading a stored byte gives its specified little-endian digit. -/
theorem writeLE_byte (image : ByteArray) (offset width value index : Nat)
    (fits : offset + width ≤ image.size) (inside : index < width) :
    (Mir.writeLE image offset width value)[offset + index]! = byte value index := by
  have bytes := (writeLE_encodes image offset width value fits).2 (offset + index)
  simpa [show offset + index < offset + width by omega] using bytes

/-- Arbitrary bytes before and after the destination interval are preserved. -/
theorem writeLE_outside (image : ByteArray) (offset width value address : Nat)
    (fits : offset + width ≤ image.size)
    (outside : address < offset ∨ offset + width ≤ address) :
    (Mir.writeLE image offset width value)[address]! = image[address]! := by
  have bytes := (writeLE_encodes image offset width value fits).2 address
  simpa [show ¬ (offset ≤ address ∧ address < offset + width) by omega] using bytes

/-- Actual integer constant encoding, including the lowerer's explicit native
integer conversion before storage. This is byte adequacy given literal
resolution and destination layout, not an independent C evaluation theorem. -/
theorem gConst_integer (tags : Silmaril.Cerberus.Mem.Concrete.Tags)
    (image : ByteArray) (offset : Nat) (type : Ctype) (literal : IntegerConstant)
    (width : Nat) (signed : Bool) (value : Int)
    (destination : Types.ofCtype type = .int width signed)
    (resolved : Types.integerConstantValue literal = .ok value)
    (fits : offset + width ≤ image.size) :
    ∃ output, Lower.gConst tags image offset type (.integer literal) = .ok output ∧
      EncodesLE image output offset width ((value % 2 ^ 64).toNat) := by
  refine ⟨Mir.writeLE image offset width ((value % 2 ^ 64).toNat), ?_,
    writeLE_encodes image offset width ((value % 2 ^ 64).toNat) fits⟩
  have supported : ∀ why, Types.ofCtype type ≠ .unsupported why := by
    intro why rejected
    rw [destination] at rejected
    cases rejected
  have converted := (Types.Registered.ofCtype_of_supported tags type supported).trans destination
  have decoded := Types.Registered.integerConstantValue_of_resolved tags literal value resolved
  rw [Lower.gConst]
  simp [decoded, converted, Types.addressFormat, C.CType.intShape, Lower.integerInitBits]

/-- `_Bool` stores truth, including nonzero values whose low byte is zero. -/
theorem gConst_bool (tags : Silmaril.Cerberus.Mem.Concrete.Tags)
    (image : ByteArray) (offset : Nat) (type : Ctype) (literal : IntegerConstant) (value : Int)
    (destination : Types.ofCtype type = .bool)
    (resolved : Types.integerConstantValue literal = .ok value)
    (fits : offset + 1 ≤ image.size) :
    ∃ output, Lower.gConst tags image offset type (.integer literal) = .ok output ∧
      EncodesLE image output offset 1 (if value == 0 then 0 else 1) := by
  refine ⟨Mir.writeLE image offset 1 (if value == 0 then 0 else 1), ?_,
    writeLE_encodes image offset 1 (if value == 0 then 0 else 1) fits⟩
  have supported : ∀ why, Types.ofCtype type ≠ .unsupported why := by
    intro why rejected
    rw [destination] at rejected
    cases rejected
  have converted := (Types.Registered.ofCtype_of_supported tags type supported).trans destination
  have decoded := Types.Registered.integerConstantValue_of_resolved tags literal value resolved
  rw [Lower.gConst]
  simp [decoded, converted, Types.addressFormat, C.CType.intShape, Lower.integerInitBits]

end Silmaril.Compiler.Native.Initialization
