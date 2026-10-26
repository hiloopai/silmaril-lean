module

public import Silmaril.Formats.ELF.Ast.Types
public import Silmaril.Formats.ELF.Object

/-! Proof and bounded-reader correspondence layer. Data-only clients import `Ast.Types`. -/
@[expose] public section
namespace Silmaril.Formats.ELF.Ast

@[simp] theorem encodeLE_length (width value : Nat) :
    (encodeLE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeLE, ih]

/-- The scalar serializer recovers every value that fits its declared width. -/
theorem decodeLE_encodeLE (width value : Nat) (fits : value < 256 ^ width) :
    decodeLE (encodeLE width value) = value := by
  induction width generalizing value with
  | zero =>
    have : value = 0 := by simpa using fits
    subst value
    rfl
  | succ width ih =>
    have quotient : value / 256 < 256 ^ width := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
      simpa [Nat.pow_succ, Nat.mul_comm] using fits
    simp only [encodeLE, decodeLE, BitVec.toNat_ofNat]
    rw [ih _ quotient]
    exact Nat.mod_add_div value 256

/-- Distinct in-range scalar values cannot acquire the same byte encoding. -/
theorem encodeLE_injective {width left right : Nat}
    (leftFits : left < 256 ^ width) (rightFits : right < 256 ^ width)
    (equal : encodeLE width left = encodeLE width right) : left = right := by
  have decoded := congrArg decodeLE equal
  simpa only [decodeLE_encodeLE width left leftFits,
    decodeLE_encodeLE width right rightFits] using decoded


@[simp] theorem Part.bytes_size (part : Part) : part.bytes.size = part.size := by
  cases part <;>
    simp [Part.bytes, Part.size, fieldsBytes, identificationPrefix, headerFields,
      programHeaderFields, sectionHeaderFields, symbolFields, relaFields, Nat.add_comm]
  omega


@[simp] theorem Block.bytes_size (block : Block) : block.bytes.size = block.size :=
  Part.bytes_size block.body


theorem File.bytes_size (file : File) :
    file.bytes.size = (file.blocks.map Block.size).sum := by
  rcases file with ⟨blocks⟩
  change (blocks.flatMap fun block => block.bytes.toList).length = _
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp [ih]


theorem BlocksAt.append (offset : Nat) (left right : List Block) :
    BlocksAt offset (left ++ right) ↔
      BlocksAt offset left ∧ BlocksAt (offset + (left.map Block.size).sum) right := by
  induction left generalizing offset with
  | nil => simp [BlocksAt]
  | cons block rest ih => simp [BlocksAt, ih, Nat.add_assoc, and_assoc]


def File.Interprets (file : File) (object : ObjectFile) : Prop :=
  readObject file.bytes = some object


@[simp] theorem File.ofBytes_bytes (bytes : Bytes) : (File.ofBytes bytes).bytes = bytes := by
  simp [File.ofBytes, File.bytes, Block.bytes, Part.bytes]

@[simp] theorem File.ofBytes_wellFormed (bytes : Bytes) : (File.ofBytes bytes).WellFormed := by
  trivial

/-- Independently provided parser certificates can be transported along exact
serialization equality. This theorem does not create such a certificate. -/
theorem File.interprets_of_lossless {file : File} {original : Bytes} {object : ObjectFile}
    (lossless : file.Lossless original) (parsed : readObject original = some object) :
    file.Interprets object := by
  change readObject file.bytes = some object
  rw [show file.bytes = original from lossless]
  exact parsed

theorem File.interpretation_unique {file : File} {left right : ObjectFile}
    (first : file.Interprets left) (second : file.Interprets right) : left = right :=
  Option.some.inj (first.symm.trans second)

/-- List equality is sufficient for a byte-identity certificate. -/
theorem File.lossless_of_toList {file : File} {original : Bytes}
    (equal : file.bytes.toList = original.toList) : file.Lossless original :=
  Array.toList_inj.mp equal


end Silmaril.Formats.ELF.Ast
