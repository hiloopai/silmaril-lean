module

public import Silmaril.Formats.ELF.Cst
public import Silmaril.Data.BinaryImage
public import Silmaril.Data.ByteLiterals.Types

/-! # `IsCST`: a fast, chunked check that a CST is a file's bytes

`Cst.File.IsCST cst img lits : Bool` checks that serializing `cst` gives exactly the bytes of
the pinned file `img` (a `Silmaril.BinaryImage`, the `binary_image` chunk form). It is a list of
**ranged equality checks**, one per CST block: the block at offset `o` with encoded length `n`
satisfies `bytes[o, o + n) = encode block`, both sides compared as little-endian `Nat`s. Each
block also checks its layout step: its offset is where the previous block ended, the last block
ends at the file size, and its typed fields fit their widths (`Ast.BlocksAt`). Nothing is parsed
and nothing is searched.

* The file side of a comparison is a shift and a `mod` per 4 KiB chunk literal it touches, which
  the kernel computes with GMP (`BinaryImage.rangeNat`).
* Typed records (header, program and section headers, symbols, RELAs) are encoded as `Nat`s
  directly from their fields (`Ast.fieldsNat`).
* Raw payloads (section contents, padding) would cost one kernel step per byte if unfolded.
  Generated CSTs store them as chunk literals, `toBitVecBytes (decode chunk size [c₀, …])`, so
  the optional table `lits` names those literals per block (`RawLiteral`) and the check uses
  their value directly. `File.LiteralsMatch cst lits` says the table names the CST's own
  payloads; it is proved by `rfl` (the kernel compares the literals, it does not evaluate them),
  see the `cst_literals` command in `Silmaril.Formats.ELF.Cst.IsCstCommand`. Without a table
  (`lits = []`) raw payloads are packed 256 bytes at a time, which is correct but slow.

`File.isCST_sound` turns `IsCST cst img lits = true` into `cst.bytes = some img.bits`, so every
fact about the CST is a fact about the file; `File.isCST_layout` adds `LayoutWellFormed` and the
per-block slices.

**Chunks.** `File.segmentOK cst img lits lo hi` checks blocks `lo` to `hi - 1` only. Each
segment is an independent kernel goal (`by decide +kernel`); `File.segmentOK_trans` chains
segments and `File.isCST_of_segment` turns the whole range into `IsCST`. `tools/elf-ast --iscst`
emits one theorem per segment.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Formats.ELF.Ast

/-! ## Little-endian values of byte lists -/

/-- The little-endian value of a list of fields, each truncated to its width (as `encodeLE`
does). Equal to `decodeLE (fieldsBytes fields)` (`decodeLE_fieldsBytes`). -/
def fieldsNat : Fields → Nat
  | [] => 0
  | (width, value) :: rest => value % 256 ^ width + 256 ^ width * fieldsNat rest

theorem decodeLE_append (first second : List (BitVec 8)) :
    decodeLE (first ++ second) = decodeLE first + 256 ^ first.length * decodeLE second := by
  induction first with
  | nil => simp [decodeLE]
  | cons byte rest ih =>
    simp only [List.cons_append, decodeLE, ih, List.length_cons, Nat.pow_succ, Nat.mul_add,
      Nat.add_assoc]
    rw [Nat.mul_comm (256 ^ rest.length) 256, Nat.mul_assoc]

theorem decodeLE_lt (bytes : List (BitVec 8)) : decodeLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [decodeLE]
  | cons byte rest ih =>
    simp only [decodeLE, List.length_cons, Nat.pow_succ]
    have := byte.isLt
    simp only [Nat.reducePow] at this
    have : 256 * decodeLE rest + 256 ≤ 256 * 256 ^ rest.length := by
      rw [show 256 * decodeLE rest + 256 = 256 * (decodeLE rest + 1) by omega]
      exact Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (256 ^ rest.length)]
    omega

theorem decodeLE_encodeLE_mod (width value : Nat) :
    decodeLE (encodeLE width value) = value % 256 ^ width := by
  induction width generalizing value with
  | zero => simp [encodeLE, decodeLE, Nat.mod_one]
  | succ width ih =>
    have split : value % 256 ^ (width + 1) = value % 256 + 256 * (value / 256 % 256 ^ width) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ width) 256, Nat.mod_mul]
    rw [split]
    simp only [encodeLE, decodeLE, BitVec.toNat_ofNat, ih]

theorem decodeLE_fieldsBytes (fields : Fields) :
    decodeLE (fieldsBytes fields) = fieldsNat fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    obtain ⟨width, value⟩ := field
    simp only [fieldsBytes, List.flatMap_cons] at ih ⊢
    rw [decodeLE_append, decodeLE_encodeLE_mod, encodeLE_length, ih]
    rfl

/-- Lists of one length with one little-endian value are equal. -/
theorem decodeLE_injective {first second : List (BitVec 8)} (length : first.length = second.length)
    (value : decodeLE first = decodeLE second) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons byte rest ih =>
    cases second with
    | nil => simp at length
    | cons other others =>
      simp only [decodeLE] at value
      have hb := byte.isLt
      have ho := other.isLt
      simp only [Nat.reducePow] at hb ho
      have low : byte.toNat = other.toNat := by omega
      have high : decodeLE rest = decodeLE others := by omega
      rw [BitVec.eq_of_toNat_eq low, ih (by simpa using length) high]

/-! ## Pieces -/

/-- A piece of a byte string: its length and its little-endian value. -/
abbrev Piece := Nat × Nat

/-- `Covers bytes pieces`: `bytes` is the concatenation of the pieces' byte strings. -/
inductive Covers : List (BitVec 8) → List Piece → Prop
  | nil : Covers [] []
  | cons (first : List (BitVec 8)) {rest : List (BitVec 8)} {pieces : List Piece} :
      Covers rest pieces → Covers (first ++ rest) ((first.length, decodeLE first) :: pieces)

theorem Covers.append {first second : List (BitVec 8)} {left right : List Piece}
    (h₁ : Covers first left) (h₂ : Covers second right) : Covers (first ++ second) (left ++ right) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons part _ ih => simpa [List.append_assoc] using Covers.cons part ih

theorem Covers.single (bytes : List (BitVec 8)) : Covers bytes [(bytes.length, decodeLE bytes)] := by
  simpa using Covers.cons bytes Covers.nil

/-- Covering with pieces whose length and value are given by other expressions. -/
theorem Covers.single' {bytes : List (BitVec 8)} {length value : Nat}
    (hl : bytes.length = length) (hv : decodeLE bytes = value) : Covers bytes [(length, value)] := by
  subst hl hv
  exact Covers.single bytes

/-- Raw bytes in pieces of at most 256 bytes, so packing never builds a large number. This
costs kernel steps per byte; generated CSTs use `RawLiteral`s instead. -/
def rawPiecesAux : Nat → List (BitVec 8) → List Piece
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, byte :: rest =>
    let head := (byte :: rest).take 256
    (head.length, decodeLE head) :: rawPiecesAux fuel ((byte :: rest).drop 256)

def rawPieces (bytes : List (BitVec 8)) : List Piece := rawPiecesAux bytes.length bytes

theorem covers_rawPiecesAux : ∀ (fuel : Nat) (bytes : List (BitVec 8)), bytes.length ≤ fuel →
    Covers bytes (rawPiecesAux fuel bytes)
  | 0, bytes, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]
    exact Covers.nil
  | _ + 1, [], _ => Covers.nil
  | fuel + 1, byte :: rest, h => by
    have split := List.take_append_drop 256 (byte :: rest)
    simp only [rawPiecesAux]
    conv => lhs; rw [← split]
    refine Covers.cons _ (covers_rawPiecesAux fuel _ ?_)
    simp only [List.length_drop, List.length_cons] at h ⊢
    omega

theorem covers_rawPieces (bytes : List (BitVec 8)) : Covers bytes (rawPieces bytes) :=
  covers_rawPiecesAux _ bytes (Nat.le_refl _)

/-- The pieces of one physical part: typed records are one piece computed from their fields. -/
def Part.pieces : Part → List Piece
  | .header fields padding =>
      [(57 + padding.size, decodeLE (Part.header fields padding).bytes.toList)]
  | .programHeader _ fields => [(56, fieldsNat (programHeaderFields fields))]
  | .sectionHeader _ fields => [(64, fieldsNat (sectionHeaderFields fields))]
  | .symbol _ _ fields => [(24, fieldsNat (symbolFields fields))]
  | .rela _ _ fields => [(24, fieldsNat (relaFields fields))]
  | .raw _ bytes => rawPieces bytes.toList

theorem fieldsBytes_cover (fields : Fields) (length : Nat)
    (h : (fields.map Prod.fst).sum = length) :
    Covers (fieldsBytes fields) [(length, fieldsNat fields)] :=
  Covers.single' (by rw [← h]; exact fieldsBytes_length' fields) (decodeLE_fieldsBytes fields)
where
  fieldsBytes_length' (fields : Fields) :
      (fieldsBytes fields).length = (fields.map Prod.fst).sum := by
    induction fields with
    | nil => rfl
    | cons field rest ih =>
      simp only [fieldsBytes, List.flatMap_cons, List.length_append, encodeLE_length,
        List.map_cons, List.sum_cons] at *
      rw [ih]

theorem Part.covers_pieces (part : Part) : Covers part.bytes.toList part.pieces := by
  cases part with
  | header fields padding =>
    exact Covers.single' (by rw [Array.length_toList, Part.bytes_size]; rfl) rfl
  | programHeader _ fields => exact fieldsBytes_cover _ _ rfl
  | sectionHeader _ fields => exact fieldsBytes_cover _ _ rfl
  | symbol _ _ fields => exact fieldsBytes_cover _ _ rfl
  | rela _ _ fields => exact fieldsBytes_cover _ _ rfl
  | raw _ bytes => exact covers_rawPieces _

theorem Covers.length_sum {bytes : List (BitVec 8)} {pieces : List Piece}
    (h : Covers bytes pieces) : bytes.length = (pieces.map Prod.fst).sum := by
  induction h with
  | nil => rfl
  | cons first _ ih => simp [ih]

end Silmaril.Formats.ELF.Ast

namespace Silmaril.BinaryImage

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Ast Silmaril.IncludeBytes

/-! ## Chunk literals as raw payloads -/

/-- A raw payload given by its chunk literals, `toBitVecBytes (decode chunk size chunks)`. -/
structure RawLiteral where
  chunk : Nat
  size : Nat
  chunks : List Nat
  deriving DecidableEq, Repr

namespace RawLiteral

def bytes (lit : RawLiteral) : Bytes :=
  ByteLiterals.toBitVecBytes (decode lit.chunk lit.size lit.chunks)

/-- The literals cover the declared size. -/
def WF (lit : RawLiteral) : Prop := 0 < lit.chunk ∧ lit.size ≤ lit.chunk * lit.chunks.length

instance (lit : RawLiteral) : Decidable lit.WF := inferInstanceAs (Decidable (_ ∧ _))

/-- The little-endian value of `decode chunk len chunks`, chunk by chunk. -/
def valueAux (chunk : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | len, c :: cs =>
    c % 2 ^ (8 * min chunk len) + 2 ^ (8 * min chunk len) * valueAux chunk (len - chunk) cs

def value (lit : RawLiteral) : Nat := valueAux lit.chunk lit.size lit.chunks

theorem decodeLE_bytesLE (k c : Nat) :
    decodeLE ((bytesLE k c).map fun byte => BitVec.ofNat 8 byte.toNat) = c % 2 ^ (8 * k) := by
  induction k generalizing c with
  | zero => simp [bytesLE, decodeLE, Nat.mod_one]
  | succ k ih =>
    simp only [bytesLE, List.map_cons, decodeLE, BitVec.toNat_ofNat, ih]
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add, Nat.mod_mul]
    simp

theorem decodeLE_bytesChunks (chunk : Nat) : ∀ (len : Nat) (cs : List Nat),
    decodeLE ((bytesChunks chunk len cs).map fun byte => BitVec.ofNat 8 byte.toNat) =
      valueAux chunk len cs
  | _, [] => rfl
  | len, c :: cs => by
    have pow : (256 : Nat) ^ min chunk len = 2 ^ (8 * min chunk len) := by
      rw [Nat.pow_mul]
    rw [bytesChunks_cons, List.map_append, decodeLE_append, decodeLE_bytesLE,
      decodeLE_bytesChunks chunk (len - chunk) cs, List.length_map, length_bytesLE, valueAux, pow]

theorem bytes_toList (lit : RawLiteral) :
    lit.bytes.toList = (bytesChunks lit.chunk lit.size lit.chunks).map
      fun byte => BitVec.ofNat 8 byte.toNat := rfl

theorem covers (lit : RawLiteral) (wf : lit.WF) :
    Covers lit.bytes.toList [(lit.size, lit.value)] := by
  refine Covers.single' ?_ ?_
  · rw [bytes_toList, List.length_map, length_bytesChunks]
    exact Nat.min_eq_left wf.2
  · rw [bytes_toList, decodeLE_bytesChunks]
    rfl

end RawLiteral

/-! ## Byte ranges of a binary image -/

/-- The little-endian value of `n` bytes from `offset`, read from the chunk literals: per
chunk touched, one shift and one `mod`. `fuel` bounds the number of steps (`n` suffices). -/
def rangeNatAux (img : BinaryImage) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, offset, n =>
    if n = 0 then 0 else
      let r := offset % img.chunk
      let t := min n (img.chunk - r)
      (img.chunks.getD (offset / img.chunk) 0 >>> (8 * r)) % 2 ^ (8 * t) +
        2 ^ (8 * t) * rangeNatAux img fuel (offset + t) (n - t)

def rangeNat (img : BinaryImage) (offset n : Nat) : Nat := img.rangeNatAux n offset n

/-- Compare consecutive pieces against the file from `offset`; the end offset if all agree. -/
def checkPieces (img : BinaryImage) : Nat → List Piece → Option Nat
  | offset, [] => some offset
  | offset, (n, value) :: rest =>
    if img.rangeNat offset n = value then checkPieces img (offset + n) rest else none


/-! ## Soundness of the ranged comparison -/

theorem length_window (img : BinaryImage) (offset n : Nat) : (img.window offset n).length = n := by
  simp [window]

theorem window_add (img : BinaryImage) (offset n m : Nat) :
    img.window offset (n + m) = img.window offset n ++ img.window (offset + n) m := by
  simp only [window, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Nat.add_assoc]

theorem window_zero (img : BinaryImage) (offset : Nat) : img.window offset 0 = [] := rfl

/-- The base-256 digits of `x` pack back to `x` modulo `2 ^ (8 * t)`. -/
theorem decodeLE_digits (t : Nat) : ∀ x : Nat,
    decodeLE ((List.range t).map fun k => BitVec.ofNat 8 ((x >>> (8 * k)) % 256)) =
      x % 2 ^ (8 * t) := by
  induction t with
  | zero => intro x; simp [decodeLE, Nat.mod_one]
  | succ t ih =>
    intro x
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, decodeLE]
    have shift : ∀ k, x >>> (8 * (k + 1)) = (x >>> 8) >>> (8 * k) := by
      intro k
      rw [← Nat.shiftRight_add]
      congr 1
      omega
    have tail := ih (x >>> 8)
    simp only [Function.comp_def, Nat.succ_eq_add_one, shift]
    rw [tail, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow,
      show 8 * (t + 1) = 8 + 8 * t by omega, Nat.pow_add, Nat.mod_mul]
    simp only [Nat.reducePow, Nat.mod_mod]

theorem div_mod_of_lt_chunk {chunk offset k : Nat} (inside : offset % chunk + k < chunk) :
    (offset + k) / chunk = offset / chunk ∧ (offset + k) % chunk = offset % chunk + k := by
  have hc : 0 < chunk := by omega
  have split : offset + k = (offset % chunk + k) + chunk * (offset / chunk) := by
    have := Nat.mod_add_div offset chunk
    omega
  rw [split, Nat.add_mul_div_left _ _ hc, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt inside, Nat.mod_eq_of_lt inside]
  simp

/-- A window inside one chunk is a shift and a `mod` of that chunk's literal. -/
theorem decodeLE_window_chunk (img : BinaryImage) (offset t : Nat)
    (inside : offset % img.chunk + t ≤ img.chunk) :
    decodeLE (img.window offset t) =
      (img.chunks.getD (offset / img.chunk) 0 >>> (8 * (offset % img.chunk))) % 2 ^ (8 * t) := by
  rw [← decodeLE_digits]
  unfold window
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk : k < t := List.mem_range.mp hk
  obtain ⟨hdiv, hmod⟩ := div_mod_of_lt_chunk (chunk := img.chunk) (offset := offset) (k := k)
    (by omega)
  simp only [byte, hdiv, hmod, Nat.shiftRight_add, Nat.mul_add]

theorem rangeNatAux_eq (img : BinaryImage) (wf : img.WF) : ∀ (fuel offset n : Nat), n ≤ fuel →
    img.rangeNatAux fuel offset n = decodeLE (img.window offset n)
  | 0, offset, n, h => by
    rw [Nat.le_zero.mp h]
    rfl
  | fuel + 1, offset, n, h => by
    unfold rangeNatAux
    by_cases zero : n = 0
    · subst zero; rfl
    · simp only [zero, ↓reduceIte]
      have hc := wf.1
      have hr : offset % img.chunk < img.chunk := Nat.mod_lt _ hc
      have ht : 0 < min n (img.chunk - offset % img.chunk) := by omega
      have split : n = min n (img.chunk - offset % img.chunk) +
          (n - min n (img.chunk - offset % img.chunk)) := by omega
      conv => rhs; rw [split, window_add, decodeLE_append, length_window]
      rw [decodeLE_window_chunk img offset _ (by omega),
        rangeNatAux_eq img wf fuel _ _ (by omega)]
      have pow : (256 : Nat) ^ min n (img.chunk - offset % img.chunk) =
          2 ^ (8 * min n (img.chunk - offset % img.chunk)) := by
        rw [Nat.pow_mul]
      rw [pow]

theorem rangeNat_eq (img : BinaryImage) (wf : img.WF) (offset n : Nat) :
    img.rangeNat offset n = decodeLE (img.window offset n) :=
  img.rangeNatAux_eq wf n offset n (Nat.le_refl n)

/-- Agreeing pieces mean the covered bytes are the file's bytes from `offset`. -/
theorem checkPieces_sound (img : BinaryImage) (wf : img.WF) {bytes : List (BitVec 8)}
    {pieces : List Piece} (covers : Covers bytes pieces) :
    ∀ {offset stop : Nat}, img.checkPieces offset pieces = some stop →
      stop = offset + bytes.length ∧ bytes = img.window offset bytes.length := by
  induction covers with
  | nil =>
    intro offset stop h
    simp only [checkPieces, Option.some.injEq] at h
    exact ⟨by simp [h], rfl⟩
  | cons first _ ih =>
    intro offset stop h
    simp only [checkPieces] at h
    split at h
    · rename_i same
      obtain ⟨hstop, hrest⟩ := ih h
      rw [rangeNat_eq img wf] at same
      have hfirst : img.window offset first.length = first :=
        decodeLE_injective (by simp [length_window]) same
      refine ⟨by simp [hstop, Nat.add_assoc], ?_⟩
      rw [List.length_append, window_add, hfirst, ← hrest]
    · cases h

theorem bits_toList_eq_window (img : BinaryImage) (wf : img.WF) :
    img.bits.toList = img.window 0 img.size := by
  rw [← window_eq wf 0 img.size (by omega), List.drop_zero, List.take_of_length_le]
  rw [Array.length_toList, size_bits wf]

end Silmaril.BinaryImage

namespace Silmaril.Formats.ELF.Cst

open Ast (Piece fieldsNat rawPieces Covers)
open Silmaril.BinaryImage (RawLiteral)

/-! ## The check -/

/-- Pieces of a section body: one piece per symbol or RELA record. -/
def SectionBody.pieces : SectionBody → List Piece
  | .raw data => rawPieces data.toList
  | .symbols entries | .dynamicSymbols entries =>
      entries.map fun entry => (24, fieldsNat (Ast.symbolFields entry.raw))
  | .relas entries => entries.map fun entry => (24, fieldsNat (Ast.relaFields entry))
  | .noBits => []

/-- The raw payload a block stores, if it is raw bytes (a raw section body or padding). -/
def File.rawPayload? (file : File) : Part → Option Bytes
  | .sectionPayload index => do
      let part ← file.sections[index]?
      match part.body with
      | .raw data => some data
      | _ => none
  | .raw _ data => some data
  | _ => none

/-- Pieces of a CST part, with the same reference failures as `File.resolvePart`. A raw part
with a literal is one piece, the literal's value. -/
def File.partPieces (file : File) (lit : Option RawLiteral) (part : Part) : Option (List Piece) :=
  match lit with
  | some lit => if lit.WF then some [(lit.size, lit.value)] else none
  | none =>
    match part with
    | .sectionPayload index => do
        let part ← file.sections[index]?
        pure part.body.pieces
    | part => (file.resolvePart part).map Ast.Part.pieces

/-- One block: it resolves, its fields fit, its bytes are the file's bytes at its offset, and it
ends where the next block (or the file) starts. -/
def File.blockOK (file : File) (img : BinaryImage) (next : Nat) (lit : Option RawLiteral)
    (block : Block) : Bool :=
  match file.resolvePart block.body, file.partPieces lit block.body with
  | some part, some pieces =>
    decide part.WellFormed &&
      match img.checkPieces block.offset pieces with
      | some stop => stop == next
      | none => false
  | _, _ => false

/-- Where the next block starts: its offset, or the file size after the last block. -/
def nextOffset (img : BinaryImage) : List Block → Nat
  | [] => img.size
  | block :: _ => block.offset

/-- The first `count` blocks of `blocks` are correct; `lits` lists their raw literals. -/
def File.blocksOK (file : File) (img : BinaryImage) :
    Nat → List Block → List (Option RawLiteral) → Bool
  | 0, _, _ => true
  | _ + 1, [], _ => true
  | count + 1, block :: rest, lits =>
    file.blockOK img (nextOffset img rest) lits.head?.join block &&
      file.blocksOK img count rest lits.tail

/-- Blocks `lo` to `hi - 1` are correct: one independent kernel goal per segment. -/
def File.segmentOK (file : File) (img : BinaryImage) (lits : List (Option RawLiteral))
    (lo hi : Nat) : Bool :=
  file.blocksOK img (hi - lo) (file.blocks.drop lo) (lits.drop lo)

/-- The image is well formed and the first block starts at 0 (or the file is empty). -/
def File.startOK (file : File) (img : BinaryImage) : Bool :=
  decide img.WF && nextOffset img file.blocks == 0

/-- The CST serializes to exactly the bytes of `img`, checked by ranged comparisons. -/
def File.IsCST (file : File) (img : BinaryImage) (lits : List (Option RawLiteral) := []) : Bool :=
  file.startOK img && file.segmentOK img lits 0 file.blocks.length

/-- The table `lits` names, for each block, the literal its raw payload is. -/
def File.LiteralsMatch (file : File) (lits : List (Option RawLiteral)) : Prop :=
  ∀ (index : Nat) (block : Block) (lit : RawLiteral), file.blocks[index]? = some block →
    lits[index]? = some (some lit) → file.rawPayload? block.body = some lit.bytes

/-- The form in which generated tables are proved, by `rfl`. -/
def File.literalPayloads (file : File) (lits : List (Option RawLiteral)) : List (Option (Option Bytes)) :=
  (file.blocks.zip lits).map fun (block, lit) => lit.map fun _ => file.rawPayload? block.body

theorem File.literalsMatch_nil (file : File) : file.LiteralsMatch [] := by
  intro _ _ _ _ h
  simp at h

theorem File.literalsMatch_of_eq {file : File} {lits : List (Option RawLiteral)}
    (h : file.literalPayloads lits =
      (lits.take file.blocks.length).map (Option.map fun lit => some lit.bytes)) :
    file.LiteralsMatch lits := by
  intro index block lit hb hl
  have hi : index < file.blocks.length := by
    by_contra hn; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
  have := congrArg (·[index]?) h
  simp only [File.literalPayloads, List.getElem?_map, hl, List.getElem?_take, hi, ite_true] at this
  simpa [List.getElem?_zip_eq_some, hb, hl] using this

/-! ## Soundness -/

open Silmaril.BinaryImage in
theorem SectionBody.covers_pieces (body : SectionBody) : Covers body.bytes.toList body.pieces := by
  cases body with
  | raw data => exact Ast.covers_rawPieces _
  | symbols entries | dynamicSymbols entries =>
    simp only [SectionBody.bytes, SectionBody.pieces, List.toList_toArray]
    induction entries with
    | nil => exact Covers.nil
    | cons entry rest ih =>
      simp only [List.flatMap_cons, List.map_cons]
      exact (Ast.fieldsBytes_cover _ 24 rfl).append ih
  | relas entries =>
    simp only [SectionBody.bytes, SectionBody.pieces, List.toList_toArray]
    induction entries with
    | nil => exact Covers.nil
    | cons entry rest ih =>
      simp only [List.flatMap_cons, List.map_cons]
      exact (Ast.fieldsBytes_cover _ 24 rfl).append ih
  | noBits => exact Covers.nil

theorem File.resolvePart_of_rawPayload {file : File} {part : Part} {data : Bytes}
    {resolved : Ast.Part} (raw : file.rawPayload? part = some data)
    (h : file.resolvePart part = some resolved) : resolved.bytes = data := by
  cases part with
  | sectionPayload index =>
    simp only [File.rawPayload?, File.resolvePart] at raw h
    cases found : file.sections[index]? with
    | none => simp [found] at raw
    | some sec =>
      simp only [found] at raw h
      cases body : sec.body <;> simp [body] at raw h
      subst h raw
      rfl
  | raw role bytes =>
    simp only [File.rawPayload?, File.resolvePart, Option.some.injEq] at raw h
    subst h raw
    rfl
  | header => simp [File.rawPayload?] at raw
  | sectionHeader => simp [File.rawPayload?] at raw
  | programHeader => simp [File.rawPayload?] at raw

theorem File.covers_partPieces {file : File} {lit : Option RawLiteral} {part : Part}
    {pieces : List Piece} {resolved : Ast.Part}
    (literal : ∀ value, lit = some value → file.rawPayload? part = some value.bytes)
    (hp : file.partPieces lit part = some pieces) (hr : file.resolvePart part = some resolved) :
    Covers resolved.bytes.toList pieces := by
  cases lit with
  | some value =>
    simp only [File.partPieces] at hp
    split at hp
    · rename_i wf
      cases hp
      rw [File.resolvePart_of_rawPayload (literal value rfl) hr]
      exact value.covers wf
    · cases hp
  | none =>
    cases part with
    | sectionPayload index =>
      simp only [File.partPieces, File.resolvePart] at hp hr
      cases found : file.sections[index]? with
      | none => simp [found] at hp
      | some sec =>
        simp only [found] at hp hr
        simp at hp hr
        subst hp hr
        exact sec.body.covers_pieces
    | header padding =>
      simp only [File.partPieces, hr, Option.map_some, Option.some.injEq] at hp
      subst hp; exact resolved.covers_pieces
    | sectionHeader index =>
      simp only [File.partPieces, hr, Option.map_some, Option.some.injEq] at hp
      subst hp; exact resolved.covers_pieces
    | programHeader index =>
      simp only [File.partPieces, hr, Option.map_some, Option.some.injEq] at hp
      subst hp; exact resolved.covers_pieces
    | raw role data =>
      simp only [File.partPieces, hr, Option.map_some, Option.some.injEq] at hp
      subst hp; exact resolved.covers_pieces

/-- A checked block resolves to an AST block whose bytes are the file's bytes at its offset. -/
theorem File.blockOK_sound {file : File} {img : BinaryImage} {next : Nat}
    {lit : Option RawLiteral} {block : Block} (wf : img.WF)
    (literal : ∀ value, lit = some value → file.rawPayload? block.body = some value.bytes)
    (h : file.blockOK img next lit block = true) :
    ∃ resolved, file.resolveBlock block = some resolved ∧ resolved.offset = block.offset ∧
      resolved.body.WellFormed ∧
      resolved.bytes.toList = img.window block.offset resolved.size ∧
      block.offset + resolved.size = next := by
  unfold File.blockOK at h
  split at h
  · rename_i part pieces hr hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨wellFormed, rest⟩ := h
    split at rest
    · rename_i stop hstop
      have covers := File.covers_partPieces literal hp hr
      obtain ⟨hend, hbytes⟩ := img.checkPieces_sound wf covers hstop
      have hsize : part.bytes.toList.length = part.size := by
        rw [Array.length_toList, Ast.Part.bytes_size]
      refine ⟨⟨block.offset, part⟩, by simp [File.resolveBlock, hr], rfl, wellFormed, ?_, ?_⟩
      · change part.bytes.toList = img.window block.offset part.size
        rw [← hsize]; exact hbytes
      · change block.offset + part.size = next
        rw [← hsize, ← hend]; exact beq_iff_eq.mp rest
    · cases rest
  · cases h

/-- What a run of checked blocks gives: they resolve, sit contiguously from the first offset to
the end of the file, and each one's bytes are the file's bytes at its offset. -/
theorem File.blocksOK_sound {file : File} {img : BinaryImage} (wf : img.WF) :
    ∀ (blocks : List Block) (count : Nat) (lits : List (Option RawLiteral)),
      blocks.length ≤ count →
      (∀ (index : Nat) (block : Block) (lit : RawLiteral), blocks[index]? = some block →
        lits[index]? = some (some lit) → file.rawPayload? block.body = some lit.bytes) →
      file.blocksOK img count blocks lits = true →
      ∃ layout, blocks.mapM file.resolveBlock = some layout ∧
        Ast.BlocksAt (nextOffset img blocks) layout ∧
        layout.flatMap (fun block => block.bytes.toList) =
          img.window (nextOffset img blocks) (img.size - nextOffset img blocks) ∧
        nextOffset img blocks ≤ img.size ∧
        ∀ block ∈ layout, block.body.WellFormed ∧
          block.bytes.toList = img.window block.offset block.size ∧
          block.offset + block.size ≤ img.size
  | [], _, _, _, _, _ => ⟨[], rfl, trivial, by simp [nextOffset, BinaryImage.window], by simp [nextOffset],
      by simp⟩
  | block :: rest, count, lits, hlen, literal, h => by
    obtain ⟨count, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by simp at hlen; omega⟩
    simp only [File.blocksOK, Bool.and_eq_true] at h
    obtain ⟨hblock, hrest⟩ := h
    obtain ⟨resolved, hres, hoff, wellFormed, hbytes, hnext⟩ :=
      File.blockOK_sound wf (fun value hv => literal 0 block value rfl (by
        cases lits with
        | nil => simp at hv
        | cons first others => simpa using hv)) hblock
    obtain ⟨layout, hmap, hat, hflat, hle, hall⟩ :=
      File.blocksOK_sound wf rest count lits.tail (by simp at hlen; omega)
        (fun index b lit hb hl => literal (index + 1) b lit (by simpa using hb) (by
          cases lits with
          | nil => simp at hl
          | cons first others => simpa using hl)) hrest
    have hsize : resolved.bytes.toList.length = resolved.size := by
      rw [Array.length_toList, Ast.Block.bytes_size]
    refine ⟨resolved :: layout, by simp [List.mapM_cons, hres, hmap], ?_, ?_, ?_, ?_⟩
    · refine ⟨hoff, wellFormed, ?_⟩
      show Ast.BlocksAt (block.offset + resolved.size) layout
      rw [hnext]; exact hat
    · rw [List.flatMap_cons, hflat, hbytes, ← hnext, ← BinaryImage.window_add]
      show img.window block.offset _ = img.window block.offset (img.size - block.offset)
      congr 1
      omega
    · simp only [nextOffset]; omega
    · intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · rw [hoff]; exact ⟨wellFormed, hbytes, by omega⟩
      · exact hall b hb

theorem File.blocksOK_add (file : File) (img : BinaryImage) :
    ∀ (m n : Nat) (blocks : List Block) (lits : List (Option RawLiteral)),
      file.blocksOK img (m + n) blocks lits =
        (file.blocksOK img m blocks lits && file.blocksOK img n (blocks.drop m) (lits.drop m))
  | 0, n, blocks, lits => by simp [File.blocksOK]
  | m + 1, n, [], lits => by
    rw [Nat.add_right_comm]
    cases n <;> simp [File.blocksOK]
  | m + 1, n, block :: rest, lits => by
    rw [Nat.add_right_comm]
    simp only [File.blocksOK, List.drop_succ_cons, Bool.and_assoc]
    rw [File.blocksOK_add file img m n rest lits.tail]
    cases lits <;> simp

/-- Chain two adjacent segments. -/
theorem File.segmentOK_trans {file : File} {img : BinaryImage} {lits : List (Option RawLiteral)}
    {lo mid hi : Nat} (h₁ : lo ≤ mid) (h₂ : mid ≤ hi)
    (left : file.segmentOK img lits lo mid = true) (right : file.segmentOK img lits mid hi = true) :
    file.segmentOK img lits lo hi = true := by
  unfold File.segmentOK at *
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, File.blocksOK_add, left,
    List.drop_drop, List.drop_drop, show lo + (mid - lo) = mid by omega, right]
  rfl

/-- Assemble `IsCST` from the start check and one segment covering every block. -/
theorem File.isCST_of_segment {file : File} {img : BinaryImage} {lits : List (Option RawLiteral)}
    {count : Nat} (start : file.startOK img = true) (length : file.blocks.length = count)
    (all : file.segmentOK img lits 0 count = true) : file.IsCST img lits = true := by
  simp only [File.IsCST, start, length, all, Bool.and_self]

theorem File.isCST_spec {file : File} {img : BinaryImage} {lits : List (Option RawLiteral)}
    (h : file.IsCST img lits = true) (literal : file.LiteralsMatch lits) :
    img.WF ∧ ∃ layout, file.layout = some ⟨layout⟩ ∧ Ast.BlocksAt 0 layout ∧
      layout.flatMap (fun block => block.bytes.toList) = img.window 0 img.size ∧
      ∀ block ∈ layout, block.body.WellFormed ∧
        block.bytes.toList = img.window block.offset block.size ∧
        block.offset + block.size ≤ img.size := by
  simp only [File.IsCST, File.startOK, File.segmentOK, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Nat.sub_zero, List.drop_zero] at h
  obtain ⟨⟨wf, start⟩, blocks⟩ := h
  obtain ⟨layout, hmap, hat, hflat, -, hall⟩ :=
    File.blocksOK_sound wf file.blocks _ lits (Nat.le_refl _) literal blocks
  rw [start, Nat.sub_zero] at hflat
  rw [start] at hat
  exact ⟨wf, layout, by simp [File.layout, hmap], hat, hflat, hall⟩

/-- **Soundness.** A CST that passes `IsCST` serializes to exactly the image's bytes. -/
theorem File.isCST_sound {file : File} {img : BinaryImage} {lits : List (Option RawLiteral)}
    (h : file.IsCST img lits = true) (literal : file.LiteralsMatch lits) :
    file.bytes = some img.bits := by
  obtain ⟨wf, layout, hlayout, -, hflat, -⟩ := File.isCST_spec h literal
  rw [File.bytes_of_layout hlayout]
  congr 1
  apply Array.toList_inj.mp
  rw [img.bits_toList_eq_window wf, ← hflat]
  rfl

/-- Soundness without a literal table (`lits = []`). -/
theorem File.isCST_sound_nil {file : File} {img : BinaryImage} (h : file.IsCST img = true) :
    file.bytes = some img.bits :=
  File.isCST_sound h file.literalsMatch_nil

theorem File.isCST_lossless {file : File} {img : BinaryImage} {lits : List (Option RawLiteral)}
    (h : file.IsCST img lits = true) (literal : file.LiteralsMatch lits) :
    file.Lossless img.bits :=
  File.isCST_sound h literal

theorem File.isCST_layoutWellFormed {file : File} {img : BinaryImage}
    {lits : List (Option RawLiteral)} (h : file.IsCST img lits = true)
    (literal : file.LiteralsMatch lits) : file.LayoutWellFormed := by
  obtain ⟨-, layout, hlayout, hat, -⟩ := File.isCST_spec h literal
  exact ⟨⟨layout⟩, hlayout, hat⟩

/-- Every resolved block is the slice of the file at its offset: the per-block form used to
transport reader facts. -/
theorem File.isCST_slice {file : File} {img : BinaryImage} {lits : List (Option RawLiteral)}
    (h : file.IsCST img lits = true) (literal : file.LiteralsMatch lits)
    {layout : Ast.File} (hlayout : file.layout = some layout) :
    ∀ block ∈ layout.blocks,
      slice img.bits block.offset block.size = some block.bytes := by
  obtain ⟨wf, blocks, hl, -, -, hall⟩ := File.isCST_spec h literal
  rw [hl, Option.some.injEq] at hlayout
  subst hlayout
  intro block hb
  obtain ⟨-, hbytes, hle⟩ := hall block hb
  rw [img.slice_bits wf]
  simp only [hle, ↓reduceIte]
  congr 1
  exact Array.toList_inj.mp hbytes.symm

end Silmaril.Formats.ELF.Cst
