module

public import Silmaril.Prelude.Bytes.Defs
import Silmaril.Proofs.Prelude.Bytes.Basic

/-! # Kernel bytes: the operations against `toList`

Every operation of `Silmaril.KBytes` is specified by `toList`. The hypotheses are
`t.wf = true` (cached lengths are correct) and that the requested bytes are in range.
Proofs are in `Silmaril.Proofs.Prelude.Bytes.Basic`.
-/

@[expose] public section

namespace Silmaril.KBytes

open Silmaril.Proofs.Prelude.Bytes

/-! ## Reads -/

theorem length_toList (t : KBytes) (ht : t.wf = true) : t.toList.length = t.len :=
  Proofs.Prelude.Bytes.length_toList t ht

/-- `read` is the little-endian value of the requested window. -/
theorem read_eq (t : KBytes) (off w : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    t.read off w = leVal ((t.toList.drop off).take w) :=
  Proofs.Prelude.Bytes.read_eq t off w ht h

/-- The digits of a read are the bytes read. -/
theorem unpack_read (t : KBytes) (ht : t.wf = true) {off w : Nat} (h : off + w ≤ t.len) :
    unpack w (t.read off w) = (t.toList.drop off).take w :=
  Proofs.Prelude.Bytes.unpack_read t ht h

/-- `readLE` answers exactly the in-range windows, with their little-endian values. -/
theorem readLE_eq (t : KBytes) (ht : t.wf = true) (off w : Nat) :
    t.readLE off w =
      if off + w ≤ t.toList.length then some (leVal ((t.toList.drop off).take w)) else none :=
  Proofs.Prelude.Bytes.readLE_eq t ht off w

theorem get?_eq (t : KBytes) (ht : t.wf = true) (i : Nat) : t.get? i = t.toList[i]? :=
  Proofs.Prelude.Bytes.get?_eq t ht i

/-! ## Ropes -/

theorem toList_append (a b : KBytes) : (a ++ b).toList = a.toList ++ b.toList := rfl

theorem wf_append {a b : KBytes} (ha : a.wf = true) (hb : b.wf = true) : (a ++ b).wf = true :=
  Proofs.Prelude.Bytes.wf_append ha hb

theorem len_slice (t : KBytes) (off w : Nat) : (t.slice off w).len = w :=
  Proofs.Prelude.Bytes.len_slice t off w

theorem wf_slice (t : KBytes) (off w : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    (t.slice off w).wf = true :=
  (slice_spec t off w ht h).1

theorem toList_slice (t : KBytes) (off w : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    (t.slice off w).toList = (t.toList.drop off).take w :=
  (slice_spec t off w ht h).2

/-! ## Canonical form and equality -/

theorem wf_canon (c : Nat) (t : KBytes) (ht : t.wf = true) : (t.canon c).wf = true :=
  (canon_spec c t ht).1

theorem toList_canon (c : Nat) (t : KBytes) (ht : t.wf = true) :
    (t.canon c).toList = t.toList :=
  (canon_spec c t ht).2

/-- Structural equality is sound for any shapes (complete only on canonical trees). -/
theorem toList_eq_of_beq (a b : KBytes) (h : a.beq b = true) : a.toList = b.toList :=
  Proofs.Prelude.Bytes.toList_eq_of_beq a b h

/-- Window-by-window equality is sound for any shapes. -/
theorem toList_eq_of_sameBytes (w : Nat) (a b : KBytes) (ha : a.wf = true) (hb : b.wf = true)
    (h : a.sameBytes w b = true) : a.toList = b.toList :=
  Proofs.Prelude.Bytes.toList_eq_of_sameBytes w a b ha hb h

/-- Ropes with the same canonical form hold the same bytes. -/
theorem toList_eq_of_canon_eq (c : Nat) (a b : KBytes) (ha : a.wf = true) (hb : b.wf = true)
    (h : a.canon c = b.canon c) : a.toList = b.toList := by
  rw [← toList_canon c a ha, ← toList_canon c b hb, h]

/-! ## Chunk literals -/

theorem wf_ofChunks (c n : Nat) (cs : List Nat) : (ofChunks c n cs).wf = true :=
  (ofChunks_spec c n cs).1

/-- The canonical tree of chunk literals holds the bytes those literals encode. -/
theorem toList_ofChunks (c n : Nat) (cs : List Nat) :
    (ofChunks c n cs).toList = chunksBytes c n cs :=
  (ofChunks_spec c n cs).2

theorem toByteArray_ofChunks (c n : Nat) (cs : List Nat) :
    (ofChunks c n cs).toByteArray = decodeChunks c n cs := by
  simp only [toByteArray, decodeChunks, toList_ofChunks]

/-- A tree proved equal to the canonical tree of chunk literals has their bytes. This is the
bridge from raw chunk literals (`include_bytes`) to kernel bytes. -/
theorem toByteArray_eq_decodeChunks {t : KBytes} {c n : Nat} {cs : List Nat}
    (h : t = ofChunks c n cs) : t.toByteArray = decodeChunks c n cs := by
  rw [h, toByteArray_ofChunks]

theorem wf_of_eq_ofChunks {t : KBytes} {c n : Nat} {cs : List Nat}
    (h : t = ofChunks c n cs) : t.wf = true := by
  rw [h]; exact wf_ofChunks c n cs

/-! ## Compiled code -/

theorem toByteArray_eq_of_eqByteArray (t : KBytes) (b : ByteArray)
    (h : t.eqByteArray b = true) : t.toByteArray = b :=
  toList_eq_of_eqByteArray t b h

end Silmaril.KBytes
