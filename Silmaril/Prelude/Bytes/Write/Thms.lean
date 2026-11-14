module

public import Silmaril.Prelude.Bytes.Write.Defs
public import Silmaril.Prelude.Bytes.Thms
import Silmaril.Proofs.Prelude.Bytes.Write

/-! # Writes on kernel bytes: specifications

Proofs are in `Silmaril.Proofs.Prelude.Bytes.Write`. The hypotheses are `t.wf = true`
(validity: cached lengths are correct) and that the written window is in range
(`off + w ≤ t.len`). Out of range, `writeLE?` and `ropeWriteLE?` return `none`.

Provenance: `toList_write`/`wf_write` restate `kwrite_spec`, and `toList_ropeWrite`/
`wf_ropeWrite` the store case of `memSimOn_kRope`, of hiloopai/silmaril-lean#133 (there
`Silmaril.Wasm.KernelEval`, stated through Wasm's `ListMem`). `toList_zerosCanon` restates
`kzeros_toListMem`. The other theorems are new here.
-/

@[expose] public section

namespace Silmaril.KBytes

open Silmaril.Proofs.Prelude.Bytes

/-! ## The byte-list model -/

theorem length_splice (bs : List UInt8) (off w v : Nat) (h : off + w ≤ bs.length) :
    (splice bs off w v).length = bs.length :=
  Proofs.Prelude.Bytes.length_splice bs off w v h

/-- Pointwise: a write changes exactly the bytes of its window, to the digits of `v`. -/
theorem getElem?_splice (bs : List UInt8) (off w v i : Nat) (h : off + w ≤ bs.length) :
    (splice bs off w v)[i]? =
      if off ≤ i ∧ i < off + w then some (UInt8.ofNat (v / 256 ^ (i - off))) else bs[i]? :=
  Proofs.Prelude.Bytes.getElem?_splice bs off w v i h

/-- Truncation: a `w`-byte write stores `v % 256 ^ w`. -/
theorem splice_mod (bs : List UInt8) (off w v : Nat) :
    splice bs off w (v % 256 ^ w) = splice bs off w v := by
  simp only [splice, unpack_mod]

/-! ## Path-copying writes -/

theorem len_write (t : KBytes) (off w v : Nat) : (t.write off w v).len = t.len :=
  Proofs.Prelude.Bytes.len_write t off w v

theorem wf_write (t : KBytes) (off w v : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    (t.write off w v).wf = true :=
  (write_spec t off w v ht h).1

theorem toList_write (t : KBytes) (off w v : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    (t.write off w v).toList = splice t.toList off w v :=
  (write_spec t off w v ht h).2

theorem writeLE?_of_le (t : KBytes) {off w : Nat} (v : Nat) (h : off + w ≤ t.len) :
    t.writeLE? off w v = some (t.write off w v) := by simp [writeLE?, h]

theorem writeLE?_of_lt (t : KBytes) {off w : Nat} (v : Nat) (h : t.len < off + w) :
    t.writeLE? off w v = none := by simp [writeLE?, Nat.not_le.2 h]

/-- Pointwise: byte `i` after a write. -/
theorem get?_write (t : KBytes) (ht : t.wf = true) {off w : Nat} (v : Nat)
    (h : off + w ≤ t.len) (i : Nat) :
    (t.write off w v).get? i = if off ≤ i ∧ i < off + w then
      some (UInt8.ofNat (v / 256 ^ (i - off))) else t.get? i :=
  Proofs.Prelude.Bytes.get?_write t ht v h i

/-- Reading the written window gives the truncated value back (across leaves too). -/
theorem readLE_write_self (t : KBytes) (ht : t.wf = true) {off w : Nat} (v : Nat)
    (h : off + w ≤ t.len) : (t.write off w v).readLE off w = some (v % 256 ^ w) :=
  readLE_self_of_splice ht (wf_write t off w v ht h) (toList_write t off w v ht h) h

/-- A read disjoint from the written window is unchanged. -/
theorem readLE_write_disjoint (t : KBytes) (ht : t.wf = true) {off w : Nat} (v : Nat)
    (h : off + w ≤ t.len) {a k : Nat} (hd : a + k ≤ off ∨ off + w ≤ a) :
    (t.write off w v).readLE a k = t.readLE a k :=
  readLE_disjoint_of_splice ht (wf_write t off w v ht h) (toList_write t off w v ht h) h hd

/-- Shared base: two writes on the same base agree on every byte outside both windows. -/
theorem get?_write_shared (t : KBytes) (ht : t.wf = true) {a k b m : Nat} (u v : Nat)
    (ha : a + k ≤ t.len) (hb : b + m ≤ t.len) {i : Nat} (hi : ¬(a ≤ i ∧ i < a + k))
    (hi' : ¬(b ≤ i ∧ i < b + m)) : (t.write a k u).get? i = (t.write b m v).get? i := by
  rw [get?_write t ht u ha, get?_write t ht v hb, ite_eq_right hi, ite_eq_right hi']

/-- Disjoint writes on the same base commute, as bytes. -/
theorem toList_write_comm (t : KBytes) (ht : t.wf = true) {a k b m : Nat} (u v : Nat)
    (ha : a + k ≤ t.len) (hb : b + m ≤ t.len) (hd : a + k ≤ b ∨ b + m ≤ a) :
    ((t.write a k u).write b m v).toList = ((t.write b m v).write a k u).toList :=
  Proofs.Prelude.Bytes.toList_write_comm t ht u v ha hb hd

/-- Performance invariant: a write keeps every leaf's length, hence any leaf-size bound. -/
theorem leafBound_write (c : Nat) (t : KBytes) (off w v : Nat) :
    leafBound c (t.write off w v) = leafBound c t :=
  Proofs.Prelude.Bytes.leafBound_write c t off w v

/-- Leaf numbers stay below `256 ^ len`, as in the literals of canonical trees. -/
theorem normal_write (t : KBytes) (off w v : Nat) (ht : t.wf = true) (h : off + w ≤ t.len)
    (hn : normal t = true) : normal (t.write off w v) = true :=
  Proofs.Prelude.Bytes.normal_write t off w v ht h hn

/-! ## Rope writes -/

theorem len_ropeWrite (t : KBytes) (off w v : Nat) (h : off + w ≤ t.len) :
    (t.ropeWrite off w v).len = t.len :=
  Proofs.Prelude.Bytes.len_ropeWrite t off w v h

theorem wf_ropeWrite (t : KBytes) (off w v : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    (t.ropeWrite off w v).wf = true :=
  (ropeWrite_spec t off w v ht h).1

theorem toList_ropeWrite (t : KBytes) (off w v : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    (t.ropeWrite off w v).toList = splice t.toList off w v :=
  (ropeWrite_spec t off w v ht h).2

/-- The two writes are interchangeable for reads: same bytes, different trees. -/
theorem readLE_ropeWrite (t : KBytes) (ht : t.wf = true) {off w : Nat} (v : Nat)
    (h : off + w ≤ t.len) (a k : Nat) :
    (t.ropeWrite off w v).readLE a k = (t.write off w v).readLE a k :=
  readLE_congr (wf_ropeWrite t off w v ht h) (wf_write t off w v ht h)
    (by rw [toList_ropeWrite t off w v ht h, toList_write t off w v ht h]) a k

/-! ## Slices -/

/-- A read of a slice is a read of the bytes it was cut from (ELF-style staged reads). -/
theorem readLE_slice (t : KBytes) (ht : t.wf = true) {off w : Nat} (h : off + w ≤ t.len)
    (o k : Nat) :
    (t.slice off w).readLE o k = if o + k ≤ w then t.readLE (off + o) k else none :=
  Proofs.Prelude.Bytes.readLE_slice t ht h o k

/-! ## Zeros -/

theorem wf_zeros (n : Nat) : (zeros n).wf = true := rfl

theorem toList_zeros (n : Nat) : (zeros n).toList = List.replicate n 0 :=
  unpack_zero n

theorem wf_zerosCanon (c n : Nat) : (zerosCanon c n).wf = true := wf_ofChunks _ _ _

theorem toList_zerosCanon (c n : Nat) (hc : 0 < c) :
    (zerosCanon c n).toList = List.replicate n 0 :=
  Proofs.Prelude.Bytes.toList_zerosCanon c n hc

end Silmaril.KBytes
