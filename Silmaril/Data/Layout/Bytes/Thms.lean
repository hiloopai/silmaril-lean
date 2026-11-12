module

public import Silmaril.Data.Layout.Bytes.Defs
public import Silmaril.Data.Layout.Thms

/-!
# Byte views: read-after-write and frame lemmas

* Memory level: `get?_write_outside`, `get?_write_inside`, `read_congr`,
  `read_write_outside` (disjoint ranges), `read_write_self`, `readable_write`.
* Codecs: `leDecode_leEncode`, `decode_encode` (values reduced modulo the width),
  `length_encode`.
* Struct lenses, for a well-formed layout (`DeclLayout.WF`, e.g. by `declLayout_wf`):
  `readField_writeField_self`, `readField_writeField_other` (struct members are framed),
  `get?_writeField_pad` (padding is framed, for structs and unions),
  `get?_writeField_outside` (a member write stays inside the record), the name-based
  `read?_write?_self`/`read?_write?_other`, `readInt_writeInt_self`, and the padding
  specifications `padOK_preserved_writeField`, `PadOK.zero_writeField`.
-/

@[expose] public section

namespace Silmaril.Data.Layout

namespace ByteMem

variable {M : Type} [ByteMem M]

theorem get?_write_outside (m : M) (a : Nat) (bs : List Byte) (b : Nat)
    (h : b < a ∨ a + bs.length ≤ b) : get? (write m a bs) b = get? m b := by
  induction bs generalizing m a with
  | nil => rfl
  | cons x xs ih =>
    simp only [write]
    rw [ih _ _ (by simp at h; omega), get?_set_ne _ _ _ _ (by simp at h; omega)]

theorem isSome_write {m : M} {a : Nat} {bs : List Byte} {b : Nat} (h : (get? m b).isSome) :
    (get? (write m a bs) b).isSome := by
  induction bs generalizing m a with
  | nil => exact h
  | cons x xs ih =>
    simp only [write]
    apply ih
    by_cases hab : a = b
    · subst hab; rw [get?_set_self _ _ _ h]; rfl
    · rw [get?_set_ne _ _ _ _ hab]; exact h

theorem readable_write {m : M} {a n : Nat} {b : Nat} {bs : List Byte} (h : Readable m a n) :
    Readable (write m b bs) a n := fun i hi => isSome_write (h i hi)

theorem get?_write_inside {m : M} {a : Nat} {bs : List Byte} {i : Nat} (hi : i < bs.length)
    (h : (get? m (a + i)).isSome) : get? (write m a bs) (a + i) = bs[i]? := by
  induction bs generalizing m a i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [write]
    cases i with
    | zero =>
      rw [get?_write_outside _ _ _ _ (by omega)]
      simp only [Nat.add_zero] at h ⊢
      rw [get?_set_self _ _ _ h]; rfl
    | succ i =>
      have : a + (i + 1) = a + 1 + i := by omega
      rw [this, ih (by simpa using hi)]
      · rfl
      · rw [get?_set_ne _ _ _ _ (by omega)]; rw [← this]; exact h

theorem read_congr {m m' : M} {a n : Nat} (h : ∀ i < n, get? m (a + i) = get? m' (a + i)) :
    read m a n = read m' a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [read]
    rw [show get? m a = get? m' a from by simpa using h 0 (by omega),
      ih (fun i hi => by rw [show a + 1 + i = a + (i + 1) by omega]; exact h (i + 1) (by omega))]

/-- Writing outside a range does not change what it reads. -/
theorem read_write_outside (m : M) {a : Nat} {bs : List Byte} {b n : Nat}
    (h : a + bs.length ≤ b ∨ b + n ≤ a) : read (write m a bs) b n = read m b n :=
  read_congr fun i hi => get?_write_outside m a bs (b + i) (by omega)

theorem read_length {m : M} {a n : Nat} {bs : List Byte} (h : read m a n = some bs) :
    bs.length = n := by
  induction n generalizing a bs with
  | zero => cases h; rfl
  | succ n ih =>
    simp only [read] at h
    split at h
    · cases h; simp [ih (by assumption)]
    · cases h

theorem read_eq_some_of_get? {m : M} {a : Nat} {bs : List Byte}
    (h : ∀ i < bs.length, get? m (a + i) = bs[i]?) : read m a bs.length = some bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [read, List.length_cons]
    rw [show get? m a = some x by simpa using h 0 (by simp),
      ih (fun i hi => by
        rw [show a + 1 + i = a + (i + 1) by omega]; simpa using h (i + 1) (by simp; omega))]

theorem readable_of_read {m : M} {a n : Nat} {bs : List Byte} (h : read m a n = some bs) :
    Readable m a n := by
  induction n generalizing a bs with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [read] at h
    split at h
    · rename_i b bs' hb hbs
      intro i hi
      cases i with
      | zero => simp [hb]
      | succ i =>
        rw [show a + (i + 1) = a + 1 + i by omega]
        exact ih hbs i (by omega)
    · cases h

/-- Reading back what was written over present bytes. -/
theorem read_write_self {m : M} {a : Nat} {bs : List Byte} (h : Readable m a bs.length) :
    read (write m a bs) a bs.length = some bs :=
  read_eq_some_of_get? fun i hi => get?_write_inside hi (h i hi)

end ByteMem

/-! ## Codecs -/

theorem length_leEncode (n v : Nat) : (leEncode n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [leEncode, ih]

theorem leDecode_leEncode (n v : Nat) : leDecode (leEncode n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [leEncode, leDecode, Nat.mod_one]
  | succ n ih =>
    simp only [leEncode, leDecode, ih, BitVec.toNat_ofNat]
    show v % 256 + 256 * (v / 256 % 256 ^ n) = v % 256 ^ (n + 1)
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

theorem length_encode (e : Endian) (n v : Nat) : (encode e n v).length = n := by
  cases e <;> simp [encode, length_leEncode]

theorem decode_encode (e : Endian) (n v : Nat) : decode e (encode e n v) = v % 256 ^ n := by
  cases e <;> simp [encode, decode, leDecode_leEncode]

/-! ## Struct lenses -/

namespace DeclLayout

variable {M : Type} [ByteMem M] {L : DeclLayout} {m : M} {base : Nat}

theorem readField_writeField_self {f : PlacedField} {bs : List Byte} (hlen : bs.length = f.size)
    (h : ByteMem.Readable m (base + f.off) f.size) :
    readField (writeField m base f bs) base f = some bs := by
  simp only [readField, writeField]
  rw [← hlen] at h ⊢
  exact ByteMem.read_write_self h

/-- Writing one member of a well-formed struct leaves every other member unchanged. -/
theorem readField_writeField_other (hL : L.WF) (hk : L.kind = .struct) {f g : PlacedField}
    (hf : f ∈ L.fields) (hg : g ∈ L.fields) (hne : f ≠ g) {bs : List Byte}
    (hlen : bs.length = f.size) :
    readField (writeField m base f bs) base g = readField m base g := by
  simp only [readField, writeField]
  apply ByteMem.read_write_outside
  have := hL.disjoint_of_ne hk hf hg hne
  omega

/-- Writing a member leaves every padding byte unchanged (structs and unions). -/
theorem get?_writeField_pad {f : PlacedField} (hf : f ∈ L.fields) {k : Nat}
    (hpad : L.isPad k = true) {bs : List Byte} (hlen : bs.length = f.size) :
    ByteMem.get? (writeField m base f bs) (base + k) = ByteMem.get? m (base + k) := by
  simp only [isPad, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hpad
  have := hpad.2 f hf
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
  simp only [writeField]
  apply ByteMem.get?_write_outside
  omega

/-- A member write changes no byte outside the record. -/
theorem get?_writeField_outside (hL : L.WF) {f : PlacedField} (hf : f ∈ L.fields) {x : Nat}
    (hx : x < base ∨ base + L.shape.size ≤ x) {bs : List Byte} (hlen : bs.length = f.size) :
    ByteMem.get? (writeField m base f bs) x = ByteMem.get? m x := by
  have := hL.inBounds f hf
  simp only [writeField]
  apply ByteMem.get?_write_outside
  omega

/-- Member writes keep the padding (`PadSpec.preserved`). -/
theorem padOK_preserved_writeField {f : PlacedField} (hf : f ∈ L.fields) {bs : List Byte}
    (hlen : bs.length = f.size) : PadOK L .preserved m (writeField m base f bs) base :=
  fun _ hk => get?_writeField_pad hf hk hlen

/-- Member writes keep zero padding zero. -/
theorem PadOK.zero_writeField {before : M} (h : PadOK L .zero before m base) {f : PlacedField}
    (hf : f ∈ L.fields) {bs : List Byte} (hlen : bs.length = f.size) (before' : M) :
    PadOK L .zero before' (writeField m base f bs) base :=
  fun k hk => (get?_writeField_pad hf hk hlen).trans (h k hk)

theorem read?_write?_self {name : String} {bs : List Byte} {m' : M}
    (hw : L.write? m base name bs = some m')
    (hr : ∀ f, L.field? name = some f → ByteMem.Readable m (base + f.off) f.size) :
    L.read? m' base name = some bs := by
  simp only [write?, Option.bind_eq_some_iff] at hw
  obtain ⟨f, hf, hw⟩ := hw
  split at hw
  · cases hw
    simp only [read?, hf, Option.bind_some]
    exact readField_writeField_self (by assumption) (hr f hf)
  · cases hw

/-- Writing member `name` of a well-formed struct leaves member `name'` unchanged. -/
theorem read?_write?_other (hL : L.WF) (hk : L.kind = .struct) {name name' : String}
    (hne : name ≠ name') {bs : List Byte} {m' : M} (hw : L.write? m base name bs = some m') :
    L.read? m' base name' = L.read? m base name' := by
  simp only [write?, Option.bind_eq_some_iff] at hw
  obtain ⟨f, hf, hw⟩ := hw
  split at hw
  · cases hw
    simp only [read?]
    cases hg : L.field? name' with
    | none => rfl
    | some g =>
      simp only [Option.bind_some]
      have h1 := mem_of_field? hf
      have h2 := mem_of_field? hg
      exact readField_writeField_other hL hk h1.1 h2.1
        (fun h => hne (h1.2.symm.trans (h ▸ h2.2))) (by assumption)
  · cases hw

/-- An integer member reads back the stored value, reduced modulo its width. -/
theorem readInt_writeInt_self (dm : DataModel) {name : String} {v : Nat} {m' : M}
    (hw : L.writeInt dm m base name v = some m') {f : PlacedField} (hf : L.field? name = some f)
    (hr : ByteMem.Readable m (base + f.off) f.size) :
    L.readInt dm m' base name = some (v % 256 ^ f.size) := by
  simp only [writeInt, hf, Option.bind_some, Option.some.injEq] at hw
  subst hw
  simp only [readInt, read?, hf, Option.bind_some]
  rw [readField_writeField_self (length_encode _ _ _) hr]
  simp [decode_encode]

end DeclLayout

end Silmaril.Data.Layout
