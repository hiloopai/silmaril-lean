module

public import Silmaril.Cerberus.Mem.Concrete.Defs

/-! Memory laws for the four-byte signed-int representation. -/

@[expose] public section
namespace Silmaril.Cerberus.Mem.Concrete

/-- A write replaces exactly its byte. impl_mem.ml:1506-1517. -/
theorem read_write_same (addr : Int) (b : Byte) (xs : Map Int Byte) :
    readByte addr (writeByte addr b xs) = b := by simp [readByte, writeByte]

/-- A write leaves every other byte unchanged. impl_mem.ml:1506-1517. -/
theorem read_write_other (a addr : Int) (b : Byte) (xs : Map Int Byte)
    (h : a ≠ addr) : readByte a (writeByte addr b xs) = readByte a xs := by
  simp [readByte, writeByte, Map.lookup_insert_of_key_ne (x := addr) (x' := a) b xs h]

/-- Representation followed by abstraction preserves a signed int. Lines 562-579,918-936. -/
theorem representation_roundtrip (addr n : Int) (xs : Map Int Byte)
    (lo : -2147483648 ≤ n) (hi : n ≤ 2147483647) :
    readInt addr (writeInt addr (reprInt n) xs) = some n := by
  have h1 : n / 256 / 256 = n / 65536 := by rw [Int.ediv_ediv_of_nonneg (by omega)]; rfl
  have h2 : n / 65536 / 256 = n / 16777216 := by rw [Int.ediv_ediv_of_nonneg (by omega)]; rfl
  have h3 : n / 16777216 / 256 = n / 4294967296 := by rw [Int.ediv_ediv_of_nonneg (by omega)]; rfl
  have h4 : addr + 1 ≠ addr := by omega
  have h5 : addr + 1 + 1 ≠ addr := by omega
  have h6 : addr + 1 + 1 + 1 ≠ addr := by omega
  simp [readInt, writeInt, reprInt, read_write_same, read_write_other, h4, h5, h6,
    show addr + 2 = addr + 1 + 1 by omega, show addr + 3 = addr + 1 + 1 + 1 by omega]
  split <;> omega

/-- Byte writes affect only the supplied range. Lines 531-561. -/
theorem read_outside_write (a b : Int) (bs : List Byte) (xs : Map Int Byte)
    (h : a < b ∨ b + bs.length ≤ a) :
    readByte a (writeInt b bs xs) = readByte a xs := by
  induction bs generalizing b with
  | nil => rfl
  | cons x bs ih =>
      simp only [writeInt]
      rw [read_write_other _ _ _ _ (by simp only [List.length_cons] at h; omega)]
      apply ih
      simp only [List.length_cons] at h
      omega

/-- Disjoint four-byte footprints preserve abstraction. Lines 350-355,1506-1517. -/
theorem disjoint_representation (a b : Int) (bs : List Byte) (xs : Map Int Byte)
    (len : bs.length = 4) (h : a + 4 ≤ b ∨ b + 4 ≤ a) :
    readInt a (writeInt b bs xs) = readInt a xs := by
  have hh (i : Int) (hi : 0 ≤ i ∧ i < 4) :
      readByte (a+i) (writeInt b bs xs) = readByte (a+i) xs :=
    read_outside_write _ _ _ _ (by rw [len]; omega)
  simp only [readInt]
  have h0 := hh 0 (by omega)
  simp only [Int.add_zero] at h0
  rw [h0]
  rw [hh 1 (by omega), hh 2 (by omega), hh 3 (by omega)]

/-- Descending allocation leaves its endpoint below the previous cursor. Lines 1069-1090. -/
theorem allocation_below_cursor (s : State) (align : Int) (h : 0 < align) :
    allocationBase s align + 4 ≤ s.lastAddress := by
  have := Int.emod_nonneg (s.lastAddress - 4) (by omega : align ≠ 0)
  simp only [allocationBase]
  omega

/-- Access checks depend on lifetime and allocation, independently of bytes. Lines 496-514. -/
theorem access_bytes (s : State) (ty : Ctype) (p : Pointer)
    (bs : Map Int Byte) (used : Option Int) :
    access {s with bytes := bs, lastUsed := used} ty p = access s ty p := by
  rfl

/-- A successful typed store followed by load at the same footprint returns its value. -/
theorem load_after_store (s s' : State) (ty : Ctype) (p : Pointer)
    (n : Int) (fp : Int × Int)
    (lo : -2147483648 ≤ n) (hi : n ≤ 2147483647)
    (written : store s ty p (some n) = .ok (fp, s')) :
    ∃ s'', load s' ty p = .ok (some n, s'') := by
  cases h : access s ty p with
  | error err => simp [store, h, Bind.bind, Except.bind] at written
  | ok pair =>
      rcases pair with ⟨id, addr⟩
      simp [store, h, lo, hi, Bind.bind, Except.bind] at written
      rcases written with ⟨rfl, rfl⟩
      simp only [load, access_bytes, h, Bind.bind, Except.bind, Pure.pure,
        representation_roundtrip addr n s.bytes lo hi]
      exact ⟨_, rfl⟩

/-- A successful store leaves the result of load on a disjoint object unchanged. -/
theorem store_disjoint (s s' : State) (ty otherTy : Ctype) (p q : Pointer)
    (n : Int) (fp : Int × Int) (id addr : Int)
    (lo : -2147483648 ≤ n) (hi : n ≤ 2147483647)
    (written : store s ty p (some n) = .ok (fp, s'))
    (other : access s otherTy q = .ok (id, addr))
    (disjoint : addr + 4 ≤ fp.1 ∨ fp.1 + 4 ≤ addr) :
    ∃ s'', load s' otherTy q = .ok (readInt addr s.bytes, s'') := by
  cases h : access s ty p with
  | error err => simp [store, h, Bind.bind, Except.bind] at written
  | ok pair =>
      rcases pair with ⟨pid, base⟩
      simp [store, h, lo, hi, Bind.bind, Except.bind] at written
      rcases written with ⟨rfl, rfl⟩
      simp only [load, access_bytes, other, Bind.bind, Except.bind, Pure.pure]
      rw [disjoint_representation addr base (reprInt n) s.bytes (by simp [reprInt]) disjoint]
      exact ⟨_, rfl⟩

/-- The allocation invariant places objects above the cursor. impl_mem.ml:1069-1090. -/
def AllocationInvariant (s : State) : Prop :=
  ∀ id a, s.allocations.lookup id = some a → s.lastAddress ≤ a.base

/-- Allocation preserves the invariant and its footprint overlaps no existing object. -/
theorem allocations_do_not_overlap (s s' : State) (align : Int) (ty : Ctype)
    (p : Pointer) (positive : 0 < align) (inv : AllocationInvariant s)
    (allocated : allocate s align ty = .ok (p, s')) :
    AllocationInvariant s' ∧ ∀ id a, s.allocations.lookup id = some a → s'.lastAddress + 4 ≤ a.base := by
  have below := allocation_below_cursor s align positive
  unfold allocate at allocated
  cases h : layout ty with
  | error err => simp [h, Bind.bind, Except.bind] at allocated
  | ok size =>
      simp [h, show ¬align ≤ 0 by omega, Bind.bind, Except.bind] at allocated
      split at allocated
      · simp at allocated
      · rcases allocated with ⟨rfl, rfl⟩
        constructor
        · intro id a member
          by_cases equal : id = s.nextId
          · subst id
            simp only [Map.lookup_insert] at member
            cases member
            exact Int.le_refl _
          · rw [Map.lookup_insert_of_key_ne (x := s.nextId) (x' := id) {base := allocationBase s align} s.allocations equal] at member
            have old := inv id a member
            dsimp
            omega
        · intro id a member
          have old := inv id a member
          dsimp
          omega

/-- The initial empty allocation table satisfies the invariant. Lines 326-344. -/
theorem initial_allocation_invariant : AllocationInvariant {} := by
  simp [AllocationInvariant, Map.lookup]

end Silmaril.Cerberus.Mem.Concrete
