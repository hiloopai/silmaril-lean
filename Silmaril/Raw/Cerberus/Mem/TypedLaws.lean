module

public import Silmaril.Cerberus.Mem.Typed.Defs
public import Silmaril.Cerberus.Mem.ConcreteLaws.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity

/-! Laws for typed byte footprints at the pinned concrete model. -/

@[expose] public section
namespace Silmaril.Cerberus.Mem.Concrete

/-- Every integer byte occupies one address. impl_mem.ml:918-936. -/
theorem encodeInteger_length (w : Nat) (n : Int) : (encodeInteger w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [encodeInteger, ih]

/-- Representation writes the same byte values as the base byte-map operation. -/
theorem writeRepresentation_bytes (a : Int) (bs : Representation) (s : State) :
    (writeRepresentation a bs s).bytes = writeInt a (bs.map Prod.fst) s.bytes := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => simp [writeRepresentation, writeInt, ih]

/-- Pointer-copy writes preserve allocation and lifetime checks. -/
theorem writeRepresentation_allocations (a : Int) (bs : Representation) (s : State) :
    (writeRepresentation a bs s).allocations = s.allocations ∧
    (writeRepresentation a bs s).dead = s.dead ∧
    (writeRepresentation a bs s).functions = s.functions := by
  induction bs generalizing a with
  | nil => simp [writeRepresentation]
  | cons b bs ih => simpa [writeRepresentation] using ih (a+1)

/-- Fetch after a byte write recovers every supplied byte. -/
theorem fetch_write (a : Int) (bs : List Byte) (xs : Map Int Byte) :
    fetchBytes bs.length a (writeInt a bs xs) = bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.length_cons, fetchBytes, writeInt, read_write_same]
      congr 1
      have hh : fetchBytes bs.length (a+1) (writeByte a b (writeInt (a+1) bs xs)) =
          fetchBytes bs.length (a+1) (writeInt (a+1) bs xs) := by
        generalize writeInt (a+1) bs xs = ys
        have aux (w : Nat) (base : Int) (h : a < base) :
            fetchBytes w base (writeByte a b ys) = fetchBytes w base ys := by
          induction w generalizing base with
          | zero => rfl
          | succ w ih =>
              simp only [fetchBytes]
              rw [read_write_other base a b ys (by omega), ih (base+1) (by omega)]
        exact aux _ _ (by omega)
      rw [hh, ih]

/-- Fetches on a disjoint range are unchanged for every representation width. -/
theorem fetch_disjoint (w : Nat) (a b : Int) (bs : List Byte) (xs : Map Int Byte)
    (h : a + w ≤ b ∨ b + bs.length ≤ a) :
    fetchBytes w a (writeInt b bs xs) = fetchBytes w a xs := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
      simp only [fetchBytes]
      rw [read_outside_write _ _ _ _ (by omega), ih (a+1) (by omega)]

/-- Unsigned abstraction of an integer representation is reduction modulo its width. -/
theorem decode_encode (w : Nat) (n : Int) :
    decodeInteger (encodeInteger w n) = some (n % (256 ^ w)) := by
  induction w generalizing n with
  | zero => simp [encodeInteger, decodeInteger]
  | succ w ih =>
      simp only [encodeInteger, decodeInteger, ih, bind, Option.bind, pure, Pure.pure]
      congr 1
      have pos : (0 : Int) < 256 ^ w := by positivity
      have div := Int.ediv_ediv_of_nonneg (x := n) (y := 256) (z := 256 ^ w) (by omega)
      have e1 := Int.emod_add_mul_ediv n 256
      have e2 := Int.emod_add_mul_ediv (n / 256) (256 ^ w)
      have e3 := Int.emod_add_mul_ediv n (256 ^ (w+1))
      rw [pow_succ] at e3 ⊢
      rw [div, Int.mul_comm 256 (256 ^ w)] at e2
      have eq : n % 256 + 256 * (n / 256 % 256 ^ w) = n % (256 ^ w * 256) := by
        linear_combination e1 + 256 * e2 - e3
      exact eq

/-- Every binary64 encoding, including all NaN payloads, survives eight bytes. -/
theorem floating_representation_roundtrip (x : Numeric.Ieee754.F64) :
    decodeFloating (encodeFloating x) = some x := by
  have bound := x.bits.toNat_lt_size
  have eq : ((x.bits.toNat : Int) % 256 ^ 8) = x.bits.toNat :=
    Int.emod_eq_of_lt (by omega) (by norm_num; exact_mod_cast bound)
  simp only [decodeFloating, encodeFloating, decode_encode, eq, Option.map_some,
    Int.toNat_natCast, UInt64.ofNat_toNat]

/-- Floating representations have the pinned size for every real C type. -/
theorem encodeFloating_length (x : Numeric.Ieee754.F64) :
    (encodeFloating x).length = 8 := encodeInteger_length 8 x.bits.toNat

/-- Fetching a stored binary64 representation recovers all its bits. -/
theorem floating_written_roundtrip (x : Numeric.Ieee754.F64) (addr : Int)
    (xs : Map Int Byte) :
    decodeFloating (fetchBytes 8 addr (writeInt addr (encodeFloating x) xs)) = some x := by
  have fetch := fetch_write addr (encodeFloating x) xs
  rw [encodeFloating_length] at fetch
  rw [fetch, floating_representation_roundtrip]

/-- Signed abstraction selects the sign bit at every enabled scalar width. -/
theorem integer_representation_roundtrip (w : Nat) (signed : Bool) (n a : Int)
    (xs : Map Int Byte) (width : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (range : if signed then -(256 ^ w : Int) / 2 ≤ n ∧ n < (256 ^ w : Int) / 2
      else 0 ≤ n ∧ n < (256 ^ w : Int)) :
    (decodeInteger (fetchBytes w a (writeInt a (encodeInteger w n) xs))).map
      (fun v => if signed && v ≥ (256 ^ w : Int) / 2 then v - 256 ^ w else v) = some n := by
  have fetch := fetch_write a (encodeInteger w n) xs
  rw [encodeInteger_length] at fetch
  rw [fetch, decode_encode]
  cases signed <;> rcases width with rfl | rfl | rfl | rfl <;>
    norm_num at range ⊢ <;> (try split) <;>
    by_cases hn : 0 ≤ n <;> omega

/-- Any typed representation preserves all fetched bytes outside its footprint. -/
theorem typed_write_disjoint (w : Nat) (a b : Int) (bs : Representation) (s : State)
    (h : a + w ≤ b ∨ b + bs.length ≤ a) :
    fetchBytes w a (writeRepresentation b bs s).bytes = fetchBytes w a s.bytes := by
  rw [writeRepresentation_bytes]
  apply fetch_disjoint
  simpa using h

/-- A successful typed access identifies a subobject contained in its allocation. -/
theorem typed_access_footprint (tags : Tags) (s : State) (ty : Ctype)
    (id addr size : Int)
    (h : accessTyped tags s ty (.allocated id addr) = .ok (id, addr, size)) :
    ∃ a, s.allocations.lookup id = some a ∧ a.base ≤ addr ∧ addr+size ≤ a.base+a.size := by
  unfold accessTyped at h
  cases hl : typeLayout 64 tags ty with
  | error e => simp [hl, Bind.bind, Except.bind] at h
  | ok l =>
      simp only [hl, Bind.bind, Except.bind] at h
      split at h
      · simp at h
      · cases ha : s.allocations.lookup id with
        | none => simp [ha] at h
        | some a =>
            simp only [ha] at h
            split at h
            · have bounds := ‹a.base ≤ addr ∧ addr + l.size ≤ a.base + a.size›
              cases hw : checkAtomic a ty addr l.size with
              | error e => simp [hw] at h
              | ok result =>
                  simp only [hw] at h
                  have eq : size = l.size := by simpa using (congrArg (fun x : Int × Int × Int => x.2.2) (Except.ok.inj h)).symm
                  exact ⟨a, rfl, bounds.1, by simpa [eq] using bounds.2⟩
            · simp at h

/-- Byte and copy-offset changes cannot alter lifetime or bounds. -/
theorem typed_access_write (tags : Tags) (s : State) (ty : Ctype) (p : Pointer)
    (a : Int) (bs : Representation) (used : Option Int) :
    accessTyped tags {(writeRepresentation a bs s) with lastUsed := used} ty p =
      accessTyped tags s ty p := by
  have h := writeRepresentation_allocations a bs s
  simp only [accessTyped, h.1, h.2.1]

/-- Typed load after store covers all enabled integer widths, over arbitrary
prior memory and allocation provenance. impl_mem.ml:768-783,962-973,1375-1610. -/
theorem typed_integer_load_after_store (tags : Tags) (s s' : State)
    (ity : IntegerType) (ann : List Annot) (p : Pointer)
    (n : Int) (w : Nat) (signed : Bool) (fp : Int × Int)
    (support : registeredIntegerLayout tags ity = some (w, signed))
    (width : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (range : if signed then -(256 ^ w : Int) / 2 ≤ n ∧ n < (256 ^ w : Int) / 2
      else 0 ≤ n ∧ n < (256 ^ w : Int))
    (written : storeTyped tags s (.mk ann (.basic (.integer ity))) p (.integer ity n) =
      .ok (fp, s')) :
    ∃ s'', loadTyped tags s' (.mk ann (.basic (.integer ity))) p =
      .ok (.integer ity n, s'') := by
  have fits : (representationBounds w signed).1 ≤ n ∧ n ≤ (representationBounds w signed).2 := by
    cases signed <;> simp [representationBounds] at range ⊢ <;> omega
  have hr : represent 64 tags (.integer ity n) s =
      .ok (plainBytes (encodeInteger w n), s) := by
    simp [represent, support, fits, Pure.pure, Except.pure]
  cases h : accessTyped tags s (.mk ann (.basic (.integer ity))) p with
  | error e => simp [storeTyped, h, Bind.bind, Except.bind] at written
  | ok pair =>
      rcases pair with ⟨id, addr, size⟩
      cases hw : checkWritable s id with
      | error e => simp [storeTyped, h, hw, Bind.bind, Except.bind] at written
      | ok result =>
          simp only [storeTyped, h, hw, hr, Bind.bind, Except.bind, Pure.pure] at written
          split at written
          · simp at written
          · have written' := Except.ok.inj written
            cases written'
            have fetch := fetch_write addr (encodeInteger w n) s.bytes
            rw [encodeInteger_length] at fetch
            have rt := integer_representation_roundtrip w signed n addr s.bytes width range
            rw [fetch, decode_encode] at rt
            simp only [Option.map_some, Option.some.injEq] at rt
            simp only [loadTyped, typed_access_write, h, Bind.bind, Except.bind]
            simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at rt
            simp [abstractValue, typeLayout, support, Bind.bind, Except.bind, Pure.pure, Except.pure,
              writeRepresentation_bytes, plainBytes, Function.comp_def, fetch, decode_encode, rt]


end Silmaril.Cerberus.Mem.Concrete
