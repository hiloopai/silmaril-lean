module

public import Silmaril.Cerberus.Mem.TypedLaws.Defs

/-! # `int` objects in the concrete memory

The typed operations of `Mem.Typed` on a whole `int` object (a C local `int`), for every
annotation of the type and every tag environment: allocation (`allocate_int`), access, store,
load and kill of a live, writable, non-atomic 4-byte object. These are the memory steps of a
compiled `int` local: the Core `create`, `store`, `load` and `kill` of the object answer with
these states.
-/

@[expose] public section

namespace Silmaril.Cerberus.Mem.Concrete

/-- `int`, with any annotations. -/
def intType (ann : List Annot) : Ctype := .mk ann (.basic (.integer (.signed .int)))

theorem layout_intType (tags : Tags) (ann : List Annot) :
    typeLayout 64 tags (intType ann) = .ok ⟨4, 4, []⟩ := by
  simp [typeLayout, intType, registeredIntegerLayout, registeredInteger, integerLayout, baseWidth]
  rfl

/-- The address of the next allocation of a 4-byte, 4-aligned object. -/
def nextIntAddress (s : State) : Int := (s.lastAddress - 4) - (s.lastAddress - 4) % 4

/-- Writing a representation changes only the byte maps. -/
theorem writeRepresentation_shape (a : Int) (bs : Representation) (s : State) :
    ∃ b pb, writeRepresentation a bs s = {s with bytes := b, pointerBytes := pb} := by
  induction bs generalizing a with
  | nil => exact ⟨s.bytes, s.pointerBytes, rfl⟩
  | cons x bs ih =>
    obtain ⟨b, pb, h⟩ := ih (a + 1)
    rcases x with ⟨y, prov⟩
    simp only [writeRepresentation, h]
    exact ⟨_, _, rfl⟩

/-- A fresh `int` object is allocated below every earlier one, with unspecified bytes. -/
theorem allocate_int (tags : Tags) (ann : List Annot) (s : State) (hpos : 0 < nextIntAddress s) :
    allocateTyped tags s 4 (intType ann) = .ok (.allocated s.nextId (nextIntAddress s),
      { writeRepresentation (nextIntAddress s) (plainBytes (List.replicate 4 none)) s with
        nextId := s.nextId + 1
        lastAddress := nextIntAddress s
        allocations := s.allocations.insert s.nextId
          ({base := nextIntAddress s, size := 4, objectType := some (intType ann)} : Allocation)
        lastUsed := some s.nextId }) := by
  unfold nextIntAddress at hpos ⊢
  have halloc := writeRepresentation_allocations (s.lastAddress - 4 - (s.lastAddress - 4) % 4)
    (plainBytes (List.replicate 4 none)) s
  have hn : ¬ (s.lastAddress - 4 - (s.lastAddress - 4) % 4 ≤ 0) := by omega
  simp only [allocateTyped, layout_intType, bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right_of_eq_false _ _ (by simp), ite_eq_right_of_eq_false _ _ (by simpa using hn)]
  rw [show (4 : Int).toNat = 4 from rfl]
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape (s.lastAddress - 4 - (s.lastAddress - 4) % 4)
    (plainBytes (List.replicate 4 none)) s
  simp only [h]
  simp [intType]

/-- A live, non-atomic, 4-byte object at `addr`. -/
structure LiveInt (s : State) (id addr : Int) : Prop where
  alive : id ∉ s.dead
  found : ∃ a, s.allocations.lookup id = some a ∧ a.base = addr ∧ a.size = 4 ∧ a.atomic = false ∧
    a.readonly = none

theorem access_int (tags : Tags) (ann : List Annot) {s : State} {id addr : Int}
    (h : LiveInt s id addr) :
    accessTyped tags s (intType ann) (.allocated id addr) = .ok (id, addr, 4) := by
  obtain ⟨alive, a, look, base, size, atomic, _⟩ := h
  simp [accessTyped, layout_intType, alive, look, base, size, checkAtomic, atomic, bind,
    Except.bind, pure, Except.pure]

/-- An `int` value is representable in its 4 bytes. -/
def IntRange (n : Int) : Prop := -2147483648 ≤ n ∧ n ≤ 2147483647

theorem store_int (tags : Tags) (ann : List Annot) {s : State} {id addr : Int}
    (h : LiveInt s id addr) {n : Int} (hn : IntRange n) :
    storeTyped tags s (intType ann) (.allocated id addr) (.integer (.signed .int) n) =
      .ok ((addr, 4), {writeRepresentation addr (plainBytes (encodeInteger 4 n)) s with
        lastUsed := some id}) := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := h
  obtain ⟨lo, hi⟩ := hn
  have hr : represent 64 tags (.integer (.signed .int) n) s =
      .ok (plainBytes (encodeInteger 4 n), s) := by
    simp [represent, registeredIntegerLayout, registeredInteger, integerLayout, baseWidth,
      representationBounds, lo, hi, pure, Except.pure]
  simp [storeTyped, access_int tags ann ⟨alive, a, look, base, size, atomic, ro⟩, checkWritable,
    look, ro, hr, bind, Except.bind, pure, Except.pure, plainBytes, encodeInteger_length]

theorem kill_int (tags : Tags) (ann : List Annot) {s : State} {id addr : Int}
    (h : LiveInt s id addr) :
    killTyped tags s (intType ann) (.allocated id addr) =
      .ok ((), { s with
        allocations := s.allocations.erase id
        dead := id :: s.dead
        lastUsed := some id }) := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := h
  simp [killTyped, access_int tags ann ⟨alive, a, look, base, size, atomic, ro⟩, look, base,
    bind, Except.bind, pure, Except.pure]

/-- No pointer-copy metadata on the object's bytes, so reading it exposes nothing. -/
def PlainAt (s : State) (addr : Int) : Prop :=
  ∀ i : Nat, i < 4 → s.pointerBytes.lookup (addr + i) = none

theorem load_int (tags : Tags) (ann : List Annot) {s : State} {id addr : Int}
    (h : LiveInt s id addr) (plain : PlainAt s addr) {n : Int} (hn : IntRange n)
    (bytes : fetchBytes 4 addr s.bytes = encodeInteger 4 n) :
    loadTyped tags s (intType ann) (.allocated id addr) =
      .ok (.integer (.signed .int) n, {s with lastUsed := some id}) := by
  have hdec : decodeInteger (fetchBytes 4 addr s.bytes) = some (n % 4294967296) := by
    rw [bytes]
    have := decode_encode 4 n
    simpa using this
  obtain ⟨lo, hi⟩ := hn
  have p0 : s.pointerBytes.lookup addr = none := by simpa using plain 0 (by omega)
  have p1 : s.pointerBytes.lookup (addr + 1) = none := by simpa using plain 1 (by omega)
  have p2 : s.pointerBytes.lookup (addr + 2) = none := by simpa using plain 2 (by omega)
  have p3 : s.pointerBytes.lookup (addr + 3) = none := by simpa using plain 3 (by omega)
  have hexp : exposeRead 64 tags s (intType ann) addr = s := by
    simp [exposeRead, intType, registeredIntegerLayout, registeredInteger, integerLayout, baseWidth,
      exposeReadBytes, List.range, List.range.loop, p0, p1, p2, p3]
  have habs : abstractValue 64 tags s (intType ann) addr = .ok (.integer (.signed .int) n) := by
    have hl := layout_intType tags ann
    unfold intType at hl ⊢
    simp only [abstractValue, hl, bind, Except.bind, pure, Except.pure, registeredIntegerLayout,
      registeredInteger, integerLayout, baseWidth, Option.bind, Option.map]
    simp only [show ((4 : Int).toNat) = 4 from rfl, hdec]
    congr 2
    norm_num
    split <;> omega
  unfold loadTyped
  rw [access_int tags ann h]
  simp only [bind, Except.bind, habs, hexp, pure, Except.pure]

end Silmaril.Cerberus.Mem.Concrete
