module

public import Silmaril.Compiler.Core.Source.StartupArgs.Defs
public import Silmaril.Cerberus.Mem.IntSlots.Defs

/-! # The concrete memory after the startup of `main(argc, argv)`

Byte-level facts about the concrete memory model (`Mem.Concrete`) used by the startup objects:
lookups in updated maps, `writeRepresentation`, and the representations of `char` arrays,
`char *` arrays, `int` and pointers.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.StartupArgs

open Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete (Tags Pointer MemoryValue Failure Byte Representation typeLayout allocateTyped
  storeTyped accessTyped loadTyped updateLastAllocation readonlyKind unatomic writeRepresentation
  plainBytes encodeInteger decodeInteger represent readByte fetchBytes registeredIntegerLayout
  registeredInteger integerLayout representationBounds encodeAddress representPointer)

/-! ## Maps with integer keys -/

theorem lookup_insert_int {v : Type} (m : Map Int v) (x y : Int) (a : v) :
    (m.insert x a).lookup y = if y = x then some a else m.lookup y := by
  by_cases h : y = x
  · subst h; simp
  · simp only [h, ↓reduceIte]
    exact Map.lookup_insert_of_key_ne _ _ (by simpa [MapKey.key] using h)

theorem lookup_erase_int {v : Type} (m : Map Int v) (x y : Int) :
    (m.erase x).lookup y = if y = x then none else m.lookup y := by
  by_cases h : y = x
  · subst h; simp [Map.lookup, Map.erase]
  · simp only [h, ↓reduceIte, Map.lookup, Map.erase]
    exact Finmap.lookup_erase_ne (by simpa [MapKey.key] using h)

/-! ## Writing representations -/

/-- Bytes outside the written range keep their value and copy metadata. -/
theorem writeRepresentation_out (a : Int) (bs : Representation) (s : Mem.Concrete.State) (x : Int)
    (hx : x < a ∨ a + bs.length ≤ x) :
    (writeRepresentation a bs s).bytes.lookup x = s.bytes.lookup x ∧
      (writeRepresentation a bs s).pointerBytes.lookup x = s.pointerBytes.lookup x := by
  induction bs generalizing a with
  | nil => simp [writeRepresentation]
  | cons b bs ih =>
    obtain ⟨y, prov⟩ := b
    have hne : x ≠ a := by simp at hx; omega
    obtain ⟨h1, h2⟩ := ih (a + 1) (by simp at hx ⊢; omega)
    simp only [writeRepresentation, Mem.Concrete.writeByte]
    refine ⟨by simp only [lookup_insert_int, hne, ↓reduceIte, h1], ?_⟩
    cases prov <;> simp only [lookup_insert_int, lookup_erase_int, hne, ↓reduceIte, h2]

/-- Byte `j` of the written range is entry `j` of the representation. -/
theorem writeRepresentation_in (a : Int) (bs : Representation) (s : Mem.Concrete.State) (j : Nat)
    (hj : j < bs.length) :
    (writeRepresentation a bs s).bytes.lookup (a + j) = some bs[j].1 ∧
      (writeRepresentation a bs s).pointerBytes.lookup (a + j) = bs[j].2 := by
  induction bs generalizing a j with
  | nil => simp at hj
  | cons b bs ih =>
    obtain ⟨y, prov⟩ := b
    cases j with
    | zero =>
      simp only [writeRepresentation, Mem.Concrete.writeByte, Nat.cast_zero, Int.add_zero]
      refine ⟨by simp, ?_⟩
      cases prov <;> simp [lookup_erase_int]
    | succ j =>
      have hne : a + ((j + 1 : Nat) : Int) ≠ a := by omega
      obtain ⟨h1, h2⟩ := ih (a + 1) j (by simp at hj; omega)
      rw [show a + 1 + (j : Int) = a + ((j + 1 : Nat) : Int) by omega] at h1 h2
      simp only [writeRepresentation, Mem.Concrete.writeByte]
      refine ⟨by simp only [lookup_insert_int, hne, ↓reduceIte, h1]; rfl, ?_⟩
      cases prov <;> simp only [lookup_insert_int, lookup_erase_int, hne, ↓reduceIte, h2] <;> rfl

/-- `writeRepresentation` changes only the byte maps. -/
theorem writeRepresentation_fields (a : Int) (bs : Representation) (s : Mem.Concrete.State) :
    (writeRepresentation a bs s).allocations = s.allocations ∧
    (writeRepresentation a bs s).nextId = s.nextId ∧
    (writeRepresentation a bs s).lastAddress = s.lastAddress ∧
    (writeRepresentation a bs s).dead = s.dead ∧
    (writeRepresentation a bs s).enumTypes = s.enumTypes ∧
    (writeRepresentation a bs s).stdout = s.stdout := by
  obtain ⟨b, pb, h⟩ := StartupReach.writeRepresentation_shape a bs s
  simp [h]

/-- Allocation metadata updates do not write output. -/
theorem updateLastAllocation_stdout (m : Mem.Concrete.State) (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (updateLastAllocation m f).stdout = m.stdout := by
  unfold updateLastAllocation
  split
  · rfl
  · split <;> rfl

/-! ## Representations of the startup values -/

theorem layout_char (tags : Tags) : registeredIntegerLayout tags .char = some (1, true) := by
  simp [registeredIntegerLayout, registeredInteger, integerLayout]

theorem layout_signedInt (tags : Tags) : registeredIntegerLayout tags (.signed .int) = some (4, true) := by
  simp [registeredIntegerLayout, registeredInteger, integerLayout, Mem.Concrete.baseWidth]

theorem represent_char (fuel : Nat) (tags : Tags) (s : Mem.Concrete.State) {c : Int}
    (h0 : 0 ≤ c) (h1 : c ≤ 127) :
    represent (fuel + 1) tags (.integer .char c) s = .ok (plainBytes [some c], s) := by
  simp only [represent, layout_char, representationBounds, pure, Except.pure]
  simp [show (-128 : Int) ≤ c by omega, h1, encodeInteger, Int.emod_eq_of_lt (b := 256) h0 (by omega)]

theorem represent_signedInt (fuel : Nat) (tags : Tags) (s : Mem.Concrete.State) {n : Int}
    (h0 : -2147483648 ≤ n) (h1 : n ≤ 2147483647) :
    represent (fuel + 1) tags (.integer (.signed .int) n) s = .ok (plainBytes (encodeInteger 4 n), s) := by
  simp only [represent, layout_signedInt, representationBounds, pure, Except.pure]
  simp [h0, h1]

/-- The representation of a pointer with allocation provenance: its address, each byte tagged
with the allocation and the byte's index. -/
def provBytes (id a : Int) : Representation :=
  (encodeInteger 8 a).zipIdx.map fun (b, i) => (b, some (some id, i))

theorem represent_allocated (fuel : Nat) (tags : Tags) (s : Mem.Concrete.State) (ty : Ctype)
    {id a : Int} (h0 : 0 ≤ a) (h1 : a < 18446744073709551616) :
    represent (fuel + 1) tags (.pointer ty (.allocated id a)) s = .ok (provBytes id a, s) := by
  simp [represent, representPointer, encodeAddress, h0, h1, provBytes, bind, Except.bind, pure,
    Except.pure]

theorem represent_null (fuel : Nat) (tags : Tags) (s : Mem.Concrete.State) (ty ty' : Ctype) :
    represent (fuel + 1) tags (.pointer ty (.null ty')) s = .ok (plainBytes (encodeInteger 8 0), s) := by
  simp [represent, representPointer, pure, Except.pure]

theorem foldlM_append {α : Type} (s : Mem.Concrete.State)
    (f : Representation × Mem.Concrete.State → α → Except Failure (Representation × Mem.Concrete.State))
    (r : α → Representation) :
    ∀ (xs : List α) (acc : Representation), (∀ x ∈ xs, ∀ acc, f (acc, s) x = .ok (acc ++ r x, s)) →
      xs.foldlM f (acc, s) = .ok (acc ++ xs.flatMap r, s)
  | [], acc, _ => by simp [pure, Except.pure]
  | x :: xs, acc, h => by
    rw [List.foldlM_cons, h x (by simp) acc]
    show List.foldlM f (acc ++ r x, s) xs = _
    rw [foldlM_append s f r xs (acc ++ r x) fun y hy => h y (by simp [hy])]
    simp

/-- An array whose elements are represented independently of the state. -/
theorem represent_array (fuel : Nat) (tags : Tags) (s : Mem.Concrete.State)
    (r : MemoryValue → Representation) (xs : List MemoryValue)
    (h : ∀ x ∈ xs, represent fuel tags x s = .ok (r x, s)) :
    represent (fuel + 1) tags (.array xs) s = .ok (xs.flatMap r, s) := by
  simp only [represent]
  rw [foldlM_append s _ r xs [] fun x hx acc => by simp [h x hx, bind, Except.bind, pure, Except.pure]]
  simp

/-! ## Creating one object -/

/-- The memory only grows downwards: allocations below the old frontier and fresh identifiers;
everything at or above the old frontier and every older allocation is unchanged. -/
structure Grows (m m' : Mem.Concrete.State) : Prop where
  last : m'.lastAddress ≤ m.lastAddress
  next : m.nextId ≤ m'.nextId
  dead : m'.dead = m.dead
  enums : m'.enumTypes = m.enumTypes
  stdout : m'.stdout = m.stdout
  allocs : ∀ id < m.nextId, m'.allocations.lookup id = m.allocations.lookup id
  bytes : ∀ x, m.lastAddress ≤ x →
    m'.bytes.lookup x = m.bytes.lookup x ∧ m'.pointerBytes.lookup x = m.pointerBytes.lookup x

theorem Grows.refl (m : Mem.Concrete.State) : Grows m m :=
  ⟨le_rfl, le_rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem Grows.trans {m1 m2 m3 : Mem.Concrete.State} (h12 : Grows m1 m2) (h23 : Grows m2 m3) :
    Grows m1 m3 where
  last := h23.last.trans h12.last
  next := h12.next.trans h23.next
  dead := h23.dead.trans h12.dead
  enums := h23.enums.trans h12.enums
  stdout := h23.stdout.trans h12.stdout
  allocs id hid := (h23.allocs id (lt_of_lt_of_le hid h12.next)).trans (h12.allocs id hid)
  bytes x hx := by
    obtain ⟨a, b⟩ := h23.bytes x (h12.last.trans hx)
    obtain ⟨c, d⟩ := h12.bytes x hx
    exact ⟨a.trans c, b.trans d⟩

/-- Where the next allocation of `size` bytes aligned to `align` goes. -/
def nextBase (m : Mem.Concrete.State) (size align : Int) : Int :=
  (m.lastAddress - size) - (m.lastAddress - size) % align

/-- The allocation record of a startup object. -/
def allocRecord (a size : Int) (ty : Ctype) (pref : Prefix) : Mem.Concrete.Allocation :=
  {base := a, size := size, objectType := some ty, readonlyKind := readonlyKind pref}

/-- **One startup object.** Under the side conditions (layout, alignment, room, a fresh
identifier, a state-independent representation of the right size), `createStore` allocates at
`nextBase`, records the allocation, and writes the representation there. -/
theorem createStore_spec (tags : Tags) (m : Mem.Concrete.State) (obj : Startup.Object) (v : MemoryValue)
    {l : Mem.Concrete.TypeLayout} (hl : typeLayout 64 tags obj.type = .ok l)
    (hna : ∀ q t, obj.type ≠ .mk q (.atomic t))
    (halign : 0 < l.align) (hsize : 0 ≤ l.size) (hpos : 0 < nextBase m l.size l.align)
    (hdead : m.nextId ∉ m.dead)
    {n : MemoryValue} (hn : toMemory (unatomic obj.type) (fromMemory v) = .ok n)
    {bs : Representation} (hrep : ∀ s, represent 64 tags n s = .ok (bs, s))
    (hlen : bs.length = l.size.toNat) :
    ∃ m', createStore tags m obj v = .ok (.allocated m.nextId (nextBase m l.size l.align), m') ∧
      Grows m m' ∧ m'.nextId = m.nextId + 1 ∧ m'.lastAddress = nextBase m l.size l.align ∧
      m'.allocations.lookup m.nextId =
        some (allocRecord (nextBase m l.size l.align) l.size obj.type obj.allocationPrefix) ∧
      ∀ (j : Nat) (hj : j < bs.length), m'.bytes.lookup (nextBase m l.size l.align + j) = some (bs[j]'hj).1 ∧
        m'.pointerBytes.lookup (nextBase m l.size l.align + j) = (bs[j]'hj).2 := by
  set a := nextBase m l.size l.align with ha
  have hz : a + l.size ≤ m.lastAddress := by
    have : 0 ≤ (m.lastAddress - l.size) % l.align := Int.emod_nonneg _ (by omega)
    simp only [ha, nextBase]; omega
  let w0 := writeRepresentation a (plainBytes (List.replicate l.size.toNat none)) m
  obtain ⟨fa, fn, fl, fd, fe, -⟩ := writeRepresentation_fields a
    (plainBytes (List.replicate l.size.toNat none)) m
  let rec0 : Mem.Concrete.Allocation := {base := a, size := l.size, objectType := some obj.type}
  let m1 : Mem.Concrete.State := {w0 with
    nextId := m.nextId + 1, lastAddress := a,
    allocations := m.allocations.insert m.nextId rec0, lastUsed := some m.nextId}
  have halloc : allocateTyped tags m l.align obj.type = .ok (.allocated m.nextId a, m1) := by
    simp only [allocateTyped, hl, bind, Except.bind, pure, Except.pure]
    simp only [show ¬ l.align ≤ 0 by omega, ↓reduceIte,
      show m.lastAddress - l.size - (m.lastAddress - l.size) % l.align = a from rfl,
      show ¬ a ≤ 0 by omega]
    simp only [fn, fa, m1, w0, rec0]
  let m1' := updateLastAllocation m1 fun r => {r with readonlyKind := readonlyKind obj.allocationPrefix}
  have hrec : m1'.allocations.lookup m.nextId =
      some (allocRecord a l.size obj.type obj.allocationPrefix) := by
    simp [m1', m1, updateLastAllocation, rec0, allocRecord]
  have hlook1 : ∀ id, id ≠ m.nextId → m1'.allocations.lookup id = m.allocations.lookup id := by
    intro id hid
    simp [m1', m1, updateLastAllocation, rec0, lookup_insert_int, hid]
  have hbytes1 : m1'.bytes = w0.bytes ∧ m1'.pointerBytes = w0.pointerBytes ∧ m1'.dead = m.dead ∧
      m1'.nextId = m.nextId + 1 ∧ m1'.lastAddress = a ∧ m1'.enumTypes = m.enumTypes := by
    simp [m1', m1, updateLastAllocation, rec0, w0, fd, fe]
  obtain ⟨hb1, hpb1, hd1, hn1, hl1, he1⟩ := hbytes1
  have hacc : accessTyped tags m1' obj.type (.allocated m.nextId a) = .ok (m.nextId, a, l.size) := by
    simp [accessTyped, hl, hd1, hdead, hrec, allocRecord, Mem.Concrete.checkAtomic, bind, Except.bind,
      pure, Except.pure]
  let m2 : Mem.Concrete.State := {writeRepresentation a bs m1' with lastUsed := some m.nextId}
  have hstore : storeTyped tags m1' obj.type (.allocated m.nextId a) n = .ok ((a, l.size), m2) := by
    simp [storeTyped, hacc, Mem.Concrete.checkWritable, hrec, allocRecord, hrep, hlen, bind,
      Except.bind, pure, Except.pure, m2]
  have hcs : createStore tags m obj v = .ok (.allocated m.nextId a, m2) := by
    have hstore' : storeTyped tags (updateLastAllocation m1 fun r =>
        {r with readonlyKind := readonlyKind obj.allocationPrefix}) obj.type (.allocated m.nextId a) n =
        .ok ((a, l.size), m2) := hstore
    simp only [createStore, hl, halloc, hn, bind, Except.bind, pure, Except.pure, hstore']
  obtain ⟨fa2, fn2, fl2, fd2, fe2, -⟩ := writeRepresentation_fields a bs m1'
  refine ⟨m2, hcs, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [m2, fl2, hl1]; omega
  · simp only [m2, fn2, hn1]; omega
  · simp only [m2, fd2, hd1]
  · simp only [m2, fe2, he1]
  · change (writeRepresentation a bs m1').stdout = m.stdout
    rw [(writeRepresentation_fields a bs m1').2.2.2.2.2]
    change (updateLastAllocation m1 _).stdout = m.stdout
    rw [updateLastAllocation_stdout]
    change w0.stdout = m.stdout
    exact (writeRepresentation_fields a (plainBytes (List.replicate l.size.toNat none)) m).2.2.2.2.2
  · intro id hid
    simp only [m2, fa2]
    exact hlook1 id (by omega)
  · intro x hx
    obtain ⟨o1, o2⟩ := writeRepresentation_out a bs m1' x (Or.inr (by rw [hlen]; omega))
    obtain ⟨o3, o4⟩ := writeRepresentation_out a (plainBytes (List.replicate l.size.toNat none)) m x
      (Or.inr (by simp [plainBytes]; omega))
    simp only [m2]
    exact ⟨o1.trans (hb1 ▸ o3), o2.trans (hpb1 ▸ o4)⟩
  · simp only [m2, fn2, hn1]
  · simp only [m2, fl2, hl1]
  · simp only [m2, fa2, hrec]
  · intro j hj
    exact writeRepresentation_in a bs m1' j hj

/-! ## Reading back -/

theorem decodeInteger_encodeInteger_nat (n k : Nat) :
    decodeInteger (encodeInteger n (k : Int)) = some ((k % 256 ^ n : Nat) : Int) := by
  induction n generalizing k with
  | zero => simp [encodeInteger, decodeInteger, Nat.mod_one]
  | succ n ih =>
    have h1 : (k : Int) % 256 = ((k % 256 : Nat) : Int) := by omega
    have h2 : (k : Int) / 256 = ((k / 256 : Nat) : Int) := by omega
    simp only [encodeInteger, decodeInteger, h1, h2, ih, bind, Option.bind, pure]
    simp only [Option.some.injEq]
    rw [pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    push_cast; ring

theorem decodeInteger_encodeInteger (n : Nat) (v : Int) (h0 : 0 ≤ v) (h1 : v < 256 ^ n) :
    decodeInteger (encodeInteger n v) = some v := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [decodeInteger_encodeInteger_nat, Nat.mod_eq_of_lt (by exact_mod_cast h1)]

theorem length_encodeInteger (n : Nat) (v : Int) : (encodeInteger n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [encodeInteger, ih]

/-- Every byte of `encodeInteger` is specified. -/
theorem encodeInteger_some (n : Nat) (v : Int) :
    encodeInteger n v = ((List.range n).map fun i => v / 256 ^ i % 256).map some := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [encodeInteger, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, pow_zero, Int.ediv_one, List.cons.injEq, true_and]
    apply List.map_congr_left
    intro i _
    simp [pow_succ, Int.ediv_ediv_of_nonneg, Function.comp, mul_comm]

/-- Reading `n` bytes that are all specified. -/
theorem fetchBytes_of (n : Nat) (a : Int) (xs : Map Int Byte) (e : List Int) (hlen : e.length = n)
    (h : ∀ (j : Nat) (hj : j < n), xs.lookup (a + j) = some (some (e[j]'(hlen ▸ hj)))) :
    fetchBytes n a xs = e.map some := by
  induction n generalizing a e with
  | zero =>
    cases e with
    | nil => rfl
    | cons => simp at hlen
  | succ n ih =>
    cases e with
    | nil => simp at hlen
    | cons e0 e =>
      simp only [fetchBytes, List.map_cons, List.cons.injEq]
      have h0 := h 0 (by omega)
      simp only [Nat.cast_zero, Int.add_zero] at h0
      refine ⟨by simp [readByte, h0], ih (a + 1) e (by simpa using hlen) fun j hj => ?_⟩
      have := h (j + 1) (by omega)
      rw [show a + ((j + 1 : Nat) : Int) = a + 1 + j by omega] at this
      simpa using this

/-- A live allocation. -/
structure Live (m : Mem.Concrete.State) (id b size : Int) : Prop where
  lookup : ∃ r : Mem.Concrete.Allocation, m.allocations.lookup id = some r ∧ r.base = b ∧ r.size = size ∧
    r.atomic = false
  alive : id ∉ m.dead

theorem Live.grows {m m' : Mem.Concrete.State} {id b size : Int} (h : Live m id b size) (g : Grows m m')
    (hid : id < m.nextId) : Live m' id b size :=
  ⟨by rw [g.allocs id hid]; exact h.lookup, by rw [g.dead]; exact h.alive⟩

theorem accessTyped_live (tags : Tags) (m : Mem.Concrete.State) {id b size : Int} (h : Live m id b size)
    (ty : Ctype) {l : Mem.Concrete.TypeLayout} (hl : typeLayout 64 tags ty = .ok l) {a : Int}
    (ha : b ≤ a) (ha' : a + l.size ≤ b + size) :
    accessTyped tags m ty (.allocated id a) = .ok (id, a, l.size) := by
  obtain ⟨⟨r, hr, hb, hs, hat⟩, hd⟩ := h
  simp [accessTyped, hl, hd, hr, hb, hs, ha, ha', Mem.Concrete.checkAtomic, hat, bind, Except.bind,
    pure, Except.pure]

theorem typeLayout_char_fuel (fuel : Nat) (tags : Tags) :
    typeLayout (fuel + 1) tags Startup.charType = .ok ⟨1, 1, []⟩ := by
  simp [typeLayout, Startup.charType, layout_char]; rfl

theorem typeLayout_char (tags : Tags) : typeLayout 64 tags Startup.charType = .ok ⟨1, 1, []⟩ :=
  typeLayout_char_fuel 63 tags

theorem typeLayout_int (tags : Tags) : typeLayout 64 tags Startup.intType = .ok ⟨4, 4, []⟩ :=
  StartupReach.layout_int tags

theorem typeLayout_pointer_fuel (fuel : Nat) (tags : Tags) (q : Qualifiers) (ty : Ctype) :
    typeLayout (fuel + 1) tags (.mk [] (.pointer q ty)) = .ok ⟨8, 8, []⟩ := by
  simp [typeLayout]; rfl

theorem typeLayout_pointer (tags : Tags) (q : Qualifiers) (ty : Ctype) :
    typeLayout 64 tags (.mk [] (.pointer q ty)) = .ok ⟨8, 8, []⟩ :=
  typeLayout_pointer_fuel 63 tags q ty

/-- A `char` read of a specified byte below 128. -/
theorem load_char (tags : Tags) (m : Mem.Concrete.State) {id b size a c : Int} (h : Live m id b size)
    (ha : b ≤ a) (ha' : a + 1 ≤ b + size) (hc : m.bytes.lookup a = some (some c))
    (h0 : 0 ≤ c) (h1 : c < 128) :
    ∃ m', loadTyped tags m Startup.charType (.allocated id a) = .ok (.integer .char c, m') := by
  have hf : fetchBytes 1 a m.bytes = [some c] := fetchBytes_of 1 a m.bytes [c] rfl fun j hj => by
    obtain rfl : j = 0 := by omega
    simpa using hc
  have hacc : accessTyped tags m (.mk [] (.basic (.integer .char))) (.allocated id a) = .ok (id, a, 1) :=
    accessTyped_live tags m h _ (typeLayout_char tags) ha ha'
  have hlay : typeLayout 64 tags (.mk [] (.basic (.integer .char))) = .ok ⟨1, 1, []⟩ := typeLayout_char tags
  refine ⟨{Mem.Concrete.exposeRead 64 tags m Startup.charType a with lastUsed := some id}, ?_⟩
  simp [loadTyped, hacc, Mem.Concrete.abstractValue, hlay, Startup.charType, layout_char, hf,
    decodeInteger, bind, Except.bind, pure, Except.pure, show ¬ (128 ≤ c) by omega]

/-- Reading `n` bytes whose lookups are known. -/
theorem fetchBytes_eq (n : Nat) (a : Int) (xs : Map Int Byte) (e : List Byte) (hlen : e.length = n)
    (h : ∀ (j : Nat) (hj : j < n), xs.lookup (a + j) = some (e[j]'(hlen ▸ hj))) :
    fetchBytes n a xs = e := by
  induction n generalizing a e with
  | zero =>
    cases e with
    | nil => rfl
    | cons => simp at hlen
  | succ n ih =>
    cases e with
    | nil => simp at hlen
    | cons e0 e =>
      simp only [fetchBytes, List.cons.injEq]
      have h0 := h 0 (by omega)
      simp only [Nat.cast_zero, Int.add_zero] at h0
      refine ⟨by simp [readByte, h0], ih (a + 1) e (by simpa using hlen) fun j hj => ?_⟩
      have := h (j + 1) (by omega)
      rw [show a + ((j + 1 : Nat) : Int) = a + 1 + j by omega] at this
      simpa using this

/-- An `int` read of a stored non-negative `int`. -/
theorem load_int (tags : Tags) (m : Mem.Concrete.State) {id b size a n : Int} (h : Live m id b size)
    (ha : b ≤ a) (ha' : a + 4 ≤ b + size) (hf : fetchBytes 4 a m.bytes = encodeInteger 4 n)
    (h0 : 0 ≤ n) (h1 : n < 2147483648) :
    ∃ m', loadTyped tags m Startup.intType (.allocated id a) = .ok (.integer (.signed .int) n, m') := by
  have hacc : accessTyped tags m (.mk [] (.basic (.integer (.signed .int)))) (.allocated id a) =
      .ok (id, a, 4) := accessTyped_live tags m h _ (typeLayout_int tags) ha ha'
  have hlay : typeLayout 64 tags (.mk [] (.basic (.integer (.signed .int)))) = .ok ⟨4, 4, []⟩ :=
    typeLayout_int tags
  have hd := decodeInteger_encodeInteger 4 n h0 (by norm_num; omega)
  refine ⟨{Mem.Concrete.exposeRead 64 tags m Startup.intType a with lastUsed := some id}, ?_⟩
  simp [loadTyped, hacc, Mem.Concrete.abstractValue, hlay, Startup.intType, layout_signedInt, hf, hd,
    bind, Except.bind, pure, Except.pure, show ¬ (2147483648 ≤ n) by omega]

/-- A pointer read of an intact pointer representation with allocation provenance. -/
theorem abstractPointer_allocated (m : Mem.Concrete.State) {refTy : Ctype}
    (hr : refTy = Startup.charType ∨ refTy = Startup.charPointer) {a id v : Int} (hv : v ≠ 0)
    (hp : ∀ k : Nat, k < 8 → m.pointerBytes.lookup (a + k) = some (some id, k)) :
    Mem.Concrete.abstractPointer m refTy a v = .ok (.allocated id v) := by
  have hall : (List.range 8).all (fun i : Nat => m.pointerBytes.lookup (a + i) == some (some id, i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [hp i (List.mem_range.mp hi)]
    simp
  have h0 := hp 0 (by omega)
  simp only [Nat.cast_zero, Int.add_zero] at h0
  rcases hr with rfl | rfl <;>
    simp [Mem.Concrete.abstractPointer, hv, Startup.charType, Startup.charPointer, h0, hall, pure,
      Except.pure]

theorem abstractPointer_null (m : Mem.Concrete.State) (refTy : Ctype) (a : Int) :
    Mem.Concrete.abstractPointer m refTy a 0 = .ok (.null refTy) := by
  simp [Mem.Concrete.abstractPointer, pure, Except.pure]

/-- A pointer read: the bytes decode to `v`, and the pointer is what `abstractPointer` makes of it. -/
theorem load_pointer (tags : Tags) (m : Mem.Concrete.State) {id b size a v : Int} (h : Live m id b size)
    (q : Qualifiers) (refTy : Ctype) (ha : b ≤ a) (ha' : a + 8 ≤ b + size)
    (hf : fetchBytes 8 a m.bytes = encodeInteger 8 v) (h0 : 0 ≤ v) (h1 : v < 18446744073709551616)
    {p : Pointer} (hp : Mem.Concrete.abstractPointer m refTy a v = .ok p) :
    ∃ m', loadTyped tags m (.mk [] (.pointer q refTy)) (.allocated id a) = .ok (.pointer refTy p, m') := by
  have hacc : accessTyped tags m (.mk [] (.pointer q refTy)) (.allocated id a) = .ok (id, a, 8) :=
    accessTyped_live tags m h _ (typeLayout_pointer tags q refTy) ha ha'
  have hd := decodeInteger_encodeInteger 8 v h0 (by norm_num; omega)
  refine ⟨{Mem.Concrete.exposeRead 64 tags m (.mk [] (.pointer q refTy)) a with lastUsed := some id}, ?_⟩
  simp [loadTyped, hacc, Mem.Concrete.abstractValue, typeLayout_pointer, hf, hd, hp, bind, Except.bind,
    pure, Except.pure]

/-! ## The startup objects of `ArgsOk` arguments -/

/-- The characters `Startup.stringValue` accepts without a host exception (printable ASCII
except a backslash, as `Spec.ArgsOk` requires). -/
def Chars (s : String) : Prop := ∀ c ∈ s.toList, 0x20 ≤ c.toNat ∧ c.toNat ≤ 0x7e ∧ c ≠ '\\'

/-- The `char` array of a startup string. -/
def strValue (s : String) : MemoryValue :=
  .array (s.toList.map (fun c => .integer .char c.toNat) ++ [.integer .char 0])

theorem mapM_except_ok {α β ε : Type} (f : α → Except ε β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, h x (by simp), mapM_except_ok f g xs fun y hy => h y (by simp [hy])]
    rfl

theorem stringValue_ok (s : String) (h : Chars s) : Startup.stringValue s = .ok (strValue s) := by
  simp only [Startup.stringValue, bind, Except.bind]
  rw [mapM_except_ok _ (fun c => MemoryValue.integer .char c.toNat) _ fun c hc => ?_]
  · rfl
  obtain ⟨h1, h2, h3⟩ := h c hc
  have h4 : c.toNat ≠ 92 := fun e => h3 (Char.toNat_inj.mp (by rw [e]; rfl))
  simp [h1, h2, h4, pure, Except.pure]

/-- The object of a startup string. -/
def strObject (s : String) : Startup.Object :=
  ⟨.mk [] (.array Startup.charType (some (s.length + 1))), .literal (strValue s), .other "argv refs"⟩

theorem objects_ok (args : List String) (h : ∀ s ∈ args, Chars s) (loc : Loc) (main argc argv : Sym) :
    Startup.objects args false loc main argc argv = .ok (args.map strObject ++
      [⟨.mk [] (.array Startup.charPointer (some (args.length + 1))), .pointers, .source loc [main, argv]⟩,
       ⟨Startup.intType, .literal (.integer (.signed .int) args.length), .source loc [main, argc]⟩,
       ⟨Startup.argvType, .arrayPointer args.length, .source loc [main, argv]⟩]) := by
  simp only [Startup.objects, bind, Except.bind]
  rw [mapM_except_ok _ strObject _ fun s hs => by
    simp [stringValue_ok s (h s hs), strObject, pure, Except.pure]]
  simp [pure, Except.pure]

theorem startObjects_append (tags : Tags) (m : Mem.Concrete.State) (xs ys : List Startup.Object)
    (ptrs : List Pointer) :
    startObjects tags m (xs ++ ys) ptrs = (do
      let (ptrs', m') ← startObjects tags m xs ptrs
      startObjects tags m' ys ptrs') := by
  induction xs generalizing m ptrs with
  | nil => simp [startObjects, bind, Except.bind, pure, Except.pure]
  | cons x xs ih =>
    simp only [List.cons_append, startObjects, bind, Except.bind]
    split
    · rfl
    · split
      · rfl
      · exact ih _ _

/-- String `s` is the live allocation `id` at `b`, with its characters and terminator. -/
structure StrAt (m : Mem.Concrete.State) (id b : Int) (s : String) : Prop where
  live : Live m id b (s.length + 1)
  chars : ∀ (j : Nat) (c : Char), s.toList[j]? = some c →
    m.bytes.lookup (b + j) = some (some (c.toNat : Int))
  nul : m.bytes.lookup (b + s.length) = some (some 0)

theorem StrAt.grows {m m' : Mem.Concrete.State} {id b : Int} {s : String} (h : StrAt m id b s)
    (g : Grows m m') (hid : id < m.nextId) (hb : m.lastAddress ≤ b) : StrAt m' id b s where
  live := h.live.grows g hid
  chars j c hc := by rw [(g.bytes _ (by omega)).1]; exact h.chars j c hc
  nul := by rw [(g.bytes _ (by omega)).1]; exact h.nul

/-- The string pointers `qs` of the strings `ss`, the first with identifier `id0`. -/
def StrPtrs (m : Mem.Concrete.State) (id0 : Int) (ss : List String) (qs : List Pointer) : Prop :=
  qs.length = ss.length ∧ ∀ (i : Nat) (s : String), ss[i]? = some s →
    ∃ b, qs[i]? = some (.allocated (id0 + i) b) ∧ StrAt m (id0 + i) b s ∧ m.lastAddress ≤ b ∧
      b + s.length + 1 ≤ 281474976710655 ∧ 0 < b

theorem loadedMemoryList_chars (cs : List Int) :
    loadedMemoryList Startup.charType (fromMemoryList (cs.map (MemoryValue.integer .char))) =
      .ok (cs.map (MemoryValue.integer .char)) := by
  have hi : intType Startup.charType = some .char := rfl
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [fromMemoryList, fromMemory, loadedMemoryList, toMemory, objectMemory, hi, ih, bind,
      Except.bind, pure, Except.pure]

theorem strValue_eq (s : String) :
    strValue s = .array ((s.toList.map (fun c : Char => (c.toNat : Int)) ++ [0]).map (.integer .char)) := by
  simp [strValue]

theorem toMemory_strValue (s : String) :
    toMemory (unatomic (.mk [] (.array Startup.charType (some (s.length + 1))))) (fromMemory (strValue s)) =
      .ok (strValue s) := by
  rw [strValue_eq]
  simp only [unatomic, fromMemory, toMemory, objectMemory, bind, Except.bind, loadedMemoryList_chars]
  rfl

/-- The representation of a startup string: its bytes, then the terminator. -/
def strBytes (s : String) : Representation :=
  plainBytes (s.toList.map (fun c => some (c.toNat : Int)) ++ [some 0])

theorem represent_strValue (tags : Tags) (s : String) (h : Chars s) (m : Mem.Concrete.State) :
    represent 64 tags (strValue s) m = .ok (strBytes s, m) := by
  rw [strValue, represent_array 63 tags m (fun x => match x with
    | .integer _ c => plainBytes [some c] | _ => []) _ fun x hx => ?_]
  · have e : ∀ {α β : Type} (f : α → β) (l : List α), l.flatMap (fun a => [f a]) = l.map f := by
      intro α β f l; induction l <;> simp_all
    simp [strBytes, plainBytes, List.flatMap_append, List.flatMap_map, e]
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
  rcases hx with ⟨c, hc, rfl⟩ | rfl
  · obtain ⟨h1, h2, -⟩ := h c hc
    rw [represent_char 62 tags m (by omega) (by omega)]
  · rw [represent_char 62 tags m le_rfl (by omega)]

theorem length_strBytes (s : String) : (strBytes s).length = s.length + 1 := by
  simp [strBytes, plainBytes, String.length_toList]

theorem strBytes_char (s : String) {j : Nat} {c : Char} (h : s.toList[j]? = some c) :
    (strBytes s)[j]? = some (some (c.toNat : Int), none) := by
  have hj : j < s.toList.length := by
    rcases Nat.lt_or_ge j s.toList.length with hj | hj
    · exact hj
    · rw [List.getElem?_eq_none hj] at h; cases h
  simp only [strBytes, plainBytes, List.map_append]
  rw [List.getElem?_append_left (by simpa using hj), List.getElem?_map, List.getElem?_map, h]
  rfl

theorem strBytes_nul (s : String) : (strBytes s)[s.length]? = some (some 0, none) := by
  simp [strBytes, plainBytes, String.length_toList]

/-- Bytes written by `createStore_spec`, read through `getElem?`. -/
theorem bytes_of_written {m' : Mem.Concrete.State} {a : Int} {bs : Representation}
    (h : ∀ (j : Nat) (hj : j < bs.length), m'.bytes.lookup (a + j) = some (bs[j]'hj).1 ∧
      m'.pointerBytes.lookup (a + j) = (bs[j]'hj).2)
    {j : Nat} {x : Byte × Option (Option Int × Nat)} (hx : bs[j]? = some x) :
    m'.bytes.lookup (a + j) = some x.1 ∧ m'.pointerBytes.lookup (a + j) = x.2 := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hx
  exact h j hj

theorem typeLayout_strObject (tags : Tags) (s : String) :
    typeLayout 64 tags (strObject s).type = .ok ⟨((s.length : Int) + 1) * 1, 1, []⟩ := by
  simp only [strObject, typeLayout, bind, Except.bind]
  rw [typeLayout_char_fuel 62]
  simp [show ¬ ((s.length : Int) + 1 < 0) by omega, pure, Except.pure]

/-- The room the strings take. -/
def strRoom (ss : List String) : Int := ((ss.map fun s => s.length + 1).sum : Nat)

theorem strRoom_cons (s : String) (ss : List String) :
    strRoom (s :: ss) = strRoom ss + (s.length + 1) := by
  simp only [strRoom, List.map_cons, List.sum_cons]; push_cast; ring

/-- **The strings.** Each string becomes a live `char` array below the previous one, with its
characters and terminator. -/
theorem startObjects_strings (tags : Tags) :
    ∀ (ss : List String) (m : Mem.Concrete.State) (ptrs : List Pointer),
      (∀ s ∈ ss, Chars s) → m.dead = [] → m.lastAddress ≤ 281474976710655 → strRoom ss < m.lastAddress →
      ∃ qs m', startObjects tags m (ss.map strObject) ptrs = .ok (ptrs ++ qs, m') ∧ Grows m m' ∧
        m'.nextId = m.nextId + ss.length ∧ m'.lastAddress = m.lastAddress - strRoom ss ∧
        StrPtrs m' m.nextId ss qs
  | [], m, ptrs, _, _, _, _ => ⟨[], m, by simp [startObjects, pure, Except.pure], Grows.refl m, by simp,
      by simp [strRoom], rfl, fun i s h => by simp at h⟩
  | s :: ss, m, ptrs, hchars, hdead, htop, hroom => by
    have hroom' : strRoom ss + (s.length + 1) < m.lastAddress := by
      rw [strRoom_cons] at hroom; exact hroom
    have hr0 : 0 ≤ strRoom ss := Int.natCast_nonneg _
    have hb : nextBase m (((s.length : Int) + 1) * 1) 1 = m.lastAddress - (s.length + 1) := by
      simp [nextBase]
    obtain ⟨m1, hcs, g1, hn1, hl1, hrec1, hbytes1⟩ := createStore_spec tags m (strObject s) (strValue s)
      (typeLayout_strObject tags s) (by simp [strObject]) (by norm_num) (by dsimp only; omega)
      (by simp [nextBase]; omega) (by simp [hdead]) (toMemory_strValue s)
      (represent_strValue tags s (hchars s (by simp))) (by rw [length_strBytes]; dsimp only; omega)
    rw [hb] at hcs hl1 hrec1 hbytes1
    obtain ⟨qs, m', hrest, g2, hn2, hl2, hptrs⟩ := startObjects_strings tags ss m1
      (ptrs ++ [.allocated m.nextId (m.lastAddress - (s.length + 1))])
      (fun t ht => hchars t (by simp [ht])) (by rw [g1.dead, hdead]) (by rw [hl1]; omega)
      (by rw [hl1]; omega)
    refine ⟨.allocated m.nextId (m.lastAddress - (s.length + 1)) :: qs, m', ?_, g1.trans g2, by rw [hn2, hn1]; simp; omega, by rw [hl2, hl1, strRoom_cons]; omega,
      by simp [hptrs.1], ?_⟩
    · simp only [List.map_cons, startObjects, strObject, Startup.contents, bind, Except.bind, pure,
        Except.pure]
      simp only [strObject] at hcs
      rw [hcs]
      simpa using hrest
    intro i t hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [Nat.cast_zero, Int.add_zero]
      have hstr1 : StrAt m1 m.nextId (m.lastAddress - (s.length + 1)) s := by
        refine ⟨⟨⟨_, hrec1, rfl, by simp [allocRecord], rfl⟩, by rw [g1.dead, hdead]; simp⟩,
          fun j c hc => ?_, ?_⟩
        · simpa using (bytes_of_written hbytes1 (strBytes_char s hc)).1
        · simpa using (bytes_of_written hbytes1 (strBytes_nul s)).1
      refine ⟨_, rfl, hstr1.grows g2 (by omega) (by rw [hl1]), ?_, by omega, by omega⟩
      have := g2.last; rw [hl1] at this; exact this
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨b, hq, hstr, hlast, hbtop, hbpos⟩ := hptrs.2 i t hi
      rw [hn1, show m.nextId + 1 + (i : Int) = m.nextId + ((i + 1 : Nat) : Int) by omega] at hq hstr
      exact ⟨b, by simpa using hq, hstr, hlast, hbtop, hbpos⟩

/-! ## The `argv` array and the parameter objects -/

theorem fetchBytes_grows {m m' : Mem.Concrete.State} (g : Grows m m') (n : Nat) (x : Int)
    (hx : m.lastAddress ≤ x) : fetchBytes n x m'.bytes = fetchBytes n x m.bytes := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [fetchBytes, readByte, (g.bytes x hx).1, ih (x + 1) (by omega)]

/-- Reading back `n` written bytes that are all specified. -/
theorem fetchBytes_written {m' : Mem.Concrete.State} {a : Int} {bs : Representation}
    (h : ∀ (j : Nat) (hj : j < bs.length), m'.bytes.lookup (a + j) = some (bs[j]'hj).1 ∧
      m'.pointerBytes.lookup (a + j) = (bs[j]'hj).2)
    (off : Nat) (e : List Byte) (he : ∀ (k : Nat) (hk : k < e.length), (bs[off + k]?).map (·.1) = some e[k]) :
    fetchBytes e.length (a + off) m'.bytes = e :=
  fetchBytes_eq _ _ _ e rfl fun k hk => by
    have := he k hk
    rw [Option.map_eq_some_iff] at this
    obtain ⟨x, hx, hxe⟩ := this
    have := (bytes_of_written h hx).1
    rw [show a + ((off + k : Nat) : Int) = a + off + k by omega] at this
    rw [this, hxe]

/-- Entry `w * i + k` of a concatenation of pieces of length `w`. -/
theorem getElem?_flatMap_uniform {α β : Type} (f : α → List β) (w : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = w) → ∀ (i k : Nat), k < w →
      (l.flatMap f)[w * i + k]? = (l[i]?).bind fun x => (f x)[k]?
  | [], _, i, k, _ => by simp
  | x :: xs, hw, 0, k, hk => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem?_cons_zero, Option.bind_some]
    rw [List.getElem?_append_left (by rw [hw x (by simp)]; exact hk)]
  | x :: xs, hw, i + 1, k, hk => by
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hw x (by simp)]; nlinarith), hw x (by simp),
      show w * (i + 1) + k - w = w * i + k by rw [Nat.mul_succ]; omega,
      getElem?_flatMap_uniform f w xs (fun y hy => hw y (by simp [hy])) i k hk]
    simp

/-- The `argv` array of `char *` with the string pointers `qs`, null-terminated. -/
structure ArrAt (m : Mem.Concrete.State) (id B : Int) (qs : List Pointer) : Prop where
  live : Live m id B (8 * (qs.length + 1))
  slot : ∀ (i : Nat) (id' b : Int), qs[i]? = some (.allocated id' b) →
    fetchBytes 8 (B + 8 * i) m.bytes = encodeInteger 8 b ∧
      ∀ k : Nat, k < 8 → m.pointerBytes.lookup (B + 8 * i + k) = some (some id', k)
  null : fetchBytes 8 (B + 8 * qs.length) m.bytes = encodeInteger 8 0

theorem ArrAt.grows {m m' : Mem.Concrete.State} {id B : Int} {qs : List Pointer} (h : ArrAt m id B qs)
    (g : Grows m m') (hid : id < m.nextId) (hB : m.lastAddress ≤ B) : ArrAt m' id B qs where
  live := h.live.grows g hid
  slot i id' b hq := by
    obtain ⟨h1, h2⟩ := h.slot i id' b hq
    refine ⟨by rw [fetchBytes_grows g _ _ (by omega)]; exact h1, fun k hk => ?_⟩
    rw [(g.bytes _ (by omega)).2]; exact h2 k hk
  null := by rw [fetchBytes_grows g _ _ (by omega)]; exact h.null

/-- An `int` object holding `n`. -/
structure IntAt (m : Mem.Concrete.State) (id C n : Int) : Prop where
  live : Live m id C 4
  bytes : fetchBytes 4 C m.bytes = encodeInteger 4 n
  plain : Mem.Concrete.PlainAt m C
  readonly : ∀ a, m.allocations.lookup id = some a → a.readonly = none

theorem IntAt.grows {m m' : Mem.Concrete.State} {id C n : Int} (h : IntAt m id C n) (g : Grows m m')
    (hid : id < m.nextId) (hC : m.lastAddress ≤ C) : IntAt m' id C n :=
  ⟨h.live.grows g hid, by rw [fetchBytes_grows g _ _ hC]; exact h.bytes,
    fun i hi => by rw [(g.bytes _ (by omega)).2]; exact h.plain i hi,
    fun a ha => h.readonly a ((g.allocs id hid).symm.trans ha)⟩

/-- A pointer object holding the pointer `.allocated id' b`. -/
structure PtrAt (m : Mem.Concrete.State) (id V id' b : Int) : Prop where
  live : Live m id V 8
  bytes : fetchBytes 8 V m.bytes = encodeInteger 8 b
  prov : ∀ k : Nat, k < 8 → m.pointerBytes.lookup (V + k) = some (some id', k)

theorem PtrAt.grows {m m' : Mem.Concrete.State} {id V id' b : Int} (h : PtrAt m id V id' b)
    (g : Grows m m') (hid : id < m.nextId) (hV : m.lastAddress ≤ V) : PtrAt m' id V id' b :=
  ⟨h.live.grows g hid, by rw [fetchBytes_grows g _ _ hV]; exact h.bytes,
    fun k hk => by rw [(g.bytes _ (by omega)).2]; exact h.prov k hk⟩

theorem length_provBytes (id a : Int) : (provBytes id a).length = 8 := by
  simp [provBytes, length_encodeInteger]

theorem provBytes_getElem? (id a : Int) (k : Nat) :
    (provBytes id a)[k]? = (encodeInteger 8 a)[k]?.map fun b => (b, some (some id, k)) := by
  simp only [provBytes, List.getElem?_map, List.getElem?_zipIdx]
  cases (encodeInteger 8 a)[k]? <;> simp

/-- The contents of the `argv` array. -/
def arrValue (qs : List Pointer) : MemoryValue :=
  .array (qs.map (.pointer Startup.charType) ++ [.pointer Startup.charType (.null Startup.charType)])

/-- The `argv` array object. -/
def arrObject (n : Nat) (loc : Loc) (main argv : Sym) : Startup.Object :=
  ⟨.mk [] (.array Startup.charPointer (some (n + 1))), .pointers, .source loc [main, argv]⟩

/-- The representation of a pointer element of the `argv` array. -/
def slotBytes : MemoryValue → Representation
  | .pointer _ (.allocated id a) => provBytes id a
  | .pointer _ (.null _) => plainBytes (encodeInteger 8 0)
  | _ => []

theorem toMemory_arrValue (qs : List Pointer) (n : Nat) :
    toMemory (unatomic (.mk [] (.array Startup.charPointer (some (n + 1))))) (fromMemory (arrValue qs)) =
      .ok (arrValue qs) := by
  have hl : ∀ ps : List Pointer, loadedMemoryList Startup.charPointer
      (fromMemoryList (ps.map (MemoryValue.pointer Startup.charType))) =
      .ok (ps.map (MemoryValue.pointer Startup.charType)) := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map_cons, fromMemoryList, fromMemory, loadedMemoryList, toMemory, objectMemory, ih]
      rfl
  have e : arrValue qs = .array ((qs ++ [Pointer.null Startup.charType]).map
      (MemoryValue.pointer Startup.charType)) := by
    simp [arrValue]
  rw [e]
  simp only [unatomic, fromMemory, toMemory, objectMemory, bind, Except.bind, hl]
  rfl

theorem typeLayout_arrObject (tags : Tags) (n : Nat) (loc : Loc) (main argv : Sym) :
    typeLayout 64 tags (arrObject n loc main argv).type = .ok ⟨((n : Int) + 1) * 8, 8, []⟩ := by
  simp only [arrObject, typeLayout, bind, Except.bind]
  rw [show Startup.charPointer = .mk [] (.pointer ⟨false, false, false⟩ Startup.charType) from rfl,
    typeLayout_pointer_fuel 62]
  simp [show ¬ ((n : Int) + 1 < 0) by omega, pure, Except.pure]

/-- **The `argv` array.** -/
theorem createStore_array (tags : Tags) (m : Mem.Concrete.State) (qs : List Pointer) (loc : Loc)
    (main argv : Sym)
    (hq : ∀ q ∈ qs, ∃ id b, q = .allocated id b ∧ 0 ≤ b ∧ b < 18446744073709551616)
    (hdead : m.dead = []) (hpos : 0 < nextBase m (((qs.length : Int) + 1) * 8) 8) :
    ∃ m', createStore tags m (arrObject qs.length loc main argv) (arrValue qs) =
        .ok (.allocated m.nextId (nextBase m (((qs.length : Int) + 1) * 8) 8), m') ∧
      Grows m m' ∧ m'.nextId = m.nextId + 1 ∧
      m'.lastAddress = nextBase m (((qs.length : Int) + 1) * 8) 8 ∧
      ArrAt m' m.nextId (nextBase m (((qs.length : Int) + 1) * 8) 8) qs := by
  have hrep : ∀ s, represent 64 tags (arrValue qs) s =
      .ok ((qs.map (MemoryValue.pointer Startup.charType) ++
        [MemoryValue.pointer Startup.charType (.null Startup.charType)]).flatMap slotBytes, s) := fun s => by
    rw [arrValue, represent_array 63 tags s slotBytes _ fun x hx => ?_]
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨q, hq', rfl⟩ | rfl
    · obtain ⟨id, b, rfl, h0, h1⟩ := hq q hq'
      rw [represent_allocated 62 tags s _ h0 h1]; rfl
    · rw [represent_null]; rfl
  have hw : ∀ x ∈ qs.map (MemoryValue.pointer Startup.charType) ++
      [MemoryValue.pointer Startup.charType (.null Startup.charType)],
      (slotBytes x).length = 8 := by
    intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨q, hq', rfl⟩ | rfl
    · obtain ⟨id, b, rfl, -, -⟩ := hq q hq'
      simp [slotBytes, length_provBytes]
    · simp [slotBytes, plainBytes, length_encodeInteger]
  obtain ⟨m', hcs, g, hn, hl, hrec, hbytes⟩ := createStore_spec tags m (arrObject qs.length loc main argv)
    (arrValue qs) (typeLayout_arrObject tags qs.length loc main argv) (by simp [arrObject]) (by norm_num)
    (by dsimp only; omega) hpos (by simp [hdead]) (toMemory_arrValue qs qs.length) hrep (by
      dsimp only
      rw [List.length_flatMap, List.map_congr_left hw]
      simp [Function.comp_def, List.map_const', List.sum_replicate]; omega)
  set B := nextBase m (((qs.length : Int) + 1) * 8) 8
  set xs := qs.map (MemoryValue.pointer Startup.charType) ++
    [MemoryValue.pointer Startup.charType (.null Startup.charType)]
  have hentry : ∀ (i k : Nat), k < 8 → (xs.flatMap slotBytes)[8 * i + k]? =
      (xs[i]?).bind fun x => (slotBytes x)[k]? := getElem?_flatMap_uniform slotBytes 8 xs hw
  refine ⟨m', hcs, g, hn, hl, ⟨⟨_, hrec, rfl, by simp [allocRecord]; ring, rfl⟩, by rw [g.dead, hdead]; simp⟩,
    fun i id' b hq => ?_, ?_⟩
  · have hi : i < qs.length := (List.getElem?_eq_some_iff.mp hq).1
    have hx : xs[i]? = some (.pointer Startup.charType (.allocated id' b)) := by
      simp only [xs]
      rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map, hq]; rfl
    have hk : ∀ k : Nat, k < 8 → (xs.flatMap slotBytes)[8 * i + k]? =
        (encodeInteger 8 b)[k]?.map fun e => (e, some (some id', k)) := by
      intro k hk; rw [hentry i k hk, hx]; simp [slotBytes, provBytes_getElem?]
    refine ⟨?_, fun k hk' => ?_⟩
    · have := fetchBytes_written hbytes (8 * i) (encodeInteger 8 b) fun k hk' => by
        rw [length_encodeInteger] at hk'
        rw [hk k hk', List.getElem?_eq_getElem (by rw [length_encodeInteger]; exact hk')]
        rfl
      rw [length_encodeInteger] at this
      simpa using this
    · obtain ⟨hk1, hk2⟩ := List.getElem?_eq_some_iff.mp (show (xs.flatMap slotBytes)[8 * i + k]? =
        some ((encodeInteger 8 b)[k]'(by rw [length_encodeInteger]; exact hk'), some (some id', k)) by
          rw [hk k hk', List.getElem?_eq_getElem (by rw [length_encodeInteger]; exact hk')]; rfl)
      have := (hbytes (8 * i + k) hk1).2
      rw [hk2] at this
      rw [show B + 8 * (i : Int) + k = B + ((8 * i + k : Nat) : Int) by push_cast; ring]
      exact this
  · have hx : xs[qs.length]? = some (.pointer Startup.charType (.null Startup.charType)) := by
      simp [xs]
    have := fetchBytes_written hbytes (8 * qs.length) (encodeInteger 8 0) fun k hk' => by
      rw [length_encodeInteger] at hk'
      rw [hentry _ k hk', hx]
      simp [slotBytes, plainBytes, List.getElem?_eq_getElem (l := encodeInteger 8 0) (i := k)
        (by rw [length_encodeInteger]; exact hk')]
    rw [length_encodeInteger] at this
    simpa using this

/-- The `argc` parameter object. -/
def argcObject (n : Nat) (loc : Loc) (main argc : Sym) : Startup.Object :=
  ⟨Startup.intType, .literal (.integer (.signed .int) n), .source loc [main, argc]⟩

/-- The `argv` parameter object. -/
def argvObject (n : Nat) (loc : Loc) (main argv : Sym) : Startup.Object :=
  ⟨Startup.argvType, .arrayPointer n, .source loc [main, argv]⟩

/-- **The `argc` parameter object.** -/
theorem createStore_argc (tags : Tags) (m : Mem.Concrete.State) (n : Nat) (hn : n < 2147483648)
    (loc : Loc) (main argc : Sym) (hdead : m.dead = []) (hpos : 0 < nextBase m 4 4) :
    ∃ m', createStore tags m (argcObject n loc main argc) (.integer (.signed .int) n) =
        .ok (.allocated m.nextId (nextBase m 4 4), m') ∧
      Grows m m' ∧ m'.nextId = m.nextId + 1 ∧ m'.lastAddress = nextBase m 4 4 ∧
      IntAt m' m.nextId (nextBase m 4 4) n := by
  obtain ⟨m', hcs, g, hn', hl, hrec, hbytes⟩ := createStore_spec tags m (argcObject n loc main argc)
    (.integer (.signed .int) n) (typeLayout_int tags) (by simp [argcObject, Startup.intType])
    (by norm_num) (by norm_num) hpos (by simp [hdead])
    (n := .integer (.signed .int) n) rfl
    (fun s => represent_signedInt 63 tags s (n := n) (by omega) (by omega))
    (by simp [plainBytes, length_encodeInteger])
  refine ⟨m', hcs, g, hn', hl, ⟨⟨_, hrec, rfl, by simp [allocRecord], rfl⟩, by rw [g.dead, hdead]; simp⟩,
    ?_, ?_, ?_⟩
  · have := fetchBytes_written hbytes 0 (encodeInteger 4 n) fun k hk => by
      rw [length_encodeInteger] at hk
      simp [plainBytes, List.getElem?_eq_getElem (l := encodeInteger 4 n) (i := k)
        (by rw [length_encodeInteger]; exact hk)]
    simpa [length_encodeInteger] using this
  · intro i hi
    have h := (hbytes i (by simpa [plainBytes, length_encodeInteger] using hi)).2
    simpa [plainBytes] using h
  · intro a ha
    rw [hrec, Option.some.injEq] at ha
    subst a
    rfl

/-- **The `argv` parameter object.** -/
theorem createStore_argv (tags : Tags) (m : Mem.Concrete.State) (n : Nat) (id B : Int)
    (hB0 : 0 ≤ B) (hB1 : B < 18446744073709551616)
    (loc : Loc) (main argv : Sym) (hdead : m.dead = []) (hpos : 0 < nextBase m 8 8) :
    ∃ m', createStore tags m (argvObject n loc main argv)
        (.pointer Startup.charPointer (.allocated id B)) =
        .ok (.allocated m.nextId (nextBase m 8 8), m') ∧
      Grows m m' ∧ m'.nextId = m.nextId + 1 ∧ m'.lastAddress = nextBase m 8 8 ∧
      PtrAt m' m.nextId (nextBase m 8 8) id B := by
  obtain ⟨m', hcs, g, hn', hl, hrec, hbytes⟩ := createStore_spec tags m (argvObject n loc main argv)
    (.pointer Startup.charPointer (.allocated id B))
    (typeLayout_pointer tags _ _) (by simp [argvObject, Startup.argvType])
    (by norm_num) (by norm_num) hpos (by simp [hdead])
    (n := .pointer Startup.charPointer (.allocated id B)) rfl
    (fun s => represent_allocated 63 tags s _ (id := id) hB0 hB1) (by simp [length_provBytes])
  refine ⟨m', hcs, g, hn', hl, ⟨⟨_, hrec, rfl, by simp [allocRecord], rfl⟩, by rw [g.dead, hdead]; simp⟩,
    ?_, fun k hk => ?_⟩
  · have := fetchBytes_written hbytes 0 (encodeInteger 8 B) fun k hk => by
      rw [length_encodeInteger] at hk
      rw [Nat.zero_add, provBytes_getElem?,
        List.getElem?_eq_getElem (by rw [length_encodeInteger]; omega)]
      simp
    simpa [length_encodeInteger] using this
  · have hx : (provBytes id B)[k]? = some ((encodeInteger 8 B)[k]'(by rw [length_encodeInteger]; exact hk),
        some (some id, k)) := by
      rw [provBytes_getElem?, List.getElem?_eq_getElem (by rw [length_encodeInteger]; exact hk)]
      rfl
    simpa using (bytes_of_written hbytes hx).2

theorem objects_ok' (args : List String) (h : ∀ s ∈ args, Chars s) (loc : Loc) (main argc argv : Sym) :
    Startup.objects args false loc main argc argv = .ok (args.map strObject ++
      [arrObject args.length loc main argv, argcObject args.length loc main argc,
       argvObject args.length loc main argv]) :=
  objects_ok args h loc main argc argv

theorem nextBase_ge (m : Mem.Concrete.State) (size align : Int) (h : 0 < align) :
    m.lastAddress - size - (align - 1) ≤ nextBase m size align ∧ nextBase m size align ≤ m.lastAddress - size := by
  have h1 := Int.emod_nonneg (m.lastAddress - size) (show align ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos (m.lastAddress - size) h
  simp only [nextBase]; omega

/-- **The startup objects of `main(argc, argv)`.** From a memory without dead allocations and with
room for them, `startObjects` creates the strings (`StrPtrs`), the `argv` array of their pointers
(`ArrAt`), the `argc` object holding `argc` (`IntAt`), and the `argv` parameter object pointing at
the array (`PtrAt`), with consecutive identifiers from `m.nextId`. -/
theorem startObjects_args (tags : Tags) (args : List String) (h : ∀ s ∈ args, Chars s)
    (hn : args.length < 2147483648) (loc : Loc) (main argc argv : Sym) (m : Mem.Concrete.State)
    (hdead : m.dead = []) (htop : m.lastAddress ≤ 281474976710655)
    (hroom : strRoom args + 8 * (args.length + 1) + 64 < m.lastAddress) :
    ∃ qs B C V m', startObjects tags m (args.map strObject ++
        [arrObject args.length loc main argv, argcObject args.length loc main argc,
         argvObject args.length loc main argv]) [] =
        .ok (qs ++ [.allocated (m.nextId + args.length) B, .allocated (m.nextId + args.length + 1) C,
          .allocated (m.nextId + args.length + 2) V], m') ∧
      Grows m m' ∧ m'.nextId = m.nextId + args.length + 3 ∧ m'.dead = [] ∧
      m.lastAddress - strRoom args - 8 * (args.length + 1) - 32 ≤ m'.lastAddress ∧
      StrPtrs m' m.nextId args qs ∧ ArrAt m' (m.nextId + args.length) B qs ∧
      IntAt m' (m.nextId + args.length + 1) C args.length ∧
      PtrAt m' (m.nextId + args.length + 2) V (m.nextId + args.length) B ∧
      0 < B ∧ B + 8 * (args.length + 1) ≤ 281474976710655 ∧ m'.lastAddress = V ∧ V < C ∧ C < B := by
  have hr0 : 0 ≤ strRoom args := Int.natCast_nonneg _
  obtain ⟨qs, m1, hs, g1, hn1, hl1, hptrs⟩ := startObjects_strings tags args m [] h hdead htop (by omega)
  have hlen : qs.length = args.length := hptrs.1
  have hlenI : (qs.length : Int) = args.length := by rw [hlen]
  have hq : ∀ q ∈ qs, ∃ id b, q = .allocated id b ∧ 0 ≤ b ∧ b < 18446744073709551616 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨b, hb, -, -, hbtop, hbpos⟩ := hptrs.2 i args[i] (by
      rw [List.getElem?_eq_getElem (by omega)])
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hb
    exact ⟨_, b, hb, by omega, by omega⟩
  have hd1 : m1.dead = [] := by rw [g1.dead, hdead]
  set B := nextBase m1 (((qs.length : Int) + 1) * 8) 8 with hB
  obtain ⟨hB1, hB2⟩ := nextBase_ge m1 (((qs.length : Int) + 1) * 8) 8 (by norm_num)
  obtain ⟨m2, hcs2, g2, hn2, hl2, harr⟩ := createStore_array tags m1 qs loc main argv hq hd1 (by omega)
  have hd2 : m2.dead = [] := by rw [g2.dead, hd1]
  set C := nextBase m2 4 4 with hC
  obtain ⟨hC1, hC2⟩ := nextBase_ge m2 4 4 (by norm_num)
  obtain ⟨m3, hcs3, g3, hn3, hl3, hint⟩ := createStore_argc tags m2 args.length hn loc main argc hd2
    (by omega)
  have hd3 : m3.dead = [] := by rw [g3.dead, hd2]
  set V := nextBase m3 8 8 with hV
  obtain ⟨hV1, hV2⟩ := nextBase_ge m3 8 8 (by norm_num)
  obtain ⟨m4, hcs4, g4, hn4, hl4, hptr⟩ := createStore_argv tags m3 args.length (m1.nextId) B
    (by omega) (by omega) loc main argv hd3 (by omega)
  refine ⟨qs, B, C, V, m4, ?_, g1.trans (g2.trans (g3.trans g4)), by rw [hn4, hn3, hn2, hn1]; ring,
    by rw [g4.dead, hd3], by omega, ?_, ?_, ?_, ?_, by omega, by omega, hl4, by omega, by omega⟩
  · rw [startObjects_append, hs]
    simp only [List.nil_append, bind, Except.bind, startObjects, arrObject, Startup.contents]
    have e1 : (.array (qs.map (.pointer Startup.charType) ++
        [.pointer Startup.charType (.null Startup.charType)]) : MemoryValue) = arrValue qs := rfl
    simp only [pure, Except.pure, e1]
    rw [show (⟨.mk [] (.array Startup.charPointer (some (args.length + 1))), .pointers,
      .source loc [main, argv]⟩ : Startup.Object) = arrObject qs.length loc main argv by rw [hlen]; rfl,
      hcs2]
    simp only [argcObject]
    rw [show (⟨Startup.intType, .literal (.integer (.signed .int) args.length), .source loc [main, argc]⟩ :
      Startup.Object) = argcObject args.length loc main argc from rfl, hcs3]
    simp only [argvObject]
    rw [← hB]
    rw [List.getElem?_append_left (by simp [hlen]), List.getElem?_append_right (by omega),
      hlen, Nat.sub_self]
    simp only [List.getElem?_cons_zero]
    rw [show (⟨Startup.argvType, .arrayPointer args.length, .source loc [main, argv]⟩ :
      Startup.Object) = argvObject args.length loc main argv from rfl, hcs4]
    simp only [hn1, hn2, hn3, List.append_assoc, List.cons_append, List.nil_append, ← hC, ← hV]
    congr 3; ring_nf
  · refine ⟨hlen, fun i s hi => ?_⟩
    obtain ⟨b, hb, hstr, hlast, hbtop, hbpos⟩ := hptrs.2 i s hi
    exact ⟨b, hb, hstr.grows (g2.trans (g3.trans g4)) (by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega) hlast,
      (g2.trans (g3.trans g4)).last.trans hlast, hbtop, hbpos⟩
  · rw [← hn1]
    exact harr.grows (g3.trans g4) (by omega) (by rw [hl2])
  · rw [show m.nextId + args.length + 1 = m2.nextId by rw [hn2, hn1]]
    exact hint.grows g4 (by omega) (by rw [hl3])
  · rw [show m.nextId + args.length + 2 = m3.nextId by rw [hn3, hn2, hn1]; ring,
      show m.nextId + args.length = m1.nextId by rw [hn1]]
    exact hptr

/-! ## Later memories -/

/-- What later actions keep of the memory `m`: every allocation older than `m.nextId` is unchanged
and not killed, and the bytes at or above `m`'s frontier are unchanged. Stores below the
frontier, newer allocations and their kills keep it. -/
structure Keeps (m m' : Mem.Concrete.State) : Prop where
  allocs : ∀ id < m.nextId, m'.allocations.lookup id = m.allocations.lookup id
  dead : ∀ id < m.nextId, id ∈ m'.dead → id ∈ m.dead
  bytes : ∀ x, m.lastAddress ≤ x →
    m'.bytes.lookup x = m.bytes.lookup x ∧ m'.pointerBytes.lookup x = m.pointerBytes.lookup x

theorem Grows.keeps {m m' : Mem.Concrete.State} (g : Grows m m') : Keeps m m' :=
  ⟨g.allocs, fun _ _ h => g.dead ▸ h, g.bytes⟩

theorem Keeps.refl (m : Mem.Concrete.State) : Keeps m m := (Grows.refl m).keeps

theorem Live.keeps {m m' : Mem.Concrete.State} {id b size : Int} (h : Live m id b size) (g : Keeps m m')
    (hid : id < m.nextId) : Live m' id b size :=
  ⟨by rw [g.allocs id hid]; exact h.lookup, fun hd => h.alive (g.dead id hid hd)⟩

theorem fetchBytes_keeps {m m' : Mem.Concrete.State} (g : Keeps m m') (n : Nat) (x : Int)
    (hx : m.lastAddress ≤ x) : fetchBytes n x m'.bytes = fetchBytes n x m.bytes := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [fetchBytes, readByte, (g.bytes x hx).1, ih (x + 1) (by omega)]

theorem StrAt.keeps {m m' : Mem.Concrete.State} {id b : Int} {s : String} (h : StrAt m id b s)
    (g : Keeps m m') (hid : id < m.nextId) (hb : m.lastAddress ≤ b) : StrAt m' id b s where
  live := h.live.keeps g hid
  chars j c hc := by rw [(g.bytes _ (by omega)).1]; exact h.chars j c hc
  nul := by rw [(g.bytes _ (by omega)).1]; exact h.nul

theorem ArrAt.keeps {m m' : Mem.Concrete.State} {id B : Int} {qs : List Pointer} (h : ArrAt m id B qs)
    (g : Keeps m m') (hid : id < m.nextId) (hB : m.lastAddress ≤ B) : ArrAt m' id B qs where
  live := h.live.keeps g hid
  slot i id' b hq := by
    obtain ⟨h1, h2⟩ := h.slot i id' b hq
    refine ⟨by rw [fetchBytes_keeps g _ _ (by omega)]; exact h1, fun k hk => ?_⟩
    rw [(g.bytes _ (by omega)).2]; exact h2 k hk
  null := by rw [fetchBytes_keeps g _ _ (by omega)]; exact h.null

theorem IntAt.keeps {m m' : Mem.Concrete.State} {id C n : Int} (h : IntAt m id C n) (g : Keeps m m')
    (hid : id < m.nextId) (hC : m.lastAddress ≤ C) : IntAt m' id C n :=
  ⟨h.live.keeps g hid, by rw [fetchBytes_keeps g _ _ hC]; exact h.bytes,
    fun i hi => by rw [(g.bytes _ (by omega)).2]; exact h.plain i hi,
    fun a ha => h.readonly a ((g.allocs id hid).symm.trans ha)⟩

theorem PtrAt.keeps {m m' : Mem.Concrete.State} {id V id' b : Int} (h : PtrAt m id V id' b)
    (g : Keeps m m') (hid : id < m.nextId) (hV : m.lastAddress ≤ V) : PtrAt m' id V id' b :=
  ⟨h.live.keeps g hid, by rw [fetchBytes_keeps g _ _ hV]; exact h.bytes,
    fun k hk => by rw [(g.bytes _ (by omega)).2]; exact h.prov k hk⟩

theorem Grows.keeps_trans {m1 m2 m3 : Mem.Concrete.State} (g : Grows m1 m2) (k : Keeps m2 m3) :
    Keeps m1 m3 where
  allocs id hid := (k.allocs id (lt_of_lt_of_le hid g.next)).trans (g.allocs id hid)
  dead id hid hd := g.dead ▸ k.dead id (lt_of_lt_of_le hid g.next) hd
  bytes x hx := by
    obtain ⟨a, b⟩ := k.bytes x (g.last.trans hx)
    obtain ⟨c, d⟩ := g.bytes x hx
    exact ⟨a.trans c, b.trans d⟩

/-! ## `errno` -/

/-- The `errno` object, as a startup object. -/
def errnoObject : Startup.Object :=
  ⟨StartupReach.intTy, .literal (.integer (.signed .int) 0), .other "errno"⟩

theorem allocateTyped_int (tags : Tags) (m : Mem.Concrete.State) :
    allocateTyped tags m 4 StartupReach.intTy = allocateTyped ∅ m 4 StartupReach.intTy := by
  simp only [allocateTyped, StartupReach.layout_int]

/-- Creating `errno` is creating a startup `int` object (its layout does not depend on the tags). -/
theorem createErrno_eq (tags : Tags) (m : Mem.Concrete.State) :
    createErrno tags m = createStore ∅ m errnoObject (.integer (.signed .int) 0) := by
  simp only [createErrno, createStore, errnoObject, StartupReach.layout_int, allocateTyped_int]
  rfl

/-- **`errno`.** From a memory without dead allocations and with room, `createErrno` succeeds and
grows the memory. -/
theorem createErrno_spec (tags : Tags) (m : Mem.Concrete.State) (hdead : m.dead = [])
    (hpos : 0 < nextBase m 4 4) :
    ∃ p m', createErrno tags m = .ok (p, m') ∧ Grows m m' := by
  obtain ⟨m', hcs, g, -⟩ := createStore_spec ∅ m errnoObject (.integer (.signed .int) 0)
    (StartupReach.layout_int ∅) (by simp [errnoObject, StartupReach.intTy]) (by norm_num) (by norm_num)
    hpos (by simp [hdead]) (n := .integer (.signed .int) 0) rfl
    (fun s => represent_signedInt 63 ∅ s (n := 0) (by norm_num) (by norm_num))
    (by simp [plainBytes, length_encodeInteger])
  exact ⟨_, m', (createErrno_eq tags m).trans hcs, g⟩

end Silmaril.Cerberus.Core.StartupArgs
