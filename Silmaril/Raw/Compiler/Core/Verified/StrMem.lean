module

public import Silmaril.Cerberus.Mem.TypedAggregateLaws.Defs
public import Silmaril.Cerberus.Mem.IntSlots.Defs
public import Silmaril.Cerberus.Mem.Operations.Defs

/-! # Concrete memory facts for `printf`: string objects and the format argument object

`printf("…", …)` in Cerberus's Core reads its format string through two objects:

* the string literal, a read-only `char` array created at startup
  (`create_readonly(Ivalignof(char[n]), char[n], Specified(array(…)))`), which `listFromStr`
  reads one `char` at a time through `PtrArrayShift`;
* the call's first argument object, of type `const char*`, created by the caller, holding the
  decayed pointer to the literal, loaded back by `printf_proxy`, killed after the call.

`StrObj m id addr cs` describes the first (its characters `cs`, the terminating 0 included,
plain bytes) and `PtrObj` the second (the eight bytes of a pointer with intact copy metadata).
`Keeps m m'` says that `m'` keeps every object of `m`: allocations and lifetimes of the ids below
`m.nextId`, bytes and pointer metadata at or above `m.lastAddress`. Both descriptions survive
`Keeps`; every later allocation, store into a later object, load and kill of a later object
keeps the earlier memory. The lemmas here are about `Mem.Concrete` only (no dynamics).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StrMem

open Silmaril.Cerberus
open Mem.Concrete

/-- Plain `char` (signed, one byte). -/
abbrev charTy (ann : List Annot) : Ctype := .mk ann (.basic (.integer .char))

/-- `char[n]`. -/
abbrev charArr (ann annE : List Annot) (n : Int) : Ctype := .mk ann (.array (charTy annE) (some n))

/-! ## Keeping the earlier objects -/

/-- `m'` keeps every object of `m`. -/
structure Keeps (m m' : State) : Prop where
  enums : m'.enumTypes = m.enumTypes
  nextId : m.nextId ≤ m'.nextId
  last : m'.lastAddress ≤ m.lastAddress
  alloc : ∀ j, j < m.nextId → m'.allocations.lookup j = m.allocations.lookup j
  dead : ∀ j, j < m.nextId → (j ∈ m'.dead ↔ j ∈ m.dead)
  bytes : ∀ x, m.lastAddress ≤ x → m'.bytes.lookup x = m.bytes.lookup x
  pbytes : ∀ x, m.lastAddress ≤ x → m'.pointerBytes.lookup x = m.pointerBytes.lookup x

theorem Keeps.refl (m : State) : Keeps m m :=
  ⟨rfl, le_refl _, le_refl _, fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Keeps.trans {m₁ m₂ m₃ : State} (h₁ : Keeps m₁ m₂) (h₂ : Keeps m₂ m₃) : Keeps m₁ m₃ :=
  ⟨h₂.enums.trans h₁.enums, le_trans h₁.nextId h₂.nextId, le_trans h₂.last h₁.last,
    fun j hj => (h₂.alloc j (lt_of_lt_of_le hj h₁.nextId)).trans (h₁.alloc j hj),
    fun j hj => (h₂.dead j (lt_of_lt_of_le hj h₁.nextId)).trans (h₁.dead j hj),
    fun x hx => (h₂.bytes x (le_trans h₁.last hx)).trans (h₁.bytes x hx),
    fun x hx => (h₂.pbytes x (le_trans h₁.last hx)).trans (h₁.pbytes x hx)⟩

/-- A state that differs only in fields that hold no object. -/
theorem Keeps.of_same {m m' : State} (e : m'.enumTypes = m.enumTypes) (n : m'.nextId = m.nextId)
    (l : m'.lastAddress = m.lastAddress) (a : m'.allocations = m.allocations) (d : m'.dead = m.dead)
    (b : m'.bytes = m.bytes) (p : m'.pointerBytes = m.pointerBytes) : Keeps m m' :=
  ⟨e, n.ge, l.le, fun _ _ => by rw [a], fun _ _ => by rw [d], fun _ _ => by rw [b],
    fun _ _ => by rw [p]⟩

/-! ### Helpers about writes and maps -/

theorem wr_nextId (a : Int) (bs : Representation) (s : State) :
    (writeRepresentation a bs s).nextId = s.nextId := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape a bs s
  rw [h]

theorem wr_lastAddress (a : Int) (bs : Representation) (s : State) :
    (writeRepresentation a bs s).lastAddress = s.lastAddress := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape a bs s
  rw [h]

theorem wr_enumTypes (a : Int) (bs : Representation) (s : State) :
    (writeRepresentation a bs s).enumTypes = s.enumTypes := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape a bs s
  rw [h]

theorem wr_stdout (a : Int) (bs : Representation) (s : State) :
    (writeRepresentation a bs s).stdout = s.stdout := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape a bs s
  rw [h]

theorem wr_lastUsed (a : Int) (bs : Representation) (s : State) :
    (writeRepresentation a bs s).lastUsed = s.lastUsed := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape a bs s
  rw [h]

theorem lookup_writeInt_outside (a c : Int) (bs : List Byte) (xs : Map Int Byte)
    (h : c < a ∨ a + bs.length ≤ c) : (writeInt a bs xs).lookup c = xs.lookup c := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
    simp only [writeInt, writeByte]
    rw [Map.lookup_insert_of_key_ne _ _ (show c ≠ a by omega), ih (a + 1) (by omega)]

theorem bytes_write_outside (a c : Int) (bs : Representation) (s : State)
    (h : c < a ∨ a + bs.length ≤ c) :
    (writeRepresentation a bs s).bytes.lookup c = s.bytes.lookup c := by
  rw [writeRepresentation_bytes]
  exact lookup_writeInt_outside a c _ _ (by simpa using h)

theorem readByte_writeInt (a : Int) (bs : List Byte) (xs : Map Int Byte) (i : Nat)
    (h : i < bs.length) : readByte (a + i) (writeInt a bs xs) = bs[i] := by
  induction bs generalizing a i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero => simp [writeInt, read_write_same]
    | succ i =>
      simp only [writeInt]
      rw [read_write_other _ _ _ _ (by omega), show a + ((i + 1 : Nat) : Int) = a + 1 + i by omega,
        ih (a + 1) i (by simpa using h)]
      simp

theorem encodeInteger_getElem (w : Nat) (n : Int) (i : Nat) (h : i < w) :
    (encodeInteger w n)[i]'(by rw [encodeInteger_length]; exact h) = some (n / 256 ^ i % 256) := by
  induction w generalizing n i with
  | zero => omega
  | succ w ih =>
    cases i with
    | zero => simp [encodeInteger]
    | succ i =>
      simp only [encodeInteger, List.getElem_cons_succ]
      rw [ih (n / 256) i (by omega), Int.ediv_ediv_of_nonneg (by norm_num), pow_succ']

theorem fetchBytes_eq_encode (w : Nat) (a n : Int) (xs : Map Int Byte)
    (h : ∀ i : Nat, i < w → readByte (a + i) xs = some (n / 256 ^ i % 256)) :
    fetchBytes w a xs = encodeInteger w n := by
  induction w generalizing a n with
  | zero => rfl
  | succ w ih =>
    simp only [fetchBytes, encodeInteger]
    have h0 := h 0 (by omega)
    simp only [Nat.cast_zero, Int.add_zero, pow_zero, Int.ediv_one] at h0
    rw [h0, ih (a + 1) (n / 256)]
    intro i hi
    rw [show a + 1 + (i : Int) = a + ((i + 1 : Nat) : Int) by omega, h (i + 1) (by omega),
      Int.ediv_ediv_of_nonneg (by norm_num), pow_succ']

theorem map_lookup_erase_ne {v : Type} (m : Map Int v) {x x' : Int} (h : x' ≠ x) :
    (m.erase x).lookup x' = m.lookup x' :=
  Finmap.lookup_erase_ne h

theorem updateLast_of (s : State) (f : Allocation → Allocation) {j : Int} {a : Allocation}
    (hj : s.lastUsed = some j) (ha : s.allocations.lookup j = some a) :
    updateLastAllocation s f = {s with allocations := s.allocations.insert j (f a)} := by
  unfold updateLastAllocation
  simp [hj, ha]

/-- A write below the earlier objects keeps them. -/
theorem Keeps.write {m₀ m : State} (h : Keeps m₀ m) (a : Int) (bs : Representation)
    (below : a + bs.length ≤ m₀.lastAddress) : Keeps m₀ (writeRepresentation a bs m) := by
  have hw := writeRepresentation_allocations a bs m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wr_enumTypes]; exact h.enums
  · rw [wr_nextId]; exact h.nextId
  · rw [wr_lastAddress]; exact h.last
  · intro j hj; rw [hw.1]; exact h.alloc j hj
  · intro j hj; rw [hw.2.1]; exact h.dead j hj
  · intro x hx; rw [bytes_write_outside _ _ _ _ (.inr (by omega))]; exact h.bytes x hx
  · intro x hx; rw [pointer_find_disjoint _ _ _ _ (.inr (by omega))]; exact h.pbytes x hx

/-- Changing the allocation of an id that the earlier memory did not have keeps it. -/
theorem Keeps.alloc_insert {m₀ m : State} (h : Keeps m₀ m) {j : Int} (hj : m₀.nextId ≤ j)
    (x : Allocation) : Keeps m₀ {m with allocations := m.allocations.insert j x} :=
  ⟨h.enums, h.nextId, h.last, fun j' hj' => by
    rw [Map.lookup_insert_of_key_ne _ _ (show j' ≠ j by omega)]; exact h.alloc j' hj',
    h.dead, h.bytes, h.pbytes⟩

theorem Keeps.alloc_erase {m₀ m : State} (h : Keeps m₀ m) {j : Int} (hj : m₀.nextId ≤ j) :
    Keeps m₀ {m with allocations := m.allocations.erase j} :=
  ⟨h.enums, h.nextId, h.last, fun j' hj' => by
    rw [map_lookup_erase_ne _ (show j' ≠ j by omega)]; exact h.alloc j' hj',
    h.dead, h.bytes, h.pbytes⟩

theorem Keeps.dead_cons {m₀ m : State} (h : Keeps m₀ m) {j : Int} (hj : m₀.nextId ≤ j) :
    Keeps m₀ {m with dead := j :: m.dead} :=
  ⟨h.enums, h.nextId, h.last, h.alloc, fun j' hj' => by
    have : j' ≠ j := by omega
    simpa [this] using h.dead j' hj', h.bytes, h.pbytes⟩

theorem Keeps.lastUsed {m₀ m : State} (h : Keeps m₀ m) (u : Option Int) :
    Keeps m₀ {m with lastUsed := u} :=
  ⟨h.enums, h.nextId, h.last, h.alloc, h.dead, h.bytes, h.pbytes⟩

theorem Keeps.location {m₀ m : State} (h : Keeps m₀ m) (l : Loc) :
    Keeps m₀ {m with currentLocation := l} :=
  ⟨h.enums, h.nextId, h.last, h.alloc, h.dead, h.bytes, h.pbytes⟩

theorem Keeps.stdout {m₀ m : State} (h : Keeps m₀ m) (s : String) :
    Keeps m₀ {m with stdout := s} :=
  ⟨h.enums, h.nextId, h.last, h.alloc, h.dead, h.bytes, h.pbytes⟩

/-- `updateLastAllocation` of a later allocation keeps the earlier objects. -/
theorem Keeps.updateLast {m₀ m : State} (h : Keeps m₀ m) {j : Int} (hj : m.lastUsed = some j)
    (hj0 : m₀.nextId ≤ j) (f : Allocation → Allocation) :
    Keeps m₀ (updateLastAllocation m f) := by
  rcases ha : m.allocations.lookup j with _ | a
  · have : updateLastAllocation m f = m := by unfold updateLastAllocation; simp [hj, ha]
    rw [this]; exact h
  · rw [updateLast_of m f hj ha]; exact h.alloc_insert hj0 _

/-! ## String objects -/

/-- A live array object at `addr` holding the bytes `cs`, plain, at or above the last
allocation, with an id already allocated. -/
structure StrObj (m : State) (id addr : Int) (cs : List Int) : Prop where
  alive : id ∉ m.dead
  alloc : ∃ a, m.allocations.lookup id = some a ∧ a.base = addr ∧ a.size = cs.length ∧
    a.atomic = false
  bytes : ∀ i (h : i < cs.length), readByte (addr + i) m.bytes = some cs[i]
  plain : ∀ i, i < cs.length → m.pointerBytes.lookup (addr + i) = none
  below : id < m.nextId
  above : m.lastAddress ≤ addr

theorem StrObj.keeps {m m' : State} {id addr : Int} {cs : List Int} (h : StrObj m id addr cs)
    (k : Keeps m m') : StrObj m' id addr cs where
  alive := by rw [k.dead id h.below]; exact h.alive
  alloc := by rw [k.alloc id h.below]; exact h.alloc
  bytes i hi := by
    have := h.bytes i hi
    unfold readByte at this ⊢
    rw [k.bytes _ (by have := h.above; omega)]; exact this
  plain i hi := by rw [k.pbytes _ (by have := h.above; omega)]; exact h.plain i hi
  below := lt_of_lt_of_le h.below k.nextId
  above := le_trans k.last h.above

/-- The representation of a string's characters: one plain byte each. -/
def strBytes (cs : List Int) : Representation := cs.map fun c => (some c, none)

theorem layout_charTy (tags : Tags) (ann : List Annot) :
    typeLayout 64 tags (charTy ann) = .ok ⟨1, 1, []⟩ := by
  simp [typeLayout, registeredIntegerLayout, registeredInteger, integerLayout]
  rfl

theorem layout_charArr (tags : Tags) (ann annE : List Annot) (n : Nat) :
    typeLayout 64 tags (charArr ann annE n) = .ok ⟨n, 1, []⟩ := by
  simp [typeLayout, registeredIntegerLayout, registeredInteger, integerLayout]
  rfl

theorem fold_str (f : Representation × State → MemoryValue → Except Failure (Representation × State))
    (s : State) (hf : ∀ acc c, 0 ≤ c ∧ c < 128 →
      f (acc, s) (.integer .char c) = .ok (acc ++ [(some c, none)], s)) :
    ∀ (cs : List Int), (∀ c ∈ cs, 0 ≤ c ∧ c < 128) → ∀ acc : Representation,
      (cs.map (MemoryValue.integer .char)).foldlM f (acc, s) = .ok (acc ++ strBytes cs, s)
  | [], _, acc => by simp [strBytes, pure, Except.pure]
  | c :: cs, hc, acc => by
    rw [List.map_cons, List.foldlM_cons, hf acc c (hc c (by simp))]
    simp only [bind, Except.bind]
    rw [fold_str f s hf cs (fun c h => hc c (by simp [h])) _]
    simp [strBytes]

theorem represent_str (tags : Tags) (s : State) (cs : List Int)
    (hc : ∀ c ∈ cs, 0 ≤ c ∧ c < 128) :
    represent 64 tags (.array (cs.map (.integer .char))) s = .ok (strBytes cs, s) := by
  rw [show (64 : Nat) = 63 + 1 from rfl, represent]
  dsimp only
  rw [fold_str _ s ?_ cs hc []]
  · simp
  · intro acc c hc'
    have : c % 256 = c := Int.emod_eq_of_lt hc'.1 (by omega)
    have hb : -128 ≤ c ∧ c ≤ 127 := by omega
    simp [represent, registeredIntegerLayout, registeredInteger, integerLayout,
      representationBounds, plainBytes, encodeInteger, this, hb, bind, Except.bind, pure, Except.pure]

/-- **Creating a string object**: `create_readonly(1, char[n], array(cs))` of the characters `cs`
(each in `0 … 127`) allocates the object just below the last allocation. -/
theorem createReadOnly_str (tags : Tags) (m : State) (annT annE : List Annot) (cs : List Int)
    (hn : cs ≠ []) (hc : ∀ c ∈ cs, 0 ≤ c ∧ c < 128) (room : (cs.length : Int) < m.lastAddress)
    (fresh : m.nextId ∉ m.dead) (pref : Prefix) :
    ∃ m', createReadOnly tags m 1 (charArr annT annE cs.length)
        (.array (cs.map (.integer .char))) pref =
        .ok (.allocated m.nextId (m.lastAddress - cs.length), m') ∧
      StrObj m' m.nextId (m.lastAddress - cs.length) cs ∧ Keeps m m' ∧
      m'.lastAddress = m.lastAddress - cs.length ∧ m'.nextId = m.nextId + 1 ∧
      m'.dead = m.dead ∧ m'.stdout = m.stdout := by
  -- `cs ≠ []` is not needed: the empty string is created in the same way.
  have _ := hn
  have hpos : ¬ (m.lastAddress - (cs.length : Int) ≤ 0) := by omega
  have halloc : allocateTyped tags m 1 (charArr annT annE cs.length) =
      .ok (.allocated m.nextId (m.lastAddress - cs.length),
        { writeRepresentation (m.lastAddress - cs.length)
            (plainBytes (List.replicate cs.length none)) m with
          nextId := m.nextId + 1
          lastAddress := m.lastAddress - cs.length
          allocations := m.allocations.insert m.nextId
            ({base := m.lastAddress - cs.length, size := cs.length,
              objectType := some (charArr annT annE cs.length)} : Allocation)
          lastUsed := some m.nextId }) := by
    simp only [allocateTyped, layout_charArr, bind, Except.bind, pure, Except.pure]
    simp only [Int.emod_one, Int.sub_zero, Int.toNat_natCast]
    rw [ite_eq_right_of_eq_false _ _ (by simp), ite_eq_right_of_eq_false _ _ (by simpa using hpos)]
    obtain ⟨b, pb, h⟩ := writeRepresentation_shape (m.lastAddress - cs.length)
      (plainBytes (List.replicate cs.length none)) m
    simp only [h]
  set addr := m.lastAddress - (cs.length : Int)
  set A : Allocation :=
    ({base := addr, size := cs.length, objectType := some (charArr annT annE cs.length)} : Allocation)
  set W := writeRepresentation addr (plainBytes (List.replicate cs.length none)) m
  set S1 : State := ({ W with
    nextId := m.nextId + 1
    lastAddress := addr
    allocations := m.allocations.insert m.nextId A
    lastUsed := some m.nextId } : State)
  have hWa := writeRepresentation_allocations addr (plainBytes (List.replicate cs.length none)) m
  have S1dead : S1.dead = m.dead := by simp [S1, W, hWa.2.1]
  have S1look : S1.allocations.lookup m.nextId = some A := Map.lookup_insert _ _ _
  have keepW : Keeps m W := (Keeps.refl m).write _ _ (by simp [plainBytes, addr])
  have keep1 : Keeps m S1 := by
    refine ⟨keepW.enums, ?_, ?_, ?_, keepW.dead, keepW.bytes, keepW.pbytes⟩
    · simp [S1]
    · simp [S1, addr]
    · intro j hj
      simp only [S1]
      rw [Map.lookup_insert_of_key_ne _ _ (show j ≠ m.nextId by omega)]
  have hacc : accessTyped tags S1 (charArr annT annE cs.length) (.allocated m.nextId addr) =
      .ok (m.nextId, addr, cs.length) := by
    simp [accessTyped, layout_charArr, S1dead, fresh, S1look, A, checkAtomic, bind, Except.bind,
      pure, Except.pure]
  have hwr : checkWritable S1 m.nextId = .ok () := by
    simp [checkWritable, S1look, A, pure, Except.pure]
  have hstore : storeTyped tags S1 (charArr annT annE cs.length) (.allocated m.nextId addr)
      (.array (cs.map (.integer .char))) =
      .ok ((addr, cs.length), {writeRepresentation addr (strBytes cs) S1 with lastUsed := some m.nextId}) := by
    simp [storeTyped, hacc, hwr, represent_str tags S1 cs hc, strBytes, bind, Except.bind, pure,
      Except.pure]
  set S2 : State := ({writeRepresentation addr (strBytes cs) S1 with lastUsed := some m.nextId} : State)
  have S2look : S2.allocations.lookup m.nextId = some A := by
    simp [S2, writeRepresentation_allocations, S1look]
  have hfin := updateLast_of S2
    (fun a => {a with readonly := some (readonlyKind pref), readonlyKind := readonlyKind pref})
    rfl S2look
  refine ⟨updateLastAllocation S2
    (fun a => {a with readonly := some (readonlyKind pref), readonlyKind := readonlyKind pref}),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [createReadOnly, halloc, hstore, bind, Except.bind, pure, Except.pure]
  · rw [hfin]
    refine ⟨?_, ⟨_, Map.lookup_insert _ _ _, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · simpa [S2, S1, W, hWa.2.1, writeRepresentation_allocations] using fresh
    · intro i hi
      change readByte (addr + i) (writeRepresentation addr (strBytes cs) S1).bytes = _
      rw [writeRepresentation_bytes, readByte_writeInt _ _ _ i (by simpa [strBytes] using hi)]
      simp [strBytes]
    · intro i hi
      change (writeRepresentation addr (strBytes cs) S1).pointerBytes.lookup (addr + i) = none
      rw [pointer_find_write _ _ _ i (by simpa [strBytes] using hi)]
      simp [strBytes]
    · simp [S2, S1, wr_nextId]
    · simp [S2, S1, wr_lastAddress]
  · exact ((keep1.write addr (strBytes cs) (by simp [strBytes, addr])).lastUsed _).updateLast rfl
      (le_refl _) _
  · rw [hfin]; simp [S2, S1, wr_lastAddress]
  · rw [hfin]; simp [S2, S1, wr_nextId]
  · rw [hfin]; simp [S2, S1, W, writeRepresentation_allocations]
  · rw [hfin]; simp [S2, S1, W, wr_stdout]

theorem access_char_aux (tags : Tags) (ann : List Annot) {m : State} {id addr : Int}
    {cs : List Int} (h : StrObj m id addr cs) (i : Nat) (hi : i < cs.length) :
    accessTyped tags m (charTy ann) (.allocated id (addr + i)) = .ok (id, addr + i, 1) := by
  obtain ⟨a, look, base, size, atomic⟩ := h.alloc
  have hb : a.base ≤ addr + i ∧ addr + i + 1 ≤ a.base + a.size := by omega
  simp [accessTyped, layout_charTy, h.alive, look, hb, checkAtomic, atomic, bind,
    Except.bind, pure, Except.pure]

/-- **Loading a character** of a string object. -/
theorem load_char (tags : Tags) (ann : List Annot) {m : State} {id addr : Int} {cs : List Int}
    (h : StrObj m id addr cs) (i : Nat) (hi : i < cs.length) (hc : 0 ≤ cs[i] ∧ cs[i] < 128) :
    loadTyped tags m (charTy ann) (.allocated id (addr + i)) =
      .ok (.integer .char cs[i], {m with lastUsed := some id}) := by
  have hb := h.bytes i hi
  have hp := h.plain i hi
  have hexp : exposeRead 64 tags m (charTy ann) (addr + i) = m := by
    simp [exposeRead, registeredIntegerLayout, registeredInteger, integerLayout,
      exposeReadBytes, hp]
  have habs : abstractValue 64 tags m (charTy ann) (addr + i) = .ok (.integer .char cs[i]) := by
    have hl := layout_charTy tags ann
    simp only [abstractValue, hl, bind, Except.bind, pure, Except.pure, registeredIntegerLayout,
      registeredInteger, integerLayout]
    have : ¬ 128 ≤ cs[i] := by omega
    simp [fetchBytes, hb, decodeInteger, integerLayout, this]
  unfold loadTyped
  rw [access_char_aux tags ann h i hi]
  simp only [bind, Except.bind, habs, hexp, pure, Except.pure]

/-- The footprint of that load (for the dynamics' access annotation). -/
theorem access_char (tags : Tags) (ann : List Annot) {m : State} {id addr : Int} {cs : List Int}
    (h : StrObj m id addr cs) (i : Nat) (hi : i < cs.length) :
    accessTyped tags m (charTy ann) (.allocated id (addr + i)) = .ok (id, addr + i, 1) :=
  access_char_aux tags ann h i hi

/-- **Shifting a pointer** into a string object by `k` characters, within the object or one past
its end. -/
theorem shift_char (tags : Tags) (ann : List Annot) {m : State} {id addr : Int} {cs : List Int}
    (h : StrObj m id addr cs) (i : Int) (k : Int) (hi : 0 ≤ i + k) (hk : i + k ≤ cs.length) :
    shiftPointer tags m (.allocated id (addr + i)) (charTy ann) k =
      .ok (.allocated id (addr + i + k)) := by
  obtain ⟨a, look, base, size, atomic⟩ := h.alloc
  have hb : a.base ≤ addr + i + k ∧ addr + i + k ≤ a.base + a.size := by omega
  simp [shiftPointer, layout_charTy, look, hb, bind, Except.bind, pure, Except.pure]

/-! ## The format argument object (a pointer) -/

/-- The address of a fresh 8-byte, 8-aligned object below the last allocation. -/
def ptrAddr (m : State) : Int := (m.lastAddress - 8) - (m.lastAddress - 8) % 8

/-- The memory after `create(8, ty)` (`ty` a pointer type), as the dynamics' `create` leaves it
(`Dynamics.memoryRequest`: `allocateTyped`, then the prefix's read-only kind on the new
allocation). -/
def createdPtr (pref : Prefix) (ty : Ctype) (m : State) : State :=
  updateLastAllocation
    { writeRepresentation (ptrAddr m) (plainBytes (List.replicate 8 none)) m with
      nextId := m.nextId + 1
      lastAddress := ptrAddr m
      allocations := m.allocations.insert m.nextId
        ({base := ptrAddr m, size := 8, objectType := some ty} : Allocation)
      lastUsed := some m.nextId }
    fun a => {a with readonlyKind := readonlyKind pref}

/-- A fresh pointer object is allocated below every earlier one. -/
theorem allocate_ptr (tags : Tags) (m : State) (ann : List Annot) (q : Qualifiers) (ref : Ctype)
    (hpos : 0 < ptrAddr m) :
    allocateTyped tags m 8 (.mk ann (.pointer q ref)) = .ok (.allocated m.nextId (ptrAddr m),
      { writeRepresentation (ptrAddr m) (plainBytes (List.replicate 8 none)) m with
        nextId := m.nextId + 1
        lastAddress := ptrAddr m
        allocations := m.allocations.insert m.nextId
          ({base := ptrAddr m, size := 8, objectType := some (.mk ann (.pointer q ref))} : Allocation)
        lastUsed := some m.nextId }) := by
  unfold ptrAddr at hpos ⊢
  have hn : ¬ (m.lastAddress - 8 - (m.lastAddress - 8) % 8 ≤ 0) := by omega
  simp only [allocateTyped, typeLayout, bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right_of_eq_false _ _ (by simp), ite_eq_right_of_eq_false _ _ (by simpa using hn)]
  rw [show (8 : Int).toNat = 8 from rfl]
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape (m.lastAddress - 8 - (m.lastAddress - 8) % 8)
    (plainBytes (List.replicate 8 none)) m
  simp only [h]

/-- A live, writable 8-byte object at or above the last allocation. -/
structure PtrSlot (m : State) (id addr : Int) : Prop where
  alive : id ∉ m.dead
  alloc : ∃ a, m.allocations.lookup id = some a ∧ a.base = addr ∧ a.size = 8 ∧ a.atomic = false ∧
    a.readonly = none
  below : id < m.nextId
  above : m.lastAddress ≤ addr

theorem createdPtr_slot (pref : Prefix) (ty : Ctype) (m : State) (fresh : m.nextId ∉ m.dead) :
    PtrSlot (createdPtr pref ty m) m.nextId (ptrAddr m) := by
  unfold createdPtr
  rw [updateLast_of _ _ rfl (Map.lookup_insert _ _ _)]
  refine ⟨?_, ⟨_, Map.lookup_insert _ _ _, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · simpa [(writeRepresentation_allocations _ _ m).2.1] using fresh
  · simp
  · simp

theorem createdPtr_keeps (pref : Prefix) (ty : Ctype) (m : State) :
    Keeps m (createdPtr pref ty m) := by
  have hW : Keeps m (writeRepresentation (ptrAddr m) (plainBytes (List.replicate 8 none)) m) :=
    (Keeps.refl m).write _ _ (by simp [plainBytes]; unfold ptrAddr; omega)
  unfold createdPtr
  refine Keeps.updateLast ?_ rfl (le_refl _) _
  refine ⟨hW.enums, ?_, ?_, ?_, hW.dead, hW.bytes, hW.pbytes⟩
  · simp
  · simp only; unfold ptrAddr; omega
  · intro j hj
    simp only
    rw [Map.lookup_insert_of_key_ne _ _ (show j ≠ m.nextId by omega)]

theorem createdPtr_facts (pref : Prefix) (ty : Ctype) (m : State) :
    (createdPtr pref ty m).lastAddress = ptrAddr m ∧ (createdPtr pref ty m).nextId = m.nextId + 1 ∧
      (createdPtr pref ty m).dead = m.dead ∧ (createdPtr pref ty m).stdout = m.stdout ∧
      (createdPtr pref ty m).enumTypes = m.enumTypes := by
  unfold createdPtr
  rw [updateLast_of _ _ rfl (Map.lookup_insert _ _ _)]
  simp [wr_enumTypes, wr_stdout, (writeRepresentation_allocations _ _ m).2.1]

theorem ptrAddr_bounds (m : State) : m.lastAddress - 15 ≤ ptrAddr m ∧ ptrAddr m + 8 ≤ m.lastAddress := by
  unfold ptrAddr; omega

/-- The bytes of a stored pointer with allocation provenance. -/
def ptrBytes (pid paddr : Int) : Representation :=
  (encodeInteger 8 paddr).zipIdx.map fun (b, i) => (b, some (some pid, i))

/-- A pointer object holding the pointer `allocated pid paddr`. -/
structure PtrObj (m : State) (id addr pid paddr : Int) : Prop where
  slot : PtrSlot m id addr
  bytes : ∀ i : Nat, i < 8 → readByte (addr + i) m.bytes = some ((paddr / 256 ^ i) % 256)
  prov : ∀ i : Nat, i < 8 → m.pointerBytes.lookup (addr + i) = some (some pid, i)
  range : 0 < paddr ∧ paddr < 18446744073709551616

theorem PtrSlot.keeps {m m' : State} {id addr : Int} (h : PtrSlot m id addr) (k : Keeps m m') :
    PtrSlot m' id addr where
  alive := by rw [k.dead id h.below]; exact h.alive
  alloc := by rw [k.alloc id h.below]; exact h.alloc
  below := lt_of_lt_of_le h.below k.nextId
  above := le_trans k.last h.above

theorem PtrObj.keeps {m m' : State} {id addr pid paddr : Int} (h : PtrObj m id addr pid paddr)
    (k : Keeps m m') : PtrObj m' id addr pid paddr where
  slot := h.slot.keeps k
  bytes i hi := by
    have := h.bytes i hi
    unfold readByte at this ⊢
    rw [k.bytes _ (by have := h.slot.above; omega)]; exact this
  prov i hi := by rw [k.pbytes _ (by have := h.slot.above; omega)]; exact h.prov i hi
  range := h.range

theorem access_ptr_aux (tags : Tags) (ann : List Annot) (q : Qualifiers) (ref : Ctype) {m : State}
    {id addr : Int} (h : PtrSlot m id addr) :
    accessTyped tags m (.mk ann (.pointer q ref)) (.allocated id addr) = .ok (id, addr, 8) := by
  obtain ⟨alive, ⟨a, look, base, size, atomic, _⟩, _, _⟩ := h
  simp [accessTyped, typeLayout, alive, look, base, size, checkAtomic, atomic, bind,
    Except.bind, pure, Except.pure]

/-- **Storing a pointer** into a pointer object. -/
theorem store_ptr (tags : Tags) (ann : List Annot) (q : Qualifiers) (ref : Ctype) {m : State}
    {id addr : Int} (h : PtrSlot m id addr) {pid paddr : Int}
    (range : 0 < paddr ∧ paddr < 18446744073709551616) :
    storeTyped tags m (.mk ann (.pointer q ref)) (.allocated id addr)
        (.pointer ref (.allocated pid paddr)) =
      .ok ((addr, 8), {writeRepresentation addr (ptrBytes pid paddr) m with lastUsed := some id}) ∧
    PtrObj {writeRepresentation addr (ptrBytes pid paddr) m with lastUsed := some id} id addr pid paddr := by
  have hacc := access_ptr_aux tags ann q ref h
  obtain ⟨alive, ⟨a, look, base, size, atomic, ro⟩, below, above⟩ := h
  have hr : represent 64 tags (.pointer ref (.allocated pid paddr)) m =
      .ok (ptrBytes pid paddr, m) := by
    simp [represent, representPointer, encodeAddress, range.2, show 0 ≤ paddr by omega, ptrBytes,
      bind, Except.bind, pure, Except.pure]
  have hw := writeRepresentation_allocations addr (ptrBytes pid paddr) m
  have hfst : (ptrBytes pid paddr).map Prod.fst = encodeInteger 8 paddr := by
    simp [ptrBytes, List.map_map, Function.comp_def]
  refine ⟨?_, ⟨⟨?_, ⟨a, ?_, base, size, atomic, ro⟩, ?_, ?_⟩, ?_, ?_, range⟩⟩
  · simp [storeTyped, hacc, checkWritable, look, ro, hr, bind, Except.bind, pure, Except.pure,
      ptrBytes, encodeInteger_length]
  · simpa [hw.2.1] using alive
  · simpa [hw.1] using look
  · simpa [wr_nextId] using below
  · simpa [wr_lastAddress] using above
  · intro i hi
    change readByte (addr + i) (writeRepresentation addr (ptrBytes pid paddr) m).bytes = _
    rw [writeRepresentation_bytes, hfst,
      readByte_writeInt _ _ _ i (by rw [encodeInteger_length]; exact hi),
      encodeInteger_getElem 8 paddr i hi]
  · intro i hi
    exact pointer_copy_lookup m addr paddr (some pid) i hi

theorem access_ptr (tags : Tags) (ann : List Annot) (q : Qualifiers) (ref : Ctype) {m : State}
    {id addr : Int} (h : PtrSlot m id addr) :
    accessTyped tags m (.mk ann (.pointer q ref)) (.allocated id addr) = .ok (id, addr, 8) :=
  access_ptr_aux tags ann q ref h

/-- What a store into a later object keeps: the earlier objects, when the object lies below them. -/
theorem store_ptr_keeps {m₀ m : State} (k : Keeps m₀ m) {addr : Int} (below : addr + 8 ≤ m₀.lastAddress)
    (id pid paddr : Int) :
    Keeps m₀ {writeRepresentation addr (ptrBytes pid paddr) m with lastUsed := some id} :=
  (k.write addr (ptrBytes pid paddr) (by simp [ptrBytes, encodeInteger_length]; omega)).lastUsed _

/-- **Loading the pointer** back. -/
theorem load_ptr (tags : Tags) (ann : List Annot) (q : Qualifiers) (ref : Ctype)
    (hobj : (match ref with | .mk _ (.function ..) => false | _ => true) = true) {m : State}
    {id addr pid paddr : Int} (h : PtrObj m id addr pid paddr) :
    loadTyped tags m (.mk ann (.pointer q ref)) (.allocated id addr) =
      .ok (.pointer ref (.allocated pid paddr), {m with lastUsed := some id}) := by
  have hacc := access_ptr_aux tags ann q ref h.slot
  have hf : fetchBytes 8 addr m.bytes = encodeInteger 8 paddr :=
    fetchBytes_eq_encode 8 addr paddr m.bytes h.bytes
  have hdec : decodeInteger (fetchBytes 8 addr m.bytes) = some paddr := by
    rw [hf, decode_encode]
    have := h.range
    congr 1
    exact Int.emod_eq_of_lt (by omega) (by norm_num; omega)
  have hptr : abstractPointer m ref addr paddr = .ok (.allocated pid paddr) := by
    have first : m.pointerBytes.lookup addr = some (some pid, 0) := by simpa using h.prov 0 (by omega)
    have intact : (List.range 8).all (fun i =>
        m.pointerBytes.lookup (addr + i) == some (some pid, i)) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      simp only [List.mem_range] at hi
      simp [h.prov i hi]
    have hne : paddr ≠ 0 := by have := h.range; omega
    clear hacc hf hdec h
    rcases ref with ⟨ann', kind⟩
    cases kind <;> simp_all [abstractPointer, pure, Except.pure]
  simp [loadTyped, hacc, abstractValue, typeLayout, hdec, hptr, exposeRead, bind, Except.bind,
    pure, Except.pure]

/-- The memory after killing the object `id`. -/
def killed (m : State) (id : Int) : State :=
  { m with allocations := m.allocations.erase id, dead := id :: m.dead, lastUsed := some id }

theorem Keeps.killed {m₀ m : State} (h : Keeps m₀ m) {j : Int} (hj : m₀.nextId ≤ j) :
    Keeps m₀ (killed m j) :=
  ((h.alloc_erase hj).dead_cons hj).lastUsed _

/-- **Killing** the pointer object. -/
theorem kill_ptr (tags : Tags) (ann : List Annot) (q : Qualifiers) (ref : Ctype) {m : State}
    {id addr : Int} (h : PtrSlot m id addr) :
    killTyped tags m (.mk ann (.pointer q ref)) (.allocated id addr) =
      .ok ((), killed m id) := by
  have hacc := access_ptr_aux tags ann q ref h
  obtain ⟨_, ⟨a, look, base, _⟩, _, _⟩ := h
  simp [killTyped, hacc, look, base, killed, bind, Except.bind, pure, Except.pure]

end Silmaril.Compile.Core.Verified.StrMem
