module

public import Silmaril.Cerberus.Mem.IntSlots.Defs
public import Silmaril.Machine.CBackend.Lir.Semantics.Defs

/-! # Core concrete memory in Lir linear memory

The relation between the Core memory (`Mem.Concrete.State`, the byte map of the dynamics) and
the Lir linear memory of a compiled program, for objects whose address escapes (`&x`, arrays,
structs). Each tracked Core object (`Obj`: allocation id, Core base address, size) is placed at
a Lir address `lir`; a Core pointer `(id, a)` into it is the Lir word `lir + (a - base)`. Core
addresses depend on the startup (argument strings are allocated first), so the placement is a
map per object, not one offset.

`Rel m lm objs`:
* every object is live, writable and non-atomic in `m`, with the recorded base and size, and fits
  in `lm`;
* its bytes agree: a specified Core byte `some v` is the Lir byte with value `v`; an unspecified
  Core byte (`none`: fresh or padding) allows any Lir byte;
* its bytes carry no pointer-copy metadata (integers only; pointer bytes are the next step);
* objects are pairwise apart (distinct ids, disjoint Core and Lir ranges), at or above the Core
  allocation cursor, with ids below `nextId`.

Proved:
* `store`, `load`: integer stores and loads of every enabled width (`char`, `short`, `int`,
  `long`, signed or unsigned: 1, 2, 4 or 8 bytes) at any in-bounds address of an object (an
  array element, a struct member) are the Lir store and load of that width (sign- or
  zero-extending) at the placed address, and keep the relation;
* `allocate`: a fresh object is placed at any fresh Lir range; `kill`: the others stay placed;
* the bookkeeping fields (`lastUsed`, `currentLocation`) that the dynamics changes around actions;
* pointers (`PtrRel`): Core's `array_shift`/`member_shift` are word additions (`PtrRel.shift`),
  Lir loads and stores through a pointer register hit the placed address (`exec_load`,
  `exec_store`), equality of pointers into one object is word equality (`word_eq_iff`), and a
  pointer into an object placed above 0 is not null (`word_ne_zero`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.MemRel

open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete
open Silmaril.Machine

/-- A Core byte and a Lir byte agree: an unspecified Core byte allows every Lir byte. -/
def ByteRel (b : Byte) (x : BitVec 8) : Prop := ∀ v, b = some v → (x.toNat : Int) = v

/-- A Core object placed in Lir memory. -/
structure Obj where
  id : Int
  base : Int
  lir : Nat
  size : Nat

/-- The Lir address of the Core address `a` of object `o`. -/
def Obj.addr (o : Obj) (a : Int) : Nat := o.lir + (a - o.base).toNat

/-- Object `o` of the Core memory `m` is placed in the Lir memory `lm`. -/
structure Placed (m : State) (lm : Lir.Memory) (o : Obj) : Prop where
  alive : o.id ∉ m.dead
  found : ∃ a, m.allocations.lookup o.id = some a ∧ a.base = o.base ∧ a.size = (o.size : Int) ∧
    a.atomic = false ∧ a.readonly = none
  fits : o.lir + o.size ≤ lm.size
  bytes : ∀ i : Nat, i < o.size → ByteRel (readByte (o.base + i) m.bytes) (lm.bytes (o.lir + i))
  plain : ∀ i : Nat, i < o.size → m.pointerBytes.lookup (o.base + i) = none

/-- Two objects have distinct ids and disjoint ranges in Core and in Lir memory. -/
def Apart (o o' : Obj) : Prop :=
  o.id ≠ o'.id ∧
  (o.base + o.size ≤ o'.base ∨ o'.base + o'.size ≤ o.base) ∧
  (o.lir + o.size ≤ o'.lir ∨ o'.lir + o'.size ≤ o.lir)

theorem Apart.symm {o o' : Obj} (h : Apart o o') : Apart o' o :=
  ⟨fun e => h.1 e.symm, h.2.1.symm, h.2.2.symm⟩

/-- **The memory relation.** -/
structure Rel (m : State) (lm : Lir.Memory) (objs : List Obj) : Prop where
  placed : ∀ o ∈ objs, Placed m lm o
  apart : objs.Pairwise Apart
  below : ∀ o ∈ objs, m.lastAddress ≤ o.base
  fresh : ∀ o ∈ objs, o.id < m.nextId

/-- No object is placed yet: the relation at startup, before the first `create`. -/
theorem Rel.nil (m : State) (lm : Lir.Memory) : Rel m lm [] :=
  ⟨by simp, .nil, by simp, by simp⟩

theorem Rel.apart_of {m : State} {lm : Lir.Memory} {objs : List Obj} (h : Rel m lm objs)
    {o o' : Obj} (ho : o ∈ objs) (ho' : o' ∈ objs) (ne : o ≠ o') : Apart o o' :=
  haveI : Std.Symm Apart := ⟨fun _ _ e => e.symm⟩
  h.apart.forall ho ho' ne

/-- A Core pointer and the Lir word that represents it: null is `0`; a pointer `(id, a)` into a
placed object is `lir + (a - base)` modulo `2^64`, also out of bounds (Core's pure
`array_shift` and `member_shift` do not check bounds; accesses do). -/
def PtrRel (objs : List Obj) : Pointer → Lir.Word → Prop
  | .null _, w => w = 0
  | .allocated id a, w => ∃ o ∈ objs, o.id = id ∧ w = BitVec.ofInt 64 (o.lir + (a - o.base))
  | _, _ => False

/-! ## Bookkeeping fields -/

/-- The relation reads only bytes, copy metadata, allocations, lifetimes, the cursor and the
next id. -/
theorem Rel.congr {m m' : State} {lm : Lir.Memory} {objs : List Obj} (h : Rel m lm objs)
    (hb : m'.bytes = m.bytes) (hp : m'.pointerBytes = m.pointerBytes)
    (ha : m'.allocations = m.allocations) (hd : m'.dead = m.dead)
    (hl : m'.lastAddress = m.lastAddress) (hn : m'.nextId = m.nextId) : Rel m' lm objs := by
  refine ⟨fun o ho => ?_, h.apart, fun o ho => hl ▸ h.below o ho, fun o ho => hn ▸ h.fresh o ho⟩
  obtain ⟨alive, found, fits, bytes, plain⟩ := h.placed o ho
  exact ⟨hd ▸ alive, ha ▸ found, fits, hb ▸ bytes, hp ▸ plain⟩

theorem Rel.lastUsed {m : State} {lm : Lir.Memory} {objs : List Obj} (h : Rel m lm objs)
    (u : Option Int) : Rel {m with lastUsed := u} lm objs :=
  h.congr rfl rfl rfl rfl rfl rfl

theorem Rel.currentLocation {m : State} {lm : Lir.Memory} {objs : List Obj} (h : Rel m lm objs)
    (l : Loc) : Rel {m with currentLocation := l} lm objs :=
  h.congr rfl rfl rfl rfl rfl rfl

/-! ## Core byte writes -/

theorem read_writeInt_at (a : Int) (bs : List Byte) (xs : Map Int Byte) (i : Nat)
    (hi : i < bs.length) : readByte (a + i) (writeInt a bs xs) = bs[i] := by
  induction bs generalizing a i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [writeInt, read_write_same]
    | succ i =>
      simp only [writeInt]
      rw [read_write_other _ _ _ _ (by push_cast; omega)]
      have := ih (a + 1) i (by simpa using hi)
      rw [show a + ((i + 1 : Nat) : Int) = a + 1 + i by push_cast; ring, this]
      simp

theorem pointerBytes_write_outside (a b : Int) (bs : List Byte) (s : State)
    (h : b < a ∨ a + bs.length ≤ b) :
    (writeRepresentation a (plainBytes bs) s).pointerBytes.lookup b = s.pointerBytes.lookup b := by
  induction bs generalizing a with
  | nil => rfl
  | cons x bs ih =>
    simp only [plainBytes, List.map_cons, writeRepresentation]
    simp only [List.length_cons] at h
    simp only [Map.lookup, Map.erase]
    rw [Finmap.lookup_erase_ne (fun e => by change b = a at e; omega)]
    have := ih (a + 1) (by omega)
    simpa [plainBytes, Map.lookup] using this

theorem pointerBytes_write_inside (a : Int) (bs : List Byte) (s : State) (i : Nat)
    (hi : i < bs.length) :
    (writeRepresentation a (plainBytes bs) s).pointerBytes.lookup (a + i) = none := by
  induction bs generalizing a i with
  | nil => simp at hi
  | cons x bs ih =>
    simp only [plainBytes, List.map_cons, writeRepresentation]
    cases i with
    | zero =>
      simp only [Map.lookup, Map.erase]
      have e : MapKey.key (a + ((0 : Nat) : Int)) = MapKey.key a := by
        change a + ((0 : Nat) : Int) = a
        simp
      rw [e]
      exact Finmap.lookup_erase _ _
    | succ i =>
      have := ih (a + 1) i (by simpa using hi)
      simp only [plainBytes] at this
      rw [show a + ((i + 1 : Nat) : Int) = a + 1 + i by push_cast; ring]
      simp only [Map.lookup, Map.erase] at this ⊢
      rw [Finmap.lookup_erase_ne (fun e => by change a + 1 + i = a at e; omega)]
      exact this

/-! ## Little-endian bytes -/

/-- Byte `i` of the `w`-byte representation of `n`. -/
theorem encodeInteger_get (w : Nat) (n : Int) (i : Nat) (hi : i < w) :
    (encodeInteger w n)[i]'(by rw [encodeInteger_length]; exact hi) = some (n / 256 ^ i % 256) := by
  induction w generalizing n i with
  | zero => omega
  | succ w ih =>
    cases i with
    | zero => simp [encodeInteger]
    | succ i =>
      simp only [encodeInteger, List.getElem_cons_succ]
      rw [ih (n / 256) i (by omega), Int.ediv_ediv_of_nonneg (by omega), pow_succ, mul_comm]

/-- Byte `i` of the word of `n`. -/
theorem wordByte_ofInt (n : Int) (i : Nat) (hi : i < 8) :
    ((LittleEndian.wordByte (BitVec.ofInt 64 n) i).toNat : Int) = n / 256 ^ i % 256 := by
  simp only [LittleEndian.wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
  obtain _ | _ | _ | _ | _ | _ | _ | _ | i := i <;> push_cast <;> omega

/-- The value of `n` little-endian bytes from `addr`. -/
def leVal (bytes : Nat → Lir.Byte) (addr : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (bytes addr).toNat + 256 * leVal bytes (addr + 1) n

theorem leVal_lt (bytes : Nat → Lir.Byte) (addr n : Nat) : leVal bytes addr n < 256 ^ n := by
  induction n generalizing addr with
  | zero => simp [leVal]
  | succ n ih =>
    simp only [leVal, Nat.pow_succ]
    have := (bytes addr).isLt
    have := ih (addr + 1)
    omega

theorem readLE_toNat (bytes : Nat → Lir.Byte) (addr n : Nat) (hn : n ≤ 8) :
    (Lir.readLE bytes addr n).toNat = leVal bytes addr n := by
  induction n generalizing addr with
  | zero => simp [Lir.readLE, leVal]
  | succ n ih =>
    simp only [Lir.readLE, leVal]
    have ih' := ih (addr + 1) (by omega)
    have hbound := leVal_lt bytes (addr + 1) n
    have hpow : 256 ^ n ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have hx := (bytes addr).isLt
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, ih', BitVec.toNat_setWidth]
    have e1 : (bytes addr).toNat % 2 ^ 64 = (bytes addr).toNat := by omega
    have e2 : leVal bytes (addr + 1) n <<< 8 % 2 ^ 64 = leVal bytes (addr + 1) n <<< 8 := by
      rw [Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt
      calc _ < 256 ^ n * 2 ^ 8 := by apply Nat.mul_lt_mul_of_pos_right hbound; decide
        _ ≤ 256 ^ 7 * 2 ^ 8 := Nat.mul_le_mul_right _ hpow
        _ = 2 ^ 64 := by decide
    rw [e1, e2, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hx), Nat.shiftLeft_eq]
    omega

/-- Specified Core bytes related to Lir bytes decode to the Lir little-endian value. -/
theorem decode_leVal (xs : Map Int Byte) (bytes : Nat → Lir.Byte) (w : Nat) (a : Int) (addr : Nat)
    (hb : ∀ k : Nat, k < w → ByteRel (readByte (a + k) xs) (bytes (addr + k))) {u : Int}
    (hu : decodeInteger (fetchBytes w a xs) = some u) : (leVal bytes addr w : Int) = u := by
  induction w generalizing a addr u with
  | zero => simpa [fetchBytes, decodeInteger, leVal] using hu
  | succ w ih =>
    simp only [fetchBytes, decodeInteger, bind, Option.bind] at hu
    have h0 := hb 0 (by omega)
    simp only [Nat.cast_zero, Int.add_zero, Nat.add_zero] at h0
    revert hu
    cases r : readByte a xs with
    | none => simp
    | some b =>
      cases d : decodeInteger (fetchBytes w (a + 1) xs) with
      | none => simp
      | some y =>
        simp only [pure, Option.some.injEq]
        rintro rfl
        have := ih (a + 1) (addr + 1) (fun k hk => by
          have := hb (k + 1) (by omega)
          rwa [show a + ((k + 1 : Nat) : Int) = a + 1 + k by push_cast; ring,
            show addr + (k + 1) = addr + 1 + k by omega] at this) d
        rw [r] at h0
        simp only [leVal]
        push_cast
        rw [h0 b rfl, this]

/-! ## Integer types -/

/-- The enabled integer widths, in bytes. -/
def GoodWidth (w : Nat) : Prop := w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8

/-- The Lir access of `w` bytes. -/
def lirWidth : Nat → Lir.Width
  | 1 => .b1
  | 2 => .b2
  | 4 => .b4
  | _ => .b8

theorem lirWidth_bytes {w : Nat} (hw : GoodWidth w) : (lirWidth w).bytes = w := by
  rcases hw with rfl | rfl | rfl | rfl <;> rfl

/-- The C integer type `ity`, with any annotations. -/
def intTy (ann : List Annot) (ity : IntegerType) : Ctype := .mk ann (.basic (.integer ity))

theorem layout_intTy (tags : Tags) (ann : List Annot) {ity : IntegerType} {w : Nat} {sg : Bool}
    (hl : registeredIntegerLayout tags ity = some (w, sg)) :
    typeLayout 64 tags (intTy ann ity) = .ok ⟨w, w, []⟩ := by
  simp [typeLayout, intTy, hl, pure, Except.pure]

/-- An integer access inside a placed object. -/
theorem access_intTy (tags : Tags) (ann : List Annot) {ity : IntegerType} {w : Nat} {sg : Bool}
    (hl : registeredIntegerLayout tags ity = some (w, sg)) {m : State} {lm : Lir.Memory} {o : Obj}
    (hp : Placed m lm o) {a : Int} (lo : o.base ≤ a) (hi : a + w ≤ o.base + o.size) :
    accessTyped tags m (intTy ann ity) (.allocated o.id a) = .ok (o.id, a, w) := by
  obtain ⟨alive, ⟨al, look, base, size, atomic, _⟩, _, _, _⟩ := hp
  have hb : al.base ≤ a ∧ a + w ≤ al.base + al.size := by rw [base, size]; omega
  simp [accessTyped, layout_intTy tags ann hl, alive, look, hb, checkAtomic, atomic, bind,
    Except.bind, pure, Except.pure]

theorem writeRepresentation_fields (a : Int) (bs : Representation) (s : State) :
    (writeRepresentation a bs s).lastAddress = s.lastAddress ∧
    (writeRepresentation a bs s).nextId = s.nextId := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape a bs s
  rw [h]; exact ⟨rfl, rfl⟩

/-! ## Stores -/

/-- The Core state after a store of the `w`-byte integer `n` at `a` into allocation `id`. -/
def stored (m : State) (id a : Int) (w : Nat) (n : Int) : State :=
  {writeRepresentation a (plainBytes (encodeInteger w n)) m with lastUsed := some id}

/-- The Lir memory after a `w`-byte store. -/
def storedLir (lm : Lir.Memory) (addr w : Nat) (v : Lir.Word) : Lir.Memory :=
  {lm with bytes := Lir.writeLE lm.bytes addr w v}

/-- **An integer store** inside a placed object is the Lir store of the same width at its placed
address, and keeps the relation. -/
theorem store (tags : Tags) (ann : List Annot) {ity : IntegerType} {w : Nat} {sg : Bool}
    (hl : registeredIntegerLayout tags ity = some (w, sg)) (hw : GoodWidth w)
    {m : State} {lm : Lir.Memory} {objs : List Obj} {o : Obj} {a n : Int} (h : Rel m lm objs)
    (ho : o ∈ objs) (lo : o.base ≤ a) (hi : a + w ≤ o.base + o.size)
    (hn : (representationBounds w sg).1 ≤ n ∧ n ≤ (representationBounds w sg).2) :
    storeTyped tags m (intTy ann ity) (.allocated o.id a) (.integer ity n) =
      .ok ((a, w), stored m o.id a w n) ∧
    lm.store (lirWidth w) (o.addr a) (BitVec.ofInt 64 n) =
      some (storedLir lm (o.addr a) w (BitVec.ofInt 64 n)) ∧
    Rel (stored m o.id a w n) (storedLir lm (o.addr a) w (BitVec.ofInt 64 n)) objs := by
  have hp := h.placed o ho
  have hacc := access_intTy tags ann hl hp lo hi
  have hw8 : w ≤ 8 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨_, ⟨al, look, _, _, _, ro⟩, fits, _, _⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · have hr : represent 64 tags (.integer ity n) m = .ok (plainBytes (encodeInteger w n), m) := by
      simp [represent, hl, hn, pure, Except.pure]
    simp [storeTyped, hacc, checkWritable, look, ro, hr, bind, Except.bind, pure, Except.pure,
      plainBytes, encodeInteger_length, stored]
  · have hb : lm.InBounds (o.addr a) (lirWidth w) := by
      simp only [Lir.Memory.InBounds, lirWidth_bytes hw, Obj.addr]; omega
    simp [Lir.Memory.store, hb, storedLir, lirWidth_bytes hw]
  · have wa := writeRepresentation_allocations a (plainBytes (encodeInteger w n)) m
    have wf := writeRepresentation_fields a (plainBytes (encodeInteger w n)) m
    have wb : (stored m o.id a w n).bytes = writeInt a (encodeInteger w n) m.bytes := by
      simp [stored, writeRepresentation_bytes, plainBytes, Function.comp_def]
    refine ⟨fun o' ho' => ?_, h.apart, fun o' ho' => ?_, fun o' ho' => ?_⟩
    · obtain ⟨alive', found', fits', bytes', plain'⟩ := h.placed o' ho'
      have hsame : ∀ i : Nat, i < o'.size → a ≤ o'.base + i → o'.base + i < a + w → o' = o := by
        intro i hi' h1 h2
        by_contra ne
        obtain ⟨_, hc, _⟩ := h.apart_of ho' ho ne
        omega
      refine ⟨by simpa [stored, wa.2.1] using alive', by simpa [stored, wa.1] using found',
        fits', fun i hi' => ?_, fun i hi' => ?_⟩
      · rw [wb]
        by_cases hc : a ≤ o'.base + i ∧ o'.base + i < a + w
        · obtain rfl := hsame i hi' hc.1 hc.2
          obtain ⟨k, hk⟩ : ∃ k : Nat, o'.base + i = a + k := ⟨(o'.base + i - a).toNat, by omega⟩
          have hkw : k < w := by omega
          rw [hk, read_writeInt_at _ _ _ _ (by rw [encodeInteger_length]; exact hkw),
            encodeInteger_get w n k hkw]
          intro v hv
          cases hv
          simp only [storedLir, Lir.writeLE, Obj.addr]
          rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
            show o'.lir + i - (o'.lir + (a - o'.base).toNat) = k by omega]
          exact wordByte_ofInt n k (by omega)
        · rw [read_outside_write _ _ _ _ (by rw [encodeInteger_length]; omega)]
          have hl' : ¬ (o.addr a ≤ o'.lir + i ∧ o'.lir + i < o.addr a + w) := by
            by_cases e : o' = o
            · subst e; simp only [Obj.addr]; omega
            · obtain ⟨_, _, hc'⟩ := h.apart_of ho' ho e
              simp only [Obj.addr]; omega
          simp only [storedLir, Lir.writeLE, ite_eq_right_of_eq_false _ _ (eq_false hl')]
          exact bytes' i hi'
      · by_cases hc : a ≤ o'.base + i ∧ o'.base + i < a + w
        · obtain ⟨k, hk⟩ : ∃ k : Nat, o'.base + i = a + k := ⟨(o'.base + i - a).toNat, by omega⟩
          simp only [stored]
          rw [hk]
          exact pointerBytes_write_inside a _ m k (by rw [encodeInteger_length]; omega)
        · simp only [stored]
          rw [pointerBytes_write_outside _ _ _ _ (by rw [encodeInteger_length]; omega)]
          exact plain' i hi'
    · simpa [stored, wf.1] using h.below o' ho'
    · simpa [stored, wf.2] using h.fresh o' ho'

/-! ## Loads -/

/-- The value Core reads from `w` bytes of unsigned value `u`. -/
def valueOf (w : Nat) (sg : Bool) (u : Int) : Int :=
  if sg && u ≥ (256 : Int) ^ w / 2 then u - 256 ^ w else u

/-- The Lir extension of a load of signedness `sg`. -/
def lirExt (sg : Bool) : Lir.Ext := if sg then .sign else .zero

theorem exposeReadBytes_plain (s : State) (addr : Int) (w : Nat)
    (h : ∀ i : Nat, i < w → s.pointerBytes.lookup (addr + i) = none) :
    exposeReadBytes s addr w = s := by
  unfold exposeReadBytes
  have key : ∀ l : List Int, (∀ i ∈ l, s.pointerBytes.lookup (addr + i) = none) → l.foldl (fun s i =>
      match (s.pointerBytes.lookup (addr+i)).bind (·.1) with
      | none => s
      | some id => match s.allocations.lookup id with
        | none => s
        | some a => {s with allocations := s.allocations.insert id {a with exposed := true}}) s = s := by
    intro l hl
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldl_cons]
      rw [hl i (by simp)]
      exact ih (fun j hj => hl j (by simp [hj]))
  refine key _ (fun i hi => ?_)
  simp at hi
  obtain ⟨k, hk, rfl⟩ := hi
  exact h k hk

/-- **An integer load** of specified bytes inside a placed object is the Lir load of the same
width and signedness at its placed address; the relation survives the Core state change. -/
theorem load (tags : Tags) (ann : List Annot) {ity : IntegerType} {w : Nat} {sg : Bool}
    (hl : registeredIntegerLayout tags ity = some (w, sg)) (hw : GoodWidth w)
    {m : State} {lm : Lir.Memory} {objs : List Obj} {o : Obj} {a u : Int} (h : Rel m lm objs)
    (ho : o ∈ objs) (lo : o.base ≤ a) (hi : a + w ≤ o.base + o.size)
    (hu : decodeInteger (fetchBytes w a m.bytes) = some u) :
    loadTyped tags m (intTy ann ity) (.allocated o.id a) =
      .ok (.integer ity (valueOf w sg u), {m with lastUsed := some o.id}) ∧
    lm.load (lirWidth w) (lirExt sg) (o.addr a) = some (BitVec.ofInt 64 (valueOf w sg u)) := by
  have hp := h.placed o ho
  have hacc := access_intTy tags ann hl hp lo hi
  have hw8 : w ≤ 8 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨_, _, fits, bytes, plain⟩ := hp
  obtain ⟨d, hd⟩ : ∃ d : Nat, a = o.base + d := ⟨(a - o.base).toNat, by omega⟩
  have hb (k : Nat) (hk : k < w) :
      ByteRel (readByte (a + k) m.bytes) (lm.bytes (o.addr a + k)) := by
    have := bytes (d + k) (by omega)
    rwa [show o.base + ((d + k : Nat) : Int) = a + k by push_cast; omega,
      show o.lir + (d + k) = o.addr a + k by simp only [Obj.addr]; omega] at this
  have hpl (k : Nat) (hk : k < w) : m.pointerBytes.lookup (a + k) = none := by
    have := plain (d + k) (by omega)
    rwa [show o.base + ((d + k : Nat) : Int) = a + k by push_cast; omega] at this
  have hle := decode_leVal m.bytes lm.bytes w a (o.addr a) hb hu
  have hlt := leVal_lt lm.bytes (o.addr a) w
  refine ⟨?_, ?_⟩
  · have hexp : exposeRead 64 tags m (intTy ann ity) a = m := by
      simp only [exposeRead, intTy, hl]
      exact exposeReadBytes_plain m a w hpl
    have habs : abstractValue 64 tags m (intTy ann ity) a = .ok (.integer ity (valueOf w sg u)) := by
      have hl' := layout_intTy tags ann hl
      unfold intTy at hl' ⊢
      simp only [abstractValue, hl', bind, Except.bind, pure, Except.pure, hl,
        show ((w : Int).toNat) = w from rfl, hu, valueOf]
    unfold loadTyped
    rw [hacc]
    simp only [bind, Except.bind, habs, hexp, pure, Except.pure]
  · have hin : lm.InBounds (o.addr a) (lirWidth w) := by
      simp only [Lir.Memory.InBounds, lirWidth_bytes hw, Obj.addr]
      omega
    simp only [Lir.Memory.load, hin, ite_true, Option.some.injEq, lirWidth_bytes hw]
    have hraw := readLE_toNat lm.bytes (o.addr a) w hw8
    cases sg
    · apply BitVec.eq_of_toNat_eq
      simp only [lirExt, Bool.false_eq_true, ite_false, Lir.extend, valueOf, Bool.false_and,
        BitVec.toNat_ofInt]
      rw [hraw]
      rcases hw with rfl | rfl | rfl | rfl <;> norm_num at hlt ⊢ <;> omega
    · apply BitVec.eq_of_toInt_eq
      simp only [lirExt, ite_true, Lir.extend, valueOf, Bool.true_and]
      rcases hw with rfl | rfl | rfl | rfl <;>
      · rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt,
          BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth, hraw]
        simp only [lirWidth, Lir.Width.bytes] at hlt ⊢
        norm_num at hlt ⊢
        simp only [Int.bmod]
        split <;> split <;> omega

/-! ## Allocation and kill -/

/-- **Allocation.** A successful Core `create` of a non-atomic object of layout `l` is placed at
any Lir range `lir … lir + size` that fits and is apart from the placed objects. The fresh
object's bytes are unspecified, so any Lir bytes agree with them. -/
theorem allocate {tags : Tags} {m m' : State} {lm : Lir.Memory} {objs : List Obj} {align : Int}
    {ty : Ctype} {l : TypeLayout} {p : Pointer} (h : Rel m lm objs)
    (hl : typeLayout 64 tags ty = .ok l) (hsz : 0 ≤ l.size)
    (hat : ∀ ann t, ty ≠ .mk ann (.atomic t)) (hdead : m.nextId ∉ m.dead)
    (lir : Nat) (fits : lir + l.size.toNat ≤ lm.size)
    (apartL : ∀ o ∈ objs, lir + l.size.toNat ≤ o.lir ∨ o.lir + o.size ≤ lir)
    (hk : allocateTyped tags m align ty = .ok (p, m')) :
    ∃ addr, p = .allocated m.nextId addr ∧
      Rel m' lm (⟨m.nextId, addr, lir, l.size.toNat⟩ :: objs) := by
  simp only [allocateTyped, hl, bind, Except.bind] at hk
  split at hk
  · simp at hk
  rename_i halign
  split at hk
  · simp at hk
  rename_i hpos
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  set addr := m.lastAddress - l.size - (m.lastAddress - l.size) % align with haddr
  have hmod := Int.emod_nonneg (m.lastAddress - l.size) (show align ≠ 0 by omega)
  have hlow : addr + l.size ≤ m.lastAddress := by omega
  set bs := List.replicate l.size.toNat (none : Byte)
  have wa := writeRepresentation_allocations addr (plainBytes bs) m
  have wf := writeRepresentation_fields addr (plainBytes bs) m
  simp only [wf.2, wa.1]
  refine ⟨addr, rfl, ⟨fun o ho => ?_, ?_, fun o ho => ?_, fun o ho => ?_⟩⟩
  · rcases List.mem_cons.mp ho with rfl | ho
    · refine ⟨by simpa [wa.2.1] using hdead, ⟨_, Map.lookup_insert _ _ _, rfl, ?_, ?_, rfl⟩, fits,
        fun i hi => ?_, fun i hi => ?_⟩
      · simp only; omega
      · obtain ⟨ann, k⟩ := ty
        cases k
        case atomic t => exact absurd rfl (hat _ _)
        all_goals rfl
      · rw [writeRepresentation_bytes, show (plainBytes bs).map Prod.fst = bs by
          simp [plainBytes, Function.comp_def]]
        rw [read_writeInt_at _ _ _ _ (by simpa [bs] using hi)]
        intro v hv
        simp [bs] at hv
      · exact pointerBytes_write_inside addr bs m i (by simpa [bs] using hi)
    · obtain ⟨alive, ⟨al, look, base, size, atomic, ro⟩, fits', bytes, plain⟩ := h.placed o ho
      have hbelow := h.below o ho
      have hfresh := h.fresh o ho
      refine ⟨by simpa [wa.2.1] using alive, ⟨al, ?_, base, size, atomic, ro⟩, fits',
        fun i hi => ?_, fun i hi => ?_⟩
      · simp only
        rw [Map.lookup_insert_of_key_ne _ _ (fun e => by change o.id = m.nextId at e; omega)]
        exact look
      · rw [writeRepresentation_bytes, read_outside_write _ _ _ _ (by simp [plainBytes, bs]; omega)]
        exact bytes i hi
      · rw [pointerBytes_write_outside _ _ _ _ (by simp [bs]; omega)]
        exact plain i hi
  · refine List.Pairwise.cons (fun o ho => ?_) h.apart
    have hbelow := h.below o ho
    have hfresh := h.fresh o ho
    refine ⟨fun e => by simp only at e; omega, ?_, apartL o ho⟩
    left; simp only; omega
  · rcases List.mem_cons.mp ho with rfl | ho
    · exact le_refl _
    · have := h.below o ho; simp only; omega
  · rcases List.mem_cons.mp ho with rfl | ho
    · simp
    · have := h.fresh o ho; simp only; omega

theorem accessTyped_id {tags : Tags} {s : State} {ty : Ctype} {id addr : Int} {r : Int × Int × Int}
    (h : accessTyped tags s ty (.allocated id addr) = .ok r) : r.1 = id := by
  unfold accessTyped at h
  cases hl : typeLayout 64 tags ty with
  | error e => simp [hl, bind, Except.bind] at h
  | ok l =>
    simp only [hl, bind, Except.bind] at h
    split at h
    · simp at h
    · cases ha : s.allocations.lookup id with
      | none => simp [ha] at h
      | some a =>
        simp only [ha] at h
        split at h
        · cases hw : checkAtomic a ty addr l.size with
          | error e => simp [hw] at h
          | ok _ =>
            simp only [hw, pure, Except.pure, Except.ok.injEq] at h
            rw [← h]
        · simp at h

/-- **Kill.** After a Core `kill` of allocation `id`, the other objects stay placed. -/
theorem kill {tags : Tags} {m m' : State} {lm : Lir.Memory} {objs : List Obj} {ty : Ctype}
    {id a : Int} (h : Rel m lm objs) (hk : killTyped tags m ty (.allocated id a) = .ok ((), m')) :
    Rel m' lm (objs.filter fun o => o.id ≠ id) := by
  unfold killTyped at hk
  cases hacc : accessTyped tags m ty (.allocated id a) with
  | error e => simp [hacc, bind, Except.bind] at hk
  | ok r =>
    have hid := accessTyped_id hacc
    obtain ⟨id', a', sz⟩ := r
    simp only at hid
    subst hid
    simp only [hacc, bind, Except.bind] at hk
    cases ha : m.allocations.lookup id' with
    | none => simp [ha] at hk
    | some al =>
    simp only [ha] at hk
    split at hk
    · simp at hk
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and] at hk
    subst hk
    refine ⟨fun o ho => ?_, h.apart.filter _, fun o ho => h.below o (List.mem_of_mem_filter ho),
      fun o ho => h.fresh o (List.mem_of_mem_filter ho)⟩
    have hne : o.id ≠ id' := by simpa using (List.mem_filter.mp ho).2
    obtain ⟨alive, ⟨al, look, base, size, atomic, ro⟩, fits, bytes, plain⟩ :=
      h.placed o (List.mem_of_mem_filter ho)
    refine ⟨?_, ⟨al, ?_, base, size, atomic, ro⟩, fits, bytes, plain⟩
    · simp only [List.mem_cons, not_or]; exact ⟨hne, alive⟩
    · simp only [Map.lookup, Map.erase] at look ⊢
      exact (Finmap.lookup_erase_ne (s := m.allocations) (a := MapKey.key o.id)
        (a' := MapKey.key id') hne).trans look

/-! ## Pointers -/

/-- Core's pointer shifts (`array_shift` by `size * n`, `member_shift` by the member offset)
are Lir word additions. -/
theorem PtrRel.shift {objs : List Obj} {id a : Int} {w : Lir.Word}
    (h : PtrRel objs (.allocated id a) w) (off : Int) :
    PtrRel objs (.allocated id (a + off)) (w + BitVec.ofInt 64 off) := by
  obtain ⟨o, ho, hid, rfl⟩ := h
  refine ⟨o, ho, hid, ?_⟩
  rw [← BitVec.ofInt_add]
  congr 1
  ring

/-- The word of a pointer into a placed object. -/
theorem PtrRel.word {m : State} {lm : Lir.Memory} {objs : List Obj} {o : Obj} {a : Int}
    {w : Lir.Word} (h : Rel m lm objs) (ho : o ∈ objs) (hp : PtrRel objs (.allocated o.id a) w) :
    w = BitVec.ofInt 64 (o.lir + (a - o.base)) := by
  obtain ⟨o', ho', hid, rfl⟩ := hp
  by_cases e : o' = o
  · subst e; rfl
  · exact absurd hid (h.apart_of ho' ho e).1

/-- The address of a pointer within (or one past) a placed object. -/
theorem word_toNat {m : State} {lm : Lir.Memory} {objs : List Obj} {o : Obj} {a : Int}
    (h : Rel m lm objs) (ho : o ∈ objs) (hsize : lm.size < 2 ^ 64)
    (lo : o.base ≤ a) (hi : a ≤ o.base + o.size) :
    (BitVec.ofInt 64 (o.lir + (a - o.base))).toNat = o.addr a := by
  have := (h.placed o ho).fits
  rw [BitVec.toNat_ofInt]
  simp only [Obj.addr]
  omega

/-- The Lir store through a pointer register is the placed store. -/
theorem exec_store {R : Type} [DecidableEq R] {m : State} {lm : Lir.Memory} {objs : List Obj}
    {o : Obj} {a : Int} {n : Nat} {fr : Lir.Frame R} {rb rs : R} {w v : Lir.Word}
    (h : Rel m lm objs) (ho : o ∈ objs) (hsize : lm.size < 2 ^ 64) (hn : GoodWidth n)
    (lo : o.base ≤ a) (hi : a + n ≤ o.base + o.size)
    (hp : PtrRel objs (.allocated o.id a) w) (hb : fr.get rb = some w) (hs : fr.get rs = some v) :
    (Lir.Op.store (lirWidth n) rb 0 rs).exec fr lm = some (fr, storedLir lm (o.addr a) n v) := by
  have hw := word_toNat h ho hsize lo (by rcases hn with rfl | rfl | rfl | rfl <;> omega)
  rw [← hp.word h ho] at hw
  have fits := (h.placed o ho).fits
  have hin : lm.InBounds (o.addr a) (lirWidth n) := by
    simp only [Lir.Memory.InBounds, lirWidth_bytes hn, Obj.addr]; omega
  simp [Lir.Op.exec, hb, hs, hw, Lir.Memory.store, hin, storedLir, lirWidth_bytes hn]

/-- A Lir load through a pointer register is the load at the placed address. -/
theorem exec_load {R : Type} [DecidableEq R] {m : State} {lm : Lir.Memory} {objs : List Obj}
    {o : Obj} {a : Int} {fr : Lir.Frame R} {rd rb : R} {w r : Lir.Word} {width : Lir.Width}
    {ext : Lir.Ext} (h : Rel m lm objs) (ho : o ∈ objs) (hsize : lm.size < 2 ^ 64)
    (lo : o.base ≤ a) (hi : a ≤ o.base + o.size)
    (hp : PtrRel objs (.allocated o.id a) w) (hb : fr.get rb = some w)
    (hl : lm.load width ext (o.addr a) = some r) :
    (Lir.Op.load width ext rd rb 0).exec fr lm = some (fr.set rd r, lm) := by
  have hw := word_toNat h ho hsize lo hi
  rw [← hp.word h ho] at hw
  simp [Lir.Op.exec, hb, hw, hl]

/-- Equality of two pointers into the same object (Core compares their addresses) is equality of
their words. -/
theorem word_eq_iff {m : State} {lm : Lir.Memory} {objs : List Obj} {o : Obj} {a b : Int}
    (h : Rel m lm objs) (ho : o ∈ objs) (hsize : lm.size < 2 ^ 64)
    (la : o.base ≤ a) (ha : a ≤ o.base + o.size) (lb : o.base ≤ b) (hb : b ≤ o.base + o.size) :
    BitVec.ofInt 64 (o.lir + (a - o.base)) = BitVec.ofInt 64 (o.lir + (b - o.base)) ↔ a = b := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [word_toNat h ho hsize la ha, word_toNat h ho hsize lb hb] at this
    simp only [Obj.addr] at this
    omega
  · rintro rfl; rfl

/-- A pointer within (or one past) an object placed above address 0 is not the null word. -/
theorem word_ne_zero {m : State} {lm : Lir.Memory} {objs : List Obj} {o : Obj} {a : Int}
    (h : Rel m lm objs) (ho : o ∈ objs) (hsize : lm.size < 2 ^ 64) (hpos : 0 < o.lir)
    (lo : o.base ≤ a) (hi : a ≤ o.base + o.size) :
    BitVec.ofInt 64 (o.lir + (a - o.base)) ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [word_toNat h ho hsize lo hi] at this
  simp only [Obj.addr] at this
  have z : (0 : Lir.Word).toNat = 0 := rfl
  omega

end Silmaril.Compile.Core.Verified.MemRel
