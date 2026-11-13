module

public import Silmaril.Compiler.Core.Verified.LoadTask.Defs
public import Silmaril.Cerberus.Mem.TypedAggregateLaws.Defs

/-! # Several disjoint integer locals

The frame rules missing from the one-local fragment: storing in one four-byte slot
preserves every disjoint slot, and killing one allocation preserves the others.
`Slots` records a finite collection of live initialized locals. Its store rule updates
exactly the written local; reads and location changes preserve the whole collection.
These are source-memory facts, independent of any executable recognizer.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Slots

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete (LiveInt PlainAt IntRange)
open Locals (Slot stored killed)

/-- Half-open byte ranges do not overlap. Touching endpoints are permitted. -/
def Apart (a : Int) (n : Nat) (b : Int) (k : Nat) : Prop :=
  a + n ≤ b ∨ b + k ≤ a

theorem Apart.symm {a b : Int} {n k : Nat} (h : Apart a n b k) : Apart b k a n :=
  Or.symm h

theorem Apart.byte {a b : Int} {n k i j : Nat} (h : Apart a n b k)
    (hi : i < n) (hj : j < k) : a + i ≠ b + j := by
  rcases h with h | h <;> omega

/-- A representation write leaves pointer metadata outside its range unchanged. -/
theorem pointerByte_writeRepresentation (bs : Mem.Concrete.Representation) (a c : Int)
    (m : Mem.Concrete.State) (h : c < a ∨ a + bs.length ≤ c) :
    (Mem.Concrete.writeRepresentation a bs m).pointerBytes.lookup c = m.pointerBytes.lookup c :=
  Mem.Concrete.pointer_find_disjoint m c a bs h

/-- Reading a disjoint range is unchanged by a representation write. -/
theorem fetchBytes_writeRepresentation (bs : Mem.Concrete.Representation) (a b : Int)
    (k : Nat) (m : Mem.Concrete.State) (h : Apart a bs.length b k) :
    Mem.Concrete.fetchBytes k b (Mem.Concrete.writeRepresentation a bs m).bytes =
      Mem.Concrete.fetchBytes k b m.bytes :=
  Mem.Concrete.typed_write_disjoint k b a bs m h.symm

/-- A store updates no allocation's lifetime, including the written allocation. -/
theorem live_stored {m : Mem.Concrete.State} {id addr : Int} (h : LiveInt m id addr)
    (wid waddr value : Int) : LiveInt (stored m wid waddr value) id addr := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape waddr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 value)) m
  unfold stored
  rw [hw]
  exact Locals.liveInt_with h rfl rfl

/-- Reserving a fresh negative-action exclusion id changes no local's contents. -/
theorem slot_nextExcluded {m : Mem.Concrete.State} {id addr value : Int}
    (h : Slot m id addr value) (n : Nat) :
    Slot {m with nextExcluded := n} id addr value :=
  ⟨Locals.liveInt_with h.live rfl rfl, h.plain, h.bytes⟩

/-- The frame rule for an integer store. -/
theorem slot_stored {m : Mem.Concrete.State} {id addr value : Int} (h : Slot m id addr value)
    (wid waddr wvalue : Int) (apart : Apart waddr 4 addr 4) :
    Slot (stored m wid waddr wvalue) id addr value := by
  have len : (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 wvalue)).length = 4 := by
    simp [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length]
  refine ⟨live_stored h.live _ _ _, ?_, ?_⟩
  · intro i hi
    change (Mem.Concrete.writeRepresentation waddr
      (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 wvalue)) m).pointerBytes.lookup
        (addr + i) = none
    rw [pointerByte_writeRepresentation _ waddr (addr + i) m (by
      rw [len]
      rcases apart with h | h
      · right; omega
      · left; omega)]
    exact h.plain i hi
  · change Mem.Concrete.fetchBytes 4 addr (Mem.Concrete.writeRepresentation waddr
      (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 wvalue)) m).bytes = _
    rw [fetchBytes_writeRepresentation _ waddr addr 4 m (by rwa [len])]
    exact h.bytes

/-- Killing a different allocation preserves an integer local. -/
theorem slot_killed {m : Mem.Concrete.State} {id addr value : Int} (h : Slot m id addr value)
    (other : Int) (ne : id ≠ other) : Slot (killed m other) id addr value := by
  refine ⟨⟨?_, ?_⟩, h.plain, h.bytes⟩
  · simpa [killed, ne] using h.live.alive
  · obtain ⟨a, ha, rest⟩ := h.live.found
    refine ⟨a, ?_, rest⟩
    change (m.allocations.erase other).lookup id = some a
    simp only [Map.lookup, Map.erase]
    rw [Finmap.lookup_erase_ne (show MapKey.key id ≠ MapKey.key other from ne)]
    exact ha

/-- Allocating another integer object preserves every disjoint existing slot. -/
theorem slot_created {m : Mem.Concrete.State} {id addr value : Int} (h : Slot m id addr value)
    (pref : Prefix) (ann : List Annot) (fresh : id ≠ m.nextId)
    (apart : Apart (Mem.Concrete.nextIntAddress m) 4 addr 4) :
    Slot (Actions.created pref ann m) id addr value := by
  let bs := Mem.Concrete.plainBytes (List.replicate 4 none)
  let a := Mem.Concrete.nextIntAddress m
  have len : bs.length = 4 := by simp [bs, Mem.Concrete.plainBytes]
  have hw := Mem.Concrete.writeRepresentation_shape a bs m
  obtain ⟨b, pb, hw⟩ := hw
  have shape : Actions.created pref ann m =
      {m with
        bytes := b
        pointerBytes := pb
        nextId := m.nextId + 1
        lastAddress := a
        allocations := (m.allocations.insert m.nextId
          ({base := a, size := 4, objectType := some (Mem.Concrete.intType ann)} :
            Mem.Concrete.Allocation)).insert m.nextId
          ({base := a, size := 4, objectType := some (Mem.Concrete.intType ann),
            readonlyKind := Mem.Concrete.readonlyKind pref} : Mem.Concrete.Allocation),
        lastUsed := some m.nextId} := by
    unfold Actions.created
    change Mem.Concrete.updateLastAllocation
      {Mem.Concrete.writeRepresentation a bs m with
        nextId := m.nextId + 1, lastAddress := a,
        allocations := m.allocations.insert m.nextId
          ({base := a, size := 4, objectType := some (Mem.Concrete.intType ann)} :
            Mem.Concrete.Allocation), lastUsed := some m.nextId} _ = _
    rw [hw]
    simp [Mem.Concrete.updateLastAllocation]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [shape]; exact h.live.alive
  · obtain ⟨old, found, rest⟩ := h.live.found
    refine ⟨old, ?_, rest⟩
    rw [shape]
    simpa only [Map.lookup_insert_of_key_ne _ _ (show MapKey.key id ≠ MapKey.key m.nextId from fresh)]
      using found
  · intro i hi
    rw [shape]
    change pb.lookup (addr + i) = none
    have hp := pointerByte_writeRepresentation bs a (addr + i) m (by
      rw [len]
      rcases apart with h | h
      · right; omega
      · left; omega)
    rw [hw] at hp
    exact hp.trans (h.plain i hi)
  · rw [shape]
    change Mem.Concrete.fetchBytes 4 addr b = _
    have hb := fetchBytes_writeRepresentation bs a addr 4 m (by rwa [len])
    rw [hw] at hb
    exact hb.trans h.bytes

/-- A source local's allocation, address and current integer value. -/
structure Local where
  id : Int
  address : Int
  value : Int
  deriving DecidableEq, Repr

/-- The concrete memory contains each local's initialized value. -/
def Holds (m : Mem.Concrete.State) (locals : List Local) : Prop :=
  ∀ l ∈ locals, Slot m l.id l.address l.value

/-- Allocation ids are distinct and the byte ranges of distinct locals are disjoint. -/
def Disjoint (locals : List Local) : Prop :=
  locals.Pairwise fun a b => a.id ≠ b.id ∧ Apart a.address 4 b.address 4

theorem Disjoint.apart {locals : List Local} (h : Disjoint locals)
    {a b : Local} (ha : a ∈ locals) (hb : b ∈ locals) (ne : a.id ≠ b.id) :
    Apart a.address 4 b.address 4 := by
  induction locals generalizing a b with
  | nil => simp at ha
  | cons first rest ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with ha0 | harest
    · subst a
      rcases List.mem_cons.mp hb with hb0 | hbrest
      · subst b; exact False.elim (ne rfl)
      · exact (head b hbrest).2
    · rcases List.mem_cons.mp hb with hb0 | hbrest
      · subst b; exact (head a harest).2.symm
      · exact ih tail harest hbrest ne

/-- Reads touch no local, however many locals there are. -/
theorem holds_touched {m m' : Mem.Concrete.State} {locals : List Local}
    (h : Holds m locals) (t : LoadTask.Touched m m') : Holds m' locals :=
  fun l hl => t.slot (h l hl)

/-- Store into a designated local, preserving all the other disjoint local values. -/
theorem holds_store {m : Mem.Concrete.State} {locals : List Local}
    (h : Holds m locals) (target : Local) (ht : target ∈ locals)
    (separate : ∀ l ∈ locals, l.id ≠ target.id → Apart target.address 4 l.address 4)
    (value : Int) :
    Holds (stored m target.id target.address value)
      (locals.map fun l => if l.id = target.id then {l with value := value} else l) := by
  intro l hl
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hl
  split
  · rename_i eq
    have addr : old.address = target.address := by
      by_contra ne
      -- A live allocation has a unique base, even if its id occurs twice in the list.
      exact False.elim (by
        have := h old hold
        obtain ⟨a, ha, base, -⟩ := this.live.found
        obtain ⟨b, hb, base', -⟩ := (h target ht).live.found
        rw [eq, hb] at ha
        cases ha
        exact ne (base.symm.trans base'))
    simpa [eq, addr] using Locals.stored_slot (h target ht).live value
  · exact slot_stored (h old hold) _ _ _ (separate old hold ‹_›)

/-- The collection store rule specialized to the pairwise disjoint invariant. -/
theorem holds_store_disjoint {m : Mem.Concrete.State} {locals : List Local}
    (h : Holds m locals) (d : Disjoint locals) (target : Local) (ht : target ∈ locals)
    (value : Int) :
    Holds (stored m target.id target.address value)
      (locals.map fun l => if l.id = target.id then {l with value := value} else l) :=
  holds_store h target ht (fun _l hl ne => d.apart ht hl ne.symm) value

/-- Removing a killed local from the collection preserves all the remaining locals. -/
theorem holds_kill {m : Mem.Concrete.State} {locals : List Local} (h : Holds m locals)
    (id : Int) : Holds (killed m id) (locals.filter fun l => l.id != id) := by
  intro l hl
  obtain ⟨hl, ne⟩ := List.mem_filter.mp hl
  exact slot_killed (h l hl) id (by simpa using ne)

/-- Allocation preserves the initialized collection when the new id is fresh and its
four-byte range is disjoint from all the existing ranges. -/
theorem holds_create {m : Mem.Concrete.State} {locals : List Local} (h : Holds m locals)
    (pref : Prefix) (ann : List Annot)
    (fresh : ∀ l ∈ locals, l.id ≠ m.nextId)
    (apart : ∀ l ∈ locals, Apart (Mem.Concrete.nextIntAddress m) 4 l.address 4) :
    Holds (Actions.created pref ann m) locals :=
  fun l hl => slot_created (h l hl) pref ann (fresh l hl) (apart l hl)

/-- Disjoint memory ranges cannot race, even when both accesses write. -/
theorem races_eq_false_of_apart {a b : Access}
    (h : a.address + a.size ≤ b.address ∨ b.address + b.size ≤ a.address) :
    races a b = false := by
  rcases h with h | h
  · have no : ¬ b.address < a.address + a.size := by omega
    simp [races, no]
  · have no : ¬ a.address < b.address + b.size := by omega
    simp [races, no]

end Silmaril.Compile.Core.Verified.Slots
