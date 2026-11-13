module

public import Silmaril.Compiler.Core.Verified.MemRel.Defs
public import Silmaril.Compiler.Core.Verified.Slots.Defs

/-! # Integer subobjects of aggregate allocations

An integer member or element occupies four bytes inside a live allocation; it need
not be the allocation's base, and the allocation need not have size four. `Live` is
this access invariant. `Slot` adds the initialized bytes. In particular, two slots
can share an allocation id: store framing uses byte ranges, not distinct ids.

These are source-memory facts, with a bridge from `MemRel.Placed`. They do not
recognize aggregates or extend the accepted compiler fragment on their own.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.IntSubobject

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Mem.Concrete

/-- Four writable, non-atomic bytes contained in an allocation. -/
structure Live (s : State) (id addr : Int) : Prop where
  alive : id ∉ s.dead
  found : ∃ a, s.allocations.lookup id = some a ∧ a.base ≤ addr ∧
    addr + 4 ≤ a.base + a.size ∧ a.atomic = false ∧ a.readonly = none

/-- A defined integer at an element or member address. -/
structure Slot (s : State) (id addr n : Int) : Prop where
  live : Live s id addr
  plain : PlainAt s addr
  bytes : fetchBytes 4 addr s.bytes = encodeInteger 4 n

/-- Whole-object scalar slots embed in the subobject invariant. -/
theorem Live.ofLiveInt {s : State} {id addr : Int} (h : LiveInt s id addr) :
    Live s id addr := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := h
  exact ⟨alive, a, look, by omega, by omega, atomic, ro⟩

theorem Slot.ofSlot {s : State} {id addr n : Int} (h : Locals.Slot s id addr n) :
    Slot s id addr n := ⟨.ofLiveInt h.live, h.plain, h.bytes⟩

/-- Any in-bounds member/element of a placed object satisfies `Live`. -/
theorem Live.ofPlaced {s : State} {lm : Silmaril.Machine.Lir.Memory} {o : MemRel.Obj}
    (h : MemRel.Placed s lm o) {addr : Int} (lo : o.base ≤ addr)
    (hi : addr + 4 ≤ o.base + o.size) : Live s o.id addr := by
  obtain ⟨alive, ⟨a, look, base, size, atomic, ro⟩, _⟩ := h
  exact ⟨alive, a, look, by omega, by omega, atomic, ro⟩

/-- Only lifetime and allocation metadata matter for access validity. -/
theorem Live.mono {s s' : State} {id addr : Int} (h : Live s id addr)
    (hd : s'.dead = s.dead) (ha : s'.allocations = s.allocations) : Live s' id addr :=
  ⟨hd ▸ h.alive, ha ▸ h.found⟩

theorem Live.focus {s : State} {id addr : Int} (h : Live s id addr) (ann : List Annot) :
    Live (ReturnConst.focusMemory ann s) id addr := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann s
  rw [hl]
  exact h.mono rfl rfl

theorem Slot.touched {s s' : State} {id addr n : Int} (h : Slot s id addr n)
    (t : LoadTask.Touched s s') : Slot s' id addr n := by
  obtain ⟨l, u, rfl⟩ := t
  exact ⟨h.live.mono rfl rfl, h.plain, h.bytes⟩

/-- Reserving a negative-action exclusion id changes neither bytes nor lifetimes. -/
theorem Slot.nextExcluded {s : State} {id addr n : Int} (h : Slot s id addr n)
    (next : Nat) : Slot {s with nextExcluded := next} id addr n :=
  ⟨h.live.mono rfl rfl, h.plain, h.bytes⟩

theorem access (tags : Tags) (ann : List Annot) {s : State} {id addr : Int}
    (h : Live s id addr) :
    accessTyped tags s (intType ann) (.allocated id addr) = .ok (id, addr, 4) := by
  obtain ⟨alive, a, look, lo, hi, atomic, _⟩ := h
  simp [accessTyped, layout_intType, alive, look, lo, hi, checkAtomic, atomic,
    bind, Except.bind, pure, Except.pure]

/-- Typed integer stores use subobject bounds, without changing their enclosing allocation. -/
theorem store (tags : Tags) (ann : List Annot) {s : State} {id addr n : Int}
    (h : Live s id addr) (hn : IntRange n) :
    storeTyped tags s (intType ann) (.allocated id addr) (.integer (.signed .int) n) =
      .ok ((addr, 4), Locals.stored s id addr n) := by
  obtain ⟨a, look, lo, hi, atomic, ro⟩ := h.found
  obtain ⟨lo', hi'⟩ := hn
  have hr : represent 64 tags (.integer (.signed .int) n) s =
      .ok (plainBytes (encodeInteger 4 n), s) := by
    simp [represent, registeredIntegerLayout, registeredInteger, integerLayout, baseWidth,
      representationBounds, lo', hi', pure, Except.pure]
  simp [storeTyped, access tags ann h, checkWritable, look, ro, hr,
    bind, Except.bind, pure, Except.pure, plainBytes, encodeInteger_length, Locals.stored]

/-- Typed loads of a specified subobject expose no pointer provenance and preserve its bytes. -/
theorem load (tags : Tags) (ann : List Annot) {s : State} {id addr : Int}
    (h : Live s id addr) (plain : PlainAt s addr) {n : Int} (hn : IntRange n)
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
  rw [access tags ann h]
  simp only [bind, Except.bind, habs, hexp, pure, Except.pure]


/-- An integer write keeps every allocation live, including its own. -/
theorem Live.stored {s : State} {id addr : Int} (h : Live s id addr)
    (wid waddr n : Int) : Live (Locals.stored s wid waddr n) id addr := by
  obtain ⟨b, pb, hw⟩ := writeRepresentation_shape waddr (plainBytes (encodeInteger 4 n)) s
  unfold Locals.stored
  rw [hw]
  exact h.mono rfl rfl

/-- The written bytes form an initialized subobject. -/
theorem stored_slot {s : State} {id addr : Int} (h : Live s id addr) (n : Int) :
    Slot (Locals.stored s id addr n) id addr n := by
  refine ⟨h.stored _ _ _, ?_, ?_⟩
  · intro i hi
    exact Locals.plain_write _ addr s i (by simpa [encodeInteger_length] using hi)
  · change fetchBytes 4 addr (writeRepresentation addr (plainBytes (encodeInteger 4 n)) s).bytes = _
    have hf := Locals.fetch_write (encodeInteger 4 n) addr s
    simpa [encodeInteger_length] using hf

/-- Adjacent elements or members remain initialized after a store, even in the same allocation. -/
theorem Slot.stored {s : State} {id addr n : Int} (h : Slot s id addr n)
    (wid waddr v : Int) (apart : Slots.Apart waddr 4 addr 4) :
    Slot (Locals.stored s wid waddr v) id addr n := by
  have len : (plainBytes (encodeInteger 4 v)).length = 4 := by
    simp [plainBytes, encodeInteger_length]
  refine ⟨h.live.stored _ _ _, ?_, ?_⟩
  · intro i hi
    change (writeRepresentation waddr (plainBytes (encodeInteger 4 v)) s).pointerBytes.lookup
      (addr + i) = none
    rw [Slots.pointerByte_writeRepresentation _ waddr (addr + i) s (by
      rw [len]
      rcases apart with h | h
      · right; omega
      · left; omega)]
    exact h.plain i hi
  · change fetchBytes 4 addr (writeRepresentation waddr (plainBytes (encodeInteger 4 v)) s).bytes = _
    rw [Slots.fetchBytes_writeRepresentation _ waddr addr 4 s (by rwa [len])]
    exact h.bytes

/-- Killing an enclosing allocation invalidates all of its subobjects; other allocations survive. -/
theorem Slot.killed {s : State} {id addr n : Int} (h : Slot s id addr n)
    (other : Int) (ne : id ≠ other) : Slot (Locals.killed s other) id addr n := by
  refine ⟨⟨?_, ?_⟩, h.plain, h.bytes⟩
  · simpa [Locals.killed, ne] using h.live.alive
  · obtain ⟨a, ha, rest⟩ := h.live.found
    refine ⟨a, ?_, rest⟩
    change (s.allocations.erase other).lookup id = some a
    simp only [Map.lookup, Map.erase]
    rw [Finmap.lookup_erase_ne (show MapKey.key id ≠ MapKey.key other from ne)]
    exact ha

end Silmaril.Compile.Core.Verified.IntSubobject
