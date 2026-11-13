module

public import Silmaril.Compiler.Core.Verified.ArrInit.Defs
public import Silmaril.Compiler.Core.Verified.PtrStmt.Defs
/-! # Array allocation and lifetime framing

Array creation uses the same `StrMem.Keeps` interface as pointer and string
objects. Existing scalar slots and initialized array elements remain intact
when new allocations are made below them. Killing another allocation preserves
all element definitions; killing an array removes all of its definitions.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrLife

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open ArrDesig (Arr arrAddr createdArr)
open ArrMem (Array Defs Inv)

/-- Every tracked array is an earlier allocation at or above the allocation frontier. -/
structure Frontier (m : Mem.Concrete.State) (arrays : List Array) : Prop where
  ids : ∀ a ∈ arrays, a.object.id < m.nextId
  addrs : ∀ a ∈ arrays, m.lastAddress ≤ a.object.addr

theorem arr_keeps {m m' : Mem.Concrete.State} {id addr : Int} {N : Nat}
    (h : Arr m id addr N) (keep : StrMem.Keeps m m') (hid : id < m.nextId) :
    Arr m' id addr N :=
  ⟨by rw [keep.dead id hid]; exact h.alive, by rw [keep.alloc id hid]; exact h.found⟩

theorem slot_keeps {m m' : Mem.Concrete.State} {id addr n : Int}
    (h : IntSubobject.Slot m id addr n) (keep : StrMem.Keeps m m')
    (hid : id < m.nextId) (ha : m.lastAddress ≤ addr) : IntSubobject.Slot m' id addr n := by
  refine ⟨⟨?_, ?_⟩, fun i hi => ?_, ?_⟩
  · rw [keep.dead id hid]; exact h.live.alive
  · rw [keep.alloc id hid]; exact h.live.found
  · rw [keep.pbytes _ (by omega)]; exact h.plain i hi
  · rw [← h.bytes]
    have e : ∀ j : Int, addr ≤ j → m'.bytes.lookup j = m.bytes.lookup j :=
      fun j hj => keep.bytes j (by omega)
    simp only [Mem.Concrete.fetchBytes, Mem.Concrete.readByte, e addr (le_refl _),
      e (addr + 1) (by omega), e (addr + 1 + 1) (by omega), e (addr + 1 + 1 + 1) (by omega)]

theorem inv_keeps {m m' : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) (f : Frontier m arrays) (keep : StrMem.Keeps m m') : Inv m' arrays ds := by
  refine { h with
    live := fun a ha => arr_keeps (h.live a ha) keep (f.ids a ha)
    defs := ?_ }
  intro q d hd
  obtain ⟨ok, a, ha, key, bound, slot⟩ := h.defs q d hd
  refine ⟨ok, a, ha, key, bound, slot_keeps slot keep (f.ids a ha) ?_⟩
  have := f.addrs a ha
  unfold Array.addr
  omega

theorem frontier_keeps {m m' : Mem.Concrete.State} {arrays : List Array}
    (h : Frontier m arrays) (keep : StrMem.Keeps m m') : Frontier m' arrays :=
  ⟨fun a ha => lt_of_lt_of_le (h.ids a ha) keep.nextId,
    fun a ha => le_trans keep.last (h.addrs a ha)⟩

/-- Fresh arrays end at or below the previous frontier, including any alignment padding. -/
theorem arrAddr_bounds (m : Mem.Concrete.State) (N : Nat) :
    arrAddr m N + 4 * N ≤ m.lastAddress ∧ arrAddr m N % 4 = 0 := by
  unfold arrAddr
  omega

/-- The actual array allocation and prefix preserve every earlier object. -/
theorem created_keeps (pref : Prefix) (ann annE : List Annot) (N : Nat) (m : Mem.Concrete.State) :
    StrMem.Keeps m (ArrCreate.createdArrP pref ann annE N m) := by
  have hW : StrMem.Keeps m (Mem.Concrete.writeRepresentation (arrAddr m N)
      (Mem.Concrete.plainBytes (List.replicate (N * 4) none)) m) :=
    (StrMem.Keeps.refl m).write _ _ (by
      simp only [Mem.Concrete.plainBytes, List.length_map, List.length_replicate]
      have := (arrAddr_bounds m N).1
      omega)
  unfold ArrCreate.createdArrP createdArr
  refine StrMem.Keeps.updateLast ?_ rfl (le_refl _) _
  refine ⟨hW.enums, ?_, ?_, ?_, hW.dead, hW.bytes, hW.pbytes⟩
  · simp
  · have := (arrAddr_bounds m N).1
    simp only
    omega
  · intro j hj
    simp only
    rw [Map.lookup_insert_of_key_ne _ _ (show j ≠ m.nextId by omega)]

/-- Attach a fresh, not-yet-defined array without altering any older definitions. -/
theorem inv_cons {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) (a : Array) (live : Arr m a.object.id a.object.addr a.length)
    (aligned : a.object.addr % 4 = 0)
    (fresh : ∀ b ∈ arrays, a.object.sym.key ≠ b.object.sym.key)
    (sep : ∀ b ∈ arrays, a.object.id ≠ b.object.id ∧
      Slots.Apart a.object.addr (4 * a.length) b.object.addr (4 * b.length)) :
    Inv m (a :: arrays) ds := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact live
    · exact h.live b hb
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact aligned
    · exact h.aligned b hb
  · intro b hb c hc eq
    rcases List.mem_cons.mp hb with bh | hb
    · subst b
      rcases List.mem_cons.mp hc with ch | hc
      · exact ch.symm
      · exact False.elim (fresh c hc eq)
    · rcases List.mem_cons.mp hc with ch | hc
      · subst c
        exact False.elim (fresh b hb eq.symm)
      · exact h.unique b hb c hc eq
  · intro b hb c hc ne
    rcases List.mem_cons.mp hb with bh | hb
    · subst b
      rcases List.mem_cons.mp hc with ch | hc
      · subst c
        exact False.elim (ne rfl)
      · exact sep c hc
    · rcases List.mem_cons.mp hc with ch | hc
      · subst c
        exact ⟨(sep b hb).1.symm, (sep b hb).2.symm⟩
      · exact h.apart b hb c hc ne
  · intro q d hd
    obtain ⟨ok, b, hb, rest⟩ := h.defs q d hd
    exact ⟨ok, b, List.mem_cons_of_mem a hb, rest⟩

/-- Creation adds one actual aggregate allocation; it does not create synthetic scalar objects. -/
theorem inv_create {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) (front : Frontier m arrays) (x : Sym) (N : Nat)
    (fresh : ∀ b ∈ arrays, x.key ≠ b.object.sym.key) (alive : m.nextId ∉ m.dead)
    (pref : Prefix) (ann annE : List Annot) :
    Inv (ArrCreate.createdArrP pref ann annE N m)
      (⟨⟨x, m.nextId, arrAddr m N⟩, N⟩ :: arrays) ds := by
  have old := inv_keeps h front (created_keeps pref ann annE N m)
  apply inv_cons old
  · exact ArrCreate.createdArrP_arr pref ann annE N m alive
  · exact (arrAddr_bounds m N).2
  · exact fresh
  · intro b hb
    have ids := front.ids b hb
    have addrs := front.addrs b hb
    have upper := (arrAddr_bounds m N).1
    exact ⟨by simp only; omega, Or.inl (by simp only; omega)⟩

/-- The existing scalar/pointer invariant also frames through any such allocation. -/
theorem scalarInv_keeps {env : Env} {m m' : Mem.Concrete.State}
    {ints ptrs : List StateMem.Local} {ds : StateExpr.Key → Option IntExpr.Term}
    {pts : StateExpr.Key → Option StateExpr.PtsTo} (h : StateMem.Inv env m ints ds ptrs pts)
    (ids : ∀ l ∈ ints, l.id < m.nextId) (addrs : ∀ l ∈ ints, m.lastAddress ≤ l.addr)
    (keep : StrMem.Keeps m m') : StateMem.Inv env m' ints ds ptrs pts := by
  have := h.ptrs.frame (StateMem.PFrame.ofKeeps ptrs keep)
  refine ⟨h.env, fun l hl => PtrStmt.liveInt_keeps (h.live l hl) keep (ids l hl), h.apart, ?_⟩
  intro q d hd
  obtain ⟨ok, l, hl, key, slot⟩ := h.defs q d hd
  exact ⟨ok, l, hl, key, PtrStmt.slot_keeps slot keep (ids l hl) (addrs l hl)⟩

theorem arr_killed {m : Mem.Concrete.State} {id addr : Int} {N : Nat}
    (h : Arr m id addr N) (other : Int) (ne : id ≠ other) : Arr (Locals.killed m other) id addr N := by
  refine ⟨?_, ?_⟩
  · simpa [Locals.killed, ne] using h.alive
  · obtain ⟨a, look, rest⟩ := h.found
    refine ⟨a, ?_, rest⟩
    change (m.allocations.erase other).lookup id = some a
    simp only [Map.lookup, Map.erase]
    rw [Finmap.lookup_erase_ne (show MapKey.key id ≠ MapKey.key other from ne)]
    exact look

theorem inv_killOutside {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) (id : Int) (ne : ∀ a ∈ arrays, a.object.id ≠ id) :
    Inv (Locals.killed m id) arrays ds := by
  refine { h with
    live := fun a ha => arr_killed (h.live a ha) id (ne a ha)
    defs := ?_ }
  intro q d hd
  obtain ⟨ok, a, ha, key, bound, slot⟩ := h.defs q d hd
  exact ⟨ok, a, ha, key, bound, slot.killed id (ne a ha)⟩

/-- Remove the entire killed array and all of its element definitions. -/
theorem inv_kill {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) {a : Array} (ha : a ∈ arrays) :
    Inv (Locals.killed m a.object.id)
      (arrays.filter fun b => b.object.sym.key != a.object.sym.key)
      (ArrInit.forget ds a.object.sym.key) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨hb, ne⟩ := List.mem_filter.mp hb
    have keyne : b.object.sym.key ≠ a.object.sym.key := by simpa using ne
    exact arr_killed (h.live b hb) _ (h.apart b hb a ha keyne).1
  · intro b hb
    exact h.aligned b (List.mem_filter.mp hb).1
  · intro b hb c hc eq
    exact h.unique b (List.mem_filter.mp hb).1 c (List.mem_filter.mp hc).1 eq
  · intro b hb c hc ne
    exact h.apart b (List.mem_filter.mp hb).1 c (List.mem_filter.mp hc).1 ne
  · intro q d hd
    unfold ArrInit.forget at hd
    split at hd
    · cases hd
    · rename_i ne
      obtain ⟨ok, b, hb, key, bound, slot⟩ := h.defs q d hd
      have keyne : b.object.sym.key ≠ a.object.sym.key := fun eq => ne (key.symm.trans eq)
      exact ⟨ok, b, List.mem_filter.mpr ⟨hb, by simpa using keyne⟩, key, bound,
        slot.killed _ (h.apart b hb a ha keyne).1⟩

end Silmaril.Compile.Core.Verified.ArrLife
