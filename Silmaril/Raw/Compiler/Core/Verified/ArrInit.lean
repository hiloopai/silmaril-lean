module

public import Silmaril.Compiler.Core.Verified.ArrMem.Defs
public import Silmaril.Compiler.Core.Verified.AggregateUninit.Defs
/-! # The unspecified store after array creation

The canonical Core initialization action is proved directly from `ArrDesig.Arr`,
without requiring a target-memory placement. It clears the whole array's element
definitions while preserving definitions of disjoint arrays.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrInit

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete
open ArrDesig (Arr intArr layout_intArr)
open ArrMem (Array Defs Inv)

/-- The memory after the whole-array unspecified store. -/
def stored (m : Mem.Concrete.State) (id addr : Int) (N : Nat) : Mem.Concrete.State :=
  {writeRepresentation addr (plainBytes (List.replicate (4 * N) none)) m with
    lastUsed := some id}

/-- Forget every definition belonging to one array, retaining all other definitions. -/
def forget (ds : Defs) (q : StateExpr.Key) : Defs :=
  fun p => if p.1 = q then none else ds p

theorem access (tags : Tags) (ann annE : List Annot) {m : Mem.Concrete.State} {id addr : Int} {N : Nat}
    (h : Arr m id addr N) :
    accessTyped tags m (intArr ann annE N) (.allocated id addr) = .ok (id, addr, 4 * N) := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := h
  simp [accessTyped, layout_intArr, alive, look, base, size, checkAtomic, atomic,
    bind, Except.bind, pure, Except.pure, mul_comm]

/-- Both array annotations may differ; the object and stored value have the same length. -/
theorem store (tags : Tags) (ann annE vann vannE : List Annot)
    {m : Mem.Concrete.State} {id addr : Int} {N : Nat} (h : Arr m id addr N) :
    storeTyped tags m (intArr ann annE N) (.allocated id addr)
      (.unspecified (intArr vann vannE N)) = .ok ((addr, 4 * N), stored m id addr N) := by
  obtain ⟨a, look, _, _, _, ro⟩ := h.found
  simp [storeTyped, access tags ann annE h, checkWritable, look, ro, represent,
    layout_intArr, stored, plainBytes, bind, Except.bind, pure, Except.pure,
    Int.toNat_mul, mul_comm]

theorem arr_stored {m : Mem.Concrete.State} {id addr : Int} {N : Nat} (h : Arr m id addr N)
    (wid waddr : Int) (size : Nat) : Arr (stored m wid waddr size) id addr N := by
  obtain ⟨b, pb, hw⟩ := writeRepresentation_shape waddr (plainBytes (List.replicate (4 * size) none)) m
  unfold stored
  rw [hw]
  exact ArrMem.Arr.mono h rfl rfl

theorem slot_stored {m : Mem.Concrete.State} {id addr v : Int} (h : IntSubobject.Slot m id addr v)
    (wid waddr : Int) (size : Nat) (apart : Slots.Apart waddr (4 * size) addr 4) :
    IntSubobject.Slot (stored m wid waddr size) id addr v := by
  have len : (plainBytes (List.replicate (4 * size) (none : Byte))).length = 4 * size := by
    simp [plainBytes]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, pb, hw⟩ := writeRepresentation_shape waddr
      (plainBytes (List.replicate (4 * size) none)) m
    unfold stored
    rw [hw]
    exact h.live.mono rfl rfl
  · intro i hi
    change (writeRepresentation waddr (plainBytes (List.replicate (4 * size) none)) m).pointerBytes.lookup
      (addr + i) = none
    rw [Slots.pointerByte_writeRepresentation _ waddr (addr + i) m (by
      rw [len]
      rcases apart with h | h
      · right; omega
      · left; omega)]
    exact h.plain i hi
  · change fetchBytes 4 addr (writeRepresentation waddr
      (plainBytes (List.replicate (4 * size) none)) m).bytes = _
    rw [Slots.fetchBytes_writeRepresentation _ waddr addr 4 m (by rwa [len])]
    exact h.bytes

/-- Reinitializing one array removes only its definitions, never a neighboring array's. -/
theorem inv_stored {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) {a : Array} (ha : a ∈ arrays) :
    Inv (stored m a.object.id a.object.addr a.length) arrays (forget ds a.object.sym.key) := by
  refine { h with
    live := fun b hb => arr_stored (h.live b hb) _ _ _
    defs := ?_ }
  intro q d hd
  unfold forget at hd
  split at hd
  · cases hd
  · rename_i ne
    obtain ⟨ok, b, hb, key, bound, slot⟩ := h.defs q d hd
    refine ⟨ok, b, hb, key, bound, slot_stored slot _ _ _ ?_⟩
    have sep := (h.apart a ha b hb (fun eq => ne (key.symm.trans eq.symm))).2
    unfold Slots.Apart Array.addr at *
    rcases sep with h | h <;> omega

/-- The actual Store action records the full array write footprint. -/
theorem store_apply {file : Program} {labels : Labels} (k : List Frame)
    (ann annE vann vannE : List Annot) {m : Mem.Concrete.State} {id addr : Int} {N : Nat}
    (h : Arr m id addr N) :
    Interleave.LocalReaches file labels false
      ⟨.apply (.memory .store) [.ctype (intArr ann annE N), .object (.pointer (.allocated id addr)),
        .loaded (.unspecified (intArr vann vannE N))], k, m⟩
      ⟨.value .unit, .annotations [⟨k.findSome? fun f => match f with
        | .excluded n => some n | _ => none, [], true, addr, 4 * N⟩] :: k, stored m id addr N⟩ := by
  apply Relation.ReflTransGen.single
  apply Interleave.LocalStep.memory (name := "Store")
  simp [requestAux, awaitsScheduling, memoryRequest, toMemory,
    store ({definitions := file.tagDefs, enums := m.enumTypes} : Tags) ann annE vann vannE h,
    access ({definitions := file.tagDefs, enums := m.enumTypes} : Tags) ann annE h,
    bind, Except.bind, pure, Except.pure]
  rfl

end Silmaril.Compile.Core.Verified.ArrInit
