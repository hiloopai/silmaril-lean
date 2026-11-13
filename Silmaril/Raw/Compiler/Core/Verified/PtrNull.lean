module

public import Silmaril.Compiler.Core.Verified.StrMem.Defs

/-! # A pointer object holding the null pointer

`PtrNull m id addr`: the live 8-byte pointer object `id` at `addr` holds eight zero bytes, which
`Mem.Concrete` reads back as the null pointer whatever their provenance metadata
(`abstractPointer` tests the address first). Storing a null pointer writes exactly these bytes
(`store_null`); loading reads back `null` (`load_null`); `Keeps` keeps the object
(`PtrNull.keeps`). The lemmas here are about `Mem.Concrete` only (no dynamics).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StrMem

open Silmaril.Cerberus
open Mem.Concrete

/-- A pointer object holding the null pointer: eight zero bytes. -/
structure PtrNull (m : State) (id addr : Int) : Prop where
  slot : PtrSlot m id addr
  bytes : ∀ i : Nat, i < 8 → readByte (addr + i) m.bytes = some 0

theorem PtrNull.keeps {m m' : State} {id addr : Int} (h : PtrNull m id addr) (k : Keeps m m') :
    PtrNull m' id addr where
  slot := h.slot.keeps k
  bytes i hi := by
    have := h.bytes i hi
    unfold readByte at this ⊢
    rw [k.bytes _ (by have := h.slot.above; omega)]; exact this

/-- **Storing the null pointer** into a pointer object. -/
theorem store_null (tags : Tags) (ann : List Annot) (q : Qualifiers) (ref ref' : Ctype) {m : State}
    {id addr : Int} (h : PtrSlot m id addr) :
    storeTyped tags m (.mk ann (.pointer q ref)) (.allocated id addr) (.pointer ref (.null ref')) =
      .ok ((addr, 8), {writeRepresentation addr (plainBytes (encodeInteger 8 0)) m with lastUsed := some id}) ∧
    PtrNull {writeRepresentation addr (plainBytes (encodeInteger 8 0)) m with lastUsed := some id} id addr := by
  have hacc := access_ptr_aux tags ann q ref h
  obtain ⟨alive, ⟨a, look, base, size, atomic, ro⟩, below, above⟩ := h
  have hr : represent 64 tags (.pointer ref (.null ref')) m =
      .ok (plainBytes (encodeInteger 8 0), m) := by
    simp [represent, representPointer, pure, Except.pure]
  have hw := writeRepresentation_allocations addr (plainBytes (encodeInteger 8 0)) m
  have hfst : (plainBytes (encodeInteger 8 0)).map Prod.fst = encodeInteger 8 0 := by
    simp [plainBytes, List.map_map, Function.comp_def]
  refine ⟨?_, ⟨⟨?_, ⟨a, ?_, base, size, atomic, ro⟩, ?_, ?_⟩, ?_⟩⟩
  · simp [storeTyped, hacc, checkWritable, look, ro, hr, bind, Except.bind, pure, Except.pure,
      plainBytes, encodeInteger_length]
  · simpa [hw.2.1] using alive
  · simpa [hw.1] using look
  · simpa [wr_nextId] using below
  · simpa [wr_lastAddress] using above
  · intro i hi
    change readByte (addr + i) (writeRepresentation addr (plainBytes (encodeInteger 8 0)) m).bytes = _
    rw [writeRepresentation_bytes, hfst,
      readByte_writeInt _ _ _ i (by rw [encodeInteger_length]; exact hi),
      encodeInteger_getElem 8 0 i hi]
    simp

/-- **Loading the null pointer** back. -/
theorem load_null (tags : Tags) (ann : List Annot) (q : Qualifiers) (ref : Ctype) {m : State}
    {id addr : Int} (h : PtrNull m id addr) :
    loadTyped tags m (.mk ann (.pointer q ref)) (.allocated id addr) =
      .ok (.pointer ref (.null ref), {m with lastUsed := some id}) := by
  have hacc := access_ptr_aux tags ann q ref h.slot
  have hf : fetchBytes 8 addr m.bytes = encodeInteger 8 0 :=
    fetchBytes_eq_encode 8 addr 0 m.bytes (fun i hi => by simpa using h.bytes i hi)
  have hdec : decodeInteger (fetchBytes 8 addr m.bytes) = some 0 := by
    rw [hf, decode_encode]; rfl
  have hptr : abstractPointer m ref addr 0 = .ok (.null ref) := by
    simp [abstractPointer, pure, Except.pure]
  simp [loadTyped, hacc, abstractValue, typeLayout, hdec, hptr, exposeRead, bind, Except.bind,
    pure, Except.pure]

end Silmaril.Compile.Core.Verified.StrMem
