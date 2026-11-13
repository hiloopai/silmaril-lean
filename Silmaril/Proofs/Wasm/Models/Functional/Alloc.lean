module

public import Silmaril.Wasm.Models.Functional.Defs
public import Silmaril.Proofs.Wasm.Models.Runtime.Basic
public import Silmaril.Wasm.Models.Features.Thms

/-!
# Functional code only allocates

`step_allocOnly`: for a feature set `S ≤ functional` (no memories, tables, globals, reference
types, bulk operations or mutable aggregates), a Core step from code of `S` (at runtime,
`Rt.CodeIn S`) under a host that only allocates changes the store by allocation only. Each rule
either keeps the store, allocates (`struct.new`, `array.new*`, `throw`), is a host call, or has
a redex outside `S`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Functional

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Models
  Silmaril.Wasm.Models.Rt Silmaril.Proofs.Wasm.Models.Rt

variable {S : FeatureSet} {H : Type}

@[simp] theorem allocOnly_refl (s : Store H) : AllocOnly s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

@[simp] theorem allocOnly_addStruct (s : Store H) (si : StructInst) :
    AllocOnly s (s.addStruct si) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_append _ _, List.prefix_refl _,
    List.prefix_refl _⟩

@[simp] theorem allocOnly_addArray (s : Store H) (ai : ArrayInst) :
    AllocOnly s (s.addArray ai) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, List.prefix_append _ _,
    List.prefix_refl _⟩

@[simp] theorem allocOnly_addExn (s : Store H) (e : ExnInst) : AllocOnly s (s.addExn e) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, List.prefix_refl _,
    List.prefix_append _ _⟩

/-- The capabilities `functional` lacks. -/
structure Lacks (S : FeatureSet) : Prop where
  memory : S.has .memory = false
  table : S.has .table = false
  mutGlobal : S.has .mutGlobal = false
  bulkMemory : S.has .bulkMemory = false
  bulkMemoryOpt : S.has .bulkMemoryOpt = false
  callIndirect : S.has .callIndirect = false
  gcMut : S.has .gcMut = false
  simd : S.has .simd = false

theorem lacks_functional : Lacks functional := ⟨by decide, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide⟩

theorem not_has_of_le {S T : FeatureSet} (h : S ≤ T) {c : Cap} (hc : T.has c = false) :
    S.has c = false := by
  cases hs : S.has c
  · rfl
  · rw [has_of_le h hs] at hc
    exact absurd hc (by decide)

theorem Lacks.of_le {S T : FeatureSet} (h : S ≤ T) (hT : Lacks T) : Lacks S :=
  ⟨not_has_of_le h hT.memory, not_has_of_le h hT.table, not_has_of_le h hT.mutGlobal,
    not_has_of_le h hT.bulkMemory, not_has_of_le h hT.bulkMemoryOpt,
    not_has_of_le h hT.callIndirect, not_has_of_le h hT.gcMut, not_has_of_le h hT.simd⟩

theorem variable_allocOnly (hS : Lacks S) {c c' : Config H} (h : VariableStep c c')
    (hc : CodeIn S c.code) : AllocOnly c.store c'.store := by
  have := hS.mutGlobal
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB]

theorem table_allocOnly (hS : Lacks S) {P : Profile} {c c' : Config H} (h : TableStep P c c')
    (hc : CodeIn S c.code) : AllocOnly c.store c'.store := by
  have := hS.table
  have := hS.bulkMemory
  have := hS.callIndirect
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB, tblIdxB]

theorem memory_allocOnly (hS : Lacks S) {P : Profile} {c c' : Config H} (h : MemoryStep P c c')
    (hc : CodeIn S c.code) : AllocOnly c.store c'.store := by
  have := hS.memory
  have := hS.bulkMemory
  have := hS.bulkMemoryOpt
  have := hS.simd
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB, memIdxB]

theorem reference_allocOnly {c c' : Config H} (h : RefStep c c') : AllocOnly c.store c'.store := by
  cases h <;> simp

theorem aggregate_allocOnly (hS : Lacks S) {c c' : Config H} (h : AggregateStep c c')
    (hc : CodeIn S c.code) : AllocOnly c.store c'.store := by
  have := hS.gcMut
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB]

/-- **Functional code only allocates.** -/
theorem step_allocOnly (hS : Lacks S) {P : Profile} {host : HostSemantics H}
    (hh : HostAllocOnly host) {c c' : Config H} (h : Step P host c c') (hc : CodeIn S c.code) :
    AllocOnly c.store c'.store := by
  induction h with
  | parametric _ => exact allocOnly_refl _
  | numeric _ => exact allocOnly_refl _
  | vector _ => exact allocOnly_refl _
  | «variable» h => exact variable_allocOnly hS h hc
  | table h => exact table_allocOnly hS h hc
  | memory h => exact memory_allocOnly hS h hc
  | reference h => exact reference_allocOnly h
  | aggregate h => exact aggregate_allocOnly hS h hc
  | ctxtInstrs _ _ ih => exact ih (codeIn_append.mp (codeIn_append.mp hc).1).2
  | ctxtLabel _ ih => exact ih (admIn_label.mp (codeIn_cons.mp hc).1).2
  | ctxtHandler _ ih => exact ih (admIn_handler.mp (codeIn_cons.mp hc).1).2
  | ctxtFrame _ ih => exact ih (admIn_frame.mp (codeIn_cons.mp hc).1)
  | callRefHost _ _ _ _ _ hhost => exact hh _ _ _ _ _ hhost
  | throw => exact allocOnly_addExn _ _
  | _ => exact allocOnly_refl _

end Silmaril.Proofs.Wasm.Models.Functional
