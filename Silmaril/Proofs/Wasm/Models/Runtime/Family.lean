module

public import Silmaril.Proofs.Wasm.Models.Runtime.Basic
public import Silmaril.Wasm.Models.Features.Thms

/-!
# The runtime invariant: the delegated reduction families

Each family of Core 3.0 rules (parametric, numeric, vector, variable, table, memory, reference,
aggregate) keeps code of `S` in `S` and does not touch the store's functions. The right-hand
sides are values, traps, or the expansion forms `Rt.instrB` allows (`table.fill` to
`table.set`, `table.copy` to `table.get`/`table.set`, `memory.fill/copy/init` to byte
loads/stores, `array.fill/copy/init_*` to `array.get`/`array.set`, `struct.new_default` to
`struct.new`, `array.new*` to `array.new_fixed`, `local.tee` to `local.set`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Rt

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Models
  Silmaril.Wasm.Models.Rt

variable {S : FeatureSet} {H : Type}

theorem has_gcImm_of_gcMut (h : S.has .gcMut = true) : S.has .gcImm = true :=
  has_pre h (by decide)

theorem parametric_codeIn {is is' : List Admin} (h : ParametricStep is is') (hc : CodeIn S is) :
    CodeIn S is' := by
  cases h <;> simp_all

theorem numeric_codeIn {P : Profile} {is is' : List Admin} (h : NumericStep P is is')
    (hc : CodeIn S is) : CodeIn S is' := by
  cases h <;> simp_all

theorem vector_codeIn {P : Profile} {is is' : List Admin} (h : VectorStep P is is')
    (hc : CodeIn S is) : CodeIn S is' := by
  cases h <;> simp_all [vconst]

theorem variable_codeIn {c c' : Config H} (h : VariableStep c c') (hc : CodeIn S c.code) :
    CodeIn S c'.code ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB, Store.setGlobal]

theorem table_codeIn {P : Profile} {c c' : Config H} (h : TableStep P c c')
    (hc : CodeIn S c.code) : CodeIn S c'.code ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB, Store.setTable, Store.setElem]

theorem memory_codeIn {P : Profile} {c c' : Config H} (h : MemoryStep P c c')
    (hc : CodeIn S c.code) : CodeIn S c'.code ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB, Store.setMem, Store.setData,
    store8, load8u]

theorem reference_codeIn {c c' : Config H} (h : RefStep c c') (hc : CodeIn S c.code) :
    CodeIn S c'.code ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> simp_all

theorem aggregate_codeIn {c c' : Config H} (h : AggregateStep c c') (hc : CodeIn S c.code) :
    CodeIn S c'.code ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB, arrRef, has_gcImm_of_gcMut,
    Store.addStruct, Store.setStructField, Store.addArray, Store.setArrayField]

end Silmaril.Proofs.Wasm.Models.Rt
