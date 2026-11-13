module

public import Silmaril.Wasm.Det.CompRef.Thms
public import Silmaril.Wasm.Component.Reference.Litmus.Thms
public import Silmaril.Wasm.Det.NoMem.Thms
public import Silmaril.Wasm.Det.Stateless.Thms
public import Silmaril.Wasm.Link.Recipe

/-!
# The adder component is deterministic and stateless on the reference machine (litmus)

The module of `adderS` (`binCore3 .add`, no imports) has one instance store, `binStore .add`
(`isInst_store`: every `IsInst` instance is the result of `instantiateOnce?`), which passes the
executable checks of the no-memory and stateless subsets (kernel evaluation). So `ModDet` and
`ModStateless` hold at every profile, and `simple_returns_eq`/`simple_seq_returns_eq` apply.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.CompRef.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
  Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.CompRef Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)

theorem storeB_bin : Silmaril.Wasm.Det.NoMem.storeB (binStore .add) = true := by decide +kernel
theorem stateless_bin : Silmaril.Wasm.Det.Stateless.moduleStatelessCheck (binStore .add) = true := by
  decide +kernel

/-- Every instance of the adder's module has the store `binStore .add`. -/
theorem isInst_store {I : ScalarInstance} (h : adderS.mod.IsInst I) : I.store = binStore .add := by
  obtain ⟨⟨mt, hi⟩, -, -⟩ := h
  have hl : mt.imports = [] :=
    List.eq_nil_of_length_eq_zero (Silmaril.Wasm.Link.GC.Recipe.validation_imports_length hi.valid)
  obtain ⟨f, hf, -⟩ := hi.instantiated
  rw [hl] at hf
  have hb : binStore .add = I.store := by
    unfold binStore
    rw [show Silmaril.Wasm.Validation.CExternType.funcs [] = [] from rfl] at hf
    simp only [List.length_nil, List.range_zero, List.map_nil] at hf
    have hf' : Silmaril.Wasm.Execution.Core.instantiateOnce? (importStore [])
        (binCore3 .add) [] = some (I.store, f, none) := hf
    rw [hf']
  exact hb.symm

theorem adder_modDet (P : Profile) : ModDet P adderS.mod := fun I h => by
  rw [isInst_store h]
  exact Silmaril.Wasm.Det.NoMem.detModule_of_storeB storeB_bin

theorem adder_modStateless (P : Profile) : ModStateless P adderS.mod := fun I h => by
  rw [isInst_store h]
  exact Silmaril.Wasm.Det.Stateless.statelessModule_of_check stateless_bin

theorem adderS_floatFree : adderS.FloatFree := by
  intro x hx
  simp only [adderS, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, rfl⟩

end Silmaril.Proofs.Wasm.Det.CompRef.Litmus
