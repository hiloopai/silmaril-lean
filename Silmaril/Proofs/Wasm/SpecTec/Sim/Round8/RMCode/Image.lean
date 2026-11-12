module

public import Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.Defs

/-!
# Round 8, memory SIMD: the code-erased image is the image of the named host store

`eraseC_configVD`: at a configuration whose code holds no memory SIMD instruction,
`eraseC (configVD hn c) = configV id (hostC hn c)`. Only the `CODE` fields of the function
instances change (`eraseC_funcInstVD`); every other part of the image has no `CODE` record
(`Round8.CodeErase.Swap.ncB_*`), so `eraseC` fixes it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMCode

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Round6.MemSimd (AdminsMS)
open Round7.MemSimd (funcInstVD storeVD stateVD configVD)
open CodeErase.Swap

variable {H : Type}

theorem funcInstVD_eq (hn : H → String) (fi : FuncInst H) :
    funcInstVD hn fi = .struct [("TYPE", CT.defType fi.type),
      ("MODULE", moduleInstToValue CT fi.module), ("CODE", codeVD hn fi)] := by
  obtain ⟨ty, m, code⟩ := fi
  cases code <;> rfl

theorem ncB_defType (fi : FuncInst H) : ncB (CT.defType fi.type) = true := by
  simp [CT]

/-- **Erasing a function instance's code gives the named host function's image.** -/
theorem eraseC_funcInstVD (hn : H → String) (fi : FuncInst H) :
    eraseC (funcInstVD hn fi) = funcInstV id (hostSFI hn fi) := by
  rw [funcInstVD_eq]
  simp only [eraseC_struct, eraseCf_cons, eraseCf_nil, String.reduceEq, ite_false, ite_true,
    eraseC_of_ncB _ (ncB_defType fi), eraseC_of_ncB _ (ncB_moduleInstToValue fi.module)]
  rfl

theorem eraseC_storeVD (hn : H → String) (s : Store H) :
    eraseC (storeVD hn s) = storeV id (hostifyS hn s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ncB_storeRest (H := H) s
  simp only [storeVD, storeV, hostifyS, eraseC_struct, eraseCf_cons, eraseCf_nil,
    String.reduceEq, ite_false]
  rw [eraseC_of_ncB _ h1, eraseC_of_ncB _ h2, eraseC_of_ncB _ h3, eraseC_of_ncB _ h4,
    eraseC_of_ncB _ h5, eraseC_of_ncB _ h6, eraseC_of_ncB _ h7, eraseC_of_ncB _ h8,
    eraseC_of_ncB _ h9, eraseC_list', List.map_map, List.map_map]
  have hf : (eraseC ∘ funcInstVD hn) = (funcInstV id ∘ hostSFI hn) :=
    funext fun fi => eraseC_funcInstVD hn fi
  rw [hf]

/-- **The code-erased image of a configuration with memory-SIMD-free code is the image of the
configuration over the named host store.** -/
theorem eraseC_configVD (hn : H → String) {c : Config H} (hms : AdminsMS c.code) :
    eraseC (configVD hn c) = configV id (hostC hn c) := by
  simp only [configVD, stateVD, configV, stateV, hostC, eraseC_case, eraseC_tuple, eraseCs,
    eraseC_storeVD, eraseC_frameV, eraseC_list, Round7.MemSimd.adminsToVD_eq c.code hms,
    eraseCs_adminsToV]

/-- `eraseC` fixes the image of a code sequence. -/
theorem eraseC_adminsList (l : List Admin) : eraseC (.list (adminsToV l)) = .list (adminsToV l) := by
  rw [eraseC_list, eraseCs_adminsToV]

end Silmaril.Wasm.SpecTec.Sim.Round8.RMCode
