module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZModLA
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZModOk

/-!
# Module typing of the wasm-3.0 script, `Module_ok` at every memory-only module

* `moduleOk_memL`: in every evaluator `simEnv B` whose primitives answer
  `$clos_moduletype({MEMS mts}, [] -> [])` with `v`, `Module_ok` derives `(memModuleV mts, v)` for
  every list `mts` of memory types that Core validates, under every reading of `otherwise`.
* `moduleOk_memL_repaired`: so `stepModel (withClosMod BI)` validates every such module at
  `[] -> []`, for every host and profile.
* `memModule_satL`: **satisfaction on memory-only modules**: every Core typing of `memModule mts`
  is a `Module_ok` fact of `stepModel (withClosMod BI)` at the image `[] -> []` of its type.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modPrems mtNil withClosMod ruleAt_moduleOk)

variable {B : Builtins}

/-- **Every premise of `Module_ok` holds at `memModuleV mts`**, when Core validates every
`mt ∈ mts`. -/
theorem dprems_modL {mts : List Silmaril.Wasm.MemoryType} (hv : ∀ mt ∈ mts, mt.Valid) (O : ElseI)
    (els : Prop) : ∀ pr ∈ modPrems, DPremB (simEnv B) O els (ρL mts) pr := by
  intro pr hpr
  simp only [modPrems, List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [dprem0_L mts O els, dprem1_L mts O els, dprem2_L mts O els, dprem3_L mts O els,
    dprem4_L hv O els, dprem5_L mts O els, dprem6_L mts O els, dprem7_L mts O els,
    dprem8_L mts O els, dprem9_L mts O els, dprem10_L mts O els, dprem11_L mts O els,
    dprem12_L mts O els, dprem13_L mts O els, dprem14_L mts O els, dprem15_L mts O els,
    dprem16_L mts O els, dprem17_L mts O els, dprem18_L mts O els, dprem19_L mts O els]

/-- **`Module_ok` validates every module whose only definitions are Core-valid memories**, at the
module type `v` the primitives give `$clos_moduletype({MEMS mts}, [] -> [])`. -/
theorem moduleOk_memL (O : ElseI) {mts : List Silmaril.Wasm.MemoryType}
    (hv : ∀ mt ∈ mts, mt.Valid) {v : Value}
    (hB : B.call "clos_moduletype" [.val (ctxMems (mts.map Encode.toValue)), .val mtNil] = some v) :
    DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [memModuleV mts, v]) :=
  dderivesB_of_ruleAt ruleAt_moduleOk (self_mem_conclAlts _) (modσL mts) (quantsOk_modL mts)
    (evalExp_modConclL mts hB) (dprems_modL hv O _)

/-- **`stepModel (withClosMod BI)` validates every memory-only module whose memory types Core
validates**, at `[] -> []`, for every host and profile. -/
theorem moduleOk_memL_repaired {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {mts : List Silmaril.Wasm.MemoryType}
    (hv : ∀ mt ∈ mts, mt.Valid) :
    (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
      (.tuple [memModuleV mts, mtNil]) :=
  moduleOk_memL _ hv rfl

/-- **Satisfaction on memory-only modules**: every Core typing `τ` of `memModule mts` is
`[] -> []`, and `stepModel (withClosMod BI)` has the `Module_ok` fact at its image. -/
theorem memModule_satL {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {mts : List Silmaril.Wasm.MemoryType}
    {τ : CModuleType} (h : ModuleOk (memModule mts) τ) :
    τ = ⟨[], []⟩ ∧ (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok"
      "|-%:%" [] (.tuple [memModuleV mts, mtNil]) := by
  obtain ⟨rfl, hv⟩ := (memModule_ok_iff mts τ).1 h
  exact ⟨rfl, moduleOk_memL_repaired P hn host hv⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
