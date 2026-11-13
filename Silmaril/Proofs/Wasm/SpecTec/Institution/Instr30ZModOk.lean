module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZModA
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZModB

/-!
# Module typing of the wasm-3.0 script, `Module_ok` at a module with one memory

* `moduleOk_mem`: in every evaluator `simEnv B` whose primitives answer
  `$clos_moduletype({MEMS [mt]}, [] -> [])` with `v`, `Module_ok` derives `(memModuleV [mt], v)`
  for every memory type `mt` that Core validates, under every reading of `otherwise`. All twenty
  premises are discharged in the scope `modσ1 mt`; the three that see the memory are `Mem_ok`
  (premise 4, through `Memtype_ok` and `Limits_ok`), the context equation (premise 12) and
  `$funcidx_nonfuncs` (premise 14, through `$free_mem`).
* `moduleOk_mem_repaired`: so `stepModel (withClosMod BI)` validates `memModuleV [mt]` at
  `[] -> []`, for every host and profile; `not_moduleOk_mem`: `stepModel BI` does not.
* Core: `memModule_ok_iff`: Core validates `memModule mts` (at `[] -> []`, its only possible type)
  exactly when it validates every `mt ∈ mts`. `memModule_sat`: every Core typing of a one-memory
  module is a `Module_ok` fact of `stepModel (withClosMod BI)`, at the image `[] -> []` of its type.
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

/-- **Every premise of `Module_ok` holds at `memModuleV [mt]`**, when Core validates `mt`. -/
theorem dprems_mod1 {mt : Silmaril.Wasm.MemoryType} (hv : mt.Valid) (O : ElseI) (els : Prop) :
    ∀ pr ∈ modPrems, DPremB (simEnv B) O els (ρ1 mt) pr := by
  intro pr hpr
  simp only [modPrems, List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [dprem0_1 mt O els, dprem1_1 mt O els, dprem2_1 mt O els, dprem3_1 mt O els,
    dprem4_1 hv O els, dprem5_1 mt O els, dprem6_1 mt O els, dprem7_1 mt O els, dprem8_1 mt O els,
    dprem9_1 mt O els, dprem10_1 mt O els, dprem11_1 mt O els, dprem12_1 mt O els,
    dprem13_1 mt O els, dprem14_1 mt O els, dprem15_1 mt O els, dprem16_1 mt O els,
    dprem17_1 mt O els, dprem18_1 mt O els, dprem19_1 mt O els]

/-- **`Module_ok` validates a module with one Core-valid memory**, at the module type `v` the
primitives give `$clos_moduletype({MEMS [mt]}, [] -> [])`, under every reading of `otherwise`. -/
theorem moduleOk_mem (O : ElseI) {mt : Silmaril.Wasm.MemoryType} (hv : mt.Valid) {v : Value}
    (hB : B.call "clos_moduletype" [.val (ctxMems [Encode.toValue mt]), .val mtNil] = some v) :
    DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [memModuleV [mt], v]) :=
  dderivesB_of_ruleAt ruleAt_moduleOk (self_mem_conclAlts _) (modσ1 mt) (quantsOk_mod1 mt)
    (evalExp_modConcl1 mt hB) (dprems_mod1 hv O _)

/-- **The repaired evaluator validates a module with one Core-valid memory** at `[] -> []`. -/
theorem moduleOk_mem_withClosMod (B : Builtins) {mt : Silmaril.Wasm.MemoryType} (hv : mt.Valid) :
    (Wasm30.stepModel (withClosMod B)).D "Module_ok" "|-%:%" [] (.tuple [memModuleV [mt], mtNil]) :=
  moduleOk_mem _ hv rfl

/-- **`stepModel (withClosMod BI)` validates every module with one Core-valid memory**, at
`[] -> []`, for every host and profile. -/
theorem moduleOk_mem_repaired {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {mt : Silmaril.Wasm.MemoryType}
    (hv : mt.Valid) :
    (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
      (.tuple [memModuleV [mt], mtNil]) :=
  moduleOk_mem_withClosMod _ hv

/-- **Without the repair, no module with memories is validated**: `stepModel BI` has no
`Module_ok` fact at `memModuleV mts`, at any module type (`Instr30X.stepModel_not_moduleOk`). -/
theorem not_moduleOk_mem {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (mts : List Silmaril.Wasm.MemoryType)
    (v : Value) :
    ¬ (Wasm30.stepModel (Round4Int.BI P hn host)).D "Module_ok" "|-%:%" []
      (.tuple [memModuleV mts, v]) :=
  Instr30X.stepModel_not_moduleOk P hn host _ _

/-! ## The Core side -/

/-- **Core validates `memModule mts` exactly when it validates each of its memory types**, and
then at `[] -> []`. -/
theorem memModule_ok_iff (mts : List Silmaril.Wasm.MemoryType) (τ : CModuleType) :
    ModuleOk (memModule mts) τ ↔ τ = ⟨[], []⟩ ∧ ∀ mt ∈ mts, mt.Valid := by
  constructor
  · rintro ⟨htypes, himports, -, -, htags, -, hmems, -, -, -, -, -, hexports, -⟩
    cases himports
    cases hexports
    exact ⟨rfl, hmems⟩
  · rintro ⟨rfl, hv⟩
    exact ModuleOk.mk (dts := []) (jts := []) (gts := []) (tts := []) (fdts := []) (rts := [])
      TypesOk.nil .nil rfl rfl .nil GlobalsOk.nil hv .nil .nil (fun _ h => nomatch h) .nil
      (fun _ h => nomatch h) .nil List.nodup_nil

/-- **Satisfaction at one memory**: every Core typing of `memModule [mt]` is a `Module_ok` fact of
`stepModel (withClosMod BI)`, at `[] -> []` (the image of its type `⟨[], []⟩`). -/
theorem memModule_sat {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {mt : Silmaril.Wasm.MemoryType}
    {τ : CModuleType} (h : ModuleOk (memModule [mt]) τ) :
    τ = ⟨[], []⟩ ∧ (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%"
      [] (.tuple [memModuleV [mt], mtNil]) := by
  obtain ⟨rfl, hv⟩ := (memModule_ok_iff [mt] τ).1 h
  exact ⟨rfl, moduleOk_mem_repaired P hn host (hv mt List.mem_cons_self)⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
