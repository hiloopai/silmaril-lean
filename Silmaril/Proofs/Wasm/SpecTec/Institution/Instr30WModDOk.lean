module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WModDA

/-!
# Module typing of the wasm-3.0 script, `Module_ok` at memories and passive data

* `moduleOk_md`: in every evaluator `simEnv B` whose primitives answer
  `$clos_moduletype({MEMS mt*, DATAS OK*}, [] -> [])` with `v`, `Module_ok` derives
  `(mdModuleV mts ds, v)` whenever Core validates every `mt ∈ mts`, under every reading of
  `otherwise`.
* `moduleOk_md_inv`, `moduleOk_md_iff`: the converse, by `moduleOk_noImpExp_inv`; at
  `withClosMod B`, `Module_ok(mdModuleV mts ds, v)` holds exactly when `v = [] -> []` and every
  `mt` is valid. The data premise holds at every list of data images, so it adds no condition.
* Core: `mdModule_ok_iff`: when every data segment is passive, Core validates `mdModule mts ds`
  exactly at `[] -> []` and exactly when it validates every `mt ∈ mts`.
* `mdModule_sat_iff`: **the satisfaction condition is exact** on modules of memories and passive
  data segments, at `stepModel (withClosMod BI)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modPrems mtNil withClosMod ruleAt_moduleOk)

variable {B : Builtins}

/-- **Every premise of `Module_ok` holds at `mdModuleV mts ds`**, when Core validates every
`mt ∈ mts`. -/
theorem dprems_modD {mts : List Silmaril.Wasm.MemoryType} (ds : List Silmaril.Wasm.Data)
    (hv : ∀ mt ∈ mts, mt.Valid) (O : ElseI) (els : Prop) :
    ∀ pr ∈ modPrems, DPremB (simEnv B) O els (ρD mts ds) pr := by
  intro pr hpr
  simp only [modPrems, List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [dprem0_D mts ds O els, dprem1_D mts ds O els, dprem2_D mts ds O els,
    dprem3_D mts ds O els, dprem4_D ds hv O els, dprem5_D mts ds O els, dprem6_D mts ds O els,
    dprem7_D mts ds O els, dprem8_D mts ds O els, dprem9_D mts ds O els, dprem10_D mts ds O els,
    dprem11_D mts ds O els, dprem12_D mts ds O els, dprem13_D mts ds O els,
    dprem14_D mts ds O els, dprem15_D mts ds O els, dprem16_D mts ds O els,
    dprem17_D mts ds O els, dprem18_D mts ds O els, dprem19_D mts ds O els]

/-- **`Module_ok` validates every module of Core-valid memories and data segments**, at the module
type `v` the primitives give `$clos_moduletype({MEMS mt*, DATAS OK*}, [] -> [])`. -/
theorem moduleOk_md (O : ElseI) {mts : List Silmaril.Wasm.MemoryType} (ds : List Silmaril.Wasm.Data)
    (hv : ∀ mt ∈ mts, mt.Valid) {v : Value}
    (hB : B.call "clos_moduletype"
      [.val (ctxMD (mts.map Encode.toValue) (oksV ds)), .val mtNil] = some v) :
    DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [mdModuleV mts ds, v]) :=
  dderivesB_of_ruleAt ruleAt_moduleOk (self_mem_conclAlts _) (modσD mts ds) (quantsOk_modD mts ds)
    (evalExp_modConclD mts ds hB) (dprems_modD ds hv O _)

/-- **`Module_ok` is reflected at modules of memories and data**: a `Module_ok(mdModuleV mts ds, v)`
fact gives `mt.Valid` for every `mt ∈ mts`, and `v` is the primitives' answer to
`$clos_moduletype(C, [] -> [])` at some `C`. -/
theorem moduleOk_md_inv {O : ElseI} {mts : List Silmaril.Wasm.MemoryType}
    {ds : List Silmaril.Wasm.Data} {v : Value}
    (h : DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [mdModuleV mts ds, v])) :
    (∀ mt ∈ mts, mt.Valid) ∧ ∃ c, B.call "clos_moduletype" [.val c, .val mtNil] = some v :=
  let ⟨⟨_, _, fmem, hp4⟩, hB⟩ := moduleOk_noImpExp_inv h
  ⟨prem4_inv fmem hp4, hB⟩

/-- **`Module_ok` is exact at modules of memories and data, at the repaired primitives.** -/
theorem moduleOk_md_iff (O : ElseI) (mts : List Silmaril.Wasm.MemoryType)
    (ds : List Silmaril.Wasm.Data) (v : Value) :
    DDerivesB (simEnv (withClosMod B)) O "Module_ok" "|-%:%" [] (.tuple [mdModuleV mts ds, v]) ↔
      v = mtNil ∧ ∀ mt ∈ mts, mt.Valid := by
  constructor
  · intro h
    obtain ⟨hv, c, hB⟩ := moduleOk_md_inv h
    exact ⟨(Option.some.inj hB).symm, hv⟩
  · rintro ⟨rfl, hv⟩
    exact moduleOk_md O ds hv rfl

/-! ## The Core side -/

/-- A passive data segment is valid in every context. -/
theorem dataOk_of_passive {C : Context} {d : Silmaril.Wasm.Data} (h : Passive d) : DataOk C d := by
  unfold Passive at h
  unfold DataOk
  split at h
  · rename_i hm
    rw [hm]
    exact .passive
  · exact h.elim

/-- **Core validates `mdModule mts ds`, with passive data, exactly when it validates each memory
type**, and then at `[] -> []`. -/
theorem mdModule_ok_iff (mts : List Silmaril.Wasm.MemoryType) {ds : List Silmaril.Wasm.Data}
    (hp : ∀ d ∈ ds, Passive d) (τ : CModuleType) :
    ModuleOk (mdModule mts ds) τ ↔ τ = ⟨[], []⟩ ∧ ∀ mt ∈ mts, mt.Valid := by
  constructor
  · rintro ⟨htypes, himports, -, -, htags, -, hmems, -, -, -, -, -, hexports, -⟩
    cases himports
    cases hexports
    exact ⟨rfl, hmems⟩
  · rintro ⟨rfl, hv⟩
    exact ModuleOk.mk (dts := []) (jts := []) (gts := []) (tts := []) (fdts := []) (rts := [])
      TypesOk.nil .nil rfl rfl .nil GlobalsOk.nil hv .nil .nil
      (fun d hd => dataOk_of_passive (hp d hd)) .nil (fun _ h => nomatch h) .nil List.nodup_nil

/-- **The satisfaction condition is exact on modules of memories and passive data segments**: for
every host and profile, `stepModel (withClosMod BI)` has the fact `Module_ok(mdModuleV mts ds, v)`
exactly when Core validates `mdModule mts ds` at some `τ` (necessarily `[] -> []`) and `v` is its
image `[] -> []`. -/
theorem mdModule_sat_iff {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (mts : List Silmaril.Wasm.MemoryType)
    {ds : List Silmaril.Wasm.Data} (hp : ∀ d ∈ ds, Passive d) (v : Value) :
    (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
        (.tuple [mdModuleV mts ds, v]) ↔
      ∃ τ, ModuleOk (mdModule mts ds) τ ∧ τ = ⟨[], []⟩ ∧ v = mtNil := by
  constructor
  · intro h
    obtain ⟨rfl, hv⟩ := (moduleOk_md_iff _ mts ds v).1 h
    exact ⟨⟨[], []⟩, (mdModule_ok_iff mts hp _).2 ⟨rfl, hv⟩, rfl, rfl⟩
  · rintro ⟨τ, hτ, -, rfl⟩
    exact (moduleOk_md_iff _ mts ds _).2 ⟨rfl, ((mdModule_ok_iff mts hp τ).1 hτ).2⟩

/-- Non-vacuity: a module with one passive data segment of two bytes and no memory. -/
def dataSeg : Silmaril.Wasm.Data := ⟨⟨#[0x61, 0x62]⟩, .passive⟩

/-- **Non-vacuity**: `stepModel (withClosMod BI)` validates the module whose only definition is the
passive data segment `"ab"`, at `[] -> []`, and Core validates it at `[] -> []`. -/
theorem dataModule_ok {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
        (.tuple [mdModuleV [] [dataSeg], mtNil]) ∧ ModuleOk (mdModule [] [dataSeg]) ⟨[], []⟩ :=
  have hp : ∀ d ∈ [dataSeg], Passive d := fun d hd => by
    obtain rfl := List.mem_singleton.1 hd
    trivial
  ⟨moduleOk_md _ [dataSeg] (by simp) rfl,
    (mdModule_ok_iff [] hp _).2 ⟨rfl, by simp⟩⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30W
