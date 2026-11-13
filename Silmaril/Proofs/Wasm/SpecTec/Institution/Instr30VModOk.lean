module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30VModA

/-!
# Module typing of the wasm-3.0 script, ws5 `Module_ok` at active data segments

* `moduleOk_mdv`: in every evaluator `simEnv B` whose primitives answer
  `$clos_moduletype({MEMS mt*, DATAS OK*}, [] -> [])` with `v`, `Module_ok` derives
  `(mdvModuleV mts dvs, v)` for **any** data images `dvs` that are typed and have `Data_ok` facts
  in that context, when Core validates every `mt ∈ mts`.
* `moduleOk_mda`: at the images `dataVA d` of passive or constant-active segments (`DataShape`).
* `moduleOk_mdv_inv`: reflection of the memories and of `v`, at any data images;
  `moduleOk_mda_iff`: at `withClosMod B`, exact on `DataShape` modules.
* Core: `dataOk_of_shape`, `mdaModule_ok_iff`: Core validates a module of memories and
  `DataShape` data segments exactly at `[] -> []` and exactly when every memory type is valid.
* `mdaModule_sat_iff`: **the satisfaction condition is exact** on modules of memories and passive
  or constant-active data segments, at `stepModel (withClosMod BI)`.
* `mdvModuleV_passive`: at passive segments the image is an earlier `Instr30W.mdModuleV`.
* `activeModule_ok`: non-vacuity, a module with one `i32` memory and one active segment
  `(i32.const 0) "ab"`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30V

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modPrems mtNil withClosMod ruleAt_moduleOk)
open Silmaril.Wasm.SpecTec.Institution.Instr30W (okV mdModule Passive dataOk_of_passive)

variable {B : Builtins}

/-- **Every premise of `Module_ok` holds at `mdvModuleV mts dvs`**, when Core validates every
`mt ∈ mts` and every image has a `Data_ok` fact. -/
theorem dprems_modV {mts : List MemoryType} {dvs : List Value} (hv : ∀ mt ∈ mts, mt.Valid)
    (O : ElseI)
    (hdd : ∀ dv ∈ dvs, DDerivesB (simEnv B) O "Data_ok" "%|-%:%" [] (.tuple [ctxV mts dvs, dv, okV]))
    (els : Prop) : ∀ pr ∈ modPrems, DPremB (simEnv B) O els (ρV mts dvs) pr := by
  intro pr hpr
  simp only [modPrems, List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [dprem0_V mts dvs O els, dprem1_V mts dvs O els, dprem2_V mts dvs O els,
    dprem3_V mts dvs O els, dprem4_V dvs hv O els, dprem5_V mts dvs O els, dprem6_V mts dvs O els,
    dprem7_V mts O hdd els, dprem8_V mts dvs O els, dprem9_V mts dvs O els,
    dprem10_V mts dvs O els, dprem11_V mts dvs O els, dprem12_V mts dvs O els,
    dprem13_V mts dvs O els, dprem14_V mts dvs O els, dprem15_V mts dvs O els,
    dprem16_V mts dvs O els, dprem17_V mts dvs O els, dprem18_V mts dvs O els,
    dprem19_V mts dvs O els]

/-- **`Module_ok` validates memories and any typed data images with `Data_ok` facts**, at the
module type `v` the primitives give `$clos_moduletype({MEMS mt*, DATAS OK*}, [] -> [])`. -/
theorem moduleOk_mdv (O : ElseI) {mts : List MemoryType} {dvs : List Value}
    (hv : ∀ mt ∈ mts, mt.Valid) (hdv : ∀ dv ∈ dvs, TypedV (simEnv B) (.varT "data" []) dv)
    (hdd : ∀ dv ∈ dvs, DDerivesB (simEnv B) O "Data_ok" "%|-%:%" [] (.tuple [ctxV mts dvs, dv, okV]))
    {v : Value} (hB : B.call "clos_moduletype" [.val (ctxV mts dvs), .val mtNil] = some v) :
    DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [mdvModuleV mts dvs, v]) :=
  dderivesB_of_ruleAt ruleAt_moduleOk (self_mem_conclAlts _) (modσV mts dvs) (quantsOk_modV mts hdv)
    (evalExp_modConclV mts dvs hB) (dprems_modV hv O hdd _)

/-- **`Module_ok` validates memories and passive or constant-active data segments.** -/
theorem moduleOk_mda (O : ElseI) {mts : List MemoryType} {ds : List Data}
    (hv : ∀ mt ∈ mts, mt.Valid) (hs : ∀ d ∈ ds, DataShape mts d) {v : Value}
    (hB : B.call "clos_moduletype" [.val (ctxV mts (ds.map dataVA)), .val mtNil] = some v) :
    DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [mdvModuleV mts (ds.map dataVA), v]) :=
  moduleOk_mdv O hv
    (fun dv hdv => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hdv
      exact typedV_dataVA (hs d hd))
    (fun dv hdv => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hdv
      exact dd_dataOkA O (ctxT_v mts _) (hs d hd)) hB

/-- **Reflection of memories and of `v` at any data images**: a `Module_ok(mdvModuleV mts dvs, v)`
fact gives `mt.Valid` for every `mt ∈ mts`, and `v` is the primitives' answer to
`$clos_moduletype(C, [] -> [])` at some `C`. -/
theorem moduleOk_mdv_inv {O : ElseI} {mts : List MemoryType} {dvs : List Value} {v : Value}
    (h : DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [mdvModuleV mts dvs, v])) :
    (∀ mt ∈ mts, mt.Valid) ∧ ∃ c, B.call "clos_moduletype" [.val c, .val mtNil] = some v :=
  let ⟨⟨_, _, fmem, hp4⟩, hB⟩ := Instr30W.moduleOk_noImpExp_inv h
  ⟨Instr30W.prem4_inv fmem hp4, hB⟩

/-- **`Module_ok` is exact at modules of memories and `DataShape` data, at the repaired
primitives.** -/
theorem moduleOk_mda_iff (O : ElseI) (mts : List MemoryType) {ds : List Data}
    (hs : ∀ d ∈ ds, DataShape mts d) (v : Value) :
    DDerivesB (simEnv (withClosMod B)) O "Module_ok" "|-%:%" []
        (.tuple [mdvModuleV mts (ds.map dataVA), v]) ↔
      v = mtNil ∧ ∀ mt ∈ mts, mt.Valid := by
  constructor
  · intro h
    obtain ⟨hv, c, hB⟩ := moduleOk_mdv_inv h
    exact ⟨(Option.some.inj hB).symm, hv⟩
  · rintro ⟨rfl, hv⟩
    exact moduleOk_mda O hv hs rfl

/-- At passive segments, the image is an earlier. -/
theorem mdvModuleV_passive (mts : List MemoryType) {ds : List Data} (hp : ∀ d ∈ ds, Passive d) :
    mdvModuleV mts (ds.map dataVA) = Instr30W.mdModuleV mts ds := by
  have e : ds.map dataVA = ds.map Instr30W.dataV := List.map_congr_left fun d hd =>
    dataVA_passive (hp d hd)
  rw [e]
  rfl

/-! ## The Core side -/

/-- **A passive or constant-active data segment is valid** in every context whose memories are
`mts`. -/
theorem dataOk_of_shape {C : Context} {mts : List MemoryType} (hm : C.mems = mts) {d : Data}
    (h : DataShape mts d) : DataOk C d := by
  rcases h with hp | ⟨x, mt, b, he, hx⟩
  · exact dataOk_of_passive hp
  · unfold DataOk
    rw [he]
    exact .active (a := mt.address) (l := mt.limits) (by rw [hm, hx])
      ⟨.instr (.numeric (.intConst _ b)), fun i hi => by
        obtain rfl := List.mem_singleton.1 hi
        exact .intConst _ b⟩

/-- **Core validates `mdModule mts ds`, with `DataShape` data, exactly when it validates each
memory type**, and then at `[] -> []`. -/
theorem mdaModule_ok_iff (mts : List MemoryType) {ds : List Data} (hs : ∀ d ∈ ds, DataShape mts d)
    (τ : CModuleType) : ModuleOk (mdModule mts ds) τ ↔ τ = ⟨[], []⟩ ∧ ∀ mt ∈ mts, mt.Valid := by
  constructor
  · rintro ⟨htypes, himports, -, -, htags, -, hmems, -, -, -, -, -, hexports, -⟩
    cases himports
    cases hexports
    exact ⟨rfl, hmems⟩
  · rintro ⟨rfl, hv⟩
    exact ModuleOk.mk (dts := []) (jts := []) (gts := []) (tts := []) (fdts := []) (rts := [])
      TypesOk.nil .nil rfl rfl .nil GlobalsOk.nil hv .nil .nil
      (fun d hd => dataOk_of_shape rfl (hs d hd)) .nil (fun _ h => nomatch h) .nil List.nodup_nil

/-- **The satisfaction condition is exact on modules of memories and passive or constant-active
data segments**: for every host and profile, `stepModel (withClosMod BI)` has the fact
`Module_ok(mdvModuleV mts (dataVA d*), v)` exactly when Core validates `mdModule mts ds` at some
`τ` (necessarily `[] -> []`) and `v` is its image `[] -> []`. -/
theorem mdaModule_sat_iff {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (mts : List MemoryType) {ds : List Data}
    (hs : ∀ d ∈ ds, DataShape mts d) (v : Value) :
    (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
        (.tuple [mdvModuleV mts (ds.map dataVA), v]) ↔
      ∃ τ, ModuleOk (mdModule mts ds) τ ∧ τ = ⟨[], []⟩ ∧ v = mtNil := by
  constructor
  · intro h
    obtain ⟨rfl, hv⟩ := (moduleOk_mda_iff _ mts hs v).1 h
    exact ⟨⟨[], []⟩, (mdaModule_ok_iff mts hs _).2 ⟨rfl, hv⟩, rfl, rfl⟩
  · rintro ⟨τ, hτ, -, rfl⟩
    exact (moduleOk_mda_iff _ mts hs _).2 ⟨rfl, ((mdaModule_ok_iff mts hs τ).1 hτ).2⟩

/-! ## Non-vacuity -/

/-- One `i32` memory of at least one page. -/
def mem1 : MemoryType := ⟨.i32, ⟨1, none⟩⟩

/-- The active data segment `(i32.const 0) "ab"` in memory 0. -/
def activeSeg : Data := ⟨⟨#[0x61, 0x62]⟩, .active ⟨0⟩ [.intConst .i32 0]⟩

/-- `activeSeg` is constant-active in `[mem1]`. -/
theorem activeSeg_shape : DataShape [mem1] activeSeg := .inr ⟨⟨0⟩, mem1, 0, rfl, rfl⟩

/-- **Non-vacuity**: `stepModel (withClosMod BI)` validates the module of one `i32` memory and the
active segment `(i32.const 0) "ab"`, at `[] -> []`, and Core validates it at `[] -> []`. -/
theorem activeModule_ok {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
        (.tuple [mdvModuleV [mem1] [dataVA activeSeg], mtNil]) ∧
      ModuleOk (mdModule [mem1] [activeSeg]) ⟨[], []⟩ :=
  have hs : ∀ d ∈ [activeSeg], DataShape [mem1] d := fun d hd => by
    obtain rfl := List.mem_singleton.1 hd
    exact activeSeg_shape
  have hv : ∀ mt ∈ [mem1], mt.Valid := fun mt hmt => by
    obtain rfl := List.mem_singleton.1 hmt
    decide
  ⟨moduleOk_mda _ hv hs rfl, (mdaModule_ok_iff [mem1] hs _).2 ⟨rfl, hv⟩⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30V
