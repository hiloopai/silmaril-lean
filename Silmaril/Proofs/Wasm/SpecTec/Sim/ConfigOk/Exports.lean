module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Step

/-!
# Finding (fixed in round 4): the ported export encoding is never typed

The ported runtime bridge wrote an export's name as a text value:
`exportInstToValueText e = {NAME (.text e.name), ADDR …}`. The IL type of that field is `name`,
a one-case variant `name ::= % char* -- if |$utf8(char*)| < 2^32` (`1.1-syntax.values`), whose
inhabitants are `case` values, never texts. So:

* `not_hasTyp_exportinstText`: no export encoded that way is an `exportinst`;
* `not_typedV_moduleinstText_of_export`: a module instance with at least one export, encoded that
  way, is not a typed `moduleinst`.

Round 3 drew the consequences for the configuration encoding (no frame, store or configuration
whose modules export anything was `Typed`; with the witness `exportConfig`, Core typing did not
imply `Typed` for any `B`). Round 4 applied the fix (upstream item U4,
`docs/projects/spectec/README.md`): `RuntimeBridge.exportInstToValue` now writes `NAME` as
`nameToValue`, `.case "%" (.tuple [.list chars])` with each character
`.case "%" (.tuple [.num (.natN c.toNat)])`, so those configuration-level refutations no longer
hold and were retired (they are recorded at `06a61e534`). The text encoding is kept as
`RuntimeBridge.exportInstToValueText`. Typing a name still evaluates `$utf8`, whose clauses bind
their result bytes through `if` premises (so the evaluator leaves them to `B`), and needs its
byte length below `2 ^ 32`, a bound Core does not impose on `String` (`Round4.ModuleBnd`).

`exportConfig` (one global, exported, empty code) stays as a Core-typed example
(`configOk_exportConfig`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.ConfigOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Equiv.RuntimeBridge (exportInstToValueText)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {B : Builtins}

/-- The type of a record field declaration. -/
def fieldTyp : TypField → Typ
  | .mk _ t _ _ => t

/-- A typed record has typed fields, positionally. -/
theorem hasTypFields_forall₂ {env : Env} {σ : VarEnv} :
    ∀ {fs : List TypField} {gs : List (AtomS × Value)}, HasTypFields env σ fs gs →
      List.Forall₂ (fun f g => HasTyp env σ (fieldTyp f) g.2) fs gs
  | [], gs, h => by rw [hasTypFields_nil_iff.1 h]; exact .nil
  | .mk _ _ _ _ :: _, _, h => by
    obtain ⟨_, _, rfl, hw, -, hr⟩ := hasTypFields_cons_iff.1 h
    exact .cons hw (hasTypFields_forall₂ hr)

/-- The empty scope binds term variables only. -/
theorem valsOnly_empty : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩

/-- **Inversion of a closed record type**: a typed record has typed fields, in the empty scope. -/
theorem hasTypFields_of_closedStruct {x : IL.Id} {fs : List TypField} {ρ : VarEnv}
    (hρ : ValsOnly ρ) (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.structT fs)]))
    {gs : List (AtomS × Value)} (h : HasTyp (simEnv B) ρ (.varT x []) (.struct gs)) :
    List.Forall₂ (fun f g => HasTyp (simEnv B) VarEnv.empty (fieldTyp f) g.2) fs gs := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := IntNumeric.matchArgs_nil_scope hm
    obtain ⟨gs', he, hf⟩ := hasTypDef_structT_iff.1 hd
    cases he
    exact hasTypFields_forall₂ hf
  · exact absurd hrest not_hasTypInsts_nil

set_option maxRecDepth 100000 in
theorem findTyp_name :
    ∃ cs, (simEnv B).findTyp? "name" = some ([], [.instD [] [] (.variantT cs)]) :=
  ⟨_, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_moduleinst' : (simEnv B).findTyp? "moduleinst" = some ([], [.instD [] [] (.structT
    [.mk "TYPES" (.iterT (.varT "deftype" []) .list) [] [],
     .mk "TAGS" (.iterT (.varT "tagaddr" []) .list) [] [],
     .mk "GLOBALS" (.iterT (.varT "globaladdr" []) .list) [] [],
     .mk "MEMS" (.iterT (.varT "memaddr" []) .list) [] [],
     .mk "TABLES" (.iterT (.varT "tableaddr" []) .list) [] [],
     .mk "FUNCS" (.iterT (.varT "funcaddr" []) .list) [] [],
     .mk "DATAS" (.iterT (.varT "dataaddr" []) .list) [] [],
     .mk "ELEMS" (.iterT (.varT "elemaddr" []) .list) [] [],
     .mk "EXPORTS" (.iterT (.varT "exportinst" []) .list) [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_exportinst : (simEnv B).findTyp? "exportinst" = some ([], [.instD [] [] (.structT
    [.mk "NAME" (.varT "name" []) [] [], .mk "ADDR" (.varT "externaddr" []) [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_funcinst : (simEnv B).findTyp? "funcinst" = some ([], [.instD [] [] (.structT
    [.mk "TYPE" (.varT "deftype" []) [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
     .mk "CODE" (.varT "funccode" []) [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_store' : (simEnv B).findTyp? "store" = some ([], [.instD [] [] (.structT
    [.mk "TAGS" (.iterT (.varT "taginst" []) .list) [] [],
     .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
     .mk "MEMS" (.iterT (.varT "meminst" []) .list) [] [],
     .mk "TABLES" (.iterT (.varT "tableinst" []) .list) [] [],
     .mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [],
     .mk "DATAS" (.iterT (.varT "datainst" []) .list) [] [],
     .mk "ELEMS" (.iterT (.varT "eleminst" []) .list) [] [],
     .mk "STRUCTS" (.iterT (.varT "structinst" []) .list) [] [],
     .mk "ARRAYS" (.iterT (.varT "arrayinst" []) .list) [] [],
     .mk "EXNS" (.iterT (.varT "exninst" []) .list) [] []])]) := rfl

/-- A text is never a `name`. -/
theorem not_hasTyp_name_text {ρ : VarEnv} (hρ : ValsOnly ρ) (t : String) :
    ¬ HasTyp (simEnv B) ρ (.varT "name" []) (.text t) := by
  intro h
  obtain ⟨cs, htd⟩ := findTyp_name (B := B)
  obtain ⟨_, _, he⟩ := hasTyp_varT_case_of_variant
    (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd
    (by rintro _ _ _ h; simp at h; exact ⟨_, h.2.2⟩) h
  cases he

/-- An export instance encoded as copied (`NAME` a text) is never an `exportinst`. -/
theorem not_hasTyp_exportinstText {ρ : VarEnv} (hρ : ValsOnly ρ) (e : Execution.Core.ExportInst) :
    ¬ HasTyp (simEnv B) ρ (.varT "exportinst" []) (exportInstToValueText e) := by
  intro h
  have hF := hasTypFields_of_closedStruct hρ findTyp_exportinst h
  simp only [List.forall₂_cons] at hF
  exact not_hasTyp_name_text valsOnly_empty e.name hF.1

/-- `moduleinst`, with the exports encoded as copied (`exportInstToValueText`). -/
def moduleInstToValueText (m : Execution.Core.ModuleInst) : Value :=
  .struct
    [("TYPES", .list (m.types.map CT.defType)),
     ("TAGS", .list (m.tags.map fun a => .num (.natN a))),
     ("GLOBALS", .list (m.globals.map fun a => .num (.natN a))),
     ("MEMS", .list (m.mems.map fun a => .num (.natN a))),
     ("TABLES", .list (m.tables.map fun a => .num (.natN a))),
     ("FUNCS", .list (m.funcs.map fun a => .num (.natN a))),
     ("DATAS", .list (m.datas.map fun a => .num (.natN a))),
     ("ELEMS", .list (m.elems.map fun a => .num (.natN a))),
     ("EXPORTS", .list (m.exports.map exportInstToValueText))]

/-- **A module instance with an export, encoded as copied, is not a typed `moduleinst`.** -/
theorem not_typedV_moduleinstText_of_export (m : Execution.Core.ModuleInst)
    {e : Execution.Core.ExportInst} (he : e ∈ m.exports) :
    ¬ TypedV (simEnv B) (.varT "moduleinst" []) (moduleInstToValueText m) := by
  intro h
  have hF := hasTypFields_of_closedStruct valsOnly_empty findTyp_moduleinst'
    (h _ valsOnly_empty)
  simp only [List.forall₂_cons] at hF
  obtain ⟨l, hl', hl⟩ := hasTyp_iterT_list_iff.1 hF.2.2.2.2.2.2.2.2.1
  cases hl'
  exact not_hasTyp_exportinstText valsOnly_empty e
    (hasTypList_iff.1 hl _ (List.mem_map_of_mem he))

/-! ## A Core-typed configuration with an export -/

/-- An immutable `i32` global holding `0`. -/
def global0 : Execution.Core.GlobalInst :=
  ⟨⟨.const, .num (.int .i32)⟩, .num ⟨.int .i32, 0⟩⟩

/-- The store holding `global0` only. -/
def exportStore : Execution.Core.Store H := { globals := [global0] }

/-- The module instance exporting global `0` as `"g"`. -/
def exportModule : Execution.Core.ModuleInst :=
  { globals := [0], exports := [⟨"g", .global 0⟩] }

/-- `exportModule`'s frame, with empty code, over `exportStore`. -/
def exportConfig : Execution.Core.Config H :=
  ⟨exportStore, ⟨[], exportModule⟩, []⟩

/-- `exportStore` is typed by Core. -/
theorem coreStoreOk_exportStore : Execution.Core.StoreOk (exportStore (H := H)) where
  tags := by simp [exportStore]
  globals := by
    simp only [exportStore, List.mem_singleton]
    rintro _ rfl
    exact ⟨.num _, .num _⟩
  mems := by simp [exportStore]
  tables := by simp [exportStore]
  funcs := by simp [exportStore]
  elems := by simp [exportStore]
  structs := by simp [exportStore]
  arrays := by simp [exportStore]
  exns := by simp [exportStore]
  acyclicStructs := by simp [exportStore]
  acyclicArrays := by simp [exportStore]
  acyclicExns := by simp [exportStore]
  structsClosed := by simp [exportStore]
  arraysClosed := by simp [exportStore]

/-- `exportModule` is typed by Core over `exportStore`. -/
theorem moduleInstOk_exportModule :
    ∃ C, Execution.Core.ModuleInstOk (exportStore (H := H)) exportModule C :=
  ⟨_, .mk (k := 0) (by simp [exportModule]) .nil (.cons (.global rfl) .nil) .nil .nil .nil
    (by simp [exportModule]) .nil
    (by simp only [exportModule, List.mem_singleton]; rintro _ rfl; exact ⟨_, .global rfl⟩)
    (by simp [exportModule]) (by simp [exportModule]) (Nat.zero_le _)⟩

/-- **`exportConfig` is typed by Core** (`⊢ config : []`). -/
theorem configOk_exportConfig : Execution.Core.ConfigOk (exportConfig (H := H)) [] := by
  obtain ⟨C, hC⟩ := moduleInstOk_exportModule (H := H)
  exact ⟨_, ⟨coreStoreOk_exportStore, C, [], hC, .nil, rfl⟩, .nil⟩

end Silmaril.Wasm.SpecTec.Sim.ConfigOk
