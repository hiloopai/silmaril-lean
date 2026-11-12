module

public import Silmaril.Wasm.SpecTec.Sim.Round8.RMHost.Defs

/-!
# Round 8, memory SIMD: the host store of a typed configuration is typed

`TypedD` at `⟨s, f, is⟩` with memory-SIMD-free code gives `Typed` at `⟨hostify s, f, is⟩`, for
every name of the host function `()`, in every `simEnv B`. The record `store` is read field by
field (`ConfigOk.hasTypFields_of_closedStruct`); every field other than `FUNCS` is the same
value, and a function instance keeps its typed `TYPE` and `MODULE` fields and gets the typed code
`_HOSTFUNC name` (`typedV_funcinst_host`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMHost

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round6.MemSimd (AdminsMS)
open Round7.MemSimd (funcInstVD storeVD TypedD)

variable {H : Type} {B : Builtins}

/-- A typed value at a closed type name is typed in the empty scope. -/
theorem hasTyp_empty_of_typedV {x : IL.Id} {v : Value} (h : TypedV (simEnv B) (.varT x []) v) :
    HasTyp (simEnv B) VarEnv.empty (.varT x []) v :=
  h _ ConfigOk.valsOnly_empty

/-- The code `_HOSTFUNC name` is a typed `funccode`. -/
theorem typedV_hostCode (name : String) :
    TypedV (simEnv B) (.varT "funccode" []) (.case "_HOSTFUNC" (.text name)) :=
  Typing.typedV_closedCase Round5.Pos.findTyp_funccode rfl (hasTyp_textT_iff.2 ⟨_, rfl⟩)

/-- **The host image of a typed function instance is a typed `funcinst`.** -/
theorem typedV_funcinst_host (hn : H → String) (hn' : Unit → String) {fi : FuncInst H}
    (h : TypedV (simEnv B) funcinstT (funcInstVD hn fi)) :
    TypedV (simEnv B) funcinstT (funcInstV hn' (hostFI fi)) := by
  have hf := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    ConfigOk.findTyp_funcinst (hasTyp_empty_of_typedV h)
  obtain ⟨hty, hf⟩ := List.forall₂_cons.1 hf
  obtain ⟨hmod, -⟩ := List.forall₂_cons.1 hf
  have hty' : TypedV (simEnv B) (.varT "deftype" []) _ :=
    (Typing.typedV_iff_empty (Typing.closedT_var _)).2 hty
  have hmod' : TypedV (simEnv B) (.varT "moduleinst" []) _ :=
    (Typing.typedV_iff_empty (Typing.closedT_var _)).2 hmod
  exact Round5.Pos.typedV_struct ConfigOk.findTyp_funcinst (Round5.Pos.hasTypFields_cons_of hty'
    (Round5.Pos.hasTypFields_cons_of hmod' (Round5.Pos.hasTypFields_one (typedV_hostCode _))))

/-- A typed list over a closed type name, from the empty scope. -/
theorem typedV_list_of_empty {x : IL.Id} {v : Value}
    (h : HasTyp (simEnv B) VarEnv.empty (.iterT (.varT x []) .list) v) :
    TypedV (simEnv B) (.iterT (.varT x []) .list) v :=
  (Typing.typedV_iff_empty (Typing.closedT_list _)).2 h

/-- The host images of typed function instances are typed. -/
theorem typedV_funcs_host (hn : H → String) (hn' : Unit → String) {F : List (FuncInst H)}
    (h : TypedV (simEnv B) (.iterT funcinstT .list) (.list (F.map (funcInstVD hn)))) :
    TypedV (simEnv B) (.iterT funcinstT .list) (.list ((F.map hostFI).map (funcInstV hn'))) := by
  refine Round5.Pos.typedV_map fun g hg => ?_
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hg
  exact typedV_funcinst_host hn hn' (typedV_list_iff.1 h _ (List.mem_map_of_mem hfi))

set_option maxRecDepth 100000 in
/-- **The host store of a typed store is typed.** -/
theorem typedV_store_host (hn : H → String) (hn' : Unit → String) {s : Store H}
    (h : TypedV (simEnv B) storeT (storeVD hn s)) :
    TypedV (simEnv B) storeT (storeV hn' (hostify s)) := by
  have hf := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    ConfigOk.findTyp_store' (hasTyp_empty_of_typedV h)
  simp only [List.forall₂_cons] at hf
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, -⟩ := hf
  exact Round5.Pos.typedV_struct ConfigOk.findTyp_store' <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₁) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₂) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₃) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₄) <|
    Round5.Pos.hasTypFields_cons_of (typedV_funcs_host hn hn' (typedV_list_of_empty h₅)) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₆) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₇) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₈) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₉) <|
    Round5.Pos.hasTypFields_one (typedV_list_of_empty h₁₀)

/-- **`TypedD` at memory-SIMD-free code gives `Typed` at the host store**, for every name of the
host function. -/
theorem typed_hostify (hn : H → String) (hn' : Unit → String) {s : Store H} {f : Frame}
    {is : List Admin} (hms : AdminsMS is) (h : TypedD (simEnv B) hn ⟨s, f, is⟩) :
    Typed (simEnv B) hn' ⟨hostify s, f, is⟩ := by
  have TD := Round7.MemSimd.typingFactsD_simEnv B hn
  have T := Typing.typingFacts_simEnv B hn'
  obtain ⟨hst, hcode⟩ := (TD.config _).1 h
  obtain ⟨hs, hfr⟩ := (TD.state s f).1 hst
  refine (T.config _).2 ⟨(T.state _ _).2 ⟨typedV_store_host hn hn' hs, hfr⟩, ?_⟩
  rwa [← Round7.MemSimd.adminsToVD_eq is hms]

end Silmaril.Wasm.SpecTec.Sim.Round8.RMHost
