module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.RMCode.Valid

/-!
# Round 8, memory SIMD: the named host store of a typed configuration is typed

`typed_hostC`: `TypedD` at `c` with memory-SIMD-free code gives `Typed` at `hostC hn c` with the
names `id`. This is round 8 pass 1's `RMHost.typed_hostify` for `hostSFI hn` instead of
`RMHost.hostFI`: a function instance keeps its typed `TYPE` and `MODULE` fields and gets the code
`_HOSTFUNC name`, a typed `funccode` for every name (`RMHost.typedV_hostCode`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMCode

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round6.MemSimd (AdminsMS)
open Round7.MemSimd (funcInstVD storeVD TypedD)
open Round8.RMHost (hasTyp_empty_of_typedV typedV_hostCode typedV_list_of_empty)

variable {H : Type} {B : Builtins}

/-- **The named host image of a typed function instance is a typed `funcinst`.** -/
theorem typedV_funcinst_hostS (hn : H → String) {fi : FuncInst H}
    (h : TypedV (simEnv B) funcinstT (funcInstVD hn fi)) :
    TypedV (simEnv B) funcinstT (funcInstV id (hostSFI hn fi)) := by
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

/-- The named host images of typed function instances are typed. -/
theorem typedV_funcs_hostS (hn : H → String) {F : List (FuncInst H)}
    (h : TypedV (simEnv B) (.iterT funcinstT .list) (.list (F.map (funcInstVD hn)))) :
    TypedV (simEnv B) (.iterT funcinstT .list) (.list ((F.map (hostSFI hn)).map (funcInstV id))) := by
  refine Round5.Pos.typedV_map fun g hg => ?_
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hg
  exact typedV_funcinst_hostS hn (typedV_list_iff.1 h _ (List.mem_map_of_mem hfi))

set_option maxRecDepth 100000 in
/-- **The named host store of a typed store is typed.** -/
theorem typedV_store_hostS (hn : H → String) {s : Store H}
    (h : TypedV (simEnv B) storeT (storeVD hn s)) :
    TypedV (simEnv B) storeT (storeV id (hostifyS hn s)) := by
  have hf := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    ConfigOk.findTyp_store' (hasTyp_empty_of_typedV h)
  simp only [List.forall₂_cons] at hf
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, -⟩ := hf
  exact Round5.Pos.typedV_struct ConfigOk.findTyp_store' <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₁) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₂) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₃) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₄) <|
    Round5.Pos.hasTypFields_cons_of (typedV_funcs_hostS hn (typedV_list_of_empty h₅)) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₆) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₇) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₈) <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_of_empty h₉) <|
    Round5.Pos.hasTypFields_one (typedV_list_of_empty h₁₀)

/-- **`TypedD` at memory-SIMD-free code gives `Typed` at the named host store.** -/
theorem typed_hostC (hn : H → String) {c : Config H} (hms : AdminsMS c.code)
    (h : TypedD (simEnv B) hn c) : Typed (simEnv B) id (hostC hn c) := by
  have TD := Round7.MemSimd.typingFactsD_simEnv B hn
  have T := Typing.typingFacts_simEnv B (id : String → String)
  obtain ⟨hst, hcode⟩ := (TD.config _).1 h
  obtain ⟨hs, hfr⟩ := (TD.state c.store c.frame).1 hst
  refine (T.config _).2 ⟨(T.state _ _).2 ⟨typedV_store_hostS hn hs, hfr⟩, ?_⟩
  show TypedV _ _ (.list (adminsToV c.code))
  rwa [← Round7.MemSimd.adminsToVD_eq c.code hms]

end Silmaril.Wasm.SpecTec.Sim.Round8.RMCode
