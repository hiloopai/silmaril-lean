module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Swap10Inv

/-!
# Typing re-encoded 1.0 configurations in `simEnv10T`

Round 8's `Utf8Strip10Typ` (leg 2 for 1.0) for a re-encoding `F` of export lists whose images are
typed in `simEnv10T B` (`hF`); stripping is `F = []`. **`typed10_exp10`**: a configuration typed in
`utf8Env10T B`, with its exports re-encoded, is typed in `simEnv10T B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst ExportInst)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT storeT frameT nT instrsT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (tyEvB goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (badU20 evFreeB goodEvs_of_all)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T hasTyp_u10T_iff findTyp?_utf8Env10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (adminsT adminT10 labelT10 frameCaseT10 hasTyp_tup2G10
  hasTyp_tup3G10 hasTyp_tup3_inv hasTyp_closedVariant_inv typedV_of_scope typedV_list_of_scope
  valsOnly_empty)
open Silmaril.Wasm.SpecTec.Sim20.Whole (hasTypFields_of_closed hasTypFields_cons_nil_iff
  typedV_of_empty20 typedV_list_of_empty20 typedV_structG hasTypFields_consG hasTypFields_oneG)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String} {F : ModuleInst → List ExportInst}

open Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10 (typedV_u10 sameTyps_utf8 sameTyps_sim typedV_funcInst_iffE
  typedV_store_iffE typedV_frame_iffE typedV_stV_iffE typed10_iffE typedV_listNil10
  findTyp_moduleinst10T funcInstV_fields typedV_instr_of_adminE typedV_label_iffE typedV_frameA_iffE)

/-! ## Re-encoding, structure by structure -/

/-- **A `moduleinst` of `utf8Env10T B` with its exports re-encoded is a `moduleinst` of
`simEnv10T B`.** -/
theorem typedV_moduleInst_exp10 (hB : ∀ ws, B.call "utf8" ws = none)
    (hEx : ∀ m : ModuleInst, TypedV (simEnv10T B) Sim20.Utf8Swap.exportsT (expV10 (F m))) {m : ModuleInst}
    (h : TypedV (utf8Env10T B) (.varT "moduleinst" []) (moduleInstV m)) :
    TypedV (simEnv10T B) (.varT "moduleinst" []) (moduleInstV (expModule10 F m)) := by
  have hf := hasTypFields_of_closed ((sameTyps_utf8 B "moduleinst").trans findTyp_moduleinst10T) h
  obtain ⟨hT, hf₁⟩ := hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hF, hf₂⟩ := hasTypFields_cons_nil_iff.1 hf₁
  obtain ⟨hG, hf₃⟩ := hasTypFields_cons_nil_iff.1 hf₂
  obtain ⟨hTa, hf₄⟩ := hasTypFields_cons_nil_iff.1 hf₃
  obtain ⟨hM, -⟩ := hasTypFields_cons_nil_iff.1 hf₄
  exact typedV_structG findTyp_moduleinst10T
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hT))
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hF))
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hG))
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hTa))
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hM))
      (hasTypFields_oneG (hEx m)))))))

/-- **A function instance of `utf8Env10T B` with its module's exports re-encoded is one of
`simEnv10T B`.** -/
theorem typedV_funcInst_exp10 (hB : ∀ ws, B.call "utf8" ws = none)
    (hEx : ∀ m : ModuleInst, TypedV (simEnv10T B) Sim20.Utf8Swap.exportsT (expV10 (F m))) {fi : FuncInst V1.Func H}
    (h : TypedV (utf8Env10T B) (.varT "funcinst" []) (funcInstV hn fi)) :
    TypedV (simEnv10T B) (.varT "funcinst" []) (funcInstV hn (expFI10 F fi)) := by
  cases fi with
  | wasm t m fn =>
    obtain ⟨hT, hM, hC⟩ := (typedV_funcInst_iffE (sameTyps_utf8 B) (t := funcTypeV t)
      (c := funcV fn)).1 h
    exact (typedV_funcInst_iffE (sameTyps_sim B)).2 ⟨typedV_u10 hB (by decide) (by decide) hT,
      typedV_moduleInst_exp10 hB hEx hM, typedV_u10 hB (by decide) (by decide) hC⟩
  | host t h' => exact Utf8Strip10.typedV_funcInst_strip10 hB h

/-- **A store of `utf8Env10T B` with re-encoded exports is a store of `simEnv10T B`.** -/
theorem typedV_store_exp10 (hB : ∀ ws, B.call "utf8" ws = none)
    (hEx : ∀ m : ModuleInst, TypedV (simEnv10T B) Sim20.Utf8Swap.exportsT (expV10 (F m))) {s : Store H}
    (h : TypedV (utf8Env10T B) storeT (storeV hn s)) :
    TypedV (simEnv10T B) storeT (storeV hn (expStore10 F s)) := by
  obtain ⟨hF, hG, hT, hM⟩ := (typedV_store_iffE (sameTyps_utf8 B)).1 h
  refine (typedV_store_iffE (sameTyps_sim B)).2 ⟨?_, typedV_u10 hB (by decide) (by decide) hG,
    typedV_u10 hB (by decide) (by decide) hT, typedV_u10 hB (by decide) (by decide) hM⟩
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  obtain ⟨fi, hfi, rfl⟩ : ∃ fi ∈ s.funcs, funcInstV hn (expFI10 F fi) = u := by
    simpa only [expStore10, List.map_map, List.mem_map, Function.comp_apply] using hu
  exact typedV_funcInst_exp10 hB hEx (Sim.typedV_list_iff.1 hF _ (List.mem_map_of_mem hfi))

/-- **A frame of `utf8Env10T B` with its module's exports re-encoded is a frame of `simEnv10T B`.** -/
theorem typedV_frame_exp10 (hB : ∀ ws, B.call "utf8" ws = none)
    (hEx : ∀ m : ModuleInst, TypedV (simEnv10T B) Sim20.Utf8Swap.exportsT (expV10 (F m))) {f : Frame}
    (h : TypedV (utf8Env10T B) frameT (frameV f)) :
    TypedV (simEnv10T B) frameT (frameV (expFrame10 F f)) := by
  obtain ⟨hL, hM⟩ := (typedV_frame_iffE (sameTyps_utf8 B)).1 h
  exact (typedV_frame_iffE (sameTyps_sim B)).2
    ⟨typedV_u10 hB (by decide) (by decide) hL, typedV_moduleInst_exp10 hB hEx hM⟩

/-- **A state of `utf8Env10T B` with re-encoded exports is a state of `simEnv10T B`.** -/
theorem typedV_state_exp10 (hB : ∀ ws, B.call "utf8" ws = none)
    (hEx : ∀ m : ModuleInst, TypedV (simEnv10T B) Sim20.Utf8Swap.exportsT (expV10 (F m))) {s : Store H} {f : Frame}
    (h : TypedV (utf8Env10T B) stateT (stateV hn s f)) :
    TypedV (simEnv10T B) stateT (stateV hn (expStore10 F s) (expFrame10 F f)) := by
  obtain ⟨hs, hf⟩ := (typedV_stV_iffE (sameTyps_utf8 B)).1 h
  exact (typedV_stV_iffE (sameTyps_sim B)).2 ⟨typedV_store_exp10 hB hEx hs, typedV_frame_exp10 hB hEx hf⟩

/-! ## Code -/

mutual
/-- **An `admininstr` of `utf8Env10T B` with the exports of its frames re-encoded is an
`admininstr` of `simEnv10T B`.** -/
theorem typedV_admin_exp10 (hB : ∀ ws, B.call "utf8" ws = none)
    (hEx : ∀ m : ModuleInst, TypedV (simEnv10T B) Sim20.Utf8Swap.exportsT (expV10 (F m))) : ∀ a : Admin,
    TypedV (utf8Env10T B) adminT10 (adminToV a) →
      TypedV (simEnv10T B) adminT10 (adminToV (expAdmin10 F a))
  | .source i, h => Whole.typedV_admin_of_instr10T
      (typedV_u10 hB (by decide) (by decide) (typedV_instr_of_adminE (sameTyps_utf8 B) h))
  | .invoke a, _ => Whole.typedV_invoke10T a
  | .trap, _ => Whole.typedV_trap10T
  | .label n cont body, h => by
    obtain ⟨h₁, h₂, h₃⟩ := (typedV_label_iffE (sameTyps_utf8 B)).1 h
    exact (typedV_label_iffE (sameTyps_sim B)).2 ⟨typedV_u10 hB (by decide) (by decide) h₁,
      typedV_u10 hB (by decide) (by decide) h₂, typedV_admins_exp10 hB hEx body h₃⟩
  | .frame n f body, h => by
    obtain ⟨h₁, h₂, h₃⟩ := (typedV_frameA_iffE (sameTyps_utf8 B)).1 h
    exact (typedV_frameA_iffE (sameTyps_sim B)).2 ⟨typedV_u10 hB (by decide) (by decide) h₁,
      typedV_frame_exp10 hB hEx h₂, typedV_admins_exp10 hB hEx body h₃⟩

/-- `typedV_admin_exp10` on a sequence. -/
theorem typedV_admins_exp10 (hB : ∀ ws, B.call "utf8" ws = none)
    (hEx : ∀ m : ModuleInst, TypedV (simEnv10T B) Sim20.Utf8Swap.exportsT (expV10 (F m))) : ∀ l : List Admin,
    TypedV (utf8Env10T B) adminsT (.list (adminsToV l)) →
      TypedV (simEnv10T B) adminsT (.list (adminsToV (expAdmins10 F l)))
  | [], _ => typedV_listNil10
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := Sim.typedV_list_cons_iff.1 h
    exact Sim.typedV_list_cons_iff.2 ⟨typedV_admin_exp10 hB hEx a ha, typedV_admins_exp10 hB hEx l hl⟩
end

/-- **Leg 2 for 1.0: a configuration typed in `utf8Env10T B`, with its exports re-encoded, is typed
in `simEnv10T B`.** -/
theorem typed10_exp10 (hB : ∀ ws, B.call "utf8" ws = none)
    (hEx : ∀ m : ModuleInst, TypedV (simEnv10T B) Sim20.Utf8Swap.exportsT (expV10 (F m))) {c : Config H}
    (h : Typed10 (utf8Env10T B) hn c) : Typed10 (simEnv10T B) hn (expConfig10 F c) := by
  obtain ⟨hz, hc⟩ := (typed10_iffE (sameTyps_utf8 B)).1 h
  exact (typed10_iffE (sameTyps_sim B)).2
    ⟨typedV_state_exp10 hB hEx hz, typedV_admins_exp10 hB hEx c.code hc⟩

end Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10
