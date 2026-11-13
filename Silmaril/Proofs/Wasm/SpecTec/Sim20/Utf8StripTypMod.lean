module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripBase

/-!
# Typing across the `$utf8` erratum at export-free module instances

`Good20BU` reads its typing in `utf8Env20 B`, `Good20B` in `simEnv20 B`. The two agree on every
type off `badU20` (`Utf8Else.hasTyp_u20_iff`). At a module instance, the one field whose type
reaches `name` is `EXPORTS`, and removing the exports leaves `[]` there, which every
environment types. So:

* `typedV_u20`: off `badU20`, `utf8Env20 B` typing gives `simEnv20 B` typing (both checks on the
  type are decided by the kernel at each use).
* **`typedV_moduleInst_strip`**: a `moduleinst` of `utf8Env20 B` without its exports is a
  `moduleinst` of `simEnv20 B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (tyEvB goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (badU20 hasTyp_u20_iff evFreeB goodEvs_of_all)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20 types20_utf8Env20 Types20)

variable {B : Builtins}

/-- **Off `badU20`, a type of `utf8Env20 B` is one of `simEnv20 B`.** -/
theorem hasTyp_u20 (hB : ∀ ws, B.call "utf8" ws = none) {t : Typ} {v : Value}
    (ht : (evTyp t).all (tyEvB badU20) = true) (hte : (evTyp t).all (evFreeB "utf8") = true)
    (h : HasTyp (utf8Env20 B) VarEnv.empty t v) : HasTyp (simEnv20 B) VarEnv.empty t v :=
  (hasTyp_u20_iff hB rfl (fun p hp => by simp [VarEnv.empty, Map.empty] at hp) (goodT_of_all ht)
    (goodEvs_of_all hte)).1 h

/-- `hasTyp_u20` in every value-only scope. -/
theorem typedV_u20 (hB : ∀ ws, B.call "utf8" ws = none) {t : Typ} {v : Value}
    (ht : (evTyp t).all (tyEvB badU20) = true) (hte : (evTyp t).all (evFreeB "utf8") = true)
    (h : TypedV (utf8Env20 B) t v) : TypedV (simEnv20 B) t v := fun ρ hρ =>
  (hasTyp_u20_iff hB hρ.1 (fun p hp => by simp [hρ.2.1] at hp) (goodT_of_all ht)
    (goodEvs_of_all hte)).1 (h ρ hρ)

/-- The empty list is typed at every list type. -/
theorem typedV_listNil {e : Env} {t : Typ} : TypedV e (.iterT t .list) (.list []) :=
  Sim.typedV_list_iff.2 fun _ hu => nomatch hu

/-- **A `moduleinst` of `utf8Env20 B` without its exports is a `moduleinst` of `simEnv20 B`.** -/
theorem typedV_moduleInst_strip (hB : ∀ ws, B.call "utf8" ws = none) {m : ModuleInst}
    (h : TypedV (utf8Env20 B) (.varT "moduleinst" []) (moduleInstV m)) :
    TypedV (simEnv20 B) (.varT "moduleinst" []) (moduleInstV (stripModule20 m)) := by
  have hf := Whole.hasTypFields_of_closed
    ((types20_utf8Env20 B).find (StoreBulk.findTyp_moduleinst20 (B := StoreBulk.noBuiltins))) h
  obtain ⟨hT, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
  have hT' : TypedV (simEnv20 B) (.iterT (.varT "functype" []) .list)
      (.list (m.types.map funcTypeV)) :=
    typedV_u20 hB (by decide) (by decide) (Whole.typedV_list_of_empty20 hT)
  have hE := StoreBulk.types20_simEnv20 B
  have hA := fun {x : IL.Id} (htd : (simEnv20 B).findTyp? x =
      some ([], [.instD [] [] (.aliasT (.varT "addr" []))])) (xs : List Nat) =>
    StoreBulk.typedV_addrsE hE htd xs
  exact Whole.typedV_structG (StoreBulk.findTyp_moduleinst20 (B := B))
    (Whole.hasTypFields_consG hT'
    (Whole.hasTypFields_consG (hA Whole.findTyp_funcaddr20 m.funcs)
    (Whole.hasTypFields_consG (hA StoreBulk.findTyp_globaladdr20 m.globals)
    (Whole.hasTypFields_consG (hA StoreBulk.findTyp_tableaddr20 m.tables)
    (Whole.hasTypFields_consG (hA StoreBulk.findTyp_memaddr20 m.mems)
    (Whole.hasTypFields_consG (hA StoreBulk.findTyp_elemaddr20 m.elems)
    (Whole.hasTypFields_consG (hA StoreBulk.findTyp_dataaddr20 m.datas)
      (Whole.hasTypFields_oneG typedV_listNil))))))))

variable {H : Type} {hn : H → String}

/-- **A `funcinst` of `utf8Env20 B` without its module's exports is a `funcinst` of
`simEnv20 B`.** -/
theorem typedV_funcInst_strip (hB : ∀ ws, B.call "utf8" ws = none) {fi : FuncInst H}
    (h : TypedV (utf8Env20 B) (.varT "funcinst" []) (funcInstV hn fi)) :
    TypedV (simEnv20 B) (.varT "funcinst" []) (funcInstV hn (stripFI20 fi)) := by
  have hf := Whole.hasTypFields_of_closed
    ((types20_utf8Env20 B).find (Whole.findTyp_funcinst20 (B := StoreBulk.noBuiltins))) h
  obtain ⟨hT, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hM, hf₂⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
  obtain ⟨hC, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₂
  have hT' := typedV_u20 hB (by decide) (by decide) (Whole.typedV_of_empty20 hT)
  have hM' := typedV_moduleInst_strip hB (Whole.typedV_of_empty20 hM)
  have hC' := typedV_u20 hB (by decide) (by decide) (Whole.typedV_of_empty20 hC)
  exact Whole.typedV_structG (Whole.findTyp_funcinst20 (B := B))
    (Whole.hasTypFields_consG hT' (Whole.hasTypFields_consG hM' (Whole.hasTypFields_oneG hC')))

/-- A list of values typed at `x*` in `utf8Env20 B`, read off a field. -/
theorem typedV_u20_list (hB : ∀ ws, B.call "utf8" ws = none) {x : IL.Id} {l : List Value}
    (ht : (evTyp (.iterT (.varT x []) .list)).all (tyEvB badU20) = true)
    (hte : (evTyp (.iterT (.varT x []) .list)).all (evFreeB "utf8") = true)
    (h : HasTyp (utf8Env20 B) VarEnv.empty (.iterT (.varT x []) .list) (.list l)) :
    TypedV (simEnv20 B) (.iterT (.varT x []) .list) (.list l) :=
  typedV_u20 hB ht hte (Whole.typedV_list_of_empty20 h)

/-- **A `store` of `utf8Env20 B` without exports is a `store` of `simEnv20 B`.** -/
theorem typedV_store_strip (hB : ∀ ws, B.call "utf8" ws = none) {s : Store H}
    (h : TypedV (utf8Env20 B) (.varT "store" []) (storeV hn s)) :
    TypedV (simEnv20 B) (.varT "store" []) (storeV hn (stripStore20 s)) := by
  have hf := Whole.hasTypFields_of_closed
    ((types20_utf8Env20 B).find (Whole.findTyp_store20 (B := StoreBulk.noBuiltins))) h
  obtain ⟨hF, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hG, hf₂⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
  obtain ⟨hT, hf₃⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₂
  obtain ⟨hM, hf₄⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₃
  obtain ⟨hE, hf₅⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₄
  obtain ⟨hD, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₅
  have hF₀ : ∀ u ∈ s.funcs.map (funcInstV hn), TypedV (utf8Env20 B) (.varT "funcinst" []) u :=
    Sim.typedV_list_iff.1 (Whole.typedV_list_of_empty20 hF)
  have hF' : TypedV (simEnv20 B) (.iterT (.varT "funcinst" []) .list)
      (.list ((s.funcs.map stripFI20).map (funcInstV hn))) := by
    refine Sim.typedV_list_iff.2 fun u hu => ?_
    obtain ⟨fi, hfi, rfl⟩ : ∃ fi ∈ s.funcs, funcInstV hn (stripFI20 fi) = u := by
      simpa only [List.map_map, List.mem_map, Function.comp_apply] using hu
    exact typedV_funcInst_strip hB (hF₀ _ (List.mem_map_of_mem hfi))
  exact Whole.typedV_structG (Whole.findTyp_store20 (B := B))
    (Whole.hasTypFields_consG hF'
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hG)
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hT)
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hM)
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hE)
      (Whole.hasTypFields_oneG (typedV_u20_list hB (by decide) (by decide) hD)))))))

/-- **A `frame` of `utf8Env20 B` without its module's exports is a `frame` of `simEnv20 B`.** -/
theorem typedV_frame_strip (hB : ∀ ws, B.call "utf8" ws = none) {f : Frame}
    (h : TypedV (utf8Env20 B) (.varT "frame" []) (frameV f)) :
    TypedV (simEnv20 B) (.varT "frame" []) (frameV (stripFrame20 f)) := by
  have hf := Whole.hasTypFields_of_closed
    ((types20_utf8Env20 B).find (Whole.findTyp_frame20 (B := StoreBulk.noBuiltins))) h
  obtain ⟨hL, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hM, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
  exact Whole.typedV_structG (Whole.findTyp_frame20 (B := B))
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hL)
      (Whole.hasTypFields_oneG (typedV_moduleInst_strip hB (Whole.typedV_of_empty20 hM))))

/-- **A `state` of `utf8Env20 B` without exports is a `state` of `simEnv20 B`.** -/
theorem typedV_state_strip (hB : ∀ ws, B.call "utf8" ws = none) {s : Store H} {f : Frame}
    (h : TypedV (utf8Env20 B) (.varT "state" []) (stateV hn s f)) :
    TypedV (simEnv20 B) (.varT "state" []) (stateV hn (stripStore20 s) (stripFrame20 f)) := by
  obtain ⟨hs, hf⟩ := Whole.typedV_pair_inv
    ((types20_utf8Env20 B).find (Whole.findTyp_state20 (B := StoreBulk.noBuiltins))) h
  exact Whole.typedV_stateV_iff.2 ⟨typedV_store_strip hB hs, typedV_frame_strip hB hf⟩

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
