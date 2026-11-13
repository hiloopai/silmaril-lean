module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapStep

/-!
# Typing across the `$utf8` erratum at re-encoded module instances

Round 7's `Utf8StripTypMod` for a re-encoding `F` of export lists whose images are typed in
`simEnv20 B` (`hF`); stripping is `F = []`. Every field but `EXPORTS` moves from `utf8Env20 B` to
`simEnv20 B` off `badU20` (`Utf8Strip.typedV_u20`), and `EXPORTS` holds `F m`.

* **`typedV_moduleInst_exp`**, `typedV_funcInst_exp`, `typedV_store_exp`, `typedV_frame_exp`,
  `typedV_state_exp`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

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
open Silmaril.Wasm.SpecTec.Sim20.Utf8Strip (typedV_u20 typedV_u20_list)

variable {B : Builtins} {F : ModuleInst → List ExportInst}

/-- **A `moduleinst` of `utf8Env20 B` without its exports is a `moduleinst` of `simEnv20 B`.** -/
theorem typedV_moduleInst_exp (hB : ∀ ws, B.call "utf8" ws = none)
    (hF : ∀ m : ModuleInst, TypedV (simEnv20 B) exportsT (expV (F m))) {m : ModuleInst}
    (h : TypedV (utf8Env20 B) (.varT "moduleinst" []) (moduleInstV m)) :
    TypedV (simEnv20 B) (.varT "moduleinst" []) (moduleInstV (expModule20 F m)) := by
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
      (Whole.hasTypFields_oneG (hF m)))))))))

variable {H : Type} {hn : H → String}

/-- **A `funcinst` of `utf8Env20 B` without its module's exports is a `funcinst` of
`simEnv20 B`.** -/
theorem typedV_funcInst_exp (hB : ∀ ws, B.call "utf8" ws = none)
    (hF : ∀ m : ModuleInst, TypedV (simEnv20 B) exportsT (expV (F m))) {fi : FuncInst H}
    (h : TypedV (utf8Env20 B) (.varT "funcinst" []) (funcInstV hn fi)) :
    TypedV (simEnv20 B) (.varT "funcinst" []) (funcInstV hn (expFI20 F fi)) := by
  have hf := Whole.hasTypFields_of_closed
    ((types20_utf8Env20 B).find (Whole.findTyp_funcinst20 (B := StoreBulk.noBuiltins))) h
  obtain ⟨hT, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hM, hf₂⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
  obtain ⟨hC, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₂
  have hT' := typedV_u20 hB (by decide) (by decide) (Whole.typedV_of_empty20 hT)
  have hM' := typedV_moduleInst_exp hB hF (Whole.typedV_of_empty20 hM)
  have hC' := typedV_u20 hB (by decide) (by decide) (Whole.typedV_of_empty20 hC)
  exact Whole.typedV_structG (Whole.findTyp_funcinst20 (B := B))
    (Whole.hasTypFields_consG hT' (Whole.hasTypFields_consG hM' (Whole.hasTypFields_oneG hC')))

/-- **A `store` of `utf8Env20 B` without exports is a `store` of `simEnv20 B`.** -/
theorem typedV_store_exp (hB : ∀ ws, B.call "utf8" ws = none)
    (hF : ∀ m : ModuleInst, TypedV (simEnv20 B) exportsT (expV (F m))) {s : Store H}
    (h : TypedV (utf8Env20 B) (.varT "store" []) (storeV hn s)) :
    TypedV (simEnv20 B) (.varT "store" []) (storeV hn (expStore20 F s)) := by
  have hf := Whole.hasTypFields_of_closed
    ((types20_utf8Env20 B).find (Whole.findTyp_store20 (B := StoreBulk.noBuiltins))) h
  obtain ⟨hFs, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hG, hf₂⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
  obtain ⟨hT, hf₃⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₂
  obtain ⟨hM, hf₄⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₃
  obtain ⟨hE, hf₅⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₄
  obtain ⟨hD, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₅
  have hF₀ : ∀ u ∈ s.funcs.map (funcInstV hn), TypedV (utf8Env20 B) (.varT "funcinst" []) u :=
    Sim.typedV_list_iff.1 (Whole.typedV_list_of_empty20 hFs)
  have hF' : TypedV (simEnv20 B) (.iterT (.varT "funcinst" []) .list)
      (.list ((s.funcs.map (expFI20 F)).map (funcInstV hn))) := by
    refine Sim.typedV_list_iff.2 fun u hu => ?_
    obtain ⟨fi, hfi, rfl⟩ : ∃ fi ∈ s.funcs, funcInstV hn (expFI20 F fi) = u := by
      simpa only [List.map_map, List.mem_map, Function.comp_apply] using hu
    exact typedV_funcInst_exp hB hF (hF₀ _ (List.mem_map_of_mem hfi))
  exact Whole.typedV_structG (Whole.findTyp_store20 (B := B))
    (Whole.hasTypFields_consG hF'
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hG)
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hT)
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hM)
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hE)
      (Whole.hasTypFields_oneG (typedV_u20_list hB (by decide) (by decide) hD)))))))

/-- **A `frame` of `utf8Env20 B` without its module's exports is a `frame` of `simEnv20 B`.** -/
theorem typedV_frame_exp (hB : ∀ ws, B.call "utf8" ws = none)
    (hF : ∀ m : ModuleInst, TypedV (simEnv20 B) exportsT (expV (F m))) {f : Frame}
    (h : TypedV (utf8Env20 B) (.varT "frame" []) (frameV f)) :
    TypedV (simEnv20 B) (.varT "frame" []) (frameV (expFrame20 F f)) := by
  have hf := Whole.hasTypFields_of_closed
    ((types20_utf8Env20 B).find (Whole.findTyp_frame20 (B := StoreBulk.noBuiltins))) h
  obtain ⟨hL, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hM, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
  exact Whole.typedV_structG (Whole.findTyp_frame20 (B := B))
    (Whole.hasTypFields_consG (typedV_u20_list hB (by decide) (by decide) hL)
      (Whole.hasTypFields_oneG (typedV_moduleInst_exp hB hF (Whole.typedV_of_empty20 hM))))

/-- **A `state` of `utf8Env20 B` without exports is a `state` of `simEnv20 B`.** -/
theorem typedV_state_exp (hB : ∀ ws, B.call "utf8" ws = none)
    (hF : ∀ m : ModuleInst, TypedV (simEnv20 B) exportsT (expV (F m))) {s : Store H} {f : Frame}
    (h : TypedV (utf8Env20 B) (.varT "state" []) (stateV hn s f)) :
    TypedV (simEnv20 B) (.varT "state" []) (stateV hn (expStore20 F s) (expFrame20 F f)) := by
  obtain ⟨hs, hf⟩ := Whole.typedV_pair_inv
    ((types20_utf8Env20 B).find (Whole.findTyp_state20 (B := StoreBulk.noBuiltins))) h
  exact Whole.typedV_stateV_iff.2 ⟨typedV_store_exp hB hF hs, typedV_frame_exp hB hF hf⟩

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
