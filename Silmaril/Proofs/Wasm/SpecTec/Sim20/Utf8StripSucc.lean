module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripUnstrip
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripGood

/-!
# The successor half of leg 2

* `adminsMods_map_eDA`: body erasure keeps the frames of the code.
* **`good20BU_succ`** (`goodUnstrip20_holds`): the successor `c'` of a step from a `Good20BU`
  configuration `c` is `Good20BU` when `stripConfig20 c'` is `Good20B`. The module instances of
  `c` are `ModOk` (they are typed in `utf8Env20`, `modOk_of_state_u20`, `adminsMods_of_u20`), so
  are those of `c'` (`modsQ_step`), and the `simEnv20` typing of the stripped successor moves to
  `utf8Env20` (`Utf8Mono.typedV_ext`) and back onto `c'` (`typedV_state_unstrip`,
  `typedV_admins_unstrip`). The other parts are round 6's `okB_step` and `plain20_step`.
* **`fwdU20_of_unstripStep`**: `Utf8Mono.Task.fwdU20` from `Task.unstripStep20` alone.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (Good20B utf8Env20)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eDA)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (eraseS eraseFI)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (Good20BU storeB_utf8 envExt20 typedV_ext)

variable {H : Type} {Q : ModuleInst → Prop}

/-- **Body erasure keeps the frames of the code.** -/
theorem adminMods_eDA (a : Admin) : AdminMods Q (eDA a) ↔ AdminMods Q a := by
  induction a using Admin.rec (motive_2 := fun l => AdminsMods Q (l.map eDA) ↔ AdminsMods Q l) with
  | nil => exact Iff.rfl
  | cons _ _ h₁ h₂ => exact and_congr h₁ h₂
  | label _ _ _ h =>
    show AdminsMods Q (StoreDeep.eDAL _) ↔ _
    rw [StoreDeep.eDAL_eq]
    exact h
  | frame _ _ _ h =>
    show _ ∧ AdminsMods Q (StoreDeep.eDAL _) ↔ _
    rw [StoreDeep.eDAL_eq]
    exact and_congr Iff.rfl h
  | _ => exact Iff.rfl

/-- `adminMods_eDA` on a sequence. -/
theorem adminsMods_map_eDA (l : List Admin) : AdminsMods Q (l.map eDA) ↔ AdminsMods Q l := by
  induction l with
  | nil => exact Iff.rfl
  | cons a l ih => exact and_congr (adminMods_eDA a) ih

/-- The function instances of the erased store have the modules of the store's. -/
theorem modOk_of_eraseS {B : Builtins} {s : Store H} (h : ∀ fi ∈ s.funcs, ModOk B fi.module) :
    ∀ fi ∈ (eraseS s).funcs, ModOk B fi.module := by
  intro fi hfi
  obtain ⟨g, hg, rfl⟩ : ∃ g ∈ s.funcs, eraseFI g = fi := by
    simpa only [eraseS, List.mem_map] using hfi
  exact h g hg

/-- **The successor half of leg 2.** -/
theorem good20BU_succ {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
    {host : HostSemantics H} {c c' : Config H} (hg : Good20BU hn P c) (hs : Step P host c c')
    (hg' : Good20B hn P (stripConfig20 c')) : Good20BU hn P c' := by
  have hB := storeB_utf8 P
  have hst := modOk_of_state_u20 hg.typ.state
  have hfuncs : ∀ fi ∈ c.store.funcs, ModOk (Whole.storeB P) fi.module :=
    fun fi hfi => hst.1 (eraseFI fi) (List.mem_map_of_mem hfi)
  have hcode : AdminsMods (ModOk (Whole.storeB P)) c.code :=
    (adminsMods_map_eDA c.code).1 (adminsMods_of_u20 _ hg.typ.code)
  have hq' : ModsQ (ModOk (Whole.storeB P)) c' :=
    modsQ_step hs (noHost20_of_storeOkB hg.store) ⟨hfuncs, hst.2, hcode⟩
  have hS : TypedV (utf8Env20 (Whole.storeB P)) (.varT "state" [])
      (stateV hn (stripStore20 (eraseS c'.store)) (stripFrame20 c'.frame)) := by
    rw [← eraseS_strip]
    exact typedV_ext (envExt20 _ hB) hg'.typ.state
  have hC : TypedV (utf8Env20 (Whole.storeB P)) StepFix.adminsTy
      (.list (adminsToV (stripAdmins20 (c'.code.map eDA)))) := by
    rw [← map_eDA_strip]
    exact typedV_ext (envExt20 _ hB) hg'.typ.code
  obtain ⟨hok', hf, hsm, -⟩ := StoreBulk.okB_step hs hg.ok hg.store
  exact ⟨⟨typedV_state_unstrip hS (modOk_of_eraseS hq'.funcs) hq'.frame,
      typedV_admins_unstrip _ hC ((adminsMods_map_eDA _).2 hq'.code)⟩,
    Whole.plain20_step hs hg.plain, hok', StoreBulk.storeOkB_of_funcs hg.store hf, hsm hg.small⟩

/-- **`Task.goodUnstrip20` holds.** -/
theorem goodUnstrip20_holds : Task.goodUnstrip20 :=
  fun _ _ _ _ _ _ hg hs hg' => good20BU_succ hg hs hg'

/-- **`Utf8Mono.Task.fwdU20` from leg 3 alone.** -/
theorem fwdU20_of_unstripStep (h₃ : Task.unstripStep20) : Utf8Mono.Task.fwdU20 :=
  fwdU20_of_unstrip goodUnstrip20_holds h₃

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
