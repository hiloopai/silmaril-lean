module

public import Silmaril.Proofs.Wasm.Models.FXCoreSave.Sim

/-!
# A concrete record type and a save-then-restore round trip

* `recDef`: the struct type `(struct (field i32) (field i32) (field i32) (field (ref null
  struct)))`, the record type of a function with one saved local; `recTy_ex`: it meets `RecTy`
  (so the hypotheses of `save_run` and `restore_run` are met by an actual frame);
* `storeEx`, `recEx`: the store and the record of the round trip;
* **`save_restore_ex`**: in a store with a mode global (`1`, unwinding), a buffer global (null)
  and a dispatch global, the check of a frame whose local `0` holds `42` saves the record
  `(42, fn 3, index 4)` and returns; a later frame of the same module restores it: its local
  `0` holds `42`, the dispatch global holds `4`, and the buffer is null again.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXCoreSave

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FXCoreSave
open Silmaril.Wasm.Numerics (Profile)

/-- An immutable field of value type `t`. -/
def fld (t : Ty .val) : CFieldType := .field .const (.val t)

/-- The record fields of a function with one saved local. -/
def recFields : Ty (.list .field) :=
  .cons (fld (.num (.int .i32))) (.cons (fld (.num (.int .i32))) (.cons (fld (.num (.int .i32)))
    (.cons (fld (.refv (.ref true (.abs .struct)))) .nil)))

/-- The record type: a final struct type in its own recursion group. -/
def recDef : DefType := .defn (.group (.cons (.sub true .nil (.struct recFields)) .nil)) 0

/-- A module instance with the record type at index `0` and globals `0` (mode), `1` (buffer),
`2` (dispatch) at addresses `0`, `1`, `2`. -/
def modEx : ModuleInst := { types := [recDef], globals := [0, 1, 2] }

theorem recTy_ex (ls : List (Option Val)) : RecTy ⟨ls, modEx⟩ (ix 0) 1 := by
  refine ⟨recDef, recFields, rfl, ⟨rfl⟩, rfl, ?_⟩
  intro ft hft
  simp only [recFields, Ty.toList_cons, Ty.toList_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hft
  rcases hft with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- The example store: mode `1` (unwinding), an empty buffer, dispatch index `0`. -/
def storeEx {H : Type} (gm gb gg : CGlobalType) : Store H :=
  { globals := [⟨gm, .i32 1⟩, ⟨gb, .ref .null⟩, ⟨gg, .i32 0⟩] }

/-- The example record: local `0` holds `42`, function `3`, resume index `4`. -/
def recEx : CRec := ⟨[.i32 42], 3, 4⟩

/-- **Save, then restore, in Core 3.0.** -/
theorem save_restore_ex {H : Type} (P : Profile) (host : HostSemantics H)
    (gm gb gg : CGlobalType) (rest : List Admin) :
    ∃ s', Steps P host ⟨storeEx gm gb gg, ⟨[some (.i32 42)], modEx⟩,
        expression (chkCode (ix 0) (ix 0) (ix 1) 1 3 4) ++ rest⟩
        ⟨s', ⟨[some (.i32 42)], modEx⟩, [.plain .return_] ++ rest⟩ ∧
      ∀ f' : Frame, f'.module = modEx → 1 ≤ f'.locals.length →
        ∃ s'', Steps P host ⟨s', f', expression (restoreCode (ix 0) (ix 1) (ix 2) 1) ++ rest⟩
            ⟨s'', setLocals f' [.i32 42] 0, rest⟩ ∧
          (setLocals f' [.i32 42] 0).local? (ix 0) = some (some (.i32 42)) ∧
          s''.global? f' (ix 2) = some (2, ⟨gg, .i32 4⟩) ∧
          s''.global? f' (ix 1) = some (1, ⟨gb, .ref .null⟩) := by
  let s : Store H := storeEx gm gb gg
  let f : Frame := ⟨[some (.i32 42)], modEx⟩
  have hm : s.global? f (ix 0) = some (0, ⟨gm, .i32 1⟩) := rfl
  have hb : s.global? f (ix 1) = some (1, ⟨gb, .ref .null⟩) := rfl
  have hg : s.global? f (ix 2) = some (2, ⟨gg, .i32 0⟩) := rfl
  have hL : LocalsAre f recEx.locals := by
    intro i hi
    have hi0 : i = 0 := by simp [recEx] at hi; omega
    subst hi0
    rfl
  obtain ⟨d, hsave⟩ := chk_unwind (P := P) (host := host) (s := s) (f := f) hm rfl
    (by decide) (recTy_ex _) hb recEx hL rfl rest
  refine ⟨_, hsave, ?_⟩
  intro f' hmod hlen
  let s' := saveStore s d recEx (.ref .null) 1
  have hmod' : f'.module = f.module := hmod
  have hb' : s'.global? f' (ix 1) = some (1, ⟨gb, .ref (.struct 0)⟩) := by
    rw [global?_module hmod']
    have hb0 : (s.addStruct ⟨d, (recEx.fields (.ref .null)).map .val⟩).global? f (ix 1) =
        some (1, ⟨gb, .ref .null⟩) := hb
    exact global?_setGlobal_self hb0 _
  have hg' : s'.global? f' (ix 2) = some (2, ⟨gg, .i32 0⟩) := by
    rw [global?_module hmod']
    show ((s.addStruct ⟨d, (recEx.fields (.ref .null)).map .val⟩).setGlobal 1
      (.ref (.struct s.structs.length))).global? f (ix 2) = _
    have hg0 : (s.addStruct ⟨d, (recEx.fields (.ref .null)).map .val⟩).global? f (ix 2) =
        some (2, ⟨gg, .i32 0⟩) := hg
    exact global?_setGlobal_ne hg0 (by decide) _
  have hs : s'.structs[0]? = some ⟨d, (recEx.fields (.ref .null)).map .val⟩ := by
    simp [s', saveStore, structs_setGlobal, Store.addStruct, s, storeEx]
  have hrun := restore_run_at (P := P) (host := host) (s := s') (f := f') (x := ix 0)
    (recTy_module hmod (recTy_ex [])) (by decide) hb' hg' (by decide) rfl hs rfl rfl hlen rest
  refine ⟨_, hrun, ?_, ?_, ?_⟩
  · exact localsAre_restored f' [.i32 42] hlen (by decide) 0 (by decide)
  · exact global?_setGlobal_ne (global?_setGlobal_self hg' _) (by decide) _
  · exact global?_setGlobal_self (global?_setGlobal_ne hb' (by decide) _) _

end Silmaril.Proofs.Wasm.Models.FXCoreSave
