module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripSucc

/-!
# A witness: leg 2 outside `Good20B`

`expCfg` is round 6's `table.copy` witness `StoreBulk.tcopyCfg` with the frame's module exporting
table 0 under the name `"a"`. It is `Good20BU` but not `Good20B` (`StoreBulk.not_good20B_single`),
so the forward theorem of rounds 5–6 does not reach it. Its V2 step (`table.copy-le`) strips to a
step of `utf8Env20T` between `Good20B` configurations (`step_strip20`, `good20B_strip`,
`StoreBulk.fwd_good20B`), and its successor is `Good20BU` (`good20BU_succ`). What is missing for
the step of `utf8Env20T` between the images themselves is leg 3 (`Task.unstripStep20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (Good20B oneTable segStore tcopyCodeW
  storeSmall_segStore)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (Good20BU utf8Env20T storeB_utf8 good20BU_of_good20B)

/-- A frame whose module has table 0 and element segment 0, and exports table 0 as `"a"`. -/
def expFrame : Frame := { module := { tables := [0], elems := [0], exports := [⟨"a", .table 0⟩] } }

/-- `table.copy` in a module that exports a non-empty name. -/
def expCfg : Config Empty := ⟨segStore, expFrame, tcopyCodeW⟩

/-- The successor of `expCfg`. -/
def expCfg' : Config Empty := ⟨segStore, expFrame,
  [constI32 0, constI32 0, .plain (.tableGet ⟨0⟩), .plain (.tableSet ⟨0⟩), constI32 (0 + 1),
    constI32 (0 + 1), constI32 (1 - 1), .plain (.tableCopy ⟨0⟩ ⟨0⟩)]⟩

theorem step_expCfg (P : Profile) (host : HostSemantics Empty) : Step P host expCfg expCfg' :=
  StoreBulk.TableCopyFwd.step (.le (tx := oneTable) (ty := oneTable) rfl rfl (by decide)
    (by decide) (by decide))

theorem not_good20B_expCfg (P : Profile) : ¬ Good20B Empty.elim P expCfg :=
  StoreBulk.not_good20B_single (x := ⟨"a", .table 0⟩) List.mem_cons_self (c := 'a') rfl

/-- **`expCfg` is `Good20BU`.** -/
theorem good20BU_expCfg (P : Profile) : Good20BU Empty.elim P expCfg := by
  have h₀ := good20BU_of_good20B (StoreBulk.good20B_tcopyCfg P)
  have hm : ModOk (Whole.storeB P) expFrame.module :=
    StoreBulk.typedV_moduleInst_utf8Env20 _ (fun _ h => nomatch h)
      (fun x hx => by simp only [expFrame, List.mem_singleton] at hx; subst hx; decide)
  exact ⟨⟨typedV_state_unstrip (f := expFrame) h₀.typ.state (fun _ h => nomatch h) hm,
      h₀.typ.code⟩,
    Whole.Plain20.plain (s := segStore) (f := expFrame)
      [.num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 1⟩] (.tableCopy ⟨0⟩ ⟨0⟩) [] rfl,
    by decide, h₀.store, storeSmall_segStore⟩

/-- **Legs 1 and 2 at `expCfg`**: outside `Good20B`, the step strips to a step of `utf8Env20T`
between `Good20B` configurations, and the successor is `Good20BU`. -/
theorem expCfg_legs (P : Profile) (host : HostSemantics Empty) :
    Good20BU Empty.elim P expCfg ∧ ¬ Good20B Empty.elim P expCfg ∧ Step P host expCfg expCfg' ∧
      Good20B Empty.elim P (stripConfig20 expCfg) ∧ Good20BU Empty.elim P expCfg' ∧
      SStepB (utf8Env20T (Whole.storeB P)) (configV Empty.elim (stripConfig20 expCfg))
        (configV Empty.elim (stripConfig20 expCfg')) := by
  have hg := good20BU_expCfg P
  have hs := step_expCfg P host
  have hg₀ := good20B_strip hg
  have hf := StoreBulk.fwd_good20B hg₀ (step_strip20 hs (noHost20_of_storeOkB hg.store))
  exact ⟨hg, not_good20B_expCfg P, hs, hg₀, good20BU_succ hg hs hf.1,
    Utf8Else.sstepB_utf8_20T (storeB_utf8 P) hf.2⟩

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
