module

public import Silmaril.Wasm.FX.Examples.Thms
public import Silmaril.Wasm.Models.FXAsyncPC.Thms

/-!
# The sum-of-a-generator example and its asyncify lowerings: proofs

* `runN_stop_add'`, `beh_of_stop'`: a stopped run of a deterministic machine stays stopped and
  has exactly one behaviour (restated from `Silmaril.Proofs.Wasm.Models.FXAsync.Run`, whose
  module is another topic's proof file and is not imported);
* `gen_kernel`: the kernel program `genW` called on main returns `[6]` and nothing else
  (a closed evaluation of 60 kernel steps);
* `gen_tgt`, `gen_pc`: so do its asyncify lowering (`tstep (compP genW)`, by
  `FXAsync.lower_correct_init`) and the first-order asyncify machine
  (`fstep (annP (compP genW))`, by `FXAsyncPC.kernel_pc_correct`);
* `gen_fx_eq_tgt`: the `StepFX'` behaviours of the WasmFX program `genProg` (`gen_beh`) are the
  images under `obsB` of the asyncify target's behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.Asyncify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.Models.FXAsync (SV Res Outcome runN beh Obs sstep tstep compP sInit tInit
  lower_correct_init)
open Silmaril.Wasm.Models.FXAsyncPC (fstep annP bodies rootCode fInit kernel_pc_correct)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {C V : Type}

theorem runN_stop_add' {step : C → Res C V} {n : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) (k : Nat) : runN step (n + k) c = .stop o := by
  induction n generalizing c with
  | zero => cases h
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [runN] at h ⊢
    split at h
    · exact ih h
    · exact h

theorem beh_of_stop' {step : C → Res C V} {n : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) : beh step c = {o.toObs} := by
  ext b
  constructor
  · rintro (⟨m, o', hm, rfl⟩ | ⟨rfl, hdiv⟩)
    · have h1 : runN step (n + m) c = .stop o := runN_stop_add' h m
      have h2 : runN step (n + m) c = .stop o' := by
        rw [Nat.add_comm]; exact runN_stop_add' hm n
      rw [h1] at h2; cases h2; rfl
    · obtain ⟨c', hc'⟩ := hdiv n
      rw [h] at hc'; cases hc'
  · rintro rfl
    exact .inl ⟨n, o, h, rfl⟩

theorem gen_kernel_run :
    runN (sstep genW i32Test) 60 (sInit 1 []) = .stop (.done [.val (Val.i32 6)]) := by
  rfl

theorem gen_kernel : beh (sstep genW i32Test) (sInit 1 []) = {.done [.val (Val.i32 6)]} :=
  beh_of_stop' gen_kernel_run

theorem gen_tgt : beh (tstep (compP genW) i32Test) (tInit 1 []) = {.done [.val (Val.i32 6)]} := by
  rw [← lower_correct_init]; exact gen_kernel

theorem gen_pc : beh (fstep (annP (compP genW)) (bodies (compP genW) (rootCode 1)) i32Test)
    (fInit 1 []) = {.done [.val (Val.i32 6)]} := by
  rw [← kernel_pc_correct]; exact gen_kernel

theorem gen_fx_eq_tgt (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost (kitFx 6 genWY)
        (genProg (Profile.deterministic o) noHost) =
      obsB '' beh (tstep (compP genW) i32Test) (tInit 1 []) := by
  rw [gen_beh, gen_tgt, Set.image_singleton]
  rfl

end Silmaril.Proofs.Wasm.FX.Examples.Asyncify
