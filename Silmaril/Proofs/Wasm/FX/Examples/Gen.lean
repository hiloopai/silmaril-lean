module

public import Silmaril.Proofs.Wasm.FX.Examples.Kit

/-!
# Generators: encodings, runs and behaviours

* `genOk`, `takeOk`: the encodings of `genW` and `takeW` are `EncI` derivations, so the kit
  settings satisfy `Ok`;
* `gen_run`, `take_run`: the kernel runs from the call of main, computed by evaluation; with
  `gen_check`/`gen_tight` (and the same for `take`) along them;
* **`gen_beh`**: the sum-of-a-generator program has exactly one `StepFX'` behaviour in the
  deterministic profile with no host calls: it returns `[6]`;
* **`take_beh`**: the take-two program returns `[3]`, and nothing else;
* `gen_mem`, `take_mem`: those results are behaviours at every profile and host.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (SV SCfg Ins Prog sstep runN beh Obs Outcome sInit allVals)
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (checkRun)
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (checkTight)
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable (P : Profile) (host : HostSemantics Nat)

/-! ## Sum of a generator -/

theorem genEnc0 : EncI (kitS P host 6 genWY) genW genBody genY :=
  .push rfl (.suspend (kitTag P host 6 genWY) (.push rfl (.suspend (kitTag P host 6 genWY) (.push rfl
    (.suspend (kitTag P host 6 genWY) (.push rfl .nil))))))

theorem genEnc5 : EncI (kitS P host 6 genWY) genW [] [] := .nil

theorem genEnc4 : EncI (kitS P host 6 genWY) genW [.resume 0 [⟨0, 5⟩], .prim 2 opAdd] genH4 :=
  .resume (np := 0) (kitTag P host 6 genWY) rfl (genEnc5 P host) (kitD P host 6 genWY) rfl rfl (kitH P host 6 genWY) rfl rfl
    (.prim (kitAdd P host 6 genWY) .nil)

theorem genEnc3 : EncI (kitS P host 6 genWY) genW [.resume 0 [⟨0, 4⟩], .prim 2 opAdd] genH3 :=
  .resume (np := 0) (kitTag P host 6 genWY) rfl (genEnc4 P host) (kitD P host 6 genWY) rfl rfl (kitH P host 6 genWY) rfl rfl
    (.prim (kitAdd P host 6 genWY) .nil)

theorem genEnc2 : EncI (kitS P host 6 genWY) genW [.resume 0 [⟨0, 3⟩], .prim 2 opAdd] genH2 :=
  .resume (np := 0) (kitTag P host 6 genWY) rfl (genEnc3 P host) (kitD P host 6 genWY) rfl rfl (kitH P host 6 genWY) rfl rfl
    (.prim (kitAdd P host 6 genWY) .nil)

theorem genEnc1 : EncI (kitS P host 6 genWY) genW [.contNew 0, .resume 0 [⟨0, 2⟩]] (genWY 1) :=
  .contNew rfl
    (.resume (np := 0) (kitTag P host 6 genWY) rfl (genEnc2 P host) (kitD P host 6 genWY) rfl rfl (kitH P host 6 genWY) rfl rfl .nil)

theorem genOk : Ok (kitS P host 6 genWY) genW :=
  kitOk P host 6 genWY (by decide) fun f np body h =>
    match f, h with
    | 0, h => by cases h; exact ⟨by decide, rfl, genEnc0 P host⟩
    | 1, h => by cases h; exact ⟨by decide, rfl, genEnc1 P host⟩
    | 2, h => by cases h; exact ⟨by decide, rfl, genEnc2 P host⟩
    | 3, h => by cases h; exact ⟨by decide, rfl, genEnc3 P host⟩
    | 4, h => by cases h; exact ⟨by decide, rfl, genEnc4 P host⟩
    | 5, h => by cases h; exact ⟨by decide, rfl, genEnc5 P host⟩
    | _ + 6, h => nomatch h

theorem gen_run :
    runN (sstep genW i32Test) 60 (sInit 1 []) = .stop (.done [.val (Val.i32 6)]) := by
  rfl

theorem gen_check : checkRun genW 60 (sInit 1 []) = true := by
  rfl

theorem gen_tight : checkTight genW 60 (sInit 1 []) = true := by
  rfl

/-- **Sum of a generator**: exactly one behaviour, returning `1 + 2 + 3 = 6`. -/
theorem gen_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost (kitFx 6 genWY)
      (genProg (Profile.deterministic o) noHost) = {.returns [Val.i32 6]} := by
  rw [genProg, kit_beh 6 genWY o (genOk (Profile.deterministic o) noHost) 1 gen_run gen_check gen_tight]
  simp [obsB, allVals]

/-- The sum is a behaviour at every profile and host. -/
theorem gen_mem : Behaviour.returns [Val.i32 6] ∈
    behavioursFX' P host (kitFx 6 genWY) (genProg P host) :=
  kit_mem P host 6 genWY (genOk P host) 1 gen_run gen_check

/-! ## Take two, then drop the generator -/

theorem takeEnc0 : EncI (kitS P host 4 takeWY) takeW genBody genY :=
  .push rfl (.suspend (kitTag P host 4 takeWY) (.push rfl (.suspend (kitTag P host 4 takeWY) (.push rfl
    (.suspend (kitTag P host 4 takeWY) (.push rfl .nil))))))

theorem takeEnc3 : EncI (kitS P host 4 takeWY) takeW [.drop] [.core .drop] := .drop .nil

theorem takeEnc2 : EncI (kitS P host 4 takeWY) takeW [.resume 0 [⟨0, 3⟩], .prim 2 opAdd]
    (takeWY 2) :=
  .resume (np := 0) (kitTag P host 4 takeWY) rfl (takeEnc3 P host) (kitD P host 4 takeWY) rfl rfl (kitH P host 4 takeWY) rfl rfl
    (.prim (kitAdd P host 4 takeWY) .nil)

theorem takeEnc1 : EncI (kitS P host 4 takeWY) takeW [.contNew 0, .resume 0 [⟨0, 2⟩]]
    (takeWY 1) :=
  .contNew rfl
    (.resume (np := 0) (kitTag P host 4 takeWY) rfl (takeEnc2 P host) (kitD P host 4 takeWY) rfl rfl (kitH P host 4 takeWY) rfl rfl .nil)

theorem takeOk : Ok (kitS P host 4 takeWY) takeW :=
  kitOk P host 4 takeWY (by decide) fun f np body h =>
    match f, h with
    | 0, h => by cases h; exact ⟨by decide, rfl, takeEnc0 P host⟩
    | 1, h => by cases h; exact ⟨by decide, rfl, takeEnc1 P host⟩
    | 2, h => by cases h; exact ⟨by decide, rfl, takeEnc2 P host⟩
    | 3, h => by cases h; exact ⟨by decide, rfl, takeEnc3 P host⟩
    | _ + 4, h => nomatch h

theorem take_run :
    runN (sstep takeW i32Test) 40 (sInit 1 []) = .stop (.done [.val (Val.i32 3)]) := by
  rfl

theorem take_check : checkRun takeW 40 (sInit 1 []) = true := by
  rfl

theorem take_tight : checkTight takeW 40 (sInit 1 []) = true := by
  rfl

/-- **Take two from a generator and drop it**: exactly one behaviour, returning `1 + 2 = 3`. -/
theorem take_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost (kitFx 4 takeWY)
      (takeProg (Profile.deterministic o) noHost) = {.returns [Val.i32 3]} := by
  rw [takeProg, kit_beh 4 takeWY o (takeOk (Profile.deterministic o) noHost) 1 take_run take_check take_tight]
  simp [obsB, allVals]

/-- The result is a behaviour at every profile and host. -/
theorem take_mem : Behaviour.returns [Val.i32 3] ∈
    behavioursFX' P host (kitFx 4 takeWY) (takeProg P host) :=
  kit_mem P host 4 takeWY (takeOk P host) 1 take_run take_check

end Silmaril.Proofs.Wasm.FX.Examples
