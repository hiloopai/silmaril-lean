module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.Conv

/-!
# Calm programs: the `StepFX'` behaviours are exactly the kernel's

Non-vacuity of `beh_eq`, with every hypothesis discharged for the deterministic profile and no
host calls:

* `add_beh`: a one-function program `addW` (push `1`, push `2`, `i32.add`) in a setting `addS`
  with one FX function has exactly one `StepFX'` behaviour, returning `[3]`;
* `res_beh`: a program `resW` that makes a continuation of a function returning `5` and resumes
  it under a handler (the setting `resS`: three FX functions, one tag, the block types of
  `FXAsyncFX`'s example) has exactly one `StepFX'` behaviour, returning `[5]`.

`checkCalm` decides the calm part of the fragment along a run by evaluation.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (checkRun supported_of_checkRun opAdd exTypes btD btH
  resumeFX exD exH)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- Check `calmCfg` along at most `fuel` steps of the kernel run, which must stop. -/
def checkCalm (W : Prog (Ins Val)) : Nat → SCfg Val → Bool
  | 0, _ => false
  | fuel + 1, x =>
    calmCfg x &&
      match sstep W i32Test x with
      | .next y => checkCalm W fuel y
      | .stop _ => true

theorem calm_of_checkCalm {W : Prog (Ins Val)} :
    ∀ (fuel : Nat) (x : SCfg Val), checkCalm W fuel x = true →
      ∀ n y, runN (sstep W i32Test) n x = .next y → calmCfg y = true
  | 0, _, h => nomatch h
  | fuel + 1, x, h => by
    have h' : calmCfg x = true ∧ (match sstep W i32Test x with
        | .next y => checkCalm W fuel y
        | .stop _ => true) = true := by
      simpa only [checkCalm, Bool.and_eq_true] using h
    intro n y hy
    cases n with
    | zero => cases hy; exact h'.1
    | succ n =>
      cases hx : sstep W i32Test x with
      | next x' =>
        rw [hx] at h'
        exact calm_of_checkCalm fuel x' h'.2 n y (by simpa only [runN, hx] using hy)
      | stop o => simp only [runN, hx, reduceCtorEq] at hy

/-- The kernel program: `1 + 2`. -/
def addW : Prog (Ins Val)
  | 0 => some (0, [.push (Val.i32 1), .push (Val.i32 2), .prim 2 opAdd])
  | _ => none

/-- Its encoded body. -/
def addY : List InstrFX :=
  [.core (.intConst .i32 1), .core .nop, .core (.intConst .i32 2), .core .nop,
    .core (.intBinOp .i32 .add)]

/-- The module instance. -/
def addM : ModuleInst := { types := exTypes, funcs := [0] }

/-- The FX function table. -/
def addFx : Nat → Option FuncFX
  | 0 => some ⟨addM, 0, 1, [], localGets 0 ++ addY⟩
  | _ => none

/-- The store: one FX function. -/
def addStore : Store Nat := { funcs := [⟨exTypes.head!, addM, .host 0⟩] }

/-- **The setting.** -/
def addS (P : Profile) (host : HostSemantics Nat) : Setup Nat where
  P := P
  host := host
  fx := addFx
  s := addStore
  M := addM
  f0 := ⟨[], addM⟩
  xf := ix
  fa := id
  xt := ix
  ta := id
  ar := fun _ => 1
  ct := ix 0

variable (P : Profile) (host : HostSemantics Nat)

theorem addPrim : PrimOk (addS P host) 2 opAdd (.intBinOp .i32 .add) := by
  intro bs f hbs _
  match bs, hbs with
  | [a, b], _ =>
    exact .numeric (.intBinOp (t := .i32) (op := .add) (x := b) (y := a) (z := b + a) rfl)

theorem addEnc : EncI (addS P host) addW [.push (Val.i32 1), .push (Val.i32 2), .prim 2 opAdd] addY :=
  .push rfl (.push rfl (.prim (addPrim P host) .nil))

theorem addOk : Ok (addS P host) addW where
  funcs f np body h := by
    match f, h with
    | 0, h =>
      cases h
      exact ⟨by decide, ⟨exTypes.head!, addM, .host 0⟩, 0, addY, rfl, rfl, rfl, rfl,
        addEnc P host⟩
  root := rfl
  tags := Function.injective_id

theorem add_kernel_run :
    runN (sstep addW i32Test) 10 (sInit 0 (([] : List Val).map .val)) =
      .stop (.done [.val (Val.i32 3)]) := by
  rfl

theorem add_calm : CalmSupported addW (sInit 0 (([] : List Val).map .val)) :=
  ⟨supported_of_checkRun 10 _ rfl, calm_of_checkCalm 10 _ rfl⟩

/-- **The WasmFX program has exactly one `StepFX'` behaviour: it returns `[3]`** (deterministic
profile, no host calls). -/
theorem add_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost addFx
      (fxInit (addS (Profile.deterministic o) noHost) 0 []) = {.returns [Val.i32 3]} := by
  have h := beh_eq (addS (Profile.deterministic o) noHost) (o := o) rfl rfl
    (addOk _ _) (rel_init (addS (Profile.deterministic o) noHost) 0 []) add_calm
  rw [show behavioursFX' (Profile.deterministic o) noHost addFx
      (fxInit (addS (Profile.deterministic o) noHost) 0 []) = _ from h,
    Silmaril.Proofs.Wasm.Models.FXAsync.beh_of_stop add_kernel_run]
  simp [obsB, Outcome.toObs, allVals]

/-! ## A resumed continuation that returns -/

/-- The kernel program: function `1` makes a continuation of function `0` (which returns `5`)
and resumes it under a handler for tag `0` (function `2`, never called). -/
def resW : Prog (Ins Val)
  | 0 => some (0, [.push (Val.i32 5)])
  | 1 => some (0, [.contNew 0, .resume 0 [⟨0, 2⟩]])
  | 2 => some (0, [])
  | _ => none

/-- The encoded bodies. -/
def resY : Nat → List InstrFX
  | 0 => [.core (.intConst .i32 5), .core .nop]
  | 1 => [.core (.refFunc (ix 0)), .fx (.contNew (ix 0)), resumeFX []]
  | _ => []

/-- The module instance. -/
def resM : ModuleInst := { types := exTypes, tags := [0], funcs := [0, 1, 2] }

/-- The FX function table. -/
def resFx : Nat → Option FuncFX
  | f => if f < 3 then some ⟨resM, 0, 1, [], localGets 0 ++ resY f⟩ else none

/-- The store: three FX functions and one tag. -/
def resStore : Store Nat :=
  { funcs := [0, 1, 2].map fun f => ⟨exTypes.head!, resM, .host f⟩, tags := [⟨exTypes.head!⟩] }

/-- **The setting.** -/
def resS (P : Profile) (host : HostSemantics Nat) : Setup Nat where
  P := P
  host := host
  fx := resFx
  s := resStore
  M := resM
  f0 := ⟨[], resM⟩
  xf := ix
  fa := id
  xt := ix
  ta := id
  ar := fun _ => 1
  ct := ix 0

theorem resTag : TagOk (resS P host) 0 := ⟨⟨exTypes.head!⟩, rfl, rfl⟩

theorem resEnc : ∀ f np body, resW f = some (np, body) →
    np = 0 ∧ EncI (resS P host) resW body (resY f)
  | 0, _, _, h => by cases h; exact ⟨rfl, .push rfl .nil⟩
  | 1, _, _, h => by
    cases h
    exact ⟨rfl, .contNew (bf := [.push (Val.i32 5)]) rfl
      (.resume (np := 0) (resTag P host) rfl .nil exD rfl rfl exH rfl rfl .nil)⟩
  | 2, _, _, h => by cases h; exact ⟨rfl, .nil⟩
  | _ + 3, _, _, h => nomatch h

theorem resW_lt : ∀ f np body, resW f = some (np, body) → f < 3
  | 0, _, _, _ | 1, _, _, _ | 2, _, _, _ => by decide
  | _ + 3, _, _, h => nomatch h

theorem resFuncs : ∀ f, f < 3 → resM.funcs[f]? = some f ∧
    resStore.funcs[f]? = some ⟨exTypes.head!, resM, .host f⟩ ∧
      resFx f = some ⟨resM, 0, 1, [], localGets 0 ++ resY f⟩
  | 0, _ | 1, _ | 2, _ => ⟨rfl, rfl, rfl⟩
  | _ + 3, h => absurd h (by omega)

theorem resOk : Ok (resS P host) resW where
  funcs f np body h := by
    obtain ⟨rfl, henc⟩ := resEnc P host f np body h
    have hf : f < 3 := resW_lt f 0 body h
    obtain ⟨h₁, h₂, h₃⟩ := resFuncs f hf
    have hix : (ix f : FuncIdx).toNat = f := by
      simp only [ix, Idx.toNat, Nat.mod_eq_of_lt (by omega : f < 2 ^ 32)]
    exact ⟨by decide, ⟨exTypes.head!, resM, .host f⟩, f, resY f,
      show resM.funcs[(ix f : FuncIdx).toNat]? = some f by rw [hix]; exact h₁, h₂, rfl,
      h₃, henc⟩
  root := rfl
  tags := Function.injective_id

theorem res_kernel_run :
    runN (sstep resW i32Test) 20 (sInit 1 (([] : List Val).map .val)) =
      .stop (.done [.val (Val.i32 5)]) := by
  rfl

theorem res_calm : CalmSupported resW (sInit 1 (([] : List Val).map .val)) :=
  ⟨supported_of_checkRun 20 _ rfl, calm_of_checkCalm 20 _ rfl⟩

/-- **A resumed continuation that returns**: the WasmFX program has exactly one `StepFX'`
behaviour, returning `[5]`. -/
theorem res_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost resFx
      (fxInit (resS (Profile.deterministic o) noHost) 1 []) = {.returns [Val.i32 5]} := by
  have h := beh_eq (resS (Profile.deterministic o) noHost) (o := o) rfl rfl
    (resOk _ _) (rel_init (resS (Profile.deterministic o) noHost) 1 []) res_calm
  rw [show behavioursFX' (Profile.deterministic o) noHost resFx
      (fxInit (resS (Profile.deterministic o) noHost) 1 []) = _ from h,
    Silmaril.Proofs.Wasm.Models.FXAsync.beh_of_stop res_kernel_run]
  simp [obsB, Outcome.toObs, allVals]

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
