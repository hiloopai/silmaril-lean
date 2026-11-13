module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.Beh
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# A generator, end to end: kernel, asyncify target and `StepFX'`

`exW` (kernel program over Core values):

* function 0, a generator: `push 1; suspend 0 1; push 2` (yields `1`, then returns `2`);
* function 1, main: `contNew 0; resume 0 [(on 0 2)]`;
* function 2, the handler of the first yield: `resume 0 [(on 0 3)]; i32.add` (resumes the
  generator under a fresh handler and adds the yielded value to its result);
* function 3, the handler of a second yield (never reached): no code.

`exS P host` is a setting for every profile and host: a store with these four functions as FX
functions (host codes `0 … 3`) whose bodies are the encodings `exY f`, one tag, and a module
instance with the two block types of the `resume` encoding. Everything is checked:

* `exOk`: the global hypotheses `Ok` (the encodings are `EncI` derivations, `exPrim`: `i32.add`
  computes the kernel's addition);
* `exSupported`: the kernel run from the call of `main` stays in the fragment (a closed
  evaluation, `checkRun`);
* `ex_kernel`: the kernel returns `[3]`, and so does the asyncify target (`lower_correct`);
* **`ex_fx`**: the WasmFX program `fxInit (exS P host) 1 []` returns `[3]` under `StepFX'`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

/-! ## Checking the fragment along a run -/

/-- Check `fine` along at most `fuel` steps of the kernel run, which must stop. -/
def checkRun (W : Prog (Ins Val)) : Nat → SCfg Val → Bool
  | 0, _ => false
  | fuel + 1, x =>
    fine W x &&
      match sstep W i32Test x with
      | .next y => checkRun W fuel y
      | .stop _ => true

theorem supported_of_checkRun {W : Prog (Ins Val)} :
    ∀ (fuel : Nat) (x : SCfg Val), checkRun W fuel x = true → Supported W x
  | 0, _, h => nomatch h
  | fuel + 1, x, h => by
    have h' : fine W x = true ∧ (match sstep W i32Test x with
        | .next y => checkRun W fuel y
        | .stop _ => true) = true := by
      simpa only [checkRun, Bool.and_eq_true] using h
    intro n y hy
    cases n with
    | zero => cases hy; exact h'.1
    | succ n =>
      cases hx : sstep W i32Test x with
      | next x' =>
        rw [hx] at h'
        exact supported_of_checkRun fuel x' h'.2 n y (by simpa only [runN, hx] using hy)
      | stop o => simp only [runN, hx, reduceCtorEq] at hy

/-! ## The program -/

/-- `i32.add` on kernel operands (top first). -/
def opAdd : List Val → List Val
  | [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => [Val.i32 (b + a)]
  | vs => vs

/-- The kernel program. -/
def exW : Prog (Ins Val)
  | 0 => some (0, [.push (Val.i32 1), .suspend 0 1, .push (Val.i32 2)])
  | 1 => some (0, [.contNew 0, .resume 0 [⟨0, 2⟩]])
  | 2 => some (0, [.resume 0 [⟨0, 3⟩], .prim 2 opAdd])
  | 3 => some (0, [])
  | _ => none

/-- The block types: `[cont] → [r]` and `[cont] → [payload, cont]`. -/
def exTypes : List Silmaril.Wasm.Validation.DefType :=
  [Silmaril.Wasm.V2.FuncType.toDefType ⟨[.num (.int .i32)], [.num (.int .i32)]⟩,
    Silmaril.Wasm.V2.FuncType.toDefType ⟨[.num (.int .i32)], [.num (.int .i32), .num (.int .i32)]⟩]

/-- The module instance shared by all frames. -/
def exM : ModuleInst := { types := exTypes, tags := [0], funcs := [0, 1, 2, 3] }

/-- `block btD`. -/
def btD : BlockType := .typeIdx (ix 0)

/-- `block btH`. -/
def btH : BlockType := .typeIdx (ix 1)

/-- The encoded `resume` with inlined handler code `Z`. -/
def resumeFX (Z : List InstrFX) : InstrFX :=
  .block btD (.block btH [.fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)]), .core (.br (ix 1))] :: Z)

/-- The encoded bodies. -/
def exY : Nat → List InstrFX
  | 0 => [.core (.intConst .i32 1), .core .nop, .fx (.suspend (ix 0)), .core (.intConst .i32 2),
      .core .nop]
  | 1 => [.core (.refFunc (ix 0)), .fx (.contNew (ix 0)),
      resumeFX [resumeFX [], .core (.intBinOp .i32 .add)]]
  | 2 => [resumeFX [], .core (.intBinOp .i32 .add)]
  | _ => []

/-- The FX functions: host code `f` is kernel function `f`. -/
def exFx : Nat → Option FuncFX
  | f => if f < 4 then some ⟨exM, 0, 1, [], localGets 0 ++ exY f⟩ else none

/-- The store: four FX functions and one tag. -/
def exStore : Store Nat :=
  { funcs := [0, 1, 2, 3].map fun f => ⟨exTypes.head!, exM, .host f⟩,
    tags := [⟨exTypes.head!⟩] }

/-- **The setting**, for every profile and host. -/
def exS (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat) : Setup Nat where
  P := P
  host := host
  fx := exFx
  s := exStore
  M := exM
  f0 := ⟨[], exM⟩
  xf := ix
  fa := id
  xt := ix
  ta := id
  ar := fun _ => 1
  ct := ix 0

/-! ## Runs -/

theorem ex_kernel_run :
    runN (sstep exW i32Test) 40 (sInit 1 []) = .stop (.done [.val (Val.i32 3)]) := by
  rfl

theorem ex_check : checkRun exW 40 (sInit 1 []) = true := by
  rfl

theorem ex_tgt_run :
    runN (tstep (compP exW) i32Test) 80 (tInit 1 []) = .stop (.done [.val (Val.i32 3)]) := by
  rfl

/-! ## The setting satisfies the hypotheses -/

variable (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat)

theorem exTag : TagOk (exS P host) 0 := ⟨⟨exTypes.head!⟩, rfl, rfl⟩

theorem exD : exM.blockType? btD = some ([.num (.int .i32)], [.num (.int .i32)]) := by
  rfl

theorem exH : exM.blockType? btH =
    some ([.num (.int .i32)], [.num (.int .i32), .num (.int .i32)]) := by
  rfl

theorem exPrim : PrimOk (exS P host) 2 opAdd (.intBinOp .i32 .add) := by
  intro bs f hbs _
  match bs, hbs with
  | [a, b], _ =>
    exact .numeric (.intBinOp (t := .i32) (op := .add) (x := b) (y := a) (z := b + a) rfl)

/-- The inlined handler of the second yield. -/
theorem enc3 : EncI (exS P host) exW [] [] := .nil

/-- The handler of the first yield: `resume` under handler 3, then `i32.add`. -/
theorem enc2 : EncI (exS P host) exW (exW 2).get!.2 (exY 2) :=
  .resume (np := 0) (exTag P host) rfl (enc3 P host) (exD) rfl rfl (exH) rfl rfl
    (.prim (exPrim P host) .nil)

theorem enc0 : EncI (exS P host) exW (exW 0).get!.2 (exY 0) :=
  .push rfl (.suspend (t := 0) (exTag P host) (.push rfl .nil))

theorem enc1 : EncI (exS P host) exW (exW 1).get!.2 (exY 1) :=
  .contNew (bf := (exW 0).get!.2) rfl
    (.resume (np := 0) (exTag P host) rfl (enc2 P host) (exD) rfl rfl (exH) rfl rfl .nil)

theorem exEnc : ∀ f np body, exW f = some (np, body) → np = 0 ∧ EncI (exS P host) exW body (exY f)
  | 0, _, _, h => by cases h; exact ⟨rfl, enc0 P host⟩
  | 1, _, _, h => by cases h; exact ⟨rfl, enc1 P host⟩
  | 2, _, _, h => by cases h; exact ⟨rfl, enc2 P host⟩
  | 3, _, _, h => by cases h; exact ⟨rfl, enc3 P host⟩
  | _ + 4, _, _, h => nomatch h

theorem exFuncs : ∀ f, f < 4 → exM.funcs[f]? = some f ∧
    exStore.funcs[f]? = some ⟨exTypes.head!, exM, .host f⟩ ∧
      exFx f = some ⟨exM, 0, 1, [], localGets 0 ++ exY f⟩
  | 0, _ | 1, _ | 2, _ | 3, _ => ⟨rfl, rfl, rfl⟩
  | _ + 4, h => absurd h (by omega)

theorem exW_lt : ∀ f np body, exW f = some (np, body) → f < 4
  | 0, _, _, _ | 1, _, _, _ | 2, _, _, _ | 3, _, _, _ => by decide
  | _ + 4, _, _, h => nomatch h

/-- **The setting satisfies the global hypotheses.** -/
theorem exOk : Ok (exS P host) exW where
  funcs f np body h := by
    obtain ⟨rfl, henc⟩ := exEnc P host f np body h
    have hf : f < 4 := exW_lt f 0 body h
    obtain ⟨h₁, h₂, h₃⟩ := exFuncs f hf
    have hix : (ix f : FuncIdx).toNat = f := by
      simp only [ix, Idx.toNat, Nat.mod_eq_of_lt (by omega : f < 2 ^ 32)]
    exact ⟨by decide, ⟨exTypes.head!, exM, .host f⟩, f, exY f,
      show exM.funcs[(ix f : FuncIdx).toNat]? = some f by rw [hix]; exact h₁, h₂, rfl,
      h₃, henc⟩
  root := rfl
  tags := Function.injective_id

/-- The kernel run from the call of `main` stays in the fragment. -/
theorem exSupported : Supported exW (sInit 1 (([] : List Val).map .val)) :=
  supported_of_checkRun 40 _ ex_check

/-- **The WasmFX program returns `[3]`** under `StepFX'`, for every profile and host. -/
theorem ex_fx : Behaviour.returns [Val.i32 3] ∈
    behavioursFX' P host exFx (fxInit (exS P host) 1 []) := by
  have hb : Obs.done [.val (Val.i32 3)] ∈ beh (sstep exW i32Test) (sInit 1 (([] : List Val).map .val)) :=
    Or.inl ⟨40, .done [.val (Val.i32 3)], ex_kernel_run, rfl⟩
  exact beh_in_fx (exS P host) (exOk P host) (rel_init (exS P host) 1 []) (exSupported) _ hb

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
