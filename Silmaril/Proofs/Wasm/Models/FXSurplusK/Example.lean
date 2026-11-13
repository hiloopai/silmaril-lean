module

public import Silmaril.Proofs.Wasm.Models.FXSurplusK.Sim

/-!
# Surplus operands add behaviours on the encoded kernel fragment

`skW` (kernel program over Core values, one tag `0` of payload arity `1`):

* function 0: `push 10; push 20; push 1; suspend 0 1; suspend 0 1`;
* function 1, main: `contNew 0; resume 0 [(on 0 2)]`;
* function 2, the first handler (operands `k, 1`): `resume 0 [(on 0 3)]; i32.add` (resumes `k`
  under a second handler and adds the result to the first payload);
* function 3, the second handler (operands `k', y`): `drop` (drops `k'`, returns `y`).

The kernel suspends with operands `1, 20, 10` (top first): the payload is `1`, and the
continuation keeps `20, 10`. Its second `suspend` yields `20`, which the second handler returns,
and the first adds `1`: the kernel returns `[21]` and nothing else (`sk_kernel_beh`), and its
run is in the fragment (`skSupported`). The FX run with the tight payload returns `[21]` too
(`sk_fx_21`).

At the first `suspend`, `StepFX'` may also take the payload `20, 1`. The `br 0` out of
`block btH` drops `20`, so the first handler is entered as before, but the captured
continuation has lost `20` (`sim_suspend_ex`). Its second `suspend` then yields `10`: the run
returns `[11]` (`sk_fx_11`, by `surplus_in_fx`: the kernel run of the frame without `20`, which
is in the fragment too). The lost operand does not make the run stuck, because the frame that
lost it never returns: its continuation is dropped by the second handler.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXSurplusK

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX Silmaril.Proofs.Wasm.Models.FXAsyncFX

/-! ## The program -/

/-- The kernel program. -/
def skW : Prog (Ins Val)
  | 0 => some (0, [.push (Val.i32 10), .push (Val.i32 20), .push (Val.i32 1), .suspend 0 1,
      .suspend 0 1])
  | 1 => some (0, [.contNew 0, .resume 0 [⟨0, 2⟩]])
  | 2 => some (0, [.resume 0 [⟨0, 3⟩], .prim 2 opAdd])
  | 3 => some (0, [.drop])
  | _ => none

/-- The encoded bodies. -/
def skY : Nat → List InstrFX
  | 0 => [.core (.intConst .i32 10), .core .nop, .core (.intConst .i32 20), .core .nop,
      .core (.intConst .i32 1), .core .nop, .fx (.suspend (ix 0)), .fx (.suspend (ix 0))]
  | 1 => [.core (.refFunc (ix 0)), .fx (.contNew (ix 0)),
      resumeFX [resumeFX [.core .drop], .core (.intBinOp .i32 .add)]]
  | 2 => [resumeFX [.core .drop], .core (.intBinOp .i32 .add)]
  | 3 => [.core .drop]
  | _ => []

/-- The FX functions: host code `f` is kernel function `f`. -/
def skFx : Nat → Option FuncFX
  | f => if f < 4 then some ⟨exM, 0, 1, [], localGets 0 ++ skY f⟩ else none

/-- **The setting**, for every profile and host (the store and module of `exS`). -/
def skS (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat) : Setup Nat where
  P := P
  host := host
  fx := skFx
  s := exStore
  M := exM
  f0 := ⟨[], exM⟩
  xf := ix
  fa := id
  xt := ix
  ta := id
  ar := fun _ => 1
  ct := ix 0

/-! ## The setting satisfies the hypotheses -/

variable (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat)

theorem skTag : TagOk (skS P host) 0 := ⟨⟨exTypes.head!⟩, rfl, rfl⟩

theorem skPrim : PrimOk (skS P host) 2 opAdd (.intBinOp .i32 .add) := by
  intro bs f hbs _
  match bs, hbs with
  | [a, b], _ =>
    exact .numeric (.intBinOp (t := .i32) (op := .add) (x := b) (y := a) (z := b + a) rfl)

theorem skEnc3 : EncI (skS P host) skW (skW 3).get!.2 (skY 3) := .drop .nil

theorem skEnc2 : EncI (skS P host) skW (skW 2).get!.2 (skY 2) :=
  .resume (np := 0) (skTag P host) rfl (skEnc3 P host) exD rfl rfl exH rfl rfl
    (.prim (skPrim P host) .nil)

theorem skEnc0 : EncI (skS P host) skW (skW 0).get!.2 (skY 0) :=
  .push rfl (.push rfl (.push rfl (.suspend (t := 0) (skTag P host)
    (.suspend (t := 0) (skTag P host) .nil))))

theorem skEnc1 : EncI (skS P host) skW (skW 1).get!.2 (skY 1) :=
  .contNew (bf := (skW 0).get!.2) rfl
    (.resume (np := 0) (skTag P host) rfl (skEnc2 P host) exD rfl rfl exH rfl rfl .nil)

theorem skEnc : ∀ f np body, skW f = some (np, body) →
    np = 0 ∧ EncI (skS P host) skW body (skY f)
  | 0, _, _, h => by cases h; exact ⟨rfl, skEnc0 P host⟩
  | 1, _, _, h => by cases h; exact ⟨rfl, skEnc1 P host⟩
  | 2, _, _, h => by cases h; exact ⟨rfl, skEnc2 P host⟩
  | 3, _, _, h => by cases h; exact ⟨rfl, skEnc3 P host⟩
  | _ + 4, _, _, h => nomatch h

theorem skFuncs : ∀ f, f < 4 → exM.funcs[f]? = some f ∧
    exStore.funcs[f]? = some ⟨exTypes.head!, exM, .host f⟩ ∧
      skFx f = some ⟨exM, 0, 1, [], localGets 0 ++ skY f⟩
  | 0, _ | 1, _ | 2, _ | 3, _ => ⟨rfl, rfl, rfl⟩
  | _ + 4, h => absurd h (by omega)

theorem skW_lt : ∀ f np body, skW f = some (np, body) → f < 4
  | 0, _, _, _ | 1, _, _, _ | 2, _, _, _ | 3, _, _, _ => by decide
  | _ + 4, _, _, h => nomatch h

/-- **The setting satisfies the global hypotheses.** -/
theorem skOk : Ok (skS P host) skW where
  funcs f np body h := by
    obtain ⟨rfl, henc⟩ := skEnc P host f np body h
    have hf : f < 4 := skW_lt f 0 body h
    obtain ⟨h₁, h₂, h₃⟩ := skFuncs f hf
    have hix : (ix f : FuncIdx).toNat = f := by
      simp only [ix, Idx.toNat, Nat.mod_eq_of_lt (by omega : f < 2 ^ 32)]
    exact ⟨by decide, ⟨exTypes.head!, exM, .host f⟩, f, skY f,
      show exM.funcs[(ix f : FuncIdx).toNat]? = some f by rw [hix]; exact h₁, h₂, rfl,
      h₃, henc⟩
  root := rfl
  tags := Function.injective_id

/-! ## Kernel runs -/

/-- The kernel's initial configuration: the call of `main`. -/
abbrev skInit : SCfg Val := sInit 1 (([] : List Val).map .val)

theorem sk_kernel_run :
    runN (sstep skW i32Test) 40 skInit = .stop (.done [.val (Val.i32 21)]) := by
  rfl

theorem sk_check : checkRun skW 40 skInit = true := by
  rfl

/-- The kernel run from the call of `main` stays in the fragment. -/
theorem skSupported : Supported skW skInit :=
  supported_of_checkRun 40 _ sk_check

/-- **The kernel returns `[21]` and nothing else.** -/
theorem sk_kernel_beh :
    beh (sstep skW i32Test) skInit = {Obs.done [.val (Val.i32 21)]} :=
  Silmaril.Proofs.Wasm.Models.FXAsync.beh_of_stop sk_kernel_run

/-- The kernel configuration at the first `suspend` (after six steps). -/
def skSus : SCfg Val :=
  match runN (sstep skW i32Test) 6 skInit with
  | .next y => y
  | .stop _ => skInit

theorem sk_run_sus : runN (sstep skW i32Test) 6 skInit = .next skSus := by
  rfl

/-- The frame at the first `suspend`. -/
def skFr : SFrame Val :=
  match skSus.stack with
  | fr :: _ => fr
  | [] => ⟨[], [], none⟩

theorem skSus_stack : skSus.stack = skFr :: skSus.stack.tail := by
  rfl

theorem skFr_code : skFr.code = .suspend 0 1 :: [.suspend 0 1] := by
  rfl

theorem skFr_ops : skFr.ops = [.val (Val.i32 1)] ++ [.val (Val.i32 20)] ++ [.val (Val.i32 10)] := by
  rfl

/-- The configuration at the first `suspend` with the operand `20` deleted. -/
abbrev skDel : SCfg Val := withOps skSus ([.val (Val.i32 1)] ++ [.val (Val.i32 10)])

theorem sk_del_run :
    runN (sstep skW i32Test) 40 skDel = .stop (.done [.val (Val.i32 11)]) := by
  rfl

theorem sk_del_check : checkRun skW 40 skDel = true := by
  rfl

/-! ## `StepFX'` behaviours -/

/-- **With the tight payload, the WasmFX program returns `[21]`**, for every profile and host. -/
theorem sk_fx_21 : Behaviour.returns [Val.i32 21] ∈
    behavioursFX' P host skFx (fxInit (skS P host) 1 []) := by
  have hb : Obs.done [.val (Val.i32 21)] ∈ beh (sstep skW i32Test) skInit :=
    Or.inl ⟨40, .done [.val (Val.i32 21)], sk_kernel_run, rfl⟩
  exact beh_in_fx (skS P host) (skOk P host) (FXAsyncFX.rel_init (skS P host) 1 []) skSupported _ hb

/-- **With the surplus payload `20, 1` at the first `suspend`, it returns `[11]`**, for every
profile and host. -/
theorem sk_fx_11 : Behaviour.returns [Val.i32 11] ∈
    behavioursFX' P host skFx (fxInit (skS P host) 1 []) := by
  obtain ⟨d, hd, hR⟩ := steps_in_fx (skS P host) (skOk P host) 6
    (FXAsyncFX.rel_init (skS P host) 1 []) skSupported sk_run_sus
  have hb : Obs.done [.val (Val.i32 11)] ∈ beh (sstep skW i32Test) skDel :=
    Or.inl ⟨40, .done [.val (Val.i32 11)], sk_del_run, rfl⟩
  have hin : obsB (Obs.done [.val (Val.i32 11)]) ∈ behavioursFX' P host skFx d :=
    surplus_in_fx (skS P host) (skOk P host) hR skSus_stack skFr_code skFr_ops rfl
      (supported_of_checkRun 40 _ sk_del_check) _ hb
  rcases hin with ⟨e, r, he, hcode, hbe⟩ | ⟨hdv, -⟩
  · exact Or.inl ⟨e, r, hd.trans he, hcode, hbe⟩
  · exact absurd hdv (by simp only [obsB, allVals, Option.map_some, List.reverse_cons,
      List.reverse_nil, List.nil_append, reduceCtorEq, not_false_eq_true])

/-- **Surplus operands add behaviours on the encoded kernel fragment**: with `Ok`, `Rel` and
the kernel run in the fragment (but not tight), the `StepFX'` behaviours of the encoding are not
the images of the kernel's. -/
theorem sk_not_beh_eq : behavioursFX' P host skFx (fxInit (skS P host) 1 []) ≠
    obsB '' beh (sstep skW i32Test) skInit := by
  intro heq
  have h11 := sk_fx_11 P host
  rw [heq, sk_kernel_beh, Set.image_singleton] at h11
  have hne : obsB (Obs.done [.val (Val.i32 21)]) ≠ Behaviour.returns [Val.i32 11] := by
    simp only [obsB, allVals, Option.map_some, List.reverse_cons, List.reverse_nil,
      List.nil_append, ne_eq, Behaviour.returns.injEq, List.cons.injEq, and_true]
    decide
  exact hne (Set.mem_singleton_iff.mp h11).symm

end Silmaril.Proofs.Wasm.Models.FXSurplusK
