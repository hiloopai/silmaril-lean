module

public import Silmaril.Proofs.Wasm.FX.Examples.EveryRun.Gen
public import Silmaril.Wasm.FX.Examples.EveryRun.Defs

/-!
# Cancelling a generator with `resume_throw`, by the every-run logic

`cancel_tsafe`: the program `cancelProg` (`Silmaril.Wasm.FX.Examples.EveryRun.Defs`) is totally
safe, at every profile without host calls, for the postcondition "throws the exception at
address `0`". The generator's first stage is `gen_yield`; at the yield the handler code runs
`resume_throw` (`tsafe_resumeThrow`, for both splits of the value below the continuation into
the exception's fields), and the exception travels out of the generator's label and frame, the
handler and the main function's blocks unchanged.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts newCont)
open Silmaril.Wasm.FX.Logic.EveryRun (Unhandled TSafe Inv seqPost labelPost framePost handlerPost totJ)
open Silmaril.Proofs.Wasm.FX.Logic.EveryRun
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-- The postcondition: the program throws the exception at address `a`. -/
def qThrow (a : Nat) : PostFX Nat := fun _ _ _ o => o = .throw a

theorem inv_qThrow (a : Nat) : Inv (qThrow a) :=
  inv_of_noEff (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ h => by cases h)

theorem cancel_body0 :
    Yields P 2 cancelWY [none] [.core (.ref (.func 0)), .core (.callRefType kitTypes.head!)]
      (Val.i32 1) (genK 2 gR1) := by
  intro Q₁ hQ₁ hy hb
  show TSafe _ _ _ ⟨_, _, _, fvals ([] ++ [.val (.ref (.func 0))]) ++ [.core (.callRefType _)]⟩
  refine tsafe_invoke (by simp [Admin.IsCallRef]) rfl rfl rfl fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  exact gen_yield hQ₁ 1 gR1 hy hb

/-- The cancelled generator: an exception at its `suspend`, under its label and frame. -/
theorem cancel_throw {s : Store Nat} {K : Conts} {Q : PostFX Nat} (hQ : Inv Q)
    (hq : Q s K (kF 2) (.throw 0)) :
    TSafe P (kitFx 2 cancelWY) Q
      ⟨s, K, kF 2, [.frame 1 (kF 2) [.label 1 [] (cthrowing 0 ++ gR1)]]⟩ := by
  refine tsafe_frame' (us := []) hQ (tsafe_label' (us := []) (by inv_tac) ?_)
  refine tsafe_seq' (by inv_tac) ?_
  refine tsafe_throw (ws := []) (r := []) ?_ |> fun h => by simpa using h
  simp only [seqPost, labelPost, framePost]
  exact hq

/-- **The cancelled generator is totally safe** and throws the exception at address `0`. -/
theorem cancel_tsafe : TSafe P (kitFx 2 cancelWY) (qThrow 0) (cancelProg P noHost) := by
  have hQ := inv_qThrow 0
  show TSafe _ _ _ ⟨kitStore 2, [], kF 2, fvals [] ++ .core (.plain (.call (ix 1))) :: []⟩
  refine tsafe_call hQ rfl rfl rfl rfl fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  refine tsafe_label' (us := []) (by inv_tac) ?_
  refine tsafe_refFunc (V := []) (by inv_tac) rfl ?_
  refine tsafe_contNew_seq (V := []) (by inv_tac) rfl ?_
  refine resumeFX_yield (us := []) (C := newCont 0 ⟨kitTypes.head!, kitM 2, .host 0⟩)
    (by inv_tac) rfl cancel_body0 ?_
  show TSafe _ _ _ ⟨_, _, _, fvals ([.val (Val.i32 1)] ++ [.cont 1]) ++
    [.fx (.resumeThrow (ix 0) (ix 0) [])]⟩
  refine tsafe_resumeThrow (C := genK 2 gR1) rfl rfl rfl fun V₁ vs hV => ?_
  refine tsafe_handler' (us := V₁) (by inv_tac) ?_
  refine cancel_throw (by inv_tac) ?_
  simp only [handlerPost, labelPost, seqPost, framePost]
  rfl

end Silmaril.Proofs.Wasm.FX.Examples.EveryRun
