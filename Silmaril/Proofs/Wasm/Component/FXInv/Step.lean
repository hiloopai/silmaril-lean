module

public import Silmaril.Proofs.Wasm.Component.FXInv.Erase
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Inversion of `StepFX` at host calls: the step lemma

`stepFX_noHostRedex`: the left-hand side of a `StepFX` step with no host (the internal step of
the FX engine) has no call of a component host function in its Core erasure, under any value
prefix and suffix. By induction on the step: the `core` rule is a host-free Core step
(`SingleThreaded.Step.noRedex`), the context rules preserve the property, and every other rule
has an inert head (an erased FX instruction, a trap, a branch, an exception) or calls an FX
function, whose host code is not a component host function.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXInv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Models.FX (AdminFX StepFX ConfigFX cvals cthrowing blockFX)
open Silmaril.Wasm.Component.FXEngine (FXCode fxOf noHostFX)
open Silmaril.Wasm.Component.FXInv
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- Closes `NoHostRedex s l` for a concrete `l` whose first non-value is inert. -/
macro "nhr_tac" : tactic => `(tactic| (
  apply noHostRedex_of_noRedex
  intro pre rest
  rw [decompose?_eq]
  simp [splitVals_plain_cons_nonval, splitVals_vals_append, splitVals_toAdmin_cons,
    splitVals_ref_cons, splitVals_intConst_cons, splitVals_floatConst_cons,
    splitVals_vecConst_cons, decompTop, decompHead, Admin.isCallRef, constI32, eraseA,
    decompose?_eq]))

/-- A call through a reference to an FX function is not a call of a component host
function. -/
theorem noHostRedex_invoke {s : Store (FXCode H)} {vs : List Execution.Core.Val} {c : Admin}
    {a : Nat} {fi : FuncInst (FXCode H)} {F : Silmaril.Wasm.Models.FX.FuncFX} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host (.fx F)) :
    NoHostRedex s (vals vs ++ [.ref (.func a), c]) := by
  intro pre rest Ec a' h args e
  rw [show vals pre ++ (vals vs ++ [.ref (.func a), c]) ++ rest =
      vals (pre ++ vs ++ [.ref (.func a)]) ++ c :: rest by simp [vals, Val.toAdmin],
    decompose?_of_split (splitVals_vals_cons (Admin.val?_of_IsCallRef hc) rest),
    decompHead_of_IsCallRef hc] at e
  unfold topRedex hostArity? at e
  simp only [List.getLast?_concat, hf, hcode] at e
  rcases hty : fi.type.funcType? with _ | ⟨ps, rs⟩ <;> simp only [hty] at e
  · cases e
  · split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨-, -, he, -⟩ := e
      cases he
    · cases e

theorem blockFX_noHost :
    blockFX (noHostFX H) fxOf = fun (_ : FXCode H) _ _ _ => False := by
  funext h s vs out
  simp [blockFX, noHostFX]

/-- **The step lemma**: a `StepFX` step of the FX engine starts from code with no call of a
component host function. -/
theorem stepFX_noHostRedex {P : Profile} {c c' : ConfigFX (FXCode H)}
    (hs : StepFX P (noHostFX H) fxOf c c') : NoHostRedex c.store (eraseL c.code) := by
  induction hs with
  | core h =>
    have h' : Step P (fun (_ : FXCode H) _ _ _ => False) _ _ := blockFX_noHost (H := H) ▸ h
    simpa using noHostRedex_of_noRedex (Step.noRedex h')
  | seq _ _ ih => simpa using NoHostRedex.seq ih _ _
  | ctxLabel _ ih => exact noHostRedex_single (NoHostRedex.hostFree ih) (Or.inl ⟨_, [], rfl⟩)
  | ctxFrame _ ih =>
    exact noHostRedex_single (NoHostRedex.hostFree ih) (Or.inr (Or.inr ⟨_, _, rfl⟩))
  | ctxHandler _ ih =>
    exact noHostRedex_single (NoHostRedex.hostFree ih) (Or.inr (Or.inl ⟨0, [], rfl⟩))
  | labelVals => exact noHostRedex_single (by simpa using hostFree_vals _) (Or.inl ⟨_, [], rfl⟩)
  | frameVals _ =>
    exact noHostRedex_single (by simpa using hostFree_vals _) (Or.inr (Or.inr ⟨_, _, rfl⟩))
  | handlerVals =>
    exact noHostRedex_single (by simpa using hostFree_vals _) (Or.inr (Or.inl ⟨0, [], rfl⟩))
  | @invoke s K f c vs a fi h F hc hf hcode hfx _ =>
    cases h with
    | host _ => cases hfx
    | fx F' => simpa [eraseA] using noHostRedex_invoke (vs := vs) hc hf hcode
  | suspend _ _ _ =>
    refine noHostRedex_single (NoHostRedex.hostFree (NoHostRedex.plug ?_ _))
      (Or.inr (Or.inl ⟨0, [], rfl⟩))
    nhr_tac
  | switch _ _ _ _ =>
    refine noHostRedex_single (NoHostRedex.hostFree (NoHostRedex.plug ?_ _))
      (Or.inr (Or.inl ⟨0, [], rfl⟩))
    nhr_tac
  | _ => nhr_tac

end Silmaril.Proofs.Wasm.Component.FXInv
