module

public import Silmaril.Proofs.Wasm.LambdaRTL.Sim
public import Silmaril.Wasm.SSA.Fragment.Thms

/-!
# Wasm fragment → λRTL: whole functions (proofs)

The function body is translated at depth `0` with no block labels; the function's own label and
`return` leave through `ret`. With fuel that suffices (or on which the fragment interpreter
returns), the λRTL observation is the interpreter's (`evalObs_eq_obsOpt`); with the
interpreter's soundness and completeness this gives the exact characterisations of terminating
runs, traps and stuck calls restated in `Silmaril.Wasm.LambdaRTL.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Out Res blockRes funcExit evalE evalArgs evalSeq)
open Silmaril.Wasm.LambdaRTL
open Silmaril.Wasm (IntType)

theorem initStore_spec (f : FragFunc) (args : List WVal) :
    InitStore f args (initStore f args) := by
  intro i h
  simp [initStore, List.getElem?_eq_getElem h]

theorem agree_init {f : FragFunc} {args : List WVal} {σ : Store}
    (hargs : args.map WVal.type = f.params) (hσ : InitStore f args σ) :
    Agree (nlocOf f) (f.initLocals args) σ := by
  refine ⟨?_, hσ⟩
  have := congrArg List.length hargs
  simp only [List.length_map] at this
  simp [FragFunc.initLocals, nlocOf, this]

theorem trFunc_eq {f : FragFunc} {R : WRegion} (hf : trFunc f = some R) :
    loopFreeL f.body = true ∧ R = trBody f := by
  unfold trFunc at hf
  split at hf
  · exact ⟨by assumption, (Option.some.inj hf).symm⟩
  · cases hf

/-- The translated body observes what the interpreter computes, at any fuel that suffices or on
which the interpreter returns. -/
theorem evalObs_eq_obsOpt {f : FragFunc} {args : List WVal} {σ : Store} {n : Nat}
    (hlf : loopFreeL f.body = true) (hargs : args.map WVal.type = f.params)
    (hσ : InitStore f args σ) (hn : fuelSeq f.body ≤ n ∨ (f.eval n args).isSome = true) :
    (trBody f).evalObs model σ = obsOpt (f.eval n args) := by
  have hn' : fuelSeq f.body ≤ n ∨ (evalSeq n (f.initLocals args) none f.body).isSome = true := by
    rcases hn with hn | hn
    · exact Or.inl hn
    · right
      rw [FragFunc.eval, ite_eq_left hargs] at hn
      cases h : evalSeq n (f.initLocals args) none f.body with
      | none => simp [h] at hn
      | some _ => rfl
  have hS := (sim (nloc := nlocOf f) (res := f.result) n).2.2 f.body [] 0 (f.initLocals args) σ
    (retR f.result 0 (seqVal false f.body)) none hlf hn' (by intro t ht; simp at ht)
    (agree_init hargs hσ) (SlotRes.none' _ _)
  unfold Region.evalObs trBody
  rw [FragFunc.eval, ite_eq_left hargs]
  cases h : evalSeq n (f.initLocals args) none f.body with
  | none =>
    rw [h] at hS
    simp only [SimR] at hS
    rw [hS]
    rfl
  | some out =>
    rw [h] at hS
    cases out with
    | ok ls' r =>
      obtain ⟨σ', -, -, hs, hx⟩ := hS
      have hv := seqVal_ok h
      simp only [Option.isSome_none] at hv
      rw [hx, ← hv, eval_retR hs]
      rfl
    | brk l ls' r =>
      simp only [SimR, SimAbr, List.getElem?_nil, List.length_nil] at hS
      cases l with
      | zero =>
        simp only [↓reduceIte] at hS
        obtain ⟨σ', hx⟩ := hS
        rw [hx]
        rfl
      | succ l =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte] at hS
        rw [hS]
        rfl
    | ret r =>
      simp only [SimR, SimAbr] at hS
      obtain ⟨σ', hx⟩ := hS
      rw [hx]
      rfl
    | trap =>
      simp only [SimR, SimAbr] at hS
      rw [hS]
      rfl

theorem obsOf_ne_stuck (o : FOut) : obsOf o ≠ .error .stuck := by
  cases o <;> simp [obsOf]

theorem obsOf_injective {o o' : FOut} (h : obsOf o = obsOf o') : o = o' := by
  cases o with
  | ret r =>
    cases o' with
    | ret r' =>
      simp only [obsOf, Except.ok.injEq, Prod.mk.injEq, true_and] at h
      cases r <;> cases r' <;> simp_all [encR]
    | trap => simp [obsOf] at h
  | trap =>
    cases o' with
    | ret r' => simp [obsOf] at h
    | trap => rfl

theorem trFunc_evalObs {f : FragFunc} {R : WRegion} (hf : trFunc f = some R) {args : List WVal}
    (hargs : args.map WVal.type = f.params) {σ : Store} (hσ : InitStore f args σ) {n : Nat}
    (hn : fuelSeq f.body ≤ n ∨ (f.eval n args).isSome = true) :
    R.evalObs model σ = obsOpt (f.eval n args) := by
  obtain ⟨hlf, rfl⟩ := trFunc_eq hf
  exact evalObs_eq_obsOpt hlf hargs hσ hn

theorem trFunc_run_iff {f : FragFunc} {R : WRegion} (hf : trFunc f = some R) {args : List WVal}
    (hargs : args.map WVal.type = f.params) {σ : Store} (hσ : InitStore f args σ) (o : FOut) :
    f.Run args o ↔ R.evalObs model σ = obsOf o := by
  constructor
  · intro hr
    obtain ⟨fuel, hfuel⟩ := FragFunc.eval_complete hr
    rw [trFunc_evalObs hf hargs hσ (Or.inr (by rw [hfuel]; rfl)), hfuel]
    rfl
  · intro he
    rw [trFunc_evalObs hf hargs hσ (Or.inl le_rfl)] at he
    cases hev : f.eval (fuelSeq f.body) args with
    | none =>
      rw [hev] at he
      exact absurd he.symm (obsOf_ne_stuck o)
    | some o' =>
      rw [hev] at he
      have := obsOf_injective he
      subst this
      exact FragFunc.eval_sound hev

theorem trFunc_stuck_iff {f : FragFunc} {R : WRegion} (hf : trFunc f = some R)
    {args : List WVal} (hargs : args.map WVal.type = f.params) {σ : Store}
    (hσ : InitStore f args σ) :
    (¬ ∃ o, f.Run args o) ↔ R.evalObs model σ = .error .stuck := by
  constructor
  · intro hno
    rw [trFunc_evalObs hf hargs hσ (Or.inl le_rfl)]
    cases hev : f.eval (fuelSeq f.body) args with
    | none => rfl
    | some o => exact absurd ⟨o, FragFunc.eval_sound hev⟩ hno
  · rintro he ⟨o, hr⟩
    rw [(trFunc_run_iff hf hargs hσ o).1 hr] at he
    exact obsOf_ne_stuck o he

end Silmaril.Proofs.Wasm.LambdaRTL
