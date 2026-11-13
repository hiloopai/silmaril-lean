module

public import Silmaril.Proofs.Wasm.LambdaRTL.Loop.Bwd
public import Silmaril.Proofs.Wasm.LambdaRTL.Run

/-!
# Wasm fragment → λRTL with loops: whole functions (proofs)

`evalObsL_of_seq`: a body derivation determines the λRTL observation of the translated function
(`obsTopL`). With the backward simulation (`bwdS`) this gives the exact characterisations
restated in `Silmaril.Wasm.LambdaRTL.Loop.Thms`: terminating runs and traps are λRTL results, and a
call without fragment derivation is a stuck **or divergent** λRTL run.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL (Val Op Model upd)
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Out Res blockRes funcExit evalE evalArgs evalSeq
  Exec Args Seq)
open Silmaril.Wasm.LambdaRTL
open Silmaril.Wasm (IntType)

/-- The λRTL observation of a function-body outcome (`none` of `funcExit`: stuck). -/
def obsTopL (res : Option IntType) (out : Out (Option WVal)) : Except WErr (LLab × RVal) :=
  match funcExit res out with
  | some o => obsOfL o
  | none => .error .stuck

theorem obsOfL_ne_stuck (o : FOut) : obsOfL o ≠ .error .stuck := by
  cases o <;> simp [obsOfL]

theorem obsOfL_injective {o o' : FOut} (h : obsOfL o = obsOfL o') : o = o' := by
  cases o with
  | ret r =>
    cases o' with
    | ret r' =>
      simp only [obsOfL, Except.ok.injEq, Prod.mk.injEq, true_and] at h
      cases r <;> cases r' <;> simp_all [encR]
    | trap => simp [obsOfL] at h
  | trap =>
    cases o' with
    | ret r' => simp [obsOfL] at h
    | trap => rfl

theorem evalObsL_run (r : LRegion) (σ : Store) :
    (r.evalObs modelL σ).run = (Silmaril.SSA.LambdaRTL.obs <$> r.evalRTL modelL σ).run := rfl

/-- A body derivation determines the λRTL observation of the function. -/
theorem evalObsL_of_seq {f : FragFunc} {args : List WVal} (hargs : args.map WVal.type = f.params)
    {σ : Store} (hσ : InitStore f args σ) {out : Out (Option WVal)}
    (h : Seq (f.initLocals args) none f.body out) :
    ((trBodyL f).evalObs modelL σ).run = Part.some (obsTopL f.result out) := by
  have hsim := fwdS (res := f.result) (k := retRL f.result 0 (seqVal false f.body)) h
    (ks := []) (sd := 0) (by intro t ht; simp at ht) (agree_init hargs hσ) (SlotRes.none' _ _)
  rw [evalObsL_run]
  unfold trBodyL
  cases out with
  | ok ls' r =>
    obtain ⟨σ', -, -, hs, hx⟩ := hsim
    have hv : r.isSome = seqVal false f.body := by simpa using seqVal_exec h
    rw [hx, ← hv, evalL_retRL hs, map_okL]
    rfl
  | brk l ls' r =>
    simp only [SimRL, SimAbrL, List.getElem?_nil, List.length_nil] at hsim
    cases l with
    | zero =>
      simp only [↓reduceIte] at hsim
      obtain ⟨σ', hx⟩ := hsim
      rw [hx, map_okL]
      rfl
    | succ l =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte] at hsim
      rw [hsim, map_errL]
      rfl
  | ret r =>
    simp only [SimRL, SimAbrL] at hsim
    obtain ⟨σ', hx⟩ := hsim
    rw [hx, map_okL]
    rfl
  | trap =>
    simp only [SimRL, SimAbrL] at hsim
    rw [hsim, map_errL]
    rfl

/-- A non-stuck terminating observation comes from a body derivation. -/
theorem seq_of_evalObsL {f : FragFunc} {args : List WVal} (hargs : args.map WVal.type = f.params)
    {σ : Store} (hσ : InitStore f args σ) {z : Except WErr (LLab × RVal)}
    (hz : ((trBodyL f).evalObs modelL σ).run = Part.some z) (hne : z ≠ .error .stuck) :
    ∃ out, Seq (f.initLocals args) none f.body out := by
  rw [evalObsL_run] at hz
  have hmem : z ∈ (Silmaril.SSA.LambdaRTL.obs <$> (trBodyL f).evalRTL modelL σ).run := by
    rw [hz]
    exact Part.mem_some z
  obtain ⟨w, hw, hzw⟩ := mem_map_run hmem
  have hgood : Good ((trBodyL f).evalRTL modelL σ) := by
    refine ⟨w, hw, ?_⟩
    rintro rfl
    exact hne hzw
  exact bwdS (nloc := nlocOf f) (res := f.result) f.body [] 0 (f.initLocals args) σ _ none
    (by intro t ht; simp at ht) (agree_init hargs hσ) (SlotRes.none' _ _) hgood

theorem trBodyL_run_iff {f : FragFunc} {args : List WVal} (hargs : args.map WVal.type = f.params)
    {σ : Store} (hσ : InitStore f args σ) (o : FOut) :
    f.Run args o ↔ ((trBodyL f).evalObs modelL σ).run = Part.some (obsOfL o) := by
  constructor
  · rintro ⟨-, out, hseq, hexit⟩
    rw [evalObsL_of_seq hargs hσ hseq]
    simp only [obsTopL, hexit]
  · intro h
    obtain ⟨out, hseq⟩ := seq_of_evalObsL hargs hσ h (obsOfL_ne_stuck o)
    rw [evalObsL_of_seq hargs hσ hseq] at h
    have h' := Part.some_injective h
    unfold obsTopL at h'
    cases hexit : funcExit f.result out with
    | none =>
      rw [hexit] at h'
      exact absurd h'.symm (obsOfL_ne_stuck o)
    | some o' =>
      rw [hexit] at h'
      have := obsOfL_injective h'
      subst this
      exact ⟨hargs, out, hseq, hexit⟩

theorem trBodyL_noRun_iff {f : FragFunc} {args : List WVal}
    (hargs : args.map WVal.type = f.params) {σ : Store} (hσ : InitStore f args σ) :
    (¬ ∃ o, f.Run args o) ↔
      (((trBodyL f).evalObs modelL σ).run = Part.some (.error .stuck) ∨
        ((trBodyL f).evalObs modelL σ).run = Part.none) := by
  constructor
  · intro hno
    rcases Part.eq_none_or_eq_some ((trBodyL f).evalObs modelL σ).run with h | ⟨z, h⟩
    · exact Or.inr h
    · left
      by_cases hz : z = .error .stuck
      · rw [h, hz]
      · obtain ⟨out, hseq⟩ := seq_of_evalObsL hargs hσ h hz
        have h2 := evalObsL_of_seq hargs hσ hseq
        cases hexit : funcExit f.result out with
        | none =>
          rw [h2]
          simp only [obsTopL, hexit]
        | some o => exact absurd ⟨o, hargs, out, hseq, hexit⟩ hno
  · rintro (h | h) ⟨o, hr⟩
    · rw [(trBodyL_run_iff hargs hσ o).1 hr] at h
      exact obsOfL_ne_stuck o (Part.some_injective h)
    · rw [(trBodyL_run_iff hargs hσ o).1 hr] at h
      exact Part.some_ne_none _ h

theorem trBodyL_evalObs_of_eval {f : FragFunc} {args : List WVal} {n : Nat} {o : FOut}
    (h : f.eval n args = some o) :
    ((trBodyL f).evalObs modelL (initStore f args)).run = Part.some (obsOfL o) := by
  have hr := Silmaril.Wasm.SSA.FragFunc.eval_sound h
  exact (trBodyL_run_iff hr.1 (initStore_spec f args) o).1 hr

/-! ## A divergent loop -/

theorem run_bind_of_none {α β : Type} {x : LM α} (h : x.run = Part.none) (f : α → LM β) :
    (x >>= f).run = Part.none := by
  change Part.bind x.run (ExceptT.bindCont f) = Part.none
  rw [h, Part.bind_none]

theorem run_map_of_none {α β : Type} {x : LM α} (h : x.run = Part.none) (g : α → β) :
    (g <$> x).run = Part.none := by
  rw [map_eq_pure_bind]
  exact run_bind_of_none h _

/-- `loop { br 0 }`: the body always re-enters the loop. -/
def spinBody : List Expr := [.loop none [.br 0 []]]

theorem spin_step (p : RVal × Store) :
    loopStep 0 (trSeqL 0 none [.lp 0 0] 0 [.br 0 []] (fallRL 0 none (seqVal false [.br 0 []]))) p =
      okL (.inr (RVal.unit, upd p.2 .junk p.1)) :=
  loopStep_cont rfl

theorem spin_diverges (σ : Store) :
    ((trSeqL 0 none [] 0 spinBody (retRL none 0 (seqVal false spinBody))).evalObs modelL σ).run =
      Part.none := by
  rw [evalObsL_run]
  apply run_map_of_none
  show (Silmaril.SSA.LambdaRTL.Loop.Region.evalRTL modelL (loopJoin 0 _ _) σ).run = _
  rw [evalL_loopJoin]
  apply run_bind_of_none
  rw [iterL_run, Part.eq_none_iff]
  intro y hy
  rw [Silmaril.Elgot.Part.mem_iter_iff] at hy
  generalize (RVal.unit, σ) = p at hy
  induction hy with
  | done hmem =>
    simp only [List.length_nil] at hmem
    rw [spin_step, okL_run] at hmem
    change Sum.inl _ ∈ Part.map routeE (Part.some _) at hmem
    rw [Part.map_some, Part.mem_some_iff] at hmem
    simp [routeE] at hmem
  | more _ _ ih => exact ih

end Silmaril.Proofs.Wasm.LambdaRTL
