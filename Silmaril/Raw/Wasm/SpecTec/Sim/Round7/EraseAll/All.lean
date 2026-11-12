module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.StepCall

/-!
# Round 7, the whole-evaluator erasure: the induction on fuel (unrefined)

`eraseAt_zero`: with no fuel every member answers `outOfFuel` (or `false`) on both sides.
`eraseAt_succ` puts the 29 one-step theorems of `Round7/EraseAll/Step*.lean` together, and
`eraseAt` is the induction.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

variable {Q : Value → Prop} {gr gd : String → Bool} {env : Env}

theorem eraseAt_zero : EraseAt Q gr gd env 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intros; simp only [evalExp, evalExps, evalExpFields, evalArg, evalArgs, evalDoms,
        evalIterE, evalIterList, evalRounds, Sem.pathGet, Sem.matchExp, Sem.matchDefault,
        Sem.matchExps, Sem.matchExpFields, Sem.matchIterE, Sem.matchIterList, Sem.matchRounds,
        Sem.matchArg, Sem.matchArgs, Sem.callDef, Sem.tryClauses, Sem.premHolds, Sem.premsHold,
        Sem.premIter, Sem.premRounds]; exact ER.error _)
    | (intros; simp only [Sem.pathSet]; rfl)
    | (intros; simp only [Sem.patLen])
    | (intros; simp only [Sem.derives])
    | (intros; simp only [Sem.anyRule])

theorem eraseAt_succ (H : Hyps Q gr gd env) {n : Nat} (ih : EraseAt Q gr gd env n) :
    EraseAt Q gr gd env (n + 1) :=
  ⟨step_exp H ih, step_exps ih, step_expFields ih, step_arg ih, step_args ih, step_doms ih,
    step_iterE ih, step_iterList ih, step_rounds ih, step_pathGet ih, step_pathSet ih,
    step_patLen ih, step_matchExp H ih, step_matchDefault H ih, step_matchExps ih,
    step_matchExpFields ih, step_matchIterE ih, step_matchIterList ih, step_matchRounds ih,
    step_matchArg ih, step_matchArgs ih, step_callDef H ih, step_tryClauses ih,
    step_premHolds ih, step_premsHold ih, step_premIter ih, step_premRounds ih,
    step_derives H ih, step_anyRule ih⟩

/-- **The whole evaluator commutes with erasure, at every fuel.** -/
theorem eraseAt (H : Hyps Q gr gd env) : ∀ n, EraseAt Q gr gd env n
  | 0 => eraseAt_zero
  | n + 1 => eraseAt_succ H (eraseAt H n)

/-! ## Without fuel -/

theorem ER.ok_iff {α : Type} {f : α → α} {P : α → Prop} {r r' : Res α} (h : ER f P r r') {b : α} :
    r' = .ok b ↔ ∃ a, r = .ok a ∧ f a = b := by
  rw [h.1]
  cases r <;> simp [Functor.map, Except.map]

/-- **Evaluation at the erased scope is the erasure of evaluation**, and its answers are in the
swap set. -/
theorem evalExp_erase_iff (H : Hyps Q gr gd env) {ρ : VarEnv} {e : Exp} (hρ : SG Q gd ρ)
    (hx : xExp gr gd e = true) {w : Value} :
    EvalExp env (Erase.eraseScope ρ) e w ↔ ∃ v, EvalExp env ρ e v ∧ eraseV v = w := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨v, hv, rfl⟩ := ((eraseAt H n).exp ρ e hρ hx).ok_iff.1 hn
    exact ⟨v, ⟨n, hv⟩, rfl⟩
  · rintro ⟨v, ⟨n, hv⟩, rfl⟩
    exact ⟨n, ((eraseAt H n).exp ρ e hρ hx).ok_iff.2 ⟨v, hv, rfl⟩⟩

theorem allIn_of_evalExp (H : Hyps Q gr gd env) {ρ : VarEnv} {e : Exp} (hρ : SG Q gd ρ)
    (hx : xExp gr gd e = true) {v : Value} (h : EvalExp env ρ e v) : AllIn Q v := by
  obtain ⟨n, hn⟩ := h
  exact ((eraseAt H n).exp ρ e hρ hx).2 v hn

/-- **A relation of the checked part derives an erased value exactly when it derives the value.** -/
theorem derives_erase_iff (H : Hyps Q gr gd env) {x : IL.Id} {op : MixopS} {ws : List ArgV}
    {v : Value} (hx : gr x = true) (hws : ∀ w ∈ ws, ArgIn Q gd w) (hv : AllIn Q v) :
    Derives env x op (ws.map eraseA) (eraseV v) ↔ Derives env x op ws v := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (eraseAt H n).derives x op ws v hx hws hv ▸ hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, ((eraseAt H n).derives x op ws v hx hws hv).symm ▸ hn⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
