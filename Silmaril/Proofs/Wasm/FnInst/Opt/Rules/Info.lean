module

public import Silmaril.Proofs.Wasm.FnInst.Opt.Rules.Basic

@[expose] public section

/-! # Information and distinction: eliminating `call 0; drop`

At the hole `callHole` (`0 → 0`, one visible function `0 : [] → [i32]`):

* over the least informative model `Env.top`, `call 0; drop` and the empty code are
  distinguished in *some* completion (the callee traps: `callDrop_distSome_top`), so they are
  not equivalent (`callDrop_not_equiv_top`);
* they are *not* distinguished in every completion (`callDrop_not_distEvery_top`: the
  completion `pureZero` makes them equal);
* over the more informative model `pureZero` (function `0` returns `0` and keeps the globals)
  they are equivalent (`callDrop_equiv_pureZero`), and no longer distinguished in some
  completion (`callDrop_not_distSome_pureZero`).

So equivalence is gained by adding information (`holds_mono` is one-directional), and
distinction in some completion is lost by adding information (`holds_distSome_anti` is
one-directional).
-/

namespace Silmaril.Proofs.Wasm.FnInst.Opt.Rules

open Silmaril.Wasm.FnInst.Opt.Rules

open Silmaril.Wasm.FnInst.Opt

theorem callHole_ft {f n m : ℕ} (hf : callHole.ft[f]? = some (n, m)) : f = 0 ∧ n = 0 ∧ m = 1 := by
  cases f with
  | zero =>
    have h : ((0, 1) : ℕ × ℕ) = (n, m) := Option.some.inj hf
    simp only [Prod.mk.injEq] at h
    exact ⟨rfl, h.1.symm, h.2.symm⟩
  | succ f => exact absurd hf (by simp [callHole])

theorem pureZero_completion : pureZero.Completion callHole.ft Env.top := by
  refine ⟨Env.le_top _, ?_, fun _ _ g => ⟨_, rfl⟩⟩
  intro f n m hf args g r g' hr
  obtain ⟨-, -, rfl⟩ := callHole_ft hf
  cases Set.mem_singleton_iff.mp hr
  rfl

/-- The only completion of `pureZero` is itself. -/
theorem completion_pureZero {ft : FTypes} {E : Env} (hE : E.Completion ft pureZero) :
    E = pureZero := by
  funext f args g
  exact (Set.Nonempty.subset_singleton_iff (hE.2.2 f args g)).mp (hE.1 f args g)

theorem step_call0 (E : Env) (st : St) :
    step callHole.ft E (.call 0) st = callOut E 0 0 st := by
  simp only [step, callHole, List.getElem?_cons_zero, Nat.zero_le, ↓reduceIte]

theorem callOut_pureZero (st : St) :
    callOut pureZero 0 0 st = {Out.ok ⟨st.locals, st.globals, 0 :: st.stack⟩} := by
  ext o
  constructor
  · rintro (⟨r, g', h, rfl⟩ | ⟨-, h⟩ | ⟨-, h⟩)
    · obtain ⟨rfl, rfl⟩ := Ans.ret.inj (Set.mem_singleton_iff.mp h)
      rfl
    · cases Set.mem_singleton_iff.mp h
    · cases Set.mem_singleton_iff.mp h
  · intro h
    rw [Set.mem_singleton_iff.mp h]
    exact Or.inl ⟨[0], st.globals, rfl, rfl⟩

theorem callDrop_runEq_pureZero : RunEq callHole.ft 0 pureZero callDropL.1 callDropR.1 := by
  intro st _
  show run _ _ [.call 0, .drop] st = run _ _ [] st
  rw [run_cons_ok ((step_call0 pureZero st).trans (callOut_pureZero st)), run_cons_ok rfl]

theorem trap_mem_callDrop (st : St) :
    Out.trap ∈ run callHole.ft Env.trapAll callDropL.1 st := by
  show Out.trap ∈ run _ _ [.call 0, .drop] st
  rw [run_cons, step_call0]
  exact Or.inr ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), rfl⟩

theorem callDrop_distSome_top : holds callHole Env.top (.distSome callDropL callDropR) := by
  refine ⟨Env.trapAll, Env.trapAll_completion _, fun h => ?_⟩
  let st : St := ⟨fun _ => 0, fun _ => 0, []⟩
  have ht : Out.trap ∈ run callHole.ft Env.trapAll callDropR.1 st :=
    h st (Nat.zero_le _) ▸ trap_mem_callDrop st
  cases ht

theorem callDrop_not_equiv_top : ¬ holds callHole Env.top (.equiv callDropL callDropR) :=
  distSome_iff_not_equiv.mp callDrop_distSome_top

theorem callDrop_not_distEvery_top : ¬ holds callHole Env.top (.distEvery callDropL callDropR) :=
  fun h => h pureZero pureZero_completion callDrop_runEq_pureZero

theorem callDrop_equiv_pureZero : holds callHole pureZero (.equiv callDropL callDropR) := by
  intro E hE
  rw [completion_pureZero hE]
  exact callDrop_runEq_pureZero

theorem callDrop_not_distSome_pureZero :
    ¬ holds callHole pureZero (.distSome callDropL callDropR) :=
  fun h => distSome_iff_not_equiv.mp h callDrop_equiv_pureZero

end Silmaril.Proofs.Wasm.FnInst.Opt.Rules
