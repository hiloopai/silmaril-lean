module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Live.Lock
public import Silmaril.Wasm.FX.Asyncify.Steps.Thms

/-!
# Liveness-based save sets: results

The header of `Defs`: the handler kernel with locals `lstep P sv test`, where `sv` says what a
saved frame (a caller, a resumer, a captured suspender) keeps of its locals.

* **`lock`**: for two save functions that keep the live locals (`KeepsLive`), the two machines
  run in lock step for `CR` (frames agree on code, operands, waits and live locals);
* **`live_correct`**: keeping only the live locals (`liveSave`) gives the same behaviours as
  keeping every local (`keep`), for every program and call; **`live_steps`**: and the same step
  counts; `keepsLive_correct`: the same for every save function that keeps the live locals;
* `liveSave_det`: a saved frame depends only on the locals in the live set, so a record needs to
  store only `saveSet c n` (the live locals below `n`) and not the dead ones;
  `liveSave_dead`: the dead ones are reset;
* `live_ex`: a generator with two locals, one dead at its suspension: the saved continuation
  keeps one local of two (`saveSet [.get 0] 2 = [0]`), and both machines return `[30]`.

What this does **not** say: the kernel with locals is a new source machine, not related here to
`StepFX'` or to the strategies' target machines (`FXAsync.tstep`, `fstep`, the state machine,
CPS), which have no locals. The theorem is the strategy-independent part of the optimization:
whatever a strategy saves of a frame, saving only its live locals is enough.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Live

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify.RelSim (LockStep beh_eq_of_lock)
open Silmaril.Wasm.FX.Asyncify.Steps
open Silmaril.Proofs.Wasm.FX.Asyncify.Live (CR Agree frR_refl)

variable {V : Type}

theorem keep_keepsLive : KeepsLive (keep (V := V)) := fun _ _ _ _ => rfl

theorem liveSave_keepsLive : KeepsLive (liveSave (V := V)) :=
  fun _ _ _ h => by simp only [liveSave, h, ite_true]

/-- **Save functions that keep the live locals run in lock step.** -/
theorem lock {sv sv' : Save V} (hs : KeepsLive sv) (hs' : KeepsLive sv') (P : Prog (LIns V))
    (test : V → Bool) : LockStep CR (lstep P sv test) (lstep P sv' test) :=
  Silmaril.Proofs.Wasm.FX.Asyncify.Live.lock hs hs'

theorem init_cr (f : Nat) (args : List (SV V)) : CR (lInit f args) (lInit f args) :=
  ⟨.nil, .cons (frR_refl _) .nil⟩

/-- **Any save function that keeps the live locals preserves behaviours.** -/
theorem keepsLive_correct {sv : Save V} (hs : KeepsLive sv) (P : Prog (LIns V)) (test : V → Bool)
    (f : Nat) (args : List (SV V)) :
    beh (lstep P keep test) (lInit f args) = beh (lstep P sv test) (lInit f args) :=
  beh_eq_of_lock (lock keep_keepsLive hs P test) (init_cr f args)

/-- **Saving only the live locals preserves behaviours.** -/
theorem live_correct (P : Prog (LIns V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (lstep P keep test) (lInit f args) = beh (lstep P liveSave test) (lInit f args) :=
  keepsLive_correct liveSave_keepsLive P test f args

/-- **… with the same step counts.** -/
theorem live_steps (P : Prog (LIns V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    SameSteps (lstep P keep test) (lstep P liveSave test) (lInit f args) (lInit f args) :=
  ⟨noSlower_of_rsim (Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.rsim_of_lock
      (lock keep_keepsLive liveSave_keepsLive P test)) (init_cr f args),
    noSlower_of_rsim (Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.rsim_of_lock
      (lock liveSave_keepsLive keep_keepsLive P test)) (init_cr f args)⟩

/-- A saved frame depends only on its live locals. -/
theorem liveSave_det {c : List (LIns V)} {la lb : Locals V} (h : ∀ y, live c y = true → la y = lb y) :
    liveSave c la = liveSave c lb := by
  funext y
  cases hy : live c y with
  | true => simp only [liveSave, hy, ite_true]; exact h y hy
  | false => simp only [liveSave, hy]; rfl

theorem liveSave_dead {c : List (LIns V)} {y : Nat} (h : live c y = false) (ls : Locals V) :
    liveSave c ls y = dflt := by
  simp only [liveSave, h]; rfl

/-! ## Example -/

/-- A generator with two locals (`10`, `20`), yielding the second; after the yield only the first
is live. Its consumer adds the yielded value to the generator's result. -/
def liveP : Prog (LIns Nat)
  | 0 => some (0, [.push 10, .set 0, .push 20, .set 1, .get 1, .suspend 0 1, .get 0])
  | 1 => some (0, [.contNew 0, .resume 0 [⟨0, 2⟩]])
  | 2 => some (0, [.resume 0 [⟨0, 3⟩], .prim 2 fun vs => [vs.sum]])
  | _ => none

/-- The example's save set and runs: one local of two is saved; both machines return `[30]`. -/
theorem live_ex :
    saveSet ([.get 0] : List (LIns Nat)) 2 = [0] ∧
    runN (lstep liveP keep fun _ => true) 30 (lInit 1 []) = .stop (.done [.val 30]) ∧
    runN (lstep liveP liveSave fun _ => true) 30 (lInit 1 []) = .stop (.done [.val 30]) :=
  ⟨rfl, rfl, rfl⟩

/-- info: 'Silmaril.Wasm.FX.Asyncify.Live.live_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms live_correct

end Silmaril.Wasm.FX.Asyncify.Live
