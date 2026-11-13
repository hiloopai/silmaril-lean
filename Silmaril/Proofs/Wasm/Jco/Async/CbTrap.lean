module

public import Silmaril.Wasm.Jco.Async.CbTrap.Defs
public import Silmaril.Wasm.Jco.Async.CbRet.Thms

/-!
# A callback that goes on after its `task.return`: proofs

Proofs of `Silmaril.Wasm.Jco.Async.CbTrap.Thms`.

* `retTrap_cut`: cut at `task.return`, the callback of `retTrap` is that of `retCb EXIT`.
* `cut_eq_atomic`: when the rest of every callback call is `EXIT`, cutting changes nothing.
* `earlyDrive_retTrap_atomic`: with the atomic callback of `retTrap`, every outcome of the loop
  up to `task.return` from a task without results is a trap.
* `asyncCallC_retTrap_atomic_noOk`: so the atomic call returns no value.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.CbTrap

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store startSync)
open Silmaril.Proofs.Wasm.Jco.Async.Frame

variable (M : CoreInst)

/-- Cut at its `task.return`, `retTrap` is `retCb EXIT`. -/
theorem retTrap_cut : (retTrap M).cut = retCb M [i32n cbExit] := by
  simp only [NCbSplit.cut, retTrap, retCb, RM.pure_bind]

/-- When the rest of every callback call is `EXIT`, the cut body is the atomic one. -/
theorem cut_eq_atomic {L : Type} (b : NCbSplit M L) (hp : ∀ t l, b.post t l = pure [i32n cbExit]) :
    b.cut = b.atomic := by
  simp only [NCbSplit.cut, NCbSplit.atomic, hp]

/-- The atomic callback of `retTrap`: `task.return`, then a trap. -/
theorem atomic_retTrap_cb (t : Nat) (ws : List Val) (a : List Flat) :
    (retTrap M).atomic.cb t ws a = (builtin M (.taskReturn t ws) >>= fun _ => RM.fail) := by
  simp only [NCbSplit.atomic, retTrap, RM.pure_bind]

/-- The atomic callback of `retTrap` returns no code. -/
theorem atomic_retTrap_cb_noOk (t : Nat) (ws : List Val) (a rs : List Flat)
    (s s₁ : M.withStore.St) : ¬ (retTrap M).atomic.cb t ws a s (.ok rs s₁) := by
  rw [atomic_retTrap_cb]
  rintro (⟨_, _, -, h⟩ | ⟨-, h⟩) <;> cases h

/-- **With the atomic callback of `retTrap`, the loop up to `task.return` only traps.** -/
theorem earlyDrive_retTrap_atomic (t : Nat) (ws : List Val) (rs : List Flat)
    (s : M.withStore.St) (hr : (s.2.tasks t).result = none)
    {o : Out M.withStore.St (List Val × List Flat)}
    (h : EarlyDrive M ((retTrap M).atomic.cb t ws) t rs s o) : o = .trap := by
  cases h with
  | ret hr₀ => rw [hr] at hr₀; cases hr₀
  | exitTrap => rfl
  | yieldOk _ _ h => exact absurd h (atomic_retTrap_cb_noOk M t ws _ _ _ _)
  | yieldTrap => rfl
  | waitOk _ _ _ h => exact absurd h (atomic_retTrap_cb_noOk M t ws _ _ _ _)
  | waitTrap => rfl
  | bad => rfl

/-- **The atomic call of `retTrap` returns no value**, when the synchronous lift is
`RM.liftFst m₀`. -/
theorem asyncCallC_retTrap_atomic_noOk (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (r : Option PVal) (s' : M.withStore.St) :
    ¬ asyncCallC M R core (retTrap M).atomic sig vs s (.ok r s') := by
  rw [Silmaril.Proofs.Wasm.Jco.Async.CbRet.asyncCallC_eq, hc, startTask_bind]
  intro h
  rcases (liftFst_bind_apply_ws M m₀ _ _ _).1 h with ⟨v, x, -, hk⟩ | ⟨-, h⟩
  · have hr : (((startSync s.2).1).tasks s.2.next).result = none := by
      simp [startSync, Silmaril.Wasm.Component.Async.upd]
    cases hv : resVals v with
    | none =>
      rw [hv, RM.ofOption_none, RM.fail_bind] at hk
      cases hk
    | some ws =>
      rw [hv, RM.ofOption_some, RM.pure_bind,
        show (retTrap M).atomic.pre = fun _ ws => pure ([i32n cbYield], ws) from rfl,
        RM.pure_bind] at hk
      rcases (RM.bind_apply _ _ _ _).1 hk with ⟨q, s'', hd, -⟩ | ⟨-, h⟩
      · cases earlyDrive_retTrap_atomic M _ ws _ (x, _) hr hd
      · cases h
  · cases h

end Silmaril.Proofs.Wasm.Jco.Async.CbTrap
