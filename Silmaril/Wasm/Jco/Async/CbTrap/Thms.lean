module

public import Silmaril.Wasm.Jco.Async.CbTrap.Defs
public import Silmaril.Wasm.Jco.Async.CbRet.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.CbTrap

/-!
# A callback that goes on after its `task.return`: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.CbTrap`.

**Every body.**

* `asyncCallN_post`: the caller's view does not depend on `post`, the rest of a callback call
  after its `task.return` (it may trap or wait for ever).
* `asyncCallN_eq_asyncCall`: the caller's view is `asyncCall` (stackful) of the cut body as an
  epilogue, so the `EpiOk` results of `Async/Wait` apply (`asyncCallC_eq_asyncCall`).
* `asyncCallN_eq_atomic`: when the rest of every callback call is `EXIT`, the non-atomic and the
  atomic callback give the same caller's view.

**A callback that traps after `task.return`** (`retTrap`), when the synchronous lift is
`RM.liftFst m₀`:

* **`asyncCallN_retTrap_eq_asyncCallR`**: the caller's view is `asyncCallR` of `Split.ret post`
  (the early return of `Async/Early`), for every `post`, and **`asyncCallN_retTrap_fstIs`**: the
  caller sees `visible m₀`, `M`'s C convention;
* `retTrap_rest`: the callee then traps (`post` traps, so `NRest` has no run);
* **`asyncCallC_retTrap_atomic_noOk`**: with atomic callback calls (`Async/CbRet`), the same body
  returns no value to its caller; `earlyDrive_retTrap_atomic`: its loop only traps.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)

variable (M : CoreInst)

/-- **The caller's view does not depend on the rest of a callback call after `task.return`.** -/
theorem asyncCallN_post {L : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (b : NCbSplit M L) (post : Nat → L → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) :
    asyncCallN M R core { b with post := post } sig vs = asyncCallN M R core b sig vs := rfl

/-- The caller's view is `asyncCall` of the cut body as a stackful epilogue. -/
theorem asyncCallN_eq_asyncCall {L : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (b : NCbSplit M L) (sig : Sig) (vs : List PVal) :
    asyncCallN M R core b sig vs =
      asyncCall M R (bodyWith M core sig.result b.cut.asEpi) (AComp.noCallback M) .stackful
        sig vs :=
  asyncCallC_eq_asyncCall M R core b.cut sig vs

/-- When the rest of every callback call is `EXIT`, the cut and the atomic callback agree. -/
theorem asyncCallN_eq_atomic {L : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (b : NCbSplit M L) (hp : ∀ t l, b.post t l = pure [i32n cbExit]) (sig : Sig)
    (vs : List PVal) : asyncCallN M R core b sig vs = asyncCallC M R core b.atomic sig vs := by
  rw [asyncCallN, Silmaril.Proofs.Wasm.Jco.Async.CbTrap.cut_eq_atomic M b hp]

/-- **A callback that traps after `task.return`: the caller has continued** with the early
return of `Async/Early`. -/
theorem asyncCallN_retTrap_eq_asyncCallR (R core : List Flat → RM M.withStore.St (List Flat))
    (post : Nat → List Val → RM M.withStore.St (List Flat)) (sig : Sig) (vs : List PVal)
    (m₀ : RM M.St (Option PVal)) (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) :
    asyncCallN M R core (retTrap M) sig vs = asyncCallR M R core (Split.ret post) sig vs := by
  rw [asyncCallN, Silmaril.Proofs.Wasm.Jco.Async.CbTrap.retTrap_cut]
  exact asyncCallC_retCb_eq_asyncCallR M _ R core post sig vs m₀ hc

/-- **The caller sees `M`'s C convention**, although the callback traps afterwards. -/
theorem asyncCallN_retTrap_fstIs (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St) :
    FstIs M (asyncCallN M R core (retTrap M) sig vs) (visible M m₀ sig.result) s := by
  rw [asyncCallN, Silmaril.Proofs.Wasm.Jco.Async.CbTrap.retTrap_cut]
  exact asyncCallC_retCb_fstIs M _ R core sig vs m₀ hc s

/-- **The callee traps after the caller continued**: the rest of the callback call traps and
has no run. -/
theorem retTrap_rest (t : Nat) (l : List Val) (s s' : M.withStore.St) :
    (retTrap M).post t l s .trap ∧ ¬ NRest M (retTrap M) t l s s' :=
  ⟨rfl, fun ⟨_, _, h, _⟩ => by cases h⟩

/-- With the atomic callback of `retTrap`, the loop up to `task.return` only traps. -/
theorem earlyDrive_retTrap_atomic (t : Nat) (ws : List Val) (rs : List Flat)
    (s : M.withStore.St) (hr : (s.2.tasks t).result = none)
    {o : Out M.withStore.St (List Val × List Flat)}
    (h : EarlyDrive M ((retTrap M).atomic.cb t ws) t rs s o) : o = .trap :=
  Silmaril.Proofs.Wasm.Jco.Async.CbTrap.earlyDrive_retTrap_atomic M t ws rs s hr h

/-- **With atomic callback calls the same body returns no value.** -/
theorem asyncCallC_retTrap_atomic_noOk (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (r : Option PVal) (s' : M.withStore.St) :
    ¬ asyncCallC M R core (retTrap M).atomic sig vs s (.ok r s') :=
  Silmaril.Proofs.Wasm.Jco.Async.CbTrap.asyncCallC_retTrap_atomic_noOk M R core sig vs m₀ hc s r s'

end Silmaril.Wasm.Jco.Async

/--
info: 'Silmaril.Wasm.Jco.Async.asyncCallN_retTrap_fstIs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.asyncCallN_retTrap_fstIs

/--
info: 'Silmaril.Wasm.Jco.Async.asyncCallC_retTrap_atomic_noOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.asyncCallC_retTrap_atomic_noOk
