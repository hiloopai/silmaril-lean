module

public import Silmaril.Apps.Sha256sum.Process

/-! # Forward simulation gives trace refinement

Status: **VERIFIED** (no `sorry`, no new axioms).

`Sys.TraceRefines B A` (every exiting run of `B` is, call for call, an exiting run of `A`)
is what the binary targets of `Sha256sum/Plan.lean` ask for. `Sim B A E` is the usual
proof method: a relation `R b a k` between a state of `B`, a state of `A` and the kernel
state, such that

* an internal step of `B` is matched by finitely many internal steps of `A` (possibly none;
  `B`'s run is finite, so stuttering needs no measure);
* a system call of `B` is matched, after internal steps of `A`, by the same call of `A`, and
  every reply the environment admits leads to related continuations;
* an exit of `B` is matched by an exit of `A` with the same status modulo 256.

`Sim.exec` turns it into the refinement. Relating the binary (`x86Machine`) to the buffer
layer (`IOLayer.lb`) is a `Sim` whose relation says that `obuf[0, olen)` holds the layer's
buffer and `out_error` its flag.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Sys

/-- Finitely many internal steps. -/
inductive TauStar (M : Machine) : M.State → M.State → Prop
  | refl {s} : TauStar M s s
  | step {s s' t} : M.step s = .tau s' → TauStar M s' t → TauStar M s t

theorem TauStar.exec {M : Machine} {E : Env} {s t : M.State} {k : KState} {evs : List Event}
    {n : Nat} (h : TauStar M s t) (run : Exec M E t k evs n) : Exec M E s k evs n := by
  induction h with
  | refl => exact run
  | step hs _ ih => exact .tau hs (ih run)

theorem TauStar.trans {M : Machine} {s t u : M.State} (h : TauStar M s t) (h' : TauStar M t u) :
    TauStar M s u := by
  induction h with
  | refl => exact h'
  | step hs _ ih => exact .step hs (ih h')

/-- A forward simulation of `B` by `A` under `E`. -/
structure Sim (B A : Machine) (E : Env) where
  R : B.State → A.State → KState → Prop
  tau : ∀ {b b' a k}, R b a k → B.step b = .tau b' → ∃ a', TauStar A a a' ∧ R b' a' k
  call : ∀ {b c f a k}, R b a k → B.step b = .call c f →
    ∃ a1 g, TauStar A a a1 ∧ A.step a1 = .call c g ∧ ∀ r k', E k c r k' → R (f r) (g r) k'
  exit : ∀ {b n a k}, R b a k → B.step b = .exit n →
    ∃ a1 m, TauStar A a a1 ∧ A.step a1 = .exit m ∧ m % 256 = n % 256

theorem Sim.exec {B A : Machine} {E : Env} (S : Sim B A E) {b : B.State} {k : KState}
    {evs : List Event} {n : Nat} (h : Exec B E b k evs n) :
    ∀ a, S.R b a k → Exec A E a k evs n := by
  induction h with
  | @exit b k n hs =>
    intro a hr
    obtain ⟨a1, m, ht, ha, hm⟩ := S.exit hr hs
    have := ht.exec (E := E) (k := k) (Exec.exit (E := E) (k := k) ha)
    rwa [hm] at this
  | tau hs _ ih =>
    intro a hr
    obtain ⟨a', ht, hr'⟩ := S.tau hr hs
    exact ht.exec (ih a' hr')
  | call hs he _ ih =>
    intro a hr
    obtain ⟨a1, g, ht, ha, hk⟩ := S.call hr hs
    exact ht.exec (.call ha he (ih _ (hk _ _ he)))

/-- **Simulation to refinement**, with a relational loader: every initial state of `B` is
related to `A`'s initial state on the domain. -/
theorem Sim.traceRefinesRel {B A : Machine} {env : World → Env} {initB : World → B.State → Prop}
    {initA : World → A.State} {dom : World → Prop} (S : ∀ w, Sim B A (env w))
    (hinit : ∀ w, dom w → ∀ s, initB w s → (S w).R s (initA w) (KState.init w)) :
    TraceRefinesRel B A env initB initA dom :=
  fun w hw s hs _ _ run => (S w).exec run _ (hinit w hw s hs)

end Silmaril.Apps.Sha256sum.Sys
