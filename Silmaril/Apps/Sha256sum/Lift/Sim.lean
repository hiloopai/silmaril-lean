module

public import Silmaril.Apps.Sha256sum.Process

/-! # Cut-point simulation: trace refinement from per-segment verification conditions

`Sys.TraceRefinesRel B A` (every exiting run of a low-level program `B` is, call for call, an
exiting run of a high-level program `A`) is the statement that connects a binary to a
reference program. This file reduces it to **verification conditions at cut points**, the way
a Floyd-style VC generator reduces total correctness to path conditions, but for two
programs and for system calls.

The user supplies a relation `R s k a` between `B`-states, kernel states and `A`-states, meant
to hold only at the cut points of `B` (loop heads, call returns, wherever an invariant is
convenient). The VC at a cut point is `Seg … false a s k`: a *segment* of `B`'s execution
from `s`, matched against `A` from `a`, in which

* `B` makes internal steps (`tau`) — any number, each only on `B`'s side;
* `A` makes internal steps (`atau`) — stuttering on `A`'s side, any number;
* a system call of `B` is matched by the *same* call of `A` (`call`), and for **every**
  reply the environment admits, the segment continues;
* an exit of `B` is matched by the same exit of `A` (`exit`);
* a stuck `B` state ends the segment with nothing to prove (`stuck`: safety only — a stuck
  state has no exiting run);
* after at least one `B` step the segment may stop at a state related by `R` (`cut`).

The Boolean index records whether `B` has stepped yet; the VC at a cut point is the `false`
version, so every cut-to-cut segment makes progress and the induction is on the (finite)
exiting run of `B`. No measure, no determinism of `A`, and no well-foundedness argument is
needed: this is a safety (partial-correctness) rule, which is what `TraceRefines` is.

* `Seg.exec`: under the VCs, a segment that starts related turns every exiting `B` run into an
  exiting `A` run with the same events and status;
* `traceRefinesRel_of_seg`: the packaged form for `Sys.TraceRefinesRel`;
* `Seg.taus`, `Seg.ataus`: prefixing silent runs (what a block lifter produces for a
  straight-line block) onto a segment.

Nothing here mentions x86: it applies to any `Sys.Machine` pair (an x86 binary and a Lean
reference program, or two Lean programs in a refinement chain).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Sys

variable {B A : Machine}

/-- Finitely many internal steps of a machine. -/
inductive Taus (M : Machine) : M.State → M.State → Prop
  | refl {s} : Taus M s s
  | step {s s' t} : M.step s = .tau s' → Taus M s' t → Taus M s t

theorem Taus.trans {M : Machine} {s t u : M.State} (h₁ : Taus M s t) (h₂ : Taus M t u) :
    Taus M s u := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem Taus.single {M : Machine} {s t : M.State} (h : M.step s = .tau t) : Taus M s t :=
  .step h .refl

theorem Exec.of_taus {M : Machine} {E : Env} {s t : M.State} {k evs n}
    (h : Taus M s t) (he : Exec M E t k evs n) : Exec M E s k evs n := by
  induction h with
  | refl => exact he
  | step h _ ih => exact .tau h (ih he)

/-- A matched segment of `B` against `A` (see the module doc). `R` is the cut relation. -/
inductive Seg (E : Env) (R : B.State → KState → A.State → Prop) :
    Bool → A.State → B.State → KState → Prop
  | cut {a s k} : R s k a → Seg E R true a s k
  | tau {b a s s' k} : B.step s = .tau s' → Seg E R true a s' k → Seg E R b a s k
  | atau {b a a' s k} : A.step a = .tau a' → Seg E R b a' s k → Seg E R b a s k
  | call {b a s k c f g} : B.step s = .call c f → A.step a = .call c g →
      (∀ r k', E k c r k' → Seg E R true (g r) (f r) k') → Seg E R b a s k
  | exit {b a s k n} : B.step s = .exit n → A.step a = .exit n → Seg E R b a s k
  | stuck {b a s k} : B.step s = .stuck → Seg E R b a s k

variable {E : Env} {R : B.State → KState → A.State → Prop}

/-- Case analysis of a segment at one fixed `B` node, as a reusable eliminator. -/
theorem Seg.node {X : A.State → Prop} {s : B.State} {k : KState}
    (htau : ∀ s' a, B.step s = .tau s' → Seg E R true a s' k → X a)
    (hcall : ∀ c f g a, B.step s = .call c f → A.step a = .call c g →
      (∀ r k', E k c r k' → Seg E R true (g r) (f r) k') → X a)
    (hexit : ∀ n a, B.step s = .exit n → A.step a = .exit n → X a)
    (hstuck : B.step s ≠ .stuck)
    (hatau : ∀ a a', A.step a = .tau a' → X a' → X a) :
    ∀ {b a s' k'}, Seg E R b a s' k' → s' = s → k' = k →
      (b = true → ∀ a, R s k a → X a) → X a := by
  intro b a s' k' h
  induction h with
  | cut hr => intro hs hk hb; subst hs hk; exact hb rfl _ hr
  | tau hst hseg _ => intro hs hk _; subst hs hk; exact htau _ _ hst hseg
  | atau ha _ ih => intro hs hk hb; exact hatau _ _ ha (ih hs hk hb)
  | call hb ha hf _ => intro hs hk _; subst hs hk; exact hcall _ _ _ _ hb ha hf
  | exit hb ha => intro hs hk _; subst hs hk; exact hexit _ _ hb ha
  | stuck hb => intro hs hk _; subst hs hk; exact absurd hb hstuck

/-- Both passes of `Seg.node` (first the progress segment, then the one allowed to stop). -/
theorem Seg.node' {X : A.State → Prop} {s : B.State} {k : KState}
    (hR : ∀ s k a, R s k a → Seg E R false a s k)
    (htau : ∀ s' a, B.step s = .tau s' → Seg E R true a s' k → X a)
    (hcall : ∀ c f g a, B.step s = .call c f → A.step a = .call c g →
      (∀ r k', E k c r k' → Seg E R true (g r) (f r) k') → X a)
    (hexit : ∀ n a, B.step s = .exit n → A.step a = .exit n → X a)
    (hstuck : B.step s ≠ .stuck)
    (hatau : ∀ a a', A.step a = .tau a' → X a' → X a) {b a}
    (h : Seg E R b a s k) : X a :=
  Seg.node htau hcall hexit hstuck hatau h rfl rfl fun _ a hr =>
    Seg.node htau hcall hexit hstuck hatau (hR _ _ _ hr) rfl rfl (by simp)

/-- **Soundness of cut-point simulation.** If every cut-related pair has a progress segment,
every exiting run of `B` from a segment start is an exiting run of `A` with the same events
and status. -/
theorem Seg.exec (hR : ∀ s k a, R s k a → Seg E R false a s k) {s : B.State} {k evs n}
    (h : Exec B E s k evs n) : ∀ {b a}, Seg E R b a s k → Exec A E a k evs n := by
  induction h with
  | @exit s k n hs =>
    intro b a ha
    refine Seg.node' (X := fun a => Exec A E a k [] (n % 256)) hR ?_ ?_ ?_ ?_ ?_ ha
    · intro s' a h; rw [hs] at h; cases h
    · intro c f g a h; rw [hs] at h; cases h
    · intro n' a h ha; rw [hs] at h; cases h; exact .exit ha
    · rw [hs]; simp
    · intro a a' ha h; exact .tau ha h
  | @tau s s' k evs n hs _ ih =>
    intro b a ha
    refine Seg.node' (X := fun a => Exec A E a k evs n) hR ?_ ?_ ?_ ?_ ?_ ha
    · intro s'' a h hseg; rw [hs] at h; cases h; exact ih hseg
    · intro c f g a h; rw [hs] at h; cases h
    · intro n' a h; rw [hs] at h; cases h
    · rw [hs]; simp
    · intro a a' ha h; exact .tau ha h
  | @call s c f k r k' evs n hs he _ ih =>
    intro b a ha
    refine Seg.node' (X := fun a => Exec A E a k ((c, r) :: evs) n) hR ?_ ?_ ?_ ?_ ?_ ha
    · intro s'' a h; rw [hs] at h; cases h
    · intro c' f' g a h hg hf; rw [hs] at h; cases h
      exact .call hg he (ih (hf r k' he))
    · intro n' a h; rw [hs] at h; cases h
    · rw [hs]; simp
    · intro a a' ha h; exact .tau ha h

/-- **Trace refinement from cut-point VCs**, in the relational-loader form of
`Sys.TraceRefinesRel`. `R w` is the cut relation on world `w`; `start` relates every launch
state to the reference program's initial state by a segment (typically by `Seg.cut`). -/
theorem traceRefinesRel_of_seg {env : World → Env} {initB : World → B.State → Prop}
    {initA : World → A.State} {dom : World → Prop}
    (R : World → B.State → KState → A.State → Prop)
    (vc : ∀ w, dom w → ∀ s k a, R w s k a → Seg (env w) (R w) false a s k)
    (start : ∀ w, dom w → ∀ s, initB w s → ∃ b, Seg (env w) (R w) b (initA w) s (KState.init w)) :
    TraceRefinesRel B A env initB initA dom := by
  intro w hw s hs evs n run
  obtain ⟨b, hseg⟩ := start w hw s hs
  exact Seg.exec (vc w hw) run hseg

/-! ## Building segments -/

/-- A silent `B` run before a segment that may stop. -/
theorem Seg.taus_true {a s t k} (h : Taus B s t) (hseg : Seg E R true a t k) :
    Seg E R true a s k := by
  induction h with
  | refl => exact hseg
  | step h _ ih => exact .tau h (ih hseg)

/-- A nonempty silent `B` run before a segment that may stop. -/
theorem Seg.taus {b a s s' t k} (hs : B.step s = .tau s') (h : Taus B s' t)
    (hseg : Seg E R true a t k) : Seg E R b a s k :=
  .tau hs (Seg.taus_true h hseg)

/-- A silent `A` run before a segment (stuttering on the reference side). -/
theorem Seg.ataus {b a a' s k} (h : Taus A a a') (hseg : Seg E R b a' s k) : Seg E R b a s k := by
  induction h with
  | refl => exact hseg
  | step h _ ih => exact .atau h (ih hseg)

/-- One silent `B` step, then a segment that may stop. -/
theorem Seg.tau1 {b a s s' k} (h : B.step s = .tau s') (hseg : Seg E R true a s' k) :
    Seg E R b a s k := .tau h hseg

/-- Monotonicity in the environment: a segment proved for a permissive kernel holds for
every smaller one. -/
theorem Seg.mono {E' : Env} (le : Env.Le E' E) {b a s k} (h : Seg E R b a s k) :
    Seg E' R b a s k := by
  induction h with
  | cut hr => exact .cut hr
  | tau hs _ ih => exact .tau hs ih
  | atau ha _ ih => exact .atau ha ih
  | call hb ha _ ih => exact .call hb ha fun r k' he => ih r k' (le _ _ _ _ he)
  | exit hb ha => exact .exit hb ha
  | stuck hb => exact .stuck hb

/-- Weakening the cut relation. -/
theorem Seg.weaken {R' : B.State → KState → A.State → Prop} (le : ∀ s k a, R s k a → R' s k a)
    {b a s k} (h : Seg E R b a s k) : Seg E R' b a s k := by
  induction h with
  | cut hr => exact .cut (le _ _ _ hr)
  | tau hs _ ih => exact .tau hs ih
  | atau ha _ ih => exact .atau ha ih
  | call hb ha _ ih => exact .call hb ha ih
  | exit hb ha => exact .exit hb ha
  | stuck hb => exact .stuck hb

/-! ## A weakest-precondition generator for segments

`wp` computes the VC of a segment by running `B` (symbolically, when `B.step` is unfolded by
`simp`) for at most `fuel` steps: an internal step continues, or stops when the next state is
a cut point (`isCut`), where `R` must hold; a call or an exit must be matched by `A` after
finitely many silent steps of `A`; a stuck state needs nothing. `wp_seg`: the VC implies the
segment. Cut points are chosen by a Boolean test on the state (for a binary: "is `rip` one of
these addresses"), so the generator never loops at a cut. -/

section Wp

variable (E R) (isCut : B.State → Bool)

/-- The VC after one `B` step: at a cut point, the cut relation; elsewhere, more steps. -/
def wpNext (cont : B.State → KState → A.State → Prop) (s : B.State) (k : KState) (a : A.State) :
    Prop :=
  if isCut s then R s k a else cont s k a

/-- The weakest precondition of the segments of at most `fuel` steps from `s`. -/
def wp : Nat → B.State → KState → A.State → Prop
  | 0, _, _, _ => False
  | fuel + 1, s, k, a =>
    match B.step s with
    | .tau s' => wpNext R isCut (wp fuel) s' k a
    | .call c f => ∃ a' g, Taus A a a' ∧ A.step a' = .call c g ∧
        ∀ r k', E k c r k' → wpNext R isCut (wp fuel) (f r) k' (g r)
    | .exit n => ∃ a', Taus A a a' ∧ A.step a' = .exit n
    | .stuck => True

variable {E R isCut}

theorem wp_seg : ∀ {fuel s k a}, wp E R isCut fuel s k a → ∀ {b}, Seg E R b a s k
  | 0, _, _, _, h => h.elim
  | fuel + 1, s, k, a, h => by
    have next : ∀ {s' k' a'}, wpNext R isCut (wp E R isCut fuel) s' k' a' → Seg E R true a' s' k' := by
      intro s' k' a' h
      unfold wpNext at h
      split at h
      · exact .cut h
      · exact wp_seg h
    unfold wp at h
    split at h
    · rename_i s' hs; exact .tau hs (next h)
    · rename_i c f hs
      obtain ⟨a', g, ht, hg, hf⟩ := h
      exact Seg.ataus ht (.call hs hg fun r k' he => next (hf r k' he))
    · rename_i n hs
      obtain ⟨a', ht, hg⟩ := h
      exact Seg.ataus ht (.exit hs hg)
    · rename_i hs; exact .stuck hs

theorem wp_succ {fuel s k a} :
    wp E R isCut (fuel + 1) s k a ↔
      match B.step s with
      | .tau s' => wpNext R isCut (wp E R isCut fuel) s' k a
      | .call c f => ∃ a' g, Taus A a a' ∧ A.step a' = .call c g ∧
          ∀ r k', E k c r k' → wpNext R isCut (wp E R isCut fuel) (f r) k' (g r)
      | .exit n => ∃ a', Taus A a a' ∧ A.step a' = .exit n
      | .stuck => True := Iff.rfl

/-- **Trace refinement from the generated VCs**: at every cut point, `wp` for some fuel. -/
theorem traceRefinesRel_of_wp {env : World → Env} {initB : World → B.State → Prop}
    {initA : World → A.State} {dom : World → Prop}
    (R : World → B.State → KState → A.State → Prop) (isCut : World → B.State → Bool)
    (vc : ∀ w, dom w → ∀ s k a, R w s k a → ∃ fuel, wp (env w) (R w) (isCut w) fuel s k a)
    (start : ∀ w, dom w → ∀ s, initB w s → R w s (KState.init w) (initA w)) :
    TraceRefinesRel B A env initB initA dom :=
  traceRefinesRel_of_seg R
    (fun w hw s k a hr => by obtain ⟨fuel, h⟩ := vc w hw s k a hr; exact wp_seg h)
    (fun w hw s hs => ⟨true, .cut (start w hw s hs)⟩)

end Wp

end Silmaril.Apps.Sha256sum.Sys
