module

public import Silmaril.Machine.CBackend.Behaviour.Contract.Defs
/-!
# Examples for the observables core: non-vacuity and a two-function proof

* Refinement is not trivial: a different return value does not refine
  (`not_refines_other_return`); undefined behaviour after a trace allows
  only continuations of that trace (`refines_after_undefined`,
  `not_refines_other_prefix`).
* `twice_meets_contract`: a function-by-function proof. `incr` adds one to
  arguments below 10 (otherwise its contract makes the call undefined) and
  `twice` calls `incr` twice. Each body is checked against its contract
  assuming the callee meets its own (`Refines.bind`, `Contract.le` style
  reasoning), and `link_refines` concludes for the linked program.
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour.Observable.Examples

/-- Observables with natural-number events and return values. -/
abbrev Ob : Type := Observable Nat Nat Empty Empty Empty

theorem not_refines_other_return :
    ¬ Refines .allowed ({⟨[], .returned 1⟩} : Set Ob) {⟨[], .returned 0⟩} := by
  intro h
  rcases h (Set.mem_singleton _) with h | ⟨t, -, h⟩ | ⟨-, h, -⟩ <;> simp_all

theorem refines_after_undefined :
    Refines .forbidden ({⟨[1, 2], .returned 0⟩} : Set Ob) {⟨[1], .undefined⟩} := by
  rintro o rfl
  exact mem_close_of_undefined rfl ⟨[2], rfl⟩

theorem not_refines_other_prefix :
    ¬ Refines .forbidden ({⟨[2], .returned 0⟩} : Set Ob) {⟨[1], .undefined⟩} := by
  intro h
  rcases h (Set.mem_singleton _) with h | ⟨t, ht, h⟩ | ⟨h, -⟩
  · simp at h
  · simp only [Set.mem_singleton_iff, Observable.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp at ht
  · cases h

/-! ## Two functions, two contracts, one linked program -/

/-- `false` is `incr`, `true` is `twice`. -/
abbrev Fn : Type := Bool

def incrContract : Contract Nat Nat Nat Empty Empty Empty where
  pre a := a < 10
  post a o := o = ⟨[], .returned (a + 1)⟩

def twiceContract : Contract Nat Nat Nat Empty Empty Empty where
  pre a := a < 9
  post a o := o = ⟨[], .returned (a + 2)⟩

def spec : Fn → Nat → Set Ob
  | false => incrContract.spec
  | true => twiceContract.spec

/-- The bodies: `incr` returns its argument plus one; `twice` calls `incr` on
its argument and then on the result. -/
def body : Fn → (Fn → Nat → Set Ob) → Nat → Set Ob
  | false, _, a => {⟨[], .returned (a + 1)⟩}
  | true, env, a => bind (env false a) (env false)

/-- The linked program. -/
def linked : Fn → Nat → Set Ob
  | false => body false fun _ _ => ∅
  | true => body true fun f => if f then fun _ => ∅ else body false fun _ _ => ∅

theorem linked_fix (f : Fn) (a : Nat) : linked f a = body f linked a := by
  cases f <;> rfl

/-- `twice` calls `incr`, and nothing else calls anything. -/
def calls (q p : Fn × Nat) : Prop := q.1 = false ∧ p.1 = true

theorem calls_wf : WellFounded calls :=
  Subrelation.wf (r := InvImage (· < ·) fun p : Fn × Nat => if p.1 then 1 else 0)
    (fun {q p} ⟨hq, hp⟩ => by simp [InvImage, hq, hp]) (InvImage.wf _ Nat.lt_wfRel.wf)

theorem twice_meets_contract :
    ∀ f a, Refines .forbidden (linked f a) (spec f a) := by
  refine link_refines calls calls_wf body linked linked_fix spec ?_
  rintro (_ | _) a env henv
  · -- `incr` meets its contract outright.
    refine Contract.refines_spec_iff.2 fun _ => Refines.of_subset ?_
    rintro o rfl
    rfl
  · -- `twice`, assuming `incr` meets its contract.
    have hinc : ∀ b, Refines .forbidden (env false b) (incrContract.spec b) :=
      fun b => henv false b ⟨rfl, rfl⟩
    refine (Refines.bind (hinc a) hinc nofun).trans ?_
    refine Contract.refines_spec_iff.2 fun (ha : a < 9) => Refines.of_subset ?_
    rintro o ⟨o₁, h₁, ⟨v, hv, o₂, h₂, rfl⟩ | ⟨e, he, rfl⟩⟩
    · rw [Contract.spec_of_pre (show a < 10 by omega)] at h₁
      change o₁ = _ at h₁
      subst h₁
      cases hv
      rw [Contract.spec_of_pre (show a + 1 < 10 by omega)] at h₂
      change o₂ = _ at h₂
      subst h₂
      rfl
    · rw [Contract.spec_of_pre (show a < 10 by omega)] at h₁
      change o₁ = _ at h₁
      subst h₁
      cases he

end Silmaril.Machine.Behaviour.Observable.Examples
