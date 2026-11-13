module

public import Silmaril.Machine.CBackend.Behaviour.Bind.Defs
/-!
# Function contracts as refinement statements, and modular linking

A *contract* for a function with arguments `A` is a precondition and a
postcondition on observables. It denotes a behaviour set per argument
(`Contract.spec`): undefined behaviour when the precondition fails, otherwise
every observable the postcondition admits. Undefined behaviour being the top
of refinement, **"the function meets its contract" is "the function refines
its contract"** (`refines_spec_iff`, and `refines_spec_iff_hoare` for the
Hoare-triple reading). The caller's obligation (the precondition) and the
callee's guarantee (the postcondition) are thereby one refinement statement,
and every law of refinement applies to contracts.

* Footprints: `Contract.framed` adds to a state-passing contract the guarantee
  that the final state agrees with the initial one outside a footprint;
  `Contract.frame` is the frame rule.
* Modular verification: `link_refines`. Functions are given by bodies that
  denote behaviour sets *given* the behaviours of the functions they call. If
  each body refines its contract whenever its callees refine theirs, and calls
  descend along a well-founded relation on `(function, argument)` pairs, then
  every function of the linked program refines its contract. Recursion is
  allowed as long as some measure on arguments decreases.
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour

namespace Observable

/-- A function contract: a precondition on the argument and the observables
admitted when it holds. -/
structure Contract (A E V X T F : Type*) where
  pre : A → Prop
  post : A → Observable E V X T F → Prop

namespace Contract

variable {A E V X T F : Type*}

/-- The behaviour set of a contract at an argument: undefined behaviour if the
precondition fails, the postcondition otherwise. -/
def spec (c : Contract A E V X T F) (a : A) : Set (Observable E V X T F) :=
  {o | (¬ c.pre a ∧ o = ⟨[], .undefined⟩) ∨ (c.pre a ∧ c.post a o)}

theorem spec_of_pre {c : Contract A E V X T F} {a : A} (h : c.pre a) :
    c.spec a = {o | c.post a o} := by
  ext o
  simp [spec, h]

theorem spec_of_not_pre {c : Contract A E V X T F} {a : A} (h : ¬ c.pre a) :
    c.spec a = {⟨[], .undefined⟩} := by
  ext o
  simp [spec, h]

variable {x : Exhaustion}

/-- **A function meets its contract iff it refines it.** -/
theorem refines_spec_iff {c : Contract A E V X T F} {a : A} {B : Set (Observable E V X T F)} :
    Refines x B (c.spec a) ↔ (c.pre a → Refines x B {o | c.post a o}) := by
  by_cases h : c.pre a
  · rw [spec_of_pre h]
    exact ⟨fun hr _ => hr, fun hr => hr h⟩
  · refine ⟨fun _ hp => absurd hp h, fun _ => ?_⟩
    exact refines_of_undefined_nil (by rw [spec_of_not_pre h]; rfl) B

/-- The Hoare-triple reading: when the postcondition admits no undefined
behaviour, refining the contract (exhaustion forbidden) is "from the
precondition, every observable satisfies the postcondition". A
postcondition that admits divergence is partial correctness, one that
excludes it is total correctness. -/
theorem refines_spec_iff_hoare {c : Contract A E V X T F} {a : A}
    {B : Set (Observable E V X T F)} (hpost : ∀ t, ¬ c.post a ⟨t, .undefined⟩) :
    Refines .forbidden B (c.spec a) ↔ (c.pre a → ∀ o ∈ B, c.post a o) := by
  rw [refines_spec_iff]
  exact imp_congr_right fun _ => refines_iff_subset_of_safe fun t ht => hpost t ht

/-- Weakening a contract: a stronger precondition-free guarantee. `c ≤ d` when
`d` asks less of the caller and promises less. -/
def Le (c d : Contract A E V X T F) : Prop :=
  ∀ a, d.pre a → c.pre a ∧ ∀ o, c.post a o → d.post a o

theorem Le.refines {c d : Contract A E V X T F} (h : c.Le d) (a : A) :
    Refines x (c.spec a) (d.spec a) := by
  rw [refines_spec_iff]
  intro hd
  obtain ⟨hc, hpost⟩ := h a hd
  rw [spec_of_pre hc]
  exact Refines.of_subset fun o ho => hpost o ho

/-! ## Footprints and the frame rule -/

variable {L W R : Type*}

/-- A state-passing contract (`A = Arg × state`, returns `R × state`) with the
extra guarantee that a return leaves the state unchanged outside the footprint
`fp a`. -/
def framed {Arg : Type*} (c : Contract (Arg × (L → W)) E (R × (L → W)) X T F)
    (fp : Arg × (L → W) → Set L) : Contract (Arg × (L → W)) E (R × (L → W)) X T F where
  pre := c.pre
  post a o := c.post a o ∧ ∀ r s', o.ending = .returned (r, s') → ∀ l ∉ fp a, s' l = a.2 l

/-- **The frame rule.** If a function refines a framed contract, then on a safe
call each return preserves every property that depends only on the state
outside the footprint. -/
theorem frame {Arg : Type*} {c : Contract (Arg × (L → W)) E (R × (L → W)) X T F}
    {fp : Arg × (L → W) → Set L} {a : Arg × (L → W)}
    {B : Set (Observable E (R × (L → W)) X T F)}
    (h : Refines .forbidden B ((c.framed fp).spec a)) (hpre : c.pre a)
    (hsafe : ∀ t, ¬ c.post a ⟨t, .undefined⟩)
    (P : (L → W) → Prop) (hP : ∀ s s', (∀ l ∉ fp a, s' l = s l) → P s → P s')
    {o : Observable E (R × (L → W)) X T F} (ho : o ∈ B) {r : R} {s' : L → W}
    (hret : o.ending = .returned (r, s')) (hinit : P a.2) : P s' := by
  have hpost := (refines_spec_iff_hoare (c := c.framed fp)
    (fun t ht => hsafe t ht.1)).1 h hpre o ho
  exact hP a.2 s' (hpost.2 r s' hret) hinit

end Contract

/-! ## Modular verification of linked programs -/

section Link

variable {Fn A E V X T F : Type*}

/-- **Function-by-function verification composes.**

`body f env a` is the behaviour set of function `f` on argument `a` when the
functions it calls behave as `env` says; `linked` is the linked program, any
fixed point of the bodies. `dec (g, b) (f, a)` says that a call of `f` on `a`
may call `g` on `b`; it must be well founded (a call graph without cycles, or
recursion on a decreasing measure).

If each body refines its specification whenever the environment refines the
specifications of the calls it may make, then every function of the linked
program refines its specification. -/
theorem link_refines {x : Exhaustion} (dec : Fn × A → Fn × A → Prop) (wf : WellFounded dec)
    (body : Fn → (Fn → A → Set (Observable E V X T F)) → A → Set (Observable E V X T F))
    (linked : Fn → A → Set (Observable E V X T F)) (hfix : ∀ f a, linked f a = body f linked a)
    (spec : Fn → A → Set (Observable E V X T F))
    (hbody : ∀ f a env, (∀ g b, dec (g, b) (f, a) → Refines x (env g b) (spec g b)) →
      Refines x (body f env a) (spec f a)) :
    ∀ f a, Refines x (linked f a) (spec f a) := by
  have key : ∀ p : Fn × A, Refines x (linked p.1 p.2) (spec p.1 p.2) := by
    intro p
    induction p using wf.induction with
    | _ p ih =>
      rw [hfix]
      exact hbody p.1 p.2 linked fun g b h => ih (g, b) h
  exact fun f a => key (f, a)

end Link

end Observable

end Silmaril.Machine.Behaviour
