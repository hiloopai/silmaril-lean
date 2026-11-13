module

public import Silmaril.Machine.CBackend.Behaviour.Refinement.Defs
/-!
# Continuations and cross-target corollaries

`Outcome.bind o k` is the set of outcomes of running a continuation `k` after a
callee with outcome `o`: a return `r` continues as `k r`; every other outcome
propagates unchanged. `Outcome.Rel.bind` shows that each mode absorbs
continuations : if the callee outcomes are related and the continuations
map related return values to related outcomes, the composite outcomes are
related in the same mode. A callee that fails to return makes both callers fail
in the corresponding way.

`Implements.cross` is the cross-target corollary: two targets
implementing one deterministic source are related through the unique source
outcome. There is no direct relation between their states.

Horizontal composition (linking two separately implemented functions through
a call) is not provided: it needs an open semantics with calls to unknown
code and an assume/guarantee treatment of the ABI.
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour

open Semantics

variable {S S₁ S₂ R R' R₁ R₂ R₂' T T' T₁ T₂ F F' F₁ F₂ : Type*}

/-- Outcomes after running a continuation on a returned value; every other
outcome propagates unchanged. -/
def Outcome.bind (o : Outcome R T F) (k : R → Outcome R₂ T F → Prop) :
    Outcome R₂ T F → Prop :=
  match o with
  | .returned r => k r
  | .trapped t => (· = .trapped t)
  | .faulted f => (· = .faulted f)
  | .undefined => (· = .undefined)
  | .exhausted => (· = .exhausted)
  | .diverges => (· = .diverges)

/-- Each mode absorbs continuations. The continuation premise `hk` relates the
continuations on related return values. `htot` is needed only under the
exhaustion relaxation, where a target that ran out of resources before the
continuation must still find a specification outcome after it. -/
theorem Outcome.Rel.bind {m : Mode} {ob : Obs R R' T T' F F'} {ob₂ : Obs R₂ R₂' T T' F F'}
    (htrap : ∀ a b, ob.trap a b → ob₂.trap a b) (hfault : ∀ a b, ob.fault a b → ob₂.fault a b)
    {k : R → Outcome R₂ T F → Prop} {k' : R' → Outcome R₂' T' F' → Prop}
    (hk : ∀ r r', ob.ret r r' → ∀ p, k r p → ∃ p', k' r' p' ∧ Outcome.Rel m ob₂ p p')
    (htot : m.exhaustion = .allowed → ∀ r', ∃ p', k' r' p')
    {o : Outcome R T F} {o' : Outcome R' T' F'} (h : Outcome.Rel m ob o o')
    {p : Outcome R₂ T F} (hp : o.bind k p) : ∃ p', o'.bind k' p' ∧ Outcome.Rel m ob₂ p p' := by
  cases o <;> cases o' <;> simp only [Outcome.Rel, Outcome.bind] at h hp ⊢
  all_goals first
    | exact hk _ _ h p hp
    | (subst hp
       exact ⟨_, rfl, by
         first | exact True.intro | exact h | exact h.imp id (htrap _ _) | exact hfault _ _ h⟩)
    | (subst hp
       obtain ⟨p', hp'⟩ := htot h _
       exact ⟨p', hp', by cases p' <;> first | exact True.intro | exact h⟩)

namespace Implements

variable {Call : Type*} {m₁ m₂ : Mode}

/-- Cross-target : two targets implementing one deterministic source are
related only through it. The two outcomes relate to the same source outcome. -/
theorem cross {src : Semantics S R T F} {tgt₁ : Semantics S₁ R₁ T₁ F₁}
    {tgt₂ : Semantics S₂ R₂ T₂ F₂} {entry : Call → S}
    {Rep₁ : Call → S₁ → Prop} {Rep₂ : Call → S₂ → Prop}
    {ob₁ : Call → S₁ → Obs R₁ R T₁ T F₁ F} {ob₂ : Call → S₂ → Obs R₂ R T₂ T F₂ F}
    (hdet : src.Deterministic)
    (h₁ : Implements m₁ src tgt₁ entry Rep₁ ob₁) (h₂ : Implements m₂ src tgt₂ entry Rep₂ ob₂)
    {c : Call} {t₁ : S₁} {t₂ : S₂} (hr₁ : Rep₁ c t₁) (hr₂ : Rep₂ c t₂)
    (hs : src.Safe (entry c)) {o₁ : Outcome R₁ T₁ F₁} {o₂ : Outcome R₂ T₂ F₂}
    (hb₁ : tgt₁.Beh t₁ o₁) (hb₂ : tgt₂.Beh t₂ o₂) :
    ∃ o, src.Beh (entry c) o ∧ Outcome.Rel m₁ (ob₁ c t₁) o₁ o ∧
      Outcome.Rel m₂ (ob₂ c t₂) o₂ o := by
  obtain ⟨o, ho, hr⟩ := h₁ c t₁ hr₁ hs o₁ hb₁
  obtain ⟨o', ho', hr'⟩ := h₂ c t₂ hr₂ hs o₂ hb₂
  rw [Beh.unique hdet ho' ho] at hr'
  exact ⟨o, ho, hr, hr'⟩

/-- The cross-target relation as a direct outcome relation, when the second
implementation's mode is symmetric (`strict` or `trapOrDiverge`, exhaustion
forbidden). -/
theorem cross_rel {src : Semantics S R T F} {tgt₁ : Semantics S₁ R₁ T₁ F₁}
    {tgt₂ : Semantics S₂ R₂ T₂ F₂} {entry : Call → S}
    {Rep₁ : Call → S₁ → Prop} {Rep₂ : Call → S₂ → Prop}
    {ob₁ : Call → S₁ → Obs R₁ R T₁ T F₁ F} {ob₂ : Call → S₂ → Obs R₂ R T₂ T F₂ F}
    (hdet : src.Deterministic) (hm₂ : m₂.failure ≠ .divergeToTrap)
    (he₂ : m₂.exhaustion = .forbidden)
    (h₁ : Implements m₁ src tgt₁ entry Rep₁ ob₁) (h₂ : Implements m₂ src tgt₂ entry Rep₂ ob₂)
    {c : Call} {t₁ : S₁} {t₂ : S₂} (hr₁ : Rep₁ c t₁) (hr₂ : Rep₂ c t₂)
    (hs : src.Safe (entry c)) {o₁ : Outcome R₁ T₁ F₁} {o₂ : Outcome R₂ T₂ F₂}
    (hb₁ : tgt₁.Beh t₁ o₁) (hb₂ : tgt₂.Beh t₂ o₂) :
    Outcome.Rel (m₁ ⊔ m₂) ((ob₁ c t₁).comp (ob₂ c t₂).flip) o₁ o₂ := by
  obtain ⟨o, -, hr, hr'⟩ := cross hdet h₁ h₂ hr₁ hr₂ hs hb₁ hb₂
  exact hr.trans (hr'.symm hm₂ he₂)

end Implements

end Silmaril.Machine.Behaviour
