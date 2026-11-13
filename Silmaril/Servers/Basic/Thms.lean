module

public import Silmaril.Servers.Basic.Defs

@[expose] public section

/-!
# Atomic servers: satisfaction, refinement and interface morphisms

* `Refines.sat`: refinement preserves satisfaction; `Refines.trans`.
* `sat_each_iff`: `each R` holds of `M` exactly when `M` refines `ofRel R`.
* `ofFun_refines_iff`: the server of `f` refines `ofRel R` exactly when `R q (f q)` for every
  request.
* `Hom.sat_lift_iff`: the satisfaction condition of interface morphisms.
-/

namespace Silmaril.Servers

variable {I J : Iface} {M N K : Model I} {φ : Sen I}

/-- Refinement preserves satisfaction. -/
theorem Refines.sat (h : Refines M N) (hN : Sat N φ) : Sat M φ := fun t ht => hN t (h ht)

/-- Refinement is transitive. -/
theorem Refines.trans (h : Refines M N) (h' : Refines N K) : Refines M K :=
  Set.Subset.trans h h'

/-- `each R` holds of a server exactly when it refines the loosest server of `R`. -/
theorem sat_each_iff (R : I.Req → I.Resp → Prop) : Sat M (each R) ↔ Refines M (ofRel R) :=
  Iff.rfl

/-- **Servers as functions**: the server of `f` refines `ofRel R` exactly when `f` answers
every request as `R` allows. -/
theorem ofFun_refines_iff (f : I.Req → I.Resp) (R : I.Req → I.Resp → Prop) :
    Refines (ofFun f) (ofRel R) ↔ ∀ q, R q (f q) := by
  constructor
  · intro h q
    have hm : [(q, f q)] ∈ ofFun f := by
      intro e he
      rw [List.mem_singleton.1 he]
    exact h hm (q, f q) List.mem_cons_self
  · intro h t ht e he
    rw [ht e he]
    exact h e.1

/-- **The satisfaction condition** of interface morphisms. -/
theorem Hom.sat_lift_iff (h : Hom I J) (M : Model I) (φ : Sen J) :
    Sat (h.lift M) φ ↔ Sat M (h.pull φ) := by
  constructor
  · intro hs t ht t' htt'
    exact hs t' ⟨t, ht, htt'⟩
  · rintro hs t' ⟨t, ht, htt'⟩
    exact hs t ht t' htt'

/-- Lifting preserves refinement. -/
theorem Hom.lift_mono (h : Hom I J) (hMN : Refines M N) : Refines (h.lift M) (h.lift N) := by
  rintro t' ⟨t, ht, htt'⟩
  exact ⟨t, hMN ht, htt'⟩

end Silmaril.Servers
