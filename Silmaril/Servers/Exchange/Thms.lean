module

public import Silmaril.Servers.Exchange.Defs
public import Silmaril.Servers.Core.Thms

@[expose] public section

/-!
# Exchange servers: satisfaction, refinement, interface morphisms and the lifts to the core

* `Refines.sat`: refinement preserves satisfaction; `Refines.trans`.
* `sat_each_iff`: `each R` holds of `M` exactly when `M` refines `ofRel R`.
* `ofFun_refines_iff`: the server of `f` refines `ofRel R` exactly when `R q (f q)` for every
  request.
* `Hom.sat_lift_iff`: the satisfaction condition of interface morphisms.
* The lifts to the concurrent core: a server used sequentially is linearizable for its
  specification (`seqUse_sat_lin`); a server with a fresh instance per request that satisfies
  `each R` refines the atomic-handler server of `R` (`fresh_refines_server`), so it is
  linearizable (`fresh_sat_lin`); `ofFun f` with fresh instances refines the core's function
  server (`fresh_ofFun_refines`); both lifts preserve refinement (`seqUse_mono`, `fresh_mono`).
-/

namespace Silmaril.Servers.Exchange

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

/-! ## The lifts to the concurrent core -/

/-- Refinement of exchange servers lifts to refinement of their sequential uses. -/
theorem seqUse_mono (h : Refines M N) : (seqUse M).Refines (seqUse N) :=
  fun _ ⟨l, hn, hm, ht⟩ => ⟨l, hn, h hm, ht⟩

/-- Refinement of exchange servers lifts to refinement with fresh instances. -/
theorem fresh_mono (h : Refines M N) : (fresh M).Refines (fresh N) :=
  fun _ ⟨hw, hm⟩ => ⟨hw, fun i r s hr hs => h (hm i r s hr hs)⟩

/-- **A server used sequentially is linearizable** with respect to every specification it
satisfies. -/
theorem seqUse_sat_lin (h : Sat M φ) : (seqUse M).Sat (Sen.lin φ) := by
  rintro _ ⟨l, hn, hm, rfl⟩
  exact (Servers.Sen.lin_seq_iff l hn).2 (h _ hm)

/-- **With a fresh instance per request, `each R` gives the atomic sentence of `R`**, however
the requests overlap. -/
theorem fresh_sat_atomic {R : I.Req → I.Resp → Prop} (h : Sat M (each R)) :
    (fresh M).Sat (Servers.Sen.atomic R) :=
  fun _ ⟨_, hm⟩ i r s hr hs => h _ (hm i r s hr hs) (r, s) List.mem_cons_self

/-- **With a fresh instance per request, a server satisfying `each R` refines the
atomic-handler server of `R`.** -/
theorem fresh_refines_server {R : I.Req → I.Resp → Prop} (h : Sat M (each R)) :
    (fresh M).Refines ((Machine.ofRel R).server ()) :=
  fun t ht => (Machine.server_ofRel_tr_iff R t).2 ⟨ht.1, fresh_sat_atomic h t ht⟩

/-- With a fresh instance per request, a server satisfying `each R` is linearizable for `R`. -/
theorem fresh_sat_lin {R : I.Req → I.Resp → Prop} (h : Sat M (each R)) :
    (fresh M).Sat (Servers.Sen.lin (SeqSpec.pointwise R)) := by
  have := Servers.Model.sat_lin_of_refines_server (fresh_refines_server h)
  rwa [Machine.hist_ofRel] at this

/-- **A server refining the function `f` refines, with fresh instances, the core's function
server of `f`.** -/
theorem fresh_ofFun_refines {f : I.Req → I.Resp} (h : Refines M (ofFun f)) :
    (fresh M).Refines (Servers.Model.ofFun f) := by
  rw [Servers.Model.ofFun_eq_server]
  exact fresh_refines_server (R := fun r s => s = f r) fun t ht e he => h ht e he

end Silmaril.Servers.Exchange
