module

public import Silmaril.Compiler.CompilesTo.Sim.Defs

/-!
# The composition theorem: segments give the whole function

`Corr.whole_of_segments`: if every segment of a correspondence is simulated, the source and the
target are simulated end to end from every point. The proof is a well-founded induction on the
source run, which `Source.Safe` makes finite; every segment takes at least one source step.
-/

@[expose] public section

namespace Silmaril.Compiler.CompilesTo

variable {σ τ R : Type}

theorem Hop.transGen {step : σ → σ → Prop} {cut : σ → Prop} {s t : σ}
    (h : Hop step cut s t) : Relation.TransGen step s t := by
  induction h with
  | one h => exact .single h
  | more h _ _ ih => exact Relation.TransGen.head h ih

theorem Seg.transGen {step : σ → σ → Prop} {cut : σ → Prop} {s t : σ}
    (h : Seg step cut s t) : Relation.TransGen step s t :=
  h.1.transGen

/-- Safety is inherited along runs. -/
theorem Source.Safe.of_reaches {S : Source σ R} {s t : σ} (h : S.Safe s)
    (hr : Relation.ReflTransGen S.step s t) : S.Safe t := by
  refine ⟨fun u hu => h.1 u (hr.trans hu), ?_⟩
  have hacc := h.2
  induction hr with
  | refl => exact hacc
  | tail _ hstep ih => exact (ih).inv hstep

/-- Accessibility passes to the transitive closure. -/
theorem acc_transGen {α : Type} {r : α → α → Prop} {a : α} (h : Acc r a) :
    Acc (Relation.TransGen r) a := by
  induction h with
  | intro x _ ih =>
    refine Acc.intro x fun y hy => ?_
    induction hy with
    | single hyx => exact ih _ hyx
    | tail hyz hzx _ => exact (ih _ hzx).inv hyz

namespace Corr

variable (C : Corr σ τ R)

/-- **The composition theorem.** If every segment is simulated, so is every run from every
point to the function's return. -/
theorem whole_of_segments (h : ∀ k, C.Segment k) (k : Nat) : C.Whole k := by
  intro x0 s x hs hx hr hsafe
  have key : ∀ s, Acc (Relation.TransGen fun t u => C.src.step u t) s →
      ∀ k x, C.srcAt k s → C.tgtAt k x → C.rel k x0 s x → C.src.Safe s →
      ∃ t r y, Relation.ReflTransGen C.src.step s t ∧ C.src.final t r ∧
        Relation.ReflTransGen C.tgtStep x y ∧ C.tgtFinal x0 y ∧ C.result x0 r y := by
    intro s hacc
    induction hacc with
    | intro s _ ih =>
      intro k x hs hx hr hsafe
      obtain ⟨t, y, hst, hxy, hnext⟩ := h k x0 s x hs hx hr hsafe
      have hst' := hst.1
      have hxy' := hxy.transGen
      rcases hnext with ⟨j, htj, hyj, hrj⟩ | ⟨r, hfin, hyf, hres⟩
      · have hsafe' := hsafe.of_reaches hst'.to_reflTransGen
        obtain ⟨u, r, z, h1, h2, h3, h4, h5⟩ := ih t hst'.swap j y htj hyj hrj hsafe'
        exact ⟨u, r, z, hst'.to_reflTransGen.trans h1, h2, hxy'.to_reflTransGen.trans h3, h4, h5⟩
      · exact ⟨t, r, y, hst'.to_reflTransGen, hfin, hxy'.to_reflTransGen, hyf, hres⟩
  exact key s (acc_transGen hsafe.2) k x hs hx hr hsafe

end Corr

end Silmaril.Compiler.CompilesTo

end
