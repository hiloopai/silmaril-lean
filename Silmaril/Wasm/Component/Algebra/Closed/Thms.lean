module

public import Silmaril.Wasm.Component.Algebra.Closed.Defs
public import Silmaril.Wasm.Component.Algebra.Ops.Thms

/-!
# Contextual equivalence through closed contexts

* **`ClosedCtxEquiv.of_compEquiv`** (the closed-context direction): denotationally equivalent
  components are equivalent in every closed context, observed at its exports. The same for
  refinement (`ClosedCtxRefines.of_compRefines`), for parametric equivalence
  (`closedCtxEquiv_of_parEquiv`) and for the full contextual equivalence
  (`ClosedCtxEquiv.of_ctxEquiv`).
* `denU_eval_closeTm`: the closing context `closeTm k` runs its hole with every import
  trapping, `((closeTm k).eval fun _ => c).denU C = trapsH ≫ c.denU C`.
* **`closedCtxEquiv_iff_of_closed`**: for components **without imports** (and with the same
  number of exports, which a closed context cannot observe) the converse holds: closed-context
  equivalence is denotational equivalence. Same for refinement.

For components with imports the converse is not claimed. A closed context supplies the
imports of the hole by core instances and nested components; whether these separate any two
strategies depends on what the core semantics `C` can compute. The conditional form
`compEquiv_of_closedCtxEquiv` takes exactly that separation property as a hypothesis
(`Separates C c c'`: if every closed context gives `c` and `c'` the same strategy, they have
the same strategy).
-/

public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- **Closed-context direction**: equivalent components are equivalent in closed contexts. -/
theorem ClosedCtxEquiv.of_compEquiv {C : CoreSem M} {c c' : Comp M} (h : CompEquiv C c c') :
    ClosedCtxEquiv C c c' :=
  fun t _ => ctxEquiv_iff.2 h t

/-- Refining components refine in closed contexts. -/
theorem ClosedCtxRefines.of_compRefines {C : CoreSem M} {c c' : Comp M}
    (h : CompRefines C c c') : ClosedCtxRefines C c c' :=
  fun t _ => ctxRefines_iff.2 h t

/-- Contextual equivalence restricts to closed contexts. -/
theorem ClosedCtxEquiv.of_ctxEquiv {C : CoreSem M} {c c' : Comp M} (h : CtxEquiv C c c') :
    ClosedCtxEquiv C c c' :=
  fun t _ => h t

/-- Parametrically equivalent components are equivalent in closed contexts, for every `C`. -/
theorem closedCtxEquiv_of_parEquiv {c c' : Comp M} (h : ParEquiv c c') (C : CoreSem M) :
    ClosedCtxEquiv C c c' :=
  ClosedCtxEquiv.of_compEquiv (h C)

omit [CoreModule M] in
/-- The closing context is closed. -/
theorem closed_closeTm (k : Nat) : (closeTm k : Tm M).Closed := rfl

/-- The strategy of a component depends on its exports only through their implementations. -/
theorem denU_mk_exports (C : CoreSem M) (I : Iface) (ns : List (Node M)) {xs ys : List Export}
    (h : xs.map Export.impl = ys.map Export.impl) :
    (Comp.mk I ns xs).denU C = (Comp.mk I ns ys).denU C := by
  simp only [Comp.denU, exportsH, h]

/-- The closing context runs its hole with every import trapping. -/
theorem denU_eval_closeTm (C : CoreSem M) {c : Comp M} {k : Nat} (hk : c.exports.length = k) :
    ((closeTm k : Tm M).eval fun _ => c).denU C =
      (Strategy.ofHandler (implsH 0 [])).comp (c.denU C) := by
  subst hk
  have hx : (reexport 0 (List.replicate c.exports.length blankExport)).map Export.impl =
      (reexport 0 c.exports).map Export.impl := by
    rw [map_impl_reexport, map_impl_reexport, List.length_replicate]
  have he : ((closeTm c.exports.length : Tm M).eval fun _ => c) =
      Comp.mk [] [.inst c []] (reexport 0 (List.replicate c.exports.length blankExport)) := rfl
  rw [he, denU_mk_exports C [] _ hx]
  exact denU_wrap C [] [] c

/-- Trapping every import of a component without imports changes nothing. -/
theorem trap_comp_denU_of_closed (C : CoreSem M) {c : Comp M} (hc : c.imports = []) :
    (Strategy.ofHandler (implsH 0 [])).comp (c.denU C) = c.denU C := by
  have h0 : implsH 0 [] = maskH c.imports.length := by
    rw [hc, List.length_nil, ← implsH_fwd 0]
    rfl
  rw [h0, maskH_comp_denU]

/-- **For components without imports and with the same number of exports, closed-context
equivalence is denotational equivalence.** (A closed context fixes how many exports of its hole
it observes, so the number of exports is a hypothesis.) -/
theorem closedCtxEquiv_iff_of_closed {C : CoreSem M} {c c' : Comp M} (hc : c.imports = [])
    (hc' : c'.imports = []) (hs : c.exports.length = c'.exports.length) :
    ClosedCtxEquiv C c c' ↔ CompEquiv C c c' := by
  refine ⟨fun h => ⟨⟨by rw [hc, hc'], hs⟩, ?_⟩, ClosedCtxEquiv.of_compEquiv⟩
  have hd := (ifaceEquiv_iff.1 (h (closeTm c.exports.length) (closed_closeTm _))).2
  rwa [denU_eval_closeTm C rfl, denU_eval_closeTm C hs.symm, trap_comp_denU_of_closed C hc,
    trap_comp_denU_of_closed C hc'] at hd

/-- **For components without imports and with the same number of exports, closed-context
refinement is refinement.** -/
theorem closedCtxRefines_iff_of_closed {C : CoreSem M} {c c' : Comp M} (hc : c.imports = [])
    (hc' : c'.imports = []) (hs : c.exports.length = c'.exports.length) :
    ClosedCtxRefines C c c' ↔ CompRefines C c c' := by
  refine ⟨fun h => ⟨⟨by rw [hc, hc'], hs⟩, ?_⟩, ClosedCtxRefines.of_compRefines⟩
  have hd := (ifaceRefines_iff.1 (h (closeTm c.exports.length) (closed_closeTm _))).2
  rwa [denU_eval_closeTm C rfl, denU_eval_closeTm C hs.symm, trap_comp_denU_of_closed C hc,
    trap_comp_denU_of_closed C hc'] at hd

/-- **Separation by closed contexts**: the closed contexts distinguish `c` from `c'` unless
they have the same strategy. This is the property of the core semantics under which the
converse of `ClosedCtxEquiv.of_compEquiv` holds; it is a hypothesis, not proved for any
`C` here. -/
def Separates (C : CoreSem M) (c c' : Comp M) : Prop :=
  SameSizes c c' →
    (∀ t : Tm M, t.Closed → ((t.eval fun _ => c).denU C = (t.eval fun _ => c').denU C)) →
      c.denU C = c'.denU C

/-- **The converse, conditionally**: if closed contexts separate `c` and `c'`, closed-context
equivalence implies denotational equivalence. -/
theorem compEquiv_of_closedCtxEquiv {C : CoreSem M} {c c' : Comp M} (hsep : Separates C c c')
    (hs : SameSizes c c') (h : ClosedCtxEquiv C c c') : CompEquiv C c c' :=
  ⟨hs, hsep hs fun t ht => (ifaceEquiv_iff.1 (h t ht)).2⟩

end Silmaril.Wasm.Component.Algebra
