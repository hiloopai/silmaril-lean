module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Structural
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault.Structural

/-!
# Observational equivalence of let-iter terms

The let-iter operational semantics is parameterised by an atomic instruction
relation, an explicit primitive-divergence predicate and an explicit
primitive-fault relation. Two terms are observationally equivalent when they
agree on all three for every environment and initial machine state: the same
finite results with the same final states, the same faults, and the same
infinite executions.

This is the operational counterpart of the equational theory in
`Silmaril.Isotope.LetIter.LocallyNameless.Equiv`. The two do not coincide: see
`Silmaril.Isotope.LetIter.Semantics.ObservationTheory` for the fragment of the
theory that is operationally sound and for the axioms that are not.
-/

@[expose] public section

universe u v w x

namespace Silmaril.Isotope.LetIter.LocallyNameless

open Semantics (FreeEnv BoundEnv)

variable {ν : Type x} {Φ : Type u} {n : Nat}

/-- Agreement of finite results, faults and divergences at every instruction
model over a fixed pair of value and machine-state universes. -/
structure Tm.Obs.{uu, vv, ww, xx} {ν : Type xx} {Φ : Type uu} {n : Nat}
    (a b : Tm ν Φ n) : Prop where
  /-- The same results and final machine states are reachable. -/
  eval : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {free : FreeEnv ν α} {bound : BoundEnv α n} {s s' : σ} {value : Value α},
    Semantics.Eval instr free bound a s value s' ↔ Semantics.Eval instr free bound b s value s'
  /-- The same primitive faults are reachable, with the same final states. -/
  fault : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {free : FreeEnv ν α} {bound : BoundEnv α n} {s s' : σ},
    Semantics.Fault instr faults free bound a s s' ↔
      Semantics.Fault instr faults free bound b s s'
  /-- Infinite execution, internal or inside an explicitly divergent primitive,
  occurs in exactly the same configurations. -/
  diverges : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {prim : Φ → Value α → σ → Prop} {free : FreeEnv ν α} {bound : BoundEnv α n} {s : σ},
    Semantics.External.Diverges instr free prim (.term bound a s) ↔
      Semantics.External.Diverges instr free prim (.term bound b s)

namespace Tm.Obs

/-- Observational equivalence is reflexive. -/
theorem refl (a : Tm ν Φ n) : Tm.Obs.{u, v, w, x} a a := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Observational equivalence is symmetric. -/
theorem symm {a b : Tm ν Φ n} (h : Tm.Obs.{u, v, w, x} a b) : Tm.Obs.{u, v, w, x} b a :=
  ⟨h.eval.symm, h.fault.symm, h.diverges.symm⟩

/-- Observational equivalence is transitive. -/
theorem trans {a b c : Tm ν Φ n} (h : Tm.Obs.{u, v, w, x} a b) (h' : Tm.Obs.{u, v, w, x} b c) :
    Tm.Obs.{u, v, w, x} a c :=
  ⟨h.eval.trans h'.eval, h.fault.trans h'.fault, h.diverges.trans h'.diverges⟩

/-- Internal divergence agrees, as the instance at the empty primitive predicate. -/
theorem internalDiverges {a b : Tm ν Φ n} (h : Tm.Obs.{u, v, w, x} a b)
    {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {free : FreeEnv ν α} {bound : BoundEnv α n} {s : σ} :
    Semantics.Diverges instr free (.term bound a s) ↔
      Semantics.Diverges instr free (.term bound b s) :=
  Semantics.External.Diverges.false_iff.symm.trans
    (h.diverges.trans Semantics.External.Diverges.false_iff)

/-- A primitive application is a congruence in its argument. -/
theorem op (f : Φ) {a b : Tm ν Φ n} (h : Tm.Obs.{u, v, w, x} a b) :
    Tm.Obs.{u, v, w, x} (.op f a) (.op f b) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r; cases r with | op arg step => exact .op (h.eval.mp arg) step
    · rintro r; cases r with | op arg step => exact .op (h.eval.mpr arg) step
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r
      cases r with
      | op_arg arg => exact .op_arg (h.fault.mp arg)
      | op_fault arg fault => exact .op_fault (h.eval.mp arg) fault
    · rintro r
      cases r with
      | op_arg arg => exact .op_arg (h.fault.mpr arg)
      | op_fault arg fault => exact .op_fault (h.eval.mpr arg) fault
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | primitive arg div => exact .fold (.primitive (h.eval.mp arg) div)
      | core core => cases core with | op arg => exact .fold (.core (.op (h.diverges.mp arg)))
    · intro d
      cases d.unfold with
      | primitive arg div => exact .fold (.primitive (h.eval.mpr arg) div)
      | core core => cases core with | op arg => exact .fold (.core (.op (h.diverges.mpr arg)))

/-- Sequencing is a congruence in both positions. -/
theorem let₁ {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)} (ha : Tm.Obs.{u, v, w, x} a a')
    (hb : Tm.Obs.{u, v, w, x} b b') : Tm.Obs.{u, v, w, x} (.let₁ a b) (.let₁ a' b') where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r; cases r with | let₁ arg body => exact .let₁ (ha.eval.mp arg) (hb.eval.mp body)
    · rintro r; cases r with | let₁ arg body => exact .let₁ (ha.eval.mpr arg) (hb.eval.mpr body)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r
      cases r with
      | let₁_arg arg => exact .let₁_arg (ha.fault.mp arg)
      | let₁_body arg body => exact .let₁_body (ha.eval.mp arg) (hb.fault.mp body)
    · rintro r
      cases r with
      | let₁_arg arg => exact .let₁_arg (ha.fault.mpr arg)
      | let₁_body arg body => exact .let₁_body (ha.eval.mpr arg) (hb.fault.mpr body)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold (.core (.let₁_arg (ha.diverges.mp arg)))
        | let₁_body arg body =>
            exact .fold (.core (.let₁_body (ha.eval.mp arg) (hb.diverges.mp body)))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold (.core (.let₁_arg (ha.diverges.mpr arg)))
        | let₁_body arg body =>
            exact .fold (.core (.let₁_body (ha.eval.mpr arg) (hb.diverges.mpr body)))

/-- Pairing is a congruence in both components. -/
theorem pair {a a' b b' : Tm ν Φ n} (ha : Tm.Obs.{u, v, w, x} a a')
    (hb : Tm.Obs.{u, v, w, x} b b') : Tm.Obs.{u, v, w, x} (.pair a b) (.pair a' b') where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with | pair left right => exact .pair (ha.eval.mp left) (hb.eval.mp right)
    · rintro r
      cases r with | pair left right => exact .pair (ha.eval.mpr left) (hb.eval.mpr right)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r
      cases r with
      | pair_left left => exact .pair_left (ha.fault.mp left)
      | pair_right left right => exact .pair_right (ha.eval.mp left) (hb.fault.mp right)
    · rintro r
      cases r with
      | pair_left left => exact .pair_left (ha.fault.mpr left)
      | pair_right left right => exact .pair_right (ha.eval.mpr left) (hb.fault.mpr right)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | pair_left left => exact .fold (.core (.pair_left (ha.diverges.mp left)))
        | pair_right left right =>
            exact .fold (.core (.pair_right (ha.eval.mp left) (hb.diverges.mp right)))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | pair_left left => exact .fold (.core (.pair_left (ha.diverges.mpr left)))
        | pair_right left right =>
            exact .fold (.core (.pair_right (ha.eval.mpr left) (hb.diverges.mpr right)))

/-- Pair elimination is a congruence in both positions. -/
theorem let₂ {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 2)} (ha : Tm.Obs.{u, v, w, x} a a')
    (hb : Tm.Obs.{u, v, w, x} b b') : Tm.Obs.{u, v, w, x} (.let₂ a b) (.let₂ a' b') where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r; cases r with | let₂ arg body => exact .let₂ (ha.eval.mp arg) (hb.eval.mp body)
    · rintro r; cases r with | let₂ arg body => exact .let₂ (ha.eval.mpr arg) (hb.eval.mpr body)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r
      cases r with
      | let₂_arg arg => exact .let₂_arg (ha.fault.mp arg)
      | let₂_body arg body => exact .let₂_body (ha.eval.mp arg) (hb.fault.mp body)
    · rintro r
      cases r with
      | let₂_arg arg => exact .let₂_arg (ha.fault.mpr arg)
      | let₂_body arg body => exact .let₂_body (ha.eval.mpr arg) (hb.fault.mpr body)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₂_arg arg => exact .fold (.core (.let₂_arg (ha.diverges.mp arg)))
        | let₂_body arg body =>
            exact .fold (.core (.let₂_body (ha.eval.mp arg) (hb.diverges.mp body)))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₂_arg arg => exact .fold (.core (.let₂_arg (ha.diverges.mpr arg)))
        | let₂_body arg body =>
            exact .fold (.core (.let₂_body (ha.eval.mpr arg) (hb.diverges.mpr body)))

/-- Left injection is a congruence. -/
theorem inl {a b : Tm ν Φ n} (h : Tm.Obs.{u, v, w, x} a b) :
    Tm.Obs.{u, v, w, x} (.inl a) (.inl b) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r; cases r with | inl arg => exact .inl (h.eval.mp arg)
    · rintro r; cases r with | inl arg => exact .inl (h.eval.mpr arg)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r; cases r with | inl arg => exact .inl (h.fault.mp arg)
    · rintro r; cases r with | inl arg => exact .inl (h.fault.mpr arg)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with | inl arg => exact .fold (.core (.inl (h.diverges.mp arg)))
    · intro d
      cases d.unfold with
      | core core => cases core with | inl arg => exact .fold (.core (.inl (h.diverges.mpr arg)))

/-- Right injection is a congruence. -/
theorem inr {a b : Tm ν Φ n} (h : Tm.Obs.{u, v, w, x} a b) :
    Tm.Obs.{u, v, w, x} (.inr a) (.inr b) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r; cases r with | inr arg => exact .inr (h.eval.mp arg)
    · rintro r; cases r with | inr arg => exact .inr (h.eval.mpr arg)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r; cases r with | inr arg => exact .inr (h.fault.mp arg)
    · rintro r; cases r with | inr arg => exact .inr (h.fault.mpr arg)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with | inr arg => exact .fold (.core (.inr (h.diverges.mp arg)))
    · intro d
      cases d.unfold with
      | core core => cases core with | inr arg => exact .fold (.core (.inr (h.diverges.mpr arg)))

/-- Case analysis is a congruence in the scrutinee and in both branches. -/
theorem case {e e' : Tm ν Φ n} {l l' r r' : Tm ν Φ (n + 1)} (he : Tm.Obs.{u, v, w, x} e e')
    (hl : Tm.Obs.{u, v, w, x} l l') (hr : Tm.Obs.{u, v, w, x} r r') :
    Tm.Obs.{u, v, w, x} (.case e l r) (.case e' l' r') where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro run
      cases run with
      | case_inl scrutinee branch => exact .case_inl (he.eval.mp scrutinee) (hl.eval.mp branch)
      | case_inr scrutinee branch => exact .case_inr (he.eval.mp scrutinee) (hr.eval.mp branch)
    · rintro run
      cases run with
      | case_inl scrutinee branch => exact .case_inl (he.eval.mpr scrutinee) (hl.eval.mpr branch)
      | case_inr scrutinee branch => exact .case_inr (he.eval.mpr scrutinee) (hr.eval.mpr branch)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | case_arg arg => exact .case_arg (he.fault.mp arg)
      | case_inl arg branch => exact .case_inl (he.eval.mp arg) (hl.fault.mp branch)
      | case_inr arg branch => exact .case_inr (he.eval.mp arg) (hr.fault.mp branch)
    · rintro f
      cases f with
      | case_arg arg => exact .case_arg (he.fault.mpr arg)
      | case_inl arg branch => exact .case_inl (he.eval.mpr arg) (hl.fault.mpr branch)
      | case_inr arg branch => exact .case_inr (he.eval.mpr arg) (hr.fault.mpr branch)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | case_scrutinee arg => exact .fold (.core (.case_scrutinee (he.diverges.mp arg)))
        | case_inl arg branch =>
            exact .fold (.core (.case_inl (he.eval.mp arg) (hl.diverges.mp branch)))
        | case_inr arg branch =>
            exact .fold (.core (.case_inr (he.eval.mp arg) (hr.diverges.mp branch)))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | case_scrutinee arg => exact .fold (.core (.case_scrutinee (he.diverges.mpr arg)))
        | case_inl arg branch =>
            exact .fold (.core (.case_inl (he.eval.mpr arg) (hl.diverges.mpr branch)))
        | case_inr arg branch =>
            exact .fold (.core (.case_inr (he.eval.mpr arg) (hr.diverges.mpr branch)))

/-- Empty elimination is a congruence in its argument. -/
theorem abort {a b : Tm ν Φ n} (h : Tm.Obs.{u, v, w, x} a b) :
    Tm.Obs.{u, v, w, x} (.abort a) (.abort b) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · intro r; cases r
    · intro r; cases r
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r; cases r with | abort_arg arg => exact .abort_arg (h.fault.mp arg)
    · rintro r; cases r with | abort_arg arg => exact .abort_arg (h.fault.mpr arg)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | abort arg => exact .fold (.core (.abort (h.diverges.mp arg)))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | abort arg => exact .fold (.core (.abort (h.diverges.mpr arg)))

/-- One direction of the iteration congruence for divergence: an infinite loop
on one body is an infinite loop on an observationally equivalent body. -/
theorem loop_diverges_of {b b' : Tm ν Φ (n + 1)} (hb : Tm.Obs.{u, v, w, x} b b')
    {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {prim : Φ → Value α → σ → Prop} {free : FreeEnv ν α} {bound : BoundEnv α n}
    {current : Value α} {s : σ}
    (h : Semantics.External.Diverges instr free prim (.loop bound b' current s)) :
    Semantics.External.Diverges instr free prim (.loop bound b current s) := by
  refine Semantics.External.Diverges.coinduct
    (fun c => (∃ (cur : Value α) (t : σ), c = .loop bound b cur t ∧
      Semantics.External.Diverges instr free prim (.loop bound b' cur t)) ∨
      Semantics.External.Diverges instr free prim c) ?_ (Or.inl ⟨current, s, rfl, h⟩)
  rintro c (⟨cur, t, rfl, hd⟩ | hd)
  · cases hd.unfold with
    | core core => cases core with
      | loop_body step => exact .core (.loop_body (Or.inr (hb.diverges.mpr step)))
      | loop_step head tail =>
          exact .core (.loop_step (hb.eval.mpr head) (Or.inl ⟨_, _, rfl, tail⟩))
  · exact hd.unfold.mono (fun _ h => Or.inr h)

/-- Iteration is a congruence in its initializer and in its body. -/
theorem iter {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)} (ha : Tm.Obs.{u, v, w, x} a a')
    (hb : Tm.Obs.{u, v, w, x} b b') : Tm.Obs.{u, v, w, x} (.iter a b) (.iter a' b') where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | iter init loop =>
          exact .iter (ha.eval.mp init) (loop.map_body (fun hbody => hb.eval.mp hbody))
    · rintro r
      cases r with
      | iter init loop =>
          exact .iter (ha.eval.mpr init) (loop.map_body (fun hbody => hb.eval.mpr hbody))
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r
      cases r with
      | iter_init arg => exact .iter_init (ha.fault.mp arg)
      | iter_loop arg loop =>
          exact .iter_loop (ha.eval.mp arg)
            (loop.map_body (fun hbody => hb.eval.mp hbody) (fun hbody => hb.fault.mp hbody))
    · rintro r
      cases r with
      | iter_init arg => exact .iter_init (ha.fault.mpr arg)
      | iter_loop arg loop =>
          exact .iter_loop (ha.eval.mpr arg)
            (loop.map_body (fun hbody => hb.eval.mpr hbody) (fun hbody => hb.fault.mpr hbody))
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init => exact .fold (.core (.iter_init (ha.diverges.mp init)))
        | iter_loop init loop =>
            exact .fold (.core (.iter_loop (ha.eval.mp init)
              (loop_diverges_of hb.symm loop)))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init => exact .fold (.core (.iter_init (ha.diverges.mpr init)))
        | iter_loop init loop =>
            exact .fold (.core (.iter_loop (ha.eval.mpr init) (loop_diverges_of hb loop)))

end Tm.Obs

end Silmaril.Isotope.LetIter.LocallyNameless
