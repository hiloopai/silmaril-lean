module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.External
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Reflection

/-!
# Observational equivalence of lambda-SSA expressions and regions

Lambda-SSA has no equational theory, no refinement relation, and no
denotational model: it is de Bruijn, so alpha-equivalence is definitional, and
no further identifications are imposed. The only intrinsic notion of sameness
available is therefore agreement of the operational semantics at every
instruction model. Two expressions, or two regions, are observationally
equivalent when, for every atomic instruction relation, primitive-divergence
predicate, primitive-fault relation, environment and initial machine state,
they produce the same results (and, for regions, the same exit labels) with the
same final states, fault in the same final states, and diverge together.

Internal divergence is the instance of the external interface at the empty
primitive-divergence predicate, so the three components below also identify
purely internal infinite execution.

The congruences are stated for every position of every region former. Regions
are congruent in their subregions and in their expression positions; the
expression congruences are what `Tm.Obs` exists for.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u}

/-- Agreement of an expression's finite results, faults and divergences at
every instruction model over a fixed pair of value and machine-state universes. -/
structure Tm.Obs.{uu, vv, ww} {Φ : Type uu} (a a' : Tm Φ) : Prop where
  /-- The same results and final machine states are reachable. -/
  eval : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {s s' : σ} {value : Value α},
    Semantics.Tm.Eval instr env a s value s' ↔ Semantics.Tm.Eval instr env a' s value s'
  /-- The same primitive faults are reachable, with the same final states. -/
  fault : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {env : Semantics.Env α} {s s' : σ},
    Semantics.Tm.Fault instr faults env a s s' ↔ Semantics.Tm.Fault instr faults env a' s s'
  /-- Entering an explicitly divergent primitive happens in the same configurations. -/
  diverges : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {prim : Φ → Value α → σ → Prop} {env : Semantics.Env α} {s : σ},
    Semantics.Tm.ExternalDiverges instr prim env a s ↔
      Semantics.Tm.ExternalDiverges instr prim env a' s

namespace Tm.Obs

/-- Observational equivalence of expressions is reflexive. -/
theorem refl (a : Tm Φ) : Tm.Obs.{u, v, w} a a := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Observational equivalence of expressions is symmetric. -/
theorem symm {a a' : Tm Φ} (h : Tm.Obs.{u, v, w} a a') : Tm.Obs.{u, v, w} a' a :=
  ⟨h.eval.symm, h.fault.symm, h.diverges.symm⟩

/-- Observational equivalence of expressions is transitive. -/
theorem trans {a a' a'' : Tm Φ} (h : Tm.Obs.{u, v, w} a a') (h' : Tm.Obs.{u, v, w} a' a'') :
    Tm.Obs.{u, v, w} a a'' :=
  ⟨h.eval.trans h'.eval, h.fault.trans h'.fault, h.diverges.trans h'.diverges⟩

end Tm.Obs

/-- Agreement of a region's finite results, faults and divergences at every
instruction model over a fixed pair of value and machine-state universes. -/
structure Region.Obs.{uu, vv, ww} {Φ : Type uu} (r r' : Region Φ) : Prop where
  /-- The same exit labels, results and final machine states are reachable. -/
  eval : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {s s' : σ} {label : Nat} {out : Value α},
    Semantics.Region.Eval instr env r s label out s' ↔
      Semantics.Region.Eval instr env r' s label out s'
  /-- The same primitive faults are reachable, with the same final states. -/
  fault : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {env : Semantics.Env α} {s s' : σ},
    Semantics.Region.Fault instr faults env r s s' ↔
      Semantics.Region.Fault instr faults env r' s s'
  /-- Infinite execution, internal or inside an explicitly divergent primitive,
  occurs in exactly the same configurations. -/
  diverges : ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {prim : Φ → Value α → σ → Prop} {env : Semantics.Env α} {s : σ},
    Semantics.External.Diverges instr prim (.region env r s) ↔
      Semantics.External.Diverges instr prim (.region env r' s)

namespace Region.Obs

/-- Observational equivalence of regions is reflexive. -/
theorem refl (r : Region Φ) : Region.Obs.{u, v, w} r r := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Observational equivalence of regions is symmetric. -/
theorem symm {r r' : Region Φ} (h : Region.Obs.{u, v, w} r r') : Region.Obs.{u, v, w} r' r :=
  ⟨h.eval.symm, h.fault.symm, h.diverges.symm⟩

/-- Observational equivalence of regions is transitive. -/
theorem trans {r r' r'' : Region Φ} (h : Region.Obs.{u, v, w} r r')
    (h' : Region.Obs.{u, v, w} r' r'') : Region.Obs.{u, v, w} r r'' :=
  ⟨h.eval.trans h'.eval, h.fault.trans h'.fault, h.diverges.trans h'.diverges⟩

/-- Internal divergence agrees, as the instance at the empty primitive predicate. -/
theorem internalDiverges {r r' : Region Φ} (h : Region.Obs.{u, v, w} r r')
    {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {s : σ} :
    Semantics.Diverges instr (.region env r s) ↔ Semantics.Diverges instr (.region env r' s) :=
  Semantics.External.Diverges.false_iff.symm.trans
    (h.diverges.trans Semantics.External.Diverges.false_iff)

/-- Branching is a congruence in its argument. -/
theorem br (label : Nat) {a a' : Tm Φ} (h : Tm.Obs.{u, v, w} a a') :
    Region.Obs.{u, v, w} (.br label a) (.br label a') where
  eval := by
    intro α σ instr env s s' lbl out
    constructor
    · rintro run; cases run with | br arg => exact .br (h.eval.mp arg)
    · rintro run; cases run with | br arg => exact .br (h.eval.mpr arg)
  fault := by
    intro α σ instr faults env s s'
    constructor
    · rintro f; cases f with | br arg => exact .br (h.fault.mp arg)
    · rintro f; cases f with | br arg => exact .br (h.fault.mpr arg)
  diverges := by
    intro α σ instr prim env s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core
      | br div => exact .fold (.br (h.diverges.mp div))
    · intro d
      cases d.unfold with
      | core core => cases core
      | br div => exact .fold (.br (h.diverges.mpr div))

/-- Binding a result is a congruence in the bound expression and the body. -/
theorem let₁ {a a' : Tm Φ} {r r' : Region Φ} (ha : Tm.Obs.{u, v, w} a a')
    (h : Region.Obs.{u, v, w} r r') :
    Region.Obs.{u, v, w} (.let₁ a r) (.let₁ a' r') where
  eval := by
    intro α σ instr env s s' lbl out
    constructor
    · rintro run; cases run with | let₁ arg body => exact .let₁ (ha.eval.mp arg) (h.eval.mp body)
    · rintro run; cases run with | let₁ arg body => exact .let₁ (ha.eval.mpr arg) (h.eval.mpr body)
  fault := by
    intro α σ instr faults env s s'
    constructor
    · rintro f
      cases f with
      | let₁_arg arg => exact .let₁_arg (ha.fault.mp arg)
      | let₁_body arg body => exact .let₁_body (ha.eval.mp arg) (h.fault.mp body)
    · rintro f
      cases f with
      | let₁_arg arg => exact .let₁_arg (ha.fault.mpr arg)
      | let₁_body arg body => exact .let₁_body (ha.eval.mpr arg) (h.fault.mpr body)
  diverges := by
    intro α σ instr prim env s
    constructor
    · intro d
      cases d.unfold with
      | let₁_arg div => exact .fold (.let₁_arg (ha.diverges.mp div))
      | core core => cases core with
        | let₁ arg rest => exact .fold_core (.let₁ (ha.eval.mp arg) (h.diverges.mp rest))
    · intro d
      cases d.unfold with
      | let₁_arg div => exact .fold (.let₁_arg (ha.diverges.mpr div))
      | core core => cases core with
        | let₁ arg rest => exact .fold_core (.let₁ (ha.eval.mpr arg) (h.diverges.mpr rest))

/-- Splitting a pair is a congruence in the scrutinee and the body. -/
theorem let₂ {a a' : Tm Φ} {r r' : Region Φ} (ha : Tm.Obs.{u, v, w} a a')
    (h : Region.Obs.{u, v, w} r r') :
    Region.Obs.{u, v, w} (.let₂ a r) (.let₂ a' r') where
  eval := by
    intro α σ instr env s s' lbl out
    constructor
    · rintro run; cases run with | let₂ arg body => exact .let₂ (ha.eval.mp arg) (h.eval.mp body)
    · rintro run; cases run with | let₂ arg body => exact .let₂ (ha.eval.mpr arg) (h.eval.mpr body)
  fault := by
    intro α σ instr faults env s s'
    constructor
    · rintro f
      cases f with
      | let₂_arg arg => exact .let₂_arg (ha.fault.mp arg)
      | let₂_body arg body => exact .let₂_body (ha.eval.mp arg) (h.fault.mp body)
    · rintro f
      cases f with
      | let₂_arg arg => exact .let₂_arg (ha.fault.mpr arg)
      | let₂_body arg body => exact .let₂_body (ha.eval.mpr arg) (h.fault.mpr body)
  diverges := by
    intro α σ instr prim env s
    constructor
    · intro d
      cases d.unfold with
      | let₂_arg div => exact .fold (.let₂_arg (ha.diverges.mp div))
      | core core => cases core with
        | let₂ arg rest => exact .fold_core (.let₂ (ha.eval.mp arg) (h.diverges.mp rest))
    · intro d
      cases d.unfold with
      | let₂_arg div => exact .fold (.let₂_arg (ha.diverges.mpr div))
      | core core => cases core with
        | let₂ arg rest => exact .fold_core (.let₂ (ha.eval.mpr arg) (h.diverges.mpr rest))

/-- Case analysis is a congruence in the discriminant and in both branches. -/
theorem case {a a' : Tm Φ} {l l' r r' : Region Φ} (ha : Tm.Obs.{u, v, w} a a')
    (hl : Region.Obs.{u, v, w} l l') (hr : Region.Obs.{u, v, w} r r') :
    Region.Obs.{u, v, w} (.case a l r) (.case a' l' r') where
  eval := by
    intro α σ instr env s s' lbl out
    constructor
    · rintro run
      cases run with
      | case_inl arg branch => exact .case_inl (ha.eval.mp arg) (hl.eval.mp branch)
      | case_inr arg branch => exact .case_inr (ha.eval.mp arg) (hr.eval.mp branch)
    · rintro run
      cases run with
      | case_inl arg branch => exact .case_inl (ha.eval.mpr arg) (hl.eval.mpr branch)
      | case_inr arg branch => exact .case_inr (ha.eval.mpr arg) (hr.eval.mpr branch)
  fault := by
    intro α σ instr faults env s s'
    constructor
    · rintro f
      cases f with
      | case_arg arg => exact .case_arg (ha.fault.mp arg)
      | case_inl arg branch => exact .case_inl (ha.eval.mp arg) (hl.fault.mp branch)
      | case_inr arg branch => exact .case_inr (ha.eval.mp arg) (hr.fault.mp branch)
    · rintro f
      cases f with
      | case_arg arg => exact .case_arg (ha.fault.mpr arg)
      | case_inl arg branch => exact .case_inl (ha.eval.mpr arg) (hl.fault.mpr branch)
      | case_inr arg branch => exact .case_inr (ha.eval.mpr arg) (hr.fault.mpr branch)
  diverges := by
    intro α σ instr prim env s
    constructor
    · intro d
      cases d.unfold with
      | case_arg div => exact .fold (.case_arg (ha.diverges.mp div))
      | core core => cases core with
        | case_inl arg rest => exact .fold_core (.case_inl (ha.eval.mp arg) (hl.diverges.mp rest))
        | case_inr arg rest => exact .fold_core (.case_inr (ha.eval.mp arg) (hr.diverges.mp rest))
    · intro d
      cases d.unfold with
      | case_arg div => exact .fold (.case_arg (ha.diverges.mpr div))
      | core core => cases core with
        | case_inl arg rest =>
            exact .fold_core (.case_inl (ha.eval.mpr arg) (hl.diverges.mpr rest))
        | case_inr arg rest =>
            exact .fold_core (.case_inr (ha.eval.mpr arg) (hr.diverges.mpr rest))

/-- One direction of the control-flow-graph congruence for divergence. The
coinduction tracks both region and control-transfer configurations. -/
theorem cfg_diverges_of {entry entry' : Region Φ} {count : Nat}
    {blocks blocks' : Fin count → Region Φ}
    (he : Region.Obs.{u, v, w} entry entry')
    (hb : ∀ i, Region.Obs.{u, v, w} (blocks i) (blocks' i))
    {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {prim : Φ → Value α → σ → Prop} {env : Semantics.Env α} {s : σ}
    (h : Semantics.External.Diverges instr prim (.region env (.cfg entry' count blocks') s)) :
    Semantics.External.Diverges instr prim (.region env (.cfg entry count blocks) s) := by
  refine Semantics.External.Diverges.coinduct
    (fun c =>
      (∃ (e : Semantics.Env α) (t : σ), c = .region e (.cfg entry count blocks) t ∧
        Semantics.External.Diverges instr prim (.region e (.cfg entry' count blocks') t)) ∨
      (∃ (e : Semantics.Env α) (lbl : Nat) (val : Value α) (t : σ),
        c = .follow e blocks lbl val t ∧
        Semantics.External.Diverges instr prim (.follow e blocks' lbl val t)) ∨
      Semantics.External.Diverges instr prim c) ?_ (Or.inl ⟨env, s, rfl, h⟩)
  rintro c (⟨e, t, rfl, hd⟩ | ⟨e, lbl, val, t, rfl, hd⟩ | hd)
  · cases hd.unfold with
    | core core => cases core with
      | cfg_entry rest => exact .core (.cfg_entry (Or.inr (Or.inr (he.diverges.mpr rest))))
      | cfg_follow run rest =>
          exact .core (.cfg_follow (he.eval.mpr run) (Or.inr (Or.inl ⟨e, _, _, _, rfl, rest⟩)))
  · cases hd.unfold with
    | core core => cases core with
      | follow_body inside rest =>
          exact .core (.follow_body inside (Or.inr (Or.inr ((hb _).diverges.mpr rest))))
      | follow_next inside head rest =>
          exact .core (.follow_next inside ((hb _).eval.mpr head)
            (Or.inr (Or.inl ⟨e, _, _, _, rfl, rest⟩)))
  · exact hd.unfold.mono (fun _ h => Or.inr (Or.inr h))

/-- A control-flow graph is a congruence in its entry and in every block. -/
theorem cfg {entry entry' : Region Φ} {count : Nat} {blocks blocks' : Fin count → Region Φ}
    (he : Region.Obs.{u, v, w} entry entry')
    (hb : ∀ i, Region.Obs.{u, v, w} (blocks i) (blocks' i)) :
    Region.Obs.{u, v, w} (.cfg entry count blocks) (.cfg entry' count blocks') where
  eval := by
    intro α σ instr env s s' lbl out
    constructor
    · rintro run
      cases run with
      | cfg entryRun follow =>
          exact .cfg (he.eval.mp entryRun)
            (follow.map_block (fun i cur {_s _next _v _s'} run => (hb i).eval.mp run))
    · rintro run
      cases run with
      | cfg entryRun follow =>
          exact .cfg (he.eval.mpr entryRun)
            (follow.map_block (fun i cur {_s _next _v _s'} run => (hb i).eval.mpr run))
  fault := by
    intro α σ instr faults env s s'
    constructor
    · rintro f
      cases f with
      | cfg_entry fault => exact .cfg_entry (he.fault.mp fault)
      | cfg_follow run fault =>
          exact .cfg_follow (he.eval.mp run)
            (fault.map_block (fun i cur {_s _next _v _s'} run => (hb i).eval.mp run)
              (fun i cur {_s _s'} f => (hb i).fault.mp f))
    · rintro f
      cases f with
      | cfg_entry fault => exact .cfg_entry (he.fault.mpr fault)
      | cfg_follow run fault =>
          exact .cfg_follow (he.eval.mpr run)
            (fault.map_block (fun i cur {_s _next _v _s'} run => (hb i).eval.mpr run)
              (fun i cur {_s _s'} f => (hb i).fault.mpr f))
  diverges := by
    intro α σ instr prim env s
    exact ⟨cfg_diverges_of he.symm (fun i => (hb i).symm),
      cfg_diverges_of he (fun i => hb i)⟩

end Region.Obs

end Silmaril.Isotope.LambdaSSA
