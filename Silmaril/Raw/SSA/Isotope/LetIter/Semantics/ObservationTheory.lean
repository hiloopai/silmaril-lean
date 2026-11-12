module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Observation
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.DivergenceStructural
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External.Structural
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Substitution
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Simulation
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.RawTheory

/-!
# The operationally sound fragment of the let-iter theory

`LetIter.LocallyNameless.Equiv` is sound for the Elgot-monadic denotational
model, where types constrain the values a computation can produce and the
purity predicate is interpreted. The operational semantics is untyped: `Value α`
carries no type information, a missing instruction transition is stuckness, and
`IsPure` places no constraint whatsoever on the instruction relation. Full
soundness of `Equiv` for `Tm.Obs` is therefore false, and this module says
exactly how far it goes.

`ObsTheory` is the fragment that is sound for every instruction model, with no
typing, determinism, totality or purity side condition on the model: every
congruence rule, the beta laws whose elimination is already forced by the
operational rules, the empty-initial law, the six sequencing and commuting
conversions, and all four Elgot axioms `iterBind`, `fixpoint`, `naturality` and
`codiagonal`. It also contains `letBeta` and `uniformity`, each guarded by
`Semantics.Inert` on the term being substituted.

Two things are not in `ObsTheory`, each for a stated reason.

* `letBeta` and `uniformity` at the full generality of syntactic `Pure`.
  `Semantics.Substitution` supplies the semantic substitution lemma the
  operational development was missing, and its hypotheses are what `Inert`
  discharges. They cannot be discharged by any contract on the instruction
  relation, for three independent reasons, each with a witness below: `Pure`
  admits `abort`, `let₂` and `case`, which are stuck (`not_obs_letBeta_abort`,
  which fails even for `emptyInstr`, and `emptyInstr_respectsPure`); the fault
  oracle is an independent parameter of `Tm.Obs`; and so is the
  primitive-divergence oracle. `RespectsPure` remains *necessary* for any
  instruction-level formulation, and `counterInstr_not_respectsPure` together
  with `not_obs_letBeta` is that half.
* `unitEta`, `pairEta` and `caseEta` need canonical forms, which the untyped
  value domain cannot supply; `not_obs_unitEta`, `not_obs_pairEta` and
  `not_obs_caseEta` are the separating models. `Tm.ReturnsUnit`,
  `Tm.ReturnsPair` and `Tm.ReturnsSum` name the missing hypothesis,
  `obs_unitEta_of_canonical`, `obs_pairEta_of_canonical` and
  `obs_caseEta_of_canonical` prove the three laws from it, and `ObsEtaTheory`
  is the fragment closed under them, with `ObsEtaTheory.sound`. Discharging the
  hypothesis would need a value-typing development in the style of
  `Silmaril.Isotope.LambdaSSA.Semantics.ValueTyped`.
-/

@[expose] public section

universe u v w x

namespace Silmaril.Isotope.LetIter.LocallyNameless

open Semantics (FreeEnv BoundEnv extend)

variable {ν : Type x} {Φ : Type u} {n : Nat}

/-! ## Renaming the administrative binders of the sequencing conversions -/

section Renaming

variable {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}
  {free : FreeEnv ν α} {m : Nat}

/-- The environments an inserted binder relates: index zero is untouched and
every older index skips the inserted slot. -/
theorem underBinder_agree {bound : BoundEnv α m} (inserted current : Value α) :
    ∀ i : Fin (m + 1),
      extend (extend bound inserted) current (Fin.cases 0 (fun j => j.succ.succ) i) =
        extend bound current i :=
  Fin.cases rfl (fun _ => rfl)

/-- The environments two inserted binders relate. -/
theorem underTwoBinders_agree {bound : BoundEnv α m} (inserted left right : Value α) :
    ∀ i : Fin (m + 2),
      extend (extend (extend bound inserted) left) right
        (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ)) i) =
        extend (extend bound left) right i :=
  Fin.cases rfl (Fin.cases rfl (fun _ => rfl))

/-- An inserted binder is invisible to evaluation. -/
theorem eval_underBinder_iff {bound : BoundEnv α m} {inserted current : Value α}
    {t : Tm ν Φ (m + 1)} {s s' : σ} {value : Value α} :
    Semantics.Eval instr free (extend (extend bound inserted) current) t.underBinder
        s value s' ↔
      Semantics.Eval instr free (extend bound current) t s value s' :=
  Semantics.Eval.rename_iff (underBinder_agree _ _)

/-- An inserted binder is invisible to faulting. -/
theorem fault_underBinder_iff {bound : BoundEnv α m} {inserted current : Value α}
    {t : Tm ν Φ (m + 1)} {s s' : σ} :
    Semantics.Fault instr faults free (extend (extend bound inserted) current) t.underBinder
        s s' ↔
      Semantics.Fault instr faults free (extend bound current) t s s' :=
  Semantics.Fault.rename_iff (underBinder_agree _ _)

/-- An inserted binder is invisible to divergence. -/
theorem diverges_underBinder_iff {bound : BoundEnv α m} {inserted current : Value α}
    {t : Tm ν Φ (m + 1)} {s : σ} :
    Semantics.External.Diverges instr free prim
        (.term (extend (extend bound inserted) current) t.underBinder s) ↔
      Semantics.External.Diverges instr free prim (.term (extend bound current) t s) :=
  Semantics.External.Diverges.rename_iff (underBinder_agree _ _)

/-- Two inserted binders are invisible to evaluation. -/
theorem eval_underTwoBinders_iff {bound : BoundEnv α m} {inserted left right : Value α}
    {t : Tm ν Φ (m + 2)} {s s' : σ} {value : Value α} :
    Semantics.Eval instr free (extend (extend (extend bound inserted) left) right)
        t.underTwoBinders s value s' ↔
      Semantics.Eval instr free (extend (extend bound left) right) t s value s' :=
  Semantics.Eval.rename_iff (underTwoBinders_agree _ _ _)

/-- Two inserted binders are invisible to faulting. -/
theorem fault_underTwoBinders_iff {bound : BoundEnv α m} {inserted left right : Value α}
    {t : Tm ν Φ (m + 2)} {s s' : σ} :
    Semantics.Fault instr faults free (extend (extend (extend bound inserted) left) right)
        t.underTwoBinders s s' ↔
      Semantics.Fault instr faults free (extend (extend bound left) right) t s s' :=
  Semantics.Fault.rename_iff (underTwoBinders_agree _ _ _)

/-- Two inserted binders are invisible to divergence. -/
theorem diverges_underTwoBinders_iff {bound : BoundEnv α m} {inserted left right : Value α}
    {t : Tm ν Φ (m + 2)} {s : σ} :
    Semantics.External.Diverges instr free prim
        (.term (extend (extend (extend bound inserted) left) right) t.underTwoBinders s) ↔
      Semantics.External.Diverges instr free prim
        (.term (extend (extend bound left) right) t s) :=
  Semantics.External.Diverges.rename_iff (underTwoBinders_agree _ _ _)

/-- A newest binder is invisible to a lifted term's evaluation. -/
theorem eval_lift_iff {bound : BoundEnv α m} {inserted : Value α} {t : Tm ν Φ m}
    {s s' : σ} {value : Value α} :
    Semantics.Eval instr free (extend bound inserted) t.lift s value s' ↔
      Semantics.Eval instr free bound t s value s' :=
  Semantics.Eval.rename_iff (fun _ => rfl)

/-- A newest binder is invisible to a lifted term's faults. -/
theorem fault_lift_iff {bound : BoundEnv α m} {inserted : Value α} {t : Tm ν Φ m}
    {s s' : σ} :
    Semantics.Fault instr faults free (extend bound inserted) t.lift s s' ↔
      Semantics.Fault instr faults free bound t s s' :=
  Semantics.Fault.rename_iff (fun _ => rfl)

/-- A newest binder is invisible to a lifted term's divergence. -/
theorem diverges_lift_iff {bound : BoundEnv α m} {inserted : Value α} {t : Tm ν Φ m}
    {s : σ} :
    Semantics.External.Diverges instr free prim (.term (extend bound inserted) t.lift s) ↔
      Semantics.External.Diverges instr free prim (.term bound t s) :=
  Semantics.External.Diverges.rename_iff (fun _ => rfl)

/-- An inserted binder is invisible to a loop's iterations. -/
theorem loop_underBinder_iff {bound : BoundEnv α m} {inserted current : Value α}
    {t : Tm ν Φ (m + 1)} {s s' : σ} {value : Value α} :
    Semantics.Loop instr free (extend bound inserted) t.underBinder current s value s' ↔
      Semantics.Loop instr free bound t current s value s' := by
  constructor
  · exact fun h => h.map_body (fun hb => eval_underBinder_iff.mp hb)
  · exact fun h => h.map_body (fun hb => eval_underBinder_iff.mpr hb)

/-- An inserted binder is invisible to a loop's faults. -/
theorem loopFault_underBinder_iff {bound : BoundEnv α m} {inserted current : Value α}
    {t : Tm ν Φ (m + 1)} {s s' : σ} :
    Semantics.LoopFault instr faults free (extend bound inserted) t.underBinder
        current s s' ↔
      Semantics.LoopFault instr faults free bound t current s s' := by
  constructor
  · exact fun h => h.map_body (fun hb => eval_underBinder_iff.mp hb)
      (fun hb => fault_underBinder_iff.mp hb)
  · exact fun h => h.map_body (fun hb => eval_underBinder_iff.mpr hb)
      (fun hb => fault_underBinder_iff.mpr hb)

/-- An inserted binder is invisible to a loop's divergence. -/
theorem loopDiverges_underBinder_iff {bound : BoundEnv α m} {inserted current : Value α}
    {t : Tm ν Φ (m + 1)} {s : σ} :
    Semantics.External.Diverges instr free prim
        (.loop (extend bound inserted) t.underBinder current s) ↔
      Semantics.External.Diverges instr free prim (.loop bound t current s) := by
  constructor
  · exact fun h => h.map_loop_body (fun hb => eval_underBinder_iff.mp hb)
      (fun hb => diverges_underBinder_iff.mp hb)
  · exact fun h => h.map_loop_body (fun hb => eval_underBinder_iff.mpr hb)
      (fun hb => diverges_underBinder_iff.mpr hb)

end Renaming

/-! ## Soundness of the individual axioms -/

section Axioms

variable {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
  {free : FreeEnv ν α} {m : Nat}

/-- Reading a bound variable yields its value and performs no state transition. -/
theorem eval_bv_result {bound : BoundEnv α m} {i : Fin m} {s s' : σ} {value : Value α}
    (h : Semantics.Eval instr free bound (.bv i) s value s') : value = bound i ∧ s' = s := by
  cases h; exact ⟨rfl, rfl⟩

end Axioms

/-- Returning the bound variable is the identity. -/
theorem obs_letEta (a : Tm ν Φ n) : Tm.Obs.{u, v, w, x} (.let₁ a (.bv 0)) a where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₁ arg body => obtain ⟨rfl, rfl⟩ := eval_bv_result body; exact arg
    · intro r; exact .let₁ r .bv
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r
      cases r with
      | let₁_arg arg => exact arg
      | let₁_body _ body => cases body
    · exact .let₁_arg
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact arg
        | let₁_body _ body => cases body.unfold with | core c => cases c
    · exact fun d => .fold_core (.let₁_arg d)

/-- Eliminating an explicit pair runs its components in order. -/
theorem obs_pairBeta (a b : Tm ν Φ n) (c : Tm ν Φ (n + 2)) :
    Tm.Obs.{u, v, w, x} (.let₂ (.pair a b) c) (.let₁ a (.let₁ b.lift c)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₂ arg body =>
          cases arg with
          | pair left right => exact .let₁ left (.let₁ (eval_lift_iff.mpr right) body)
    · rintro r
      cases r with
      | let₁ left rest =>
          cases rest with
          | let₁ right body => exact .let₂ (.pair left (eval_lift_iff.mp right)) body
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro r
      cases r with
      | let₂_arg arg =>
          cases arg with
          | pair_left left => exact .let₁_arg left
          | pair_right left right => exact .let₁_body left (.let₁_arg (fault_lift_iff.mpr right))
      | let₂_body arg body =>
          cases arg with
          | pair left right =>
              exact .let₁_body left (.let₁_body (eval_lift_iff.mpr right) body)
    · rintro r
      cases r with
      | let₁_arg arg => exact .let₂_arg (.pair_left arg)
      | let₁_body left rest =>
          cases rest with
          | let₁_arg arg => exact .let₂_arg (.pair_right left (fault_lift_iff.mp arg))
          | let₁_body right body =>
              exact .let₂_body (.pair left (eval_lift_iff.mp right)) body
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₂_arg arg =>
            cases arg.unfold with
            | core c => cases c with
              | pair_left left => exact .fold_core (.let₁_arg left)
              | pair_right left right =>
                  exact .fold_core (.let₁_body left
                    (.fold_core (.let₁_arg (diverges_lift_iff.mpr right))))
        | let₂_body arg body =>
            cases arg with
            | pair left right =>
                exact .fold_core (.let₁_body left
                  (.fold_core (.let₁_body (eval_lift_iff.mpr right) body)))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.let₂_arg (.fold_core (.pair_left arg)))
        | let₁_body left rest =>
            cases rest.unfold with
            | core c => cases c with
              | let₁_arg arg =>
                  exact .fold_core (.let₂_arg
                    (.fold_core (.pair_right left (diverges_lift_iff.mp arg))))
              | let₁_body right body =>
                  exact .fold_core (.let₂_body (.pair left (eval_lift_iff.mp right)) body)

/-- Case analysis on an explicit left injection takes the left branch. -/
theorem obs_caseBetaL (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.case (.inl e) l r) (.let₁ e l) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro run
      cases run with
      | case_inl scrutinee branch =>
          cases scrutinee with | inl arg => exact .let₁ arg branch
      | case_inr scrutinee _ => cases scrutinee
    · rintro run
      cases run with | let₁ arg body => exact .case_inl (.inl arg) body
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | case_arg arg => cases arg with | inl a => exact .let₁_arg a
      | case_inl scrutinee branch =>
          cases scrutinee with | inl arg => exact .let₁_body arg branch
      | case_inr scrutinee _ => cases scrutinee
    · rintro f
      cases f with
      | let₁_arg arg => exact .case_arg (.inl arg)
      | let₁_body arg body => exact .case_inl (.inl arg) body
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | case_scrutinee arg =>
            cases arg.unfold with | core c => cases c with
              | inl a => exact .fold_core (.let₁_arg a)
        | case_inl scrutinee branch =>
            cases scrutinee with | inl arg => exact .fold_core (.let₁_body arg branch)
        | case_inr scrutinee _ => cases scrutinee
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.case_scrutinee (.fold_core (.inl arg)))
        | let₁_body arg body => exact .fold_core (.case_inl (.inl arg) body)

/-- Case analysis on an explicit right injection takes the right branch. -/
theorem obs_caseBetaR (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.case (.inr e) l r) (.let₁ e r) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro run
      cases run with
      | case_inr scrutinee branch =>
          cases scrutinee with | inr arg => exact .let₁ arg branch
      | case_inl scrutinee _ => cases scrutinee
    · rintro run
      cases run with | let₁ arg body => exact .case_inr (.inr arg) body
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | case_arg arg => cases arg with | inr a => exact .let₁_arg a
      | case_inr scrutinee branch =>
          cases scrutinee with | inr arg => exact .let₁_body arg branch
      | case_inl scrutinee _ => cases scrutinee
    · rintro f
      cases f with
      | let₁_arg arg => exact .case_arg (.inr arg)
      | let₁_body arg body => exact .case_inr (.inr arg) body
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | case_scrutinee arg =>
            cases arg.unfold with | core c => cases c with
              | inr a => exact .fold_core (.let₁_arg a)
        | case_inr scrutinee branch =>
            cases scrutinee with | inr arg => exact .fold_core (.let₁_body arg branch)
        | case_inl scrutinee _ => cases scrutinee
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.case_scrutinee (.fold_core (.inr arg)))
        | let₁_body arg body => exact .fold_core (.case_inr (.inr arg) body)

/-- Nothing after an empty elimination is observable: `abort` is stuck. -/
theorem obs_emptyInitial (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.let₁ (.abort a) b) (.let₁ (.abort a) c) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r; cases r with | let₁ arg _ => cases arg
    · rintro r; cases r with | let₁ arg _ => cases arg
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | let₁_arg arg => exact .let₁_arg arg
      | let₁_body arg _ => cases arg
    · rintro f
      cases f with
      | let₁_arg arg => exact .let₁_arg arg
      | let₁_body arg _ => cases arg
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.let₁_arg arg)
        | let₁_body arg _ => cases arg
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.let₁_arg arg)
        | let₁_body arg _ => cases arg


/-! ## Soundness of the sequencing conversions -/

/-- Bind a primitive's argument before applying it. -/
theorem obs_bindOp (f : Φ) (a : Tm ν Φ n) (c : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.let₁ (.op f a) c)
      (.let₁ a (.let₁ (.op f (.bv 0)) c.underBinder)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₁ arg body =>
          cases arg with
          | op inner step => exact .let₁ inner (.let₁ (.op .bv step) (eval_underBinder_iff.mpr body))
    · rintro r
      cases r with
      | let₁ inner rest =>
          cases rest with
          | let₁ arg body =>
              cases arg with
              | op bv step =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .let₁ (.op inner step) (eval_underBinder_iff.mp body)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro fl
      cases fl with
      | let₁_arg arg =>
          cases arg with
          | op_arg inner => exact .let₁_arg inner
          | op_fault inner fault => exact .let₁_body inner (.let₁_arg (.op_fault .bv fault))
      | let₁_body arg body =>
          cases arg with
          | op inner step =>
              exact .let₁_body inner
                (.let₁_body (.op .bv step) (fault_underBinder_iff.mpr body))
    · rintro fl
      cases fl with
      | let₁_arg arg => exact .let₁_arg (.op_arg arg)
      | let₁_body inner rest =>
          cases rest with
          | let₁_arg arg =>
              cases arg with
              | op_arg bv => cases bv
              | op_fault bv fault =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .let₁_arg (.op_fault inner fault)
          | let₁_body arg body =>
              cases arg with
              | op bv step =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .let₁_body (.op inner step) (fault_underBinder_iff.mp body)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg =>
            cases arg.unfold with
            | core c => cases c with
              | op inner => exact .fold_core (.let₁_arg inner)
            | primitive inner div =>
                exact .fold_core (.let₁_body inner
                  (.fold_core (.let₁_arg (.fold (.primitive .bv div)))))
        | let₁_body arg body =>
            cases arg with
            | op inner step =>
                exact .fold_core (.let₁_body inner
                  (.fold_core (.let₁_body (.op .bv step) (diverges_underBinder_iff.mpr body))))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.let₁_arg (.fold_core (.op arg)))
        | let₁_body inner rest =>
            cases rest.unfold with
            | core c => cases c with
              | let₁_arg arg =>
                  cases arg.unfold with
                  | core c₂ => cases c₂ with | op bv => cases bv.unfold with | core c₃ => cases c₃
                  | primitive bv div =>
                      obtain ⟨hv, hs⟩ := eval_bv_result bv
                      simp only [Semantics.extend_zero] at hv
                      subst hv; subst hs
                      exact .fold_core (.let₁_arg (.fold (.primitive inner div)))
              | let₁_body arg body =>
                  cases arg with
                  | op bv step =>
                      obtain ⟨hv, hs⟩ := eval_bv_result bv
                      simp only [Semantics.extend_zero] at hv
                      subst hv; subst hs
                      exact .fold_core (.let₁_body (.op inner step)
                        (diverges_underBinder_iff.mp body))

/-- Sequencing is associative. -/
theorem obs_bindLet (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.let₁ (.let₁ a b) c) (.let₁ a (.let₁ b c.underBinder)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₁ arg body =>
          cases arg with
          | let₁ inner mid => exact .let₁ inner (.let₁ mid (eval_underBinder_iff.mpr body))
    · rintro r
      cases r with
      | let₁ inner rest =>
          cases rest with
          | let₁ mid body => exact .let₁ (.let₁ inner mid) (eval_underBinder_iff.mp body)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro fl
      cases fl with
      | let₁_arg arg =>
          cases arg with
          | let₁_arg inner => exact .let₁_arg inner
          | let₁_body inner mid => exact .let₁_body inner (.let₁_arg mid)
      | let₁_body arg body =>
          cases arg with
          | let₁ inner mid =>
              exact .let₁_body inner (.let₁_body mid (fault_underBinder_iff.mpr body))
    · rintro fl
      cases fl with
      | let₁_arg arg => exact .let₁_arg (.let₁_arg arg)
      | let₁_body inner rest =>
          cases rest with
          | let₁_arg arg => exact .let₁_arg (.let₁_body inner arg)
          | let₁_body mid body =>
              exact .let₁_body (.let₁ inner mid) (fault_underBinder_iff.mp body)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg =>
            cases arg.unfold with
            | core c => cases c with
              | let₁_arg inner => exact .fold_core (.let₁_arg inner)
              | let₁_body inner mid =>
                  exact .fold_core (.let₁_body inner (.fold_core (.let₁_arg mid)))
        | let₁_body arg body =>
            cases arg with
            | let₁ inner mid =>
                exact .fold_core (.let₁_body inner
                  (.fold_core (.let₁_body mid (diverges_underBinder_iff.mpr body))))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.let₁_arg (.fold_core (.let₁_arg arg)))
        | let₁_body inner rest =>
            cases rest.unfold with
            | core c => cases c with
              | let₁_arg arg => exact .fold_core (.let₁_arg (.fold_core (.let₁_body inner arg)))
              | let₁_body mid body =>
                  exact .fold_core (.let₁_body (.let₁ inner mid)
                    (diverges_underBinder_iff.mp body))

/-- Pair elimination commutes with a following binding. -/
theorem obs_bindLetPair (e : Tm ν Φ n) (c : Tm ν Φ (n + 2)) (d : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.let₁ (.let₂ e c) d)
      (.let₂ e (.let₁ c d.underBinder.underBinder)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₁ arg body =>
          cases arg with
          | let₂ inner mid =>
              exact .let₂ inner (.let₁ mid
                (eval_underBinder_iff.mpr (eval_underBinder_iff.mpr body)))
    · rintro r
      cases r with
      | let₂ inner rest =>
          cases rest with
          | let₁ mid body =>
              exact .let₁ (.let₂ inner mid)
                (eval_underBinder_iff.mp (eval_underBinder_iff.mp body))
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro fl
      cases fl with
      | let₁_arg arg =>
          cases arg with
          | let₂_arg inner => exact .let₂_arg inner
          | let₂_body inner mid => exact .let₂_body inner (.let₁_arg mid)
      | let₁_body arg body =>
          cases arg with
          | let₂ inner mid =>
              exact .let₂_body inner (.let₁_body mid
                (fault_underBinder_iff.mpr (fault_underBinder_iff.mpr body)))
    · rintro fl
      cases fl with
      | let₂_arg arg => exact .let₁_arg (.let₂_arg arg)
      | let₂_body inner rest =>
          cases rest with
          | let₁_arg arg => exact .let₁_arg (.let₂_body inner arg)
          | let₁_body mid body =>
              exact .let₁_body (.let₂ inner mid)
                (fault_underBinder_iff.mp (fault_underBinder_iff.mp body))
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg =>
            cases arg.unfold with
            | core c => cases c with
              | let₂_arg inner => exact .fold_core (.let₂_arg inner)
              | let₂_body inner mid =>
                  exact .fold_core (.let₂_body inner (.fold_core (.let₁_arg mid)))
        | let₁_body arg body =>
            cases arg with
            | let₂ inner mid =>
                exact .fold_core (.let₂_body inner (.fold_core (.let₁_body mid
                  (diverges_underBinder_iff.mpr (diverges_underBinder_iff.mpr body)))))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₂_arg arg => exact .fold_core (.let₁_arg (.fold_core (.let₂_arg arg)))
        | let₂_body inner rest =>
            cases rest.unfold with
            | core c => cases c with
              | let₁_arg arg => exact .fold_core (.let₁_arg (.fold_core (.let₂_body inner arg)))
              | let₁_body mid body =>
                  exact .fold_core (.let₁_body (.let₂ inner mid)
                    (diverges_underBinder_iff.mp (diverges_underBinder_iff.mp body)))

/-- Case analysis commutes with a following binding. -/
theorem obs_bindLetCase (e : Tm ν Φ n) (l r d : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.let₁ (.case e l r) d)
      (.case e (.let₁ l d.underBinder) (.let₁ r d.underBinder)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro run
      cases run with
      | let₁ arg body =>
          cases arg with
          | case_inl scrutinee branch =>
              exact .case_inl scrutinee (.let₁ branch (eval_underBinder_iff.mpr body))
          | case_inr scrutinee branch =>
              exact .case_inr scrutinee (.let₁ branch (eval_underBinder_iff.mpr body))
    · rintro run
      cases run with
      | case_inl scrutinee rest =>
          cases rest with
          | let₁ branch body =>
              exact .let₁ (.case_inl scrutinee branch) (eval_underBinder_iff.mp body)
      | case_inr scrutinee rest =>
          cases rest with
          | let₁ branch body =>
              exact .let₁ (.case_inr scrutinee branch) (eval_underBinder_iff.mp body)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro fl
      cases fl with
      | let₁_arg arg =>
          cases arg with
          | case_arg inner => exact .case_arg inner
          | case_inl scrutinee branch => exact .case_inl scrutinee (.let₁_arg branch)
          | case_inr scrutinee branch => exact .case_inr scrutinee (.let₁_arg branch)
      | let₁_body arg body =>
          cases arg with
          | case_inl scrutinee branch =>
              exact .case_inl scrutinee (.let₁_body branch (fault_underBinder_iff.mpr body))
          | case_inr scrutinee branch =>
              exact .case_inr scrutinee (.let₁_body branch (fault_underBinder_iff.mpr body))
    · rintro fl
      cases fl with
      | case_arg arg => exact .let₁_arg (.case_arg arg)
      | case_inl scrutinee rest =>
          cases rest with
          | let₁_arg arg => exact .let₁_arg (.case_inl scrutinee arg)
          | let₁_body branch body =>
              exact .let₁_body (.case_inl scrutinee branch) (fault_underBinder_iff.mp body)
      | case_inr scrutinee rest =>
          cases rest with
          | let₁_arg arg => exact .let₁_arg (.case_inr scrutinee arg)
          | let₁_body branch body =>
              exact .let₁_body (.case_inr scrutinee branch) (fault_underBinder_iff.mp body)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg =>
            cases arg.unfold with
            | core c => cases c with
              | case_scrutinee inner => exact .fold_core (.case_scrutinee inner)
              | case_inl scrutinee branch =>
                  exact .fold_core (.case_inl scrutinee (.fold_core (.let₁_arg branch)))
              | case_inr scrutinee branch =>
                  exact .fold_core (.case_inr scrutinee (.fold_core (.let₁_arg branch)))
        | let₁_body arg body =>
            cases arg with
            | case_inl scrutinee branch =>
                exact .fold_core (.case_inl scrutinee (.fold_core (.let₁_body branch
                  (diverges_underBinder_iff.mpr body))))
            | case_inr scrutinee branch =>
                exact .fold_core (.case_inr scrutinee (.fold_core (.let₁_body branch
                  (diverges_underBinder_iff.mpr body))))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | case_scrutinee arg => exact .fold_core (.let₁_arg (.fold_core (.case_scrutinee arg)))
        | case_inl scrutinee rest =>
            cases rest.unfold with
            | core c => cases c with
              | let₁_arg arg =>
                  exact .fold_core (.let₁_arg (.fold_core (.case_inl scrutinee arg)))
              | let₁_body branch body =>
                  exact .fold_core (.let₁_body (.case_inl scrutinee branch)
                    (diverges_underBinder_iff.mp body))
        | case_inr scrutinee rest =>
            cases rest.unfold with
            | core c => cases c with
              | let₁_arg arg =>
                  exact .fold_core (.let₁_arg (.fold_core (.case_inr scrutinee arg)))
              | let₁_body branch body =>
                  exact .fold_core (.let₁_body (.case_inr scrutinee branch)
                    (diverges_underBinder_iff.mp body))

/-- Bind the scrutinee of a pair elimination. -/
theorem obs_bindPair (a : Tm ν Φ n) (c : Tm ν Φ (n + 2)) :
    Tm.Obs.{u, v, w, x} (.let₂ a c) (.let₁ a (.let₂ (.bv 0) c.underTwoBinders)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₂ arg body => exact .let₁ arg (.let₂ .bv (eval_underTwoBinders_iff.mpr body))
    · rintro r
      cases r with
      | let₁ arg rest =>
          cases rest with
          | let₂ bv body =>
              obtain ⟨hv, hs⟩ := eval_bv_result bv
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .let₂ arg (eval_underTwoBinders_iff.mp body)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro fl
      cases fl with
      | let₂_arg arg => exact .let₁_arg arg
      | let₂_body arg body =>
          exact .let₁_body arg (.let₂_body .bv (fault_underTwoBinders_iff.mpr body))
    · rintro fl
      cases fl with
      | let₁_arg arg => exact .let₂_arg arg
      | let₁_body arg rest =>
          cases rest with
          | let₂_arg bv => cases bv
          | let₂_body bv body =>
              obtain ⟨hv, hs⟩ := eval_bv_result bv
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .let₂_body arg (fault_underTwoBinders_iff.mp body)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₂_arg arg => exact .fold_core (.let₁_arg arg)
        | let₂_body arg body =>
            exact .fold_core (.let₁_body arg
              (.fold_core (.let₂_body .bv (diverges_underTwoBinders_iff.mpr body))))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.let₂_arg arg)
        | let₁_body arg rest =>
            cases rest.unfold with
            | core c => cases c with
              | let₂_arg bv => cases bv.unfold with | core c₂ => cases c₂
              | let₂_body bv body =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .fold_core (.let₂_body arg (diverges_underTwoBinders_iff.mp body))

/-- Bind the scrutinee of a case analysis. -/
theorem obs_bindCase (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.case e l r)
      (.let₁ e (.case (.bv 0) l.underBinder r.underBinder)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro run
      cases run with
      | case_inl scrutinee branch =>
          exact .let₁ scrutinee (.case_inl .bv (eval_underBinder_iff.mpr branch))
      | case_inr scrutinee branch =>
          exact .let₁ scrutinee (.case_inr .bv (eval_underBinder_iff.mpr branch))
    · rintro run
      cases run with
      | let₁ scrutinee rest =>
          cases rest with
          | case_inl bv branch =>
              obtain ⟨hv, hs⟩ := eval_bv_result bv
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .case_inl scrutinee (eval_underBinder_iff.mp branch)
          | case_inr bv branch =>
              obtain ⟨hv, hs⟩ := eval_bv_result bv
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .case_inr scrutinee (eval_underBinder_iff.mp branch)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro fl
      cases fl with
      | case_arg arg => exact .let₁_arg arg
      | case_inl scrutinee branch =>
          exact .let₁_body scrutinee (.case_inl .bv (fault_underBinder_iff.mpr branch))
      | case_inr scrutinee branch =>
          exact .let₁_body scrutinee (.case_inr .bv (fault_underBinder_iff.mpr branch))
    · rintro fl
      cases fl with
      | let₁_arg arg => exact .case_arg arg
      | let₁_body scrutinee rest =>
          cases rest with
          | case_arg bv => cases bv
          | case_inl bv branch =>
              obtain ⟨hv, hs⟩ := eval_bv_result bv
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .case_inl scrutinee (fault_underBinder_iff.mp branch)
          | case_inr bv branch =>
              obtain ⟨hv, hs⟩ := eval_bv_result bv
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .case_inr scrutinee (fault_underBinder_iff.mp branch)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | case_scrutinee arg => exact .fold_core (.let₁_arg arg)
        | case_inl scrutinee branch =>
            exact .fold_core (.let₁_body scrutinee
              (.fold_core (.case_inl .bv (diverges_underBinder_iff.mpr branch))))
        | case_inr scrutinee branch =>
            exact .fold_core (.let₁_body scrutinee
              (.fold_core (.case_inr .bv (diverges_underBinder_iff.mpr branch))))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.case_scrutinee arg)
        | let₁_body scrutinee rest =>
            cases rest.unfold with
            | core c => cases c with
              | case_scrutinee bv => cases bv.unfold with | core c₂ => cases c₂
              | case_inl bv branch =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .fold_core (.case_inl scrutinee (diverges_underBinder_iff.mp branch))
              | case_inr bv branch =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .fold_core (.case_inr scrutinee (diverges_underBinder_iff.mp branch))


/-! ## Soundness of the two one-step Elgot axioms -/

/-- Elgot iteration binding: the initializer runs exactly once, up front. -/
theorem obs_iterBind (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.iter a b) (.let₁ a (.iter (.bv 0) b.underBinder)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | iter init loop => exact .let₁ init (.iter .bv (loop_underBinder_iff.mpr loop))
    · rintro r
      cases r with
      | let₁ init rest =>
          cases rest with
          | iter bv loop =>
              obtain ⟨hv, hs⟩ := eval_bv_result bv
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .iter init (loop_underBinder_iff.mp loop)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro fl
      cases fl with
      | iter_init arg => exact .let₁_arg arg
      | iter_loop arg loop =>
          exact .let₁_body arg (.iter_loop .bv (loopFault_underBinder_iff.mpr loop))
    · rintro fl
      cases fl with
      | let₁_arg arg => exact .iter_init arg
      | let₁_body arg rest =>
          cases rest with
          | iter_init bv => cases bv
          | iter_loop bv loop =>
              obtain ⟨hv, hs⟩ := eval_bv_result bv
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .iter_loop arg (loopFault_underBinder_iff.mp loop)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init => exact .fold_core (.let₁_arg init)
        | iter_loop init loop =>
            exact .fold_core (.let₁_body init
              (.fold_core (.iter_loop .bv (loopDiverges_underBinder_iff.mpr loop))))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.iter_init arg)
        | let₁_body init rest =>
            cases rest.unfold with
            | core c => cases c with
              | iter_init bv => cases bv.unfold with | core c₂ => cases c₂
              | iter_loop bv loop =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .fold_core (.iter_loop init (loopDiverges_underBinder_iff.mp loop))

/-- Elgot fixpoint: unfold one iteration step. -/
theorem obs_fixpoint (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.iter a b)
      (.let₁ a (.case b (.bv 0) (.iter (.bv 0) b.underBinder.underBinder))) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | iter init loop =>
          cases loop with
          | done step => exact .let₁ init (.case_inl step .bv)
          | step head tail =>
              exact .let₁ init (.case_inr head (.iter .bv
                (loop_underBinder_iff.mpr (loop_underBinder_iff.mpr tail))))
    · rintro r
      cases r with
      | let₁ init rest =>
          cases rest with
          | case_inl scrutinee branch =>
              obtain ⟨hv, hs⟩ := eval_bv_result branch
              simp only [Semantics.extend_zero] at hv
              subst hv; subst hs
              exact .iter init (.done scrutinee)
          | case_inr scrutinee rest' =>
              cases rest' with
              | iter bv loop =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .iter init (.step scrutinee
                    (loop_underBinder_iff.mp (loop_underBinder_iff.mp loop)))
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro fl
      cases fl with
      | iter_init arg => exact .let₁_arg arg
      | iter_loop arg loop =>
          cases loop with
          | body fault => exact .let₁_body arg (.case_arg fault)
          | step head tail =>
              exact .let₁_body arg (.case_inr head (.iter_loop .bv
                (loopFault_underBinder_iff.mpr (loopFault_underBinder_iff.mpr tail))))
    · rintro fl
      cases fl with
      | let₁_arg arg => exact .iter_init arg
      | let₁_body arg rest =>
          cases rest with
          | case_arg f => exact .iter_loop arg (.body f)
          | case_inl _ branch => cases branch
          | case_inr scrutinee rest' =>
              cases rest' with
              | iter_init bv => cases bv
              | iter_loop bv loop =>
                  obtain ⟨hv, hs⟩ := eval_bv_result bv
                  simp only [Semantics.extend_zero] at hv
                  subst hv; subst hs
                  exact .iter_loop arg (.step scrutinee
                    (loopFault_underBinder_iff.mp (loopFault_underBinder_iff.mp loop)))
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init => exact .fold_core (.let₁_arg init)
        | iter_loop init loop =>
            cases loop.unfold with
            | core c => cases c with
              | loop_body body =>
                  exact .fold_core (.let₁_body init (.fold_core (.case_scrutinee body)))
              | loop_step head tail =>
                  exact .fold_core (.let₁_body init (.fold_core (.case_inr head
                    (.fold_core (.iter_loop .bv (loopDiverges_underBinder_iff.mpr
                      (loopDiverges_underBinder_iff.mpr tail)))))))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact .fold_core (.iter_init arg)
        | let₁_body init rest =>
            cases rest.unfold with
            | core c => cases c with
              | case_scrutinee body =>
                  exact .fold_core (.iter_loop init (.fold_core (.loop_body body)))
              | case_inl _ branch => cases branch.unfold with | core c₂ => cases c₂
              | case_inr scrutinee rest' =>
                  cases rest'.unfold with
                  | core c₂ => cases c₂ with
                    | iter_init bv => cases bv.unfold with | core c₃ => cases c₃
                    | iter_loop bv loop =>
                        obtain ⟨hv, hs⟩ := eval_bv_result bv
                        simp only [Semantics.extend_zero] at hv
                        subst hv; subst hs
                        exact .fold_core (.iter_loop init (.fold_core (.loop_step scrutinee
                          (loopDiverges_underBinder_iff.mp
                            (loopDiverges_underBinder_iff.mp loop)))))


/-! ## Opening a binder: `letBeta`

`letBeta` substitutes a syntactically `Pure` term under a binder. Syntactic
purity is not enough operationally, and no contract on the instruction relation
can make it enough: `Pure` admits `abort`, `let₂` and `case`, which are *stuck*
on the wrong value, and `Tm.Obs` quantifies over the fault oracle and the
primitive-divergence oracle independently of `instr`, so a pure opcode may
still be declared faulting or divergent. `not_obs_letBeta_abort` below is the
corresponding separating model; it uses the *empty* instruction relation, which
satisfies `RespectsPure` vacuously.

`Silmaril.Isotope.LetIter.Semantics.Inert` is the class of terms that discharge
the hypotheses of the substitution lemma in every model: no instruction
application and no elimination form. On that class `letBeta` holds with no side
condition on the model at all. -/

/-- **Pure-let beta** for a substituend that is already a value: binding it and
substituting it are observationally the same. -/
theorem obs_letBeta (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) (ha : Semantics.Inert a) :
    Tm.Obs.{u, v, w, x} (.let₁ a b) (b.instantiate a) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₁ arg body =>
          obtain ⟨rfl, rfl⟩ := ha.unique arg
          exact (Semantics.Eval.instantiate_iff ha).mpr body
    · intro r
      exact .let₁ (ha.eval s) ((Semantics.Eval.instantiate_iff ha).mp r)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | let₁_arg arg => exact absurd arg ha.not_fault
      | let₁_body arg body =>
          obtain ⟨rfl, rfl⟩ := ha.unique arg
          exact (Semantics.Fault.instantiate_iff ha).mpr body
    · intro f
      exact .let₁_body (ha.eval s) ((Semantics.Fault.instantiate_iff ha).mp f)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact absurd arg ha.not_diverges
        | let₁_body arg body =>
            obtain ⟨rfl, rfl⟩ := ha.unique arg
            exact (Semantics.External.Diverges.instantiate_iff ha).mpr body
    · intro d
      exact .fold_core (.let₁_body (ha.eval s)
        ((Semantics.External.Diverges.instantiate_iff ha).mp d))

/-! ## The uniformity square -/

section Uniformity

variable {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}
  {free : FreeEnv ν α} {m : Nat} {bound : BoundEnv α m} {h b b' : Tm ν Φ (m + 1)}

/-- The value the pure map of a uniformity square sends a loop state to. -/
def uniformMap {α : Type v} (free : FreeEnv ν α) {m : Nat} (bound : BoundEnv α m)
    (h : Tm ν Φ (m + 1)) (z : Value α) : Value α :=
  Semantics.inertValue free (extend bound z) h

/-- The right-hand side of the uniformity square runs `b'` at the image state. -/
theorem uniformity_rhs_eval_iff (hh : Semantics.Inert h) {z value : Value α} {s s' : σ} :
    Semantics.Eval instr free (extend bound z) (Tm.instantiate b'.underBinder h) s value s' ↔
      Semantics.Eval instr free (extend bound (uniformMap free bound h z)) b' s value s' :=
  (Semantics.Eval.instantiate_iff hh).trans eval_underBinder_iff

/-- The right-hand side of the uniformity square faults exactly when `b'` does
at the image state. -/
theorem uniformity_rhs_fault_iff (hh : Semantics.Inert h) {z : Value α} {s s' : σ} :
    Semantics.Fault instr faults free (extend bound z)
        (Tm.instantiate b'.underBinder h) s s' ↔
      Semantics.Fault instr faults free (extend bound (uniformMap free bound h z)) b' s s' :=
  (Semantics.Fault.instantiate_iff hh).trans fault_underBinder_iff

/-- The right-hand side of the uniformity square diverges exactly when `b'`
does at the image state. -/
theorem uniformity_rhs_diverges_iff (hh : Semantics.Inert h) {z : Value α} {s : σ} :
    Semantics.External.Diverges instr free prim
        (.term (extend bound z) (Tm.instantiate b'.underBinder h) s) ↔
      Semantics.External.Diverges instr free prim
        (.term (extend bound (uniformMap free bound h z)) b' s) :=
  (Semantics.External.Diverges.instantiate_iff hh).trans diverges_underBinder_iff

/-- The left-hand side of the uniformity square exits exactly when `b` does,
with the same payload. -/
theorem uniformity_lhs_exit_iff {z out : Value α} {s s' : σ} :
    Semantics.Eval instr free (extend bound z)
        (.case b (.inl (.bv 0)) (.inr h.underBinder)) s (.inl out) s' ↔
      Semantics.Eval instr free (extend bound z) b s (.inl out) s' := by
  constructor
  · rintro r
    cases r with
    | case_inl scrutinee branch =>
        cases branch with
        | inl arg => obtain ⟨rfl, rfl⟩ := eval_bv_result arg; exact scrutinee
    | case_inr _ branch => cases branch
  · exact fun r => .case_inl r (.inl .bv)

/-- The left-hand side of the uniformity square continues exactly when `b`
does, with the continuation state pushed through the pure map. -/
theorem uniformity_lhs_cont_iff (hh : Semantics.Inert h) {z next : Value α} {s s' : σ} :
    Semantics.Eval instr free (extend bound z)
        (.case b (.inl (.bv 0)) (.inr h.underBinder)) s (.inr next) s' ↔
      ∃ w, next = uniformMap free bound h w ∧
        Semantics.Eval instr free (extend bound z) b s (.inr w) s' := by
  constructor
  · rintro r
    cases r with
    | case_inl _ branch => cases branch
    | case_inr scrutinee branch =>
        cases branch with
        | inr arg =>
            obtain ⟨rfl, rfl⟩ := hh.unique (eval_underBinder_iff.mp arg)
            exact ⟨_, rfl, scrutinee⟩
  · rintro ⟨w, rfl, run⟩
    exact .case_inr run (.inr (eval_underBinder_iff.mpr (hh.eval s')))

/-- The left-hand side of the uniformity square faults exactly when `b` does. -/
theorem uniformity_lhs_fault_iff (hh : Semantics.Inert h) {z : Value α} {s s' : σ} :
    Semantics.Fault instr faults free (extend bound z)
        (.case b (.inl (.bv 0)) (.inr h.underBinder)) s s' ↔
      Semantics.Fault instr faults free (extend bound z) b s s' := by
  constructor
  · rintro f
    cases f with
    | case_arg arg => exact arg
    | case_inl _ branch => cases branch with | inl arg => cases arg
    | case_inr _ branch =>
        cases branch with
        | inr arg => exact absurd (fault_underBinder_iff.mp arg) hh.not_fault
  · exact .case_arg

/-- The left-hand side of the uniformity square diverges exactly when `b` does. -/
theorem uniformity_lhs_diverges_iff (hh : Semantics.Inert h) {z : Value α} {s : σ} :
    Semantics.External.Diverges instr free prim
        (.term (extend bound z) (.case b (.inl (.bv 0)) (.inr h.underBinder)) s) ↔
      Semantics.External.Diverges instr free prim (.term (extend bound z) b s) := by
  constructor
  · intro d
    cases d.unfold with
    | core core => cases core with
      | case_scrutinee arg => exact arg
      | case_inl _ branch =>
          cases branch.unfold with
          | core c => cases c with | inl arg => cases arg.unfold with | core c₂ => cases c₂
      | case_inr _ branch =>
          cases branch.unfold with
          | core c =>
              cases c with
              | inr arg => exact absurd (diverges_underBinder_iff.mp arg) hh.not_diverges
  · exact fun d => .fold_core (.case_scrutinee d)

end Uniformity

/-- **Uniformity.** If a pure map `h` makes the square commute observationally,
it transports the loop: starting at `a` with body `b` is the same as starting
at `h a` with body `b'`. The square is used only through the four
correspondences above, so no classical reasoning and no instruction contract is
needed; the loop states of the two sides are in bijection via `h`. -/
theorem obs_uniformity {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)} (hh : Semantics.Inert h)
    (square : Tm.Obs.{u, v, w, x} (.case b (.inl (.bv 0)) (.inr h.underBinder))
      (Tm.instantiate b'.underBinder h)) :
    Tm.Obs.{u, v, w, x} (.iter a b) (.iter (.let₁ a h) b') where
  eval := by
    intro α σ instr free bound s s' value
    have hexit : ∀ {z out : Value α} {t t' : σ},
        Semantics.Eval instr free (extend bound (uniformMap free bound h z)) b' t (.inl out) t' ↔
          Semantics.Eval instr free (extend bound z) b t (.inl out) t' := by
      intro z out t t'
      exact ((uniformity_rhs_eval_iff hh).symm.trans square.eval.symm).trans
        uniformity_lhs_exit_iff
    have hcont : ∀ {z next : Value α} {t t' : σ},
        Semantics.Eval instr free (extend bound (uniformMap free bound h z)) b' t
            (.inr next) t' ↔
          ∃ w, next = uniformMap free bound h w ∧
            Semantics.Eval instr free (extend bound z) b t (.inr w) t' := by
      intro z next t t'
      exact ((uniformity_rhs_eval_iff hh).symm.trans square.eval.symm).trans
        (uniformity_lhs_cont_iff hh)
    constructor
    · rintro r
      cases r with
      | iter init loop =>
          refine .iter (.let₁ init (hh.eval _)) ?_
          exact Semantics.Loop.simulate
            (R := fun u w => u = uniformMap free bound h w)
            (fun hu run => hu ▸ hexit.mpr run)
            (fun hu run => ⟨_, rfl, hu ▸ hcont.mpr ⟨_, rfl, run⟩⟩) loop rfl
    · rintro r
      cases r with
      | iter init loop =>
          cases init with
          | let₁ arg body =>
              obtain ⟨rfl, rfl⟩ := hh.unique body
              refine .iter arg ?_
              exact Semantics.Loop.simulate
                (R := fun w u => u = uniformMap free bound h w)
                (fun hu run => hexit.mp (hu ▸ run))
                (fun hu run => by
                  obtain ⟨w', rfl, runB⟩ := hcont.mp (hu ▸ run)
                  exact ⟨w', rfl, runB⟩) loop rfl
  fault := by
    intro α σ instr faults free bound s s'
    have hfault : ∀ {z : Value α} {t t' : σ},
        Semantics.Fault instr faults free (extend bound (uniformMap free bound h z)) b' t t' ↔
          Semantics.Fault instr faults free (extend bound z) b t t' := by
      intro z t t'
      exact ((uniformity_rhs_fault_iff hh).symm.trans square.fault.symm).trans
        (uniformity_lhs_fault_iff hh)
    have hcont : ∀ {z next : Value α} {t t' : σ},
        Semantics.Eval instr free (extend bound (uniformMap free bound h z)) b' t
            (.inr next) t' ↔
          ∃ w, next = uniformMap free bound h w ∧
            Semantics.Eval instr free (extend bound z) b t (.inr w) t' := by
      intro z next t t'
      exact ((uniformity_rhs_eval_iff hh).symm.trans square.eval.symm).trans
        (uniformity_lhs_cont_iff hh)
    constructor
    · rintro f
      cases f with
      | iter_init arg => exact .iter_init (.let₁_arg arg)
      | iter_loop arg loop =>
          refine .iter_loop (.let₁ arg (hh.eval _)) ?_
          exact Semantics.LoopFault.simulate
            (R := fun u w => u = uniformMap free bound h w)
            (fun hu fl => hu ▸ hfault.mpr fl)
            (fun hu run => ⟨_, rfl, hu ▸ hcont.mpr ⟨_, rfl, run⟩⟩) loop rfl
    · rintro f
      cases f with
      | iter_init arg =>
          cases arg with
          | let₁_arg arg => exact .iter_init arg
          | let₁_body _ body => exact absurd body hh.not_fault
      | iter_loop arg loop =>
          cases arg with
          | let₁ arg body =>
              obtain ⟨rfl, rfl⟩ := hh.unique body
              refine .iter_loop arg ?_
              exact Semantics.LoopFault.simulate
                (R := fun w u => u = uniformMap free bound h w)
                (fun hu fl => hfault.mp (hu ▸ fl))
                (fun hu run => by
                  obtain ⟨w', rfl, runB⟩ := hcont.mp (hu ▸ run)
                  exact ⟨w', rfl, runB⟩) loop rfl
  diverges := by
    intro α σ instr prim free bound s
    have hdiv : ∀ {z : Value α} {t : σ},
        Semantics.External.Diverges instr free prim
            (.term (extend bound (uniformMap free bound h z)) b' t) ↔
          Semantics.External.Diverges instr free prim (.term (extend bound z) b t) := by
      intro z t
      exact ((uniformity_rhs_diverges_iff hh).symm.trans square.diverges.symm).trans
        (uniformity_lhs_diverges_iff hh)
    have hcont : ∀ {z next : Value α} {t t' : σ},
        Semantics.Eval instr free (extend bound (uniformMap free bound h z)) b' t
            (.inr next) t' ↔
          ∃ w, next = uniformMap free bound h w ∧
            Semantics.Eval instr free (extend bound z) b t (.inr w) t' := by
      intro z next t t'
      exact ((uniformity_rhs_eval_iff hh).symm.trans square.eval.symm).trans
        (uniformity_lhs_cont_iff hh)
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init => exact .fold_core (.iter_init (.fold_core (.let₁_arg init)))
        | iter_loop init loop =>
            refine .fold_core (.iter_loop (.let₁ init (hh.eval _)) ?_)
            exact Semantics.External.Diverges.simulate_loop
              (R := fun u w => u = uniformMap free bound h w)
              (fun hu dv => hu ▸ hdiv.mpr dv)
              (fun hu run => ⟨_, rfl, hu ▸ hcont.mpr ⟨_, rfl, run⟩⟩) rfl loop
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init =>
            cases init.unfold with
            | core c => cases c with
              | let₁_arg arg => exact .fold_core (.iter_init arg)
              | let₁_body _ body => exact absurd body hh.not_diverges
        | iter_loop init loop =>
            cases init with
            | let₁ arg body =>
                obtain ⟨rfl, rfl⟩ := hh.unique body
                refine .fold_core (.iter_loop arg ?_)
                exact Semantics.External.Diverges.simulate_loop
                  (R := fun w u => u = uniformMap free bound h w)
                  (fun hu dv => hdiv.mp (hu ▸ dv))
                  (fun hu run => by
                    obtain ⟨w', rfl, runB⟩ := hcont.mp (hu ▸ run)
                    exact ⟨w', rfl, runB⟩) rfl loop

/-! ## Naturality -/

/-- The loop body that absorbs the continuation of a loop: where the original
body exits, this one runs the continuation and exits with its result; where it
continues, this one continues unchanged. This is the body on the right-hand
side of the Elgot naturality axiom. -/
def Tm.naturalBody {n : Nat} (b k : Tm ν Φ (n + 1)) : Tm ν Φ (n + 1) :=
  .case b (.inl k.underBinder) (.inr (.bv 0))

section Naturality

variable {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}
  {free : FreeEnv ν α} {m : Nat} {bound : BoundEnv α m} {b k : Tm ν Φ (m + 1)}

/-- The absorbing body exits exactly when the original body exits and the
continuation then returns. -/
theorem naturalBody_exit_iff {z value : Value α} {s s' : σ} :
    Semantics.Eval instr free (extend bound z) (b.naturalBody k) s (.inl value) s' ↔
      ∃ out mid, Semantics.Eval instr free (extend bound z) b s (.inl out) mid ∧
        Semantics.Eval instr free (extend bound out) k mid value s' := by
  constructor
  · rintro r
    cases r with
    | case_inl scrutinee branch =>
        cases branch with
        | inl arg => exact ⟨_, _, scrutinee, eval_underBinder_iff.mp arg⟩
    | case_inr _ branch => cases branch
  · rintro ⟨out, mid, hb, hk⟩
    exact .case_inl hb (.inl (eval_underBinder_iff.mpr hk))

/-- The absorbing body continues exactly when the original body continues, with
the same new loop state. -/
theorem naturalBody_cont_iff {z next : Value α} {s s' : σ} :
    Semantics.Eval instr free (extend bound z) (b.naturalBody k) s (.inr next) s' ↔
      Semantics.Eval instr free (extend bound z) b s (.inr next) s' := by
  constructor
  · rintro r
    cases r with
    | case_inl _ branch => cases branch
    | case_inr scrutinee branch =>
        cases branch with
        | inr arg => obtain ⟨rfl, rfl⟩ := eval_bv_result arg; exact scrutinee
  · exact fun r => .case_inr r (.inr .bv)

/-- The absorbing body faults exactly when the original body faults, or exits
into a faulting continuation. -/
theorem naturalBody_fault_iff {z : Value α} {s s' : σ} :
    Semantics.Fault instr faults free (extend bound z) (b.naturalBody k) s s' ↔
      Semantics.Fault instr faults free (extend bound z) b s s' ∨
        ∃ out mid, Semantics.Eval instr free (extend bound z) b s (.inl out) mid ∧
          Semantics.Fault instr faults free (extend bound out) k mid s' := by
  constructor
  · rintro f
    cases f with
    | case_arg arg => exact Or.inl arg
    | case_inl arg branch =>
        cases branch with
        | inl bf => exact Or.inr ⟨_, _, arg, fault_underBinder_iff.mp bf⟩
    | case_inr _ branch => cases branch with | inr bf => cases bf
  · rintro (f | ⟨out, mid, hb, hk⟩)
    · exact .case_arg f
    · exact .case_inl hb (.inl (fault_underBinder_iff.mpr hk))

/-- The absorbing body diverges exactly when the original body diverges, or
exits into a diverging continuation. -/
theorem naturalBody_diverges_iff {z : Value α} {s : σ} :
    Semantics.External.Diverges instr free prim
        (.term (extend bound z) (b.naturalBody k) s) ↔
      Semantics.External.Diverges instr free prim (.term (extend bound z) b s) ∨
        ∃ out mid, Semantics.Eval instr free (extend bound z) b s (.inl out) mid ∧
          Semantics.External.Diverges instr free prim (.term (extend bound out) k mid) := by
  constructor
  · intro d
    cases d.unfold with
    | core core => cases core with
      | case_scrutinee arg => exact Or.inl arg
      | case_inl arg branch =>
          cases branch.unfold with
          | core c₁ => cases c₁ with
            | inl bd => exact Or.inr ⟨_, _, arg, diverges_underBinder_iff.mp bd⟩
      | case_inr _ branch =>
          cases branch.unfold with
          | core c₁ => cases c₁ with
            | inr bd => cases bd.unfold with | core c₂ => cases c₂
  · rintro (d | ⟨out, mid, hb, hk⟩)
    · exact .fold_core (.case_scrutinee d)
    · exact .fold_core (.case_inl hb (.fold_core (.inl (diverges_underBinder_iff.mpr hk))))

/-- **The classical step.** An infinite run of the absorbing loop is either an
infinite run of the original loop, or a finite prefix of it escaping into a
diverging continuation. The split is on whether *some* finite prefix escapes;
on the negative branch the original loop is shown infinite by coinduction. This
is the same shape as
`Silmaril.Isotope.Morphism.IterSSA.External.compile_loop_diverges_rev`. -/
theorem naturalBody_loop_diverges_rev {z : Value α} {t : σ}
    (d : Semantics.External.Diverges instr free prim
      (.loop bound (b.naturalBody k) z t)) :
    Semantics.External.Diverges instr free prim (.loop bound b z t) ∨
      ∃ out mid, Semantics.Loop instr free bound b z t out mid ∧
        Semantics.External.Diverges instr free prim (.term (extend bound out) k mid) := by
  by_cases hP : ∃ out mid, Semantics.Loop instr free bound b z t out mid ∧
      Semantics.External.Diverges instr free prim (.term (extend bound out) k mid)
  · exact Or.inr hP
  refine Or.inl (Semantics.External.Diverges.coinduct
    (fun cfg => (∃ cur u, cfg = .loop bound b cur u ∧
        Semantics.External.Diverges instr free prim
          (.loop bound (b.naturalBody k) cur u) ∧
        ¬ ∃ out mid, Semantics.Loop instr free bound b cur u out mid ∧
          Semantics.External.Diverges instr free prim (.term (extend bound out) k mid)) ∨
      Semantics.External.Diverges instr free prim cfg) ?_ (Or.inl ⟨z, t, rfl, d, hP⟩))
  rintro cfg (⟨cur, u, rfl, hd, hnot⟩ | hd)
  · cases hd.unfold with
    | core core => cases core with
      | loop_body step =>
          rcases naturalBody_diverges_iff.mp step with hb | ⟨out, mid, he, hk⟩
          · exact .core (.loop_body (Or.inr hb))
          · exact absurd ⟨out, mid, .done he, hk⟩ hnot
      | loop_step head tail =>
          refine .core (.loop_step (naturalBody_cont_iff.mp head)
            (Or.inl ⟨_, _, rfl, tail, ?_⟩))
          rintro ⟨out, mid, hloop, hk⟩
          exact hnot ⟨out, mid, .step (naturalBody_cont_iff.mp head) hloop, hk⟩
  · exact hd.unfold.mono (fun _ h => Or.inr h)

end Naturality

/-- **Naturality.** A loop followed by a continuation is a single loop whose
body absorbs the continuation. Every direction but one is a plain induction on
the finite iteration; the right-to-left divergence direction is the classical
escape-or-not argument of `naturalBody_loop_diverges_rev`. -/
theorem obs_naturality (a : Tm ν Φ n) (b k : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.let₁ (.iter a b) k) (.iter a (b.naturalBody k)) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₁ arg body =>
          cases arg with
          | iter init loop =>
              refine .iter init ?_
              exact Semantics.Loop.induction_fixed
                (motive := fun cur t v t' => ∀ (res : Value α) (u : σ),
                  Semantics.Eval instr free (extend bound v) k t' res u →
                  Semantics.Loop instr free bound (b.naturalBody k) cur t res u)
                (fun hb _ _ hk => .done (naturalBody_exit_iff.mpr ⟨_, _, hb, hk⟩))
                (fun hhead _ ih res u hk =>
                  .step (naturalBody_cont_iff.mpr hhead) (ih res u hk))
                loop _ _ body
    · rintro r
      cases r with
      | iter init loop =>
          obtain ⟨out, mid, hloop, hk⟩ :=
            Semantics.Loop.induction_fixed
              (motive := fun cur t v t' => ∃ out mid,
                Semantics.Loop instr free bound b cur t out mid ∧
                  Semantics.Eval instr free (extend bound out) k mid v t')
              (fun hb => by
                obtain ⟨out, mid, h₁, h₂⟩ := naturalBody_exit_iff.mp hb
                exact ⟨out, mid, .done h₁, h₂⟩)
              (fun hhead _ ih => by
                obtain ⟨out, mid, h₁, h₂⟩ := ih
                exact ⟨out, mid, .step (naturalBody_cont_iff.mp hhead) h₁, h₂⟩)
              loop
          exact .let₁ (.iter init hloop) hk
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | let₁_arg arg =>
          cases arg with
          | iter_init ia => exact .iter_init ia
          | iter_loop ia lf =>
              refine .iter_loop ia ?_
              exact Semantics.LoopFault.induction_fixed
                (motive := fun cur t t' =>
                  Semantics.LoopFault instr faults free bound (b.naturalBody k) cur t t')
                (fun hf => .body (naturalBody_fault_iff.mpr (Or.inl hf)))
                (fun hhead _ ih => .step (naturalBody_cont_iff.mpr hhead) ih)
                lf
      | let₁_body arg body =>
          cases arg with
          | iter init loop =>
              refine .iter_loop init ?_
              exact Semantics.Loop.induction_fixed
                (motive := fun cur t v t' => ∀ (u : σ),
                  Semantics.Fault instr faults free (extend bound v) k t' u →
                  Semantics.LoopFault instr faults free bound (b.naturalBody k) cur t u)
                (fun hb _ hk => .body (naturalBody_fault_iff.mpr (Or.inr ⟨_, _, hb, hk⟩)))
                (fun hhead _ ih u hk => .step (naturalBody_cont_iff.mpr hhead) (ih u hk))
                loop _ body
    · rintro f
      cases f with
      | iter_init ia => exact .let₁_arg (.iter_init ia)
      | iter_loop init lf =>
          rcases Semantics.LoopFault.induction_fixed
            (motive := fun cur t t' =>
              Semantics.LoopFault instr faults free bound b cur t t' ∨
                ∃ out mid, Semantics.Loop instr free bound b cur t out mid ∧
                  Semantics.Fault instr faults free (extend bound out) k mid t')
            (fun hf => by
              rcases naturalBody_fault_iff.mp hf with hb | ⟨out, mid, h₁, h₂⟩
              · exact Or.inl (.body hb)
              · exact Or.inr ⟨out, mid, .done h₁, h₂⟩)
            (fun hhead _ ih => by
              rcases ih with hb | ⟨out, mid, h₁, h₂⟩
              · exact Or.inl (.step (naturalBody_cont_iff.mp hhead) hb)
              · exact Or.inr ⟨out, mid, .step (naturalBody_cont_iff.mp hhead) h₁, h₂⟩)
            lf with hb | ⟨out, mid, hloop, hk⟩
          · exact .let₁_arg (.iter_loop init hb)
          · exact .let₁_body (.iter init hloop) hk
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg =>
            cases arg.unfold with
            | core c₁ => cases c₁ with
              | iter_init init => exact .fold_core (.iter_init init)
              | iter_loop init loopD =>
                  refine .fold_core (.iter_loop init ?_)
                  exact Semantics.External.Diverges.simulate_loop
                    (R := fun (u w : Value α) => u = w)
                    (fun hu dv => hu ▸ naturalBody_diverges_iff.mpr (Or.inl dv))
                    (fun hu run => ⟨_, rfl, hu ▸ naturalBody_cont_iff.mpr run⟩)
                    rfl loopD
        | let₁_body arg body =>
            cases arg with
            | iter init loop =>
                refine .fold_core (.iter_loop init ?_)
                exact Semantics.Loop.induction_fixed
                  (motive := fun cur t v t' =>
                    Semantics.External.Diverges instr free prim
                        (.term (extend bound v) k t') →
                      Semantics.External.Diverges instr free prim
                        (.loop bound (b.naturalBody k) cur t))
                  (fun hb hk => .fold_core (.loop_body
                    (naturalBody_diverges_iff.mpr (Or.inr ⟨_, _, hb, hk⟩))))
                  (fun hhead _ ih hk => .fold_core
                    (.loop_step (naturalBody_cont_iff.mpr hhead) (ih hk)))
                  loop body
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init => exact .fold_core (.let₁_arg (.fold_core (.iter_init init)))
        | iter_loop init loopD =>
            rcases naturalBody_loop_diverges_rev loopD with hb | ⟨out, mid, hloop, hk⟩
            · exact .fold_core (.let₁_arg (.fold_core (.iter_loop init hb)))
            · exact .fold_core (.let₁_body (.iter init hloop) hk)

/-! ## Codiagonal -/

/-- The outer body on the left of the codiagonal axiom: a whole inner loop over
`b`, started at the current outer state. -/
def Tm.innerLoop {n : Nat} (b : Tm ν Φ (n + 1)) : Tm ν Φ (n + 1) :=
  .iter (.bv 0) b.underBinder

/-- The body on the right of the codiagonal axiom: one step of `b`, whose exit
value is handed straight to the single remaining loop. -/
def Tm.flatBody {n : Nat} (b : Tm ν Φ (n + 1)) : Tm ν Φ (n + 1) :=
  .case b (.bv 0) (.inr (.bv 0))

section Codiagonal

variable {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}
  {free : FreeEnv ν α} {m : Nat} {bound : BoundEnv α m} {b : Tm ν Φ (m + 1)}

/-- Running the inner loop body is running a whole `b`-iteration. -/
theorem innerLoop_eval_iff {z result : Value α} {s s' : σ} :
    Semantics.Eval instr free (extend bound z) b.innerLoop s result s' ↔
      Semantics.Loop instr free bound b z s result s' := by
  constructor
  · rintro r
    cases r with
    | iter init loop =>
        obtain ⟨rfl, rfl⟩ := eval_bv_result init
        exact loop_underBinder_iff.mp loop
  · exact fun r => .iter .bv (loop_underBinder_iff.mpr r)

/-- The inner loop body faults exactly when the `b`-iteration faults. -/
theorem innerLoop_fault_iff {z : Value α} {s s' : σ} :
    Semantics.Fault instr faults free (extend bound z) b.innerLoop s s' ↔
      Semantics.LoopFault instr faults free bound b z s s' := by
  constructor
  · rintro f
    cases f with
    | iter_init arg => cases arg
    | iter_loop arg loop =>
        obtain ⟨rfl, rfl⟩ := eval_bv_result arg
        exact loopFault_underBinder_iff.mp loop
  · exact fun f => .iter_loop .bv (loopFault_underBinder_iff.mpr f)

/-- The inner loop body diverges exactly when the `b`-iteration is infinite. -/
theorem innerLoop_diverges_iff {z : Value α} {s : σ} :
    Semantics.External.Diverges instr free prim (.term (extend bound z) b.innerLoop s) ↔
      Semantics.External.Diverges instr free prim (.loop bound b z s) := by
  constructor
  · intro d
    cases d.unfold with
    | core core => cases core with
      | iter_init init => cases init.unfold with | core c => cases c
      | iter_loop init loop =>
          obtain ⟨rfl, rfl⟩ := eval_bv_result init
          exact loopDiverges_underBinder_iff.mp loop
  · exact fun d => .fold_core (.iter_loop .bv (loopDiverges_underBinder_iff.mpr d))

/-- The flattened body exits exactly when `b` exits with an exit value. -/
theorem flatBody_exit_iff {z out : Value α} {s s' : σ} :
    Semantics.Eval instr free (extend bound z) b.flatBody s (.inl out) s' ↔
      Semantics.Eval instr free (extend bound z) b s (.inl (.inl out)) s' := by
  constructor
  · rintro r
    cases r with
    | case_inl scrutinee branch =>
        obtain ⟨rfl, rfl⟩ := eval_bv_result branch
        exact scrutinee
    | case_inr _ branch => cases branch
  · exact fun r => .case_inl r .bv

/-- The flattened body continues either where `b` exits with a continuation
value, or where `b` itself continues. -/
theorem flatBody_cont_iff {z next : Value α} {s s' : σ} :
    Semantics.Eval instr free (extend bound z) b.flatBody s (.inr next) s' ↔
      Semantics.Eval instr free (extend bound z) b s (.inl (.inr next)) s' ∨
        Semantics.Eval instr free (extend bound z) b s (.inr next) s' := by
  constructor
  · rintro r
    cases r with
    | case_inl scrutinee branch =>
        obtain ⟨rfl, rfl⟩ := eval_bv_result branch
        exact Or.inl scrutinee
    | case_inr scrutinee branch =>
        cases branch with
        | inr arg =>
            obtain ⟨rfl, rfl⟩ := eval_bv_result arg
            exact Or.inr scrutinee
  · rintro (r | r)
    · exact .case_inl r .bv
    · exact .case_inr r (.inr .bv)

/-- The flattened body faults exactly when `b` faults. -/
theorem flatBody_fault_iff {z : Value α} {s s' : σ} :
    Semantics.Fault instr faults free (extend bound z) b.flatBody s s' ↔
      Semantics.Fault instr faults free (extend bound z) b s s' := by
  constructor
  · rintro f
    cases f with
    | case_arg arg => exact arg
    | case_inl _ branch => cases branch
    | case_inr _ branch => cases branch with | inr bf => cases bf
  · exact .case_arg

/-- The flattened body diverges exactly when `b` diverges. -/
theorem flatBody_diverges_iff {z : Value α} {s : σ} :
    Semantics.External.Diverges instr free prim (.term (extend bound z) b.flatBody s) ↔
      Semantics.External.Diverges instr free prim (.term (extend bound z) b s) := by
  constructor
  · intro d
    cases d.unfold with
    | core core => cases core with
      | case_scrutinee arg => exact arg
      | case_inl _ branch => cases branch.unfold with | core c => cases c
      | case_inr _ branch =>
          cases branch.unfold with
          | core c => cases c with
            | inr bd => cases bd.unfold with | core c₂ => cases c₂
  · exact fun d => .fold_core (.case_scrutinee d)

/-- A `b`-iteration that exits is a run of the flattened loop. -/
theorem flat_of_loop_exit {z out : Value α} {s s' : σ}
    (h : Semantics.Loop instr free bound b z s (.inl out) s') :
    Semantics.Loop instr free bound b.flatBody z s out s' :=
  Semantics.Loop.induction_fixed
    (motive := fun cur t v t' => ∀ o : Value α, v = .inl o →
      Semantics.Loop instr free bound b.flatBody cur t o t')
    (fun step _o hv => .done (flatBody_exit_iff.mpr (hv ▸ step)))
    (fun head _ ih o hv => .step (flatBody_cont_iff.mpr (Or.inr head)) (ih o hv))
    h out rfl

/-- A `b`-iteration that hands a continuation value to the outer loop is a
prefix of a run of the flattened loop. -/
theorem flat_of_loop_cont {z next value : Value α} {s s' u : σ}
    (h : Semantics.Loop instr free bound b z s (.inr next) s')
    (rest : Semantics.Loop instr free bound b.flatBody next s' value u) :
    Semantics.Loop instr free bound b.flatBody z s value u :=
  Semantics.Loop.induction_fixed
    (motive := fun cur t v t' => ∀ nx : Value α, v = .inr nx →
      ∀ (res : Value α) (w : σ), Semantics.Loop instr free bound b.flatBody nx t' res w →
        Semantics.Loop instr free bound b.flatBody cur t res w)
    (fun step _nx hv _ _ hcont =>
      .step (flatBody_cont_iff.mpr (Or.inl (hv ▸ step))) hcont)
    (fun head _ ih nx hv res w hcont =>
      .step (flatBody_cont_iff.mpr (Or.inr head)) (ih nx hv res w hcont))
    h next rfl value u rest

/-- Nested iteration is flattened iteration, on finite runs. -/
theorem loop_innerLoop_to_flat {z value : Value α} {s s' : σ}
    (h : Semantics.Loop instr free bound b.innerLoop z s value s') :
    Semantics.Loop instr free bound b.flatBody z s value s' :=
  Semantics.Loop.induction_fixed
    (motive := fun cur t v t' => Semantics.Loop instr free bound b.flatBody cur t v t')
    (fun step => flat_of_loop_exit (innerLoop_eval_iff.mp step))
    (fun head _ ih => flat_of_loop_cont (innerLoop_eval_iff.mp head) ih)
    h

/-- One more `b`-step at the front of a nested run stays inside the same outer
iteration. -/
theorem loop_innerLoop_prepend {z next value : Value α} {s s' u : σ}
    (head : Semantics.Eval instr free (extend bound z) b s (.inr next) s')
    (rest : Semantics.Loop instr free bound b.innerLoop next s' value u) :
    Semantics.Loop instr free bound b.innerLoop z s value u := by
  cases rest with
  | done step => exact .done (innerLoop_eval_iff.mpr (.step head (innerLoop_eval_iff.mp step)))
  | step head' tail =>
      exact .step (innerLoop_eval_iff.mpr (.step head (innerLoop_eval_iff.mp head'))) tail

/-- Flattened iteration is nested iteration, on finite runs. -/
theorem loop_flat_to_innerLoop {z value : Value α} {s s' : σ}
    (h : Semantics.Loop instr free bound b.flatBody z s value s') :
    Semantics.Loop instr free bound b.innerLoop z s value s' :=
  Semantics.Loop.induction_fixed
    (motive := fun cur t v t' => Semantics.Loop instr free bound b.innerLoop cur t v t')
    (fun step => .done (innerLoop_eval_iff.mpr (.done (flatBody_exit_iff.mp step))))
    (fun head _ ih => by
      rcases flatBody_cont_iff.mp head with hb | hb
      · exact .step (innerLoop_eval_iff.mpr (.done hb)) ih
      · exact loop_innerLoop_prepend hb ih)
    h

/-- A faulting `b`-iteration is a faulting flattened run. -/
theorem flatFault_of_loopFault {z : Value α} {s s' : σ}
    (h : Semantics.LoopFault instr faults free bound b z s s') :
    Semantics.LoopFault instr faults free bound b.flatBody z s s' :=
  Semantics.LoopFault.induction_fixed
    (motive := fun cur t t' => Semantics.LoopFault instr faults free bound b.flatBody cur t t')
    (fun f => .body (flatBody_fault_iff.mpr f))
    (fun head _ ih => .step (flatBody_cont_iff.mpr (Or.inr head)) ih)
    h

/-- A finite `b`-iteration handing a continuation value to the outer loop
prefixes a faulting flattened run. -/
theorem flatFault_prepend_loop {z next : Value α} {s s' u : σ}
    (h : Semantics.Loop instr free bound b z s (.inr next) s')
    (rest : Semantics.LoopFault instr faults free bound b.flatBody next s' u) :
    Semantics.LoopFault instr faults free bound b.flatBody z s u :=
  Semantics.Loop.induction_fixed
    (motive := fun cur t v t' => ∀ nx : Value α, v = .inr nx → ∀ w : σ,
      Semantics.LoopFault instr faults free bound b.flatBody nx t' w →
        Semantics.LoopFault instr faults free bound b.flatBody cur t w)
    (fun step _nx hv _ hf => .step (flatBody_cont_iff.mpr (Or.inl (hv ▸ step))) hf)
    (fun head _ ih nx hv w hf => .step (flatBody_cont_iff.mpr (Or.inr head)) (ih nx hv w hf))
    h next rfl u rest

/-- Nested iteration is flattened iteration, on faulting runs. -/
theorem loopFault_innerLoop_to_flat {z : Value α} {s s' : σ}
    (h : Semantics.LoopFault instr faults free bound b.innerLoop z s s') :
    Semantics.LoopFault instr faults free bound b.flatBody z s s' :=
  Semantics.LoopFault.induction_fixed
    (motive := fun cur t t' => Semantics.LoopFault instr faults free bound b.flatBody cur t t')
    (fun f => flatFault_of_loopFault (innerLoop_fault_iff.mp f))
    (fun head _ ih => flatFault_prepend_loop (innerLoop_eval_iff.mp head) ih)
    h

/-- One more `b`-step at the front of a faulting nested run stays inside the
same outer iteration. -/
theorem loopFault_innerLoop_prepend {z next : Value α} {s s' u : σ}
    (head : Semantics.Eval instr free (extend bound z) b s (.inr next) s')
    (rest : Semantics.LoopFault instr faults free bound b.innerLoop next s' u) :
    Semantics.LoopFault instr faults free bound b.innerLoop z s u := by
  cases rest with
  | body f => exact .body (innerLoop_fault_iff.mpr (.step head (innerLoop_fault_iff.mp f)))
  | step head' tail =>
      exact .step (innerLoop_eval_iff.mpr (.step head (innerLoop_eval_iff.mp head'))) tail

/-- Flattened iteration is nested iteration, on faulting runs. -/
theorem loopFault_flat_to_innerLoop {z : Value α} {s s' : σ}
    (h : Semantics.LoopFault instr faults free bound b.flatBody z s s') :
    Semantics.LoopFault instr faults free bound b.innerLoop z s s' :=
  Semantics.LoopFault.induction_fixed
    (motive := fun cur t t' => Semantics.LoopFault instr faults free bound b.innerLoop cur t t')
    (fun f => .body (innerLoop_fault_iff.mpr (.body (flatBody_fault_iff.mp f))))
    (fun head _ ih => by
      rcases flatBody_cont_iff.mp head with hb | hb
      · exact .step (innerLoop_eval_iff.mpr (.done hb)) ih
      · exact loopFault_innerLoop_prepend hb ih)
    h

/-- An infinite `b`-iteration is an infinite flattened run. -/
theorem loopDiverges_of_loop {z : Value α} {s : σ}
    (h : Semantics.External.Diverges instr free prim (.loop bound b z s)) :
    Semantics.External.Diverges instr free prim (.loop bound b.flatBody z s) :=
  Semantics.External.Diverges.simulate_loop
    (R := fun (x y : Value α) => x = y)
    (fun hxy d => hxy ▸ flatBody_diverges_iff.mpr d)
    (fun hxy run => ⟨_, rfl, hxy ▸ flatBody_cont_iff.mpr (Or.inr run)⟩) rfl h

/-- Nested iteration is flattened iteration, on infinite runs. The relation
carries a pending finite `b`-prefix, so that each coinductive step consumes
exactly one `b`-step. -/
theorem loopDiverges_innerLoop_to_flat {z : Value α} {s : σ}
    (h : Semantics.External.Diverges instr free prim (.loop bound b.innerLoop z s)) :
    Semantics.External.Diverges instr free prim (.loop bound b.flatBody z s) := by
  refine Semantics.External.Diverges.coinduct
    (fun cfg => (∃ ci ui, cfg = .loop bound b.flatBody ci ui ∧
        Semantics.External.Diverges instr free prim (.loop bound b.innerLoop ci ui)) ∨
      (∃ ci ui nx ui', cfg = .loop bound b.flatBody ci ui ∧
        Semantics.Loop instr free bound b ci ui (.inr nx) ui' ∧
        Semantics.External.Diverges instr free prim (.loop bound b.innerLoop nx ui')) ∨
      Semantics.External.Diverges instr free prim cfg)
    ?_ (Or.inl ⟨z, s, rfl, h⟩)
  rintro cfg (⟨ci, ui, rfl, hd⟩ | ⟨ci, ui, nx, ui', rfl, hloop, hd⟩ | hd)
  · cases hd.unfold with
    | core core => cases core with
      | loop_body step =>
          exact ((loopDiverges_of_loop (innerLoop_diverges_iff.mp step)).unfold).mono
            (fun _ hx => Or.inr (Or.inr hx))
      | loop_step head tail =>
          cases innerLoop_eval_iff.mp head with
          | done step =>
              exact .core (.loop_step (flatBody_cont_iff.mpr (Or.inl step))
                (Or.inl ⟨_, _, rfl, tail⟩))
          | step head' rest =>
              exact .core (.loop_step (flatBody_cont_iff.mpr (Or.inr head'))
                (Or.inr (Or.inl ⟨_, _, _, _, rfl, rest, tail⟩)))
  · cases hloop with
    | done step =>
        exact .core (.loop_step (flatBody_cont_iff.mpr (Or.inl step))
          (Or.inl ⟨_, _, rfl, hd⟩))
    | step head' rest =>
        exact .core (.loop_step (flatBody_cont_iff.mpr (Or.inr head'))
          (Or.inr (Or.inl ⟨_, _, _, _, rfl, rest, hd⟩)))
  · exact hd.unfold.mono (fun _ hx => Or.inr (Or.inr hx))

/-- **The inner classical step.** If no finite `b`-prefix of an infinite
flattened run ever hands a continuation value to the outer loop, then the
`b`-iteration itself is infinite. -/
theorem loop_diverges_of_no_escape {z : Value α} {s : σ}
    (hno : ¬ ∃ nx u, Semantics.Loop instr free bound b z s (.inr nx) u ∧
      Semantics.External.Diverges instr free prim (.loop bound b.flatBody nx u))
    (hd : Semantics.External.Diverges instr free prim (.loop bound b.flatBody z s)) :
    Semantics.External.Diverges instr free prim (.loop bound b z s) := by
  refine Semantics.External.Diverges.coinduct
    (fun cfg => (∃ ci ui, cfg = .loop bound b ci ui ∧
        Semantics.External.Diverges instr free prim (.loop bound b.flatBody ci ui) ∧
        ¬ ∃ nx u, Semantics.Loop instr free bound b ci ui (.inr nx) u ∧
          Semantics.External.Diverges instr free prim (.loop bound b.flatBody nx u)) ∨
      Semantics.External.Diverges instr free prim cfg)
    ?_ (Or.inl ⟨z, s, rfl, hd, hno⟩)
  rintro cfg (⟨ci, ui, rfl, hdc, hnot⟩ | hdc)
  · cases hdc.unfold with
    | core core => cases core with
      | loop_body step => exact .core (.loop_body (Or.inr (flatBody_diverges_iff.mp step)))
      | loop_step head tail =>
          rcases flatBody_cont_iff.mp head with hb | hb
          · exact absurd ⟨_, _, .done hb, tail⟩ hnot
          · refine .core (.loop_step hb (Or.inl ⟨_, _, rfl, tail, ?_⟩))
            rintro ⟨nx, u, hloop, hdn⟩
            exact hnot ⟨nx, u, .step hb hloop, hdn⟩
  · exact hdc.unfold.mono (fun _ hx => Or.inr hx)

/-- **The outer classical step.** Flattened iteration is nested iteration, on
infinite runs: at each outer state, either some finite `b`-prefix escapes to a
new outer state, or the inner loop is already infinite. -/
theorem loopDiverges_flat_to_innerLoop {z : Value α} {s : σ}
    (h : Semantics.External.Diverges instr free prim (.loop bound b.flatBody z s)) :
    Semantics.External.Diverges instr free prim (.loop bound b.innerLoop z s) := by
  refine Semantics.External.Diverges.coinduct
    (fun cfg => (∃ ci ui, cfg = .loop bound b.innerLoop ci ui ∧
        Semantics.External.Diverges instr free prim (.loop bound b.flatBody ci ui)) ∨
      Semantics.External.Diverges instr free prim cfg)
    ?_ (Or.inl ⟨z, s, rfl, h⟩)
  rintro cfg (⟨ci, ui, rfl, hdc⟩ | hdc)
  · by_cases hEsc : ∃ nx u, Semantics.Loop instr free bound b ci ui (.inr nx) u ∧
        Semantics.External.Diverges instr free prim (.loop bound b.flatBody nx u)
    · obtain ⟨nx, u, hloop, hdn⟩ := hEsc
      exact .core (.loop_step (innerLoop_eval_iff.mpr hloop) (Or.inl ⟨nx, u, rfl, hdn⟩))
    · exact .core (.loop_body
        (Or.inr (innerLoop_diverges_iff.mpr (loop_diverges_of_no_escape hEsc hdc))))
  · exact hdc.unfold.mono (fun _ hx => Or.inr hx)

end Codiagonal

/-- **Codiagonal.** A loop whose body is itself a loop over the same state is a
single loop over the flattened body. The iteration counts of the two sides are
not in bijection, so every direction is an induction or coinduction that
regroups them; the right-to-left divergence direction nests the classical
escape-or-not argument twice, once to find each outer step and once to show
that the inner loop is infinite when no outer step is ever reached. -/
theorem obs_codiagonal (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
    Tm.Obs.{u, v, w, x} (.iter a b.innerLoop) (.iter a b.flatBody) where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r; cases r with | iter init loop => exact .iter init (loop_innerLoop_to_flat loop)
    · rintro r; cases r with | iter init loop => exact .iter init (loop_flat_to_innerLoop loop)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | iter_init arg => exact .iter_init arg
      | iter_loop arg loop => exact .iter_loop arg (loopFault_innerLoop_to_flat loop)
    · rintro f
      cases f with
      | iter_init arg => exact .iter_init arg
      | iter_loop arg loop => exact .iter_loop arg (loopFault_flat_to_innerLoop loop)
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init => exact .fold_core (.iter_init init)
        | iter_loop init loop =>
            exact .fold_core (.iter_loop init (loopDiverges_innerLoop_to_flat loop))
    · intro d
      cases d.unfold with
      | core core => cases core with
        | iter_init init => exact .fold_core (.iter_init init)
        | iter_loop init loop =>
            exact .fold_core (.iter_loop init (loopDiverges_flat_to_innerLoop loop))

/-! ## The fragment -/

/-- The fragment of the raw let-iter theory that holds for every instruction
model, with no typing, determinism, totality or purity side condition. -/
inductive ObsTheory : {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  /-- Reflexivity. -/
  | refl {n : Nat} (a : Tm ν Φ n) : ObsTheory a a
  /-- Symmetry. -/
  | symm {n : Nat} {a b : Tm ν Φ n} : ObsTheory a b → ObsTheory b a
  /-- Transitivity. -/
  | trans {n : Nat} {a b c : Tm ν Φ n} : ObsTheory a b → ObsTheory b c → ObsTheory a c
  /-- Congruence for a primitive application. -/
  | op {n : Nat} {f : Φ} {a a' : Tm ν Φ n} : ObsTheory a a' → ObsTheory (.op f a) (.op f a')
  /-- Congruence for sequencing. -/
  | let₁ {n : Nat} {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)} :
      ObsTheory a a' → ObsTheory b b' → ObsTheory (.let₁ a b) (.let₁ a' b')
  /-- Congruence for pairing. -/
  | pair {n : Nat} {a a' b b' : Tm ν Φ n} :
      ObsTheory a a' → ObsTheory b b' → ObsTheory (.pair a b) (.pair a' b')
  /-- Congruence for pair elimination. -/
  | let₂ {n : Nat} {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 2)} :
      ObsTheory a a' → ObsTheory b b' → ObsTheory (.let₂ a b) (.let₂ a' b')
  /-- Congruence for left injection. -/
  | inl {n : Nat} {a a' : Tm ν Φ n} : ObsTheory a a' → ObsTheory (.inl a) (.inl a')
  /-- Congruence for right injection. -/
  | inr {n : Nat} {a a' : Tm ν Φ n} : ObsTheory a a' → ObsTheory (.inr a) (.inr a')
  /-- Congruence for case analysis. -/
  | case {n : Nat} {e e' : Tm ν Φ n} {l l' r r' : Tm ν Φ (n + 1)} :
      ObsTheory e e' → ObsTheory l l' → ObsTheory r r' →
      ObsTheory (.case e l r) (.case e' l' r')
  /-- Congruence for empty elimination. -/
  | abort {n : Nat} {a a' : Tm ν Φ n} : ObsTheory a a' → ObsTheory (.abort a) (.abort a')
  /-- Congruence for iteration. -/
  | iter {n : Nat} {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)} :
      ObsTheory a a' → ObsTheory b b' → ObsTheory (.iter a b) (.iter a' b')
  /-- Returning the bound variable is the identity. -/
  | letEta {n : Nat} (a : Tm ν Φ n) : ObsTheory (.let₁ a (.bv 0)) a
  /-- Eliminating an explicit pair runs its components in order. -/
  | pairBeta {n : Nat} (a b : Tm ν Φ n) (c : Tm ν Φ (n + 2)) :
      ObsTheory (.let₂ (.pair a b) c) (.let₁ a (.let₁ b.lift c))
  /-- Case analysis on an explicit left injection takes the left branch. -/
  | caseBetaL {n : Nat} (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      ObsTheory (.case (.inl e) l r) (.let₁ e l)
  /-- Case analysis on an explicit right injection takes the right branch. -/
  | caseBetaR {n : Nat} (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      ObsTheory (.case (.inr e) l r) (.let₁ e r)
  /-- Nothing after an empty elimination is observable. -/
  | emptyInitial {n : Nat} (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
      ObsTheory (.let₁ (.abort a) b) (.let₁ (.abort a) c)
  /-- Bind a primitive's argument before applying it. -/
  | bindOp {n : Nat} {f : Φ} (a : Tm ν Φ n) (c : Tm ν Φ (n + 1)) :
      ObsTheory (.let₁ (.op f a) c) (.let₁ a (.let₁ (.op f (.bv 0)) c.underBinder))
  /-- Sequencing is associative. -/
  | bindLet {n : Nat} (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
      ObsTheory (.let₁ (.let₁ a b) c) (.let₁ a (.let₁ b c.underBinder))
  /-- Pair elimination commutes with a following binding. -/
  | bindLetPair {n : Nat} (e : Tm ν Φ n) (c : Tm ν Φ (n + 2)) (d : Tm ν Φ (n + 1)) :
      ObsTheory (.let₁ (.let₂ e c) d) (.let₂ e (.let₁ c d.underBinder.underBinder))
  /-- Case analysis commutes with a following binding. -/
  | bindLetCase {n : Nat} (e : Tm ν Φ n) (l r d : Tm ν Φ (n + 1)) :
      ObsTheory (.let₁ (.case e l r) d)
        (.case e (.let₁ l d.underBinder) (.let₁ r d.underBinder))
  /-- Bind the scrutinee of a pair elimination. -/
  | bindPair {n : Nat} (a : Tm ν Φ n) (c : Tm ν Φ (n + 2)) :
      ObsTheory (.let₂ a c) (.let₁ a (.let₂ (.bv 0) c.underTwoBinders))
  /-- Bind the scrutinee of a case analysis. -/
  | bindCase {n : Nat} (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      ObsTheory (.case e l r) (.let₁ e (.case (.bv 0) l.underBinder r.underBinder))
  /-- Elgot iteration binding: the initializer runs exactly once, up front. -/
  | iterBind {n : Nat} (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
      ObsTheory (.iter a b) (.let₁ a (.iter (.bv 0) b.underBinder))
  /-- Elgot fixpoint: unfold one iteration step. -/
  | fixpoint {n : Nat} (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
      ObsTheory (.iter a b)
        (.let₁ a (.case b (.bv 0) (.iter (.bv 0) b.underBinder.underBinder)))
  /-- Pure-let beta, for a substituend that is already a value. -/
  | letBeta {n : Nat} (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) (ha : Semantics.Inert a) :
      ObsTheory (.let₁ a b) (b.instantiate a)
  /-- Elgot naturality: a loop followed by a continuation is a single loop
  whose body absorbs the continuation. -/
  | naturality {n : Nat} (a : Tm ν Φ n) (b k : Tm ν Φ (n + 1)) :
      ObsTheory (.let₁ (.iter a b) k) (.iter a (b.naturalBody k))
  /-- Elgot codiagonal: a loop whose body is itself a loop over the same state
  is a single loop over the flattened body. -/
  | codiagonal {n : Nat} (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
      ObsTheory (.iter a b.innerLoop) (.iter a b.flatBody)
  /-- Uniformity along a pure map that is already a value. -/
  | uniformity {n : Nat} {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)}
      (hh : Semantics.Inert h)
      (square : ObsTheory (.case b (.inl (.bv 0)) (.inr h.underBinder))
        (Tm.instantiate b'.underBinder h)) :
      ObsTheory (.iter a b) (.iter (.let₁ a h) b')

/-- Inert terms are syntactically pure, at every choice of pure effect: they
are built from variables, unit, pairing and injection alone. -/
theorem Pure.of_inert {ε : Type w} [HasEff Φ ε] {pureEff : ε} {t : Tm ν Φ n}
    (h : Semantics.Inert t) : Pure pureEff t := by
  induction h with
  | fv x => exact .fv
  | bv i => exact .bv
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

namespace ObsTheory

/-- **Soundness.** Every equation of the fragment identifies observationally
equivalent terms, for every instruction relation, primitive-divergence
predicate and primitive-fault relation. -/
theorem sound {a b : Tm ν Φ n} (h : ObsTheory a b) : Tm.Obs.{u, v, w, x} a b := by
  induction h with
  | refl a => exact Tm.Obs.refl a
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | op _ ih => exact Tm.Obs.op _ ih
  | let₁ _ _ ih₁ ih₂ => exact Tm.Obs.let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact Tm.Obs.pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact Tm.Obs.let₂ ih₁ ih₂
  | inl _ ih => exact Tm.Obs.inl ih
  | inr _ ih => exact Tm.Obs.inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact Tm.Obs.case ih₁ ih₂ ih₃
  | abort _ ih => exact Tm.Obs.abort ih
  | iter _ _ ih₁ ih₂ => exact Tm.Obs.iter ih₁ ih₂
  | letEta a => exact obs_letEta a
  | pairBeta a b c => exact obs_pairBeta a b c
  | caseBetaL e l r => exact obs_caseBetaL e l r
  | caseBetaR e l r => exact obs_caseBetaR e l r
  | emptyInitial a b c => exact obs_emptyInitial a b c
  | bindOp a c => exact obs_bindOp _ a c
  | bindLet a b c => exact obs_bindLet a b c
  | bindLetPair e c d => exact obs_bindLetPair e c d
  | bindLetCase e l r d => exact obs_bindLetCase e l r d
  | bindPair a c => exact obs_bindPair a c
  | bindCase e l r => exact obs_bindCase e l r
  | iterBind a b => exact obs_iterBind a b
  | fixpoint a b => exact obs_fixpoint a b
  | letBeta a b ha => exact obs_letBeta a b ha
  | naturality a b k => exact obs_naturality a b k
  | codiagonal a b => exact obs_codiagonal a b
  | uniformity hh _ ih => exact obs_uniformity hh ih

variable {ε : Type w} [HasEff Φ ε]

/-- Every rule of the fragment is a rule of the raw let-iter theory, at any
choice of pure effect: the fragment is a genuine sub-theory. -/
theorem toRawEquiv (pureEff : ε) {a b : Tm ν Φ n} (h : ObsTheory a b) :
    RawEquiv pureEff a b := by
  induction h with
  | refl a => exact .refl a
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | op _ ih => exact .op ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .abort ih
  | iter _ _ ih₁ ih₂ => exact .iter ih₁ ih₂
  | letEta a => exact .ax (.structural (.letEta a))
  | pairBeta a b c => exact .ax (.structural (.pairBeta a b c))
  | caseBetaL e l r => exact .ax (.structural (.caseBetaL e l r))
  | caseBetaR e l r => exact .ax (.structural (.caseBetaR e l r))
  | emptyInitial a b c => exact .ax (.structural (.emptyInitial a b c))
  | bindOp a c => exact .ax (.sequencing (.bindOp a c))
  | bindLet a b c => exact .ax (.sequencing (.bindLet a b c))
  | bindLetPair e c d => exact .ax (.sequencing (.bindLetPair e c d))
  | bindLetCase e l r d => exact .ax (.sequencing (.bindLetCase e l r d))
  | bindPair a c => exact .ax (.sequencing (.bindPair a c))
  | bindCase e l r => exact .ax (.sequencing (.bindCase e l r))
  | iterBind a b => exact .ax (.iteration (.iterBind a b))
  | fixpoint a b => exact .ax (.iteration (.fixpoint a b))
  | letBeta a b ha => exact .ax (.structural (.letBeta (Pure.of_inert ha)))
  | naturality a b k => exact .ax (.iteration (.naturality a b k))
  | codiagonal a b => exact .ax (.iteration (.codiagonal a b))
  | uniformity hh _ ih => exact .uniformity (Pure.of_inert hh) ih

end ObsTheory

/-! ## The purity contract

`Pure` and `IsPure` are syntactic: they constrain terms and opcodes, not the
instruction relation. An instruction model that calls an opcode pure while
letting it move the machine state, fail, or behave nondeterministically makes
`letBeta` and `uniformity` unsound, because both duplicate or relocate a pure
subterm. `RespectsPure` is the contract that rules this out; it is the
operational analogue of `Silmaril.Isotope.Semantics.InstructionModel.RespectsPure`
and of `Silmaril.Isotope.LambdaSSA.Tm.Eval.state_eq_of_pure`.

The contract is *necessary* for any instruction-level formulation of these two
laws, and `counterInstr_not_respectsPure` with `not_obs_letBeta` is that half.
It is not sufficient, and at the level of `Tm.Obs` it is not even the relevant
condition: `not_obs_letBeta_abort` breaks `letBeta` for an instruction relation
that satisfies `RespectsPure` vacuously, and `Tm.Obs` quantifies over the fault
oracle and the primitive-divergence oracle independently of `instr` anyway. The
condition that does work is `Semantics.Inert` on the substituted term, used by
`obs_letBeta` and `obs_uniformity`, and it needs no contract. -/

/-- An instruction relation honours a purity predicate on opcodes when every
pure opcode is total, state-preserving and deterministic. -/
structure RespectsPure {α : Type v} {σ : Type w}
    (instr : Φ → Value α → σ → Value α → σ → Prop) (pure : Φ → Prop) : Prop where
  /-- A pure opcode has a transition at every argument and state. -/
  total : ∀ f, pure f → ∀ (a : Value α) (s : σ), ∃ value, instr f a s value s
  /-- A pure opcode leaves the machine state alone. -/
  stateless : ∀ f, pure f → ∀ (a : Value α) (s : σ) (value : Value α) (s' : σ),
    instr f a s value s' → s' = s
  /-- A pure opcode has at most one result. -/
  deterministic : ∀ f, pure f → ∀ (a : Value α) (s : σ) (v v' : Value α) (s' s'' : σ),
    instr f a s v s' → instr f a s v' s'' → v = v'

/-! ## The axioms that are not operationally valid -/

/-- An instruction relation that declares its single opcode pure and yet
increments the machine state. -/
def counterInstr : Unit → Value Unit → Nat → Value Unit → Nat → Prop :=
  fun _ _ s value s' => value = .unit ∧ s' = s + 1

/-- The empty instruction relation: there are no opcodes to run. -/
def emptyInstr : Empty → Value Unit → Unit → Value Unit → Unit → Prop := fun f => f.elim

/-- The empty free-variable environment over the unit value carrier. -/
def emptyFree : FreeEnv Empty Unit := fun x => x.elim

/-- The separating model violates the purity contract: it moves the state. -/
theorem counterInstr_not_respectsPure : ¬ RespectsPure counterInstr (fun _ => True) := by
  intro h
  have := h.stateless () trivial .unit 0 .unit 1 ⟨rfl, rfl⟩
  omega

/-- `letBeta` fails: substituting a let-bound operation under a binder that uses
its result twice runs the operation twice, and `Pure` places no constraint on
the instruction relation. The two terms are the `letBeta` instance at
`a = .op f .unit` and `b = .pair (.bv 0) (.bv 0)`, which belongs to the scheme
whenever the opcode is declared pure; `counterInstr_not_respectsPure` shows the
separating model is exactly one that breaks `RespectsPure`. -/
theorem not_obs_letBeta :
    ¬ Tm.Obs.{0, 0, 0, 0} (ν := Empty) (Φ := Unit) (n := 0)
      (.let₁ (.op () .unit) (.pair (.bv 0) (.bv 0)))
      (.pair (.op () .unit) (.op () .unit)) := by
  intro h
  have run : Semantics.Eval counterInstr emptyFree Fin.elim0
      ((.let₁ (.op () .unit) (.pair (.bv 0) (.bv 0))) : Tm Empty Unit 0) 0
      (.pair .unit .unit) 1 :=
    .let₁ (.op .unit ⟨rfl, rfl⟩) (.pair .bv .bv)
  have bad := h.eval.mp run
  cases bad with
  | pair left right =>
      cases left with
      | op argL stepL =>
          cases argL
          cases right with
          | op argR stepR =>
              cases argR
              have hl : _ ∧ _ := stepL
              have hr : _ ∧ _ := stepR
              have hl2 := hl.2
              have hr2 := hr.2
              omega

/-- The empty instruction relation satisfies the purity contract vacuously:
there is no opcode to break it. -/
theorem emptyInstr_respectsPure (pure : Empty → Prop) : RespectsPure emptyInstr pure where
  total := fun f => f.elim
  stateless := fun f => f.elim
  deterministic := fun f => f.elim

/-- The separating term for `letBeta` below really is syntactically pure:
`Pure` admits `abort`, which has no evaluation rule at all. -/
theorem pure_abort_unit {ε : Type w} [HasEff Φ ε] (pureEff : ε) :
    Pure pureEff ((.abort .unit) : Tm ν Φ n) := .abort .unit

/-- **The purity contract is not merely insufficient for `letBeta`, it is
irrelevant.** `RespectsPure` constrains the instruction relation, but `Pure`
admits `abort`, `let₂` and `case`, which are stuck on the wrong value, and
`Tm.Obs` quantifies over the fault oracle and the primitive-divergence oracle
independently of `instr`. Here the instruction set is empty, so
`emptyInstr_respectsPure` holds at every purity predicate, yet the `letBeta`
instance at `a = .abort .unit`, `b = .unit` is still false: the left-hand side
is stuck and the right-hand side returns. This is why `ObsTheory.letBeta` is
guarded by `Semantics.Inert` rather than by a contract. -/
theorem not_obs_letBeta_abort :
    ¬ Tm.Obs.{0, 0, 0, 0} (ν := Empty) (Φ := Empty) (n := 0)
      (.let₁ (.abort .unit) .unit) .unit := by
  intro hobs
  have run : Semantics.Eval emptyInstr emptyFree Fin.elim0
      ((.unit) : Tm Empty Empty 0) () .unit () := .unit
  cases hobs.eval.mpr run with | let₁ arg _ => cases arg

/-- `unitEta` fails: the operational semantics does not know that a term typed
at the unit type produces `Value.unit`, because `Value α` is untyped. -/
theorem not_obs_unitEta :
    ¬ Tm.Obs.{0, 0, 0, 0} (ν := Empty) (Φ := Empty) (n := 0)
      (.let₁ (.pair .unit .unit) .unit) (.pair .unit .unit) := by
  intro h
  have run : Semantics.Eval emptyInstr emptyFree Fin.elim0
      ((.let₁ (.pair .unit .unit) .unit) : Tm Empty Empty 0) () .unit () :=
    .let₁ (.pair .unit .unit) .unit
  cases h.eval.mp run

/-- `pairEta` fails: pair elimination is stuck unless the scrutinee actually
produces a pair, so the left-hand side has no result where the right-hand side
terminates. -/
theorem not_obs_pairEta :
    ¬ Tm.Obs.{0, 0, 0, 0} (ν := Empty) (Φ := Empty) (n := 0)
      (.let₂ .unit (.pair (.bv 1) (.bv 0))) .unit := by
  intro h
  have run : Semantics.Eval emptyInstr emptyFree Fin.elim0
      ((.unit) : Tm Empty Empty 0) () .unit () := .unit
  cases h.eval.mpr run with | let₂ arg _ => cases arg

/-- `caseEta` fails for the same reason: case analysis is stuck unless the
scrutinee produces an injection. -/
theorem not_obs_caseEta :
    ¬ Tm.Obs.{0, 0, 0, 0} (ν := Empty) (Φ := Empty) (n := 0)
      (.case .unit (.inl (.bv 0)) (.inr (.bv 0))) .unit := by
  intro h
  have run : Semantics.Eval emptyInstr emptyFree Fin.elim0
      ((.unit) : Tm Empty Empty 0) () .unit () := .unit
  cases h.eval.mpr run with
  | case_inl scrutinee _ => cases scrutinee
  | case_inr scrutinee _ => cases scrutinee
/-! ## The eta laws under a canonical-forms hypothesis

The three eta failures above are all instances of the same gap: `Value α` has
no typing, so nothing forces a term to return a value of the expected shape.
Naming that gap as a hypothesis makes all three eta laws provable, and makes
them usable inside a theory: `ObsEtaTheory` below is `ObsTheory` closed under
the congruences and the three conditional eta rules, and it is sound. The gap
is therefore a hypothesis someone can discharge, not a paragraph. Discharging
it for a typed term would need a value-typing development, of which
`Silmaril.Isotope.LambdaSSA.Semantics.ValueTyped` is the shape.
-/

/-- Canonical forms at the unit type: every result of `t` is `Value.unit`. -/
def Tm.ReturnsUnit.{uu, vv, ww, xx} {ν : Type xx} {Φ : Type uu} {n : Nat}
    (t : Tm ν Φ n) : Prop :=
  ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {free : FreeEnv ν α} {bound : BoundEnv α n} {s s' : σ} {value : Value α},
    Semantics.Eval instr free bound t s value s' → value = .unit

/-- Canonical forms at a product type: every result of `t` is a `Value.pair`. -/
def Tm.ReturnsPair.{uu, vv, ww, xx} {ν : Type xx} {Φ : Type uu} {n : Nat}
    (t : Tm ν Φ n) : Prop :=
  ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {free : FreeEnv ν α} {bound : BoundEnv α n} {s s' : σ} {value : Value α},
    Semantics.Eval instr free bound t s value s' → ∃ l r, value = .pair l r

/-- Canonical forms at a coproduct type: every result of `t` is an injection. -/
def Tm.ReturnsSum.{uu, vv, ww, xx} {ν : Type xx} {Φ : Type uu} {n : Nat}
    (t : Tm ν Φ n) : Prop :=
  ∀ {α : Type vv} {σ : Type ww} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {free : FreeEnv ν α} {bound : BoundEnv α n} {s s' : σ} {value : Value α},
    Semantics.Eval instr free bound t s value s' →
      (∃ l, value = .inl l) ∨ ∃ r, value = .inr r

/-- The older of two newest binders is bound variable one. -/
theorem extend_extend_one {α : Type v} {m : Nat} (bound : BoundEnv α m)
    (left right : Value α) : extend (extend bound left) right 1 = left := rfl

/-- `unitEta` holds for a term that is known to return `Value.unit`. -/
theorem obs_unitEta_of_canonical (a : Tm ν Φ n) (hcanon : Tm.ReturnsUnit.{u, v, w, x} a) :
    Tm.Obs.{u, v, w, x} (.let₁ a .unit) a where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₁ arg body => cases body; exact (hcanon arg) ▸ arg
    · intro r
      have := hcanon r
      subst this
      exact .let₁ r .unit
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | let₁_arg arg => exact arg
      | let₁_body _ body => cases body
    · exact .let₁_arg
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₁_arg arg => exact arg
        | let₁_body _ body => cases body.unfold with | core c => cases c
    · exact fun d => .fold_core (.let₁_arg d)

/-- `pairEta` holds for a term that is known to return a pair. Only the
right-to-left direction uses the hypothesis: pair elimination followed by
repairing is stuck exactly where the scrutinee fails to produce a pair. -/
theorem obs_pairEta_of_canonical (a : Tm ν Φ n) (hcanon : Tm.ReturnsPair.{u, v, w, x} a) :
    Tm.Obs.{u, v, w, x} (.let₂ a (.pair (.bv 1) (.bv 0))) a where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro r
      cases r with
      | let₂ arg body =>
          cases body with
          | pair left right =>
              obtain ⟨rfl, rfl⟩ := eval_bv_result left
              obtain ⟨rfl, rfl⟩ := eval_bv_result right
              exact arg
    · intro r
      obtain ⟨l, rr, rfl⟩ := hcanon r
      exact .let₂ r (.pair .bv .bv)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | let₂_arg arg => exact arg
      | let₂_body _ body =>
          cases body with
          | pair_left left => cases left
          | pair_right _ right => cases right
    · exact .let₂_arg
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | let₂_arg arg => exact arg
        | let₂_body _ body =>
            cases body.unfold with
            | core c => cases c with
              | pair_left left => cases left.unfold with | core c₂ => cases c₂
              | pair_right _ right => cases right.unfold with | core c₂ => cases c₂
    · exact fun d => .fold_core (.let₂_arg d)

/-- `caseEta` holds for a term that is known to return an injection. -/
theorem obs_caseEta_of_canonical (e : Tm ν Φ n) (hcanon : Tm.ReturnsSum.{u, v, w, x} e) :
    Tm.Obs.{u, v, w, x} (.case e (.inl (.bv 0)) (.inr (.bv 0))) e where
  eval := by
    intro α σ instr free bound s s' value
    constructor
    · rintro run
      cases run with
      | case_inl scrutinee branch =>
          cases branch with | inl bv => obtain ⟨rfl, rfl⟩ := eval_bv_result bv; exact scrutinee
      | case_inr scrutinee branch =>
          cases branch with | inr bv => obtain ⟨rfl, rfl⟩ := eval_bv_result bv; exact scrutinee
    · intro run
      rcases hcanon run with ⟨l, rfl⟩ | ⟨r, rfl⟩
      · exact .case_inl run (.inl .bv)
      · exact .case_inr run (.inr .bv)
  fault := by
    intro α σ instr faults free bound s s'
    constructor
    · rintro f
      cases f with
      | case_arg arg => exact arg
      | case_inl _ branch => cases branch with | inl bv => cases bv
      | case_inr _ branch => cases branch with | inr bv => cases bv
    · exact .case_arg
  diverges := by
    intro α σ instr prim free bound s
    constructor
    · intro d
      cases d.unfold with
      | core core => cases core with
        | case_scrutinee arg => exact arg
        | case_inl _ branch =>
            cases branch.unfold with
            | core c => cases c with | inl bv => cases bv.unfold with | core c₂ => cases c₂
        | case_inr _ branch =>
            cases branch.unfold with
            | core c => cases c with | inr bv => cases bv.unfold with | core c₂ => cases c₂
    · exact fun d => .fold_core (.case_scrutinee d)

/-! ## The conditional fragment -/

/-- `ObsTheory` extended with the three eta laws, each carrying the
canonical-forms hypothesis for its own type former. Unlike `ObsTheory` this
relation mentions the value and machine-state universes, because the hypotheses
do; `ObsTheory.sound` is left untouched for callers that have no such
hypothesis to offer. -/
inductive ObsEtaTheory.{uu, vv, ww, xx} {ν : Type xx} {Φ : Type uu} :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  /-- Every unconditional rule. -/
  | obs {n : Nat} {a b : Tm ν Φ n} : ObsTheory a b → ObsEtaTheory a b
  /-- Symmetry. -/
  | symm {n : Nat} {a b : Tm ν Φ n} : ObsEtaTheory a b → ObsEtaTheory b a
  /-- Transitivity. -/
  | trans {n : Nat} {a b c : Tm ν Φ n} : ObsEtaTheory a b → ObsEtaTheory b c → ObsEtaTheory a c
  /-- Congruence for a primitive application. -/
  | op {n : Nat} {f : Φ} {a a' : Tm ν Φ n} :
      ObsEtaTheory a a' → ObsEtaTheory (.op f a) (.op f a')
  /-- Congruence for sequencing. -/
  | let₁ {n : Nat} {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)} :
      ObsEtaTheory a a' → ObsEtaTheory b b' → ObsEtaTheory (.let₁ a b) (.let₁ a' b')
  /-- Congruence for pairing. -/
  | pair {n : Nat} {a a' b b' : Tm ν Φ n} :
      ObsEtaTheory a a' → ObsEtaTheory b b' → ObsEtaTheory (.pair a b) (.pair a' b')
  /-- Congruence for pair elimination. -/
  | let₂ {n : Nat} {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 2)} :
      ObsEtaTheory a a' → ObsEtaTheory b b' → ObsEtaTheory (.let₂ a b) (.let₂ a' b')
  /-- Congruence for left injection. -/
  | inl {n : Nat} {a a' : Tm ν Φ n} : ObsEtaTheory a a' → ObsEtaTheory (.inl a) (.inl a')
  /-- Congruence for right injection. -/
  | inr {n : Nat} {a a' : Tm ν Φ n} : ObsEtaTheory a a' → ObsEtaTheory (.inr a) (.inr a')
  /-- Congruence for case analysis. -/
  | case {n : Nat} {e e' : Tm ν Φ n} {l l' r r' : Tm ν Φ (n + 1)} :
      ObsEtaTheory e e' → ObsEtaTheory l l' → ObsEtaTheory r r' →
      ObsEtaTheory (.case e l r) (.case e' l' r')
  /-- Congruence for empty elimination. -/
  | abort {n : Nat} {a a' : Tm ν Φ n} : ObsEtaTheory a a' → ObsEtaTheory (.abort a) (.abort a')
  /-- Congruence for iteration. -/
  | iter {n : Nat} {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)} :
      ObsEtaTheory a a' → ObsEtaTheory b b' → ObsEtaTheory (.iter a b) (.iter a' b')
  /-- Unit eta, for a term known to return `Value.unit`. -/
  | unitEta {n : Nat} (a : Tm ν Φ n) (hcanon : Tm.ReturnsUnit.{uu, vv, ww, xx} a) :
      ObsEtaTheory (.let₁ a .unit) a
  /-- Product eta, for a term known to return a pair. -/
  | pairEta {n : Nat} (a : Tm ν Φ n) (hcanon : Tm.ReturnsPair.{uu, vv, ww, xx} a) :
      ObsEtaTheory (.let₂ a (.pair (.bv 1) (.bv 0))) a
  /-- Coproduct eta, for a term known to return an injection. -/
  | caseEta {n : Nat} (e : Tm ν Φ n) (hcanon : Tm.ReturnsSum.{uu, vv, ww, xx} e) :
      ObsEtaTheory (.case e (.inl (.bv 0)) (.inr (.bv 0))) e

namespace ObsEtaTheory

/-- **Conditional soundness.** Every equation of the extended fragment
identifies observationally equivalent terms, given the canonical-forms
hypotheses its eta rules carry. -/
theorem sound {a b : Tm ν Φ n} (h : ObsEtaTheory.{u, v, w, x} a b) :
    Tm.Obs.{u, v, w, x} a b := by
  induction h with
  | obs h => exact h.sound
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | op _ ih => exact Tm.Obs.op _ ih
  | let₁ _ _ ih₁ ih₂ => exact Tm.Obs.let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact Tm.Obs.pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact Tm.Obs.let₂ ih₁ ih₂
  | inl _ ih => exact Tm.Obs.inl ih
  | inr _ ih => exact Tm.Obs.inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact Tm.Obs.case ih₁ ih₂ ih₃
  | abort _ ih => exact Tm.Obs.abort ih
  | iter _ _ ih₁ ih₂ => exact Tm.Obs.iter ih₁ ih₂
  | unitEta a hcanon => exact obs_unitEta_of_canonical a hcanon
  | pairEta a hcanon => exact obs_pairEta_of_canonical a hcanon
  | caseEta e hcanon => exact obs_caseEta_of_canonical e hcanon

variable {ε : Type w} [HasEff Φ ε]

/-- The extended fragment is still a sub-theory of the raw let-iter theory: the
canonical-forms hypotheses restrict which instances are *sound*, not which are
*derivable*. -/
theorem toRawEquiv (pureEff : ε) {a b : Tm ν Φ n} (h : ObsEtaTheory.{u, v, w, x} a b) :
    RawEquiv pureEff a b := by
  induction h with
  | obs h => exact h.toRawEquiv pureEff
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | op _ ih => exact .op ih
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .abort ih
  | iter _ _ ih₁ ih₂ => exact .iter ih₁ ih₂
  | unitEta a _ => exact .ax (.structural (.unitEta a))
  | pairEta a _ => exact .ax (.structural (.pairEta a))
  | caseEta e _ => exact .ax (.structural (.caseEta e))

end ObsEtaTheory

end Silmaril.Isotope.LetIter.LocallyNameless
