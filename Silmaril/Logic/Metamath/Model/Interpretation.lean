module

public import Silmaril.Logic.Metamath.Model.Soundness
public import Silmaril.Logic.Metatheory.ArithmeticSoundness

@[expose] public section

/-!
# Interpretations of grammars and arithmetical soundness

An interpretation `I : Grammar.Interp G' G` of a grammar `G'` (for instance a
language of arithmetic) in a grammar `G` maps typecodes and variables
(injectively), and sends each syntax rule of `G'` to a well-sorted tree of `G`
in the rule's argument variables: a derived operation. It translates trees
(`Interp.tr`, substituting the translated arguments into the rule's tree), and
tree assertions (`Interp.trAssertion`).

A model `M` of `G` induces a model `I.pull M` of `G'`: the domain of a sort is
the domain of its image, a rule denotes the value of its tree, freshness and
truth are those of `M`. The value of a translated tree is the value of the
tree in the induced model (`Interp.value_tr`), so `M` satisfies the
translation of a well-formed assertion exactly when the induced model
satisfies the assertion; we use the direction `Interp.satisfies_pull`.

Satisfaction is invariant under isomorphisms of models (`Model.Iso`), and
every model is isomorphic to the model it induces along the identity
interpretation (`Interp.pullIdIso`). Hence
the general arithmetical soundness theorem (`Model.arithSound_of_iso`): let
`N` be the standard model of an arithmetic grammar `G'`, and `M` a model of
well-formed axioms `Γ` whose induced model along `I` is isomorphic to `N` (the
interpreted natural numbers are the standard ones). Then every well-formed
arithmetic assertion whose translation `Γ` derives is true in `N`: `Γ` is
arithmetically sound for `I` (`Metatheory.ArithLanguage.ArithSound`), and in
particular Σ₁-sound for any class of Σ₁ sentences.
-/

namespace Silmaril.Logic.Metamath

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel

universe u w

variable {C V L C' V' L' : Type u}

namespace Grammar

/-- The context of the tree interpreting the rule `l` of `G'`: the images of
its argument variables, at the images of their sorts. -/
def Interp.BodyCtx (G' : Grammar L' C' V') (sort : C' → C) (var : V' → V) (l : L') (w : V)
    (c : C) : Prop :=
  ∃ j : Fin (G'.rule l).arity, var ((G'.rule l).args.get j).2 = w ∧
    sort ((G'.rule l).args.get j).1 = c

/-- An interpretation of the grammar `G'` in the grammar `G`. -/
structure Interp (G' : Grammar L' C' V') (G : Grammar L C V) where
  sort : C' → C
  var : V' → V
  var_injective : Function.Injective var
  sort_mem : ∀ s ∈ G'.sorts, sort s ∈ G.sorts
  prov : ∀ {c s : C'}, G'.prov c = some s → G.prov (sort c) = some (sort s)
  /-- The tree of `G` interpreting the rule `l` of `G'`. -/
  body : L' → Tree L V
  body_sort : ∀ l, G.HasSort (Interp.BodyCtx G' sort var l) (body l) (sort (G'.rule l).tc)

namespace Interp

variable {G' : Grammar L' C' V'} {G : Grammar L C V} (I : Interp G' G)

section Translation

variable [DecidableEq V]

/-- The argument tree for the variable `w` of the tree of a rule with
arguments `ps`. -/
def argTree : List (C' × V') → List (Tree L V) → V → Tree L V
  | p :: ps, t :: ts, w => if I.var p.2 = w then t else argTree ps ts w
  | _, _, w => .var w

theorem argTree_get {ps : List (C' × V')} (hnd : (ps.map Prod.snd).Nodup) {ts : List (Tree L V)}
    (hlen : ts.length = ps.length) (j : Fin ps.length) :
    I.argTree ps ts (I.var (ps.get j).2) = ts[j.1]'(j.2.trans_eq hlen.symm) := by
  induction ps generalizing ts with
  | nil => exact j.elim0
  | cons p ps ih =>
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [argTree]
      · have hne : I.var p.2 ≠ I.var (ps[j.1]).2 := fun e =>
          hnd.1 (ps[j.1]) (List.getElem_mem _) (I.var_injective e).symm
        simp only [argTree, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ, hne,
          ite_false]
        simpa using ih hnd.2 (by simpa using hlen) j

mutual

/-- The translation of a tree of `G'` into a tree of `G`. -/
def tr : Tree L' V' → Tree L V
  | .var v => .var (I.var v)
  | .node l args => (I.body l).subst (I.argTree (G'.rule l).args (trList args))
termination_by structural t => t

/-- Translate each tree of a list. -/
def trList : List (Tree L' V') → List (Tree L V)
  | [] => []
  | t :: ts => tr t :: trList ts
termination_by structural ts => ts

end

theorem trList_eq (ts : List (Tree L' V')) : I.trList ts = ts.map I.tr := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [trList, ih]

@[simp] theorem tr_var (v : V') : I.tr (.var v) = .var (I.var v) := by simp [tr]

theorem tr_node (l : L') (args : List (Tree L' V')) :
    I.tr (.node l args) = (I.body l).subst (I.argTree (G'.rule l).args (args.map I.tr)) := by
  rw [tr, trList_eq]

/-- The context of a translated tree. -/
abbrev trCtx (ctx' : V' → C' → Prop) (w : V) (c : C) : Prop :=
  ∃ v s, I.var v = w ∧ I.sort s = c ∧ ctx' v s

theorem argTree_rule {l : L'} {args : List (Tree L' V')}
    (hlen : args.length = (G'.rule l).arity) (j : Fin (G'.rule l).arity) :
    I.argTree (G'.rule l).args (args.map I.tr) (I.var ((G'.rule l).args.get j).2) =
      I.tr (args[j.1]'(j.2.trans_eq hlen.symm)) := by
  rw [I.argTree_get (G'.rule l).args_nodup (by simpa using hlen) j]
  simp

/-- Translation preserves sorts. -/
theorem hasSort_tr {ctx' : V' → C' → Prop} {t : Tree L' V'} {s : C'}
    (h : G'.HasSort ctx' t s) : G.HasSort (I.trCtx ctx') (I.tr t) (I.sort s) := by
  induction h with
  | @var v s hv => rw [tr_var]; exact .var ⟨v, s, rfl, rfl, hv⟩
  | @node l args hlen hargs ih =>
    rw [tr_node]
    refine (I.body_sort l).subst fun w c ⟨j, hw, hc⟩ => ?_
    subst hw hc
    rw [I.argTree_rule hlen j]
    have hj : (args[j.1]'(j.2.trans_eq hlen.symm), (G'.rule l).args.get j) ∈
        args.zip (G'.rule l).args := by
      have hj' : j.1 < (args.zip (G'.rule l).args).length := by simp [hlen]
      simpa [List.getElem_zip] using List.getElem_mem hj'
    exact ih _ hj

omit [DecidableEq V] in
theorem trCtx_synCtx_le {ctx' : V' → C' → Prop} (w : V) (c : C)
    (h : I.trCtx (G'.synCtx ctx') w c) : G.synCtx (I.trCtx ctx') w c := by
  obtain ⟨v, s, hv, hs, hctx, hsort⟩ := h
  exact ⟨⟨v, s, hv, hs, hctx⟩, hs ▸ I.sort_mem s hsort⟩

end Translation

/-! ## Induced models -/

section Pull

variable (M : Model.{u, w} G)

/-- The valuation of the tree of the rule `l` given by argument values. -/
noncomputable def argVal {l : L'}
    (args : (j : Fin (G'.rule l).arity) → M.Carrier (I.sort ((G'.rule l).args.get j).1)) :
    ∀ w c, BodyCtx G' I.sort I.var l w c → M.Carrier c :=
  fun _ _ h => M.transport (Classical.choose_spec h).2 (args (Classical.choose h))

theorem argVal_eq {l : L'}
    (args : (j : Fin (G'.rule l).arity) → M.Carrier (I.sort ((G'.rule l).args.get j).1))
    {w : V} {c : C} (h : BodyCtx G' I.sort I.var l w c) (j : Fin (G'.rule l).arity)
    (hj : I.var ((G'.rule l).args.get j).2 = w) (hc : I.sort ((G'.rule l).args.get j).1 = c) :
    I.argVal M args w c h = M.transport hc (args j) := by
  have key : ∀ (j₀ : Fin (G'.rule l).arity) (e : I.sort ((G'.rule l).args.get j₀).1 = c),
      j₀ = j → M.transport e (args j₀) = M.transport hc (args j) := by
    rintro j₀ e rfl
    rfl
  refine key _ _ ?_
  have h₀ := (Classical.choose_spec h).1.trans hj.symm
  have := I.var_injective h₀
  have hmap : ((G'.rule l).args.map Prod.snd)[(Classical.choose h).1]'(by simp) =
      ((G'.rule l).args.map Prod.snd)[j.1]'(by simp) := by simpa using this
  exact Fin.ext ((List.Nodup.getElem_inj_iff (G'.rule l).args_nodup).1 hmap)

/-- The model of `G'` induced by a model of `G` along the interpretation. -/
noncomputable abbrev pull : Model.{u, w} G' where
  Carrier s := M.Carrier (I.sort s)
  op {s} o args := M.transport (congrArg I.sort o.2) (M.value (I.argVal M args) (I.body o.1)
    (I.body_sort o.1))
  Fresh a b := M.Fresh a b
  fresh_symm := M.fresh_symm
  fresh_op {s t} a o args h := by
    obtain ⟨l, rfl⟩ := o
    refine M.fresh_eval _ a _ _ fun w _ c hb => ?_
    exact (M.fresh_transport a _ _).2 (h _)
  exists_fresh s hs W :=
    (M.exists_fresh (I.sort s) (I.sort_mem s hs) (W.map fun w => ⟨I.sort w.1, w.2⟩)).imp
      fun _ h w hw => h _ (List.mem_map_of_mem hw)
  IsTrue hc a := M.IsTrue (I.prov hc) a

variable [DecidableEq V]

/-- The value of a translated tree is the value of the tree in the induced
model, under the induced valuation. -/
theorem value_tr {ctx' : V' → C' → Prop} {ctxT : V → C → Prop}
    (ρ : ∀ w c, ctxT w c → M.Carrier c) (ρ' : ∀ v s, ctx' v s → M.Carrier (I.sort s))
    (hctx : ∀ w c, I.trCtx ctx' w c → ctxT w c)
    (hρ : ∀ v s hv, ρ (I.var v) (I.sort s) (hctx _ _ ⟨v, s, rfl, rfl, hv⟩) = ρ' v s hv)
    (t : Tree L' V') {s : C'} (h : G'.HasSort ctx' t s) (ht : G.HasSort ctxT (I.tr t) (I.sort s)) :
    M.value ρ (I.tr t) ht = (I.pull M).value ρ' t h := by
  induction t using Tree.induction generalizing s with
  | var v =>
    have hv := HasSort.var_iff.1 h
    unfold Model.value
    rw [eval_congr (I.tr_var v) ht (.var (hctx _ _ ⟨v, s, rfl, rfl, hv⟩)), eval_var, eval_var]
    exact hρ v s hv
  | node l args ih =>
    obtain ⟨hs, hlen, -⟩ := h.node_inv
    subst hs
    have hσ : ∀ w c, BodyCtx G' I.sort I.var l w c →
        G.HasSort ctxT (I.argTree (G'.rule l).args (args.map I.tr) w) c := by
      rintro w c ⟨j, rfl, rfl⟩
      rw [I.argTree_rule hlen j]
      exact (I.hasSort_tr (h.child j)).mono hctx
    unfold Model.value
    rw [eval_congr (I.tr_node l args) ht ((I.body_sort l).subst hσ),
      eval_subst hσ (I.body l) (I.body_sort l), eval_node]
    change _ = M.value (I.argVal M _) (I.body l) (I.body_sort l)
    refine M.value_agree _ _ _ fun w _ c hb hb' => ?_
    obtain ⟨j, rfl, rfl⟩ := hb
    rw [I.argVal_eq M _ hb' j rfl rfl]
    change M.value ρ _ _ = (I.pull M).value ρ' _ _
    unfold Model.value
    rw [eval_congr (I.argTree_rule hlen j) _ ((I.hasSort_tr (h.child j)).mono hctx)]
    exact ih _ (List.getElem_mem _) _ _

end Pull

/-! ## Translating assertions -/

section Assertions

variable [DecidableEq V]

/-- The translation of a tree expression. -/
def trExpr (e : TExpr L' C' V') : TExpr L C V := ⟨I.sort e.tc, I.tr e.tree⟩

/-- The translation of a hypothesis. -/
def trHyp : THyp L' C' V' → THyp L C V
  | .float c v => .float (I.sort c) (I.var v)
  | .ess e => .ess (I.trExpr e)

/-- The translation of a tree assertion. -/
def trAssertion (A : TAssertion L' C' V') : TAssertion L C V :=
  ⟨A.dv.map (Prod.map I.var I.var), A.hyps.map I.trHyp, I.trExpr A.concl⟩

variable {I}

theorem ctx_trAssertion {A : TAssertion L' C' V'} {w : V} {c : C} :
    (I.trAssertion A).ctx w c ↔ I.trCtx A.ctx w c := by
  simp only [TAssertion.ctx, trAssertion, List.mem_map, trCtx]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h with
    | float s v =>
      simp only [trHyp, THyp.float.injEq] at he
      exact ⟨v, s, he.2, he.1, hh⟩
    | ess e => simp [trHyp] at he
  · rintro ⟨v, s, rfl, rfl, hh⟩
    exact ⟨_, hh, rfl⟩

theorem mem_essentials_trAssertion {A : TAssertion L' C' V'} {e : TExpr L C V} :
    e ∈ (I.trAssertion A).essentials ↔ ∃ e' ∈ A.essentials, I.trExpr e' = e := by
  simp only [TAssertion.essentials, trAssertion]
  rw [List.filterMap_map, List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h with
    | float s v => simp [trHyp] at he
    | ess e' =>
      simp only [trHyp, Function.comp_apply, Option.some.injEq] at he
      exact ⟨e', TAssertion.mem_essentials.2 hh, he⟩
  · rintro ⟨e', he', rfl⟩
    exact ⟨_, TAssertion.mem_essentials.1 he', rfl⟩

variable (I)

/-- A model satisfying the translation of a well-formed assertion induces a
model satisfying the assertion. -/
theorem satisfies_pull (M : Model.{u, w} G) {A : TAssertion L' C' V'} (hA : A.WellFormed G')
    (h : M.Satisfies (I.trAssertion A)) : (I.pull M).Satisfies A := by
  classical
  intro ρ' hdv hess
  have hfun := TAssertion.functional_ctx hA.floats_nodup
  let ρ : M.Valuation (I.trAssertion A).ctx := fun w c h =>
    have hx := ctx_trAssertion.1 h.1
    have hs := Classical.choose_spec (Classical.choose_spec hx)
    M.transport hs.2.1 (ρ' (Classical.choose hx) (Classical.choose (Classical.choose_spec hx))
      ⟨hs.2.2, hA.float_sort _ _ hs.2.2⟩ : M.Carrier (I.sort _))
  have hρ : ∀ v s (hv : A.ctx v s) (hs : s ∈ G'.sorts) h,
      ρ (I.var v) (I.sort s) h = ρ' v s ⟨hv, hs⟩ := by
    intro v s hv hs h
    have key : ∀ (v₀ : V') (s₀ : C') (e : I.sort s₀ = I.sort s) (h₀ : G'.synCtx A.ctx v₀ s₀),
        v₀ = v → s₀ = s →
          M.transport e (ρ' v₀ s₀ h₀ : M.Carrier (I.sort s₀)) = ρ' v s ⟨hv, hs⟩ := by
      rintro v₀ s₀ e h₀ rfl rfl
      rfl
    have hx := ctx_trAssertion.1 h.1
    have hsp := Classical.choose_spec (Classical.choose_spec hx)
    have hv₀ : Classical.choose hx = v := I.var_injective hsp.1
    exact key _ _ _ _ hv₀ (hfun v _ _ ((congrArg (fun a => A.ctx a _) hv₀).mp hsp.2.2) hv)
  have hctx : ∀ w c, I.trCtx (G'.synCtx A.ctx) w c → G.synCtx (I.trAssertion A).ctx w c :=
    fun w c h => let ⟨h₁, h₂⟩ := I.trCtx_synCtx_le w c h; ⟨ctx_trAssertion.2 h₁, h₂⟩
  have hval : ∀ (t : Tree L' V') {s : C'} (ht : G'.HasSort (G'.synCtx A.ctx) t s)
      (ht' : G.HasSort (G.synCtx (I.trAssertion A).ctx) (I.tr t) (I.sort s)),
      M.value ρ (I.tr t) ht' = (I.pull M).value ρ' t ht :=
    I.value_tr M ρ ρ' hctx (fun v s hv => hρ v s hv.1 hv.2 (hctx _ _ ⟨v, s, rfl, rfl, hv⟩))
  have hdvT : M.DVHolds ρ (I.trAssertion A).dv := by
    intro w₁ w₂ hmem hne c d h₁ h₂
    obtain ⟨⟨x, y⟩, hxy, he⟩ := List.mem_map.1 hmem
    simp only [Prod.map, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨v, s, hv, rfl, hvs⟩ := ctx_trAssertion.1 h₁.1
    obtain ⟨v', s', hv', rfl, hvs'⟩ := ctx_trAssertion.1 h₂.1
    obtain rfl := I.var_injective hv
    obtain rfl := I.var_injective hv'
    have hs₁ : s ∈ G'.sorts := hA.float_sort _ _ hvs
    have hs₂ : s' ∈ G'.sorts := hA.float_sort _ _ hvs'
    rw [hρ _ _ hvs hs₁ h₁, hρ _ _ hvs' hs₂ h₂]
    exact hdv _ _ hxy (fun e => hne (e ▸ rfl)) _ _ _ _
  have hessT : ∀ e ∈ (I.trAssertion A).essentials, M.Holds ρ e := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_essentials_trAssertion.1 he
    obtain ⟨s, hs, ht, htrue⟩ := hess e' he'
    have ht' : G.HasSort (G.synCtx (I.trAssertion A).ctx) (I.tr e'.tree) (I.sort s) :=
      (I.hasSort_tr ht).mono hctx
    exact ⟨I.sort s, I.prov hs, ht', (congrArg (M.IsTrue (I.prov hs)) (hval _ ht ht')).mpr htrue⟩
  obtain ⟨s, hs, ht⟩ := hA.concl_wellTyped
  obtain ⟨c, hc, ht', htrue⟩ := h ρ hdvT hessT
  obtain rfl : I.sort s = c := Option.some.inj ((I.prov hs).symm.trans hc)
  have hts := ht.synCtx (G'.prov_sort hs)
  exact ⟨s, hs, hts, (congrArg (M.IsTrue (I.prov hs)) (hval _ hts ht')).mp htrue⟩

end Assertions

end Interp

end Grammar

/-! ## Isomorphisms of models -/

namespace Model

open Grammar

variable {G : Grammar L C V}

/-- An isomorphism of models: an isomorphism of algebras preserving and
reflecting freshness and truth. -/
structure Iso (M N : Model.{u, w} G) where
  hom : Algebra.Hom M.toAlgebra N.toAlgebra
  inv : Algebra.Hom N.toAlgebra M.toAlgebra
  inv_hom : ∀ {s} (a : M.Carrier s), inv.map (hom.map a) = a
  hom_inv : ∀ {s} (b : N.Carrier s), hom.map (inv.map b) = b
  fresh_iff : ∀ {s t} (a : M.Carrier s) (b : M.Carrier t),
    N.Fresh (hom.map a) (hom.map b) ↔ M.Fresh a b
  true_iff : ∀ {c s} (hc : G.prov c = some s) (a : M.Carrier s),
    N.IsTrue hc (hom.map a) ↔ M.IsTrue hc a

namespace Iso

variable {M N : Model.{u, w} G}

/-- The inverse isomorphism. -/
def symm (e : M.Iso N) : N.Iso M where
  hom := e.inv
  inv := e.hom
  inv_hom := e.hom_inv
  hom_inv := e.inv_hom
  fresh_iff a b := by rw [← e.fresh_iff, e.hom_inv, e.hom_inv]
  true_iff hc a := by rw [← e.true_iff, e.hom_inv]

/-- The identity isomorphism. -/
def refl (M : Model.{u, w} G) : M.Iso M where
  hom := Algebra.Hom.id _
  inv := Algebra.Hom.id _
  inv_hom _ := rfl
  hom_inv _ := rfl
  fresh_iff _ _ := Iff.rfl
  true_iff _ _ := Iff.rfl

theorem value_hom (e : M.Iso N) {ctx : V → C → Prop} (ρ : ∀ v s, ctx v s → N.Carrier s)
    (t : Tree L V) {s : C} (h : G.HasSort ctx t s) :
    e.hom.map (M.value (fun v s hv => e.inv.map (ρ v s hv)) t h) = N.value ρ t h := by
  rw [Model.value, Grammar.Algebra.Hom.map_eval]
  exact N.value_agree t h h fun v _ s _ _ => e.hom_inv _

/-- Isomorphic models satisfy the same assertions. -/
theorem satisfies (e : M.Iso N) {A : TAssertion L C V} (h : M.Satisfies A) : N.Satisfies A := by
  intro ρ hdv hess
  let ρM : M.Valuation A.ctx := fun v s hv => e.inv.map (ρ v s hv)
  have holds : ∀ t : TExpr L C V, M.Holds ρM t ↔ N.Holds ρ t := by
    intro t
    constructor
    · rintro ⟨s, hs, ht, htrue⟩
      exact ⟨s, hs, ht, by rw [← e.value_hom ρ]; exact (e.true_iff hs _).2 htrue⟩
    · rintro ⟨s, hs, ht, htrue⟩
      exact ⟨s, hs, ht, by rw [← e.value_hom ρ] at htrue; exact (e.true_iff hs _).1 htrue⟩
  refine (holds _).1 (h ρM ?_ fun t ht => (holds t).2 (hess t ht))
  intro x y hxy hne s t hx hy
  rw [← e.fresh_iff, e.hom_inv, e.hom_inv]
  exact hdv x y hxy hne s t hx hy

theorem satisfies_iff (e : M.Iso N) {A : TAssertion L C V} : M.Satisfies A ↔ N.Satisfies A :=
  ⟨e.satisfies, e.symm.satisfies⟩

end Iso

end Model

namespace Grammar.Interp

variable {G : Grammar L C V}

/-! ## The identity interpretation -/

section Id

variable (G)

/-- The identity interpretation of a grammar in itself: each rule is
interpreted by itself applied to its argument variables. -/
abbrev id : Interp G G where
  sort c := c
  var v := v
  var_injective _ _ h := h
  sort_mem _ h := h
  prov h := h
  body l := .node l (List.ofFn fun j => .var ((G.rule l).args.get j).2)
  body_sort _ := HasSort.node_ofFn _ fun j => .var ⟨j, rfl, rfl⟩

variable {G}

/-- A model is isomorphic to the model it induces along the identity
interpretation. -/
noncomputable def pullIdIso (M : Model.{u, w} G) : ((id G).pull M).Iso M where
  hom := ⟨fun a => a, fun o args => by
    obtain ⟨l, rfl⟩ := o
    change eval M.toAlgebra _ (.node l (List.ofFn _)) _ = _
    rw [eval_node]
    congr 1
    funext j
    rw [eval_congr (t' := .var ((G.rule l).args.get j).2) (by simp) _ (.var ⟨j, rfl, rfl⟩),
      eval_var]
    exact (id G).argVal_eq M args _ j rfl rfl⟩
  inv := ⟨fun a => a, fun o args => by
    obtain ⟨l, rfl⟩ := o
    change _ = eval M.toAlgebra _ (.node l (List.ofFn _)) _
    rw [eval_node]
    congr 1
    funext j
    rw [eval_congr (t' := .var ((G.rule l).args.get j).2) (by simp) _ (.var ⟨j, rfl, rfl⟩),
      eval_var]
    exact ((id G).argVal_eq M args _ j rfl rfl).symm⟩
  inv_hom _ := rfl
  hom_inv _ := rfl
  fresh_iff _ _ := Iff.rfl
  true_iff _ _ := Iff.rfl

end Id

end Grammar.Interp

namespace Model

open Grammar

variable {G : Grammar L C V}

/-! ## Arithmetical soundness -/

variable [DecidableEq V]

/-- The arithmetic language of a grammar `G'` with standard model `std`:
sentences are the well-formed tree assertions, the Σ₁ sentences are given by
`sigma1`, and a sentence is true when the standard model satisfies it. -/
def stdLanguage (G' : Grammar L' C' V') (std : Model.{u, w} G')
    (sigma1 : TAssertion L' C' V' → Prop) : ArithLanguage where
  Sentence := {A : TAssertion L' C' V' // A.WellFormed G'}
  IsSigma1 A := sigma1 A.1
  TrueInNat A := std.Satisfies A.1

/-- Arithmetical soundness from a model with the standard natural numbers: if
`M` is a model of the well-formed axioms `Γ` and the model induced by `M` along
the interpretation `I` of an arithmetic grammar is isomorphic to its standard
model, then every arithmetic sentence whose translation `Γ` derives is true in
the standard model. -/
theorem arithSound_of_iso {G' : Grammar L' C' V'} (M : Model.{u, w} G)
    {Γ : Set (TAssertion L C V)} (hΓ : ∀ B ∈ Γ, B.WellFormed G) (hM : M.IsModel Γ)
    (I : Grammar.Interp G' G) (std : Model.{u, w} G') (e : (I.pull M).Iso std)
    (sigma1 : TAssertion L' C' V' → Prop) :
    (stdLanguage G' std sigma1).ArithSound (TDerivable G Γ) fun A => I.trAssertion A.1 :=
  ArithLanguage.arithSound_of_model M.Satisfies (fun _ h => M.sound hΓ hM h)
    fun A hA => e.satisfies (I.satisfies_pull M A.2 hA)

/-- In particular such a system is Σ₁-sound. -/
theorem sigma1Sound_of_iso {G' : Grammar L' C' V'} (M : Model.{u, w} G)
    {Γ : Set (TAssertion L C V)} (hΓ : ∀ B ∈ Γ, B.WellFormed G) (hM : M.IsModel Γ)
    (I : Grammar.Interp G' G) (std : Model.{u, w} G') (e : (I.pull M).Iso std)
    (sigma1 : TAssertion L' C' V' → Prop) :
    (stdLanguage G' std sigma1).Sigma1Sound (TDerivable G Γ) fun A => I.trAssertion A.1 :=
  (arithSound_of_iso M hΓ hM I std e sigma1).sigma1Sound

end Model

end Silmaril.Logic.Metamath
