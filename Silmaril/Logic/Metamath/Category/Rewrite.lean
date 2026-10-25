module

public import Silmaril.Logic.Metamath.Category.Cut

@[expose] public section

/-!
# Syntax rewrites

A syntax rewrite `f : Rewrite G G'` from a grammar `G` to a grammar `G'` is a
typecode map `f.tc` sending syntax typecodes to syntax typecodes and
compatible with the provable typecodes (`G.prov c = some s` gives
`G'.prov (f.tc c) = some (f.tc s)`), an injective renaming of variables
`f.var`, and for each syntax rule `l` of `G` a template `f.tmpl l`: a tree
over `G'` whose variables are the renamed argument variables of `l`, of the
translated sort. This is a derived signature morphism: each operation of
`G.signature` is sent to a term of `G'.signature`.

Translation (`Rewrite.tree`) replaces variables by their renamings and each
node `l` by its template, with the translated children substituted for the
argument variables. On well-sorted trees it

* preserves sorts (`HasSort.rewrite`),
* only introduces renamed variables (`Rewrite.mem_vars_tree`),
* commutes with substitution (`Rewrite.tree_subst`).

It extends to tree assertions (`Rewrite.assertion`), preserving well-formedness
(`Rewrite.wellFormed`), and maps tree derivations from `Γ` to tree derivations
from the translated axioms (`TDerivation.rewrite`, `TDerivable.rewrite`), so
theorems go to theorems. With cut admissibility, a rewrite sending every axiom
of `Γ` to a theorem of `Δ` sends every theorem of `Γ` to a theorem of `Δ`
(`TDerivable.rewrite_of_derivable`).

Rewrites have identities and a composition (`Rewrite.id`, `Rewrite.comp`),
which act as identity and composition on well-sorted trees and well-formed
assertions, and satisfy the category laws on the nose.
-/

namespace Silmaril.Logic.Metamath.Grammar

universe u

variable {L C V L' C' V' L'' C'' V'' L''' C''' V''' : Type u}

/-- The variables of a well-sorted tree have sorts in its context. -/
theorem HasSort.exists_ctx_of_mem_vars {G : Grammar L C V} {ctx : V → C → Prop}
    {t : Tree L V} {s : C} (h : G.HasSort ctx t s) {v : V} (hv : v ∈ t.vars) :
    ∃ s', ctx v s' := by
  induction h with
  | var hc =>
    simp only [Tree.vars_var, List.mem_singleton] at hv
    subst hv
    exact ⟨_, hc⟩
  | @node l args hlen _ ih =>
    simp only [Tree.vars_node, List.mem_flatMap] at hv
    obtain ⟨a, ha, hv⟩ := hv
    obtain ⟨p, hp⟩ := exists_mem_zip_of_mem_left hlen ha
    exact ih (a, p) hp hv

theorem mem_zip_map_self {α β : Type*} {g : α → β} {l : List α} {b : β} {a : α}
    (h : (b, a) ∈ (l.map g).zip l) : b = g a := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · rfl
    · exact ih h

/-- A syntax rewrite from `G` to `G'`: a typecode map sending syntax typecodes
to syntax typecodes and compatible with provable typecodes, an injective
variable renaming, and a template over `G'` for each rule of `G`, well sorted
in the renamed argument variables of the rule. -/
structure Rewrite (G : Grammar L C V) (G' : Grammar L' C' V') where
  /-- The typecode map. -/
  tc : C → C'
  /-- The variable renaming. -/
  var : V ↪ V'
  /-- The template of each syntax rule. -/
  tmpl : L → Tree L' V'
  sort_mem : ∀ s ∈ G.sorts, tc s ∈ G'.sorts
  prov_eq : ∀ {c s : C}, G.prov c = some s → G'.prov (tc c) = some (tc s)
  tmpl_sort : ∀ l, G'.HasSort (fun w s => (s, w) ∈ (G.rule l).args.map fun p => (tc p.1, var p.2))
    (tmpl l) (tc (G.rule l).tc)

namespace Rewrite

variable {G : Grammar L C V} {G' : Grammar L' C' V'} {G'' : Grammar L'' C'' V''}
  {G''' : Grammar L''' C''' V'''}

@[ext]
theorem ext {f g : Rewrite G G'} (htc : f.tc = g.tc) (hvar : f.var = g.var)
    (htmpl : f.tmpl = g.tmpl) : f = g := by
  cases f; cases g
  simp only at htc hvar htmpl
  subst htc hvar htmpl
  rfl

variable (f : Rewrite G G')

/-- The renamed argument variables of a rule, with translated sorts. -/
def args (l : L) : List (C' × V') := (G.rule l).args.map fun p => (f.tc p.1, f.var p.2)

/-- The context of the template of `l`. -/
def argCtx (l : L) (w : V') (s : C') : Prop := (s, w) ∈ f.args l

theorem argCtx_iff {l : L} {w : V'} {s : C'} :
    f.argCtx l w s ↔ ∃ p ∈ (G.rule l).args, f.tc p.1 = s ∧ f.var p.2 = w := by
  simp [argCtx, args]

theorem hasSort_tmpl (l : L) : G'.HasSort (f.argCtx l) (f.tmpl l) (f.tc (G.rule l).tc) :=
  f.tmpl_sort l

theorem args_nodup (l : L) : ((f.args l).map Prod.snd).Nodup := by
  have : (f.args l).map Prod.snd = ((G.rule l).args.map Prod.snd).map f.var := by
    simp [args, Function.comp_def]
  rw [this]
  exact (G.rule l).args_nodup.map f.var.injective

/-- Every variable of a template is a renamed argument variable. -/
theorem mem_vars_tmpl {l : L} {w : V'} (hw : w ∈ (f.tmpl l).vars) :
    ∃ p ∈ (G.rule l).args, f.var p.2 = w := by
  obtain ⟨s, hs⟩ := (f.hasSort_tmpl l).exists_ctx_of_mem_vars hw
  obtain ⟨p, hp, -, rfl⟩ := f.argCtx_iff.1 hs
  exact ⟨p, hp, rfl⟩

/-- The context of renamed variables with translated sorts. -/
def mapCtx (ctx : V → C → Prop) (w : V') (s' : C') : Prop :=
  ∃ v s, ctx v s ∧ f.var v = w ∧ f.tc s = s'

theorem mapCtx_apply {ctx : V → C → Prop} {v : V} {s : C} (h : ctx v s) :
    f.mapCtx ctx (f.var v) (f.tc s) := ⟨v, s, h, rfl, rfl⟩

variable [DecidableEq V']

/-- The substitution a template receives: each renamed argument variable gets
the translated child at its position. -/
def argSubst (l : L) (ts : List (Tree L' V')) (w : V') : Tree L' V' :=
  (lookupArg (f.args l) ts w).getD (.var w)

mutual

/-- Translate a tree: rename variables and expand each node into its template. -/
def tree : Tree L V → Tree L' V'
  | .var v => .var (f.var v)
  | .node l as => (f.tmpl l).subst (f.argSubst l (treeList as))
termination_by structural t => t

/-- Translate each tree of a list. -/
def treeList : List (Tree L V) → List (Tree L' V')
  | [] => []
  | t :: ts => tree t :: treeList ts
termination_by structural ts => ts

end

theorem treeList_eq (ts : List (Tree L V)) : f.treeList ts = ts.map f.tree := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [treeList, ih]

@[simp] theorem tree_var (v : V) : f.tree (.var v) = .var (f.var v) := rfl

theorem tree_node (l : L) (as : List (Tree L V)) :
    f.tree (.node l as) = (f.tmpl l).subst (f.argSubst l (as.map f.tree)) := by
  rw [tree, treeList_eq]

/-- The argument substitution gives each renamed argument variable the tree at
its position. -/
theorem argSubst_of_mem_zip {l : L} {ts : List (Tree L' V')} {t : Tree L' V'} {p : C × V}
    (h : (t, p) ∈ ts.zip (G.rule l).args) : f.argSubst l ts (f.var p.2) = t := by
  have hm : (t, (f.tc p.1, f.var p.2)) ∈ ts.zip (f.args l) := by
    rw [args, List.zip_map_right, List.mem_map]
    exact ⟨(t, p), h, rfl⟩
  simp [argSubst, lookupArg_of_mem_zip (f.args_nodup l) hm]

/-- The translated child at each argument position. -/
theorem argSubst_map {l : L} {as : List (Tree L V)} (g : Tree L V → Tree L' V')
    {a : Tree L V} {p : C × V} (h : (a, p) ∈ as.zip (G.rule l).args) :
    f.argSubst l (as.map g) (f.var p.2) = g a := by
  refine f.argSubst_of_mem_zip ?_
  rw [List.zip_map_left, List.mem_map]
  exact ⟨(a, p), h, rfl⟩

/-- Two argument substitutions agree on a template when they agree on the
children. -/
theorem subst_tmpl_congr {l : L} {as : List (Tree L V)} (hlen : as.length = (G.rule l).arity)
    {τ : V' → Tree L' V'} (g : Tree L V → Tree L' V')
    (h : ∀ a p, (a, p) ∈ as.zip (G.rule l).args → τ (f.var p.2) = g a) :
    (f.tmpl l).subst τ = (f.tmpl l).subst (f.argSubst l (as.map g)) := by
  apply Tree.subst_congr
  intro w hw
  obtain ⟨p, hp, rfl⟩ := f.mem_vars_tmpl hw
  obtain ⟨a, ha⟩ := exists_mem_zip_of_mem_right hlen hp
  rw [h a p ha, f.argSubst_map g ha]

variable {f}

/-- Translation preserves sorts. -/
theorem _root_.Silmaril.Logic.Metamath.Grammar.HasSort.rewrite {ctx : V → C → Prop}
    {t : Tree L V} {s : C} (h : G.HasSort ctx t s) :
    G'.HasSort (f.mapCtx ctx) (f.tree t) (f.tc s) := by
  induction h with
  | var hc => exact .var (f.mapCtx_apply hc)
  | @node l as hlen _ ih =>
    rw [tree_node]
    refine (f.hasSort_tmpl l).subst fun w s' hw => ?_
    obtain ⟨p, hp, rfl, rfl⟩ := f.argCtx_iff.1 hw
    obtain ⟨a, ha⟩ := exists_mem_zip_of_mem_right hlen hp
    rw [f.argSubst_map f.tree ha]
    exact ih (a, p) ha

/-- Translation only introduces renamed variables of the tree. -/
theorem mem_vars_tree {ctx : V → C → Prop} {t : Tree L V} {s : C} (h : G.HasSort ctx t s)
    {w : V'} (hw : w ∈ (f.tree t).vars) : ∃ v ∈ t.vars, f.var v = w := by
  induction h with
  | var =>
    simp only [tree_var, Tree.vars_var, List.mem_singleton] at hw
    exact ⟨_, by simp, hw.symm⟩
  | @node l as hlen _ ih =>
    rw [tree_node, Tree.mem_vars_subst] at hw
    obtain ⟨w₀, hw₀, hw⟩ := hw
    obtain ⟨p, hp, rfl⟩ := f.mem_vars_tmpl hw₀
    obtain ⟨a, ha⟩ := exists_mem_zip_of_mem_right hlen hp
    rw [f.argSubst_map f.tree ha] at hw
    obtain ⟨v, hv, rfl⟩ := ih (a, p) ha hw
    exact ⟨v, by simpa using ⟨a, (List.of_mem_zip ha).1, hv⟩, rfl⟩

variable (f) in
/-- A substitution on `V` transported along the renaming: the renaming of `v`
receives the translation of `τ v`, other variables are left alone. -/
noncomputable def liftSubst (τ : V → Tree L V) (w : V') : Tree L' V' :=
  open Classical in if h : ∃ v, f.var v = w then f.tree (τ h.choose) else .var w

@[simp] theorem liftSubst_var (τ : V → Tree L V) (v : V) :
    f.liftSubst τ (f.var v) = f.tree (τ v) := by
  rw [liftSubst]
  split
  · rename_i h
    rw [f.var.injective h.choose_spec]
  · rename_i h
    exact absurd ⟨v, rfl⟩ h

/-- Translation commutes with substitution. -/
theorem tree_subst {ctx : V → C → Prop} {t : Tree L V} {s : C} (h : G.HasSort ctx t s)
    (τ : V → Tree L V) : f.tree (t.subst τ) = (f.tree t).subst (f.liftSubst τ) := by
  induction h with
  | var => simp
  | @node l as hlen _ ih =>
    rw [Tree.subst_node, tree_node, tree_node, Tree.subst_subst, List.map_map]
    symm
    refine f.subst_tmpl_congr hlen _ fun a p ha => ?_
    rw [f.argSubst_map f.tree ha]
    exact (ih (a, p) ha).symm

/-! ### Assertions -/

variable (f) in
/-- Translate a tree expression. -/
def texpr (e : TExpr L C V) : TExpr L' C' V' := ⟨f.tc e.tc, f.tree e.tree⟩

variable (f) in
/-- Translate a hypothesis. -/
def thyp : THyp L C V → THyp L' C' V'
  | .float c v => .float (f.tc c) (f.var v)
  | .ess e => .ess (f.texpr e)

variable (f) in
/-- Translate a tree assertion. -/
def assertion (A : TAssertion L C V) : TAssertion L' C' V' where
  dv := A.dv.map fun p => (f.var p.1, f.var p.2)
  hyps := A.hyps.map f.thyp
  concl := f.texpr A.concl

@[simp] theorem texpr_tc (e : TExpr L C V) : (f.texpr e).tc = f.tc e.tc := rfl

@[simp] theorem texpr_tree (e : TExpr L C V) : (f.texpr e).tree = f.tree e.tree := rfl

@[simp] theorem assertion_concl (A : TAssertion L C V) : (f.assertion A).concl = f.texpr A.concl :=
  rfl

theorem texpr_subst {ctx : V → C → Prop} {e : TExpr L C V} {s : C}
    (h : G.HasSort ctx e.tree s) (τ : V → Tree L V) :
    f.texpr (e.subst τ) = (f.texpr e).subst (f.liftSubst τ) := by
  simp [texpr, TExpr.subst, tree_subst h]

theorem ctx_assertion {A : TAssertion L C V} {w : V'} {s' : C'} :
    (f.assertion A).ctx w s' ↔ f.mapCtx A.ctx w s' := by
  simp only [TAssertion.ctx, assertion, List.mem_map, mapCtx]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h with
    | float c v =>
      simp only [thyp, THyp.float.injEq] at he
      exact ⟨v, c, hh, he.2, he.1⟩
    | ess e => simp [thyp] at he
  · rintro ⟨v, s, hv, rfl, rfl⟩
    exact ⟨_, hv, rfl⟩

theorem ctx_assertion_eq (A : TAssertion L C V) : (f.assertion A).ctx = f.mapCtx A.ctx := by
  funext w s'
  exact propext ctx_assertion

theorem essentials_assertion (A : TAssertion L C V) :
    (f.assertion A).essentials = A.essentials.map f.texpr := by
  simp only [TAssertion.essentials, assertion, List.filterMap_map, List.map_filterMap]
  congr 1
  funext h
  cases h <;> rfl

theorem floats_assertion (A : TAssertion L C V) :
    (f.assertion A).floats = A.floats.map fun p => (f.tc p.1, f.var p.2) := by
  simp only [TAssertion.floats, assertion, List.filterMap_map, List.map_filterMap]
  congr 1
  funext h
  cases h <;> rfl

theorem disjoint_assertion {A : TAssertion L C V} {x y : V} :
    (f.assertion A).Disjoint (f.var x) (f.var y) ↔ A.Disjoint x y := by
  have key : ∀ a b : V, (f.var a, f.var b) ∈ (f.assertion A).dv ↔ (a, b) ∈ A.dv := by
    intro a b
    simp only [assertion, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨c, d⟩, hcd, hc, hd⟩
      obtain rfl : c = a := f.var.injective hc
      obtain rfl : d = b := f.var.injective hd
      exact hcd
    · exact fun h => ⟨_, h, rfl, rfl⟩
  simp only [TAssertion.Disjoint, key]

/-- Translation preserves well-formedness. -/
theorem wellFormed {A : TAssertion L C V} (hA : A.WellFormed G) :
    (f.assertion A).WellFormed G' where
  floats_nodup := by
    rw [floats_assertion, List.map_map]
    have : (Prod.snd ∘ fun p : C × V => (f.tc p.1, f.var p.2)) = f.var ∘ Prod.snd := rfl
    rw [this, ← List.map_map]
    exact hA.floats_nodup.map f.var.injective
  float_sort w s' h := by
    obtain ⟨v, s, hv, -, rfl⟩ := ctx_assertion.1 h
    exact f.sort_mem s (hA.float_sort v s hv)
  ess_wellTyped e he := by
    rw [essentials_assertion, List.mem_map] at he
    obtain ⟨e, he, rfl⟩ := he
    obtain ⟨s, hs, ht⟩ := hA.ess_wellTyped e he
    exact ⟨f.tc s, f.prov_eq hs, by rw [ctx_assertion_eq]; exact ht.rewrite⟩
  concl_wellTyped := by
    obtain ⟨s, hs, ht⟩ := hA.concl_wellTyped
    exact ⟨f.tc s, f.prov_eq hs, by rw [ctx_assertion_eq]; exact ht.rewrite⟩
  dv_irrefl x y h := by
    simp only [assertion, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨⟨a, b⟩, hab, rfl, rfl⟩ := h
    exact fun e => hA.dv_irrefl a b hab (f.var.injective e)
  dv_float x y h := by
    simp only [assertion, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨⟨a, b⟩, hab, rfl, rfl⟩ := h
    obtain ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩ := hA.dv_float a b hab
    exact ⟨⟨f.tc s, ctx_assertion.2 (f.mapCtx_apply hs)⟩,
      ⟨f.tc s', ctx_assertion.2 (f.mapCtx_apply hs')⟩⟩

/-- The variables of a translated well-formed assertion are renamed variables
of the assertion. -/
theorem mem_allVars_assertion {A : TAssertion L C V} (hA : A.WellFormed G) {w : V'}
    (hw : w ∈ (f.assertion A).allVars) : ∃ v ∈ A.allVars, f.var v = w := by
  simp only [TAssertion.allVars, assertion, List.mem_append, List.mem_flatMap,
    List.mem_map] at hw
  rcases hw with hw | ⟨_, ⟨h, hh, rfl⟩, hw⟩
  · obtain ⟨s, -, hs⟩ := hA.concl_wellTyped
    obtain ⟨v, hv, rfl⟩ := mem_vars_tree hs hw
    exact ⟨v, TAssertion.mem_allVars_of_mem_concl hv, rfl⟩
  · cases h with
    | float c v =>
      simp only [thyp, THyp.vars, List.mem_singleton] at hw
      exact ⟨v, TAssertion.mem_allVars_of_ctx (s := c) hh, hw.symm⟩
    | ess e =>
      obtain ⟨s, -, hs⟩ := hA.ess_wellTyped e (TAssertion.mem_essentials.2 hh)
      obtain ⟨v, hv, rfl⟩ := mem_vars_tree hs hw
      exact ⟨v, TAssertion.mem_allVars_of_mem_essentials (TAssertion.mem_essentials.2 hh) hv,
        rfl⟩

variable (f) in
/-- Translate the dummy variables of a proof of a well-formed assertion. -/
def dummies {A : TAssertion L C V} (hA : A.WellFormed G) (D : TDummies A) :
    TDummies (f.assertion A) where
  floats := D.floats.map fun p => (f.tc p.1, f.var p.2)
  dv := D.dv.map fun p => (f.var p.1, f.var p.2)
  fresh p hp h := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨v, hv, he⟩ := mem_allVars_assertion hA h
    exact D.fresh q hq (f.var.injective he ▸ hv)
  dv_dummy p hp := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    simp only [List.map_map, Function.comp_def]
    exact (D.dv_dummy q hq).imp (fun h => List.mem_map.2 (by
      obtain ⟨r, hr, e⟩ := List.mem_map.1 h
      exact ⟨r, hr, by rw [e]⟩)) (fun h => List.mem_map.2 (by
      obtain ⟨r, hr, e⟩ := List.mem_map.1 h
      exact ⟨r, hr, by rw [e]⟩))
  nodup := by
    simpa [Function.comp_def] using D.nodup.map f.var.injective

theorem assertion_extend {A : TAssertion L C V} (hA : A.WellFormed G) (D : TDummies A) :
    f.assertion (A.extend D) = (f.assertion A).extend (f.dummies hA D) := by
  simp [assertion, TAssertion.extend, dummies, thyp, Function.comp_def]

end Rewrite

/-! ### Derivations -/

section Derivations

variable {G : Grammar L C V} {G' : Grammar L' C' V'} [DecidableEq V'] {Γ : Set (TAssertion L C V)}
  {A : TAssertion L C V}

theorem Rewrite.exists_of_mem_essentials (f : Rewrite G G') {B : TAssertion L C V}
    {e : TExpr L' C' V'} (he : e ∈ (f.assertion B).essentials) :
    ∃ e₀ ∈ B.essentials, f.texpr e₀ = e := by
  rw [f.essentials_assertion, List.mem_map] at he
  exact he

/-- Translation preserves well-sortedness of the substitution at an axiom. -/
theorem Rewrite.sorted_liftSubst (f : Rewrite G G') {B : TAssertion L C V} {τ : V → Tree L V}
    (sorted : ∀ v s, B.ctx v s → G.HasSort A.ctx (τ v) s) :
    ∀ w s', (f.assertion B).ctx w s' → G'.HasSort (f.assertion A).ctx (f.liftSubst τ w) s' := by
  intro w s' hw
  obtain ⟨v, s, hv, rfl, rfl⟩ := f.ctx_assertion.1 hw
  rw [Rewrite.liftSubst_var, f.ctx_assertion_eq]
  exact (sorted v s hv).rewrite

/-- Translation preserves disjoint-variable safety. -/
theorem Rewrite.dvSafe_liftSubst (f : Rewrite G G') {B : TAssertion L C V} (hB : B.WellFormed G)
    {τ : V → Tree L V} (sorted : ∀ v s, B.ctx v s → G.HasSort A.ctx (τ v) s)
    (dv : B.DVSafe τ A.Disjoint) :
    (f.assertion B).DVSafe (f.liftSubst τ) (f.assertion A).Disjoint := by
  intro x' y' hxy a' ha' b' hb'
  simp only [Rewrite.assertion, List.mem_map, Prod.mk.injEq] at hxy
  obtain ⟨⟨x, y⟩, hxy, rfl, rfl⟩ := hxy
  obtain ⟨⟨sx, hsx⟩, ⟨sy, hsy⟩⟩ := hB.dv_float x y hxy
  rw [Rewrite.liftSubst_var] at ha' hb'
  obtain ⟨a, ha, rfl⟩ := Rewrite.mem_vars_tree (sorted x sx hsx) ha'
  obtain ⟨b, hb, rfl⟩ := Rewrite.mem_vars_tree (sorted y sy hsy) hb'
  obtain ⟨hab, hd⟩ := dv x y hxy a ha b hb
  exact ⟨fun e => hab (f.var.injective e), f.disjoint_assertion.2 hd⟩

/-- Translate a tree derivation from well-formed axioms into a derivation from
the translated axioms, in the translated frame. -/
noncomputable def TDerivation.rewrite (f : Rewrite G G') (hΓ : ∀ B ∈ Γ, B.WellFormed G) :
    {e : TExpr L C V} → TDerivation G Γ A e →
      TDerivation G' (f.assertion '' Γ) (f.assertion A) (f.texpr e)
  | _, hyp he => .hyp (by rw [f.essentials_assertion]; exact List.mem_map_of_mem he)
  | _, app B hB τ sorted premises dv =>
    (TDerivation.app (G := G') (Γ := f.assertion '' Γ) (A := f.assertion A) (f.assertion B)
      ⟨B, hB, rfl⟩ (f.liftSubst τ) (f.sorted_liftSubst sorted)
      (fun e he =>
        ((premises _ (f.exists_of_mem_essentials he).choose_spec.1).rewrite f hΓ).cast (by
          have hc := (f.exists_of_mem_essentials he).choose_spec
          obtain ⟨s, -, hs⟩ := (hΓ B hB).ess_wellTyped _ hc.1
          rw [f.texpr_subst hs τ, hc.2]))
      (f.dvSafe_liftSubst (hΓ B hB) sorted dv)).cast (by
      obtain ⟨s, -, hs⟩ := (hΓ B hB).concl_wellTyped
      exact (f.texpr_subst hs τ).symm)

/-- A tree theorem of well-formed axioms translates to a tree theorem of the
translated axioms. -/
theorem TDerivable.rewrite (f : Rewrite G G') (hΓ : ∀ B ∈ Γ, B.WellFormed G)
    (hA : A.WellFormed G) (h : TDerivable G Γ A) :
    TDerivable G' (f.assertion '' Γ) (f.assertion A) := by
  obtain ⟨⟨D, d⟩⟩ := h
  refine ⟨⟨f.dummies hA D, ?_⟩⟩
  rw [← f.assertion_extend hA D]
  exact d.rewrite f hΓ

/-- A rewrite sending every axiom of `Γ` to a theorem of `Δ` sends every
theorem of `Γ` to a theorem of `Δ`. -/
theorem TDerivable.rewrite_of_derivable [Infinite V'] (f : Rewrite G G')
    {Δ : Set (TAssertion L' C' V')} (hΓ : ∀ B ∈ Γ, B.WellFormed G)
    (hΓΔ : ∀ B ∈ Γ, TDerivable G' Δ (f.assertion B)) (hA : A.WellFormed G)
    (h : TDerivable G Γ A) : TDerivable G' Δ (f.assertion A) :=
  TDerivable.trans (by rintro _ ⟨B, hB, rfl⟩; exact hΓΔ B hB) (h.rewrite f hΓ hA)

end Derivations

/-! ### Identity and composition -/

theorem mem_zip_map_self_of_mem {α β : Type*} (g : α → β) {l : List α} {a : α} (h : a ∈ l) :
    (g a, a) ∈ (l.map g).zip l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (ih h)

theorem map_eq_of_forall_mem_zip {α β : Type*} {g : β → α} {as : List α} {bs : List β}
    (hlen : as.length = bs.length) (h : ∀ a b, (a, b) ∈ as.zip bs → g b = a) :
    bs.map g = as := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨h a b (by simp), ih (by simpa using hlen) fun a' b' h' => h a' b' (by simp [h'])⟩

namespace Rewrite

variable {G : Grammar L C V} {G' : Grammar L' C' V'} {G'' : Grammar L'' C'' V''}
  {G''' : Grammar L''' C''' V'''}

variable (G) in
/-- The identity rewrite: each rule is its own template. -/
def id : Rewrite G G where
  tc c := c
  var := Function.Embedding.refl V
  tmpl l := .node l ((G.rule l).args.map fun p => .var p.2)
  sort_mem _ h := h
  prov_eq h := h
  tmpl_sort l := by
    refine .node (by simp) fun q hq => ?_
    obtain ⟨t, p⟩ := q
    obtain rfl := mem_zip_map_self hq
    exact .var (by simpa using (List.of_mem_zip hq).2)

@[simp] theorem id_tc (c : C) : (Rewrite.id G).tc c = c := rfl

@[simp] theorem id_var (v : V) : (Rewrite.id G).var v = v := rfl

/-- The composite rewrite: templates of `f` translated by `g`. -/
def comp [DecidableEq V''] (f : Rewrite G G') (g : Rewrite G' G'') : Rewrite G G'' where
  tc := g.tc ∘ f.tc
  var := f.var.trans g.var
  tmpl l := g.tree (f.tmpl l)
  sort_mem s hs := g.sort_mem _ (f.sort_mem s hs)
  prov_eq h := g.prov_eq (f.prov_eq h)
  tmpl_sort l := (f.hasSort_tmpl l).rewrite.mono fun w s h => by
    obtain ⟨v, s₀, hv, rfl, rfl⟩ := h
    obtain ⟨p, hp, rfl, rfl⟩ := f.argCtx_iff.1 hv
    exact List.mem_map.2 ⟨p, hp, rfl⟩

@[simp] theorem comp_tc [DecidableEq V''] (f : Rewrite G G') (g : Rewrite G' G'') (c : C) :
    (f.comp g).tc c = g.tc (f.tc c) := rfl

@[simp] theorem comp_var [DecidableEq V''] (f : Rewrite G G') (g : Rewrite G' G'') (v : V) :
    (f.comp g).var v = g.var (f.var v) := rfl

theorem comp_tmpl [DecidableEq V''] (f : Rewrite G G') (g : Rewrite G' G'') (l : L) :
    (f.comp g).tmpl l = g.tree (f.tmpl l) := rfl

section

variable [DecidableEq V]

/-- The identity rewrite fixes well-sorted trees. -/
theorem id_tree {ctx : V → C → Prop} {t : Tree L V} {s : C} (h : G.HasSort ctx t s) :
    (Rewrite.id G).tree t = t := by
  induction h with
  | var => rfl
  | @node l as hlen _ ih =>
    rw [tree_node]
    change (Tree.node l ((G.rule l).args.map fun p => Tree.var p.2)).subst _ = _
    rw [Tree.subst_node, List.map_map]
    congr 1
    refine map_eq_of_forall_mem_zip (by simpa using hlen) fun a p hp => ?_
    simp only [Function.comp_apply, Tree.subst_var']
    exact ((Rewrite.id G).argSubst_map _ hp).trans (ih (a, p) hp)

/-- The identity rewrite fixes well-formed assertions. -/
theorem id_assertion {A : TAssertion L C V} (hA : A.WellFormed G) :
    (Rewrite.id G).assertion A = A := by
  obtain ⟨s, -, hs⟩ := hA.concl_wellTyped
  cases A with
  | mk dv hyps concl =>
    simp only [assertion, texpr, id_tc, id_var, id_tree hs, TAssertion.mk.injEq]
    refine ⟨by simp, ?_, trivial⟩
    refine (List.map_congr_left fun h hh => ?_).trans (List.map_id _)
    cases h with
    | float => rfl
    | ess e =>
      obtain ⟨s, -, hs⟩ := hA.ess_wellTyped e (TAssertion.mem_essentials.2 hh)
      simp [thyp, texpr, id_tree hs]

end

section

variable [DecidableEq V'] [DecidableEq V'']

/-- Composition acts as composition on well-sorted trees. -/
theorem comp_tree (f : Rewrite G G') (g : Rewrite G' G'') {ctx : V → C → Prop} {t : Tree L V}
    {s : C} (h : G.HasSort ctx t s) : (f.comp g).tree t = g.tree (f.tree t) := by
  induction h with
  | var => rfl
  | @node l as hlen _ ih =>
    rw [tree_node, tree_node, g.tree_subst (f.hasSort_tmpl l)]
    apply Tree.subst_congr
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_vars_tree (f.hasSort_tmpl l) hw
    obtain ⟨p, hp, rfl⟩ := f.mem_vars_tmpl hw'
    obtain ⟨a, ha⟩ := exists_mem_zip_of_mem_right hlen hp
    rw [liftSubst_var, f.argSubst_map f.tree ha]
    exact ((f.comp g).argSubst_map (f.comp g).tree ha).trans (ih (a, p) ha)

/-- Composition acts as composition on well-formed assertions. -/
theorem comp_assertion (f : Rewrite G G') (g : Rewrite G' G'') {A : TAssertion L C V}
    (hA : A.WellFormed G) : (f.comp g).assertion A = g.assertion (f.assertion A) := by
  obtain ⟨s, -, hs⟩ := hA.concl_wellTyped
  cases A with
  | mk dv hyps concl =>
    simp only [assertion, texpr, comp_tc, comp_var, comp_tree f g hs, List.map_map,
      TAssertion.mk.injEq]
    refine ⟨rfl, List.map_congr_left fun h hh => ?_, trivial⟩
    cases h with
    | float => rfl
    | ess e =>
      obtain ⟨s, -, hs⟩ := hA.ess_wellTyped e (TAssertion.mem_essentials.2 hh)
      simp [thyp, texpr, comp_tree f g hs]

end

@[simp] theorem id_comp [DecidableEq V'] (f : Rewrite G G') : (Rewrite.id G).comp f = f := by
  ext l
  · rfl
  · rfl
  · change f.tree (.node l _) = f.tmpl l
    rw [tree_node]
    conv_rhs => rw [← Tree.subst_var (f.tmpl l)]
    apply Tree.subst_congr
    intro w hw
    obtain ⟨p, hp, rfl⟩ := f.mem_vars_tmpl hw
    exact f.argSubst_map f.tree (mem_zip_map_self_of_mem (fun p : C × V => Tree.var p.2) hp)

@[simp] theorem comp_id [DecidableEq V'] (f : Rewrite G G') : f.comp (Rewrite.id G') = f := by
  ext l
  · rfl
  · rfl
  · exact id_tree (f.hasSort_tmpl l)

theorem comp_assoc [DecidableEq V'] [DecidableEq V''] [DecidableEq V'''] (f : Rewrite G G')
    (g : Rewrite G' G'') (h : Rewrite G'' G''') : (f.comp g).comp h = f.comp (g.comp h) := by
  ext l
  · rfl
  · rfl
  · exact (comp_tree g h (f.hasSort_tmpl l)).symm

end Rewrite

end Silmaril.Logic.Metamath.Grammar
