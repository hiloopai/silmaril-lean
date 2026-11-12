module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Free

/-!
# The free-variable lemma for the internal language's evaluator

`Silmaril/SpecTec/Sem/Eval.lean` closes with a section headed "The metatheory
that is *not* here" whose single entry is the **substitution / free-variable
lemma**:

> `evalExp n env ρ e` depends only on the restriction of `ρ` to
> `Silmaril.SpecTec.IL.freeExp e`.

This file proves it, as `evalExp_agreeOn`, together with the consequences that
make it worth having: weakening (`evalExp_bindVal_of_notMem` and its three
siblings, one per namespace) and the closedness of a definition's clauses
(`callDef_eq_of_resolved`).

## Agreement, not restriction

"Depends only on the restriction of `ρ`" is stated as `VarEnv.AgreeOn`: two
scopes agree on an `IL.Sets` when they look every identifier it lists up to
the same thing.  A `VarEnv` has four namespaces (`spectec/src/il/subst.ml:9`)
and all four are needed, not just `vals`: a `CallE` to a `DefP`-bound name
resolves through `defs` (`spectec/src/il/eval.ml:361-372`), a `TypA` argument
is resolved through `typs` and a `GramA` through `grams`
(`eval.ml:636-638`).  `Sets.relid` is ignored, because a relation name is a
global and never enters a local scope.

Phrasing the hypothesis as agreement rather than as an actual restriction of
the map avoids having to say what the restriction of an association list *is*
— `Silmaril/SpecTec/Sem/Env.lean`'s `Map` shadows rather than replaces, so
restriction is not canonical — and it is the form every use site wants.

## Shape of the proof

One structural induction on the fuel, `agreeAt_succ`, of exactly the shape
`Eval.lean`'s `monoAt_succ` has, but over **twelve** members of the 29-member
mutual block rather than all of them.  That is not a weakening: the twelve are
closed under the calls `evalExp` can make.  `tryClauses`, `derives` and
`anyRule` take no `VarEnv` at all — a clause's patterns are matched in
`Subst.empty` (`eval.ml:654`) and its body is substituted with the result
(`eval.ml:664`), and a rule is tried in a scope built by `bindParams
VarEnv.empty` — so the caller's scope provably cannot reach them, and the
remaining fourteen members, the `matchExp` family and the premise machinery,
are reachable only through them.

The one clause that needs more than a congruence is `IterE`.  `freeExp`
subtracts the domain variables from the body (`spectec/src/il/free.ml:75`,
`free_exp e1 -- bound_iterexp ite`), so the induction hypothesis says nothing
about them; what re-establishes the invariant is that `evalIterE` *binds* every
domain variable, to the same value on both sides, before evaluating the body.
`EvalFree.agreeOn_body` is that step, and discharging its side condition is
where the bookkeeping lives: the row `iterRow` builds really does cover every
domain variable, which needs the length assertion of `evalIterList`
(`eval.ml:405`) and the fact that `evalDoms` reports the domains' own
variables (`eval.ml:546-549`).

## What is *not* claimed

The same statement for `matchExp` is **false**, and
`IterPatternCounterexample` exhibits a two-line counterexample.  See the scope
section at the end of this file.
-/

@[expose] public section

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod

/-! ## Agreement of two scopes on a set of identifiers -/

namespace VarEnv

/-- `ρ₁` and `ρ₂` agree on the identifier set `s`: every identifier `s` lists
is looked up to the same thing in both scopes, in each of the four namespaces
a `VarEnv` has.  `Sets.relid` is ignored, because a relation name is a global
and never lives in a local scope. -/
def AgreeOn (s : Sets) (ρ₁ ρ₂ : VarEnv) : Prop :=
  (∀ x ∈ s.varid, ρ₁.findVal? x = ρ₂.findVal? x) ∧
    (∀ x ∈ s.typid, ρ₁.findTyp? x = ρ₂.findTyp? x) ∧
    (∀ x ∈ s.defid, ρ₁.findDef? x = ρ₂.findDef? x) ∧
    (∀ x ∈ s.gramid, ρ₁.findGram? x = ρ₂.findGram? x)

namespace AgreeOn

variable {s t : Sets} {ρ₁ ρ₂ ρ₃ : VarEnv} {x : IL.Id}

/-- Agreement is reflexive. -/
@[refl] theorem refl (s : Sets) (ρ : VarEnv) : AgreeOn s ρ ρ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Agreement is symmetric. -/
theorem symm (h : AgreeOn s ρ₁ ρ₂) : AgreeOn s ρ₂ ρ₁ :=
  ⟨fun x hx => (h.1 x hx).symm, fun x hx => (h.2.1 x hx).symm,
    fun x hx => (h.2.2.1 x hx).symm, fun x hx => (h.2.2.2 x hx).symm⟩

/-- Agreement is transitive. -/
theorem trans (h₁ : AgreeOn s ρ₁ ρ₂) (h₂ : AgreeOn s ρ₂ ρ₃) : AgreeOn s ρ₁ ρ₃ :=
  ⟨fun x hx => (h₁.1 x hx).trans (h₂.1 x hx),
    fun x hx => (h₁.2.1 x hx).trans (h₂.2.1 x hx),
    fun x hx => (h₁.2.2.1 x hx).trans (h₂.2.2.1 x hx),
    fun x hx => (h₁.2.2.2 x hx).trans (h₂.2.2.2 x hx)⟩

/-- Agreement is antitone: agreeing on more is agreeing on less. -/
theorem mono (h : AgreeOn s ρ₁ ρ₂) (hsub : t ⊆ s) : AgreeOn t ρ₁ ρ₂ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨g₁, g₂, g₃, g₄, g₅⟩ := Sets.subset_def.1 hsub
  exact ⟨fun x hx => h₁ x (g₃ hx), fun x hx => h₂ x (g₁ hx),
    fun x hx => h₃ x (g₄ hx), fun x hx => h₄ x (g₅ hx)⟩

/-- Everything agrees on nothing. -/
theorem empty (ρ₁ ρ₂ : VarEnv) : AgreeOn Sets.empty ρ₁ ρ₂ := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp [Sets.empty] at hx

/-- Agreement on a union restricts to the left summand. -/
theorem union_left (h : AgreeOn (s.union t) ρ₁ ρ₂) : AgreeOn s ρ₁ ρ₂ :=
  h.mono (Sets.subset_union_left s t)

/-- Agreement on a union restricts to the right summand. -/
theorem union_right (h : AgreeOn (s.union t) ρ₁ ρ₂) : AgreeOn t ρ₁ ρ₂ :=
  h.mono (Sets.subset_union_right s t)

/-- Agreement on two sets is agreement on their union. -/
theorem union (h₁ : AgreeOn s ρ₁ ρ₂) (h₂ : AgreeOn t ρ₁ ρ₂) : AgreeOn (s.union t) ρ₁ ρ₂ := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [Sets.union, Finset.mem_union] at hx <;>
    rcases hx with hx | hx
  · exact h₁.1 x hx
  · exact h₂.1 x hx
  · exact h₁.2.1 x hx
  · exact h₂.2.1 x hx
  · exact h₁.2.2.1 x hx
  · exact h₂.2.2.1 x hx
  · exact h₁.2.2.2 x hx
  · exact h₂.2.2.2 x hx

/-- Agreement on `s` is agreement on `s` minus anything. -/
theorem diff (h : AgreeOn s ρ₁ ρ₂) (t : Sets) : AgreeOn (s.diff t) ρ₁ ρ₂ :=
  h.mono (Sets.diff_subset s t)

/-- The term variable a `varE` reads. -/
theorem findVal? (h : AgreeOn (freeVarid x) ρ₁ ρ₂) : ρ₁.findVal? x = ρ₂.findVal? x :=
  h.1 x (by simp [freeVarid, Sets.empty])

/-- The type variable a `varT` reads. -/
theorem findTyp? (h : AgreeOn (freeTypid x) ρ₁ ρ₂) : ρ₁.findTyp? x = ρ₂.findTyp? x :=
  h.2.1 x (by simp [freeTypid, Sets.empty])

/-- The definition variable a `callE` or a `defA` reads. -/
theorem findDef? (h : AgreeOn (freeDefid x) ρ₁ ρ₂) : ρ₁.findDef? x = ρ₂.findDef? x :=
  h.2.2.1 x (by simp [freeDefid, Sets.empty])

/-- The grammar variable a `varG` reads. -/
theorem findGram? (h : AgreeOn (freeGramid x) ρ₁ ρ₂) : ρ₁.findGram? x = ρ₂.findGram? x :=
  h.2.2.2 x (by simp [freeGramid, Sets.empty])

end AgreeOn

end VarEnv

/-! ## Identifier sets of a binding row -/

namespace EvalFree

/-- The identifiers a list of bindings covers, as a `Sets` living entirely in
the term namespace.  The wildcard `"_"` is removed, because `Map.bind` ignores
it (`spectec/src/il/env.ml:53-54`) and so binding a row that mentions `"_"`
says nothing about looking `"_"` up. -/
def keySet (xs : List IL.Id) : Sets :=
  { Sets.empty with varid := xs.toFinset.erase "_" }

/-- `keySet` is monotone in the list of identifiers. -/
theorem keySet_subset {xs ys : List IL.Id} (h : ∀ a ∈ xs, a ∈ ys) :
    keySet xs ⊆ keySet ys := by
  refine Sets.subset_def.2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [keySet, Sets.empty] <;>
    try exact Finset.Subset.refl _
  intro a ha
  simp only [Finset.mem_erase, List.mem_toFinset] at ha ⊢
  exact ⟨ha.1, h a ha.2⟩

/-- The identifiers one round of an iteration binds. -/
def rowSet (r : List (IL.Id × Value)) : Sets := keySet (r.map Prod.fst)

/-- `find?` after `binds` of a row that does not bind the identifier looked
up — either because the identifier is the wildcard, which `Map.bind` drops, or
because the row has no entry for it. -/
theorem find?_binds_of_not_bound {α : Type} :
    ∀ (r : List (IL.Id × α)) (m : Map α) {x : IL.Id},
      (x = "_" ∨ x ∉ r.map Prod.fst) → (m.binds r).find? x = m.find? x
  | [], _, _, _ => rfl
  | (y, v) :: r, m, x, h => by
      rw [Map.binds_cons]
      rcases h with h | h
      · subst h
        rw [find?_binds_of_not_bound r _ (Or.inl rfl)]
        by_cases hy : y = "_"
        · subst hy; simp
        · exact Map.find?_bind_of_ne _ hy v
      · simp only [List.map_cons, List.mem_cons, not_or] at h
        rw [find?_binds_of_not_bound r _ (Or.inr h.2)]
        exact Map.find?_bind_of_ne _ (Ne.symm h.1) v

/-- `find?` after `binds` of a row that *does* bind the identifier looked up
does not depend on the map underneath: the row's last entry for that
identifier wins. -/
theorem find?_binds_congr {α : Type} :
    ∀ (r : List (IL.Id × α)) (m₁ m₂ : Map α) {x : IL.Id},
      x ≠ "_" → x ∈ r.map Prod.fst → (m₁.binds r).find? x = (m₂.binds r).find? x
  | [], _, _, _, _, h => absurd h (by simp)
  | (y, v) :: r, m₁, m₂, x, hx, h => by
      rw [Map.binds_cons, Map.binds_cons]
      by_cases hm : x ∈ r.map Prod.fst
      · exact find?_binds_congr r _ _ hx hm
      · simp only [List.map_cons, List.mem_cons] at h
        have hxy : x = y := h.resolve_right hm
        subst hxy
        rw [find?_binds_of_not_bound r _ (Or.inr hm),
          find?_binds_of_not_bound r _ (Or.inr hm),
          Map.find?_bind_self _ hx, Map.find?_bind_self _ hx]

end EvalFree

namespace VarEnv

namespace AgreeOn

variable {s : Sets} {ρ₁ ρ₂ : VarEnv}

/-- Binding the *same* row on both sides preserves agreement. -/
theorem bindVals (h : AgreeOn s ρ₁ ρ₂) (r : List (IL.Id × Value)) :
    AgreeOn s (ρ₁.bindVals r) (ρ₂.bindVals r) := by
  refine ⟨fun x hx => ?_, h.2.1, h.2.2.1, h.2.2.2⟩
  show (ρ₁.vals.binds r).find? x = (ρ₂.vals.binds r).find? x
  by_cases hb : x ≠ "_" ∧ x ∈ r.map Prod.fst
  · exact EvalFree.find?_binds_congr r _ _ hb.1 hb.2
  · rw [EvalFree.find?_binds_of_not_bound r _ (by tauto),
      EvalFree.find?_binds_of_not_bound r _ (by tauto)]
    exact h.1 x hx

/-- Binding the same variable on both sides preserves agreement. -/
theorem bindVal (h : AgreeOn s ρ₁ ρ₂) (x : IL.Id) (v : Value) :
    AgreeOn s (ρ₁.bindVal x v) (ρ₂.bindVal x v) := h.bindVals [(x, v)]

end AgreeOn

/-- **Whatever a row binds, it binds the same on both sides.**  This is the
half of the `IterE` invariant that does not come from the incoming scope: the
domain variables of an iteration are rebound every round, so the two scopes
agree on them no matter what they held before. -/
theorem agreeOn_rowSet (ρ₁ ρ₂ : VarEnv) (r : List (IL.Id × Value)) :
    AgreeOn (EvalFree.rowSet r) (ρ₁.bindVals r) (ρ₂.bindVals r) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [EvalFree.rowSet, EvalFree.keySet, Finset.mem_erase, List.mem_toFinset] at hx
    exact EvalFree.find?_binds_congr r _ _ hx.1 hx.2
  all_goals simp [EvalFree.rowSet, EvalFree.keySet, Sets.empty] at hx

end VarEnv

/-! ## Bookkeeping for the iteration clauses

### Identifier sets and `List.mapM` -/

namespace EvalFree

/-- `s` is contained in `s` minus `t`, put back together with `t`.  This is
how the `IterE` invariant is discharged: `freeExp` subtracts an iteration's
domain variables from the body, and the row the evaluator binds puts them
back. -/
theorem subset_diff_union (s t : Sets) : s ⊆ (s.diff t).union t := by
  have key : ∀ a b : Finset IL.Id, a ⊆ (a \ b) ∪ b := by
    intro a b
    rw [Finset.sdiff_union_self_eq_union]
    exact Finset.subset_union_left
  exact Sets.subset_def.2 ⟨key _ _, key _ _, key _ _, key _ _, key _ _⟩

/-- `List.mapM` in the `Option` monad preserves the first components, when
every successful step does. -/
theorem map_fst_of_mapM_option {α β : Type} {f : α → Option (IL.Id × β)} {key : α → IL.Id}
    (hf : ∀ a p, f a = some p → p.1 = key a) :
    ∀ {xs : List α} {ys : List (IL.Id × β)}, xs.mapM f = some ys → ys.map Prod.fst = xs.map key
  | [], ys, h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h; rfl
  | x :: xs, ys, h => by
      rw [List.mapM_cons] at h
      cases hfx : f x with
      | none => rw [hfx] at h; simp at h
      | some p =>
          cases hzs : xs.mapM f with
          | none => rw [hfx, hzs] at h; simp at h
          | some zs =>
              rw [hfx, hzs] at h
              simp only [bind, Option.bind, Option.pure_def, Option.some.injEq] at h
              subst h
              simp only [List.map_cons, hf x p hfx, map_fst_of_mapM_option hf hzs]

/-- `List.mapM` in `Res` preserves the first components, when every successful
step does. -/
theorem map_fst_of_mapM_res {α β : Type} {f : α → Res (IL.Id × β)} {key : α → IL.Id}
    (hf : ∀ a p, f a = .ok p → p.1 = key a) :
    ∀ {xs : List α} {ys : List (IL.Id × β)}, xs.mapM f = .ok ys → ys.map Prod.fst = xs.map key
  | [], ys, h => by simp only [List.mapM_nil, pure, Except.pure] at h; cases h; rfl
  | x :: xs, ys, h => by
      simp only [List.mapM_cons, Res.bind_eq_ok] at h
      obtain ⟨p, hp, zs, hzs, hy⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq] at hy
      cases hy
      simp only [List.map_cons, hf x p hp, map_fst_of_mapM_res hf hzs]

/-- The variables `evalDoms` reports are exactly the domains' own variables
(`spectec/src/il/eval.ml:546-549`). -/
theorem map_fst_evalDoms {n : Nat} {env : Env} {ρ : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (h : evalDoms n env ρ ds = .ok xvs) :
    xvs.map Prod.fst = ds.map domVar := by
  cases n with
  | zero => simp only [evalDoms] at h; exact absurd h (by simp)
  | succ n =>
      simp only [evalDoms] at h
      refine map_fst_of_mapM_res (key := domVar) (fun d p hp => ?_) h
      simp only [Res.map_eq_ok] at hp
      obtain ⟨v, _, hv⟩ := hp
      cases hv
      rfl

/-- `List.filterMap` of a lookup that always succeeds keeps every key. -/
theorem map_fst_filterMap_getElem (i : Nat) :
    ∀ (ds : List (IL.Id × List Value)), (∀ p ∈ ds, i < p.2.length) →
      (ds.filterMap (fun d => (d.2[i]?).map fun v => (d.1, v))).map Prod.fst =
        ds.map Prod.fst
  | [], _ => rfl
  | d :: ds, h => by
      have hd : (d.2[i]?).isSome := by
        simp only [List.getElem?_eq_getElem (h d (by simp))]
        rfl
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hd
      simp only [List.filterMap_cons, hv, Option.map_some, List.map_cons]
      exact congrArg _ (map_fst_filterMap_getElem i ds (fun p hp => h p (by simp [hp])))

/-- `List.filterMap` of an option that is always `some` keeps every key. -/
theorem map_fst_filterMap_some :
    ∀ (os : List (IL.Id × Option Value)), (∀ p ∈ os, p.2.isSome) →
      (os.filterMap (fun p => p.2.map fun w => (p.1, w))).map Prod.fst = os.map Prod.fst
  | [], _ => rfl
  | o :: os, h => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (h o (by simp))
      simp only [List.filterMap_cons, hw, Option.map_some, List.map_cons]
      exact congrArg _ (map_fst_filterMap_some os (fun p hp => h p (by simp [hp])))

/-- The keys of one round of an iteration: every domain variable, plus the
`ListN` counter when there is one (`spectec/src/il/eval.ml:407-413`). -/
theorem map_fst_iterRow (ds : List (IL.Id × List Value)) (ido : Option IL.Id) (i : Nat)
    (h : ∀ p ∈ ds, i < p.2.length) :
    (iterRow ds ido i).map Prod.fst = ds.map Prod.fst ++ ido.toList := by
  simp only [iterRow, List.map_append, map_fst_filterMap_getElem i ds h]
  cases ido <;> simp

/-! ### Free-identifier bookkeeping -/

/-- `List.mapM` in `Res` is a congruence. -/
theorem mapM_congr {α β : Type} {f g : α → Res β} :
    ∀ (xs : List α), (∀ a ∈ xs, f a = g a) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.mapM_cons, h x (by simp),
        mapM_congr xs (fun a ha => h a (by simp [ha]))]

/-- `( -- )` (`spectec/src/xl/gen_free.ml:47`) is antitone in its second
argument. -/
theorem diff_subset_diff_right {t₁ t₂ : Sets} (s : Sets) (h : t₂ ⊆ t₁) :
    s.diff t₁ ⊆ s.diff t₂ := by
  obtain ⟨a, b, c, d, e⟩ := Sets.subset_def.1 h
  exact Sets.subset_def.2 ⟨Finset.sdiff_subset_sdiff (le_refl _) a,
    Finset.sdiff_subset_sdiff (le_refl _) b, Finset.sdiff_subset_sdiff (le_refl _) c,
    Finset.sdiff_subset_sdiff (le_refl _) d, Finset.sdiff_subset_sdiff (le_refl _) e⟩

/-- `keySet` turns list concatenation into `Sets.union`. -/
theorem keySet_append (xs ys : List IL.Id) :
    keySet (xs ++ ys) = (keySet xs).union (keySet ys) := by
  simp only [keySet, Sets.union, Sets.empty, List.toFinset_append, Finset.erase_union_distrib,
    Finset.union_empty]

/-- A single binder is covered by its own key. -/
theorem boundVarid_subset_keySet (y : IL.Id) : boundVarid y ⊆ keySet [y] := by
  by_cases h : y = "_"
  · simp [boundVarid, h]
  · refine Sets.subset_def.2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [boundVarid, freeVarid, keySet, Sets.empty, h]

/-- Every variable an iteration's domains bind is a key of the rows the
evaluator builds from those domains. -/
theorem boundDoms_subset_keySet : ∀ ds : List Dom, boundDoms ds ⊆ keySet (ds.map domVar)
  | [] => by simp only [boundDoms, List.map_nil]; exact Sets.empty_subset _
  | .mk y e :: ds => by
      show (boundVarid y).union (boundDoms ds) ⊆ keySet ([y] ++ ds.map domVar)
      rw [keySet_append]
      exact Sets.union_subset_union (boundVarid_subset_keySet y) (boundDoms_subset_keySet ds)

/-- The counter variable of a `ListN` iteration is covered by its own key. -/
theorem boundIter_listN_subset_keySet (eₙ : Exp) (xo : Option IL.Id) :
    boundIter (.listN eₙ xo) ⊆ keySet xo.toList := by
  cases xo with
  | none => simp only [boundIter, freeOpt]; exact Sets.empty_subset _
  | some y => exact boundVarid_subset_keySet y

/-- **The round invariant.**  If the two scopes agree on `s`, if the bindings
`r` cover `B`, and if `t` minus `B` is inside `s`, then the two scopes extended
by `r` agree on `t`.  Every `IterE` clause below is an instance: `t` is the
body's `freeExp`, `B` is `boundIterExp`, and `r` is the round. -/
theorem agreeOn_body {ρ₁ ρ₂ : VarEnv} {s B t : Sets} {r : List (IL.Id × Value)}
    (hρ : VarEnv.AgreeOn s ρ₁ ρ₂) (hB : B ⊆ rowSet r) (ht : t.diff B ⊆ s) :
    VarEnv.AgreeOn t (ρ₁.bindVals r) (ρ₂.bindVals r) :=
  (((hρ.bindVals r).union (VarEnv.agreeOn_rowSet ρ₁ ρ₂ r)).mono
    (Sets.Subset.trans (subset_diff_union t B) (Sets.union_subset_union ht hB)))

/-- A member of a list of expressions is free in the list
(`spectec/src/xl/gen_free.ml:84`). -/
theorem freeExp_subset_freeExps : ∀ {e : Exp} {es : List Exp}, e ∈ es → freeExp e ⊆ freeExps es
  | _, [], h => absurd h (by simp)
  | e, f :: fs, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp only [freeExps]; exact Sets.subset_union_left _ _
      · exact Sets.Subset.trans (freeExp_subset_freeExps h) (Sets.subset_union_right _ _)

/-- A member of a list of record fields is free in the list. -/
theorem freeExpField_subset_freeExpFields :
    ∀ {f : ExpField} {fs : List ExpField}, f ∈ fs → freeExpField f ⊆ freeExpFields fs
  | _, [], h => absurd h (by simp)
  | f, g :: gs, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp only [freeExpFields]; exact Sets.subset_union_left _ _
      · exact Sets.Subset.trans (freeExpField_subset_freeExpFields h)
          (Sets.subset_union_right _ _)

/-- A member of an argument list is free in the list
(`spectec/src/il/free.ml:155`). -/
theorem freeArg_subset_freeArgs :
    ∀ {a : Arg} {as : List Arg}, a ∈ as → freeArg a ⊆ freeArgs as
  | _, [], h => absurd h (by simp)
  | a, b :: bs, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp only [freeArgs]; exact Sets.subset_union_left _ _
      · exact Sets.Subset.trans (freeArg_subset_freeArgs h) (Sets.subset_union_right _ _)

/-- A member of an iteration's domain list is free in the list
(`spectec/src/il/free.ml:89`). -/
theorem freeDom_subset_freeDoms :
    ∀ {d : Dom} {ds : List Dom}, d ∈ ds → freeDom d ⊆ freeDoms ds
  | _, [], h => absurd h (by simp)
  | d, c :: cs, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp only [freeDoms]; exact Sets.subset_union_left _ _
      · exact Sets.Subset.trans (freeDom_subset_freeDoms h) (Sets.subset_union_right _ _)

/-- A domain's free identifiers are those of the expression it ranges over. -/
theorem freeDom_eq (d : Dom) : freeDom d = freeExp (domSrc d) := by
  cases d; rfl

/-- Shallow type resolution reads only the type variables free in its
argument (`spectec/src/il/eval.ml:636`). -/
theorem resolveTyp_agreeOn {ρ₁ ρ₂ : VarEnv} {t : Typ}
    (h : VarEnv.AgreeOn (freeTyp t) ρ₁ ρ₂) : resolveTyp ρ₁ t = resolveTyp ρ₂ t := by
  cases t with
  | varT x args =>
      cases args with
      | nil =>
          simp only [freeTyp] at h
          simp only [resolveTyp, h.union_left.findTyp?]
      | cons a as => simp [resolveTyp]
  | _ => simp [resolveTyp]

/-- Shallow grammar resolution reads only the grammar variables free in its
argument (`spectec/src/il/eval.ml:638`). -/
theorem resolveSym_agreeOn {ρ₁ ρ₂ : VarEnv} {g : Sym}
    (h : VarEnv.AgreeOn (freeSym g) ρ₁ ρ₂) : resolveSym ρ₁ g = resolveSym ρ₂ g := by
  cases g with
  | varG x args =>
      cases args with
      | nil =>
          simp only [freeSym] at h
          simp only [resolveSym, h.union_left.findGram?]
      | cons a as => simp [resolveSym]
  | _ => simp [resolveSym]

/-! ### Congruence combinators for `Res` -/

/-- `>>=` is a congruence in its continuation, which only has to agree on the
values the scrutinee can actually produce. -/
theorem bind_congr {α β : Type} {r : Res α} {f g : α → Res β}
    (h : ∀ a, r = .ok a → f a = g a) : (r >>= f) = (r >>= g) := by
  cases r with
  | error e => rfl
  | ok a => exact h a rfl

/-- `Res.assert` is a congruence in its body, which only has to agree when the
condition holds. -/
theorem assert_congr {α : Type} {c : Prop} [Decidable c] {r₁ r₂ : Res α}
    (h : c → r₁ = r₂) : Res.assert c r₁ = Res.assert c r₂ := by
  by_cases hc : c
  · simp only [Res.assert, hc, ite_true, h hc]
  · simp only [Res.assert, hc, ite_false]

/-- `Except.ok` is a left unit for `>>=`, as a rewrite rule: `simp` does not
reduce a `do` block whose scrutinee is a literal `Except.ok`. -/
theorem ok_bind {α β : Type} (a : α) (f : α → Res β) : (Except.ok a >>= f) = f a := rfl

/-- `Except.error` is absorbing for `>>=`, as a rewrite rule; see
`ok_bind`. -/
theorem error_bind {α β : Type} (er : Stuck) (f : α → Res β) :
    ((Except.error er : Res α) >>= f) = Except.error er := rfl

/-- `ite` is a congruence in both branches, each under its own hypothesis. -/
theorem ite_congr {α : Type} {c : Prop} [Decidable c] {a₁ a₂ b₁ b₂ : α}
    (ha : c → a₁ = a₂) (hb : ¬ c → b₁ = b₂) :
    (if c then a₁ else b₁) = (if c then a₂ else b₂) := by
  by_cases h : c
  · simp only [h, ite_true, ha h]
  · simp only [h, ite_false, hb h]

end EvalFree

/-! ## The induction -/

/-- The free-variable invariant, stated for every member of
`Silmaril/SpecTec/Sem/Eval.lean`'s mutual block that an `evalExp` can reach
with a scope of its own.

`tryClauses`, `derives` and `anyRule` are absent on purpose: none of them
takes a `VarEnv` at all.  A clause body is evaluated in a scope built from
`VarEnv.empty` (`spectec/src/il/eval.ml:664`) and a rule is tried in a scope
built from `bindParams VarEnv.empty` (`eval.ml:654`), so the caller's scope
cannot reach them and the induction closes without them.  The remaining
fifteen members of the block — `matchExp` and the premise machinery — are
reachable only through `tryClauses`, and are therefore also out of the loop;
see the scope section at the end of this file for what is and is not claimed
about them. -/
structure AgreeAt (n : Nat) : Prop where
  /-- `evalExp` reads only the identifiers `freeExp` reports. -/
  exp : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (e : Exp),
    VarEnv.AgreeOn (freeExp e) ρ₁ ρ₂ → evalExp n env ρ₁ e = evalExp n env ρ₂ e
  /-- `evalExps` reads only the identifiers `freeExps` reports. -/
  exps : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (es : List Exp),
    VarEnv.AgreeOn (freeExps es) ρ₁ ρ₂ → evalExps n env ρ₁ es = evalExps n env ρ₂ es
  /-- `evalExpFields` reads only the identifiers `freeExpFields` reports. -/
  expFields : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (fs : List ExpField),
    VarEnv.AgreeOn (freeExpFields fs) ρ₁ ρ₂ →
      evalExpFields n env ρ₁ fs = evalExpFields n env ρ₂ fs
  /-- `evalArg` reads only the identifiers `freeArg` reports. -/
  arg : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (a : Arg),
    VarEnv.AgreeOn (freeArg a) ρ₁ ρ₂ → evalArg n env ρ₁ a = evalArg n env ρ₂ a
  /-- `evalArgs` reads only the identifiers `freeArgs` reports. -/
  args : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (as : List Arg),
    VarEnv.AgreeOn (freeArgs as) ρ₁ ρ₂ → evalArgs n env ρ₁ as = evalArgs n env ρ₂ as
  /-- `evalDoms` reads only the identifiers `freeDoms` reports. -/
  doms : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (ds : List Dom),
    VarEnv.AgreeOn (freeDoms ds) ρ₁ ρ₂ → evalDoms n env ρ₁ ds = evalDoms n env ρ₂ ds
  /-- `evalIterE` reads only the identifiers `freeExp` reports for the whole
  `IterE`, that is, the body minus the domain variables together with the
  domain expressions. -/
  iterE : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (e : Exp) (it : Iter) (ds : List Dom),
    VarEnv.AgreeOn (freeExp (.iterE e (.mk it ds))) ρ₁ ρ₂ →
      evalIterE n env ρ₁ e it ds = evalIterE n env ρ₂ e it ds
  /-- `evalIterList` has already evaluated the domains, so its invariant is
  stated modulo the identifiers the rows it is about to build will bind: the
  keys of `xvs`, plus the `ListN` counter. -/
  iterList : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (e : Exp) (xvs : List (IL.Id × Value))
      (ido : Option IL.Id) (k : Nat) (s : Sets), VarEnv.AgreeOn s ρ₁ ρ₂ →
      (freeExp e).diff (EvalFree.keySet (xvs.map Prod.fst ++ ido.toList)) ⊆ s →
        evalIterList n env ρ₁ e xvs ido k = evalIterList n env ρ₂ e xvs ido k
  /-- `evalRounds` is given the rows outright, so its invariant is the
  per-round agreement itself. -/
  rounds : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (e : Exp) (rows : List (List (IL.Id × Value))),
    (∀ r ∈ rows, VarEnv.AgreeOn (freeExp e) (ρ₁.bindVals r) (ρ₂.bindVals r)) →
      evalRounds n env ρ₁ e rows = evalRounds n env ρ₂ e rows
  /-- `pathGet` reads only the identifiers `freePath` reports. -/
  pathGet : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (v : Value) (p : Path),
    VarEnv.AgreeOn (freePath p) ρ₁ ρ₂ → pathGet n env ρ₁ v p = pathGet n env ρ₂ v p
  /-- `pathSet` reads only the identifiers `freePath` reports. -/
  pathSet : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (v : Value) (p : Path) (w : Value),
    VarEnv.AgreeOn (freePath p) ρ₁ ρ₂ → pathSet n env ρ₁ v p w = pathSet n env ρ₂ v p w
  /-- `callDef` reads only the called name and the identifiers free in the
  arguments. -/
  callDef : ∀ (env : Env) (ρ₁ ρ₂ : VarEnv) (x : IL.Id) (as : List Arg),
    VarEnv.AgreeOn (freeExp (.callE x as)) ρ₁ ρ₂ → callDef n env ρ₁ x as = callDef n env ρ₂ x as

/-- With no fuel every member answers `outOfFuel`, whatever the scope. -/
theorem agreeAt_zero : AgreeAt 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
      | simp only [evalExp]
      | simp only [evalExps]
      | simp only [evalExpFields]
      | simp only [evalArg]
      | simp only [evalArgs]
      | simp only [evalDoms]
      | simp only [evalIterE]
      | simp only [evalIterList]
      | simp only [evalRounds]
      | simp only [pathGet]
      | simp only [pathSet]
      | simp only [callDef]

/-- The inductive step: one unit of fuel at a time, by structural recursion
on the fuel, exactly as `monoAt_succ` does for monotonicity.  Every member is
unfolded once and recombined with the congruences above; the only clauses that
need more are the four `IterE` iterators, where the body is evaluated under a
row of bindings and the invariant has to be re-established modulo the domain
variables (`EvalFree.agreeOn_body`). -/
theorem agreeAt_succ : ∀ n, AgreeAt n
  | 0 => agreeAt_zero
  | n + 1 => by
      have ih := agreeAt_succ n
      have hexp := ih.exp
      have hexps := ih.exps
      have hefs := ih.expFields
      have harg := ih.arg
      have hargs := ih.args
      have hdoms := ih.doms
      have hit := ih.iterE
      have hitl := ih.iterList
      have hrnd := ih.rounds
      have hpg := ih.pathGet
      have hps := ih.pathSet
      have hcd := ih.callDef
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- `evalExp`
      · intro env ρ₁ ρ₂ e h
        cases e with
        | varE x =>
            simp only [freeExp] at h
            simp only [evalExp, h.findVal?]
        | boolE b => simp only [evalExp]
        | numE m => simp only [evalExp]
        | textE t => simp only [evalExp]
        | unE op t e =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | binE op t e₁ e₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_right]
        | cmpE op t e₁ e₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_right]
        | tupE es =>
            simp only [freeExp] at h
            simp only [evalExp, hexps env ρ₁ ρ₂ es h]
        | projE e i =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | caseE op e =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | uncaseE e op =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | optE eo =>
            cases eo with
            | none => simp only [evalExp]
            | some e =>
                simp only [freeExp, freeExpOpt] at h
                simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | theE e =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | strE fs =>
            simp only [freeExp] at h
            simp only [evalExp, hefs env ρ₁ ρ₂ fs h]
        | dotE e a =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | compE e₁ e₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_right]
        | listE es =>
            simp only [freeExp] at h
            simp only [evalExp, hexps env ρ₁ ρ₂ es h]
        | liftE e =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | memE e₁ e₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_right]
        | lenE e =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | catE e₁ e₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_right]
        | idxE e₁ e₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_right]
        | sliceE e₁ e₂ e₃ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_left.union_right,
              hexp env ρ₁ ρ₂ e₃ h.union_right]
        | updE e₁ p e₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_right,
              hps env ρ₁ ρ₂ _ p _ h.union_left.union_right]
        | extE e₁ p e₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e₁ h.union_left.union_left,
              hexp env ρ₁ ρ₂ e₂ h.union_right,
              hpg env ρ₁ ρ₂ _ p h.union_left.union_right,
              hps env ρ₁ ρ₂ _ p _ h.union_left.union_right]
        | callE x as =>
            simp only [evalExp]
            exact hcd env ρ₁ ρ₂ x as h
        | iterE e₀ it =>
            cases it with
            | mk i ds =>
                simp only [evalExp]
                exact hit env ρ₁ ρ₂ e₀ i ds h
        | cvtE e t₁ t₂ =>
            simp only [freeExp] at h
            simp only [evalExp, hexp env ρ₁ ρ₂ e h]
        | subE e t₁ t₂ =>
            simp only [freeExp] at h
            simp only [evalExp]
            exact hexp env ρ₁ ρ₂ e h.union_left.union_left
      -- `evalExps`
      · intro env ρ₁ ρ₂ es h
        simp only [evalExps]
        exact EvalFree.mapM_congr es fun e he =>
          hexp env ρ₁ ρ₂ e (h.mono (EvalFree.freeExp_subset_freeExps he))
      -- `evalExpFields`
      · intro env ρ₁ ρ₂ fs h
        simp only [evalExpFields]
        refine EvalFree.mapM_congr fs fun f hf => ?_
        cases f with
        | mk a e =>
            have hfe : VarEnv.AgreeOn (freeExp e) ρ₁ ρ₂ :=
              h.mono (EvalFree.freeExpField_subset_freeExpFields hf)
            simp only [hexp env ρ₁ ρ₂ e hfe]
      -- `evalArg`
      · intro env ρ₁ ρ₂ a h
        cases a with
        | expA e =>
            simp only [freeArg] at h
            simp only [evalArg, hexp env ρ₁ ρ₂ e h]
        | typA t =>
            simp only [freeArg] at h
            simp only [evalArg, EvalFree.resolveTyp_agreeOn h]
        | defA x =>
            simp only [freeArg] at h
            simp only [evalArg, h.findDef?]
        | gramA g =>
            simp only [freeArg] at h
            simp only [evalArg, EvalFree.resolveSym_agreeOn h]
      -- `evalArgs`
      · intro env ρ₁ ρ₂ as h
        simp only [evalArgs]
        exact EvalFree.mapM_congr as fun a ha =>
          harg env ρ₁ ρ₂ a (h.mono (EvalFree.freeArg_subset_freeArgs ha))
      -- `evalDoms`
      · intro env ρ₁ ρ₂ ds h
        simp only [evalDoms]
        refine EvalFree.mapM_congr ds fun d hd => ?_
        have hdd : VarEnv.AgreeOn (freeDom d) ρ₁ ρ₂ :=
          h.mono (EvalFree.freeDom_subset_freeDoms hd)
        rw [EvalFree.freeDom_eq d] at hdd
        simp only [hexp env ρ₁ ρ₂ (domSrc d) hdd]
      -- `evalIterE`
      · intro env ρ₁ ρ₂ e it ds h
        simp only [freeExp] at h
        have hdiff := h.union_left
        have hIE := h.union_right
        simp only [freeIterExp] at hIE
        have hdm := hIE.union_right
        cases it with
        | opt =>
            simp only [evalIterE, hdoms env ρ₁ ρ₂ ds hdm]
            refine EvalFree.bind_congr fun xvs hxvs => EvalFree.assert_congr fun _ => ?_
            refine EvalFree.bind_congr fun os hos => ?_
            refine EvalFree.ite_congr (fun _ => rfl) fun _ => ?_
            refine EvalFree.ite_congr (fun h2 => ?_) fun _ => rfl
            have hosfst : os.map Prod.fst = xvs.map Prod.fst :=
              EvalFree.map_fst_of_mapM_option (key := Prod.fst)
                (fun a p hp => by
                  simp only [Option.map_eq_some_iff] at hp
                  obtain ⟨o, _, ho⟩ := hp
                  cases ho; rfl)
                (Res.ofOption_eq_ok.1 hos)
            have hfst : (os.filterMap fun p => p.2.map fun w => (p.1, w)).map Prod.fst
                = ds.map domVar := by
              rw [EvalFree.map_fst_filterMap_some os
                (fun p hp => by simpa using List.all_eq_true.1 h2 p hp)]
              rw [hosfst, EvalFree.map_fst_evalDoms hxvs]
            have hB : boundIterExp (IterExp.mk Iter.opt ds) ⊆
                EvalFree.rowSet (os.filterMap fun p => p.2.map fun w => (p.1, w)) := by
              simp only [boundIterExp, boundIter, Sets.empty_union, EvalFree.rowSet, hfst]
              exact EvalFree.boundDoms_subset_keySet ds
            have hbody := EvalFree.agreeOn_body hdiff hB (Sets.Subset.refl _)
            rw [hexp env _ _ e hbody]
        | list =>
            simp only [evalIterE, hdoms env ρ₁ ρ₂ ds hdm]
            refine EvalFree.bind_congr fun xvs hxvs => EvalFree.assert_congr fun _ => ?_
            refine EvalFree.bind_congr fun k _ => ?_
            refine hitl env ρ₁ ρ₂ e xvs none k _ hdiff ?_
            refine EvalFree.diff_subset_diff_right _ ?_
            simp only [boundIterExp, boundIter, Sets.empty_union, Option.toList_none,
              List.append_nil, EvalFree.map_fst_evalDoms hxvs]
            exact EvalFree.boundDoms_subset_keySet ds
        | list1 =>
            simp only [evalIterE, hdoms env ρ₁ ρ₂ ds hdm]
            refine EvalFree.bind_congr fun xvs hxvs => EvalFree.assert_congr fun _ => ?_
            refine EvalFree.bind_congr fun k _ => EvalFree.assert_congr fun _ => ?_
            refine hitl env ρ₁ ρ₂ e xvs none k _ hdiff ?_
            refine EvalFree.diff_subset_diff_right _ ?_
            simp only [boundIterExp, boundIter, Sets.empty_union, Option.toList_none,
              List.append_nil, EvalFree.map_fst_evalDoms hxvs]
            exact EvalFree.boundDoms_subset_keySet ds
        | listN eₙ xo =>
            simp only [freeIter] at hIE
            have hn := hIE.union_left
            simp only [evalIterE, hdoms env ρ₁ ρ₂ ds hdm, hexp env ρ₁ ρ₂ eₙ hn]
            refine EvalFree.bind_congr fun xvs hxvs => EvalFree.bind_congr fun kv _ => ?_
            refine EvalFree.bind_congr fun k _ => ?_
            refine hitl env ρ₁ ρ₂ e xvs xo k _ hdiff ?_
            refine EvalFree.diff_subset_diff_right _ ?_
            simp only [boundIterExp, EvalFree.keySet_append, EvalFree.map_fst_evalDoms hxvs]
            rw [Sets.union_comm (boundIter (Iter.listN eₙ xo)) (boundDoms ds)]
            exact Sets.union_subset_union (EvalFree.boundDoms_subset_keySet ds)
              (EvalFree.boundIter_listN_subset_keySet eₙ xo)
      -- `evalIterList`
      · intro env ρ₁ ρ₂ e xvs ido k s hρ hsub
        simp only [evalIterList]
        refine EvalFree.bind_congr fun ds hds => EvalFree.assert_congr fun hlen => ?_
        have hdsfst : ds.map Prod.fst = xvs.map Prod.fst :=
          EvalFree.map_fst_of_mapM_option (key := Prod.fst)
            (fun a p hp => by
              simp only [Option.map_eq_some_iff] at hp
              obtain ⟨l, _, hl⟩ := hp
              cases hl; rfl)
            (Res.ofOption_eq_ok.1 hds)
        have hlen' : ∀ p ∈ ds, p.2.length = k := by
          intro p hp
          have := List.all_eq_true.1 hlen p hp
          simpa using this
        have hrows : ∀ r ∈ iterRows ds ido k,
            VarEnv.AgreeOn (freeExp e) (ρ₁.bindVals r) (ρ₂.bindVals r) := by
          intro r hr
          simp only [iterRows, List.mem_map, List.mem_range] at hr
          obtain ⟨i, hi, rfl⟩ := hr
          refine EvalFree.agreeOn_body hρ ?_ hsub
          rw [EvalFree.rowSet,
            EvalFree.map_fst_iterRow ds ido i (fun p hp => by rw [hlen' p hp]; exact hi),
            hdsfst]
        rw [hrnd env ρ₁ ρ₂ e (iterRows ds ido k) hrows]
      -- `evalRounds`
      · intro env ρ₁ ρ₂ e rows hrows
        simp only [evalRounds]
        exact EvalFree.mapM_congr rows fun r hr => hexp env _ _ e (hrows r hr)
      -- `pathGet`
      · intro env ρ₁ ρ₂ v p h
        cases p with
        | rootP => simp only [pathGet]
        | idxP p e =>
            simp only [freePath] at h
            simp only [pathGet, hpg env ρ₁ ρ₂ v p h.union_left,
              hexp env ρ₁ ρ₂ e h.union_right]
        | sliceP p e₁ e₂ =>
            simp only [freePath] at h
            simp only [pathGet, hpg env ρ₁ ρ₂ v p h.union_left.union_left,
              hexp env ρ₁ ρ₂ e₁ h.union_left.union_right,
              hexp env ρ₁ ρ₂ e₂ h.union_right]
        | dotP p a =>
            simp only [freePath] at h
            simp only [pathGet, hpg env ρ₁ ρ₂ v p h]
      -- `pathSet`
      · intro env ρ₁ ρ₂ v p w h
        cases p with
        | rootP => simp only [pathSet]
        | idxP p e =>
            simp only [freePath] at h
            simp only [pathSet, hpg env ρ₁ ρ₂ v p h.union_left,
              hexp env ρ₁ ρ₂ e h.union_right, hps env ρ₁ ρ₂ v p _ h.union_left]
        | sliceP p e₁ e₂ =>
            simp only [freePath] at h
            simp only [pathSet, hpg env ρ₁ ρ₂ v p h.union_left.union_left,
              hexp env ρ₁ ρ₂ e₁ h.union_left.union_right,
              hexp env ρ₁ ρ₂ e₂ h.union_right,
              hps env ρ₁ ρ₂ v p _ h.union_left.union_left]
        | dotP p a =>
            simp only [freePath] at h
            simp only [pathSet, hpg env ρ₁ ρ₂ v p h, hps env ρ₁ ρ₂ v p _ h]
      -- `callDef`
      · intro env ρ₁ ρ₂ x as h
        simp only [freeExp] at h
        simp only [callDef, hargs env ρ₁ ρ₂ as h.union_right, h.union_left.findDef?]

/-! ## The free-variable lemma -/

/-- **The free-variable lemma for the evaluator.**  `evalExp n env ρ e`
depends only on the restriction of `ρ` to `Silmaril.SpecTec.IL.freeExp e`.

This is the statement `Silmaril/SpecTec/Sem/Eval.lean` lists as open in its
section "The metatheory that is *not* here". -/
theorem evalExp_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {e : Exp}
    (h : VarEnv.AgreeOn (freeExp e) ρ₁ ρ₂) : evalExp n env ρ₁ e = evalExp n env ρ₂ e :=
  (agreeAt_succ n).exp env ρ₁ ρ₂ e h

/-- The same statement with `VarEnv.AgreeOn` unfolded, word for word as
`Silmaril/SpecTec/Sem/Eval.lean` writes it in "The metatheory that is *not*
here", so that the claim can be checked against that text without unfolding
anything. -/
theorem evalExp_eq_of_find?_eq {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {e : Exp}
    (hval : ∀ x ∈ (freeExp e).varid, ρ₁.findVal? x = ρ₂.findVal? x)
    (htyp : ∀ x ∈ (freeExp e).typid, ρ₁.findTyp? x = ρ₂.findTyp? x)
    (hdef : ∀ x ∈ (freeExp e).defid, ρ₁.findDef? x = ρ₂.findDef? x)
    (hgram : ∀ x ∈ (freeExp e).gramid, ρ₁.findGram? x = ρ₂.findGram? x) :
    evalExp n env ρ₁ e = evalExp n env ρ₂ e :=
  evalExp_agreeOn ⟨hval, htyp, hdef, hgram⟩

/-- `evalExps` depends only on the restriction of `ρ` to `freeExps es`. -/
theorem evalExps_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {es : List Exp}
    (h : VarEnv.AgreeOn (freeExps es) ρ₁ ρ₂) : evalExps n env ρ₁ es = evalExps n env ρ₂ es :=
  (agreeAt_succ n).exps env ρ₁ ρ₂ es h

/-- `evalExpFields` depends only on the restriction of `ρ` to
`freeExpFields fs`. -/
theorem evalExpFields_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {fs : List ExpField}
    (h : VarEnv.AgreeOn (freeExpFields fs) ρ₁ ρ₂) :
    evalExpFields n env ρ₁ fs = evalExpFields n env ρ₂ fs :=
  (agreeAt_succ n).expFields env ρ₁ ρ₂ fs h

/-- `evalArg` depends only on the restriction of `ρ` to `freeArg a`; note that
this covers the three *unevaluated* arguments, whose only dependence on the
scope is the shallow resolution `resolveTyp`/`resolveSym` and the `DefA`
lookup (`spectec/src/il/eval.ml:636-638`). -/
theorem evalArg_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {a : Arg}
    (h : VarEnv.AgreeOn (freeArg a) ρ₁ ρ₂) : evalArg n env ρ₁ a = evalArg n env ρ₂ a :=
  (agreeAt_succ n).arg env ρ₁ ρ₂ a h

/-- `evalArgs` depends only on the restriction of `ρ` to `freeArgs as`. -/
theorem evalArgs_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {as : List Arg}
    (h : VarEnv.AgreeOn (freeArgs as) ρ₁ ρ₂) : evalArgs n env ρ₁ as = evalArgs n env ρ₂ as :=
  (agreeAt_succ n).args env ρ₁ ρ₂ as h

/-- `evalDoms` depends only on the restriction of `ρ` to `freeDoms ds`. -/
theorem evalDoms_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {ds : List Dom}
    (h : VarEnv.AgreeOn (freeDoms ds) ρ₁ ρ₂) : evalDoms n env ρ₁ ds = evalDoms n env ρ₂ ds :=
  (agreeAt_succ n).doms env ρ₁ ρ₂ ds h

/-- `evalIterE` depends only on the restriction of `ρ` to the free
identifiers of the whole `IterE`, that is, to the body minus the domain
variables together with the domain expressions
(`spectec/src/il/free.ml:75`). -/
theorem evalIterE_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {e : Exp} {it : Iter}
    {ds : List Dom} (h : VarEnv.AgreeOn (freeExp (.iterE e (.mk it ds))) ρ₁ ρ₂) :
    evalIterE n env ρ₁ e it ds = evalIterE n env ρ₂ e it ds :=
  (agreeAt_succ n).iterE env ρ₁ ρ₂ e it ds h

/-- `pathGet` depends only on the restriction of `ρ` to `freePath p`. -/
theorem pathGet_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {v : Value} {p : Path}
    (h : VarEnv.AgreeOn (freePath p) ρ₁ ρ₂) : pathGet n env ρ₁ v p = pathGet n env ρ₂ v p :=
  (agreeAt_succ n).pathGet env ρ₁ ρ₂ v p h

/-- `pathSet` depends only on the restriction of `ρ` to `freePath p`. -/
theorem pathSet_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {v : Value} {p : Path}
    {w : Value} (h : VarEnv.AgreeOn (freePath p) ρ₁ ρ₂) :
    pathSet n env ρ₁ v p w = pathSet n env ρ₂ v p w :=
  (agreeAt_succ n).pathSet env ρ₁ ρ₂ v p w h

/-- `callDef` depends only on the restriction of `ρ` to the called name and
the free identifiers of the arguments. -/
theorem callDef_agreeOn {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {x : IL.Id} {as : List Arg}
    (h : VarEnv.AgreeOn (freeExp (.callE x as)) ρ₁ ρ₂) :
    callDef n env ρ₁ x as = callDef n env ρ₂ x as :=
  (agreeAt_succ n).callDef env ρ₁ ρ₂ x as h

/-- The relational form: a denotation survives any change of scope that
preserves the free identifiers. -/
theorem EvalExp.agreeOn {env : Env} {ρ₁ ρ₂ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ₁ e v) (hρ : VarEnv.AgreeOn (freeExp e) ρ₁ ρ₂) : EvalExp env ρ₂ e v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (evalExp_agreeOn hρ).symm.trans hn⟩

/-- The relational form, as an equivalence. -/
theorem evalExp_iff_agreeOn {env : Env} {ρ₁ ρ₂ : VarEnv} {e : Exp} {v : Value}
    (hρ : VarEnv.AgreeOn (freeExp e) ρ₁ ρ₂) : EvalExp env ρ₁ e v ↔ EvalExp env ρ₂ e v :=
  ⟨fun h => h.agreeOn hρ, fun h => h.agreeOn hρ.symm⟩

/-! ## Stability under extending the scope -/

namespace VarEnv

variable {s : Sets} {ρ : VarEnv} {x : IL.Id}

/-- A scope agrees with itself extended by a term variable the set does not
mention. -/
theorem agreeOn_bindVal_self (hx : x ∉ s.varid) (v : Value) :
    AgreeOn s (ρ.bindVal x v) ρ :=
  ⟨fun y hy => Map.find?_bind_of_ne _ (by rintro rfl; exact hx hy) v,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- A scope agrees with itself extended by a type variable the set does not
mention. -/
theorem agreeOn_bindTyp_self (hx : x ∉ s.typid) (t : Typ) :
    AgreeOn s (ρ.bindTyp x t) ρ :=
  ⟨fun _ _ => rfl, fun y hy => Map.find?_bind_of_ne _ (by rintro rfl; exact hx hy) t,
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- A scope agrees with itself extended by a definition variable the set does
not mention. -/
theorem agreeOn_bindDef_self (hx : x ∉ s.defid) (y : IL.Id) :
    AgreeOn s (ρ.bindDef x y) ρ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl,
    fun z hz => Map.find?_bind_of_ne _ (by rintro rfl; exact hx hz) y, fun _ _ => rfl⟩

/-- A scope agrees with itself extended by a grammar variable the set does not
mention. -/
theorem agreeOn_bindGram_self (hx : x ∉ s.gramid) (g : Sym) :
    AgreeOn s (ρ.bindGram x g) ρ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun z hz => Map.find?_bind_of_ne _ (by rintro rfl; exact hx hz) g⟩

/-- A scope agrees with itself extended by a whole row of term variables none
of which the set mentions. -/
theorem agreeOn_bindVals_self (r : List (IL.Id × Value))
    (hr : ∀ p ∈ r, p.1 ∉ s.varid) : AgreeOn s (ρ.bindVals r) ρ := by
  refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  refine EvalFree.find?_binds_of_not_bound r _ (Or.inr fun hmem => ?_)
  obtain ⟨p, hp, hpy⟩ := List.mem_map.1 hmem
  exact hr p hp (hpy ▸ hy)

end VarEnv

/-- **Weakening.**  Binding a term variable that is not free in `e` does not
change what `e` denotes. -/
theorem evalExp_bindVal_of_notMem {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp}
    {x : IL.Id} {v : Value} (hx : x ∉ (freeExp e).varid) :
    evalExp n env (ρ.bindVal x v) e = evalExp n env ρ e :=
  evalExp_agreeOn (VarEnv.agreeOn_bindVal_self hx v)

/-- Binding a type variable that is not free in `e` does not change what `e`
denotes. -/
theorem evalExp_bindTyp_of_notMem {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp}
    {x : IL.Id} {t : Typ} (hx : x ∉ (freeExp e).typid) :
    evalExp n env (ρ.bindTyp x t) e = evalExp n env ρ e :=
  evalExp_agreeOn (VarEnv.agreeOn_bindTyp_self hx t)

/-- Binding a definition variable that is not free in `e` does not change what
`e` denotes. -/
theorem evalExp_bindDef_of_notMem {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp}
    {x y : IL.Id} (hx : x ∉ (freeExp e).defid) :
    evalExp n env (ρ.bindDef x y) e = evalExp n env ρ e :=
  evalExp_agreeOn (VarEnv.agreeOn_bindDef_self hx y)

/-- Binding a grammar variable that is not free in `e` does not change what
`e` denotes. -/
theorem evalExp_bindGram_of_notMem {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp}
    {x : IL.Id} {g : Sym} (hx : x ∉ (freeExp e).gramid) :
    evalExp n env (ρ.bindGram x g) e = evalExp n env ρ e :=
  evalExp_agreeOn (VarEnv.agreeOn_bindGram_self hx g)

/-- Binding a whole row of term variables none of which is free in `e` does
not change what `e` denotes.  This is the form an iteration needs: the body of
an `IterE` that mentions none of the domain variables is evaluated to the same
value in every round. -/
theorem evalExp_bindVals_of_notMem {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp}
    {r : List (IL.Id × Value)} (hr : ∀ p ∈ r, p.1 ∉ (freeExp e).varid) :
    evalExp n env (ρ.bindVals r) e = evalExp n env ρ e :=
  evalExp_agreeOn (VarEnv.agreeOn_bindVals_self r hr)

/-- The relational form of `evalExp_bindVal_of_notMem`. -/
theorem EvalExp.bindVal_of_notMem {env : Env} {ρ : VarEnv} {e : Exp} {v w : Value}
    {x : IL.Id} (hx : x ∉ (freeExp e).varid) (h : EvalExp env ρ e v) :
    EvalExp env (ρ.bindVal x w) e v :=
  h.agreeOn (VarEnv.agreeOn_bindVal_self hx w).symm

/-! ## The clauses of a definition are closed -/

/-- `callDef` unfolded: the *only* two places the caller's scope `ρ` appears
are the evaluation of the arguments and the resolution of the called name.
`tryClauses` — which matches the clause patterns in `VarEnv.empty`
(`spectec/src/il/eval.ml:654`) and evaluates the chosen body in the scope that
match builds (`eval.ml:664`) — takes no `VarEnv` at all. -/
theorem callDef_eq (n : Nat) (env : Env) (ρ : VarEnv) (x : IL.Id) (as : List Arg) :
    callDef (n + 1) env ρ x as =
      (do
        let argVs ← evalArgs n env ρ as
        let d ← Res.ofOption (env.findDef? ((ρ.findDef? x).getD x))
        Res.elimUndef (tryClauses n env d.2.2 argVs) .ok
          (fun _ => Res.ofOption (env.builtins.call ((ρ.findDef? x).getD x) argVs))) := by
  simp only [callDef]

/-- **A call does not depend on the caller's scope beyond the name it
resolves to and the values of its arguments.**  Two calls — possibly to
syntactically different names, from different scopes, with different argument
syntax — agree as soon as they resolve to the same global definition and
evaluate their arguments to the same list.  This is the precise sense in which
a definition's clauses are closed. -/
theorem callDef_eq_of_resolved {n : Nat} {env : Env} {ρ₁ ρ₂ : VarEnv} {x₁ x₂ : IL.Id}
    {as₁ as₂ : List Arg} (hx : (ρ₁.findDef? x₁).getD x₁ = (ρ₂.findDef? x₂).getD x₂)
    (ha : evalArgs n env ρ₁ as₁ = evalArgs n env ρ₂ as₂) :
    callDef (n + 1) env ρ₁ x₁ as₁ = callDef (n + 1) env ρ₂ x₂ as₂ := by
  simp only [callDef, hx, ha]

/-- A call whose name is not a `DefP` parameter and whose arguments are
already values can be evaluated in any scope at all — in particular in
`VarEnv.empty`. -/
theorem callDef_eq_empty {n : Nat} {env : Env} {ρ : VarEnv} {x : IL.Id} {as : List Arg}
    (hx : ρ.findDef? x = none) (ha : evalArgs n env ρ as = evalArgs n env VarEnv.empty as) :
    callDef (n + 1) env ρ x as = callDef (n + 1) env VarEnv.empty x as :=
  callDef_eq_of_resolved (by rw [hx]; rfl) ha

/-! ## What the lemma does *not* extend to: `matchExp` -/

namespace IterPatternCounterexample

/-- The pattern `(x)^(x<-y)`: a `List` iteration whose body is the domain
variable `x` itself and whose single domain ranges over `y`.

`freeExp` subtracts the domain variables from the body
(`spectec/src/il/free.ml:75`), so the only identifier free in this pattern is
`y` — `freeExp_pat` below. -/
def pat : Exp := .iterE (.varE "x") (.mk .list [.mk "x" (.varE "y")])

/-- The value the pattern is matched against, a one-element list. -/
def val : Value := .list [.num (.natN 3)]

/-- A scope in which the *domain* variable `x` happens to be bound already,
to a value the match will not accept. -/
def boundScope : VarEnv := VarEnv.empty.bindVal "x" (.num (.natN 5))

/-- The only identifier free in `pat` is `y`. -/
theorem freeExp_pat : freeExp pat = freeVarid "y" := by decide

/-- `boundScope` and the empty scope agree on everything free in `pat`. -/
theorem agree : VarEnv.AgreeOn (freeExp pat) boundScope VarEnv.empty := by
  refine ⟨fun z hz => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  rw [freeExp_pat] at hz
  have hzy : z = "y" := by simpa [freeVarid, Sets.empty] using hz
  subst hzy
  rfl

/-- In the scope that already binds `x`, the match fails: the body `x` is
matched against `3` and `boundScope` says `x` is `5`. -/
theorem match_boundScope : matchExp 8 Env.empty boundScope pat val = .error .undef := by
  simp [pat, val, boundScope, matchExp, matchIterE, matchIterList, matchRounds, matchExps,
    domVar, domSrc, VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.bind, Map.find?,
    Map.empty, Value.asList?, EvalFree.ok_bind, EvalFree.error_bind, iterCols, iterCol]

/-- In the empty scope the same match succeeds, binding `y` to the whole
list.  Note that `x` does *not* escape: `matchIterList` matches the domain
expressions in the *incoming* scope (`spectec/src/il/eval.ml:1021-1028`). -/
theorem match_empty : matchExp 8 Env.empty VarEnv.empty pat val =
    .ok (VarEnv.empty.bindVal "y" (.list [.num (.natN 3)])) := by
  simp [pat, val, matchExp, matchIterE, matchIterList, matchRounds, matchExps,
    domVar, domSrc, VarEnv.findVal?, VarEnv.findVals?, VarEnv.bindVal, VarEnv.empty,
    Map.bind, Map.find?, Map.empty, Value.asList?, EvalFree.ok_bind, iterCols, iterCol]

/-- **`matchExp` does not have the free-variable property.**  Two scopes that
agree on `freeExp pat` give different results.

The reason is a documented deviation in `Silmaril/SpecTec/Sem/Eval.lean`:
`spectec/src/il/eval.ml:1006` *removes* an iteration's domain variables from
the substitution before matching the body, and `matchRounds` does not — it
starts every round from the incoming scope.  An outer binding of a domain
variable therefore leaks into the body match.  The statement proved above for
`evalExp` is unaffected, because `evalIterE` *binds* every domain variable
before evaluating the body, which shadows whatever the outer scope held. -/
theorem matchExp_not_agreeOn :
    VarEnv.AgreeOn (freeExp pat) boundScope VarEnv.empty ∧
      matchExp 8 Env.empty boundScope pat val ≠ matchExp 8 Env.empty VarEnv.empty pat val := by
  refine ⟨agree, ?_⟩
  rw [match_boundScope, match_empty]
  simp

end IterPatternCounterexample

/-! ## Scope: what is proved here, and what is not

### Proved

1. **The free-variable lemma for `evalExp`** — `evalExp_agreeOn`: two scopes
   that agree on `Silmaril.SpecTec.IL.freeExp e`, in all four of a `VarEnv`'s
   namespaces, give `evalExp n env · e` the same answer, at every fuel level
   and in every script environment.  This is the statement
   `Silmaril/SpecTec/Sem/Eval.lean` lists as open;
   `evalExp_eq_of_find?_eq` restates it with `VarEnv.AgreeOn` unfolded, in
   that file's own words.
2. The same for every other member of the mutual block that an `evalExp` can
   reach with a scope of its own: `evalExps_agreeOn`, `evalExpFields_agreeOn`,
   `evalArg_agreeOn`, `evalArgs_agreeOn`, `evalDoms_agreeOn`,
   `evalIterE_agreeOn`, `pathGet_agreeOn`, `pathSet_agreeOn`,
   `callDef_agreeOn`, plus the two members whose invariant is stated modulo
   the variables a round binds, `AgreeAt.iterList` and `AgreeAt.rounds`.
3. **Weakening** — `evalExp_bindVal_of_notMem`, `evalExp_bindTyp_of_notMem`,
   `evalExp_bindDef_of_notMem`, `evalExp_bindGram_of_notMem` and the row form
   `evalExp_bindVals_of_notMem`: extending the scope with an identifier that
   is not free in the expression changes nothing.  The relational forms are
   `EvalExp.agreeOn`, `evalExp_iff_agreeOn` and `EvalExp.bindVal_of_notMem`.
4. **A definition's clauses are closed** — `callDef_eq`, which exhibits the
   caller's scope as occurring in exactly two places, and
   `callDef_eq_of_resolved`, which says that two calls agree as soon as they
   resolve to the same global name and evaluate their arguments to the same
   list.  `callDef_eq_empty` is the special case that moves a call into
   `VarEnv.empty`.

### Not proved, and why

* **The pattern side.**  Nothing is claimed for `matchExp`, `matchDefault`,
  `matchExps`, `matchExpFields`, `matchIterE`, `matchIterList`,
  `matchRounds`, `matchArg`, `matchArgs` or `patLen`, nor for the premise
  machinery `premHolds`, `premsHold`, `premIter` and `premRounds`.  For
  `matchExp` the statement is not merely unproved, it is **false**:
  `IterPatternCounterexample.matchExp_not_agreeOn` exhibits two scopes that
  agree on `freeExp` of an `IterE` pattern and against which the same value
  matches differently.  The cause is a deviation of
  `Silmaril/SpecTec/Sem/Eval.lean` from `spectec/src/il/eval.ml:1006`, which
  removes the domain variables from the substitution
  (`List.fold_left Subst.remove_varid s' (List.map fst xes)`) before matching
  the body; `matchRounds` starts each round from the incoming scope instead,
  so an outer binding of a domain variable leaks into the body match.  A
  correct statement for the pattern side would need a variant of `freeExp`
  that does *not* subtract `boundIterExp` at an `IterE` — equivalently, it
  would need `matchRounds` to transcribe `eval.ml:1006`.  Neither is done
  here; in particular this file does not change `Eval.lean`.
* **Tightness.**  `freeExp` is only an over-approximation of what `evalExp`
  reads, and no converse is claimed.  Two sources of slack are already known:
  the left-biased short circuit of `boolShort` means a `BinE` may never look
  at its right operand, and `Silmaril/SpecTec/IL/Free.lean`'s `freePrem`
  over-approximates a `LetPr`, because `spectec/src/backend-ast/print.ml:165`
  drops the quantifiers (that second one cannot be reached from here, since
  premises are on the pattern side).
* **The script environment.**  `Env` — the type, relation, function and
  grammar declarations — is held fixed throughout.  The corresponding
  statement, that `evalExp` reads only the declarations named in `freeExp e`
  and transitively in their bodies, is a different induction and is not here.
* **The other denotations.**  `Sem/Type.lean`, `Sem/Valid.lean` and
  `Sem/Grammar.lean` have their own environments; nothing here transfers to
  them.
-/

end Silmaril.SpecTec.Sem
