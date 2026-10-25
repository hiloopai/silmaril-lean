module

public import Silmaril.Logic.Metamath.Grammar.Basic

@[expose] public section

/-!
# Syntax trees

A syntax tree is a variable or a syntax rule applied to a list of subtrees,
one for each floating hypothesis of the rule. A tree has sort `s` in a
variable context when its variables have the sorts the context gives them and
every rule is applied to subtrees of its argument sorts. Tree substitution
replaces variables by trees.

Sorts are decidable in a functional context given as a partial map
(`check_iff`). Flattening a tree substitutes the flattenings of the subtrees
for the argument variables in the rule body. It commutes with substitution,
and a well-sorted tree and its flattening have the same variables. Flattening
a well-sorted tree is exactly the string a Metamath syntax proof produces
(`Silmaril.Logic.Metamath.Grammar.Correspondence`).
-/

namespace Silmaril.Logic.Metamath

universe u

variable {C V : Type u}

namespace Grammar

/-- A syntax tree over rule labels `L` with variables `V`. -/
inductive Tree (L V : Type u) where
  | var (v : V)
  | node (l : L) (args : List (Tree L V))
  deriving Repr

namespace Tree

variable {L : Type u}

section DecEq

variable [DecidableEq L] [DecidableEq V]

mutual

/-- Decidable equality of trees. -/
def decEq : (a b : Tree L V) → Decidable (a = b)
  | .var v, .var w =>
    if h : v = w then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .var _, .node _ _ => isFalse nofun
  | .node _ _, .var _ => isFalse nofun
  | .node l as, .node k bs =>
    if hl : l = k then
      match decEqList as bs with
      | isTrue h => isTrue (hl ▸ h ▸ rfl)
      | isFalse h => isFalse fun e => h (by cases e; rfl)
    else isFalse fun e => hl (by cases e; rfl)

/-- Decidable equality of lists of trees. -/
def decEqList : (as bs : List (Tree L V)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
  | a :: as, b :: bs =>
    match decEq a b, decEqList as bs with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse fun e => h (by cases e; rfl)
    | _, isFalse h' => isFalse fun e => h' (by cases e; rfl)

end

instance : DecidableEq (Tree L V) := decEq

end DecEq

/-- Induction on trees with a hypothesis for every child. -/
@[elab_as_elim]
theorem induction {motive : Tree L V → Prop} (var : ∀ v, motive (.var v))
    (node : ∀ l args, (∀ t ∈ args, motive t) → motive (.node l args)) : ∀ t, motive t
  | .var v => var v
  | .node l args => node l args fun t _ => induction var node t

mutual

/-- The variables of a tree, with multiplicity and in order. -/
def vars : Tree L V → List V
  | .var v => [v]
  | .node _ args => varsList args
termination_by structural t => t

/-- The variables of a list of trees. -/
def varsList : List (Tree L V) → List V
  | [] => []
  | t :: ts => vars t ++ varsList ts
termination_by structural ts => ts

end

mutual

/-- Simultaneous substitution of trees for variables. -/
def subst (τ : V → Tree L V) : Tree L V → Tree L V
  | .var v => τ v
  | .node l args => .node l (substList τ args)
termination_by structural t => t

/-- Substitution into a list of trees. -/
def substList (τ : V → Tree L V) : List (Tree L V) → List (Tree L V)
  | [] => []
  | t :: ts => subst τ t :: substList τ ts
termination_by structural ts => ts

end

theorem varsList_eq (ts : List (Tree L V)) : varsList ts = ts.flatMap vars := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [varsList, ih]

theorem substList_eq (τ : V → Tree L V) (ts : List (Tree L V)) :
    substList τ ts = ts.map (subst τ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [substList, ih]

@[simp] theorem vars_var (v : V) : (var v : Tree L V).vars = [v] := rfl

@[simp] theorem vars_node (l : L) (args : List (Tree L V)) :
    (node l args).vars = args.flatMap vars := varsList_eq args

@[simp] theorem subst_var' (τ : V → Tree L V) (v : V) : (var v).subst τ = τ v := rfl

@[simp] theorem subst_node (τ : V → Tree L V) (l : L) (args : List (Tree L V)) :
    (node l args).subst τ = node l (args.map (subst τ)) := by
  rw [subst, substList_eq]

/-- The variables of a substituted tree. -/
theorem mem_vars_subst {τ : V → Tree L V} {t : Tree L V} {w : V} :
    w ∈ (t.subst τ).vars ↔ ∃ v ∈ t.vars, w ∈ (τ v).vars := by
  induction t using Tree.induction with
  | var v => simp
  | node l args ih =>
    simp only [subst_node, vars_node, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, hw⟩
      obtain ⟨v, hv, hw⟩ := (ih a ha).1 hw
      exact ⟨v, ⟨a, ha, hv⟩, hw⟩
    · rintro ⟨v, ⟨a, ha, hv⟩, hw⟩
      exact ⟨_, ⟨a, ha, rfl⟩, (ih a ha).2 ⟨v, hv, hw⟩⟩

/-- Substitution only depends on the variables that occur. -/
theorem subst_congr {τ τ' : V → Tree L V} {t : Tree L V} (h : ∀ v ∈ t.vars, τ v = τ' v) :
    t.subst τ = t.subst τ' := by
  induction t using Tree.induction with
  | var v => simpa using h v (by simp)
  | node l args ih =>
    simp only [subst_node, node.injEq, true_and]
    exact List.map_congr_left fun a ha =>
      ih a ha fun v hv => h v (by simpa using ⟨a, ha, hv⟩)

/-- The identity substitution. -/
@[simp] theorem subst_var (t : Tree L V) : t.subst var = t := by
  induction t using Tree.induction with
  | var v => simp
  | node l args ih =>
    simp only [subst_node, node.injEq, true_and]
    exact (List.map_congr_left ih).trans (List.map_id _)

/-- Substitution composes. -/
theorem subst_subst (τ τ' : V → Tree L V) (t : Tree L V) :
    (t.subst τ).subst τ' = t.subst fun v => (τ v).subst τ' := by
  induction t using Tree.induction with
  | var v => simp
  | node l args ih =>
    simp only [subst_node, List.map_map, node.injEq, true_and]
    exact List.map_congr_left ih

end Tree

variable {L : Type u} (G : Grammar L C V)

theorem exists_mem_zip_of_mem_left {α β : Type*} {as : List α} {bs : List β}
    (h : as.length = bs.length) {a : α} (ha : a ∈ as) : ∃ b, (a, b) ∈ as.zip bs := by
  induction as generalizing bs with
  | nil => simp at ha
  | cons x as ih =>
    cases bs with
    | nil => simp at h
    | cons y bs =>
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨y, by simp⟩
      · obtain ⟨b, hb⟩ := ih (by simpa using h) ha
        exact ⟨b, by simp [hb]⟩

theorem exists_mem_zip_of_mem_right {α β : Type*} {as : List α} {bs : List β}
    (h : as.length = bs.length) {b : β} (hb : b ∈ bs) : ∃ a, (a, b) ∈ as.zip bs := by
  induction bs generalizing as with
  | nil => simp at hb
  | cons y bs ih =>
    cases as with
    | nil => simp at h
    | cons x as =>
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨x, by simp⟩
      · obtain ⟨a, ha⟩ := ih (by simpa using h) hb
        exact ⟨a, by simp [ha]⟩

/-- Choose a related element for each member of a list. -/
theorem exists_forall₂_of_forall {α β : Type*} {R : α → β → Prop} {bs : List β}
    (h : ∀ b ∈ bs, ∃ a, R a b) : ∃ as, List.Forall₂ R as bs := by
  induction bs with
  | nil => exact ⟨[], .nil⟩
  | cons b bs ih =>
    obtain ⟨a, ha⟩ := h b (by simp)
    obtain ⟨as, has⟩ := ih fun b hb => h b (by simp [hb])
    exact ⟨a :: as, .cons ha has⟩

/-- `t` has sort `s` when the variable `v` may be used at the sorts `ctx v`. -/
inductive HasSort (ctx : V → C → Prop) : Tree L V → C → Prop
  | var {v : V} {s : C} : ctx v s → HasSort ctx (.var v) s
  | node {l : L} {args : List (Tree L V)} : args.length = (G.rule l).arity →
      (∀ p ∈ args.zip (G.rule l).args, HasSort ctx p.1 p.2.1) →
      HasSort ctx (.node l args) (G.rule l).tc

/-- A variable context assigns each variable at most one sort. -/
def Functional (ctx : V → C → Prop) : Prop := ∀ v s s', ctx v s → ctx v s' → s = s'

variable {G}

namespace HasSort

variable {ctx ctx' : V → C → Prop}

theorem mono (hle : ∀ v s, ctx v s → ctx' v s) {t : Tree L V} {s : C}
    (h : G.HasSort ctx t s) : G.HasSort ctx' t s := by
  induction h with
  | var hv => exact .var (hle _ _ hv)
  | node hlen _ ih => exact .node hlen ih

/-- Substituting well-sorted trees preserves sorts. -/
theorem subst {τ : V → Tree L V} (hτ : ∀ v s, ctx v s → G.HasSort ctx' (τ v) s)
    {t : Tree L V} {s : C} (h : G.HasSort ctx t s) : G.HasSort ctx' (t.subst τ) s := by
  induction h with
  | var hv => simpa using hτ _ _ hv
  | node hlen _ ih =>
    rw [Tree.subst_node]
    refine .node (by simpa using hlen) fun p hp => ?_
    rw [List.zip_map_left, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ih q hq

/-- The variables of a tree of a syntax sort have syntax sorts. -/
theorem sort_of_mem_vars {t : Tree L V} {s : C} (h : G.HasSort ctx t s) (hs : s ∈ G.sorts)
    {v : V} (hv : v ∈ t.vars) : ∃ s' ∈ G.sorts, ctx v s' := by
  induction h with
  | var hctx => simp at hv; subst hv; exact ⟨_, hs, hctx⟩
  | @node l args hlen _ ih =>
    simp only [Tree.vars_node, List.mem_flatMap] at hv
    obtain ⟨a, ha, hv⟩ := hv
    obtain ⟨p, hp⟩ := exists_mem_zip_of_mem_left hlen ha
    exact ih (a, p) hp (G.rule_args l p (List.of_mem_zip hp).2) hv

theorem node_inv {l : L} {args : List (Tree L V)} {s : C}
    (h : G.HasSort ctx (.node l args) s) :
    (G.rule l).tc = s ∧ args.length = (G.rule l).arity ∧
      ∀ p ∈ args.zip (G.rule l).args, G.HasSort ctx p.1 p.2.1 := by
  cases h with
  | node hlen hargs => exact ⟨rfl, hlen, hargs⟩

@[simp] theorem var_iff {v : V} {s : C} : G.HasSort ctx (.var v) s ↔ ctx v s :=
  ⟨fun h => by cases h; assumption, .var⟩

end HasSort

section Check

variable [DecidableEq C] (G)

mutual

/-- Check that a tree has sort `s` when each variable `v` has the sort `f v`. -/
def check (f : V → Option C) : Tree L V → C → Bool
  | .var v, s => f v == some s
  | .node l args, s => (G.rule l).tc == s && checkList f args (G.rule l).args
termination_by structural t => t

/-- Check a list of trees against a list of argument sorts. -/
def checkList (f : V → Option C) : List (Tree L V) → List (C × V) → Bool
  | [], [] => true
  | t :: ts, p :: ps => check f t p.1 && checkList f ts ps
  | [], _ :: _ => false
  | _ :: _, [] => false
termination_by structural ts => ts

end

variable {G}

theorem checkList_iff {f : V → Option C} {args : List (Tree L V)}
    (ih : ∀ t ∈ args, ∀ s, G.check f t s = true ↔ G.HasSort (fun v s => f v = some s) t s)
    (ps : List (C × V)) :
    G.checkList f args ps = true ↔ args.length = ps.length ∧
      ∀ p ∈ args.zip ps, G.HasSort (fun v s => f v = some s) p.1 p.2.1 := by
  induction args generalizing ps with
  | nil => cases ps <;> simp [checkList]
  | cons t ts ihl =>
    cases ps with
    | nil => simp [checkList]
    | cons p ps =>
      simp only [checkList, Bool.and_eq_true, ih t (by simp), ihl (fun t ht => ih t (by simp [ht])),
        List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons, List.mem_cons,
        forall_eq_or_imp]
      tauto

/-- The sort checker is correct. -/
theorem check_iff {f : V → Option C} (t : Tree L V) (s : C) :
    G.check f t s = true ↔ G.HasSort (fun v s => f v = some s) t s := by
  induction t using Tree.induction generalizing s with
  | var v => simp [check]
  | node l args ih =>
    rw [check, Bool.and_eq_true, beq_iff_eq, checkList_iff (fun t ht => ih t ht)]
    constructor
    · rintro ⟨rfl, hlen, h⟩
      exact .node hlen h
    · intro h
      obtain ⟨hs, hlen, h⟩ := h.node_inv
      exact ⟨hs, hlen, h⟩

instance (f : V → Option C) (t : Tree L V) (s : C) :
    Decidable (G.HasSort (fun v s => f v = some s) t s) :=
  decidable_of_iff _ (check_iff t s)

end Check

variable [DecidableEq V] (G)

/-- The substitution a rule application performs: each argument variable
receives the string of its argument, and missing arguments are empty. -/
def argSubst (l : L) (ws : List (Str C V)) : Subst C V :=
  fun v => (lookupArg (G.rule l).args ws v).getD []

mutual

/-- Flattening a tree to the math string it denotes. -/
def flatten : Tree L V → Str C V
  | .var v => [.var v]
  | .node l args => Str.subst (G.argSubst l (flattenList args)) (G.rule l).body
termination_by structural t => t

/-- Flattening each tree of a list. -/
def flattenList : List (Tree L V) → List (Str C V)
  | [] => []
  | t :: ts => flatten t :: flattenList ts
termination_by structural ts => ts

end

theorem flattenList_eq (ts : List (Tree L V)) : G.flattenList ts = ts.map G.flatten := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [flattenList, ih]

@[simp] theorem flatten_var (v : V) : G.flatten (.var v) = [.var v] := rfl

theorem flatten_node (l : L) (args : List (Tree L V)) :
    G.flatten (.node l args) = Str.subst (G.argSubst l (args.map G.flatten)) (G.rule l).body := by
  rw [flatten, flattenList_eq]

/-- A grammar is unambiguous when, in every functional variable context,
well-sorted trees of the same sort with the same flattening are equal. -/
def Unambiguous : Prop :=
  ∀ ctx : V → C → Prop, Functional ctx → ∀ (s : C) (t t' : Tree L V),
    G.HasSort ctx t s → G.HasSort ctx t' s → G.flatten t = G.flatten t' → t = t'

variable {G}

/-- Flattening commutes with substitution. -/
theorem flatten_subst (τ : V → Tree L V) (t : Tree L V) :
    G.flatten (t.subst τ) = Str.subst (fun v => G.flatten (τ v)) (G.flatten t) := by
  induction t using Tree.induction with
  | var v => simp
  | node l args ih =>
    rw [Tree.subst_node, flatten_node, flatten_node, Str.subst_subst]
    congr 1
    funext v
    have : (args.map (Tree.subst τ)).map G.flatten =
        (args.map G.flatten).map (Str.subst fun v => G.flatten (τ v)) := by
      simp only [List.map_map]
      exact List.map_congr_left ih
    simp only [argSubst, this, lookupArg_map]
    cases lookupArg (G.rule l).args args v <;> simp

/-- Every variable of a flattening occurs in the tree. -/
theorem mem_vars_of_mem_vars_flatten {t : Tree L V} {v : V}
    (h : v ∈ Str.vars (G.flatten t)) : v ∈ t.vars := by
  induction t using Tree.induction with
  | var w => simpa [Str.vars] using h
  | node l args ih =>
    rw [flatten_node, Str.mem_vars_subst] at h
    obtain ⟨w, -, hw⟩ := h
    simp only [argSubst] at hw
    cases hl : lookupArg (G.rule l).args (args.map G.flatten) w with
    | none => simp [hl] at hw
    | some a =>
      rw [hl] at hw
      obtain ⟨p, hp, -⟩ := lookupArg_eq_some hl
      rw [List.zip_map_left, List.mem_map] at hp
      obtain ⟨⟨c, q⟩, hc, he⟩ := hp
      simp only [Prod.map, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simpa using ⟨c, (List.of_mem_zip hc).1, ih c (List.of_mem_zip hc).1 hw⟩

/-- Each rule argument is found by its variable. -/
theorem argSubst_flatten {l : L} {args : List (Tree L V)} {c : Tree L V} {p : C × V}
    (hp : (c, p) ∈ args.zip (G.rule l).args) :
    G.argSubst l (args.map G.flatten) p.2 = G.flatten c := by
  have : (G.flatten c, p) ∈ (args.map G.flatten).zip (G.rule l).args := by
    rw [List.zip_map_left, List.mem_map]
    exact ⟨(c, p), hp, rfl⟩
  simp [argSubst, lookupArg_of_mem_zip (G.rule l).args_nodup this]

/-- A well-sorted tree and its flattening have the same variables. -/
theorem HasSort.mem_vars_flatten {ctx : V → C → Prop} {t : Tree L V} {s : C}
    (h : G.HasSort ctx t s) {v : V} : v ∈ Str.vars (G.flatten t) ↔ v ∈ t.vars := by
  refine ⟨mem_vars_of_mem_vars_flatten, fun hv => ?_⟩
  induction h with
  | var => simpa [Str.vars] using hv
  | @node l args hlen _ ih =>
    simp only [Tree.vars_node, List.mem_flatMap] at hv
    obtain ⟨a, ha, hv⟩ := hv
    obtain ⟨p, hp⟩ := exists_mem_zip_of_mem_left hlen ha
    rw [flatten_node, Str.mem_vars_subst]
    refine ⟨p.2, ?_, ?_⟩
    · exact (G.rule l).body_perm.symm.subset
        (List.mem_map.2 ⟨p, (List.of_mem_zip hp).2, rfl⟩)
    · rw [argSubst_flatten hp]
      exact ih (a, p) hp hv

/-- The flattening of a node whose arguments flatten to the values of `σ` at
the argument variables. -/
theorem flatten_node_of_forall₂ {l : L} {args : List (Tree L V)} {σ : Subst C V}
    (h : List.Forall₂ (fun c p => G.flatten c = σ p.2) args (G.rule l).args) :
    G.flatten (.node l args) = Str.subst σ (G.rule l).body := by
  rw [flatten_node]
  apply Str.subst_congr
  intro v hv
  have hv' : v ∈ (G.rule l).args.map Prod.snd := (G.rule l).body_perm.subset hv
  obtain ⟨hlen, hzip⟩ := List.forall₂_iff_zip.1 h
  obtain ⟨p, a, hm, rfl, hl⟩ := lookupArg_isSome (as := args.map G.flatten)
    (by simpa using hlen) hv'
  rw [List.zip_map_left, List.mem_map] at hm
  obtain ⟨⟨c, q⟩, hc, he⟩ := hm
  simp only [Prod.map, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [argSubst, hl, Option.getD_some]
  exact hzip hc

end Grammar

end Silmaril.Logic.Metamath
