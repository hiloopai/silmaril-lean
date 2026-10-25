module

public import Silmaril.Logic.Metamath.Grammar.Tree
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# A sufficient criterion for unambiguity

A grammar is unambiguous when flattening is injective on well-sorted trees of
each sort in every functional variable context. We give a decidable
sufficient criterion in the style of LL(1) with left factoring, certified by a
first-symbol assignment.

A symbol class is `inl c` for the constant `c` or `inr s` for a variable of
sort `s`. A certificate `F` assigns to each sort a list of symbol classes that
contains every class with which a string of that sort can begin. The
criterion (`LLCert`) asks that

* every rule body is nonempty, and `F` is closed under the first symbol of each
  rule;
* a variable of sort `s` cannot begin a rule of sort `s`;
* any two distinct rules of the same sort fork: their grammar symbols agree up
  to a position where both have a symbol and their first-symbol classes are
  disjoint (`Forks`).

Under the criterion a well-sorted string has a unique parse even as a prefix
(`LLCert.prefix_unique`), so the grammar is unambiguous (`LLCert.unambiguous`).
The primitive grammars of set.mm and iset.mm, hol.mm and peano.mm satisfy it;
see `Silmaril.Logic.Metamath.Grammar.Examples`.
-/

namespace Silmaril.Logic.Metamath

universe u

variable {C V : Type u}

namespace Grammar

/-- The symbol classes that can begin a grammar symbol under the first-symbol
assignment `F`. -/
def firstOf (F : C → List (C ⊕ C)) : Sym C C → List (C ⊕ C)
  | .const c => [.inl c]
  | .var s => F s

/-- Two grammar symbol sequences fork: they agree up to a position where the
first-symbol classes of both symbols are disjoint. -/
def Forks [DecidableEq C] (F : C → List (C ⊕ C)) : List (Sym C C) → List (Sym C C) → Prop
  | a :: as, b :: bs => (a = b ∧ Forks F as bs) ∨ ∀ x ∈ firstOf F a, x ∉ firstOf F b
  | _, _ => False

instance decidableForks [DecidableEq C] (F : C → List (C ⊕ C)) :
    ∀ as bs, Decidable (Forks F as bs)
  | a :: as, b :: bs =>
    have := decidableForks F as bs
    inferInstanceAs (Decidable ((a = b ∧ Forks F as bs) ∨ _))
  | [], _ => inferInstanceAs (Decidable False)
  | _ :: _, [] => inferInstanceAs (Decidable False)

variable {L : Type u} [DecidableEq V]

/-- An LL(1)-style certificate of unambiguity with the first-symbol
assignment `F`. -/
structure LLCert [DecidableEq C] (G : Grammar L C V) (F : C → List (C ⊕ C)) : Prop where
  var_mem : ∀ s, .inr s ∈ F s
  items_ne_nil : ∀ l, (G.rule l).items ≠ []
  first_sub : ∀ l a, (G.rule l).items.head? = some a → ∀ x ∈ firstOf F a, x ∈ F (G.rule l).tc
  var_first : ∀ l a, (G.rule l).items.head? = some a → .inr (G.rule l).tc ∉ firstOf F a
  fork : ∀ l₁ l₂, l₁ ≠ l₂ → (G.rule l₁).tc = (G.rule l₂).tc →
    Forks F (G.rule l₁).items (G.rule l₂).items

theorem llCert_iff [DecidableEq C] (G : Grammar L C V) (F : C → List (C ⊕ C)) :
    LLCert G F ↔ (∀ s, .inr s ∈ F s) ∧ (∀ l, (G.rule l).items ≠ []) ∧
      (∀ l, ∀ a ∈ (G.rule l).items.head?.toList,
        (∀ x ∈ firstOf F a, x ∈ F (G.rule l).tc) ∧ .inr (G.rule l).tc ∉ firstOf F a) ∧
      ∀ l₁ l₂, l₁ ≠ l₂ → (G.rule l₁).tc = (G.rule l₂).tc →
        Forks F (G.rule l₁).items (G.rule l₂).items := by
  constructor
  · intro h
    refine ⟨h.var_mem, h.items_ne_nil, fun l a ha => ?_, h.fork⟩
    have ha' : (G.rule l).items.head? = some a := by simpa using ha
    exact ⟨h.first_sub l a ha', h.var_first l a ha'⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₂, fun l a ha => (h₃ l a (by simp [ha])).1,
      fun l a ha => (h₃ l a (by simp [ha])).2, h₄⟩

/-- The certificate is decidable for finite typecodes and labels. -/
instance [DecidableEq C] [Fintype C] [Fintype L] [DecidableEq L] (G : Grammar L C V)
    (F : C → List (C ⊕ C)) : Decidable (LLCert G F) :=
  decidable_of_iff _ (llCert_iff G F).symm

/-- The symbol `x` belongs to one of the classes `cls` in the context `ctx`. -/
def FirstIn (ctx : V → C → Prop) (cls : List (C ⊕ C)) : Sym C V → Prop
  | .const c => .inl c ∈ cls
  | .var v => ∃ s, ctx v s ∧ .inr s ∈ cls

omit [DecidableEq V] in
theorem FirstIn.mono {ctx : V → C → Prop} {cls cls' : List (C ⊕ C)} (h : ∀ x ∈ cls, x ∈ cls')
    {x : Sym C V} (hx : FirstIn ctx cls x) : FirstIn ctx cls' x := by
  cases x with
  | const c => exact h _ hx
  | var v => obtain ⟨s, hs, hm⟩ := hx; exact ⟨s, hs, h _ hm⟩

omit [DecidableEq V] in
/-- A symbol cannot belong to disjoint classes in a functional context. -/
theorem FirstIn.disjoint {ctx : V → C → Prop} (hfun : Functional ctx) {cls cls' : List (C ⊕ C)}
    (h : ∀ x ∈ cls, x ∉ cls') {x : Sym C V} (hx : FirstIn ctx cls x)
    (hx' : FirstIn ctx cls' x) : False := by
  cases x with
  | const c => exact h _ hx hx'
  | var v =>
    obtain ⟨s, hs, hm⟩ := hx
    obtain ⟨s', hs', hm'⟩ := hx'
    rw [hfun v s s' hs hs'] at hm
    exact h _ hm hm'

variable {G : Grammar L C V} {ctx : V → C → Prop}

/-- The argument of a well-sorted node at an argument variable of its body. -/
theorem HasSort.node_child {l : L} {args : List (Tree L V)} {s : C}
    (h : G.HasSort ctx (.node l args) s) {v : V} (hv : Sym.var v ∈ (G.rule l).body) :
    ∃ c q, (c, q) ∈ args.zip (G.rule l).args ∧ q.2 = v ∧
      lookupArg (G.rule l).args args v = some c ∧ (G.rule l).argSort v = some q.1 ∧
      G.HasSort ctx c q.1 ∧ G.argSubst l (args.map G.flatten) v = G.flatten c := by
  obtain ⟨-, hlen, hargs⟩ := h.node_inv
  obtain ⟨q, c, hm, rfl, hl⟩ :=
    lookupArg_isSome hlen ((G.rule l).mem_args_of_mem_body hv)
  exact ⟨c, q, hm, rfl, hl, SyntaxRule.argSort_of_mem (List.of_mem_zip hm).2, hargs _ hm,
    argSubst_flatten hm⟩

/-- Every body symbol of a well-sorted node has a grammar symbol, and its
substituted string begins with a symbol of that grammar symbol's classes. -/
theorem HasSort.item_chunk {F : C → List (C ⊕ C)} {l : L} {args : List (Tree L V)} {s : C}
    (h : G.HasSort ctx (.node l args) s)
    (first : ∀ p ∈ args.zip (G.rule l).args,
      ∃ x w, G.flatten p.1 = x :: w ∧ FirstIn ctx (F p.2.1) x)
    {y : Sym C V} (hy : y ∈ (G.rule l).body) :
    ∃ i, (G.rule l).itemOf y = some i ∧ ∃ x w,
      y.subst (G.argSubst l (args.map G.flatten)) = x :: w ∧ FirstIn ctx (firstOf F i) x := by
  cases y with
  | const c => exact ⟨.const c, rfl, .const c, [], rfl, by simp [FirstIn, firstOf]⟩
  | var v =>
    obtain ⟨c, q, hm, -, -, hsort, -, hsub⟩ := h.node_child hy
    obtain ⟨x, w, hx, hfx⟩ := first _ hm
    refine ⟨.var q.1, by simp [SyntaxRule.itemOf, hsort], x, w, ?_, hfx⟩
    rw [Sym.subst_var, hsub, hx]

theorem SyntaxRule.head_items {r : SyntaxRule C V} {y : Sym C V} {ys : Str C V}
    (hb : r.body = y :: ys) {i : Sym C C} (hi : r.itemOf y = some i) :
    r.items.head? = some i := by
  simp [SyntaxRule.items, hb, hi]

/-- The first symbol of a well-sorted node lies in the classes of the first
grammar symbol of its rule. -/
theorem HasSort.node_first {F : C → List (C ⊕ C)} {l : L} {args : List (Tree L V)} {s : C}
    (h : G.HasSort ctx (.node l args) s) (hne : (G.rule l).items ≠ [])
    (first : ∀ p ∈ args.zip (G.rule l).args,
      ∃ x w, G.flatten p.1 = x :: w ∧ FirstIn ctx (F p.2.1) x) :
    ∃ i, (G.rule l).items.head? = some i ∧ ∃ x w,
      G.flatten (.node l args) = x :: w ∧ FirstIn ctx (firstOf F i) x := by
  obtain ⟨y, ys, hb⟩ : ∃ y ys, (G.rule l).body = y :: ys := by
    cases hb : (G.rule l).body with
    | nil => exact absurd (by simp [SyntaxRule.items, hb]) hne
    | cons y ys => exact ⟨y, ys, rfl⟩
  obtain ⟨i, hi, x, w, hx, hfx⟩ := h.item_chunk first (y := y) (by simp [hb])
  refine ⟨i, SyntaxRule.head_items hb hi, x, w ++ Str.subst (G.argSubst l (args.map G.flatten)) ys,
    ?_, hfx⟩
  rw [flatten_node, hb, Str.subst_cons, hx, List.cons_append]

/-- A well-sorted string begins with a symbol of the classes of its sort. -/
theorem LLCert.first [DecidableEq C] {F : C → List (C ⊕ C)} (hF : LLCert G F)
    {t : Tree L V} {s : C} (h : G.HasSort ctx t s) :
    ∃ x w, G.flatten t = x :: w ∧ FirstIn ctx (F s) x := by
  induction h with
  | @var v s hv => exact ⟨.var v, [], by simp, s, hv, hF.var_mem s⟩
  | @node l args hlen hargs ih =>
    obtain ⟨i, hi, x, w, hx, hfx⟩ :=
      HasSort.node_first (.node hlen hargs) (hF.items_ne_nil l) ih
    exact ⟨x, w, hx, hfx.mono (hF.first_sub l i hi)⟩

theorem forks_nil_right [DecidableEq C] (F : C → List (C ⊕ C)) (as : List (Sym C C)) :
    ¬ Forks F as [] := by
  cases as <;> simp [Forks]

/-- The induction hypothesis of `LLCert.prefix_unique` on the arguments of a node. -/
def PrefixIH (G : Grammar L C V) (ctx : V → C → Prop) (args : List (Tree L V)) : Prop :=
  ∀ c ∈ args, ∀ {t' : Tree L V} {s : C} {w w' : Str C V}, G.HasSort ctx c s →
    G.HasSort ctx t' s → G.flatten c ++ w = G.flatten t' ++ w' → c = t' ∧ w = w'

theorem LLCert.item_isSome [DecidableEq C] {F : C → List (C ⊕ C)} (hF : LLCert G F) {l : L}
    {args : List (Tree L V)} {s : C} (h : G.HasSort ctx (.node l args) s)
    {y : Sym C V} (hy : y ∈ (G.rule l).body) : ∃ i, (G.rule l).itemOf y = some i := by
  obtain ⟨i, hi, -⟩ := h.item_chunk (F := F) (fun p hp => (hF.first (h.node_inv.2.2 p hp)))
    hy
  exact ⟨i, hi⟩

section Walk

variable {l₁ l₂ : L} {args₁ args₂ : List (Tree L V)} {s : C}

/-- Body symbols with the same grammar symbol consume the same prefix, by the
induction hypothesis on the arguments of the first node. -/
theorem chunk_eq (h₁ : G.HasSort ctx (.node l₁ args₁) s) (h₂ : G.HasSort ctx (.node l₂ args₂) s)
    (ih : PrefixIH G ctx args₁)
    {y₁ y₂ : Sym C V} (hy₁ : y₁ ∈ (G.rule l₁).body) (hy₂ : y₂ ∈ (G.rule l₂).body)
    (hi : (G.rule l₁).itemOf y₁ = (G.rule l₂).itemOf y₂) {r₁ r₂ : Str C V}
    (he : y₁.subst (G.argSubst l₁ (args₁.map G.flatten)) ++ r₁ =
      y₂.subst (G.argSubst l₂ (args₂.map G.flatten)) ++ r₂) :
    r₁ = r₂ ∧ ∀ v₁ v₂, y₁ = .var v₁ → y₂ = .var v₂ →
      lookupArg (G.rule l₁).args args₁ v₁ = lookupArg (G.rule l₂).args args₂ v₂ := by
  cases y₁ with
  | const c₁ =>
    cases y₂ with
    | const c₂ =>
      simp only [SyntaxRule.itemOf, Option.some.injEq, Sym.const.injEq] at hi
      subst hi
      simp only [Sym.subst_const, List.singleton_append, List.cons.injEq, true_and] at he
      exact ⟨he, by simp⟩
    | var v₂ =>
      obtain ⟨c, q, -, -, -, hsort, -⟩ := h₂.node_child hy₂
      simp [SyntaxRule.itemOf, hsort] at hi
  | var v₁ =>
    cases y₂ with
    | const c₂ =>
      obtain ⟨c, q, -, -, -, hsort, -⟩ := h₁.node_child hy₁
      simp [SyntaxRule.itemOf, hsort] at hi
    | var v₂ =>
      obtain ⟨c₁, q₁, hm₁, -, hl₁, hsort₁, hc₁, hsub₁⟩ := h₁.node_child hy₁
      obtain ⟨c₂, q₂, -, -, hl₂, hsort₂, hc₂, hsub₂⟩ := h₂.node_child hy₂
      simp only [SyntaxRule.itemOf, hsort₁, hsort₂, Option.map_some, Option.some.injEq,
        Sym.var.injEq] at hi
      rw [Sym.subst_var, Sym.subst_var, hsub₁, hsub₂] at he
      rw [hi] at hc₁
      obtain ⟨rfl, hr⟩ := ih c₁ (List.of_mem_zip hm₁).1 hc₁ hc₂ he
      refine ⟨hr, ?_⟩
      rintro _ _ ⟨⟩ ⟨⟩
      rw [hl₁, hl₂]

variable [DecidableEq C] {F : C → List (C ⊕ C)}

/-- Body symbols whose grammar symbols have disjoint first classes cannot begin
the same string. -/
theorem LLCert.chunk_ne (hF : LLCert G F) (hfun : Functional ctx)
    (h₁ : G.HasSort ctx (.node l₁ args₁) s) (h₂ : G.HasSort ctx (.node l₂ args₂) s)
    {y₁ y₂ : Sym C V} (hy₁ : y₁ ∈ (G.rule l₁).body)
    (hy₂ : y₂ ∈ (G.rule l₂).body) {i₁ i₂ : Sym C C} (hi₁ : (G.rule l₁).itemOf y₁ = some i₁)
    (hi₂ : (G.rule l₂).itemOf y₂ = some i₂) (hd : ∀ x ∈ firstOf F i₁, x ∉ firstOf F i₂)
    {r₁ r₂ : Str C V}
    (he : y₁.subst (G.argSubst l₁ (args₁.map G.flatten)) ++ r₁ =
      y₂.subst (G.argSubst l₂ (args₂.map G.flatten)) ++ r₂) : False := by
  obtain ⟨j₁, hj₁, x₁, w₁, hx₁, hf₁⟩ :=
    h₁.item_chunk (F := F) (fun p hp => hF.first (h₁.node_inv.2.2 p hp)) hy₁
  obtain ⟨j₂, hj₂, x₂, w₂, hx₂, hf₂⟩ :=
    h₂.item_chunk (F := F) (fun p hp => hF.first (h₂.node_inv.2.2 p hp)) hy₂
  rw [hi₁, Option.some.injEq] at hj₁
  rw [hi₂, Option.some.injEq] at hj₂
  subst hj₁ hj₂
  rw [hx₁, hx₂, List.cons_append, List.cons_append, List.cons.injEq] at he
  rw [he.1] at hf₁
  exact FirstIn.disjoint hfun hd hf₁ hf₂

/-- Two bodies whose grammar symbols fork cannot begin the same string. -/
theorem LLCert.walk_forks (hF : LLCert G F) (hfun : Functional ctx)
    (h₁ : G.HasSort ctx (.node l₁ args₁) s) (h₂ : G.HasSort ctx (.node l₂ args₂) s)
    (ih : PrefixIH G ctx args₁) :
    ∀ (b₁ b₂ : Str C V), (∀ y ∈ b₁, y ∈ (G.rule l₁).body) → (∀ y ∈ b₂, y ∈ (G.rule l₂).body) →
      Forks F (b₁.filterMap (G.rule l₁).itemOf) (b₂.filterMap (G.rule l₂).itemOf) →
      ∀ {w w' : Str C V}, Str.subst (G.argSubst l₁ (args₁.map G.flatten)) b₁ ++ w =
        Str.subst (G.argSubst l₂ (args₂.map G.flatten)) b₂ ++ w' → False := by
  intro b₁
  induction b₁ with
  | nil => intro b₂ _ _ hf; cases b₂ <;> simp [Forks] at hf
  | cons y₁ b₁ ihb =>
    intro b₂ hs₁ hs₂ hf w w' he
    cases b₂ with
    | nil => exact forks_nil_right F _ hf
    | cons y₂ b₂ =>
      obtain ⟨i₁, hi₁⟩ := hF.item_isSome h₁ (hs₁ y₁ (by simp))
      obtain ⟨i₂, hi₂⟩ := hF.item_isSome h₂ (hs₂ y₂ (by simp))
      simp only [List.filterMap_cons, hi₁, hi₂, Forks] at hf
      simp only [Str.subst_cons, List.append_assoc] at he
      rcases hf with ⟨rfl, hf⟩ | hd
      · obtain ⟨hr, -⟩ := chunk_eq h₁ h₂ ih (hs₁ y₁ (by simp)) (hs₂ y₂ (by simp))
          (hi₁.trans hi₂.symm) he
        exact ihb b₂ (fun y hy => hs₁ y (by simp [hy])) (fun y hy => hs₂ y (by simp [hy])) hf hr
      · exact hF.chunk_ne hfun h₁ h₂ (hs₁ y₁ (by simp)) (hs₂ y₂ (by simp)) hi₁ hi₂ hd he

end Walk

/-- Two applications of the same rule that begin the same string have the same
arguments at every body variable. -/
theorem walk_same {l : L} {args₁ args₂ : List (Tree L V)} {s : C}
    (h₁ : G.HasSort ctx (.node l args₁) s) (h₂ : G.HasSort ctx (.node l args₂) s)
    (ih : PrefixIH G ctx args₁) :
    ∀ (b : Str C V), (∀ y ∈ b, y ∈ (G.rule l).body) →
      ∀ {w w' : Str C V}, Str.subst (G.argSubst l (args₁.map G.flatten)) b ++ w =
        Str.subst (G.argSubst l (args₂.map G.flatten)) b ++ w' →
      w = w' ∧ ∀ v, Sym.var v ∈ b →
        lookupArg (G.rule l).args args₁ v = lookupArg (G.rule l).args args₂ v := by
  intro b
  induction b with
  | nil => intro _ w w' he; simpa using he
  | cons y b ihb =>
    intro hs w w' he
    simp only [Str.subst_cons, List.append_assoc] at he
    obtain ⟨hr, hv⟩ := chunk_eq h₁ h₂ ih (hs y (by simp)) (hs y (by simp)) rfl he
    obtain ⟨hw, hv'⟩ := ihb (fun y hy => hs y (by simp [hy])) hr
    refine ⟨hw, fun v hvb => ?_⟩
    rcases List.mem_cons.1 hvb with rfl | hvb
    · exact hv v v rfl rfl
    · exact hv' v hvb

/-- Under an LL certificate, a well-sorted string has a unique parse even as a
prefix of a longer string. -/
theorem LLCert.prefix_unique [DecidableEq C] {F : C → List (C ⊕ C)} (hF : LLCert G F)
    (hfun : Functional ctx) (t : Tree L V) :
    ∀ {t' : Tree L V} {s : C} {w w' : Str C V}, G.HasSort ctx t s → G.HasSort ctx t' s →
      G.flatten t ++ w = G.flatten t' ++ w' → t = t' ∧ w = w' := by
  have varNode : ∀ {v : V} {l' : L} {args' : List (Tree L V)} {s : C} {w w' : Str C V},
      G.HasSort ctx (.var v) s → G.HasSort ctx (.node l' args') s →
      G.flatten (.var v) ++ w = G.flatten (.node l' args') ++ w' → False := by
    intro v l' args' s w w' ht ht' he
    obtain ⟨hs', -, hargs'⟩ := ht'.node_inv
    obtain ⟨i, hi, x, w₀, hx, hfx⟩ := ht'.node_first (F := F) (hF.items_ne_nil l')
      (fun p hp => hF.first (hargs' p hp))
    rw [hx, flatten_var, List.cons_append, List.cons_append, List.cons.injEq] at he
    rw [← he.1] at hfx
    obtain ⟨s', hs'', hm⟩ := hfx
    rw [hfun v s' s hs'' (HasSort.var_iff.1 ht), ← hs'] at hm
    exact hF.var_first l' i hi hm
  induction t using Tree.induction with
  | var v =>
    intro t' s w w' ht ht' he
    cases t' with
    | var v' =>
      simp only [flatten_var, List.singleton_append, List.cons.injEq, Sym.var.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, rfl⟩
    | node l' args' => exact (varNode ht ht' he).elim
  | node l args ih =>
    intro t' s w w' ht ht' he
    cases t' with
    | var v' => exact (varNode ht' ht he.symm).elim
    | node l' args' =>
      obtain ⟨hs₁, hlen₁, -⟩ := ht.node_inv
      obtain ⟨hs₂, hlen₂, -⟩ := ht'.node_inv
      rw [flatten_node, flatten_node] at he
      by_cases hl : l = l'
      · subst hl
        obtain ⟨hw, hv⟩ := walk_same ht ht' (fun c hc => ih c hc) _ (fun _ h => h) he
        refine ⟨?_, hw⟩
        congr 1
        refine lookupArg_ext (G.rule l).args_nodup hlen₁ hlen₂ fun p hp => hv p.2 ?_
        exact Str.mem_vars.1 ((G.rule l).body_perm.symm.subset (List.mem_map_of_mem hp))
      · exact (hF.walk_forks hfun ht ht' (fun c hc => ih c hc) _ _ (fun _ h => h)
          (fun _ h => h) (hF.fork l l' hl (hs₁.trans hs₂.symm)) he).elim

/-- An LL certificate proves unambiguity. -/
theorem LLCert.unambiguous [DecidableEq C] {F : C → List (C ⊕ C)} (hF : LLCert G F) :
    G.Unambiguous := by
  intro ctx hfun s t t' ht ht' he
  exact (hF.prefix_unique hfun t ht ht' (w := []) (w' := []) (by simp [he])).1

end Grammar

end Silmaril.Logic.Metamath
