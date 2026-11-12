module

public import Silmaril.Wasm.FnInst.Opt.Seg.Thms
public import Silmaril.Logic.Inst.Builders.Core.Defs

@[expose] public section

/-! # The segment institution of the opt track

Signatures are holes `X : HSig` (visible function types, stack type `n → m`). A signature
morphism `σ : X ⟶ Y` is a *typed context*: code `pre` before the hole and `post` after it,
`j` extra values kept below the hole, over function types that extend `X`'s (added functions
keep their indices). Plugging `plug σ s = pre ++ s ++ post` maps segments of `X` to segments
of `Y`; composition nests contexts.

Models of `Y` are environments that say nothing about functions `Y` cannot see
(`Model Y`: `Env.top` past `Y.ft`); the reduct along `σ` forgets the functions `X` cannot see.

Sentences are *scoped*: a sentence of `Y` is a hole `X` placed in `Y` by `τ : X ⟶ Y`, and a
formula `φ` over `X`'s segments: equivalence `s ≈ s'`, refinement `s ⊑ s'` (every outcome of
`s` is one of `s'`), distinction in some completion and in every completion, and conjunction.
A model `M` satisfies `(τ, φ)` when `φ` holds of `M`'s reduct at `X`. The scope is part of the
sentence for the same reason as in the module logics of `docs/projects/logic-inst.md`:
equivalence of plugged code is *not* equivalence of the plugged segments (a context can hide a
difference), so translating `s ≈ s'` to `plug σ s ≈ plug σ s'` would break the satisfaction
condition in one direction. That direction is exactly the *peephole-rewrite theorem*
(`Silmaril.Wasm.FnInst.Opt.Inst.Thms`), proved as an entailment
`(τ, s ≈ s') ⊨ (𝟙, plug τ s ≈ plug τ s')`.

Formula semantics (`holds`): over a partial model `M`, the completions of `M` are the typed,
total environments narrower than `M` (`Env.Completion`); equivalence and refinement must hold in
every completion; `distSome` asks for a difference in some completion, `distEvery` in every
completion.
-/

namespace Silmaril.Wasm.FnInst.Opt

open CategoryTheory

namespace HSig

/-- A typed context placing hole `X` inside hole `Y`. -/
structure Hom (X Y : HSig) where
  /-- Code before the hole. -/
  pre : Code
  /-- Code after the hole. -/
  post : Code
  /-- Values kept below the hole. -/
  j : ℕ
  ft_le : X.ft <+: Y.ft
  pre_ty : chk Y.ft pre Y.n = some (X.n + j)
  post_ty : chk Y.ft post (X.m + j) = some Y.m

theorem Hom.ext' {X Y : HSig} {σ τ : Hom X Y} (h₁ : σ.pre = τ.pre) (h₂ : σ.post = τ.post)
    (h₃ : σ.j = τ.j) : σ = τ := by
  cases σ; cases τ; cases h₁; cases h₂; cases h₃; rfl

/-- The empty context. -/
def Hom.id (X : HSig) : Hom X X where
  pre := []
  post := []
  j := 0
  ft_le := List.prefix_refl _
  pre_ty := rfl
  post_ty := rfl

/-- Nesting contexts: `σ` inside `τ`. -/
def Hom.comp {X Y Z : HSig} (σ : Hom X Y) (τ : Hom Y Z) : Hom X Z where
  pre := τ.pre ++ σ.pre
  post := σ.post ++ τ.post
  j := σ.j + τ.j
  ft_le := σ.ft_le.trans τ.ft_le
  pre_ty := by
    rw [chk_append, τ.pre_ty, Option.bind_some, chk_frame τ.j (chk_ft τ.ft_le σ.pre_ty),
      Nat.add_assoc]
  post_ty := by
    rw [chk_append, ← Nat.add_assoc, chk_frame τ.j (chk_ft τ.ft_le σ.post_ty), Option.bind_some,
      τ.post_ty]

instance : Category HSig where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext' (List.append_nil _) rfl (Nat.zero_add _)
  comp_id _ := Hom.ext' rfl (List.append_nil _) (Nat.add_zero _)
  assoc _ _ _ := Hom.ext' (List.append_assoc _ _ _).symm (List.append_assoc _ _ _)
    (Nat.add_assoc _ _ _)

@[simp] theorem id_pre (X : HSig) : (𝟙 X : X ⟶ X).pre = [] := rfl
@[simp] theorem id_post (X : HSig) : (𝟙 X : X ⟶ X).post = [] := rfl
@[simp] theorem comp_pre {X Y Z : HSig} (σ : X ⟶ Y) (τ : Y ⟶ Z) :
    (σ ≫ τ).pre = τ.pre ++ σ.pre := rfl
@[simp] theorem comp_post {X Y Z : HSig} (σ : X ⟶ Y) (τ : Y ⟶ Z) :
    (σ ≫ τ).post = σ.post ++ τ.post := rfl

end HSig

/-! ## Plugging -/

/-- Code placed in a context. -/
def plugC {X Y : HSig} (σ : X ⟶ Y) (c : Code) : Code := σ.pre ++ c ++ σ.post

theorem plugC_ty {X Y : HSig} (σ : X ⟶ Y) {c : Code} (hc : chk X.ft c X.n = some X.m) :
    chk Y.ft (plugC σ c) Y.n = some Y.m := by
  unfold plugC
  rw [chk_append, chk_append, σ.pre_ty, Option.bind_some,
    chk_frame σ.j (chk_ft σ.ft_le hc), Option.bind_some, σ.post_ty]

/-- A segment placed in a context. -/
def plug {X Y : HSig} (σ : X ⟶ Y) (s : Seg X) : Seg Y := ⟨plugC σ s.1, plugC_ty σ s.2⟩

theorem plug_id {X : HSig} (s : Seg X) : plug (𝟙 X) s = s :=
  Subtype.ext (by simp [plug, plugC])

theorem plug_comp {X Y Z : HSig} (σ : X ⟶ Y) (τ : Y ⟶ Z) (s : Seg X) :
    plug (σ ≫ τ) s = plug τ (plug σ s) :=
  Subtype.ext (by simp [plug, plugC, List.append_assoc])

/-! ## Formulas and their semantics -/

/-- Formulas over the segments of a hole. -/
inductive Form (X : HSig) where
  /-- Equivalence in every completion. -/
  | equiv (s s' : Seg X)
  /-- Refinement in every completion: every outcome of `s` is one of `s'`. -/
  | refine (s s' : Seg X)
  /-- An observable difference in some completion. -/
  | distSome (s s' : Seg X)
  /-- An observable difference in every completion. -/
  | distEvery (s s' : Seg X)
  /-- Conjunction. -/
  | and (φ ψ : Form X)

/-- Satisfaction of a formula at hole `X` by an environment `M` (a partial model). -/
def holds (X : HSig) (M : Env) : Form X → Prop
  | .equiv s s' => ∀ E, E.Completion X.ft M → RunEq X.ft X.n E s.1 s'.1
  | .refine s s' => ∀ E, E.Completion X.ft M → RunLe X.ft X.n E s.1 s'.1
  | .distSome s s' => ∃ E, E.Completion X.ft M ∧ ¬ RunEq X.ft X.n E s.1 s'.1
  | .distEvery s s' => ∀ E, E.Completion X.ft M → ¬ RunEq X.ft X.n E s.1 s'.1
  | .and φ ψ => holds X M φ ∧ holds X M ψ

/-- Formulas preserved by adding information (narrowing the model). -/
def Form.Positive {X : HSig} : Form X → Prop
  | .equiv _ _ | .refine _ _ | .distEvery _ _ => True
  | .distSome _ _ => False
  | .and φ ψ => φ.Positive ∧ ψ.Positive

/-! ## Models and the institution -/

/-- Forget the functions at indices `k` and above (they become unspecified). -/
def Env.restrict (k : ℕ) (E : Env) : Env := fun f => if f < k then E f else Env.top f

/-- Models of `X`: environments that leave every function `X` cannot see unspecified. -/
abbrev Model (X : HSig) : Type := {E : Env // ∀ f, X.ft.length ≤ f → E f = Env.top f}

theorem Env.restrict_restrict {a b : ℕ} (hab : a ≤ b) (E : Env) :
    (E.restrict b).restrict a = E.restrict a := by
  funext f
  unfold Env.restrict
  by_cases ha : f < a
  · rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left (Nat.lt_of_lt_of_le ha hab)]
  · rw [ite_eq_right ha, ite_eq_right ha]

/-- The reduct: forget what `X` cannot see. -/
def Model.reduct {X Y : HSig} (_ : X ⟶ Y) (M : Model Y) : Model X :=
  ⟨M.1.restrict X.ft.length, fun f hf => by
    unfold Env.restrict
    rw [ite_eq_right (Nat.not_lt.mpr hf)]⟩

theorem Model.reduct_id {X : HSig} (M : Model X) : Model.reduct (𝟙 X) M = M := by
  apply Subtype.ext
  funext f
  show (if f < X.ft.length then M.1 f else Env.top f) = M.1 f
  by_cases hf : f < X.ft.length
  · rw [ite_eq_left hf]
  · rw [ite_eq_right hf, M.2 f (Nat.not_lt.mp hf)]

theorem Model.reduct_comp {X Y Z : HSig} (σ : X ⟶ Y) (τ : Y ⟶ Z) (M : Model Z) :
    Model.reduct (σ ≫ τ) M = Model.reduct σ (Model.reduct τ M) :=
  Subtype.ext (Env.restrict_restrict σ.ft_le.length_le M.1).symm

/-- Sentences of `Y`: a hole placed in `Y`, and a formula over the hole. -/
def Sen (Y : HSig) : Type := Σ X : HSig, (X ⟶ Y) × Form X

/-- Satisfaction of a scoped sentence. -/
def Sat {Y : HSig} (M : Model Y) : Sen Y → Prop
  | ⟨X, τ, φ⟩ => holds X (Model.reduct τ M).1 φ

/-- The segment institution, as a plain presentation. -/
def segPlain : Silmaril.Inst.Plain.{0, 0, 0, 0} HSig where
  Sen := Sen
  map σ φ := ⟨φ.1, φ.2.1 ≫ σ, φ.2.2⟩
  map_id _ φ := by
    obtain ⟨X, τ, ψ⟩ := φ
    simp only [Category.comp_id]
    rfl
  map_comp σ τ φ := by
    obtain ⟨X, υ, ψ⟩ := φ
    simp only [Category.assoc]
    rfl
  Mod := Model
  reduct := Model.reduct
  reduct_id _ M := Model.reduct_id M
  reduct_comp σ τ M := Model.reduct_comp σ τ M
  Sat M φ := Sat M φ
  sat_map σ M φ := by
    obtain ⟨X, τ, ψ⟩ := φ
    show holds X (Model.reduct (τ ≫ σ) M).1 ψ ↔ holds X (Model.reduct τ (Model.reduct σ M)).1 ψ
    rw [Model.reduct_comp]

/-- **The segment institution** (`Silmaril.Inst` facade). -/
abbrev segInst : Silmaril.Inst.Institution.{0, 0, 0, 0, 0} := segPlain.toInst

/-- The sentence `s ≈ s'` at `Y` itself (empty scope). -/
def Sen.equiv {Y : HSig} (s s' : Seg Y) : Sen Y := ⟨Y, 𝟙 Y, .equiv s s'⟩

/-- The sentence `s ≈ s'` of a hole `X` placed in `Y` by `τ`. -/
def Sen.scoped {X Y : HSig} (τ : X ⟶ Y) (φ : Form X) : Sen Y := ⟨X, τ, φ⟩

/-- The environment where every call traps: a completion of the least informative model. -/
def Env.trapAll : Env := fun _ _ _ => {Ans.trap}

end Silmaril.Wasm.FnInst.Opt
