module

public import Mathlib.Control.Fix
public import Mathlib.Data.Part
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.FixedPoints

/-! # §12 Strictness analysis (notes pp. 21–24; slides pp. 93–98)

The language of recursion equations (notes p. 22)

  `Fᵢ(x₁, …, x_{kᵢ}) = eᵢ`,   `e ::= xᵢ | Aᵢ(e₁, …, e_{rᵢ}) | Fᵢ(e₁, …, e_{kᵢ})`,

over built-ins `Aᵢ`. The standard interpretation is in `D = ℤ⊥`, here
`Part ℤ` with `⊥ = Part.none`, and the user functions denote the least
solution of their equations (`Part.fix`). The abstract interpretation is in
`2 = {0, 1}` (`Bool`, `false` = "guaranteed looping"): each built-in has a
strictness function `a♯`, and the `fᵢ♯` are the least solution of the same
equations over the `a♯` (notes p. 24), a least fixed point in the complete
lattice of functions `2^k → 2`.

* `sharp_safe`: safety (notes p. 24): if `f♯(x⃗) = 0` then `f(d⃗) = ⊥` whenever
  `xᵢ = 0 ⇒ dᵢ = ⊥`, provided each built-in's strictness function is monotone
  and safe;
* `strict_of_sharp`: hence `f` is strict in its `i`th parameter when
  `f♯(1, …, 1, 0, 1, …, 1) = 0`;
* `plusSharp`: for `plus(x,y) = cond(x=0, y, plus(x-1, y+1))`,
  `plus♯(x, y) = x ∧ y` (notes p. 24).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Strictness

/-- A signature: built-ins with arities, standard and strictness
interpretations, and user functions with arities. -/
structure Sig where
  B : Type
  bar : B → ℕ
  sem : (a : B) → (Fin (bar a) → Part ℤ) → Part ℤ
  sharp : (a : B) → (Fin (bar a) → Bool) → Bool
  n : ℕ
  far : Fin n → ℕ

/-- Expressions over `k` parameters. -/
inductive Expr (S : Sig) (k : ℕ) : Type where
  | arg (i : Fin k)
  | prim (a : S.B) (es : Fin (S.bar a) → Expr S k)
  | call (f : Fin S.n) (es : Fin (S.far f) → Expr S k)

namespace Expr

variable {S : Sig} {k : ℕ}

/-- Evaluation over any interpretation of built-ins and user functions. -/
def eval {X : Type} (p : (a : S.B) → (Fin (S.bar a) → X) → X)
    (fs : (f : Fin S.n) → (Fin (S.far f) → X) → X) (env : Fin k → X) : Expr S k → X
  | .arg i => env i
  | .prim a es => p a fun j => (es j).eval p fs env
  | .call f es => fs f fun j => (es j).eval p fs env

/-- Evaluation is monotone in the environment and in the user functions, provided
the built-ins and the smaller interpretation of the user functions are monotone. -/
theorem eval_mono {X : Type} [Preorder X] {p : (a : S.B) → (Fin (S.bar a) → X) → X}
    (hp : ∀ a, Monotone (p a)) {g g' : (f : Fin S.n) → (Fin (S.far f) → X) → X}
    (hg : ∀ f, Monotone (g f)) (hgg : ∀ f x, g f x ≤ g' f x) {env env' : Fin k → X}
    (he : ∀ i, env i ≤ env' i) : ∀ e : Expr S k, e.eval p g env ≤ e.eval p g' env'
  | .arg i => he i
  | .prim a es => hp a fun j => eval_mono hp hg hgg he (es j)
  | .call f es => (hg f fun j => eval_mono hp hg hgg he (es j)).trans (hgg f _)

/-- Abstract evaluation is safe for concrete evaluation: a `0` abstract value
means a `⊥` concrete value, given safe built-ins and safe user functions. -/
theorem eval_safe {sem : (a : S.B) → (Fin (S.bar a) → Part ℤ) → Part ℤ}
    {sharp : (a : S.B) → (Fin (S.bar a) → Bool) → Bool}
    (hsafe : ∀ a x (d : Fin (S.bar a) → Part ℤ), sharp a x = false →
      (∀ j, x j = false → d j = Part.none) → sem a d = Part.none)
    {g : (f : Fin S.n) → (Fin (S.far f) → Bool) → Bool}
    {h : (f : Fin S.n) → (Fin (S.far f) → Part ℤ) → Part ℤ}
    (hg : ∀ f x d, g f x = false → (∀ j, x j = false → d j = Part.none) → h f d = Part.none)
    {x : Fin k → Bool} {d : Fin k → Part ℤ} (hd : ∀ j, x j = false → d j = Part.none) :
    ∀ e : Expr S k, e.eval sharp g x = false → e.eval sem h d = Part.none
  | .arg i, he => hd i he
  | .prim a es, he => hsafe a _ _ he fun j hj => eval_safe hsafe hg hd (es j) hj
  | .call f es, he => hg f _ _ he fun j hj => eval_safe hsafe hg hd (es j) hj

end Expr

/-- A program: a body for each user function. -/
structure Prog (S : Sig) where
  body : (f : Fin S.n) → Expr S (S.far f)

namespace Prog

variable {S : Sig} (P : Prog S)

/-- Interpretations of the user functions in `D`. -/
abbrev Funs (S : Sig) : Type := (f : Fin S.n) → (Fin (S.far f) → Part ℤ) → Part ℤ

/-- The functional whose least fixed point is the standard semantics, uncurried
for `Part.fix`. -/
def Φ (g : (x : Σ f : Fin S.n, Fin (S.far f) → Part ℤ) → Part ℤ) :
    (x : Σ f : Fin S.n, Fin (S.far f) → Part ℤ) → Part ℤ := fun x =>
  (P.body x.1).eval S.sem (fun f d => g ⟨f, d⟩) x.2

/-- The standard semantics `fᵢ` (notes p. 24): the least solution. -/
noncomputable def denote : Funs S := fun f d => Part.fix P.Φ ⟨f, d⟩

/-- Strictness functions of the user functions. -/
abbrev SharpFuns (S : Sig) : Type := (f : Fin S.n) → (Fin (S.far f) → Bool) → Bool

/-- The abstract functional over the `a♯`. -/
def Φsharp (g : SharpFuns S) : SharpFuns S := fun f x => (P.body f).eval S.sharp g x

/-- The strictness functions `fᵢ♯`: the least solution (notes p. 24), defined by
the Knaster–Tarski formula. -/
noncomputable def sharp : SharpFuns S := sInf {g | P.Φsharp g ≤ g}

/-- Monotone strictness functions of the user functions. -/
abbrev MonFuns (S : Sig) : Type := (f : Fin S.n) → (Fin (S.far f) → Bool) →o Bool

/-- The abstract functional restricted to monotone strictness functions. -/
def Φmon (hmono : ∀ a, Monotone (S.sharp a)) : MonFuns S →o MonFuns S where
  toFun m f := ⟨fun x => (P.body f).eval S.sharp (fun f => m f) x,
    fun _ _ h => Expr.eval_mono hmono (fun f => (m f).monotone) (fun _ _ => le_rfl) h _⟩
  monotone' m _ h _ _ :=
    Expr.eval_mono hmono (fun f => (m f).monotone) (fun f x => h f x) (fun _ => le_rfl) _

/-- The least solution over all functions is the least solution over monotone
functions. -/
theorem sharp_eq_lfp (hmono : ∀ a, Monotone (S.sharp a)) :
    P.sharp = fun f x => OrderHom.lfp (P.Φmon hmono) f x := by
  apply le_antisymm
  · apply sInf_le
    intro f x
    exact (congrArg (fun m : MonFuns S => m f x) (P.Φmon hmono).map_lfp).le
  · apply le_sInf
    intro g hg
    let s : Set (MonFuns S) := {m | ∀ f x, m f x ≤ g f x}
    have hs : ∀ f x, (sSup s) f x ≤ g f x := by
      intro f x
      rw [sSup_apply, OrderHom.iSup_apply]
      exact iSup_le fun m => m.2 f x
    have ha : P.Φmon hmono (sSup s) ≤ sSup s := by
      apply le_sSup
      intro f x
      exact (Expr.eval_mono hmono (fun f => ((sSup s) f).monotone) hs (fun _ => le_rfl) _).trans
        (hg f x)
    intro f x
    exact ((OrderHom.lfp_le _ ha) f x).trans (hs f x)

/-- The `fᵢ♯` solve the abstract equations when the `a♯` are monotone. -/
theorem sharp_isFixedPt (hmono : ∀ a, Monotone (S.sharp a)) : P.Φsharp P.sharp = P.sharp := by
  rw [P.sharp_eq_lfp hmono]
  funext f x
  exact congrArg (fun m : MonFuns S => m f x) (P.Φmon hmono).map_lfp

/-- The `fᵢ♯` are below every pre-fixed point. -/
theorem sharp_le {c : SharpFuns S} (hc : P.Φsharp c ≤ c) : P.sharp ≤ c := sInf_le hc

/-- A user function whose equation does not depend on the user functions
denotes its body. -/
theorem denote_eq_of_const {f : Fin S.n} {d : Fin (S.far f) → Part ℤ} {v : Part ℤ}
    (hv : ∀ g, P.Φ g ⟨f, d⟩ = v) : P.denote f d = v := by
  unfold denote
  by_cases h' : ∃ i, (Part.Fix.approx P.Φ i ⟨f, d⟩).Dom
  · rw [Part.fix_def _ h']
    exact hv _
  · rw [Part.fix_def' _ h']
    symm
    rw [Part.eq_none_iff']
    intro hd
    refine h' ⟨1, ?_⟩
    show (P.Φ (Part.Fix.approx P.Φ 0) ⟨f, d⟩).Dom
    rw [hv]
    exact hd

/-- Safety of strictness (notes p. 24). -/
theorem sharp_safe (hmono : ∀ a, Monotone (S.sharp a))
    (hsafe : ∀ a x (d : Fin (S.bar a) → Part ℤ), S.sharp a x = false →
      (∀ j, x j = false → d j = Part.none) → S.sem a d = Part.none)
    {f : Fin S.n} {x : Fin (S.far f) → Bool} (hx : P.sharp f x = false)
    {d : Fin (S.far f) → Part ℤ} (hd : ∀ j, x j = false → d j = Part.none) :
    P.denote f d = Part.none := by
  have key : ∀ i, ∀ (f : Fin S.n) (x : Fin (S.far f) → Bool) (d : Fin (S.far f) → Part ℤ),
      P.sharp f x = false → (∀ j, x j = false → d j = Part.none) →
      Part.Fix.approx P.Φ i ⟨f, d⟩ = Part.none := by
    intro i
    induction i with
    | zero => intro _ _ _ _ _; rfl
    | succ i ih =>
      intro f x d hx hd
      show (P.body f).eval S.sem (fun f d => Part.Fix.approx P.Φ i ⟨f, d⟩) d = Part.none
      refine Expr.eval_safe hsafe (g := P.sharp) (fun f x d hx hd => ih f x d hx hd) hd _ ?_
      rw [← P.sharp_isFixedPt hmono] at hx
      exact hx
  unfold denote
  by_cases h' : ∃ i, (Part.Fix.approx P.Φ i ⟨f, d⟩).Dom
  · rw [Part.fix_def _ h']
    exact key _ f x d hx hd
  · rw [Part.fix_def' _ h']

/-- `g` is strict in parameter `i` (notes p. 22). -/
def IsStrictIn {r : ℕ} (g : (Fin r → Part ℤ) → Part ℤ) (i : Fin r) : Prop :=
  ∀ d, d i = Part.none → g d = Part.none

/-- A user function is strict in `i` when `f♯(1, …, 0, …, 1) = 0`. -/
theorem strict_of_sharp (hmono : ∀ a, Monotone (S.sharp a))
    (hsafe : ∀ a x (d : Fin (S.bar a) → Part ℤ), S.sharp a x = false →
      (∀ j, x j = false → d j = Part.none) → S.sem a d = Part.none)
    {f : Fin S.n} {i : Fin (S.far f)} (h : P.sharp f (fun j => decide (j ≠ i)) = false) :
    IsStrictIn (P.denote f) i := by
  intro d hd
  refine P.sharp_safe hmono hsafe h fun j hj => ?_
  have : j = i := by simpa using hj
  subst this
  exact hd

end Prog

/-! ## The running example: `plus(x,y) = cond(x=0, y, plus(x-1, y+1))` -/

/-- The built-ins of the example. -/
inductive Prim where
  | cond | eq | sub1 | add1 | zero

/-- Arities. -/
@[reducible] def Prim.arity : Prim → ℕ
  | .cond => 3
  | .eq => 2
  | .sub1 | .add1 => 1
  | .zero => 0

/-- Standard interpretations (notes p. 22): strict except `cond` in its
branches. -/
def Prim.sem : (a : Prim) → (Fin a.arity → Part ℤ) → Part ℤ
  | .cond, d => (d 0).bind fun p => if p = 0 then d 2 else d 1
  | .eq, d => (d 0).bind fun a => (d 1).map fun b => if a = b then 1 else 0
  | .sub1, d => (d 0).map (· - 1)
  | .add1, d => (d 0).map (· + 1)
  | .zero, _ => Part.some 0

/-- Strictness functions (notes pp. 23–24): `cond♯(p,x,y) = p ∧ (x ∨ y)`,
`eq♯(x,y) = x ∧ y`, `add1♯(x) = sub1♯(x) = x`, `0♯ = 1`. -/
def Prim.sharp : (a : Prim) → (Fin a.arity → Bool) → Bool
  | .cond, x => x 0 && (x 1 || x 2)
  | .eq, x => x 0 && x 1
  | .sub1, x | .add1, x => x 0
  | .zero, _ => true

/-- The strictness functions are monotone. -/
theorem Prim.sharp_mono : ∀ a, Monotone (Prim.sharp a)
  | .cond => fun x y h => by
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    simp only [Prim.sharp]
    revert h0 h1 h2
    generalize x 0 = a0; generalize x 1 = a1; generalize x 2 = a2
    generalize y 0 = b0; generalize y 1 = b1; generalize y 2 = b2
    revert a0 a1 a2 b0 b1 b2
    decide
  | .eq => fun x y h => by
    have h0 := h 0; have h1 := h 1
    simp only [Prim.sharp]
    revert h0 h1
    generalize x 0 = a0; generalize x 1 = a1
    generalize y 0 = b0; generalize y 1 = b1
    revert a0 a1 b0 b1
    decide
  | .sub1 => fun _ _ h => h 0
  | .add1 => fun _ _ h => h 0
  | .zero => fun _ _ _ => le_rfl

theorem part_bind_none_right {α β : Type} (x : Part α) :
    x.bind (fun _ => (Part.none : Part β)) = Part.none :=
  Part.eq_none_iff.2 fun b hb => by
    obtain ⟨_, _, h⟩ := Part.mem_bind_iff.1 hb
    exact Part.notMem_none b h

/-- The strictness functions are safe. -/
theorem Prim.sharp_safe : ∀ a x (d : Fin a.arity → Part ℤ), Prim.sharp a x = false →
    (∀ j, x j = false → d j = Part.none) → Prim.sem a d = Part.none
  | .cond, x, d, hx, hd => by
    simp only [Prim.sharp, Bool.and_eq_false_iff, Bool.or_eq_false_iff] at hx
    rcases hx with h0 | ⟨h1, h2⟩
    · simp only [Prim.sem, hd 0 h0, Part.bind_none]
    · simp only [Prim.sem, hd 1 h1, hd 2 h2, ite_self, part_bind_none_right]
  | .eq, x, d, hx, hd => by
    simp only [Prim.sharp, Bool.and_eq_false_iff] at hx
    rcases hx with h0 | h1
    · simp only [Prim.sem, hd 0 h0, Part.bind_none]
    · simp only [Prim.sem, hd 1 h1, Part.map_none, part_bind_none_right]
  | .sub1, x, d, hx, hd => by simp only [Prim.sem, hd 0 hx, Part.map_none]
  | .add1, x, d, hx, hd => by simp only [Prim.sem, hd 0 hx, Part.map_none]
  | .zero, _, _, hx, _ => by simp [Prim.sharp] at hx

/-- The signature of the example: one user function of arity 2. -/
@[reducible] def plusSig : Sig where
  B := Prim
  bar := Prim.arity
  sem := Prim.sem
  sharp := Prim.sharp
  n := 1
  far _ := 2

/-- `plus(x,y) = cond(x=0, y, plus(x-1, y+1))`. -/
def plusProg : Prog plusSig where
  body _ :=
    .prim Prim.cond ![
      .prim Prim.eq ![.arg 0, .prim Prim.zero ![]],
      .arg 1,
      .call 0 ![.prim Prim.sub1 ![.arg 0], .prim Prim.add1 ![.arg 1]]]

/-- `plus♯(x, y) = x ∧ y` (notes p. 24). -/
theorem plusSharp : plusProg.sharp 0 = fun x => x 0 && x 1 := by
  have hle := plusProg.sharp_le (c := fun _ x => x 0 && x 1) (by
    intro _ x
    show ((x 0 && true) && (x 1 || (x 0 && x 1))) ≤ (x 0 && x 1)
    generalize x 0 = a
    generalize x 1 = b
    cases a <;> cases b <;> decide)
  funext x
  apply le_antisymm (hle 0 x)
  have hfix := congrFun (congrFun (plusProg.sharp_isFixedPt Prim.sharp_mono) 0) x
  rw [← hfix]
  show (x 0 && x 1) ≤ ((x 0 && true) && (x 1 || _))
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp

/-- Hence `plus` is strict in both parameters (notes p. 25). -/
theorem plus_strict (i : Fin 2) : Prog.IsStrictIn (plusProg.denote 0) i := by
  refine plusProg.strict_of_sharp Prim.sharp_mono Prim.sharp_safe ?_
  rw [plusSharp]
  revert i
  decide

end Silmaril.Courses.Cambridge.OptimisingCompilers.Strictness
