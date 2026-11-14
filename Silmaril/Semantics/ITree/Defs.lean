module

public import Silmaril.Semantics.Elgot.Thms

/-!
# ITree

Source: interaction trees, which the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126` compares with trace models after
Concrete Models, §Trace Models.

-/

@[expose] public section

section

/-!
## Interaction trees as coherent finite observations

Lean has no primitive coinductive types.  We therefore present an interaction
tree by all of its finite observations, together with the proof that adjacent
observations agree.  Between two visible nodes observation is partial: `none`
is silent divergence, while `some` exposes either a return or a visible event.

This is the weak (tau-insensitive) model of interaction trees.  Consequently
`tau t = t`; finite silent delays are unobservable, whereas an infinite silent
computation is `diverge`.  This equality is the one appropriate for the
complete-Elgot equations, which do not hold for raw, strongly bisimilar ITrees.
-/

namespace Silmaril.Elgot.ITree

universe u v w

/-- One visible observation of an interaction tree. -/
inductive Visible (E : Type u → Type u) (A : Type v) (X : Type w) : Type (max (u + 1) v w)
  | ret (value : A)
  | vis {R : Type u} (event : E R) (next : R → X)

namespace Visible

def map {E : Type u → Type u} {A : Type v} {X Y : Type w} (f : X → Y) :
    Visible E A X → Visible E A Y
  | .ret a => .ret a
  | .vis e k => .vis e (f ∘ k)

@[simp] theorem map_ret {E : Type u → Type u} {A : Type v} {X Y : Type w} (f : X → Y) (a : A) :
    map f (.ret a : Visible E A X) = .ret a := rfl

@[simp] theorem map_vis {E : Type u → Type u} {A : Type v} {X Y : Type w} {R : Type u}
    (f : X → Y) (e : E R) (k : R → X) :
    map f (.vis e k : Visible E A X) = .vis e (f ∘ k) := rfl

end Visible

/-- The observation of a tree to depth `n`.  Depth zero contains no data. -/
abbrev Approx (E : Type u → Type u) (A : Type v) : Nat → Type (max (u + 1) v)
  | 0 => PUnit
  | n + 1 => Part (Visible E A (Approx E A n))

/-- Forget the deepest visible layer of a finite observation. -/
def Approx.truncate {E : Type u → Type u} {A : Type v} :
    (n : Nat) → Approx E A (n + 1) → Approx E A n
  | 0, _ => PUnit.unit
  | n + 1, x => Visible.map (Approx.truncate n) <$> x

/-- A weak interaction tree is a coherent family of finite observations. -/
structure Tree (E : Type u → Type u) (A : Type v) : Type (max (u + 1) v) where
  observe : (n : Nat) → Approx E A n
  coherent : ∀ n, Approx.truncate n (observe (n + 1)) = observe n

@[ext]
theorem Tree.ext {E : Type u → Type u} {A : Type v} {x y : Tree E A}
    (h : ∀ n, x.observe n = y.observe n) : x = y := by
  cases x with
  | mk xo xc =>
    cases y with
    | mk yo yc =>
      simp only [Tree.mk.injEq]
      funext n
      exact h n

/-- Return immediately. -/
def ret {E : Type u → Type u} {A : Type v} (a : A) : Tree E A where
  observe
    | 0 => PUnit.unit
    | _ + 1 => Part.some (.ret a)
  coherent
    | 0 => rfl
    | _ + 1 => by simp [Approx.truncate]

/-- Silent divergence: no finite visible observation is ever produced. -/
def diverge {E : Type u → Type u} {A : Type v} : Tree E A where
  observe
    | 0 => PUnit.unit
    | _ + 1 => Part.none
  coherent
    | 0 => rfl
    | _ + 1 => by simp [Approx.truncate]

/-- Perform one visible event and continue from its response. -/
def vis {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) (k : R → Tree E A) : Tree E A where
  observe
    | 0 => PUnit.unit
    | n + 1 => Part.some (.vis e (fun r => (k r).observe n))
  coherent
    | 0 => rfl
    | n + 1 => by
      simp only [Approx.truncate, Part.map_eq_map, Part.map_some, Visible.map_vis]
      congr
      funext r
      exact (k r).coherent n

/-- A finite silent step is observationally irrelevant in the weak model. -/
def tau {E : Type u → Type u} {A : Type v} (t : Tree E A) : Tree E A := t

end Silmaril.Elgot.ITree

end

section

namespace Silmaril.Elgot.ITree

universe u v

namespace Approx

/-- Bind finite observations, consuming one unit of depth at every visible event. -/
def bind {E : Type u → Type u} {A B : Type v} :
    (n : Nat) → Approx E A n → (A → Approx E B n) → Approx E B n
  | 0, _, _ => PUnit.unit
  | n + 1, x, k => x >>= fun
      | .ret a => k a
      | .vis e next => Part.some (.vis e (fun r => bind n (next r)
          (fun a => truncate n (k a))))

@[simp] theorem bind_zero {E : Type u → Type u} {A B : Type v}
    (x : Approx E A 0) (k : A → Approx E B 0) : bind 0 x k = PUnit.unit := rfl

theorem truncate_bind {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E A (n + 1)) (k : A → Approx E B (n + 1)) :
    truncate n (bind (n + 1) x k) =
      bind n (truncate n x) (fun a => truncate n (k a)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [truncate, bind, Part.map_eq_map, Part.bind_eq_bind, Part.map_bind,
        Part.bind_map]
      apply congrArg (Part.bind x)
      funext node
      cases node with
      | ret a => simp
      | vis e next =>
          simp
          funext r
          change truncate n (bind (n + 1) (next r) (fun a => truncate (n + 1) (k a))) = _
          exact ih (next r) (fun a => truncate (n + 1) (k a))

end Approx

/-- Monadic sequencing of weak interaction trees. -/
def bind {E : Type u → Type u} {A B : Type v}
    (t : Tree E A) (k : A → Tree E B) : Tree E B where
  observe n := Approx.bind n (t.observe n) (fun a => (k a).observe n)
  coherent n := by
    rw [Approx.truncate_bind]
    congr 1
    · exact t.coherent n
    · funext a
      exact (k a).coherent n

instance instMonad (E : Type u → Type u) : Monad (Tree E) where
  pure := ret
  bind := bind

namespace Approx

end Approx

end Silmaril.Elgot.ITree

end

section

namespace Silmaril.Elgot.ITree

open Silmaril.Elgot

universe u v

namespace Approx

/-- Iterate a finite observation.  Recursive returns are discharged by `Part.iter`;
visible continuations recurse at strictly smaller observation depth. -/
noncomputable def iter {E : Type u → Type u} {A B : Type v} :
    (n : Nat) → Approx E (B ⊕ A) n → (A → Approx E (B ⊕ A) n) → Approx E B n
  | 0, _, _ => PUnit.unit
  | n + 1, x, f => Silmaril.Elgot.iter (fun x => x >>= fun
      | .ret (.inl b) => Part.some (.inl (.ret b))
      | .ret (.inr a) => Part.some (.inr (f a))
      | .vis e next => Part.some (.inl (.vis e (fun r =>
          iter n (next r) (fun a => truncate n (f a)))))) x

/-- One partial step of iteration at a fixed observation depth. -/
noncomputable def iterStep {E : Type u → Type u} {A B : Type v} (n : Nat)
    (f : A → Approx E (B ⊕ A) (n + 1)) :
    Approx E (B ⊕ A) (n + 1) →
      Part (Visible E B (Approx E B n) ⊕ Approx E (B ⊕ A) (n + 1)) :=
  fun x => x >>= fun
    | .ret (.inl b) => Part.some (.inl (.ret b))
    | .ret (.inr a) => Part.some (.inr (f a))
    | .vis e next => Part.some (.inl (.vis e (fun r =>
        iter n (next r) (fun a => truncate n (f a)))))

@[simp] theorem iter_succ {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1)) (f : A → Approx E (B ⊕ A) (n + 1)) :
    iter (n + 1) x f = Silmaril.Elgot.iter (iterStep n f) x := rfl

private theorem truncate_iterStep_square {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E (B ⊕ A) (n + 2))
    (ih : ∀ (x : Approx E (B ⊕ A) (n + 1)),
      truncate n (iter (n + 1) x (fun a => truncate (n + 1) (f a))) =
        iter n (truncate n x) (fun a => truncate n (truncate (n + 1) (f a)))) :
    ((mapReturn (iterStep (n + 1) f)
        (liftPure (Visible.map (truncate n)))) >=> (liftPure (Sum.map id (truncate (E := E) (A := B ⊕ A) (n + 1))))) =
      ((liftPure (truncate (E := E) (A := B ⊕ A) (n + 1))) >=> (iterStep n (fun a => truncate (n + 1) (f a)))) := by
  funext x
  simp [Bind.kleisliRight, mapReturn, liftPure, Function.comp_apply, iterStep,
    truncate, Part.map_eq_map, Part.bind_assoc, Part.bind_map]
  apply congrArg (Part.bind x)
  funext node
  cases node with
  | ret s =>
      cases s <;> simp
  | vis e next =>
      simp
      funext r
      exact ih (next r)

theorem truncate_iter {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1))
    (f : A → Approx E (B ⊕ A) (n + 1)) :
    truncate n (iter (n + 1) x f) =
      iter n (truncate n x) (fun a => truncate n (f a)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (Visible.map (truncate n) <$> Silmaril.Elgot.iter (iterStep (n + 1) f) x) = _
      calc
        Visible.map (truncate n) <$> Silmaril.Elgot.iter (iterStep (n + 1) f) x =
            (Silmaril.Elgot.iter (iterStep (n + 1) f) >=> liftPure (Visible.map (truncate n))) x := by
                symm
                exact Part.bind_some_eq_map _ _
        _ = Silmaril.Elgot.iter
            (mapReturn (iterStep (n + 1) f) (liftPure (Visible.map (truncate n)))) x :=
              congrFun (LawfulElgotMonad.naturality (m := Part)
                (iterStep (n + 1) f) (liftPure (Visible.map (truncate n)))) x
        _ = (liftPure (truncate (E := E) (A := B ⊕ A) (n + 1)) >=>
            Silmaril.Elgot.iter (iterStep n (fun a => truncate (n + 1) (f a)))) x :=
              congrFun (LawfulElgotMonad.uniformity (m := Part)
                (mapReturn (iterStep (n + 1) f) (liftPure (Visible.map (truncate n))))
                (iterStep n (fun a => truncate (n + 1) (f a)))
                (truncate (E := E) (A := B ⊕ A) (n + 1))
                (truncate_iterStep_square n f (fun y => ih y (fun a => truncate (n + 1) (f a))))) x
        _ = iter (n + 1) (truncate (n + 1) x) (fun a => truncate (n + 1) (f a)) := by
              simp [Bind.kleisliRight, liftPure]

end Approx

/-- Complete iteration for weak interaction trees. -/
noncomputable def iterate {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E (B ⊕ A)) (a : A) : Tree E B where
  observe n := Approx.iter n ((f a).observe n) (fun a => (f a).observe n)
  coherent n := by
    rw [Approx.truncate_iter]
    congr 1
    · exact (f a).coherent n
    · funext a
      exact (f a).coherent n

noncomputable instance instIterate (E : Type u → Type u) : Iterate (Tree E) where
  iter := iterate

end Silmaril.Elgot.ITree

end

section

namespace Silmaril.Elgot.ITree

open Silmaril.Elgot

universe u v

namespace Approx

/-- Act effectfully on the returned summand of a finite observation. -/
def mapReturn {E : Type u → Type u} {A B C : Type v} (n : Nat)
    (x : Approx E (B ⊕ A) n) (g : B → Approx E C n) : Approx E (C ⊕ A) n :=
  bind n x (Sum.elim
    (fun b => bind n (g b) (fun c => (ret (E := E) (Sum.inl c)).observe n))
    (fun a => (ret (E := E) (Sum.inr a)).observe n))

def mapInl {E : Type u → Type u} {A B : Type v} (n : Nat)
    (x : Approx E B n) : Approx E (B ⊕ A) n :=
  bind n x (fun b => (ret (E := E) (Sum.inl b)).observe n)

def post {E : Type u → Type u} {B C : Type v} (n : Nat)
    (g : B → Approx E C (n + 1)) :
    Visible E B (Approx E B n) → Part (Visible E C (Approx E C n))
  | .ret b => g b
  | .vis e next => Part.some (.vis e (fun r => bind n (next r)
      (fun b => truncate n (g b))))

/-- Rename only the recursive return summand of a finite observation. -/
def mapState {E : Type u → Type u} {A B C : Type v} (n : Nat)
    (x : Approx E (B ⊕ A) n) (h : A → C) : Approx E (B ⊕ C) n :=
  bind n x (fun s => (ret (E := E) (Sum.map id h s)).observe n)

/-- Merge the two recursive summands of a finite observation. -/
def flattenApprox {E : Type u → Type u} {A B : Type v} (n : Nat)
    (x : Approx E ((B ⊕ A) ⊕ A) n) : Approx E (B ⊕ A) n :=
  bind n x (fun s => (ret (E := E) (Silmaril.Elgot.flatten s)).observe n)

/-- A two-level residual machine. Its two recursive summands respectively
represent recursion of the outer and inner iterations. -/
noncomputable def doubleStep {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E ((B ⊕ A) ⊕ A) (n + 1)) :
    Approx E ((B ⊕ A) ⊕ A) (n + 1) →
      Part ((Visible E B (Approx E B n) ⊕ Approx E ((B ⊕ A) ⊕ A) (n + 1)) ⊕
        Approx E ((B ⊕ A) ⊕ A) (n + 1)) :=
  fun x => x >>= fun
    | .ret (.inl (.inl b)) => Part.some (.inl (.inl (.ret b)))
    | .ret (.inl (.inr a)) => Part.some (.inl (.inr (f a)))
    | .ret (.inr a) => Part.some (.inr (f a))
    | .vis e next => Part.some (.inl (.inl (.vis e (fun r =>
        iter n (iter n (next r) (fun a => truncate n (f a)))
          (fun a => iter n (truncate n (f a)) (fun a => truncate n (f a)))))))

end Approx

end Silmaril.Elgot.ITree

end

section

/-! Flattening nested iteration of weak interaction trees. -/

namespace Silmaril.Elgot.ITree

open Silmaril.Elgot

universe u v

namespace Approx

/-- Process one visible result of the inner iteration, retaining outer recursion. -/
noncomputable def doublePost {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E ((B ⊕ A) ⊕ A) (n + 1)) :
    Visible E (B ⊕ A) (Approx E (B ⊕ A) n) →
      Part (Visible E B (Approx E B n) ⊕ Approx E ((B ⊕ A) ⊕ A) (n + 1))
  | .ret (.inl b) => Part.some (.inl (.ret b))
  | .ret (.inr a) => Part.some (.inr (f a))
  | .vis e next => Part.some (.inl (.vis e (fun r =>
      iter n (next r) (fun a => iter n (truncate n (f a)) (fun a => truncate n (f a))))))

end Approx

end Silmaril.Elgot.ITree

end

section

/-! ## The visible layer of a weak interaction tree

Coherence fixes the first visible constructor and makes its finite continuation
observations into trees. Thus the existing observation model is isomorphic to
one partial visible layer whose continuations are again trees.
-/

namespace Silmaril.Elgot.ITree

universe u v w

namespace Visible

theorem map_eq_ret_iff {E : Type u → Type u} {A : Type v} {X Y : Type w}
    (f : X → Y) (x : Visible E A X) (a : A) :
    map f x = .ret a ↔ x = .ret a := by
  cases x <;> simp [map]

theorem map_eq_vis_iff {E : Type u → Type u} {A : Type v} {X Y : Type w}
    (f : X → Y) (x : Visible E A X) {R : Type u} (e : E R) (k : R → Y) :
    map f x = .vis e k ↔ ∃ next : R → X, x = .vis e next ∧ f ∘ next = k := by
  constructor
  · intro eq
    cases x with
    | ret a => cases eq
    | vis event next =>
      cases eq
      exact ⟨next, rfl, rfl⟩
  · rintro ⟨next, rfl, rfl⟩
    rfl

end Visible

/-- Assemble one partial visible layer into its coherent finite observations. -/
def roll {E : Type u → Type u} {A : Type v}
    (x : Part (Visible E A (Tree E A))) : Tree E A where
  observe
    | 0 => PUnit.unit
    | n + 1 => Visible.map (fun t => t.observe n) <$> x
  coherent
    | 0 => rfl
    | n + 1 => by
      simp only [Approx.truncate, Part.map_eq_map, Part.map_map]
      apply congrArg (fun f => Part.map f x)
      funext node
      cases node with
      | ret a => rfl
      | vis event next =>
        simp only [Function.comp_apply, Visible.map_vis]
        congr 1
        funext r
        exact (next r).coherent n

@[simp] theorem roll_none {E : Type u → Type u} {A : Type v} :
    roll (Part.none : Part (Visible E A (Tree E A))) = diverge := by
  apply Tree.ext
  intro n
  cases n <;> simp [roll, diverge]

@[simp] theorem roll_ret {E : Type u → Type u} {A : Type v} (a : A) :
    roll (Part.some (.ret a) : Part (Visible E A (Tree E A))) = ret a := rfl

@[simp] theorem roll_vis {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) (k : R → Tree E A) : roll (Part.some (.vis e k)) = vis e k := rfl

private theorem part_map_none {X Y : Type w} (f : X → Y) (x : Part X) :
    f <$> x = Part.none ↔ x = Part.none := by
  simp only [Part.map_eq_map, Part.eq_none_iff', Part.map]

private theorem part_map_some {X Y : Type w} (f : X → Y) (x : Part X) (y : Y) :
    f <$> x = Part.some y ↔ ∃ z, x = Part.some z ∧ f z = y := by
  simp only [Part.eq_some_iff, Part.map_eq_map, Part.mem_map_iff]

private theorem observe_none_of_first {E : Type u → Type u} {A : Type v}
    (t : Tree E A) (h : t.observe 1 = Part.none) (n : Nat) :
    t.observe (n + 1) = Part.none := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact (part_map_none (Visible.map (Approx.truncate n)) _).mp
      ((t.coherent (n + 1)).trans ih)

private theorem observe_ret_of_first {E : Type u → Type u} {A : Type v}
    (t : Tree E A) (a : A) (h : t.observe 1 = Part.some (.ret a)) (n : Nat) :
    t.observe (n + 1) = Part.some (.ret a) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    obtain ⟨node, found, eq⟩ := (part_map_some (Visible.map (Approx.truncate n)) _ _).mp
      ((t.coherent (n + 1)).trans ih)
    rw [(Visible.map_eq_ret_iff ..).mp eq] at found
    exact found

private theorem observe_vis_of_first {E : Type u → Type u} {A : Type v} {R : Type u}
    (t : Tree E A) (e : E R) (k : R → Approx E A 0)
    (h : t.observe 1 = Part.some (.vis e k)) (n : Nat) :
    ∃ next : R → Approx E A n, t.observe (n + 1) = Part.some (.vis e next) := by
  induction n with
  | zero => exact ⟨k, h⟩
  | succ n ih =>
    obtain ⟨next, found⟩ := ih
    obtain ⟨node, observed, eq⟩ := (part_map_some (Visible.map (Approx.truncate n)) _ _).mp
      ((t.coherent (n + 1)).trans found)
    obtain ⟨next', rfl, _⟩ := (Visible.map_eq_vis_iff ..).mp eq
    exact ⟨next', observed⟩

/-- Every coherent observation family has an actual root and coherent subtrees. -/
theorem roll_surjective {E : Type u → Type u} {A : Type v} :
    Function.Surjective (roll (E := E) (A := A)) := by
  classical
  intro t
  have first : t.observe 1 = Part.none ∨ ∃ node, t.observe 1 = Part.some node := by
    exact Part.induction_on (t.observe 1) (Or.inl rfl) (fun node => Or.inr ⟨node, rfl⟩)
  rcases first with empty | ⟨node, observed⟩
  · refine ⟨Part.none, ?_⟩
    rw [roll_none]
    apply Tree.ext
    intro n
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n => exact (observe_none_of_first t empty n).symm
  · cases node with
    | ret a =>
      refine ⟨Part.some (.ret a), ?_⟩
      rw [roll_ret]
      apply Tree.ext
      intro n
      cases n with
      | zero => exact Subsingleton.elim _ _
      | succ n => exact (observe_ret_of_first t a observed n).symm
    | @vis R e k =>
      let next (n : Nat) : R → Approx E A n :=
        Classical.choose (observe_vis_of_first t e k observed n)
      have found (n : Nat) : t.observe (n + 1) = Part.some (.vis e (next n)) :=
        Classical.choose_spec (observe_vis_of_first t e k observed n)
      have coherent (n : Nat) (r : R) : Approx.truncate n (next (n + 1) r) = next n r := by
        have eq := t.coherent (n + 1)
        rw [found (n + 1), found n] at eq
        simp only [Approx.truncate, Part.map_eq_map, Part.map_some, Visible.map_vis,
          Part.some_inj, Visible.vis.injEq, heq_eq_eq, true_and] at eq
        exact congrFun eq r
      let continuation (r : R) : Tree E A := ⟨fun n => next n r, fun n => coherent n r⟩
      refine ⟨Part.some (.vis e continuation), ?_⟩
      rw [roll_vis]
      apply Tree.ext
      intro n
      cases n with
      | zero => exact Subsingleton.elim _ _
      | succ n => exact (found n).symm

theorem vis_continuation_injective {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) {k l : R → Tree E A} (h : vis e k = vis e l) : k = l := by
  funext r
  apply Tree.ext
  intro n
  have eq := congrArg (fun t => t.observe (n + 1)) h
  simp only [vis, Part.some_inj, Visible.vis.injEq, heq_eq_eq, true_and] at eq
  exact congrFun eq r

theorem roll_injective {E : Type u → Type u} {A : Type v} :
    Function.Injective (roll (E := E) (A := A)) := by
  intro x
  induction x using Part.induction_on with
  | hnone =>
    intro y
    induction y using Part.induction_on with
    | hnone => exact fun _ => rfl
    | hsome y =>
      intro eq
      have first := congrArg (fun t => t.observe 1) eq
      simp [roll] at first
  | hsome x =>
    intro y
    induction y using Part.induction_on with
    | hnone =>
      intro eq
      have first := congrArg (fun t => t.observe 1) eq
      simp [roll] at first
    | hsome y =>
      intro eq
      have first := congrArg (fun t => t.observe 1) eq
      have zero : (fun t : Tree E A => t.observe 0) = fun _ => PUnit.unit :=
        funext (fun _ => Subsingleton.elim _ _)
      simp only [roll, Part.map_eq_map, Part.map_some, Part.some_inj, zero] at first
      cases x with
      | ret a =>
        cases y with
        | ret b => cases first; rfl
        | vis e k => cases first
      | vis e k =>
        cases y with
        | ret a => cases first
        | vis e' l =>
          change Visible.vis e (fun _ => PUnit.unit) = Visible.vis e' (fun _ => PUnit.unit) at first
          cases first
          rw [roll_vis, roll_vis] at eq
          rw [vis_continuation_injective e eq]

/-- The observation presentation has exactly the expected partial visible layer. -/
noncomputable def rootEquiv {E : Type u → Type u} {A : Type v} :
    Part (Visible E A (Tree E A)) ≃ Tree E A :=
  Equiv.ofBijective roll ⟨roll_injective, roll_surjective⟩

/-- Expose the first visible constructor, retaining full continuation trees. -/
noncomputable def out {E : Type u → Type u} {A : Type v} (t : Tree E A) :
    Part (Visible E A (Tree E A)) := rootEquiv.symm t

end Silmaril.Elgot.ITree

end

section

/-! ## Normalizing silent recursive returns

The first visible layer of an iterated tree is obtained by a partial computation
that follows recursive returns until it reaches a return value or visible event.
This statement retains full continuation trees and includes infinite silent
chains, whose partial result is undefined.
-/

namespace Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

/-- Continue a partially evaluated iteration body. -/
noncomputable def resume (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A)) : Tree E B :=
  t >>= Sum.elim ret (iter f)

/-- Follow a silent recursive return; stop at a visible root with its fully
resumed continuations. Both state and output are in the original tree universe. -/
noncomputable def normalizeStep (f : A → Tree E (B ⊕ A))
    (t : Tree E (B ⊕ A)) :
    Part (Visible E B (Tree E B) ⊕ Tree E (B ⊕ A)) :=
  out t >>= fun
    | .ret (.inl b) => Part.some (.inl (.ret b))
    | .ret (.inr a) => Part.some (.inr (f a))
    | .vis e next => Part.some (.inl (.vis e (fun r => resume f (next r))))

end Silmaril.Elgot.ITree

end
