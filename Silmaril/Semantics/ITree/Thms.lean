module

public import Silmaril.Semantics.ITree.Defs
import Silmaril.Proofs.Semantics.ITree.Basic
import Silmaril.Proofs.Semantics.ITree.Monad
import Silmaril.Proofs.Semantics.ITree.Iteration
import Silmaril.Proofs.Semantics.ITree.Laws
import Silmaril.Proofs.Semantics.ITree.Codiagonal
import Silmaril.Proofs.Semantics.ITree.Observe
import Silmaril.Proofs.Semantics.ITree.Properties
import Silmaril.Proofs.Semantics.ITree.Normalize

/-!
# ITree

Source: interaction trees, which the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126` compares with trace models after
Concrete Models, §Trace Models.


Theorems about `Silmaril.Semantics.ITree.Defs`. Proofs longer than a few lines live
under `Silmaril.Proofs.Semantics.ITree` and are only pointed at from here.
-/

public section

section

/-! ## Interaction trees as coherent finite observations -/

namespace Silmaril.Elgot.ITree

universe u v w

namespace Visible

theorem map_id {E : Type u → Type u} {A : Type v} {X : Type w} (x : Visible E A X) :
    map id x = x := by
  cases x <;> simp [map, Function.comp_def]

theorem map_comp {E : Type u → Type u} {A : Type v} {X Y Z : Type w}
    (f : X → Y) (g : Y → Z) (x : Visible E A X) :
    map g (map f x) = map (g ∘ f) x :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Visible.map_comp f g x

end Visible

/-- Equality of weak ITrees is exactly equality of every finite observation.
This is the public extensional-equality API; no Tau-counting intensional
equality is exposed. -/
theorem Tree.eq_iff_observe {E : Type u → Type u} {A : Type v}
    {x y : Tree E A} : x = y ↔ ∀ n, x.observe n = y.observe n :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Tree.eq_iff_observe

private theorem part_map_eq_some_iff {A B : Type v} (f : A → B) (x : Part A) (b : B) :
    b ∈ f <$> x ↔ ∃ a, a ∈ x ∧ f a = b := by
  rw [Part.map_eq_map, Part.mem_map_iff]

private theorem part_map_comp {A B C : Type v} (f : A → B) (g : B → C) (x : Part A) :
    g <$> (f <$> x) = (g ∘ f) <$> x := by
  simp only [Part.map_eq_map, Part.map_map]

@[simp] theorem tau_eq {E : Type u → Type u} {A : Type v} (t : Tree E A) : tau t = t :=
  Silmaril.Proofs.Semantics.Elgot.ITree.tau_eq t

end Silmaril.Elgot.ITree

end

section

namespace Silmaril.Elgot.ITree

universe u v

namespace Approx

end Approx

@[simp] theorem observe_pure {E : Type u → Type u} {A : Type v} (a : A) (n : Nat) :
    (pure a : Tree E A).observe n = match n with
      | 0 => PUnit.unit
      | _ + 1 => Part.some (.ret a) := by
  cases n <;> rfl

@[simp] theorem observe_bind {E : Type u → Type u} {A B : Type v}
    (t : Tree E A) (k : A → Tree E B) (n : Nat) :
    (t >>= k).observe n = Approx.bind n (t.observe n) (fun a => (k a).observe n) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.observe_bind t k n

namespace Approx

theorem pure_bind {E : Type u → Type u} {A B : Type v}
    (n : Nat) (a : A) (k : A → Approx E B n) :
    bind n ((ret (E := E) a).observe n) k = k a :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.pure_bind n a k

theorem bind_pure {E : Type u → Type u} {A : Type v}
    (n : Nat) (x : Approx E A n) :
    bind n x (fun a => (ret (E := E) a).observe n) = x :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.bind_pure n x

theorem bind_assoc {E : Type u → Type u} {A B C : Type v}
    (n : Nat) (x : Approx E A n) (f : A → Approx E B n) (g : B → Approx E C n) :
    bind n (bind n x f) g = bind n x (fun a => bind n (f a) g) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.bind_assoc n x f g

end Approx

instance instLawfulMonad (E : Type u → Type u) : LawfulMonad (Tree E) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.instLawfulMonad E

end Silmaril.Elgot.ITree

end

section

namespace Silmaril.Elgot.ITree

open Silmaril.Elgot

universe u v

namespace Approx

end Approx

@[simp] theorem observe_iter {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E (B ⊕ A)) (a : A) (n : Nat) :
    (Silmaril.Elgot.iter f a).observe n =
      Approx.iter n ((f a).observe n) (fun a => (f a).observe n) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.observe_iter f a n

end Silmaril.Elgot.ITree

end

section

namespace Silmaril.Elgot.ITree

open Silmaril.Elgot

universe u v

namespace Approx

theorem iter_fixpoint {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E (B ⊕ A) n) (f : A → Approx E (B ⊕ A) n) :
    iter n x f = bind n x (Sum.elim
      (fun b => (ret (E := E) b).observe n)
      (fun a => iter n (f a) f)) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.iter_fixpoint n x f

/-- Residual-state simulation: effectful return mapping commutes with forgetting
the deepest visible observation. -/
theorem truncate_mapReturn {E : Type u → Type u} {A B C : Type v}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1)) (g : B → Approx E C (n + 1)) :
    truncate n (mapReturn (n + 1) x g) =
      mapReturn n (truncate n x) (fun b => truncate n (g b)) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.truncate_mapReturn n x g

theorem truncate_mapInl {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E B (n + 1)) :
    truncate n (mapInl (A := A) (n + 1) x) = mapInl n (truncate n x) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.truncate_mapInl n x

theorem iter_mapInl {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E B n) (f : A → Approx E (B ⊕ A) n) :
    iter n (mapInl n x) f = x :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.iter_mapInl n x f

theorem iter_naturality {E : Type u → Type u} {A B C : Type v}
    (n : Nat) (x : Approx E (B ⊕ A) n) (f : A → Approx E (B ⊕ A) n)
    (g : B → Approx E C n) :
    bind n (iter n x f) g =
      iter n (mapReturn (A := A) n x g) (fun a => mapReturn (A := A) n (f a) g) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.iter_naturality n x f g

theorem truncate_mapState {E : Type u → Type u} {A B C : Type v}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1)) (h : A → C) :
    truncate n (mapState (n + 1) x h) = mapState n (truncate n x) h :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.truncate_mapState n x h

theorem iter_uniformity {E : Type u → Type u} {A B C : Type v}
    (n : Nat) (x : Approx E (B ⊕ A) n)
    (f : A → Approx E (B ⊕ A) n) (g : C → Approx E (B ⊕ C) n)
    (h : A → C) (comm : ∀ a, mapState n (f a) h = g (h a)) :
    iter n x f = iter n (mapState n x h) g :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.iter_uniformity n x f g h comm

theorem truncate_flattenApprox {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E ((B ⊕ A) ⊕ A) (n + 1)) :
    truncate n (flattenApprox (n + 1) x) = flattenApprox n (truncate n x) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.truncate_flattenApprox n x

end Approx

/-- The defining fixpoint equation for weak interaction-tree iteration. -/
theorem iterate_fixpoint {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E (B ⊕ A)) :
    Silmaril.Elgot.iter f = fun a => f a >>= Sum.elim pure (Silmaril.Elgot.iter f) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.iterate_fixpoint f

theorem iterate_naturality {E : Type u → Type u} {A B C : Type v}
    (f : A → Tree E (B ⊕ A)) (g : B → Tree E C) :
    ((Silmaril.Elgot.iter f) >=> g) =
      Silmaril.Elgot.iter (Silmaril.Elgot.mapReturn f g) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.iterate_naturality f g

theorem iterate_uniformity {E : Type u → Type u} {A B C : Type v}
    (f : A → Tree E (B ⊕ A)) (g : C → Tree E (B ⊕ C)) (h : A → C)
    (comm : (f >=> (liftPure (Sum.map id h))) = ((liftPure h) >=> g)) :
    Silmaril.Elgot.iter f = ((liftPure h) >=> (Silmaril.Elgot.iter g)) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.iterate_uniformity f g h comm

end Silmaril.Elgot.ITree

end

section

/-! ## Codiagonal -/

namespace Silmaril.Elgot.ITree

open Silmaril.Elgot

universe u v

namespace Approx

theorem doubleStep_eq_mapReturn {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E ((B ⊕ A) ⊕ A) (n + 1)) :
    doubleStep n f = Silmaril.Elgot.mapReturn (iterStep n f) (doublePost n f) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.doubleStep_eq_mapReturn n f

/-- The inner residual machine simulates the body of the outer iteration. -/
theorem doubleStep_inner_square {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E ((B ⊕ A) ⊕ A) (n + 1)) :
    (Silmaril.Elgot.iter (doubleStep n f) >=>
      liftPure (Sum.map id (fun x => iter (n + 1) x f))) =
    (liftPure (fun x => iter (n + 1) x f) >=>
      iterStep n (fun a => iter (n + 1) (f a) f)) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.doubleStep_inner_square n f

/-- Flattening residual states respects the one-level iteration machine. -/
theorem doubleStep_flatten_square {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E ((B ⊕ A) ⊕ A) (n + 1))
    (ih : ∀ x, iter n (iter n x (fun a => truncate n (f a)))
        (fun a => iter n (truncate n (f a)) (fun a => truncate n (f a))) =
      iter n (flattenApprox n x) (fun a => flattenApprox n (truncate n (f a)))) :
    (Silmaril.Elgot.flattenBody (doubleStep n f) >=>
      liftPure (Sum.map id (flattenApprox (E := E) (A := A) (B := B) (n + 1)))) =
    (liftPure (flattenApprox (E := E) (A := A) (B := B) (n + 1)) >=>
      iterStep n (fun a => flattenApprox (n + 1) (f a))) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.doubleStep_flatten_square n f ih

theorem iter_codiagonal {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E ((B ⊕ A) ⊕ A) n)
    (f : A → Approx E ((B ⊕ A) ⊕ A) n) :
    iter n (iter n x f) (fun a => iter n (f a) f) =
      iter n (flattenApprox n x) (fun a => flattenApprox n (f a)) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Approx.iter_codiagonal n x f

end Approx

@[simp] theorem observe_flattenBody {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E ((B ⊕ A) ⊕ A)) (a : A) (n : Nat) :
    (Silmaril.Elgot.flattenBody f a).observe n =
      Approx.flattenApprox n ((f a).observe n) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.observe_flattenBody f a n

/-- Nested weak iteration agrees with merging its two recursive summands. -/
theorem iterate_codiagonal {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E ((B ⊕ A) ⊕ A)) :
    Silmaril.Elgot.iter (Silmaril.Elgot.iter f) =
      Silmaril.Elgot.iter (Silmaril.Elgot.flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.iterate_codiagonal f

noncomputable instance instLawfulElgotMonad (E : Type u → Type u) :
    LawfulElgotMonad (Tree E) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.instLawfulElgotMonad E

end Silmaril.Elgot.ITree

end

section

/-! ## Observe -/

namespace Silmaril.Elgot.ITree

universe u v w

namespace Visible

end Visible

@[simp] theorem roll_out {E : Type u → Type u} {A : Type v} (t : Tree E A) :
    roll (out t) = t :=
  Silmaril.Proofs.Semantics.Elgot.ITree.roll_out t

@[simp] theorem out_roll {E : Type u → Type u} {A : Type v}
    (x : Part (Visible E A (Tree E A))) : out (roll x) = x :=
  Silmaril.Proofs.Semantics.Elgot.ITree.out_roll x

@[simp] theorem out_diverge {E : Type u → Type u} {A : Type v} :
    out (diverge : Tree E A) = Part.none :=
  Silmaril.Proofs.Semantics.Elgot.ITree.out_diverge

@[simp] theorem out_ret {E : Type u → Type u} {A : Type v} (a : A) :
    out (ret (E := E) a) = Part.some (.ret a) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.out_ret a

@[simp] theorem out_vis {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) (k : R → Tree E A) : out (vis e k) = Part.some (.vis e k) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.out_vis e k

theorem out_injective {E : Type u → Type u} {A : Type v} :
    Function.Injective (out (E := E) (A := A)) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.out_injective

/-- The destructor reproduces each finite observation by truncating its children. -/
theorem observe_succ_eq_out {E : Type u → Type u} {A : Type v} (t : Tree E A) (n : Nat) :
    t.observe (n + 1) = Visible.map (fun child => child.observe n) <$> out t :=
  Silmaril.Proofs.Semantics.Elgot.ITree.observe_succ_eq_out t n

@[simp] theorem out_eq_none_iff {E : Type u → Type u} {A : Type v} (t : Tree E A) :
    out t = Part.none ↔ t = diverge :=
  Silmaril.Proofs.Semantics.Elgot.ITree.out_eq_none_iff t

@[simp] theorem ret_inj {E : Type u → Type u} {A : Type v} {a b : A} :
    ret (E := E) a = ret b ↔ a = b :=
  Silmaril.Proofs.Semantics.Elgot.ITree.ret_inj

@[simp] theorem vis_inj {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) (k l : R → Tree E A) : vis e k = vis e l ↔ k = l :=
  Silmaril.Proofs.Semantics.Elgot.ITree.vis_inj e k l

@[simp] theorem ret_ne_diverge {E : Type u → Type u} {A : Type v} (a : A) :
    ret (E := E) a ≠ diverge :=
  Silmaril.Proofs.Semantics.Elgot.ITree.ret_ne_diverge a

@[simp] theorem vis_ne_diverge {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) (k : R → Tree E A) : vis e k ≠ diverge :=
  Silmaril.Proofs.Semantics.Elgot.ITree.vis_ne_diverge e k

@[simp] theorem ret_ne_vis {E : Type u → Type u} {A : Type v} {R : Type u}
    (a : A) (e : E R) (k : R → Tree E A) : ret a ≠ vis e k :=
  Silmaril.Proofs.Semantics.Elgot.ITree.ret_ne_vis a e k

/-- Exhaustive decomposition is a theorem about coherence, not an extra axiom. -/
theorem cases_visible {E : Type u → Type u} {A : Type v} (t : Tree E A) :
    t = diverge ∨ (∃ a, t = ret a) ∨ ∃ (R : Type u) (e : E R) (k : R → Tree E A), t = vis e k :=
  Silmaril.Proofs.Semantics.Elgot.ITree.cases_visible t

end Silmaril.Elgot.ITree

end

section

/-! ## Properties -/

namespace Silmaril.Elgot.ITree

universe u v

@[simp] theorem diverge_bind {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E B) : (diverge >>= f) = diverge :=
  Silmaril.Proofs.Semantics.Elgot.ITree.diverge_bind f

@[simp] theorem vis_bind {E : Type u → Type u} {A B : Type v} {R : Type u}
    (e : E R) (k : R → Tree E A) (f : A → Tree E B) :
    (vis e k >>= f) = vis e (fun r => k r >>= f) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.vis_bind e k f

/-- A body that returns on every path needs no recursive calls. -/
@[simp] theorem iterate_done {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E B) :
    Silmaril.Elgot.iter (fun a => f a >>= pure ∘ Sum.inl) = f :=
  Silmaril.Proofs.Semantics.Elgot.ITree.iterate_done f

/-- An endless sequence of silent recursive calls has no visible observation. -/
@[simp] theorem iterate_forever {E : Type u → Type u} {A B : Type v} (a : A) :
    Silmaril.Elgot.iter (fun a : A => (pure (.inr a) : Tree E (B ⊕ A))) a = diverge :=
  Silmaril.Proofs.Semantics.Elgot.ITree.iterate_forever a

/-- A pure state machine with no return edge is silently divergent, even when
its state changes forever. -/
theorem iterate_pure_loop {E : Type u → Type u} {A B : Type v}
    (next : A → A) (a : A) :
    Silmaril.Elgot.iter (fun a => (pure (.inr (next a)) : Tree E (B ⊕ A))) a = diverge :=
  Silmaril.Proofs.Semantics.Elgot.ITree.iterate_pure_loop next a

end Silmaril.Elgot.ITree

end

section

/-! ## Normalize -/

namespace Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

@[simp] theorem resume_body (f : A → Tree E (B ⊕ A)) (a : A) :
    resume f (f a) = iter f a :=
  Silmaril.Proofs.Semantics.Elgot.ITree.resume_body f a

theorem observe_resume (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A)) (n : Nat) :
    (resume f t).observe n =
      Approx.iter n (t.observe n) (fun a => (f a).observe n) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.observe_resume f t n

/-- Finite observations of the normalized root agree with those of iteration. -/
theorem observe_normalize (f : A → Tree E (B ⊕ A))
    (t : Tree E (B ⊕ A)) (n : Nat) :
    Visible.map (fun child : Tree E B => child.observe n) <$>
        iter (normalizeStep f) t = (resume f t).observe (n + 1) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.observe_normalize f t n

/-- Partial iteration of silent returns computes exactly the first full visible
layer, including undefinedness of an infinite silent computation. -/
theorem out_resume (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A)) :
    out (resume f t) = iter (normalizeStep f) t :=
  Silmaril.Proofs.Semantics.Elgot.ITree.out_resume f t

theorem out_iterate (f : A → Tree E (B ⊕ A)) (a : A) :
    out (iter f a) = iter (normalizeStep f) (f a) := by
  rw [← resume_body f a, out_resume]

end Silmaril.Elgot.ITree

end
