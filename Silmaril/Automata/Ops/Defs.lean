module

public import Silmaril.Automata.Category.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan

@[expose] public section

/-!
# Products and coproducts of machines

**The category.** `RelMach`: relational machines (a CSLib LTS with its state and label types),
whose morphisms map states and labels and **preserve** transitions (`Tr s l s' → Tr (f s) (g l)
(f s')`). These are the "lax" homomorphisms of labelled transition systems with total label
maps; CSLib's `LTSCat` allows partial label maps, and the typed machines of `TMach` use
**strict** homomorphisms (commuting with the partial step function, so rejections are reflected).

**Why not `TMach`.** With strict homomorphisms the obvious product and coproduct fail: a
projection out of the componentwise product must reflect rejections, but the product rejects a
label pair as soon as one side does, while the other side may accept. So the universal
constructions are stated in `RelMach`, where they exist, and `TMach.toRelMach` is a functor.

**Product** (`prod`): states `S × T`, labels `L × K`, a transition exactly when both components
step (`(s,t) —(l,k)→ (s',t')` iff `s —l→ s'` and `t —k→ t'`).
**Coproduct** (`coprod`): states `S ⊕ T`, labels `L ⊕ K`, the transitions of each side, none
between sides. `Thms` proves the universal properties (`prodIsLimit`, `coprodIsColimit`).

**Synchronous product.** `DMachine.prod` / `NMachine.prod` (same label type, both machines take
the same label; it recognizes the intersection of languages) is the categorical product
restricted along the diagonal labels `l ↦ (l, l)` (`Thms`: `sync_eq_prod_diag`), not the product
itself.
-/

namespace Silmaril.Automata

open CategoryTheory

/-- A relational machine (bundled CSLib LTS). -/
structure RelMach where
  S : Type
  L : Type
  tr : Cslib.LTS S L

/-- A transition-preserving homomorphism. -/
@[ext] structure RelMach.Hom (A B : RelMach) where
  f : A.S → B.S
  g : A.L → B.L
  map_tr : ∀ s l s', A.tr.Tr s l s' → B.tr.Tr (f s) (g l) (f s')

instance : Category RelMach where
  Hom := RelMach.Hom
  id A := ⟨id, id, fun _ _ _ h => h⟩
  comp h k := ⟨k.f ∘ h.f, k.g ∘ h.g, fun s l s' t => k.map_tr _ _ _ (h.map_tr s l s' t)⟩

@[ext] theorem RelMach.hom_ext {A B : RelMach} {h k : A ⟶ B} (hf : h.f = k.f) (hg : h.g = k.g) :
    h = k := RelMach.Hom.ext hf hg

namespace RelMach

/-- The product: both components step. -/
def prod (A B : RelMach) : RelMach :=
  ⟨A.S × B.S, A.L × B.L, ⟨fun p l q => A.tr.Tr p.1 l.1 q.1 ∧ B.tr.Tr p.2 l.2 q.2⟩⟩

def fst (A B : RelMach) : prod A B ⟶ A := ⟨Prod.fst, Prod.fst, fun _ _ _ h => h.1⟩
def snd (A B : RelMach) : prod A B ⟶ B := ⟨Prod.snd, Prod.snd, fun _ _ _ h => h.2⟩

/-- Pairing. -/
def lift {X A B : RelMach} (h : X ⟶ A) (k : X ⟶ B) : X ⟶ prod A B :=
  ⟨fun x => (h.f x, k.f x), fun l => (h.g l, k.g l), fun _ _ _ t => ⟨h.map_tr _ _ _ t, k.map_tr _ _ _ t⟩⟩

/-- The coproduct: the transitions of each side, none between sides. -/
def coprod (A B : RelMach) : RelMach :=
  ⟨A.S ⊕ B.S, A.L ⊕ B.L, ⟨fun p l q => match p, l, q with
    | .inl s, .inl l, .inl s' => A.tr.Tr s l s'
    | .inr t, .inr k, .inr t' => B.tr.Tr t k t'
    | _, _, _ => False⟩⟩

def inl (A B : RelMach) : A ⟶ coprod A B := ⟨Sum.inl, Sum.inl, fun _ _ _ h => h⟩
def inr (A B : RelMach) : B ⟶ coprod A B := ⟨Sum.inr, Sum.inr, fun _ _ _ h => h⟩

/-- Copairing. -/
def desc {A B X : RelMach} (h : A ⟶ X) (k : B ⟶ X) : coprod A B ⟶ X where
  f := Sum.elim h.f k.f
  g := Sum.elim h.g k.g
  map_tr p l q t := by
    match p, l, q, t with
    | .inl s, .inl l, .inl s', t => exact h.map_tr s l s' t
    | .inr s, .inr l, .inr s', t => exact k.map_tr s l s' t

end RelMach

/-- A typed machine as a relational machine. -/
def TMach.toRelMachObj (A : TMach) : RelMach := ⟨A.S, A.L, A.M.toLTS⟩

/-- Strict homomorphisms preserve transitions: typed machines into relational machines. -/
def TMach.toRelMach : TMach ⥤ RelMach where
  obj := TMach.toRelMachObj
  map {A B} h := ⟨h.f, h.g, fun s l s' (t : A.M.step s l = some s') => by
    have := h.comm s l
    rw [t] at this
    exact this.symm⟩

end Silmaril.Automata
