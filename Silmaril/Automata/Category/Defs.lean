module

public import Silmaril.Automata.Spec.Defs
public import Cslib.Foundations.Semantics.LTS.LTSCat.Basic
public import Mathlib.CategoryTheory.InducedCategory

@[expose] public section

/-!
# Categories of finite machines

```
            toSpec / Typed (equivalence)
   TMach  ⟵──────────────────────────  JMach        (typed machines ≃ valid JSON machines)
    ↑ │ ╲
forget│  ╲ toLTSCat
    │ ↓   ↘
  Marked   LTSCat (CSLib)  ──→  Graph               (forget labels)
```

* `TMach`: typed finite machines (`FinNamed` states and labels, a `DMachine`) with **strict
  homomorphisms**: maps of states and labels that commute with the partial step function
  (`(M.step s l).map f = N.step (f s) (g l)`): they preserve every step and reflect
  definedness, so rejections map to rejections.
* `JMach`: valid deterministic JSON machines (`Spec` with `wf` and `Deterministic`). A morphism
  of JSON machines is a pair of maps of *declared names* that commutes with the spec's step
  function (a strict homomorphism of the machines the specs denote, `Spec.Typed`): it is
  the same notion as for typed machines, read on names. `JMach` is the category induced by
  `JMach.typed` (homs of `JMach` are homs of `TMach`), so `JMach.typedFunctor : JMach ⥤ TMach` is
  fully faithful by construction;
  `Thms` proves it essentially surjective (every typed machine is isomorphic to the typed
  machine of its spec), hence an **equivalence of categories**.
* `JMarked`: valid deterministic JSON machines with layers, whose morphisms are those of the
  marked machines they denote; `JMarked.typedFunctor : JMarked ⥤ MarkedMach` is again an
  **equivalence** (`Thms`), and `JMarked.forget`, `MarkedMach.forget` forget the layers.
* `MarkedMach`: typed machines with marks (`Marks`), morphisms preserving each mark;
  `MarkedMach.forget : MarkedMach ⥤ TMach` forgets the layer.
* `toLTSCat : TMach ⥤ Cslib.LTSCat`: into CSLib's category of LTSs (Winskel–Nielsen
  morphisms with partial label maps); a strict homomorphism is an LTS morphism with a total
  label map.
* `Graph`: unlabelled transition systems with edge-preserving maps, and
  `LTSCat.unlabel : Cslib.LTSCat ⥤ Graph` (forget labels; idle steps become self-loops).
-/

namespace Silmaril.Automata

open CategoryTheory

/-- A typed finite machine (bundled). -/
structure TMach where
  S : Type
  L : Type
  [nS : FinNamed S]
  [nL : FinNamed L]
  M : DMachine S L

attribute [instance] TMach.nS TMach.nL

/-- A strict homomorphism of typed machines. -/
@[ext] structure TMach.Hom (A B : TMach) where
  f : A.S → B.S
  g : A.L → B.L
  comm : ∀ s l, (A.M.step s l).map f = B.M.step (f s) (g l)

instance : Category TMach where
  Hom := TMach.Hom
  id A := ⟨id, id, fun s l => by simp⟩
  comp h k := ⟨k.f ∘ h.f, k.g ∘ h.g, fun s l => by
    rw [← Option.map_map, h.comm, k.comm]; rfl⟩

@[ext] theorem TMach.hom_ext {A B : TMach} {h k : A ⟶ B} (hf : h.f = k.f) (hg : h.g = k.g) :
    h = k := TMach.Hom.ext hf hg

/-- A valid deterministic JSON machine. -/
structure JMach where
  sp : Spec
  wf : sp.wf = true
  det : sp.Deterministic

/-- The declared states of a well-formed spec are `FinNamed` by their names. -/
@[instance_reducible] def Spec.stateNamed (sp : Spec) (h : sp.states.Nodup) : FinNamed sp.State where
  elems := sp.states.attach
  name := Subtype.val
  complete s := List.mem_attach _ s
  nodup := by rw [List.attach_map_subtype_val]; exact h

/-- The declared labels of a well-formed spec are `FinNamed` by their names. -/
@[instance_reducible] def Spec.labelNamed (sp : Spec) (h : sp.labels.Nodup) : FinNamed sp.Label where
  elems := sp.labels.attach
  name := Subtype.val
  complete s := List.mem_attach _ s
  nodup := by rw [List.attach_map_subtype_val]; exact h

theorem Spec.wf_states {sp : Spec} (h : sp.wf = true) : sp.states.Nodup := by
  simp only [Spec.wf, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem Spec.wf_labels {sp : Spec} (h : sp.wf = true) : sp.labels.Nodup := by
  simp only [Spec.wf, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2

/-- The typed machine a JSON machine denotes. -/
def JMach.typed (A : JMach) : TMach :=
  @TMach.mk A.sp.State A.sp.Label (A.sp.stateNamed (Spec.wf_states A.wf))
    (A.sp.labelNamed (Spec.wf_labels A.wf)) A.sp.Typed

/-- JSON machines with strict homomorphisms of the machines they denote. -/
instance : Category JMach where
  Hom A B := A.typed ⟶ B.typed
  id A := 𝟙 A.typed
  comp h k := h ≫ k
  id_comp h := Category.id_comp (obj := TMach) h
  comp_id h := Category.comp_id (obj := TMach) h
  assoc h k m := Category.assoc (obj := TMach) h k m

/-- The fully faithful functor from JSON machines to typed machines. -/
def JMach.typedFunctor : JMach ⥤ TMach where
  obj := JMach.typed
  map h := h

/-! ## Marked machines -/

/-- A typed machine with marks. -/
structure MarkedMach where
  base : TMach
  marks : Marks base.S

/-- A homomorphism of marked machines: a strict homomorphism preserving every mark. -/
@[ext] structure MarkedMach.Hom (A B : MarkedMach) where
  h : A.base ⟶ B.base
  initial : ∀ s, A.marks.initial s = true → B.marks.initial (h.f s) = true
  accepting : ∀ s, A.marks.accepting s = true → B.marks.accepting (h.f s) = true
  rejecting : ∀ s, A.marks.rejecting s = true → B.marks.rejecting (h.f s) = true
  error : ∀ s, A.marks.error s = true → B.marks.error (h.f s) = true

instance : Category MarkedMach where
  Hom := MarkedMach.Hom
  id A := ⟨𝟙 A.base, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
  comp h k := ⟨h.h ≫ k.h, fun s hs => k.initial _ (h.initial s hs),
    fun s hs => k.accepting _ (h.accepting s hs), fun s hs => k.rejecting _ (h.rejecting s hs),
    fun s hs => k.error _ (h.error s hs)⟩

/-- Forget the marking layer. -/
def MarkedMach.forget : MarkedMach ⥤ TMach where
  obj A := A.base
  map h := h.h

/-! ## Marked JSON machines -/

/-- A valid deterministic JSON machine with layers on its declared states. -/
structure JMarked where
  base : JMach
  layers : Layers
  wf : layers.wf base.sp.states = true

/-- The marks the layers of a JSON machine denote. -/
def JMarked.marks (A : JMarked) : Marks A.base.typed.S where
  initial s := decide (s.1 ∈ A.layers.initial)
  accepting s := decide (s.1 ∈ A.layers.accepting)
  rejecting s := decide (s.1 ∈ A.layers.rejecting)
  error s := decide (s.1 ∈ A.layers.error)

/-- The marked typed machine a marked JSON machine denotes. -/
def JMarked.typed (A : JMarked) : MarkedMach := ⟨A.base.typed, A.marks⟩

/-- Marked JSON machines with the homomorphisms of the marked machines they denote. -/
instance : Category JMarked where
  Hom A B := A.typed ⟶ B.typed
  id A := 𝟙 A.typed
  comp h k := h ≫ k
  id_comp h := Category.id_comp (obj := MarkedMach) h
  comp_id h := Category.comp_id (obj := MarkedMach) h
  assoc h k m := Category.assoc (obj := MarkedMach) h k m

/-- The fully faithful functor from marked JSON machines to marked typed machines. -/
def JMarked.typedFunctor : JMarked ⥤ MarkedMach where
  obj := JMarked.typed
  map h := h

/-- Forget the layers of a JSON machine. -/
def JMarked.forget : JMarked ⥤ JMach where
  obj A := A.base
  map h := h.h

/-! ## Into CSLib's LTS category, and unlabelled graphs -/

/-- A typed machine as an object of CSLib's `LTSCat`. -/
def TMach.toLTSObj (A : TMach) : Cslib.LTSCat := ⟨A.S, A.L, A.M.toLTS⟩

/-- Typed machines into CSLib's category of LTSs. -/
def toLTSCat : TMach ⥤ Cslib.LTSCat where
  obj A := A.toLTSObj
  map {A B} h := {
    stateMap := h.f
    labelMap := fun l => some (h.g l)
    labelMap_tr := fun s s' l (hs : A.M.step s l = some s') => by
      have := h.comm s l
      rw [hs] at this
      exact this.symm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An unlabelled transition system. -/
structure Graph where
  V : Type
  adj : V → V → Prop

/-- Edge-preserving maps. -/
@[ext] structure Graph.Hom (A B : Graph) where
  f : A.V → B.V
  map_adj : ∀ u v, A.adj u v → B.adj (f u) (f v)

instance : Category Graph where
  Hom := Graph.Hom
  id A := ⟨id, fun _ _ h => h⟩
  comp h k := ⟨k.f ∘ h.f, fun u v e => k.map_adj _ _ (h.map_adj u v e)⟩

/-- Forget labels: `u → v` when some step (or idle step) goes from `u` to `v`. -/
def unlabel : Cslib.LTSCat ⥤ Graph where
  obj A := ⟨A.State, fun u v => u = v ∨ A.lts.UnlabelledTr u v⟩
  map {A B} h := ⟨h.stateMap, fun u v e => by
    rcases e with rfl | ⟨μ, hμ⟩
    · exact Or.inl rfl
    · have := h.labelMap_tr u v μ hμ
      cases hl : h.labelMap μ with
      | none => rw [hl] at this; exact Or.inl this
      | some ν => rw [hl] at this; exact Or.inr ⟨ν, this⟩⟩

end Silmaril.Automata
