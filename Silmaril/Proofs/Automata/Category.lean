module

public import Silmaril.Automata.Category.Defs
public import Silmaril.Automata.Spec.Thms
public import Mathlib.CategoryTheory.Equivalence

/-!
# Categories of finite machines: proofs

`JMach.typedFunctor : JMach ⥤ TMach` is an equivalence: it is fully faithful because JSON
machine morphisms are strict homomorphisms of the denoted machines, and essentially surjective
because every typed machine is isomorphic, through names, to the machine its spec denotes.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open CategoryTheory Silmaril.Automata

/-- The element of a name that is known to occur. -/
def ofNameMem {α : Type} [FinNamed α] (n : String) (h : n ∈ FinNamed.names α) : α :=
  (FinNamed.ofName? n).get (by
    obtain ⟨a, rfl⟩ := (FinNamed.mem_names_iff n).mp h
    rw [FinNamed.ofName?_name]; rfl)

theorem ofNameMem_name {α : Type} [FinNamed α] (a : α) (h) : ofNameMem (FinNamed.name a) h = a := by
  unfold ofNameMem
  simp [FinNamed.ofName?_name]

theorem name_ofNameMem {α : Type} [FinNamed α] (n : String) (h : n ∈ FinNamed.names α) :
    FinNamed.name (ofNameMem n h) = n := by
  obtain ⟨a, rfl⟩ := (FinNamed.mem_names_iff n).mp h
  rw [ofNameMem_name]

/-- The JSON machine of a typed machine. -/
def ofTyped (A : TMach) : JMach := ⟨A.M.toSpec, toSpec_wf A.M, toSpec_deterministic A.M⟩

/-- A typed machine's state, as a declared name of its spec. -/
def nmS (A : TMach) (s : A.S) : (ofTyped A).sp.State := ⟨FinNamed.name s, (FinNamed.mem_names_iff _).mpr ⟨s, rfl⟩⟩

/-- A typed machine's label, as a declared name of its spec. -/
def nmL (A : TMach) (l : A.L) : (ofTyped A).sp.Label := ⟨FinNamed.name l, (FinNamed.mem_names_iff _).mpr ⟨l, rfl⟩⟩

theorem typed_ofTyped_step (A : TMach) (s : A.S) (l : A.L) :
    (ofTyped A).sp.Typed.step (nmS A s) (nmL A l) = (A.M.step s l).map (nmS A) := by
  have hd := toSpec_deterministic A.M
  cases h : A.M.step s l with
  | some s' =>
    rw [Option.map_some]
    exact (Spec.typed_step_iff (ofTyped A).sp hd _ _ _).mpr ((toSpec_step_iff A.M s l s').mpr h)
  | none =>
    rw [Option.map_none]
    cases h' : (ofTyped A).sp.Typed.step (nmS A s) (nmL A l) with
    | none => rfl
    | some x =>
      exfalso
      have hs := (Spec.typed_step_iff (ofTyped A).sp hd _ _ _).mp h'
      obtain ⟨a, ha⟩ := (FinNamed.mem_names_iff x.1).mp x.2
      have : A.M.step s l = some a := by
        rw [← toSpec_step_iff, ha]; exact hs
      rw [h] at this; cases this

/-- The isomorphism between a typed machine and the machine its spec denotes. -/
def isoTyped (A : TMach) : (ofTyped A).typed ≅ A where
  hom := {
    f := fun n => ofNameMem n.1 n.2
    g := fun k => ofNameMem k.1 k.2
    comm := fun n k => by
      obtain ⟨a, ha⟩ := (FinNamed.mem_names_iff n.1).mp n.2
      obtain ⟨b, hb⟩ := (FinNamed.mem_names_iff k.1).mp k.2
      have en : n = nmS A a := Subtype.ext ha.symm
      have ek : k = nmL A b := Subtype.ext hb.symm
      subst en ek
      show Option.map (fun n : (ofTyped A).sp.State => ofNameMem n.1 n.2)
          ((ofTyped A).sp.Typed.step (nmS A a) (nmL A b)) =
        A.M.step (ofNameMem (nmS A a).1 (nmS A a).2) (ofNameMem (nmL A b).1 (nmL A b).2)
      rw [typed_ofTyped_step]
      have e1 : ofNameMem (nmS A a).1 (nmS A a).2 = a := ofNameMem_name a _
      have e2 : ofNameMem (nmL A b).1 (nmL A b).2 = b := ofNameMem_name b _
      rw [e1, e2]
      cases A.M.step a b with
      | none => rfl
      | some c => simp only [Option.map_some]; exact congrArg some (ofNameMem_name c _) }
  inv := {
    f := nmS A
    g := nmL A
    comm := fun s l => (typed_ofTyped_step A s l).symm }
  hom_inv_id := TMach.hom_ext (funext fun n => Subtype.ext (name_ofNameMem n.1 n.2))
    (funext fun k => Subtype.ext (name_ofNameMem k.1 k.2))
  inv_hom_id := TMach.hom_ext (funext fun s => ofNameMem_name s (nmS A s).2)
    (funext fun l => ofNameMem_name l (nmL A l).2)

instance typedFunctor_full : JMach.typedFunctor.Full := ⟨fun h => ⟨h, rfl⟩⟩

instance typedFunctor_faithful : JMach.typedFunctor.Faithful := ⟨fun h => h⟩

instance typedFunctor_essSurj : JMach.typedFunctor.EssSurj :=
  ⟨fun A => ⟨ofTyped A, ⟨isoTyped A⟩⟩⟩

instance typedFunctor_isEquivalence : JMach.typedFunctor.IsEquivalence where

end Silmaril.Proofs.Automata
