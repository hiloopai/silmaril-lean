module

public import Silmaril.Automata.Named.Defs
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Nodup
import Silmaril.Proofs.Automata.Named

@[expose] public section

/-!
# Finite named types: theorems and the generic instances

PROVED (standard axioms; proofs in `Silmaril/Proofs/Automata/Named.lean`):

* `pairName_inj`: pair names `(a,b)` (components with `,` and `\` escaped) are injective, so
  the first unescaped comma is the separator;
* `someName_inj`, `inlName_inj`, `inrName_inj`, `none_ne_someName`, `inlName_ne_inrName`.

So `Option α`, `α ⊕ β` and `α × β` are `FinNamed` whenever their components are, with
distinctness proved once for all component types (not checked per instance).
-/

namespace Silmaril.Automata

theorem pairName_inj {a b a' b' : String} (h : pairName a b = pairName a' b') : a = a' ∧ b = b' :=
  Silmaril.Proofs.Automata.pairName_inj h

theorem someName_inj {a b : String} (h : someName a = someName b) : a = b :=
  Silmaril.Proofs.Automata.someName_inj h

theorem inlName_inj {a b : String} (h : inlName a = inlName b) : a = b :=
  Silmaril.Proofs.Automata.inlName_inj h

theorem inrName_inj {a b : String} (h : inrName a = inrName b) : a = b :=
  Silmaril.Proofs.Automata.inrName_inj h

theorem none_ne_someName (a : String) : "none" ≠ someName a :=
  Silmaril.Proofs.Automata.none_ne_someName a

theorem inlName_ne_inrName (a b : String) : inlName a ≠ inrName b :=
  Silmaril.Proofs.Automata.inlName_ne_inrName a b

variable {α β : Type} [FinNamed α] [FinNamed β]

instance : FinNamed (Option α) where
  elems := none :: (FinNamed.elems (α := α)).map some
  name | none => "none" | some a => someName (FinNamed.name a)
  complete o := by cases o <;> simp [FinNamed.complete]
  nodup := by
    simp only [List.map_cons, List.map_map, List.nodup_cons, List.mem_map, Function.comp_apply,
      not_exists, not_and]
    refine ⟨fun a _ h => none_ne_someName _ h.symm, ?_⟩
    exact Silmaril.Proofs.Automata.elems_nodup.map
      (fun a b h => Silmaril.Proofs.Automata.name_injective (someName_inj h))

instance : FinNamed (α ⊕ β) where
  elems := (FinNamed.elems (α := α)).map Sum.inl ++ (FinNamed.elems (α := β)).map Sum.inr
  name | .inl a => inlName (FinNamed.name a) | .inr b => inrName (FinNamed.name b)
  complete x := by cases x <;> simp [FinNamed.complete]
  nodup := by
    simp only [List.map_append, List.map_map]
    refine List.Nodup.append ?_ ?_ ?_
    · exact Silmaril.Proofs.Automata.elems_nodup.map
        (fun a b h => Silmaril.Proofs.Automata.name_injective (inlName_inj h))
    · exact Silmaril.Proofs.Automata.elems_nodup.map
        (fun a b h => Silmaril.Proofs.Automata.name_injective (inrName_inj h))
    · simp only [List.disjoint_left, List.mem_map, Function.comp_apply]
      rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩
      exact inlName_ne_inrName _ _ h.symm

instance : FinNamed (α × β) where
  elems := (FinNamed.elems (α := α)).product (FinNamed.elems (α := β))
  name p := pairName (FinNamed.name p.1) (FinNamed.name p.2)
  complete p := List.mem_product.mpr ⟨FinNamed.complete _, FinNamed.complete _⟩
  nodup := by
    refine (Silmaril.Proofs.Automata.elems_nodup.product
      Silmaril.Proofs.Automata.elems_nodup).map ?_
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h1, h2⟩ := pairName_inj h
    exact Prod.ext (Silmaril.Proofs.Automata.name_injective h1)
      (Silmaril.Proofs.Automata.name_injective h2)

/-- `Option Bool × (Bool ⊕ Unit)` has 3 · 3 = 9 elements, all distinctly named (by the
instances above); e.g. `(some true, inr ())` is named `(some(true),inr(()))`. -/
example : (FinNamed.elems (α := Option Bool × (Bool ⊕ Unit))).length = 9 := by decide

end Silmaril.Automata
