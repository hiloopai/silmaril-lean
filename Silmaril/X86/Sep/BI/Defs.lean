module

public import Silmaril.X86.Sep.Defs
public import Silmaril.X86.Sep.Extra.Defs

/-!
# BI operations and laws, iris-lean shaped, over a separation algebra

A standalone copy of the *shape* of iris-lean's bunched-implications interface, so that
`SProp` can later be handed to iris-lean (once a dependency on it is approved) with a
short adapter, and so that MoSeL-style reasoning has a fixed list of laws to target today.
No iris-lean code is imported or copied: the field names and statements follow
`Iris/Iris/BI/BIBase.lean` (`BIBase`) and `Iris/Iris/BI/BI.lean` (`BI`) of
`leanprover-community/iris-lean` at `fb21a8af` (Apache-2.0), minus the OFE fields
(`*_ne`, `COFE`): every carrier here is discrete.

* `Ops PROP`: the twelve `BIBase` operations, as a structure (not a class).
* `Ops.BiEntails`, `Ops.forall`, `Ops.exists`, `Ops.True`, `Ops.False`: the derived forms
  the `BI` laws mention (`⊣⊢`, `∀ x, …`, `∃ x, …`, `True`, `False`).
* `Laws O`: the non-OFE fields of iris-lean's `BI`, field for field and in order.
* `SepAlg α`: a separation algebra (a partial commutative monoid presented by a disjointness
  relation and a total union that is only meaningful on disjoint pairs). Instances: partial
  maps `ι → Option β` (hence `Frag`), and products (for instance a fragment paired with an XMM file).
* `ops α`: the classical, non-affine BI of predicates `α → Prop` over a separation algebra.
  `persistently P` holds everywhere iff `P` holds of the unit; `later` is the identity.
* `sprop : Ops SProp`: the instance for `Sep`'s assertions, built from `Sep.Entails`,
  `Sep.emp`, `Sep.sand`, `Sep.sor`, `Sep.sep` and `Sep.wand`.

NB (pure): iris's `pure_intro : φ → P ⊢ ⌜φ⌝` forces `sprop.pure φ = fun _ => φ`, which owns
anything. `Sep.spure φ` owns nothing; it is iris's `<affine> ⌜φ⌝ = emp ∧ ⌜φ⌝`.
`SProp` is not affine: `emp` is not `True`.

This module gives the definitions; the proofs that the instances satisfy `Laws` are not
part of it.
-/

@[expose] public section

namespace Silmaril.X86.Sep.BI

universe u v

/-- The operations of a bunched-implications logic: iris-lean's `BIBase`, field for field. -/
structure Ops (PROP : Type u) where
  Entails : PROP → PROP → Prop
  emp : PROP
  pure : Prop → PROP
  and : PROP → PROP → PROP
  or : PROP → PROP → PROP
  imp : PROP → PROP → PROP
  sForall : (PROP → Prop) → PROP
  sExists : (PROP → Prop) → PROP
  sep : PROP → PROP → PROP
  wand : PROP → PROP → PROP
  persistently : PROP → PROP
  later : PROP → PROP

namespace Ops

variable {PROP : Type u} (O : Ops PROP)

/-- Bi-entailment, iris's `P ⊣⊢ Q`. -/
structure BiEntails (P Q : PROP) : Prop where
  mp : O.Entails P Q
  mpr : O.Entails Q P

/-- iris's `∀ a, P a`, encoded through `sForall`. -/
def «forall» {α : Sort v} (P : α → PROP) : PROP := O.sForall fun p => ∃ a, P a = p

/-- iris's `∃ a, P a`, encoded through `sExists`. -/
def «exists» {α : Sort v} (P : α → PROP) : PROP := O.sExists fun p => ∃ a, P a = p

/-- iris's `True`, that is `⌜True⌝`. -/
def True : PROP := O.pure _root_.True

/-- iris's `False`, that is `⌜False⌝`. -/
def False : PROP := O.pure _root_.False

end Ops

/-- The laws of a (discrete) BI: the non-OFE fields of iris-lean's `BI`, in its order, with
its names. iris's `P ⊢ Q` is `O.Entails P Q`, `P ⊣⊢ Q` is `O.BiEntails P Q`. -/
structure Laws {PROP : Type u} (O : Ops PROP) : Prop where
  entails_refl {P : PROP} : O.Entails P P
  entails_trans {P Q R : PROP} : O.Entails P Q → O.Entails Q R → O.Entails P R
  equiv_iff {P Q : PROP} : (P = Q) ↔ O.BiEntails P Q

  pure_intro {φ : Prop} {P : PROP} : φ → O.Entails P (O.pure φ)
  pure_elim' {φ : Prop} {P : PROP} : (φ → O.Entails O.True P) → O.Entails (O.pure φ) P

  and_elim_l {P Q : PROP} : O.Entails (O.and P Q) P
  and_elim_r {P Q : PROP} : O.Entails (O.and P Q) Q
  and_intro {P Q R : PROP} : O.Entails P Q → O.Entails P R → O.Entails P (O.and Q R)

  or_intro_l {P Q : PROP} : O.Entails P (O.or P Q)
  or_intro_r {P Q : PROP} : O.Entails Q (O.or P Q)
  or_elim {P Q R : PROP} : O.Entails P R → O.Entails Q R → O.Entails (O.or P Q) R

  imp_intro {P Q R : PROP} : O.Entails (O.and P Q) R → O.Entails P (O.imp Q R)
  imp_elim {P Q R : PROP} : O.Entails P (O.imp Q R) → O.Entails (O.and P Q) R

  sForall_intro {P : PROP} {Ψ : PROP → Prop} :
    (∀ p, Ψ p → O.Entails P p) → O.Entails P (O.sForall Ψ)
  sForall_elim {Ψ : PROP → Prop} {p : PROP} : Ψ p → O.Entails (O.sForall Ψ) p

  sExists_intro {Ψ : PROP → Prop} {p : PROP} : Ψ p → O.Entails p (O.sExists Ψ)
  sExists_elim {Φ : PROP → Prop} {Q : PROP} :
    (∀ p, Φ p → O.Entails p Q) → O.Entails (O.sExists Φ) Q

  sep_mono {P P' Q Q' : PROP} :
    O.Entails P Q → O.Entails P' Q' → O.Entails (O.sep P P') (O.sep Q Q')
  emp_sep {P : PROP} : O.BiEntails (O.sep O.emp P) P
  sep_symm {P Q : PROP} : O.Entails (O.sep P Q) (O.sep Q P)
  sep_assoc_l {P Q R : PROP} : O.Entails (O.sep (O.sep P Q) R) (O.sep P (O.sep Q R))

  wand_intro {P Q R : PROP} : O.Entails (O.sep P Q) R → O.Entails P (O.wand Q R)
  wand_elim {P Q R : PROP} : O.Entails P (O.wand Q R) → O.Entails (O.sep P Q) R

  persistently_mono {P Q : PROP} :
    O.Entails P Q → O.Entails (O.persistently P) (O.persistently Q)
  persistently_idem_2 {P : PROP} :
    O.Entails (O.persistently P) (O.persistently (O.persistently P))
  persistently_emp_2 : O.Entails O.emp (O.persistently O.emp)
  persistently_and_2 {P Q : PROP} :
    O.Entails (O.and (O.persistently P) (O.persistently Q)) (O.persistently (O.and P Q))
  persistently_absorb_l {P Q : PROP} :
    O.Entails (O.sep (O.persistently P) Q) (O.persistently P)
  persistently_and_l {P Q : PROP} : O.Entails (O.and (O.persistently P) Q) (O.sep P Q)

  later_mono {P Q : PROP} : O.Entails P Q → O.Entails (O.later P) (O.later Q)
  later_intro {P : PROP} : O.Entails P (O.later P)

  later_sForall_2 {Φ : PROP → Prop} :
    O.Entails (O.forall fun p => O.imp (O.pure (Φ p)) (O.later p)) (O.later (O.sForall Φ))
  later_sExists_false {Φ : PROP → Prop} :
    O.Entails (O.later (O.sExists Φ))
      (O.or (O.later O.False) (O.exists fun p => O.and (O.pure (Φ p)) (O.later p)))
  later_sep {P Q : PROP} : O.BiEntails (O.later (O.sep P Q)) (O.sep (O.later P) (O.later Q))
  later_persistently {P : PROP} :
    O.BiEntails (O.later (O.persistently P)) (O.persistently (O.later P))
  later_false_em {P : PROP} :
    O.Entails (O.later P) (O.or (O.later O.False) (O.imp (O.later O.False) P))

/-! ## Separation algebras -/

/-- A separation algebra: a unit, a disjointness relation and a union, which form a partial
commutative monoid on disjoint pairs. `union` is total but its value on overlapping pairs is
never observed. -/
class SepAlg (α : Type u) where
  unit : α
  Disjoint : α → α → Prop
  union : α → α → α
  disjoint_symm {a b : α} : Disjoint a b → Disjoint b a
  union_comm {a b : α} : Disjoint a b → union a b = union b a
  unit_disjoint {a : α} : Disjoint unit a
  unit_union {a : α} : union unit a = a
  disjoint_assoc {a b c : α} :
    Disjoint a b → Disjoint (union a b) c → Disjoint b c ∧ Disjoint a (union b c)
  union_assoc {a b c : α} :
    Disjoint a b → Disjoint (union a b) c → union (union a b) c = union a (union b c)

namespace SepAlg

variable {ι : Type u} {β : Type v}

/-- The empty partial map. -/
def pmapUnit : ι → Option β := fun _ => none

/-- Partial maps with disjoint domains. -/
def pmapDisjoint (h₁ h₂ : ι → Option β) : Prop := ∀ l, h₁ l = none ∨ h₂ l = none

/-- Left-biased union of partial maps (the same body as `Frag.union`). -/
def pmapUnion (h₁ h₂ : ι → Option β) : ι → Option β := fun l =>
  match h₁ l with
  | some v => some v
  | none => h₂ l

theorem pmapUnion_none {h₁ h₂ : ι → Option β} {l : ι} (h : h₁ l = none) :
    pmapUnion h₁ h₂ l = h₂ l := by
  simp [pmapUnion, h]

theorem pmapUnion_some {h₁ h₂ : ι → Option β} {l : ι} {x : β} (h : h₁ l = some x) :
    pmapUnion h₁ h₂ l = some x := by
  simp [pmapUnion, h]

theorem pmapUnion_eq_none {h₁ h₂ : ι → Option β} {l : ι} :
    pmapUnion h₁ h₂ l = none ↔ h₁ l = none ∧ h₂ l = none := by
  cases e : h₁ l <;> simp [pmapUnion, e]

/-- Partial maps under disjoint union (`Frag` is `Loc → Option Val`). -/
instance pmap : SepAlg (ι → Option β) where
  unit := pmapUnit
  Disjoint := pmapDisjoint
  union := pmapUnion
  disjoint_symm h l := (h l).symm
  union_comm {a b} h := by
    funext l
    rcases h l with e | e
    · rw [pmapUnion_none e]; cases e' : b l <;> simp [pmapUnion, e, e']
    · rw [pmapUnion_none (h₁ := b) e]; cases e' : a l <;> simp [pmapUnion, e, e']
  unit_disjoint _ := Or.inl rfl
  unit_union := rfl
  disjoint_assoc {a b c} hab habc := by
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rcases habc l with e | e
      · exact Or.inl (pmapUnion_eq_none.mp e).2
      · exact Or.inr e
    · rcases hab l with e | e
      · exact Or.inl e
      · rcases habc l with e' | e'
        · exact Or.inl (pmapUnion_eq_none.mp e').1
        · exact Or.inr (pmapUnion_eq_none.mpr ⟨e, e'⟩)
  union_assoc {a b c} _ _ := by
    funext l
    simp only [pmapUnion]
    cases a l <;> rfl

end SepAlg

/-- Products, componentwise (for instance `Frag × (XReg → Option Xmm)`). -/
instance SepAlg.prod {α : Type u} {β : Type v} [SepAlg α] [SepAlg β] : SepAlg (α × β) where
  unit := (SepAlg.unit, SepAlg.unit)
  Disjoint a b := SepAlg.Disjoint a.1 b.1 ∧ SepAlg.Disjoint a.2 b.2
  union a b := (SepAlg.union a.1 b.1, SepAlg.union a.2 b.2)
  disjoint_symm h := ⟨SepAlg.disjoint_symm h.1, SepAlg.disjoint_symm h.2⟩
  union_comm h := by rw [SepAlg.union_comm h.1, SepAlg.union_comm h.2]
  unit_disjoint := ⟨SepAlg.unit_disjoint, SepAlg.unit_disjoint⟩
  unit_union {a} := by
    show (SepAlg.union SepAlg.unit a.1, SepAlg.union SepAlg.unit a.2) = a
    rw [SepAlg.unit_union, SepAlg.unit_union]
  disjoint_assoc hab habc :=
    have h₁ := SepAlg.disjoint_assoc hab.1 habc.1
    have h₂ := SepAlg.disjoint_assoc hab.2 habc.2
    ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩
  union_assoc hab habc := by
    rw [SepAlg.union_assoc hab.1 habc.1, SepAlg.union_assoc hab.2 habc.2]

/-! ## The BI of predicates over a separation algebra -/

section Pred

variable {α : Type u} [SepAlg α]

/-- Entailment of predicates. -/
def entails (P Q : α → Prop) : Prop := ∀ h, P h → Q h

/-- The unit predicate. -/
def emp : α → Prop := fun h => h = SepAlg.unit

/-- Separating conjunction. -/
def sep (P Q : α → Prop) : α → Prop := fun h =>
  ∃ h₁ h₂, SepAlg.Disjoint h₁ h₂ ∧ h = SepAlg.union h₁ h₂ ∧ P h₁ ∧ Q h₂

/-- Magic wand. -/
def wand (P Q : α → Prop) : α → Prop := fun h =>
  ∀ h', SepAlg.Disjoint h h' → P h' → Q (SepAlg.union h h')

/-- The persistently modality: `P` holds of the unit (and nothing is owned). -/
def persistently (P : α → Prop) : α → Prop := fun _ => P SepAlg.unit

variable (α) in
/-- The classical, non-affine BI of predicates over a separation algebra. -/
def ops : Ops (α → Prop) where
  Entails := entails
  emp := emp
  pure φ := fun _ => φ
  and P Q h := P h ∧ Q h
  or P Q h := P h ∨ Q h
  imp P Q h := P h → Q h
  sForall Ψ h := ∀ p, Ψ p → p h
  sExists Ψ h := ∃ p, Ψ p ∧ p h
  sep := sep
  wand := wand
  persistently := persistently
  later P := P

end Pred

/-! ## `SProp` -/

open Silmaril.X86.Sep (SProp Frag)

/-- `SProp` as a classical, non-affine BI, written with `Sep`'s own connectives. -/
def sprop : Ops SProp where
  Entails := Sep.Entails
  emp := Sep.emp
  pure φ := fun _ => φ
  and := Sep.sand
  or := Sep.sor
  imp P Q h := P h → Q h
  sForall Ψ h := ∀ p, Ψ p → p h
  sExists Ψ h := ∃ p, Ψ p ∧ p h
  sep := Sep.sep
  wand := Sep.wand
  persistently P := fun _ => P Frag.empty
  later P := P

end Silmaril.X86.Sep.BI
