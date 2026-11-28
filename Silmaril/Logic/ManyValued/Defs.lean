module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice

@[expose] public section

/-! # Finite truth values

The default lattice is the truth lattice, with logical conjunction as meet and
disjunction as join. The `Information` wrappers order values by how much evidence
they carry. In particular, an institution's order-lax law can use a wrapper when
its refinement is about evidence.
-/

namespace Silmaril.Logic.ManyValued

/-- Strong Kleene truth values. The middle value means unknown. -/
inductive K3 where
  | ff
  | unknown
  | tt
  deriving DecidableEq, Repr

namespace K3

instance : Fintype K3 where
  elems := {ff, unknown, tt}
  complete := by intro a; cases a <;> decide

/-- Rank in the truth order `ff < unknown < tt`. -/
def truthRank : K3 → Nat
  | .ff => 0
  | .unknown => 1
  | .tt => 2

theorem truthRank_injective : Function.Injective truthRank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

instance : LinearOrder K3 := LinearOrder.lift' truthRank truthRank_injective

instance : BoundedOrder K3 where
  bot := ff
  top := tt
  bot_le := by intro a; cases a <;> decide
  le_top := by intro a; cases a <;> decide

/-- Logical negation reverses truth and fixes the unknown value. -/
def neg : K3 → K3
  | .ff => .tt
  | .unknown => .unknown
  | .tt => .ff

/-- Strong Kleene conjunction, the truth meet. -/
abbrev conj (a b : K3) : K3 := a ⊓ b

/-- Strong Kleene disjunction, the truth join. -/
abbrev disj (a b : K3) : K3 := a ⊔ b

/-- Material implication as in the strong Kleene truth table. -/
def materialImp (a b : K3) : K3 := disj (neg a) b

/-- Conjunction of the two directions of material implication. -/
def materialIff (a b : K3) : K3 := conj (materialImp a b) (materialImp b a)

/-- Embed the two classical truth values. -/
def ofBool : Bool → K3
  | false => .ff
  | true => .tt

/-- The unknown value corresponds to `none`. -/
def ofOptionBool : Option Bool → K3
  | none => .unknown
  | some b => ofBool b

/-- Return a Boolean only when the value is known. -/
def toOptionBool : K3 → Option Bool
  | .ff => some false
  | .unknown => none
  | .tt => some true

/-- Observe K3 designation. Only `tt` is designated, so `ff` and `unknown`
both return `false`. -/
def isDesignated : K3 → Bool
  | .tt => true
  | _ => false

/-- A K3 value ordered by refinement of partial information. -/
structure Information where
  val : K3
  deriving DecidableEq, Repr

namespace Information

/-- Unknown refines to any value. A known value only refines to itself. -/
def informationLE (a b : Information) : Prop := a.val = .unknown ∨ a.val = b.val

instance : LE Information := ⟨informationLE⟩

instance : DecidableLE Information := fun a b =>
  show Decidable (a.val = .unknown ∨ a.val = b.val) from inferInstance

/-- Retain a known value only when the two inputs agree. -/
instance : SemilatticeInf Information where
  inf a b := if a = b then a else ⟨.unknown⟩
  le_refl := by rintro ⟨a⟩; cases a <;> decide
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    cases a <;> cases b <;> cases c <;> decide
  le_antisymm := by rintro ⟨a⟩ ⟨b⟩; cases a <;> cases b <;> decide
  inf_le_left := by rintro ⟨a⟩ ⟨b⟩; cases a <;> cases b <;> decide
  inf_le_right := by rintro ⟨a⟩ ⟨b⟩; cases a <;> cases b <;> decide
  le_inf := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    cases a <;> cases b <;> cases c <;> decide

instance : OrderBot Information where
  bot := ⟨.unknown⟩
  bot_le _ := Or.inl rfl

/-- Logical negation of the underlying truth value. -/
def neg (a : Information) : Information := ⟨a.val.neg⟩

end Information
end K3

/-- Belnap–Dunn FOUR. The two middle values distinguish a gap (`neither`)
from conflicting evidence (`both`). -/
inductive FDE where
  | ff
  | neither
  | both
  | tt
  deriving DecidableEq, Repr

namespace FDE

instance : Fintype FDE where
  elems := {ff, neither, both, tt}
  complete := by intro a; cases a <;> decide

/-- Decode independent support and refutation bits, in that order. -/
def ofBits : Bool → Bool → FDE
  | false, false => .neither
  | false, true => .ff
  | true, false => .tt
  | true, true => .both

/-- Whether there is positive evidence. -/
def support : FDE → Bool
  | .tt | .both => true
  | .ff | .neither => false

/-- Whether there is negative evidence. -/
def refute : FDE → Bool
  | .ff | .both => true
  | .tt | .neither => false

/-- Logical negation exchanges the support and refutation bits. -/
def neg (a : FDE) : FDE := ofBits a.refute a.support

/-- Stronger truth increases support and decreases refutation. -/
def truthLE (a b : FDE) : Prop := a.support ≤ b.support ∧ b.refute ≤ a.refute

instance : LE FDE := ⟨truthLE⟩

instance : DecidableLE FDE := fun a b =>
  show Decidable (a.support ≤ b.support ∧ b.refute ≤ a.refute) from inferInstance

/-- Truth meet requires support for both inputs and refutation of either one. -/
def conj (a b : FDE) : FDE := ofBits (a.support && b.support) (a.refute || b.refute)

/-- Truth join requires support for either input and refutation of both. -/
def disj (a b : FDE) : FDE := ofBits (a.support || b.support) (a.refute && b.refute)

instance : DistribLattice FDE where
  inf := conj
  sup := disj
  le_refl := by intro a; cases a <;> decide
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_antisymm := by intro a b; cases a <;> cases b <;> decide
  inf_le_left := by intro a b; cases a <;> cases b <;> decide
  inf_le_right := by intro a b; cases a <;> cases b <;> decide
  le_inf := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_sup_left := by intro a b; cases a <;> cases b <;> decide
  le_sup_right := by intro a b; cases a <;> cases b <;> decide
  sup_le := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_sup_inf := by intro a b c; cases a <;> cases b <;> cases c <;> decide

instance : BoundedOrder FDE where
  bot := ff
  top := tt
  bot_le := by intro a; cases a <;> decide
  le_top := by intro a; cases a <;> decide

/-- Embed the classical values using exactly one evidence bit. -/
def ofBool (b : Bool) : FDE := ofBits b (!b)

/-- Embed a partial Boolean. A missing Boolean has neither evidence bit. -/
def ofOptionBool : Option Bool → FDE
  | none => .neither
  | some b => ofBool b

/-- Observe FDE designation by projecting support. Both `tt` and `both`
are designated. This forgets refutation. -/
abbrev isDesignated (a : FDE) : Bool := a.support

/-- An FDE value ordered by accumulation of evidence. -/
structure Information where
  val : FDE
  deriving DecidableEq, Repr

namespace Information

/-- More information increases each evidence bit independently. -/
def informationLE (a b : Information) : Prop :=
  a.val.support ≤ b.val.support ∧ a.val.refute ≤ b.val.refute

instance : LE Information := ⟨informationLE⟩

instance : DecidableLE Information := fun a b =>
  show Decidable (a.val.support ≤ b.val.support ∧ a.val.refute ≤ b.val.refute) from inferInstance

/-- Information meet retains evidence shared by the inputs. -/
def meet (a b : Information) : Information :=
  ⟨ofBits (a.val.support && b.val.support) (a.val.refute && b.val.refute)⟩

/-- Information join accumulates evidence from either input. -/
def join (a b : Information) : Information :=
  ⟨ofBits (a.val.support || b.val.support) (a.val.refute || b.val.refute)⟩

instance : DistribLattice Information where
  inf := meet
  sup := join
  le_refl := by rintro ⟨a⟩; cases a <;> decide
  le_trans := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; cases a <;> cases b <;> cases c <;> decide
  le_antisymm := by rintro ⟨a⟩ ⟨b⟩; cases a <;> cases b <;> decide
  inf_le_left := by rintro ⟨a⟩ ⟨b⟩; cases a <;> cases b <;> decide
  inf_le_right := by rintro ⟨a⟩ ⟨b⟩; cases a <;> cases b <;> decide
  le_inf := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; cases a <;> cases b <;> cases c <;> decide
  le_sup_left := by rintro ⟨a⟩ ⟨b⟩; cases a <;> cases b <;> decide
  le_sup_right := by rintro ⟨a⟩ ⟨b⟩; cases a <;> cases b <;> decide
  sup_le := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; cases a <;> cases b <;> cases c <;> decide
  le_sup_inf := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; cases a <;> cases b <;> cases c <;> decide

instance : BoundedOrder Information where
  bot := ⟨.neither⟩
  top := ⟨.both⟩
  bot_le := by rintro ⟨a⟩; cases a <;> decide
  le_top := by rintro ⟨a⟩; cases a <;> decide

/-- Logical negation exchanges the two information channels. -/
def neg (a : Information) : Information := ⟨a.val.neg⟩

end Information
end FDE

/-- Embed K3 into the consistent part of FOUR. -/
def K3.toFDE : K3 → FDE
  | .ff => .ff
  | .unknown => .neither
  | .tt => .tt

/-- Partial inverse to the consistent embedding. Failure indicates conflicting evidence. -/
def FDE.toK3? : FDE → Option K3
  | .ff => some .ff
  | .neither => some .unknown
  | .both => none
  | .tt => some .tt

/-- Interpret consistent FDE values as partial Booleans. Outer `none` indicates
conflicting evidence and `some none` indicates missing evidence. -/
def FDE.toOptionBool? (a : FDE) : Option (Option Bool) := a.toK3?.map K3.toOptionBool

/-- Embed the information refinement order of K3 into that of FOUR. -/
def K3.Information.toFDE (a : K3.Information) : FDE.Information := ⟨a.val.toFDE⟩

end Silmaril.Logic.ManyValued
