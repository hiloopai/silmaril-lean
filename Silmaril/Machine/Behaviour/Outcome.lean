module

public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Logic.Relation

/-!
# Outcomes, failure modes and the outcome relation

This file fixes the vocabulary shared by the compilation relation (#452) and
machine-code equivalence (#453).

An `Outcome R T F` is what one run of a program can show: a return with a
value in `R`, a designated trap with payload in `T`, a fault in `F`,
undefined behaviour, resource exhaustion, or divergence.

* `faulted` collects machine faults that are not the designated trap: stuck
  states, unsupported instructions, page faults and the like.
* `undefined` is source-level undefined behaviour, such as a Lir `.stuck`.
* `exhausted` is running out of a resource (stack, fuel, memory) that the
  source semantics does not bound.

Following #426 and #452 faults and undefined behaviour stay distinct from traps
and from each other, and no failure mode exchanges them with anything else.

## Orientation

`Outcome.Rel mode ob o o'` relates an **implementation** (target) outcome `o`
to a **specification** (source) outcome `o'`. The relation is not symmetric in
general, and every statement below keeps this orientation. Payloads are
related by an observation `ob : Obs`, one relation each for return values,
trap payloads and fault payloads.

## Failure modes (#452)

| Target \ Source | returned v | trapped | diverges |
| --- | --- | --- | --- |
| returned v' | `ob.ret v' v`, all modes | never | never |
| trapped | never | all modes | `divergeToTrap`, `trapOrDiverge` |
| diverges | never | `trapOrDiverge` only | all modes |

Trap payloads are compared by `ob.trap` in `strict` and `divergeToTrap`. In
`trapOrDiverge` they are ignored: otherwise the relation would not be
transitive through a middle `diverges` (a trap related to a divergence related
to a trap with an unrelated payload). Faults relate only to faults (by
`ob.fault`), `undefined` only to `undefined`.

## Resource exhaustion

The exhaustion relaxation is a separate parameter `Exhaustion`, never folded
into `FailureMode`. With `.allowed`, a target `exhausted` outcome implements
every source outcome, as CompCert's out-of-memory rule does; nothing else
changes. With `.forbidden`, `exhausted` relates only to `exhausted`. A
`Mode` pairs the two choices, ordered pointwise; the composite of two steps is
in the join (`⊔`) of their modes.

## What each mode preserves

Proved below for the outcome relation (the lemmas in the section
`Preservation`):

* returns relate only to returns, in every mode (`Rel.returned_left`); from the
  source side, only returns or (under `.allowed`) exhaustion relate to a
  return (`Rel.returned_right`);
* for `failure ≤ divergeToTrap`, a target divergence implements only a source
  divergence (`Rel.diverges_left`): termination is preserved;
* for `failure ≤ divergeToTrap`, a source trap is implemented only by a target
  trap or by exhaustion (`Rel.trapped_right`): trap reliability;
* for `strict`, a target trap implements only a source trap
  (`Rel.trapped_left`): trap-freedom is preserved;
* `undefined` relates only to `undefined` on the target side
  (`Rel.undefined_left`), and on the source side is implemented only by
  `undefined` or allowed exhaustion (`Rel.undefined_right`).

## Laws

`Rel.mono` (in the mode and the observation), `Rel.refl` (reflexive
observation), `Rel.trans` (into the join of the modes and the composite
observation), `Rel.symm` (outside `divergeToTrap` and with exhaustion
forbidden), and `Rel.strict_of_mutual`: mutual `divergeToTrap` relatedness is
`strict` relatedness, so `divergeToTrap` is a preorder whose symmetric part is
`strict`.

This file does not model event traces or host I/O: an outcome carries no
trace, so the #452 question of which trace prefixes a trap may cut short is
not addressed here.
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour

/-- The observable result of one run. See the module docstring for the meaning
of each constructor; `faulted`, `undefined` and `exhausted` are kept apart from
`trapped` and from each other. -/
inductive Outcome (R T F : Type*) where
  | returned (r : R)
  | trapped (t : T)
  | faulted (f : F)
  | undefined
  | exhausted
  | diverges

/-! ## Failure modes and the exhaustion relaxation -/

/-- When may traps and divergence be exchanged (#452)? Ordered
`strict < divergeToTrap < trapOrDiverge`. -/
inductive FailureMode where
  | strict
  | divergeToTrap
  | trapOrDiverge
  deriving DecidableEq, Repr

namespace FailureMode

def rank : FailureMode → Nat
  | strict => 0
  | divergeToTrap => 1
  | trapOrDiverge => 2

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder FailureMode := LinearOrder.lift' rank rank_injective

theorem le_iff_rank {a b : FailureMode} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

theorem strict_le (a : FailureMode) : strict ≤ a := by
  cases a <;> decide

theorem le_trapOrDiverge (a : FailureMode) : a ≤ trapOrDiverge := by
  cases a <;> decide

theorem eq_trapOrDiverge_of_le {a b : FailureMode} (h : a ≤ b) (ha : a = trapOrDiverge) :
    b = trapOrDiverge := by
  subst ha; cases b <;> first | rfl | exact absurd h (by decide)

theorem ne_strict_of_le {a b : FailureMode} (h : a ≤ b) (ha : a ≠ strict) : b ≠ strict := by
  rintro rfl; cases a <;> first | exact ha rfl | exact absurd h (by decide)

end FailureMode

/-- The resource-exhaustion relaxation, ordered `forbidden < allowed`. It is a
separate axis from `FailureMode` (#452). -/
inductive Exhaustion where
  | forbidden
  | allowed
  deriving DecidableEq, Repr

namespace Exhaustion

def rank : Exhaustion → Nat
  | forbidden => 0
  | allowed => 1

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder Exhaustion := LinearOrder.lift' rank rank_injective

theorem forbidden_le (a : Exhaustion) : forbidden ≤ a := by
  cases a <;> decide

theorem eq_allowed_of_le {a b : Exhaustion} (h : a ≤ b) (ha : a = allowed) : b = allowed := by
  subst ha; cases b <;> first | rfl | exact absurd h (by decide)

end Exhaustion

/-- A failure mode together with the exhaustion relaxation. -/
structure Mode where
  failure : FailureMode
  exhaustion : Exhaustion
  deriving DecidableEq, Repr

namespace Mode

/-- No exchange of traps and divergence, no exhaustion. -/
def strict : Mode := ⟨.strict, .forbidden⟩

instance : SemilatticeSup Mode where
  le a b := a.failure ≤ b.failure ∧ a.exhaustion ≤ b.exhaustion
  le_refl a := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm a b h₁ h₂ := by
    cases a; cases b
    simp only [Mode.mk.injEq]
    exact ⟨le_antisymm h₁.1 h₂.1, le_antisymm h₁.2 h₂.2⟩
  sup a b := ⟨a.failure ⊔ b.failure, a.exhaustion ⊔ b.exhaustion⟩
  le_sup_left a b := ⟨le_sup_left, le_sup_left⟩
  le_sup_right a b := ⟨le_sup_right, le_sup_right⟩
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩

theorem le_def {a b : Mode} : a ≤ b ↔ a.failure ≤ b.failure ∧ a.exhaustion ≤ b.exhaustion :=
  Iff.rfl

@[simp] theorem sup_failure (a b : Mode) : (a ⊔ b).failure = a.failure ⊔ b.failure := rfl

@[simp] theorem sup_exhaustion (a b : Mode) : (a ⊔ b).exhaustion = a.exhaustion ⊔ b.exhaustion :=
  rfl

theorem strict_le (a : Mode) : strict ≤ a :=
  ⟨FailureMode.strict_le _, Exhaustion.forbidden_le _⟩

instance : OrderBot Mode where
  bot := strict
  bot_le := strict_le

end Mode

/-! ## Observations -/

/-- How payloads are compared: return values, trap payloads, fault payloads.
The first index is the implementation side. -/
structure Obs (R R' T T' F F' : Type*) where
  ret : R → R' → Prop
  trap : T → T' → Prop
  fault : F → F' → Prop

namespace Obs

variable {R R' R'' T T' T'' F F' F'' : Type*}

/-- Equality on every payload. -/
protected def id : Obs R R T T F F := ⟨Eq, Eq, Eq⟩

/-- Componentwise relational composition. -/
def comp (o₁ : Obs R R' T T' F F') (o₂ : Obs R' R'' T' T'' F' F'') : Obs R R'' T T'' F F'' :=
  ⟨Relation.Comp o₁.ret o₂.ret, Relation.Comp o₁.trap o₂.trap, Relation.Comp o₁.fault o₂.fault⟩

/-- Componentwise converse. -/
def flip (o : Obs R R' T T' F F') : Obs R' R T' T F' F :=
  ⟨fun b a => o.ret a b, fun b a => o.trap a b, fun b a => o.fault a b⟩

instance : LE (Obs R R' T T' F F') where
  le a b := (∀ x y, a.ret x y → b.ret x y) ∧ (∀ x y, a.trap x y → b.trap x y) ∧
    (∀ x y, a.fault x y → b.fault x y)

instance : Preorder (Obs R R' T T' F F') where
  le_refl _ := ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  le_trans _ _ _ h₁ h₂ :=
    ⟨fun x y h => h₂.1 x y (h₁.1 x y h), fun x y h => h₂.2.1 x y (h₁.2.1 x y h),
      fun x y h => h₂.2.2 x y (h₁.2.2 x y h)⟩

/-- Reflexivity on every payload. -/
structure IsRefl (o : Obs R R T T F F) : Prop where
  ret : ∀ r, o.ret r r
  trap : ∀ t, o.trap t t
  fault : ∀ f, o.fault f f

/-- A partial equivalence on every payload: symmetric and transitive, not
necessarily reflexive. Values outside its domain (such as an undefined x86
flag) are never observed. -/
structure IsPER (o : Obs R R T T F F) : Prop where
  symm : o.flip ≤ o
  trans : o.comp o ≤ o

theorem isRefl_id : (Obs.id : Obs R R T T F F).IsRefl := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem IsRefl.flip {o : Obs R R T T F F} (h : o.IsRefl) : o.flip.IsRefl :=
  ⟨h.ret, h.trap, h.fault⟩

theorem isPER_id : (Obs.id : Obs R R T T F F).IsPER where
  symm := ⟨fun _ _ h => h.symm, fun _ _ h => h.symm, fun _ _ h => h.symm⟩
  trans := ⟨fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂, fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂,
    fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂⟩

@[simp] theorem id_comp (o : Obs R R' T T' F F') : Obs.id.comp o = o := by
  cases o; simp only [comp, Obs.id, Relation.eq_comp]

@[simp] theorem comp_id (o : Obs R R' T T' F F') : o.comp Obs.id = o := by
  cases o; simp only [comp, Obs.id, Relation.comp_eq]

@[simp] theorem flip_flip (o : Obs R R' T T' F F') : o.flip.flip = o := rfl

@[simp] theorem flip_id : (Obs.id : Obs R R T T F F).flip = Obs.id := by
  simp only [flip, Obs.id, Obs.mk.injEq]
  exact ⟨funext₂ fun _ _ => propext eq_comm, funext₂ fun _ _ => propext eq_comm,
    funext₂ fun _ _ => propext eq_comm⟩

theorem flip_comp (o₁ : Obs R R' T T' F F') (o₂ : Obs R' R'' T' T'' F' F'') :
    (o₁.comp o₂).flip = o₂.flip.comp o₁.flip := by
  simp only [flip, comp, Obs.mk.injEq]
  refine ⟨funext₂ fun _ _ => propext ?_, funext₂ fun _ _ => propext ?_,
    funext₂ fun _ _ => propext ?_⟩ <;>
    exact ⟨fun ⟨m, h₁, h₂⟩ => ⟨m, h₂, h₁⟩, fun ⟨m, h₁, h₂⟩ => ⟨m, h₂, h₁⟩⟩

theorem flip_mono {a b : Obs R R' T T' F F'} (h : a ≤ b) : a.flip ≤ b.flip :=
  ⟨fun x y => h.1 y x, fun x y => h.2.1 y x, fun x y => h.2.2 y x⟩

theorem comp_mono {a a' : Obs R R' T T' F F'} {b b' : Obs R' R'' T' T'' F' F''}
    (ha : a ≤ a') (hb : b ≤ b') : a.comp b ≤ a'.comp b' :=
  ⟨fun _ _ ⟨m, h₁, h₂⟩ => ⟨m, ha.1 _ _ h₁, hb.1 _ _ h₂⟩,
    fun _ _ ⟨m, h₁, h₂⟩ => ⟨m, ha.2.1 _ _ h₁, hb.2.1 _ _ h₂⟩,
    fun _ _ ⟨m, h₁, h₂⟩ => ⟨m, ha.2.2 _ _ h₁, hb.2.2 _ _ h₂⟩⟩

end Obs

/-! ## The outcome relation -/

namespace Outcome

variable {R R' R'' T T' T'' F F' F'' : Type*}

/-- `Rel mode ob o o'`: the implementation outcome `o` implements the
specification outcome `o'`. See the module docstring for the table. -/
def Rel (mode : Mode) (ob : Obs R R' T T' F F') : Outcome R T F → Outcome R' T' F' → Prop
  | .returned a, .returned b => ob.ret a b
  | .trapped a, .trapped b => mode.failure = .trapOrDiverge ∨ ob.trap a b
  | .trapped _, .diverges => mode.failure ≠ .strict
  | .diverges, .trapped _ => mode.failure = .trapOrDiverge
  | .diverges, .diverges => True
  | .faulted a, .faulted b => ob.fault a b
  | .undefined, .undefined => True
  | .exhausted, .exhausted => True
  | .exhausted, _ => mode.exhaustion = .allowed
  | _, _ => False

namespace Rel

variable {m m' m₁ m₂ : Mode} {ob ob' : Obs R R' T T' F F'}

/-- Weakening in the mode and in the observation. -/
theorem mono (hm : m ≤ m') (hob : ob ≤ ob') {o : Outcome R T F} {p : Outcome R' T' F'}
    (h : Rel m ob o p) : Rel m' ob' o p := by
  have hf := FailureMode.eq_trapOrDiverge_of_le hm.1
  have hs := FailureMode.ne_strict_of_le hm.1
  have he := Exhaustion.eq_allowed_of_le hm.2
  cases o <;> cases p <;> simp only [Rel] at h ⊢ <;>
    first
    | exact hob.1 _ _ h
    | exact hob.2.2 _ _ h
    | exact hf h
    | exact hs h
    | exact he h
    | exact h.imp hf (hob.2.1 _ _)

theorem mono_mode (hm : m ≤ m') {o : Outcome R T F} {p : Outcome R' T' F'}
    (h : Rel m ob o p) : Rel m' ob o p :=
  h.mono hm le_rfl

theorem strict_divergeToTrap {x : Exhaustion} {o : Outcome R T F} {p : Outcome R' T' F'}
    (h : Rel ⟨.strict, x⟩ ob o p) : Rel ⟨.divergeToTrap, x⟩ ob o p :=
  mono_mode (show (⟨.strict, x⟩ : Mode) ≤ ⟨.divergeToTrap, x⟩ from
    ⟨FailureMode.strict_le _, le_rfl⟩) h

theorem divergeToTrap_trapOrDiverge {x : Exhaustion} {o : Outcome R T F}
    {p : Outcome R' T' F'} (h : Rel ⟨.divergeToTrap, x⟩ ob o p) :
    Rel ⟨.trapOrDiverge, x⟩ ob o p :=
  mono_mode (show (⟨.divergeToTrap, x⟩ : Mode) ≤ ⟨.trapOrDiverge, x⟩ from
    ⟨FailureMode.le_trapOrDiverge _, le_rfl⟩) h

theorem forbidden_allowed {f : FailureMode} {o : Outcome R T F} {p : Outcome R' T' F'}
    (h : Rel ⟨f, .forbidden⟩ ob o p) : Rel ⟨f, .allowed⟩ ob o p :=
  mono_mode (show (⟨f, .forbidden⟩ : Mode) ≤ ⟨f, .allowed⟩ from
    ⟨le_rfl, Exhaustion.forbidden_le _⟩) h

/-- Reflexivity for a reflexive observation, in every mode. -/
theorem refl {ob : Obs R R T T F F} (hob : ob.IsRefl) (m : Mode) (o : Outcome R T F) :
    Rel m ob o o := by
  cases o <;> simp only [Rel]
  · exact hob.ret _
  · exact .inr (hob.trap _)
  · exact hob.fault _

/-- Transitivity within one mode. -/
theorem trans_same {ob₁ : Obs R R' T T' F F'} {ob₂ : Obs R' R'' T' T'' F' F''}
    {o : Outcome R T F} {p : Outcome R' T' F'} {q : Outcome R'' T'' F''}
    (h₁ : Rel m ob₁ o p) (h₂ : Rel m ob₂ p q) : Rel m (ob₁.comp ob₂) o q := by
  cases o <;> cases p <;> cases q <;> simp only [Rel] at h₁ h₂ ⊢ <;>
    first
    | exact ⟨_, h₁, h₂⟩
    | exact h₁
    | exact h₂
    | exact .inl h₂
    | exact False.elim h₁
    | exact False.elim h₂
    | exact h₁.elim .inl fun h => h₂.imp id fun h' => ⟨_, h, h'⟩

/-- Transitivity: the composite is related in the join of the modes, by the
composite observation. -/
theorem trans {ob₁ : Obs R R' T T' F F'} {ob₂ : Obs R' R'' T' T'' F' F''}
    {o : Outcome R T F} {p : Outcome R' T' F'} {q : Outcome R'' T'' F''}
    (h₁ : Rel m₁ ob₁ o p) (h₂ : Rel m₂ ob₂ p q) : Rel (m₁ ⊔ m₂) (ob₁.comp ob₂) o q :=
  trans_same (h₁.mono_mode le_sup_left) (h₂.mono_mode le_sup_right)

/-- Symmetry outside `divergeToTrap` and with exhaustion forbidden: the
converse holds for the converse observation. -/
theorem symm (hf : m.failure ≠ .divergeToTrap) (he : m.exhaustion = .forbidden)
    {o : Outcome R T F} {p : Outcome R' T' F'} (h : Rel m ob o p) : Rel m ob.flip p o := by
  obtain ⟨f, x⟩ := m
  simp only at hf he
  subst he
  cases f <;> cases o <;> cases p <;> simp_all [Rel, Obs.flip]

/-- Mutual `divergeToTrap` relatedness is `strict` relatedness: a
trap/divergence exchange is permitted in one direction only. The observation
of the converse direction is irrelevant. -/
theorem strict_of_mutual {x : Exhaustion} {ob' : Obs R' R T' T F' F}
    {o : Outcome R T F} {p : Outcome R' T' F'}
    (h : Rel ⟨.divergeToTrap, x⟩ ob o p) (h' : Rel ⟨.divergeToTrap, x⟩ ob' p o) :
    Rel ⟨.strict, x⟩ ob o p := by
  cases o <;> cases p <;> simp only [Rel] at h h' ⊢
  all_goals first
    | exact h
    | exact .inr (h.resolve_left (by decide))
    | exact absurd h' (by decide)
    | exact absurd h (by decide)

/-- In the strict mode with exhaustion forbidden, equality is the only relation
equality observes. -/
theorem strict_id_iff {o o' : Outcome R T F} :
    Rel Mode.strict Obs.id o o' ↔ o = o' := by
  constructor
  · intro h
    cases o <;> cases o' <;> simp_all [Rel, Mode.strict, Obs.id]
  · rintro rfl
    exact refl Obs.isRefl_id _ _

/-! ### Preservation -/

section Preservation

variable {o : Outcome R T F} {p : Outcome R' T' F'}

/-- A target return implements only a source return, in every mode. -/
theorem returned_left {a : R} (h : Rel m ob (.returned a) p) :
    ∃ b, p = .returned b ∧ ob.ret a b := by
  cases p <;> simp only [Rel] at h
  exact ⟨_, rfl, h⟩

/-- A source return is implemented only by a return or, under the exhaustion
relaxation, by exhaustion. -/
theorem returned_right {b : R'} (h : Rel m ob o (.returned b)) :
    (∃ a, o = .returned a ∧ ob.ret a b) ∨ (o = .exhausted ∧ m.exhaustion = .allowed) := by
  cases o <;> simp only [Rel] at h
  · exact .inl ⟨_, rfl, h⟩
  · exact .inr ⟨rfl, h⟩

/-- Termination: for `failure ≤ divergeToTrap`, a target divergence implements
only a source divergence. -/
theorem diverges_left (hm : m.failure ≤ .divergeToTrap) (h : Rel m ob .diverges p) :
    p = .diverges := by
  cases p <;> simp only [Rel] at h
  · exact absurd (h ▸ hm) (by decide)
  · rfl

/-- Trap reliability: for `failure ≤ divergeToTrap`, a source trap is
implemented only by a target trap with a related payload, or by allowed
exhaustion. -/
theorem trapped_right (hm : m.failure ≤ .divergeToTrap) {b : T'} (h : Rel m ob o (.trapped b)) :
    (∃ a, o = .trapped a ∧ ob.trap a b) ∨ (o = .exhausted ∧ m.exhaustion = .allowed) := by
  have hne : m.failure ≠ .trapOrDiverge := fun he => absurd (he ▸ hm) (by decide)
  cases o <;> simp only [Rel] at h
  · exact .inl ⟨_, rfl, h.resolve_left hne⟩
  · exact .inr ⟨rfl, h⟩
  · exact absurd h hne

/-- Trap-freedom: in the strict failure mode a target trap implements only a
source trap with a related payload. -/
theorem trapped_left (hm : m.failure = .strict) {a : T} (h : Rel m ob (.trapped a) p) :
    ∃ b, p = .trapped b ∧ ob.trap a b := by
  cases p <;> simp only [Rel] at h
  · exact ⟨_, rfl, h.resolve_left (by rw [hm]; decide)⟩
  · exact absurd hm h

/-- A target fault implements only a source fault with a related payload. -/
theorem faulted_left {a : F} (h : Rel m ob (.faulted a) p) :
    ∃ b, p = .faulted b ∧ ob.fault a b := by
  cases p <;> simp only [Rel] at h
  exact ⟨_, rfl, h⟩

/-- Target undefined behaviour implements only source undefined behaviour. -/
theorem undefined_left : Rel m ob .undefined p ↔ p = .undefined := by
  cases p <;> simp only [Rel, reduceCtorEq]

/-- Source undefined behaviour is implemented only by undefined behaviour or by
allowed exhaustion. -/
theorem undefined_right (h : Rel m ob o .undefined) :
    o = .undefined ∨ (o = .exhausted ∧ m.exhaustion = .allowed) := by
  cases o <;> simp only [Rel] at h
  · exact .inl rfl
  · exact .inr ⟨rfl, h⟩

/-- Without the exhaustion relaxation, a target exhaustion implements only a
source exhaustion. -/
theorem exhausted_left (he : m.exhaustion = .forbidden) (h : Rel m ob .exhausted p) :
    p = .exhausted := by
  cases p <;> simp only [Rel] at h
  all_goals first | rfl | exact absurd (h.symm.trans he) (by decide)

end Preservation

end Rel

end Outcome

end Silmaril.Machine.Behaviour
