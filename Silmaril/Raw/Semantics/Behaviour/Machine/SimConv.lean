module

public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Relation
public import Mathlib.Order.Defs.PartialOrder

/-!
# Simulation conventions

A *simulation convention* is CompCertO's reification of "what it means for a
target-level call to represent a source-level call, and for a target-level
answer to represent a source-level answer" (`koenig2021compcerto`, Def. 2.6).
This file is the algebra alone: no semantics, no machine, no WebAssembly. It
depends on `Mathlib.Logic.Relation` and nothing else in this repository.

## The two structures

A `LangIface` (CompCertO Def. 2.1) is a pair of types: the *questions* a
component may be asked and the *answers* it may give. For a WebAssembly module
a question is a call — a function index, arguments, a memory — and an answer is
an outcome. For a machine, a question is an entry state and an answer is a
halting state.

A `SimConv I₁ I₂` (CompCertO Def. 2.6, in its §2.4) is a **Kripke world**
`World` together with a question relation `q : World → I₁.Q → I₂.Q → Prop` and an answer
relation `a : World → I₁.A → I₂.A → Prop`. The world is what lets the answer
relation mention data fixed at the question: the entry register file, the entry
stack pointer, a memory injection. Without it one cannot say "the callee-saved
registers hold *the values they held on entry*", because "on entry" is not
available when the answer is compared.

Orientation: `I₁` is the **specification** side and `I₂` the
**implementation** side, so `q w s t` reads "`t` implements the question `s` in
world `w`" and `a w s t` reads "`t` implements the answer `s` in world `w`".
This matches `koenig2021compcerto` and is the orientation
`Silmaril.Machine.CallingConvention.SimConv` instantiates (source WebAssembly on
the left, target machine on the right).

## The algebra (CompCertO Thm. 5.2)

`SimConv.id` takes the one-point world and equality on both sides.
`SimConv.comp` takes the product world and relational composition
(`Relation.Comp`) on both sides. The order is **not** inclusion of relations
but CompCertO Def. 5.1, a `∀∃∀` transport game:

`R.Refines S` — written `R ≤ S` — holds when for every world `w` of `S` and
every question pair `S` accepts at `w`, there is a world `v` of `R` at which
`R` accepts the same pair, and *every* answer pair `R` accepts at `v` is one
`S` accepts at `w`.

So `R ≤ S` says `R` is the **more general** convention: it accepts at least as
many questions and promises at least as much about answers. Reading it as an
inclusion of relations gets the question side backwards and the answer side
right, which is why it is a game and not a `⊆`.

### Why the laws are `Equiv`, not `Eq`

`(R.comp S).comp T` has world `(R.World × S.World) × T.World`, which is not
`R.World × (S.World × T.World)`. Associativity therefore cannot be an equation
between `SimConv`s: it is `SimConv.Equiv`, mutual `Refines`, which is the
equivalence relation induced by the preorder. CompCertO has exactly this issue
and resolves it the same way. The same applies to the two unit laws, whose
worlds carry a stray `PUnit` factor.

`Refines.of_map` is the workhorse: a map `f` from `S`'s worlds to `R`'s worlds
that transports questions forwards and answers backwards witnesses `R ≤ S`.
Every law below except `Refines.trans` is an instance of it, which is the
formal content of "the world is a parameter and nothing depends on its shape".

## Answer sets

A nondeterministic component answers a question with a *set* of answers, so the
answer relation has to be lifted. Lifting it demonically gives two games, and
both occur in this development: `AnswersImplement` quantifies over the
implementation set (soundness — a compiler), `AnswersRealise` over the
specification set (completeness — the WebAssembly subset tower, where the
larger language must exhibit everything the smaller one does). Both compose
along `comp`, which is what lets a chain of translations be composed in the
algebra rather than by hand.

## What is here and what is not

Here: `id`, `comp`, the preorder, `Equiv` and its `Equivalence`, associativity,
both unit laws, and `comp_mono` — the six parts of CompCertO Thm. 5.2 — plus
the two demonic liftings to answer sets.

Not here: anything about simulations. `Silmaril.Machine.Behaviour.SimConv`
restates the compilation relation against these conventions, and
`Silmaril.Machine.CallingConvention.SimConv` derives one from a
`WasmConvention`. In particular there is **no outgoing convention** in this
repository.
-/

@[expose] public section

namespace Silmaril.Machine

/-- A language interface (CompCertO Def. 2.1): a set of questions a component
may be asked and a set of answers it may give. -/
structure LangIface where
  /-- The questions, such as "call function `f` with these arguments". -/
  Q : Type*
  /-- The answers, such as "returned these values" or "trapped". -/
  A : Type*

/-- A simulation convention (CompCertO Def. 2.6): a Kripke world together with
a question relation and an answer relation indexed by it. `I₁` is the
specification side and `I₂` the implementation side. -/
structure SimConv (I₁ I₂ : LangIface) where
  /-- The Kripke world: data fixed when the question is asked and still
  available when the answer is compared. -/
  World : Type*
  /-- Which implementation questions represent which specification questions,
  and in which world. -/
  q : World → I₁.Q → I₂.Q → Prop
  /-- Which implementation answers represent which specification answers, in
  the world the question fixed. -/
  a : World → I₁.A → I₂.A → Prop

namespace SimConv

variable {I₁ I₂ I₃ I₄ : LangIface}

/-- The identity convention (CompCertO Def. 2.6, `id_A := ⟨1, =, =⟩`): one
world, equality on questions and on answers. -/
protected def id (I : LangIface) : SimConv I I where
  World := PUnit
  q _ := Eq
  a _ := Eq

@[simp] theorem id_q (I : LangIface) (v : (SimConv.id I).World) :
    (SimConv.id I).q v = Eq := rfl

@[simp] theorem id_a (I : LangIface) (v : (SimConv.id I).World) :
    (SimConv.id I).a v = Eq := rfl

/-- Composition of conventions (CompCertO Def. 3.6): the product world,
relational composition on both sides. CompCertO writes it `R · S`. -/
def comp (R : SimConv I₁ I₂) (S : SimConv I₂ I₃) : SimConv I₁ I₃ where
  World := R.World × S.World
  q v := Relation.Comp (R.q v.1) (S.q v.2)
  a v := Relation.Comp (R.a v.1) (S.a v.2)

@[simp] theorem comp_World (R : SimConv I₁ I₂) (S : SimConv I₂ I₃) :
    (R.comp S).World = (R.World × S.World) := rfl

@[simp] theorem comp_q (R : SimConv I₁ I₂) (S : SimConv I₂ I₃) (v : R.World × S.World)
    (x : I₁.Q) (z : I₃.Q) : (R.comp S).q v x z ↔ ∃ y, R.q v.1 x y ∧ S.q v.2 y z := Iff.rfl

@[simp] theorem comp_a (R : SimConv I₁ I₂) (S : SimConv I₂ I₃) (v : R.World × S.World)
    (x : I₁.A) (z : I₃.A) : (R.comp S).a v x z ↔ ∃ y, R.a v.1 x y ∧ S.a v.2 y z := Iff.rfl

/-- `K` offered only at the world `w₀`, and only on the questions `Q'`
accepts. The answer relation is `K`'s, world and all; it is the question
relation that is pinned. This is how a convention with a free world is used in
a theorem whose entry data is fixed, as a machine-code contract's is. -/
def pin (K : SimConv I₁ I₂) (w₀ : K.World) (Q' : I₁.Q → I₂.Q → Prop) : SimConv I₁ I₂ where
  World := K.World
  q w x y := w = w₀ ∧ Q' x y
  a := K.a

@[simp] theorem pin_q (K : SimConv I₁ I₂) (w₀ : K.World) (Q' : I₁.Q → I₂.Q → Prop)
    (w : K.World) (x : I₁.Q) (y : I₂.Q) : (K.pin w₀ Q').q w x y ↔ w = w₀ ∧ Q' x y := Iff.rfl

@[simp] theorem pin_a (K : SimConv I₁ I₂) (w₀ : K.World) (Q' : I₁.Q → I₂.Q → Prop) :
    (K.pin w₀ Q').a = K.a := rfl

/-! ## The refinement order (CompCertO Def. 5.1) -/

/-- `R.Refines S`, CompCertO's `R ⊑ S`, written `R ≤ S` when the two worlds
live in one universe: `R` is the **more general** convention. For every world
of `S` and every question pair `S` accepts there, `R` accepts the same pair at
some world of its own, and every answer pair `R` accepts there is one `S`
accepts.

This is a `∀∃∀` transport game, **not** an inclusion of relations: `R` accepts
*more* questions and promises *more* about answers. -/
def Refines (R : SimConv I₁ I₂) (S : SimConv I₁ I₂) : Prop :=
  ∀ v x y, S.q v x y → ∃ u, R.q u x y ∧ ∀ p r, R.a u p r → S.a v p r

/-- The workhorse: a map from `S`'s worlds to `R`'s worlds that transports
questions forwards and answers backwards witnesses `R.Refines S`. Every law of
CompCertO Thm. 5.2 except transitivity is an instance. -/
theorem Refines.of_map {R S : SimConv I₁ I₂} (f : S.World → R.World)
    (hq : ∀ v x y, S.q v x y → R.q (f v) x y)
    (ha : ∀ v p r, R.a (f v) p r → S.a v p r) : R.Refines S :=
  fun v x y h => ⟨f v, hq v x y h, ha v⟩

/-- Reflexivity (CompCertO Thm. 5.2). -/
@[refl] theorem Refines.refl (R : SimConv I₁ I₂) : R.Refines R :=
  Refines.of_map _root_.id (fun _ _ _ h => h) (fun _ _ _ h => h)

/-- Transitivity (CompCertO Thm. 5.2). This is the one law that is not an
instance of `Refines.of_map`: the world of `R` produced for a world of `T`
depends on the intermediate world of `S`, so the witness is chosen, not
mapped. -/
theorem Refines.trans {R S T : SimConv I₁ I₂} (hRS : R.Refines S) (hST : S.Refines T) :
    R.Refines T := by
  intro v x y h
  obtain ⟨u, hu, hua⟩ := hST v x y h
  obtain ⟨t, ht, hta⟩ := hRS u x y hu
  exact ⟨t, ht, fun p r hpr => hua p r (hta p r hpr)⟩

/-- `≤` on conventions over one pair of interfaces, with worlds in one
universe, is `Refines`. -/
instance : LE (SimConv I₁ I₂) where
  le := Refines

theorem le_def {R S : SimConv I₁ I₂} : R ≤ S ↔ R.Refines S := Iff.rfl

/-- Conventions over one pair of interfaces form a preorder under `Refines`
(CompCertO Thm. 5.2). It is not a partial order: the two bracketings of a
triple composite have different world types and are equivalent, not equal. -/
instance : Preorder (SimConv I₁ I₂) where
  le_refl := Refines.refl
  le_trans _ _ _ := Refines.trans

/-! ## Equivalence of conventions -/

/-- Mutual refinement, CompCertO's `R ≡ S`. Associativity and the unit laws
hold in this form and not as equations, because the two sides have different
world types. -/
def Equiv (R S : SimConv I₁ I₂) : Prop :=
  R.Refines S ∧ S.Refines R

@[refl] theorem Equiv.refl (R : SimConv I₁ I₂) : R.Equiv R :=
  ⟨Refines.refl R, Refines.refl R⟩

@[symm] theorem Equiv.symm {R S : SimConv I₁ I₂} (h : R.Equiv S) : S.Equiv R := ⟨h.2, h.1⟩

theorem Equiv.trans {R S T : SimConv I₁ I₂} (hRS : R.Equiv S) (hST : S.Equiv T) : R.Equiv T :=
  ⟨hRS.1.trans hST.1, hST.2.trans hRS.2⟩

/-- `Equiv` is an equivalence relation: the one induced by the preorder. -/
theorem equivalence_equiv : Equivalence (α := SimConv I₁ I₂) Equiv :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- `Equiv` is `≤` in both directions. -/
theorem equiv_iff_le_le {R S : SimConv I₁ I₂} : R.Equiv S ↔ R ≤ S ∧ S ≤ R := Iff.rfl

/-! ## The laws of CompCertO Thm. 5.2 -/

/-- Associativity, as mutual refinement. The two sides have worlds
`(R.World × S.World) × T.World` and `R.World × (S.World × T.World)`, which are
not the same type, so this cannot be an equation — which is exactly how
CompCertO states it. -/
theorem comp_assoc (R : SimConv I₁ I₂) (S : SimConv I₂ I₃) (T : SimConv I₃ I₄) :
    ((R.comp S).comp T).Equiv (R.comp (S.comp T)) := by
  constructor
  · refine Refines.of_map (fun v => ((v.1, v.2.1), v.2.2)) ?_ ?_
    · rintro ⟨u, v, t⟩ x z ⟨y, hy, y', hy', hz⟩
      exact ⟨y', ⟨y, hy, hy'⟩, hz⟩
    · rintro ⟨u, v, t⟩ p r ⟨y', ⟨y, hy, hy'⟩, hz⟩
      exact ⟨y, hy, y', hy', hz⟩
  · refine Refines.of_map (fun v => (v.1.1, v.1.2, v.2)) ?_ ?_
    · rintro ⟨⟨u, v⟩, t⟩ x z ⟨y', ⟨y, hy, hy'⟩, hz⟩
      exact ⟨y, hy, y', hy', hz⟩
    · rintro ⟨⟨u, v⟩, t⟩ p r ⟨y, hy, y', hy', hz⟩
      exact ⟨y', ⟨y, hy, hy'⟩, hz⟩

/-- Left unit, as mutual refinement: the left side's world carries a stray
`PUnit` factor. -/
theorem id_comp (R : SimConv I₁ I₂) : ((SimConv.id I₁).comp R).Equiv R := by
  refine ⟨Refines.of_map (fun v => (PUnit.unit, v)) (fun _ _ _ h => ⟨_, rfl, h⟩) ?_,
    Refines.of_map (fun v => v.2) ?_ (fun _ _ _ h => ⟨_, rfl, h⟩)⟩
  · rintro v p r ⟨_, rfl, h⟩
    exact h
  · rintro v x y ⟨_, rfl, h⟩
    exact h

/-- Right unit, as mutual refinement. -/
theorem comp_id (R : SimConv I₁ I₂) : (R.comp (SimConv.id I₂)).Equiv R := by
  refine ⟨Refines.of_map (fun v => (v, PUnit.unit)) (fun _ _ _ h => ⟨_, h, rfl⟩) ?_,
    Refines.of_map (fun v => v.1) ?_ (fun _ _ _ h => ⟨_, h, rfl⟩)⟩
  · rintro v p r ⟨_, h, rfl⟩
    exact h
  · rintro v x y ⟨_, h, rfl⟩
    exact h

/-- Monotonicity of composition (CompCertO Thm. 5.2, `(·) :: ⊑ × ⊑ → ⊑`): a
more general convention on either side gives a more general composite. The
proof pairs the two chosen worlds, which is exactly why the composite world
has to be the product. -/
theorem comp_mono {R' R : SimConv I₁ I₂} {S' S : SimConv I₂ I₃}
    (hR : R'.Refines R) (hS : S'.Refines S) : (R'.comp S').Refines (R.comp S) := by
  rintro ⟨v₁, v₂⟩ x z ⟨y, hxy, hyz⟩
  obtain ⟨u₁, hu₁, ha₁⟩ := hR v₁ x y hxy
  obtain ⟨u₂, hu₂, ha₂⟩ := hS v₂ y z hyz
  refine ⟨(u₁, u₂), ⟨y, hu₁, hu₂⟩, ?_⟩
  rintro p r ⟨m, hm₁, hm₂⟩
  exact ⟨m, ha₁ p m hm₁, ha₂ m r hm₂⟩

/-- Pinning is antitone in the question relation: a convention offered on
*more* questions, with the same answers, is the more general one. -/
theorem pin_refines_pin (K : SimConv I₁ I₂) (w₀ : K.World) {Q' Q'' : I₁.Q → I₂.Q → Prop}
    (h : ∀ x y, Q'' x y → Q' x y) : (K.pin w₀ Q').Refines (K.pin w₀ Q'') :=
  Refines.of_map _root_.id (fun _ _ _ hq => ⟨hq.1, h _ _ hq.2⟩) (fun _ _ _ ha => ha)

/-! ## The two demonic liftings to answer sets

A question does not determine one answer but a *set* of them. Lifting `K.a w`
to sets demonically gives two different statements, according to which side the
universal quantifier runs over, and this development needs both. -/

/-- **Soundness**: every answer in the implementation set `t` implements some
answer in the specification set `s`, at the world `w`. This is the game
`Silmaril.Machine.Behaviour.Implements'` plays and the one a compiler proves —
the target may do less than the source, never more. The implementation set
comes first, as it does in `Refines mode tgt src`. -/
def AnswersImplement (K : SimConv I₁ I₂) (w : K.World) (t : Set I₂.A) (s : Set I₁.A) : Prop :=
  ∀ o ∈ t, ∃ o' ∈ s, K.a w o' o

/-- **Completeness**: every answer in the specification set `s` is implemented
by some answer in the implementation set `t`, at the world `w`. This is the
game the WebAssembly subset tower plays — the larger language must exhibit
every behaviour of the smaller one — and it is the set-level reading of an
image inclusion. -/
def AnswersRealise (K : SimConv I₁ I₂) (w : K.World) (s : Set I₁.A) (t : Set I₂.A) : Prop :=
  ∀ o ∈ s, ∃ o' ∈ t, K.a w o o'

/-- Soundness composes along `comp`: the middle answer set is shared and the
two composite worlds are paired, exactly as the composite answer relation
asks. -/
theorem AnswersImplement.comp {K : SimConv I₁ I₂} {L : SimConv I₂ I₃} {w : K.World}
    {v : L.World} {s : Set I₁.A} {t : Set I₂.A} {u : Set I₃.A}
    (hK : K.AnswersImplement w t s) (hL : L.AnswersImplement v u t) :
    (K.comp L).AnswersImplement (w, v) u s := by
  intro o ho
  obtain ⟨p, hp, hLa⟩ := hL o ho
  obtain ⟨o', ho', hKa⟩ := hK p hp
  exact ⟨o', ho', p, hKa, hLa⟩

/-- Completeness composes along `comp`. -/
theorem AnswersRealise.comp {K : SimConv I₁ I₂} {L : SimConv I₂ I₃} {w : K.World}
    {v : L.World} {s : Set I₁.A} {t : Set I₂.A} {u : Set I₃.A}
    (hK : K.AnswersRealise w s t) (hL : L.AnswersRealise v t u) :
    (K.comp L).AnswersRealise (w, v) s u := by
  intro o ho
  obtain ⟨p, hp, hKa⟩ := hK o ho
  obtain ⟨o', ho', hLa⟩ := hL p hp
  exact ⟨o', ho', p, hKa, hLa⟩

/-- At the identity convention, soundness is set inclusion the implementation
way round. -/
@[simp] theorem id_answersImplement {I : LangIface} {w : (SimConv.id I).World}
    {s t : Set I.A} : (SimConv.id I).AnswersImplement w t s ↔ t ⊆ s := by
  constructor
  · intro h o ho
    obtain ⟨o', ho', rfl⟩ := h o ho
    exact ho'
  · exact fun h o ho => ⟨o, h ho, rfl⟩

/-- At the identity convention, completeness is set inclusion. -/
@[simp] theorem id_answersRealise {I : LangIface} {w : (SimConv.id I).World}
    {s t : Set I.A} : (SimConv.id I).AnswersRealise w s t ↔ s ⊆ t := by
  constructor
  · intro h o ho
    obtain ⟨o', ho', rfl⟩ := h o ho
    exact ho'
  · exact fun h o ho => ⟨o, h ho, rfl⟩

/-- Composition respects equivalence, by `comp_mono` in both directions. -/
theorem Equiv.comp {R' R : SimConv I₁ I₂} {S' S : SimConv I₂ I₃}
    (hR : R'.Equiv R) (hS : S'.Equiv S) : (R'.comp S').Equiv (R.comp S) :=
  ⟨comp_mono hR.1 hS.1, comp_mono hR.2 hS.2⟩

end SimConv

end Silmaril.Machine
