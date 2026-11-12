module

public import Silmaril.Raw.Semantics.Behaviour.Machine.SimConv
public import Silmaril.Raw.Semantics.Behaviour.Machine.Behaviour.Refinement

/-!
# The compilation relation against a named simulation convention

`Silmaril/Machine/Behaviour/Refinement.lean` states refinement as

```
Refines mode tgt src Init ob
```

with `Init : S' → S → Prop` and `ob : S' → S → Obs …`. The observation is
indexed by the **initial pair**, because an ABI guarantee mentions entry values
— the callee-saved registers, the return address, the entry stack pointer. That
index pair *is* a Kripke world (`koenig2021compcerto`, Def. 2.5), fixed to the
initial data rather than left free, so it cannot be named, composed, ordered or
reused.

This file restates the same relations against `Silmaril.Machine.SimConv`, where
the world is a parameter. Nothing in `Refinement.lean` changes: `Refines'` and
`Implements'` are new definitions, and `refines'_iff_refines` /
`implements'_iff_implements` prove that the old form is the new one at the
convention `SimConv.ofRefines` / `SimConv.ofImplements`, whose world is exactly
that index pair.

## The interfaces

`iface Q R T F` is the language interface (CompCertO Def. 2.1) whose questions
are drawn from `Q` and whose answers are the `Outcome R T F` of one run. For a
target the questions are machine states; for a source they are whatever the
`Implements` relation calls a `Call`. A convention is then
`SimConv (iface …source…) (iface …target…)`: **specification on the left**, as
in `koenig2021compcerto`.

## Where the mode went

`Mode` does not appear in `Refines'`. A `SimConv`'s answer relation is a
relation on outcomes, so the mode is part of the convention rather than a
separate parameter: `SimConv.ofObs mode q ob` is the convention whose answers
are related by `Outcome.Rel mode (ob w)`. The mode join of `Refines.trans` then
reappears as a *refinement between conventions*,
`SimConv.comp_ofObs_refines`:

```
(ofObs m₁ q₁ ob₁).comp (ofObs m₂ q₂ ob₂)  ⊑  ofObs (m₁ ⊔ m₂) (q₁ · q₂) (ob₂ ∘ ob₁)
```

which is `Outcome.Rel.trans` read as CompCertO Def. 5.1. Composing in the
algebra and then weakening along this refinement (`Refines'.mono`) recovers
`Refines.trans` exactly, mode join and all — see `Refines'.vcomp_obs`.

## What `vcomp` buys

`Refines.trans` takes two side conditions from its caller:

```
hI  : ∀ a c, I a c → ∃ b, I₁ a b ∧ I₂ b c
hob : ∀ a b c, … → (ob₁ a b).comp (ob₂ b c) ≤ ob a c
```

Both are *the definition of* `SimConv.comp`. In `Refines'.vcomp` they are
discharged by `rintro`ing the composite question relation and by
`exact`ing the composite answer relation; there is nothing left for the caller
to supply but the `ReflectsUB` side condition below.

## `ReflectsUB`

The one thing a bare `SimConv` does not know is CompCert's undefined-behaviour
discipline. `Refines.trans` needs the middle state to be safe, which it gets
from `Refines.safe`, which in turn needs "a target `undefined` comes only from
a source `undefined`" (`Outcome.Rel.undefined_left`). On an arbitrary answer
relation that is not automatic, so it is a named property, `SimConv.ReflectsUB`.
Every convention built by `SimConv.ofObs` — hence every convention coming from
an existing `Refines` or `Implements` fact — has it
(`SimConv.ofObs_reflectsUB`), and it is closed under composition
(`SimConv.ReflectsUB.comp`), so in practice it costs nothing.

## Variance

`Refines'` is **monotone** in the convention (`Refines'.mono`): if `K ⊑ L` —
`K` the more general convention — then a simulation at `K` is a simulation at
`L`. This is CompCertO Thm. 5.2's last rule for the **incoming** convention,
where the simulation *receives* related questions and must *produce* related
answers: accepting more questions and promising more about answers is the
harder statement, so it implies the weaker one.

For the **outgoing** convention the variance is the other way round, because
the roles of system and environment are reversed (`koenig2021compcerto`, §3.3).
We have no outgoing convention: `Semantics` has no external-call states, so a
component here is closed and `Refines'` is indexed by one convention, not two.
-/

@[expose] public section

open Silmaril.Machine.Behaviour

namespace Silmaril.Machine

open Behaviour

/-- The language interface of a closed semantics whose questions are drawn
from `Q`: questions are `Q`, answers are the outcomes of one run. For a target
`Q` is the state type; for a source it is the `Call` type of `Implements`. -/
abbrev Behaviour.iface (Q R T F : Type*) : LangIface := ⟨Q, Outcome R T F⟩

namespace SimConv

variable {Q Q' S S' R R' R'' T T' T'' F F' F'' : Type*}

/-! ## Conventions built from an observation -/

/-- The convention a mode and a world-indexed observation determine: `q` is
given outright and answers are related by `Outcome.Rel mode (ob w)`. This is
where `Mode` enters the algebra. -/
def ofObs {W : Type*} (mode : Mode) (q : W → Q → S' → Prop) (ob : W → Obs R' R T' T F' F) :
    SimConv (iface Q R T F) (iface S' R' T' F') where
  World := W
  q := q
  a w o' o := Outcome.Rel mode (ob w) o o'

@[simp] theorem ofObs_World {W : Type*} (mode : Mode) (q : W → Q → S' → Prop)
    (ob : W → Obs R' R T' T F' F) : (ofObs mode q ob).World = W := rfl

@[simp] theorem ofObs_q {W : Type*} (mode : Mode) (q : W → Q → S' → Prop)
    (ob : W → Obs R' R T' T F' F) (w : W) : (ofObs mode q ob).q w = q w := rfl

@[simp] theorem ofObs_a {W : Type*} (mode : Mode) (q : W → Q → S' → Prop)
    (ob : W → Obs R' R T' T F' F) (w : W) (o' : Outcome R T F) (o : Outcome R' T' F') :
    (ofObs mode q ob).a w o' o ↔ Outcome.Rel mode (ob w) o o' := Iff.rfl

/-- **The world of an `Implements` fact is its index pair.** The convention a
`Silmaril.Machine.Behaviour.Implements` instance carries, with the world taken
to be the pair `(c, t)` that `ob` is already indexed by. -/
def ofImplements (mode : Mode) (Rep : Q → S' → Prop) (ob : Q → S' → Obs R' R T' T F' F) :
    SimConv (iface Q R T F) (iface S' R' T' F') :=
  ofObs (W := Q × S') mode (fun w c t => c = w.1 ∧ t = w.2 ∧ Rep w.1 w.2) (fun w => ob w.1 w.2)

/-- **The world of a `Refines` fact is its initial pair.** The convention a
`Silmaril.Machine.Behaviour.Refines` instance carries. -/
def ofRefines (mode : Mode) (Init : S' → S → Prop) (ob : S' → S → Obs R' R T' T F' F) :
    SimConv (iface S R T F) (iface S' R' T' F') :=
  ofObs (W := S' × S) mode (fun w s t => s = w.2 ∧ t = w.1 ∧ Init w.1 w.2)
    (fun w => ob w.1 w.2)

/-! ## Reflecting undefined behaviour -/

/-- A convention reflects source undefined behaviour: a target `undefined` is
implemented only by a source `undefined`. This is the CompCert discipline that
makes refinement transitive, and the one thing an arbitrary `SimConv` does not
already know. -/
def ReflectsUB (K : SimConv (iface Q R T F) (iface S' R' T' F')) : Prop :=
  ∀ w o, K.a w o .undefined → o = .undefined

/-- Every convention built from an observation reflects undefined behaviour,
by `Outcome.Rel.undefined_left`. -/
theorem ofObs_reflectsUB {W : Type*} (mode : Mode) (q : W → Q → S' → Prop)
    (ob : W → Obs R' R T' T F' F) : (ofObs mode q ob).ReflectsUB :=
  fun _ _ h => Outcome.Rel.undefined_left.mp h

theorem ofImplements_reflectsUB (mode : Mode) (Rep : Q → S' → Prop)
    (ob : Q → S' → Obs R' R T' T F' F) : (ofImplements mode Rep ob).ReflectsUB :=
  ofObs_reflectsUB mode _ _

theorem ofRefines_reflectsUB (mode : Mode) (Init : S' → S → Prop)
    (ob : S' → S → Obs R' R T' T F' F) : (ofRefines mode Init ob).ReflectsUB :=
  ofObs_reflectsUB mode _ _

/-- Reflecting undefined behaviour is closed under composition. -/
theorem ReflectsUB.comp {K : SimConv (iface Q R T F) (iface Q' R' T' F')}
    {L : SimConv (iface Q' R' T' F') (iface S' R'' T'' F'')} (hK : K.ReflectsUB)
    (hL : L.ReflectsUB) : (K.comp L).ReflectsUB := by
  rintro w o ⟨p, hKp, hLp⟩
  exact hK w.1 o (hL w.2 p hLp ▸ hKp)

/-! ## The mode join, as a refinement of conventions -/

/-- **Where `m₁ ⊔ m₂` comes from.** Composing two observation conventions is
more general (CompCertO Def. 5.1) than the single observation convention at the
join of the modes with the composite observation. This is `Outcome.Rel.trans`
read as a refinement, and together with `Refines'.mono` it is what recovers the
mode join of `Refines.trans` from `SimConv.comp`. -/
theorem comp_ofObs_refines {W₁ W₂ : Type*} (m₁ m₂ : Mode) (q₁ : W₁ → Q → Q' → Prop)
    (ob₁ : W₁ → Obs R' R T' T F' F) (q₂ : W₂ → Q' → S' → Prop)
    (ob₂ : W₂ → Obs R'' R' T'' T' F'' F') :
    ((ofObs m₁ q₁ ob₁).comp (ofObs m₂ q₂ ob₂)).Refines
      (ofObs (W := W₁ × W₂) (m₁ ⊔ m₂) (fun w => Relation.Comp (q₁ w.1) (q₂ w.2))
        (fun w => (ob₂ w.2).comp (ob₁ w.1))) := by
  refine Refines.of_map _root_.id (fun _ _ _ h => h) ?_
  rintro w p r ⟨m, h₁, h₂⟩
  exact (h₂.trans h₁).mono (by rw [sup_comm]) le_rfl

end SimConv

namespace Behaviour

variable {Q S S' S'' R R' R'' T T' T'' F F' F'' : Type*}

/-! ## The compilation relation, at a convention -/

/-- `tgt` implements `src` at the convention `K`: every target state answering
a question the convention relates to a call, whose source entry state is safe,
has only behaviours the convention relates back.

This is `Implements` with the index pair freed into a Kripke world. -/
def Implements' (src : Semantics S R T F) (tgt : Semantics S' R' T' F') (entry : Q → S)
    (K : SimConv (iface Q R T F) (iface S' R' T' F')) : Prop :=
  ∀ w c t, K.q w c t → src.Safe (entry c) → ∀ o, tgt.Beh t o →
    ∃ o', src.Beh (entry c) o' ∧ K.a w o' o

/-- `tgt` refines `src` at the convention `K`: the case of `Implements'` in
which the source questions are source states. -/
def Refines' (tgt : Semantics S' R' T' F') (src : Semantics S R T F)
    (K : SimConv (iface S R T F) (iface S' R' T' F')) : Prop :=
  Implements' src tgt _root_.id K

/-! ### Agreement with the existing relations -/

/-- **`Refines` is `Refines'` at the convention whose world is the initial
pair.** No existing statement changes; this says the old form is a special
case of the new one. -/
theorem refines'_iff_refines {tgt : Semantics S' R' T' F'} {src : Semantics S R T F}
    {m : Mode} {Init : S' → S → Prop} {ob : S' → S → Obs R' R T' T F' F} :
    Refines' tgt src (SimConv.ofRefines m Init ob) ↔ Refines m tgt src Init ob := by
  constructor
  · intro h t s hI hs o hb
    exact h (t, s) s t ⟨rfl, rfl, hI⟩ hs o hb
  · rintro h ⟨t, s⟩ s' t' ⟨rfl, rfl, hI⟩ hs o hb
    exact h _ _ hI hs o hb

/-- **`Implements` is `Implements'` at the convention whose world is the pair
`(c, t)` the observation is indexed by.** -/
theorem implements'_iff_implements {src : Semantics S R T F} {tgt : Semantics S' R' T' F'}
    {m : Mode} {entry : Q → S} {Rep : Q → S' → Prop} {ob : Q → S' → Obs R' R T' T F' F} :
    Implements' src tgt entry (SimConv.ofImplements m Rep ob) ↔
      Implements m src tgt entry Rep ob := by
  constructor
  · intro h c t hRep hs o hb
    exact h (c, t) c t ⟨rfl, rfl, hRep⟩ hs o hb
  · rintro h ⟨c, t⟩ c' t' ⟨rfl, rfl, hRep⟩ hs o hb
    exact h _ _ hRep hs o hb

/-! ### Safety -/

/-- A safe source state forces a safe target state, for a convention that
reflects undefined behaviour. -/
theorem Implements'.safe {src : Semantics S R T F} {tgt : Semantics S' R' T' F'}
    {entry : Q → S} {K : SimConv (iface Q R T F) (iface S' R' T' F')}
    (h : Implements' src tgt entry K) (hub : K.ReflectsUB) {w : K.World} {c : Q} {t : S'}
    (hq : K.q w c t) (hs : src.Safe (entry c)) : tgt.Safe t := fun hu => by
  obtain ⟨o', hb, ha⟩ := h w c t hq hs _ hu
  exact hs (hub w o' ha ▸ hb)

theorem Refines'.safe {tgt : Semantics S' R' T' F'} {src : Semantics S R T F}
    {K : SimConv (iface S R T F) (iface S' R' T' F')} (h : Refines' tgt src K)
    (hub : K.ReflectsUB) {w : K.World} {s : S} {t : S'} (hq : K.q w s t) (hs : src.Safe s) :
    tgt.Safe t :=
  Implements'.safe h hub hq hs

/-! ### Monotonicity: CompCertO Thm. 5.2's last rule -/

/-- **Monotonicity in the convention.** If `K` is the more general convention
(`K.Refines L`), a simulation at `K` is a simulation at `L`. This is the
incoming half of CompCertO Thm. 5.2's last rule, and the only proof here that
needs the full `∀∃∀` unfolding of `SimConv.Refines`. -/
theorem Implements'.mono {src : Semantics S R T F} {tgt : Semantics S' R' T' F'}
    {entry : Q → S} {K L : SimConv (iface Q R T F) (iface S' R' T' F')}
    (hKL : K.Refines L) (h : Implements' src tgt entry K) : Implements' src tgt entry L := by
  intro w c t hq hs o hb
  obtain ⟨u, hu, hua⟩ := hKL w c t hq
  obtain ⟨o', hb', ha⟩ := h u c t hu hs o hb
  exact ⟨o', hb', hua o' o ha⟩

theorem Refines'.mono {tgt : Semantics S' R' T' F'} {src : Semantics S R T F}
    {K L : SimConv (iface S R T F) (iface S' R' T' F')} (hKL : K.Refines L)
    (h : Refines' tgt src K) : Refines' tgt src L :=
  Implements'.mono hKL h

/-! ### Vertical composition -/

/-- **Vertical composition.** The `hI` and `hob` side conditions of
`Refines.trans` are gone: the composite question relation and the composite
answer relation *are* `SimConv.comp`, so the proof is the two simulations run
in sequence and the middle outcome paired up. Only the undefined-behaviour
discipline is left as a hypothesis, and `SimConv.ofObs_reflectsUB` discharges
it for every convention that comes from an observation. -/
theorem Implements'.vcomp {src : Semantics S R T F} {mid : Semantics S' R' T' F'}
    {tgt : Semantics S'' R'' T'' F''} {entry : Q → S}
    {K : SimConv (iface Q R T F) (iface S' R' T' F')}
    {L : SimConv (iface S' R' T' F') (iface S'' R'' T'' F'')}
    (hK : Implements' src mid entry K) (hL : Refines' tgt mid L) (hub : K.ReflectsUB) :
    Implements' src tgt entry (K.comp L) := by
  rintro ⟨wK, wL⟩ c t ⟨u, hKq, hLq⟩ hs o hb
  obtain ⟨p, hp, hLa⟩ := hL wL u t hLq (hK.safe hub hKq hs) o hb
  obtain ⟨o', hb', hKa⟩ := hK wK c u hKq hs p hp
  exact ⟨o', hb', p, hKa, hLa⟩

/-- **The schema a machine backend instantiates.** An existing `Implements`
fact becomes an `Implements'` fact at a convention `K` pinned to the world
`w₀`, given one bridge: every outcome pair the observation relates is one `K`
relates at `w₀`.

The `key` argument re-keys calls to questions. A backend's `Call` type
carries target-side data the source question does not mention — the argument
*words*, the registers the loader does not set — so the question relation
existentially quantifies it, and `hentry` says the two agree on the source
entry state. -/
theorem Implements'.of_implements {Call : Type*} {m : Mode} {src : Semantics S R T F}
    {tgt : Semantics S' R' T' F'} {entry : Call → S} {Rep : Call → S' → Prop}
    {ob : Call → S' → Obs R' R T' T F' F}
    {K : SimConv (iface Q R T F) (iface S' R' T' F')} (key : Call → Q) (entry' : Q → S)
    (w₀ : K.World) (hentry : ∀ c, entry' (key c) = entry c)
    (hi : Implements m src tgt entry Rep ob)
    (ha : ∀ c t o o', Rep c t → Outcome.Rel m (ob c t) o o' → K.a w₀ o' o) :
    Implements' src tgt entry' (K.pin w₀ (fun x y => ∃ c, key c = x ∧ Rep c y)) := by
  rintro w x t ⟨hw, c, hkey, hRep⟩ hs o hb
  have hx : entry' x = entry c := hkey ▸ hentry c
  rw [hx] at hs ⊢
  obtain ⟨o', hb', hrel⟩ := hi c t hRep hs o hb
  refine ⟨o', hb', ?_⟩
  show K.a w o' o
  rw [hw]
  exact ha c t o o' hRep hrel

/-- Vertical composition of refinements: `K` from source to middle, `L` from
middle to target, composed by `SimConv.comp`. -/
theorem Refines'.vcomp {src : Semantics S R T F} {mid : Semantics S' R' T' F'}
    {tgt : Semantics S'' R'' T'' F''} {K : SimConv (iface S R T F) (iface S' R' T' F')}
    {L : SimConv (iface S' R' T' F') (iface S'' R'' T'' F'')}
    (hK : Refines' mid src K) (hL : Refines' tgt mid L) (hub : K.ReflectsUB) :
    Refines' tgt src (K.comp L) :=
  Implements'.vcomp hK hL hub

/-- **`Refines.trans` recovered, mode join and all.** Composing two
observation conventions and then weakening along `SimConv.comp_ofObs_refines`
lands at the single observation convention in the join of the modes. The `hI`
and `hob` obligations of `Refines.trans` have become, respectively, the
question half of `SimConv.comp` and the inequality
`SimConv.comp_ofObs_refines`. -/
theorem Refines'.vcomp_obs {W₁ W₂ : Type*} {src : Semantics S R T F}
    {mid : Semantics S' R' T' F'} {tgt : Semantics S'' R'' T'' F''} {m₁ m₂ : Mode}
    {q₁ : W₁ → S → S' → Prop} {ob₁ : W₁ → Obs R' R T' T F' F}
    {q₂ : W₂ → S' → S'' → Prop} {ob₂ : W₂ → Obs R'' R' T'' T' F'' F'}
    (hK : Refines' mid src (SimConv.ofObs m₁ q₁ ob₁))
    (hL : Refines' tgt mid (SimConv.ofObs m₂ q₂ ob₂)) :
    Refines' tgt src (SimConv.ofObs (W := W₁ × W₂) (m₁ ⊔ m₂)
      (fun w => Relation.Comp (q₁ w.1) (q₂ w.2)) (fun w => (ob₂ w.2).comp (ob₁ w.1))) :=
  Refines'.mono (SimConv.comp_ofObs_refines m₁ m₂ q₁ ob₁ q₂ ob₂)
    (hK.vcomp hL (SimConv.ofObs_reflectsUB m₁ q₁ ob₁))

end Behaviour

end Silmaril.Machine
