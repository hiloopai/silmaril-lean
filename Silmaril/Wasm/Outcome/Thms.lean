module

public import Silmaril.Wasm.Outcome.Defs

/-!
# Wasm behaviours as machine outcomes: theorems

Every behaviour relation of `Silmaril.Wasm.Behaviour.Relations` is `Outcome.Rel` at a mode,
along one of the two embeddings of `Silmaril.Wasm.Outcome.Defs`, with the identity observation and
the strict failure axis:

| Wasm relation | embedding | mode | theorem |
| --- | --- | --- | --- |
| `=` | `toOutcome` | `Mode.strict` | `eq_iff_rel` |
| `TrapRefines` | `toOutcome` | `⟨.strict, .allowed⟩` | `trapRefines_iff` |
| `TrapDiv` | `toOutcomeDiv` | `Mode.strict` | `trapDiv_iff` |
| `TrapRefinesDiv` | `toOutcomeDiv` | `⟨.strict, .allowed⟩` | `trapRefinesDiv_iff` |

The two rows that identify traps with divergence need the coarse embedding. Neither is
`Outcome.Rel` along `toOutcome` at **any** mode and observation:

* `not_trapRefinesDiv_rel`: `TrapRefinesDiv .diverges (.returns vs)` holds, but no mode lets a
  divergence implement a return;
* `not_trapDiv_rel`: relating `.traps` to `.diverges` forces `m.exhaustion = .allowed`, which
  then also relates `.traps` to a return.

`TrapDiv` is exactly the kernel of `toOutcomeDiv` (`trapDiv_iff_toOutcomeDiv_eq`). On behaviour
sets, `Behaviours.Refines TrapRefines` and `Behaviours.Refines TrapRefinesDiv` are the demonic
liftings of `Outcome.Rel ⟨.strict, .allowed⟩ Obs.id` to the image sets (`refines_iff`,
`refinesDiv_iff`).

Ported from an earlier development `Silmaril/Wasm/Behaviour/ToOutcome.lean`; the source's
discussion of x86/RV64 observations refers to compiler developments that are not in Silmaril and is
left out.
-/

@[expose] public section

namespace Silmaril.Wasm.Outcome

open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.Behaviour (TrapRefines TrapDiv TrapRefinesDiv)
open Silmaril.Machine.Behaviour (Outcome Obs Mode)

universe u

variable {V : Type u}

/-- `toOutcome` keeps the four Wasm behaviours apart. -/
theorem toOutcome_injective : Function.Injective (toOutcome (V := V)) := by
  intro b b' h
  cases b <;> cases b' <;> simp_all [toOutcome]

/-- `toOutcomeDiv` identifies trap and divergence. -/
theorem toOutcomeDiv_not_injective : ¬ Function.Injective (toOutcomeDiv (V := V)) :=
  fun h => by cases h (a₁ := .traps) (a₂ := .diverges) rfl

/-- **`=` row.** Equality of behaviours is `Outcome.Rel` at the bottom mode along
`toOutcome`. -/
theorem eq_iff_rel {b b' : Behaviour V} :
    b = b' ↔ Outcome.Rel Mode.strict Obs.id (toOutcome b) (toOutcome b') :=
  ⟨fun h => Outcome.Rel.strict_id_iff.mpr (congrArg _ h),
    fun h => toOutcome_injective (Outcome.Rel.strict_id_iff.mp h)⟩

/-- **`TrapRefines` row.** Trap insertion is `Outcome.Rel` at `⟨.strict, .allowed⟩` along
`toOutcome`. -/
theorem trapRefines_iff {b b' : Behaviour V} :
    TrapRefines b b' ↔ Outcome.Rel ⟨.strict, .allowed⟩ Obs.id (toOutcome b) (toOutcome b') := by
  cases b <;> cases b' <;> simp [TrapRefines, toOutcome, Outcome.Rel, Obs.id]

/-- **`TrapDiv` is the kernel of `toOutcomeDiv`.** -/
theorem trapDiv_iff_toOutcomeDiv_eq {b b' : Behaviour V} :
    TrapDiv b b' ↔ toOutcomeDiv b = toOutcomeDiv b' := by
  cases b <;> cases b' <;> simp [TrapDiv, toOutcomeDiv]

/-- **`TrapDiv` row.** Trap ≈ divergence is `Outcome.Rel` at the bottom mode along
`toOutcomeDiv`. -/
theorem trapDiv_iff {b b' : Behaviour V} :
    TrapDiv b b' ↔ Outcome.Rel Mode.strict Obs.id (toOutcomeDiv b) (toOutcomeDiv b') :=
  trapDiv_iff_toOutcomeDiv_eq.trans Outcome.Rel.strict_id_iff.symm

/-- **`TrapRefinesDiv` row.** Trap insertion modulo trap ≈ divergence is `Outcome.Rel` at
`⟨.strict, .allowed⟩` along `toOutcomeDiv`. -/
theorem trapRefinesDiv_iff {b b' : Behaviour V} :
    TrapRefinesDiv b b' ↔
      Outcome.Rel ⟨.strict, .allowed⟩ Obs.id (toOutcomeDiv b) (toOutcomeDiv b') := by
  cases b <;> cases b' <;> simp [TrapRefinesDiv, toOutcomeDiv, Outcome.Rel, Obs.id]

/-- `TrapRefinesDiv` is not `Outcome.Rel` along `toOutcome`, at any mode and observation. -/
theorem not_trapRefinesDiv_rel (m : Mode) (ob : Obs (List V) (List V) Nat Nat Empty Empty) :
    ¬ ∀ b b' : Behaviour V, TrapRefinesDiv b b' ↔
      Outcome.Rel m ob (toOutcome b) (toOutcome b') := by
  intro h
  have hr := (h .diverges (.returns [])).mp (Silmaril.Wasm.Behaviour.trapRefinesDiv_diverges _)
  simp [toOutcome, Outcome.Rel] at hr

/-- `TrapDiv` is not `Outcome.Rel` along `toOutcome`, at any mode and observation. -/
theorem not_trapDiv_rel (m : Mode) (ob : Obs (List V) (List V) Nat Nat Empty Empty) :
    ¬ ∀ b b' : Behaviour V, TrapDiv b b' ↔ Outcome.Rel m ob (toOutcome b) (toOutcome b') := by
  intro h
  have hx : m.exhaustion = .allowed := by
    simpa [toOutcome, Outcome.Rel] using
      (h .traps .diverges).mp Silmaril.Wasm.Behaviour.trapDiv_traps_diverges
  have hbad : TrapDiv (.traps : Behaviour V) (.returns []) :=
    (h .traps (.returns [])).mpr (by simpa [toOutcome, Outcome.Rel] using hx)
  rcases hbad with hbad | ⟨-, hbad⟩ <;> simp at hbad

/-- Demonic trap insertion on behaviour sets is the demonic lifting of
`Outcome.Rel ⟨.strict, .allowed⟩ Obs.id` to the images under `toOutcome`. -/
theorem refines_iff {s t : Set (Behaviour V)} :
    Silmaril.Wasm.Behaviours.Refines TrapRefines s t ↔
      ∀ o ∈ toOutcome '' s, ∃ o' ∈ toOutcome '' t,
        Outcome.Rel ⟨.strict, .allowed⟩ Obs.id o o' := by
  constructor
  · rintro hr _ ⟨b, hb, rfl⟩
    obtain ⟨b', hb', h⟩ := hr b hb
    exact ⟨toOutcome b', ⟨b', hb', rfl⟩, trapRefines_iff.mp h⟩
  · intro h b hb
    obtain ⟨_, ⟨b', hb', rfl⟩, hrel⟩ := h (toOutcome b) ⟨b, hb, rfl⟩
    exact ⟨b', hb', trapRefines_iff.mpr hrel⟩

/-- The same for `TrapRefinesDiv`, along `toOutcomeDiv`. -/
theorem refinesDiv_iff {s t : Set (Behaviour V)} :
    Silmaril.Wasm.Behaviours.Refines TrapRefinesDiv s t ↔
      ∀ o ∈ toOutcomeDiv '' s, ∃ o' ∈ toOutcomeDiv '' t,
        Outcome.Rel ⟨.strict, .allowed⟩ Obs.id o o' := by
  constructor
  · rintro hr _ ⟨b, hb, rfl⟩
    obtain ⟨b', hb', h⟩ := hr b hb
    exact ⟨toOutcomeDiv b', ⟨b', hb', rfl⟩, trapRefinesDiv_iff.mp h⟩
  · intro h b hb
    obtain ⟨_, ⟨b', hb', rfl⟩, hrel⟩ := h (toOutcomeDiv b) ⟨b, hb, rfl⟩
    exact ⟨b', hb', trapRefinesDiv_iff.mpr hrel⟩

end Silmaril.Wasm.Outcome
