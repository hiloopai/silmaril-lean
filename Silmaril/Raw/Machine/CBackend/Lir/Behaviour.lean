module

public import Silmaril.Machine.CBackend.Lir.Alloc.Defs
public import Silmaril.Machine.CBackend.Behaviour.Refinement.Defs

/-!
# Lir as a `Behaviour.Semantics`

`Lir.sem p` presents the small-step semantics of a Lir program `p` in the
shared vocabulary of `Silmaril.Machine.Behaviour` . A step is a running
step (`Lir.Step`), and a state whose `step` does not run is final:

* `.returned vs m` shows `returned (vs, m)`;
* `.trapped m` shows `trapped m`;
* `.stuck` shows `undefined`: stuck states are source undefined behaviour.

Lir has no faults (`F = Empty`) and no resource bound, so `exhausted` is never
a behaviour of a Lir state. `beh_iff_behaves` identifies the behaviours of
`sem p` with `Lir.Behaves` through `Behavior.toOutcome`, and the semantics is
deterministic (`sem_deterministic`) with progress (`sem_progress`).

Two refinements are stated in the strict mode with the identity observation:

* `ForwardSimulation.refines`: a forward simulation into another Lir program
  whose `Returned` and `Trapped` are Lir final results (`IntoLir`) is a
  refinement from matched pairs (`Refines.of_forward`, using target
  determinism);
* `Alloc.spill_refines`: spilling with a valid allocation refines the original
  program from the start states of the same call.

Both follow from the existing theorems (`ForwardSimulation.behaves`,
`Alloc.spill_behaves`); the `Safe` premise of `Refines` is what excludes the
stuck behaviour, which those theorems leave out.
-/

@[expose] public section

namespace Silmaril.Machine.Lir

open Relation
open Silmaril.Machine.Behaviour (Semantics Refines Mode Obs)

variable {R : Type}

/-- The outcome shown by a final `step` result; `none` for a running step. -/
def Result.toOutcome? : Result R → Option (Behaviour.Outcome (List Word × Memory) Memory Empty)
  | .running _ => none
  | .returned vs m => some (.returned (vs, m))
  | .trapped m => some (.trapped m)
  | .stuck => some .undefined

/-- The outcome of a whole-program behaviour. -/
def Behavior.toOutcome : Behavior → Behaviour.Outcome (List Word × Memory) Memory Empty
  | .returned vs m => .returned (vs, m)
  | .trapped m => .trapped m
  | .stuck => .undefined
  | .diverges => .diverges

theorem Behavior.toOutcome_injective : Function.Injective Behavior.toOutcome := by
  intro a b h
  cases a <;> cases b <;> simp_all [Behavior.toOutcome]

variable [DecidableEq R]

/-- A Lir program as a semantics: running steps, and the final result of a
state whose step does not run. -/
def sem (p : Prog R) : Semantics (State R) (List Word × Memory) Memory Empty where
  step := Step p
  final s o := (step p s).toOutcome? = some o

variable {p : Prog R}

@[simp] theorem sem_step : (sem p).step = Step p := rfl

theorem sem_final {s : State R} {o : Behaviour.Outcome (List Word × Memory) Memory Empty} :
    (sem p).final s o ↔ (step p s).toOutcome? = some o := Iff.rfl

theorem sem_deterministic (p : Prog R) : (sem p).Deterministic where
  step_unique := step_rightUnique p
  final_unique _ _ _ h h' := Option.some.inj (h.symm.trans h')
  final_stop s o h t ht := by
    change (step p s).toOutcome? = some o at h
    rw [show step p s = .running t from ht] at h
    cases h

theorem sem_progress (p : Prog R) : (sem p).Progress := by
  intro s
  cases h : step p s with
  | running t => exact .inl ⟨t, h⟩
  | returned vs m => exact .inr ⟨.returned (vs, m), by rw [sem_final, h]; rfl, nofun⟩
  | trapped m => exact .inr ⟨.trapped m, by rw [sem_final, h]; rfl, nofun⟩
  | stuck => exact .inr ⟨.undefined, by rw [sem_final, h]; rfl, nofun⟩

/-- The behaviours of `sem p` are the Lir behaviours. -/
theorem beh_iff_behaves {s : State R} {b : Behavior} :
    (sem p).Beh s b.toOutcome ↔ Behaves p s b := by
  cases b with
  | diverges => exact Iff.rfl
  | returned vs m =>
    refine exists_congr fun t => and_congr Iff.rfl ?_
    rw [sem_final]
    cases step p t <;> simp [Result.toOutcome?, Behavior.toOutcome]
  | trapped m =>
    refine exists_congr fun t => and_congr Iff.rfl ?_
    rw [sem_final]
    cases step p t <;> simp [Result.toOutcome?, Behavior.toOutcome]
  | stuck =>
    refine exists_congr fun t => and_congr Iff.rfl ?_
    rw [sem_final]
    cases step p t <;> simp [Result.toOutcome?, Behavior.toOutcome]

/-- Every behaviour of `sem p` is the outcome of a Lir behaviour. -/
theorem beh_iff {s : State R} {o : Behaviour.Outcome (List Word × Memory) Memory Empty} :
    (sem p).Beh s o ↔ ∃ b, b.toOutcome = o ∧ Behaves p s b := by
  refine ⟨fun h => ?_, fun ⟨b, hb, h⟩ => hb ▸ beh_iff_behaves.mpr h⟩
  cases o with
  | returned r => exact ⟨.returned r.1 r.2, rfl, beh_iff_behaves.mp h⟩
  | trapped m => exact ⟨.trapped m, rfl, beh_iff_behaves.mp h⟩
  | undefined => exact ⟨.stuck, rfl, beh_iff_behaves.mp h⟩
  | diverges => exact ⟨.diverges, rfl, beh_iff_behaves.mp h⟩
  | faulted e => exact e.elim
  | exhausted =>
    obtain ⟨t, -, ht⟩ := h
    revert ht
    rw [sem_final]
    cases step p t <;> simp [Result.toOutcome?]

/-- Lir has no resource bound: exhaustion is never a behaviour. -/
theorem not_beh_exhausted {s : State R} : ¬ (sem p).Beh s .exhausted := by
  intro h
  obtain ⟨b, hb, -⟩ := beh_iff.mp h
  cases b <;> cases hb

/-- A safe state does not get stuck. -/
theorem not_stuck_of_safe {s : State R} (h : (sem p).Safe s) : ¬ Behaves p s .stuck :=
  fun hb => h (beh_iff_behaves (b := .stuck) |>.mpr hb)

/-- A safe state's behaviour is a Lir behaviour other than `stuck`. -/
theorem beh_of_safe {s : State R} (h : (sem p).Safe s)
    {o : Behaviour.Outcome (List Word × Memory) Memory Empty} (ho : (sem p).Beh s o) :
    ∃ b, b.toOutcome = o ∧ Behaves p s b ∧ b ≠ .stuck := by
  obtain ⟨b, rfl, hb⟩ := beh_iff.mp ho
  exact ⟨b, rfl, hb, by rintro rfl; exact not_stuck_of_safe h hb⟩

/-- Every state has a behaviour. -/
theorem beh_exists (s : State R) :
    ∃ o, (sem p).Beh s o :=
  Semantics.Beh.exists (sem_progress p) s

/-! ## Lir-to-Lir refinement -/

/-- **A forward simulation into Lir is a refinement.** From every matched pair
whose source state is safe, each behaviour of the target program is a
behaviour of the source program. -/
theorem ForwardSimulation.refines {P : Type} [DecidableEq P] {q : Prog P}
    (sim : ForwardSimulation p (LirTarget q)) (lir : sim.IntoLir) :
    Refines Mode.strict (sem q) (sem p) (fun t s => sim.Match s t) (fun _ _ => Obs.id) := by
  refine Refines.of_forward (sem_deterministic q) (fun _ s _ _ => beh_exists s) ?_
  intro t s hm hs o ho
  obtain ⟨b, rfl, hb, hns⟩ := beh_of_safe hs ho
  exact ⟨b.toOutcome, beh_iff_behaves.mpr (sim.behaves lir hm hb hns),
    Behaviour.Outcome.Rel.refl Obs.isRefl_id _ _⟩

/-- **Spilling refines the original program.** For a valid allocation, from
start states of the same function, arguments and memory whose source state is
safe, every behaviour of the spilled program is a behaviour of the original
program. -/
theorem Alloc.spill_refines {V P : Type} [DecidableEq V] [DecidableEq P] {a : Alloc.Allocation V P}
    (hv : a.Valid) {p : Prog V} :
    Refines Mode.strict (sem (Alloc.spill a p)) (sem p)
      (fun t s => ∃ f args mem, p.start f args mem = some s ∧
        (Alloc.spill a p).start f args mem = some t)
      (fun _ _ => Obs.id) := by
  refine Refines.of_forward (sem_deterministic _) (fun _ s _ _ => beh_exists s) ?_
  rintro t s ⟨f, args, mem, hs, ht⟩ hsafe o ho
  obtain ⟨b, rfl, hb, hns⟩ := beh_of_safe hsafe ho
  obtain ⟨t', ht', hb'⟩ := Alloc.spill_behaves hv hs hb hns
  rw [ht] at ht'
  cases ht'
  exact ⟨b.toOutcome, beh_iff_behaves.mpr hb', Behaviour.Outcome.Rel.refl Obs.isRefl_id _ _⟩

end Silmaril.Machine.Lir
