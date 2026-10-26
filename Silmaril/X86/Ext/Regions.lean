module

public import Silmaril.X86.Ext.Behaviour

/-!
# Execution keeps the memory map

No instruction of `X86.Ext` maps or unmaps memory: every store goes through
`Memory.writeBytes`, which changes bytes only. So a retiring step and a
returning step keep `memory.regions` (`step_retired_regions`,
`step_returned_regions`), and so does every run of `Ext.sem`
(`reach_regions`). A behaviour's returned or trapped state therefore has the
regions of the state the run started from (`beh_returned_regions`,
`beh_trapped_regions`).
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Reg Word State MState pushWord popWord)
open Silmaril.Process (Memory)
open Relation

theorem storeN_regions {m m' : Memory} {a : Word} {k : Nat} {v : Word}
    (h : storeN m a k v = some m') : m'.regions = m.regions :=
  (storeN_writesOnly h).1

/-- Results of an instruction body whose memory has the regions of `m`. -/
def KeepsRegions (m : Memory) (o : Option (State × Memory)) : Prop :=
  ∀ s m', o = some (s, m') → m'.regions = m.regions

theorem keepsRegions_same (m : Memory) (s : State) : KeepsRegions m (some (s, m)) := by
  rintro _ _ ⟨⟩
  rfl

theorem keepsRegions_map_same {α : Type} (m : Memory) (o : Option α) (f : α → State) :
    KeepsRegions m (o.map fun x => (f x, m)) := by
  rintro s m' h
  cases o <;> simp_all

theorem keepsRegions_store {m : Memory} {a : Word} {k : Nat} {v : Word} (s : State) :
    KeepsRegions m ((storeN m a k v).map fun after => (s, after)) := by
  rintro s' m' h
  cases hs : storeN m a k v with
  | none => simp [hs] at h
  | some m'' =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact storeN_regions hs

theorem keepsRegions_writeRM (sz : Sz) (op : RM) (v : BitVec sz.bits) (s : State) (m : Memory)
    (next : Word) : KeepsRegions m (writeRM sz op v s m next) := by
  cases op with
  | reg r => exact keepsRegions_same _ _
  | mem a => exact keepsRegions_store _

theorem keepsRegions_writeNarrow (n : Narrow) (op : RM) (v : BitVec n.bits) (s : State)
    (m : Memory) (next : Word) : KeepsRegions m (writeNarrow n op v s m next) := by
  cases op with
  | reg r => exact keepsRegions_same _ _
  | mem a => exact keepsRegions_store _

theorem keepsRegions_writeRM8 (op : RM) (v : BitVec 8) (s : State) (m : Memory) (next : Word) :
    KeepsRegions m (writeRM8 op v s m next) := by
  cases op with
  | reg r => exact keepsRegions_same _ _
  | mem a => exact keepsRegions_store _

theorem keepsRegions_map {m : Memory} {o : Option (State × Memory)} (h : KeepsRegions m o)
    (f : State × Memory → State) : KeepsRegions m (o.map fun r => (f r, r.2)) := by
  rintro s m' h'
  cases ho : o with
  | none => simp [ho] at h'
  | some r =>
    simp only [ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨-, rfl⟩ := h'
    exact h _ _ ho

theorem keepsRegions_aluStep (sz : Sz) (op : AluOp) (dst : RM) (y : BitVec sz.bits) (s : State)
    (m : Memory) (next : Word) : KeepsRegions m (aluStep sz op dst y s m next) := by
  unfold aluStep
  split
  · rintro _ _ ⟨⟩
  · split
    · exact keepsRegions_same _ _
    · exact keepsRegions_map (keepsRegions_writeRM sz dst _ s m next) _

theorem keepsRegions_aluStepR (sz : Sz) (op : AluOp) (dst : Reg) (src : RM) (s : State)
    (m : Memory) (next : Word) : KeepsRegions m (aluStepR sz op dst src s m next) := by
  unfold aluStepR
  split
  · rintro _ _ ⟨⟩
  · split <;> exact keepsRegions_same _ _

theorem keepsRegions_pushWord (s : State) (m : Memory) (v : Word) :
    KeepsRegions m (pushWord s m v) := by
  rintro s' m' h
  exact (X86.pushWord_writesOnly h).1

theorem retire_regions {m : Memory} {next : Word} {o : Option (State × Memory)}
    (h : KeepsRegions m o) {core : State} {m' : Memory} (he : retire next o = .ok core m') :
    m'.regions = m.regions := by
  unfold retire at he
  split at he
  · cases he
    exact h _ _ rfl
  · cases he

theorem keepsRegions_pushWord' {s : State} {m : Memory} {v : Word} {t : State} {m' : Memory}
    (h : pushWord s m v = some (t, m')) : m'.regions = m.regions :=
  keepsRegions_pushWord s m v t m' h

/-- **An instruction keeps the memory map.** -/
theorem exec_regions {i : Instr} {s : State} {m : Memory} {len : Nat} {core : State}
    {m' : Memory} (h : exec i s m len = .ok core m') : m'.regions = m.regions := by
  cases i
  all_goals try (unfold exec at h; dsimp only at h)
  all_goals repeat' split at h
  all_goals first
    | contradiction
    | (cases h; done)
    | (cases h; rfl)
    | (cases h; exact keepsRegions_pushWord' ‹_›)
    | (refine retire_regions ?_ h
       first
        | with_reducible apply keepsRegions_same
        | with_reducible apply keepsRegions_map_same
        | with_reducible apply keepsRegions_writeRM
        | with_reducible apply keepsRegions_writeNarrow
        | with_reducible apply keepsRegions_writeRM8
        | with_reducible apply keepsRegions_aluStep
        | with_reducible apply keepsRegions_aluStepR
        | with_reducible apply keepsRegions_pushWord
        | with_reducible apply keepsRegions_store
        | (with_reducible apply keepsRegions_map; with_reducible apply keepsRegions_writeRM)
        | exact keepsRegions_pushWord _ _ _
        | apply keepsRegions_map_same)

theorem step_ok_regions {exit : Word} {m : MState} {final : MState}
    (h : step exit m = .retired final ∨ step exit m = .returned final) :
    final.memory.regions = m.memory.regions := by
  unfold step at h
  split at h
  · simp at h
  · simp at h
  · split at h
    · rename_i he
      split at h <;> simp only [Outcome.retired.injEq, Outcome.returned.injEq, reduceCtorEq,
        or_false, false_or] at h <;> subst h <;> exact exec_regions he
    all_goals simp at h

/-- A retiring step keeps the memory map. -/
theorem step_retired_regions {exit : Word} {m m' : MState} (h : step exit m = .retired m') :
    m'.memory.regions = m.memory.regions :=
  step_ok_regions (.inl h)

/-- A returning step keeps the memory map. -/
theorem step_returned_regions {exit : Word} {m final : MState} (h : step exit m = .returned final) :
    final.memory.regions = m.memory.regions :=
  step_ok_regions (.inr h)

/-- A run of `Ext.sem` keeps the memory map. -/
theorem reach_regions {Exhausted : MState → Prop} {a b : Word × MState}
    (h : ReflTransGen (sem Exhausted).step a b) : b.2.memory.regions = a.2.memory.regions := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (step_retired_regions hs.2).trans ih

/-- A returned behaviour has the memory map of the start. -/
theorem beh_returned_regions {Exhausted : MState → Prop} {exit : Word} {m final : MState}
    (h : (sem Exhausted).Beh (exit, m) (.returned final)) :
    final.memory.regions = m.memory.regions := by
  obtain ⟨u, hu, hf⟩ := h
  cases hf with
  | returned hs => exact (step_returned_regions hs).trans (reach_regions hu)

/-- A trapped behaviour has the memory map of the start. -/
theorem beh_trapped_regions {Exhausted : MState → Prop} {exit : Word} {m t : MState}
    (h : (sem Exhausted).Beh (exit, m) (.trapped t)) : t.memory.regions = m.memory.regions := by
  obtain ⟨u, hu, hf⟩ := h
  cases hf with
  | trapped => exact reach_regions hu

end Silmaril.X86.Ext
