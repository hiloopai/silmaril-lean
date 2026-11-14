module

public import Silmaril.Games.Abstract.Machine.Defs
public import Silmaril.Games.Abstract.Game.Thms
public import Mathlib.Data.List.Induction

/-!
# Abstract state machines: proofs

Proofs for `Silmaril.Games.Abstract.Machine.Thms`: runs split along
concatenation, traces are prefix-closed, strategy-deterministic machines
denote deterministic trace models, bisimilar machines have the same traces, and
deterministic labelled transition systems with the same traces are bisimilar.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.Machine

open Silmaril.Games.Abstract Silmaril.Games.Abstract.Machine

universe u

variable {G : Game.{u}} {M N : Machine G}

theorem Run.append {x y z : M.State} {s t : List G.Move} (h₁ : M.Run x s y) (h₂ : M.Run y t z) :
    M.Run x (s ++ t) z := by
  induction h₁ with
  | nil => exact h₂
  | tau h _ ih => exact .tau h (ih h₂)
  | vis h _ ih => exact .vis h (ih h₂)

/-- A run through a nonempty list: silent steps, the first move, the rest. -/
theorem Run.cons_inv {x z : M.State} {o : G.Move} {s : List G.Move} (h : M.Run x (o :: s) z) :
    ∃ x₁ y₁, M.Run x [] x₁ ∧ M.step x₁ (some o) y₁ ∧ M.Run y₁ s z := by
  generalize hl : o :: s = l at h
  induction h with
  | nil => cases hl
  | tau h _ ih =>
    obtain ⟨x₁, y₁, h₁, h₂, h₃⟩ := ih hl
    exact ⟨x₁, y₁, .tau h h₁, h₂, h₃⟩
  | vis h r _ =>
    cases hl
    exact ⟨_, _, .nil _, h, r⟩

theorem Run.of_append {x z : M.State} {s t : List G.Move} (h : M.Run x (s ++ t) z) :
    ∃ y, M.Run x s y ∧ M.Run y t z := by
  induction s generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons o s ih =>
    obtain ⟨x₁, y₁, h₁, h₂, h₃⟩ := Run.cons_inv h
    obtain ⟨y, h₄, h₅⟩ := ih h₃
    exact ⟨y, by simpa using Run.append h₁ (.vis h₂ h₄), h₅⟩

theorem tracesFrom_of_prefix {x : M.State} {s t : List G.Move} (ht : t ∈ M.tracesFrom x)
    (h : s <+: t) : s ∈ M.tracesFrom x := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨z, hz⟩ := ht
  obtain ⟨y, hy, -⟩ := Run.of_append hz
  exact ⟨y, hy⟩

/-! ## Strategy determinism -/

/-- Under `SDet`, two runs over the same moves end on one chain of silent steps. -/
theorem SDet.run_comparable (hM : M.SDet) {x y y' : M.State} {s : List G.Move}
    (h₁ : M.Run x s y) (h₂ : M.Run x s y') : M.Run y [] y' ∨ M.Run y' [] y := by
  induction h₁ generalizing y' with
  | nil => exact .inl h₂
  | tau h r ih =>
    cases h₂ with
    | nil => exact .inr (.tau h r)
    | tau h' r' =>
      obtain ⟨-, rfl⟩ := hM.nonO h h' trivial trivial
      exact ih r'
    | @vis _ _ _ o _ h' r' =>
      by_cases ho : G.IsO o
      · exact absurd trivial (hM.oStable h' ho h)
      · exact absurd (hM.nonO h h' trivial ho).1 (by simp)
  | @vis _ _ _ o _ h r ih =>
    cases h₂ with
    | tau h' r' =>
      by_cases ho : G.IsO o
      · exact absurd trivial (hM.oStable h ho h')
      · exact absurd (hM.nonO h' h trivial ho).1 (by simp)
    | vis h' r' =>
      by_cases ho : G.IsO o
      · obtain rfl := hM.oDet h h' ho
        exact ih r'
      · obtain ⟨-, rfl⟩ := hM.nonO h h' ho ho
        exact ih r'

/-- A state with a Proponent move has no silent successor. -/
theorem SDet.eq_of_tau (hM : M.SDet) {u v w : M.State} {p : G.Move} (hp : ¬ G.IsO p)
    (hu : M.step u (some p) w) (h : M.Run u [] v) : u = v := by
  cases h with
  | nil => rfl
  | tau h _ => exact absurd (hM.nonO hu h hp trivial).1 (by simp)

theorem SDet.traces_det (hM : M.SDet) {x : M.State} {s : List G.Move} {p q : G.Move}
    (hp : s ++ [p] ∈ M.tracesFrom x) (hq : s ++ [q] ∈ M.tracesFrom x) (hpo : ¬ G.IsO p)
    (hqo : ¬ G.IsO q) : p = q := by
  obtain ⟨_, hp⟩ := hp
  obtain ⟨_, hq⟩ := hq
  obtain ⟨y, hy, hy'⟩ := Run.of_append hp
  obtain ⟨z, hz, hz'⟩ := Run.of_append hq
  obtain ⟨u, u', hu, hu', -⟩ := Run.cons_inv hy'
  obtain ⟨v, v', hv, hv', -⟩ := Run.cons_inv hz'
  have hyu : M.Run x s u := by simpa using Run.append hy hu
  have hzv : M.Run x s v := by simpa using Run.append hz hv
  rcases SDet.run_comparable hM hyu hzv with h | h
  · obtain rfl := SDet.eq_of_tau hM hpo hu' h
    simpa using (hM.nonO hu' hv' hpo hqo).1
  · obtain rfl := SDet.eq_of_tau hM hqo hv' h
    simpa using (hM.nonO hu' hv' hpo hqo).1

/-- A play of the generated model ending in a Proponent move is a trace. -/
theorem mem_traces_of_mem_denote {s : List G.Move} {p : G.Move} (h : s ++ [p] ∈ M.denote)
    (hp : ¬ G.IsO p) : s ++ [p] ∈ M.traces := by
  obtain ⟨-, u, hu, p₀, w, he, hp₀, hw⟩ := h
  induction w using List.reverseRecOn with
  | nil =>
    simp only [List.append_nil] at he
    subst he
    rcases hu with rfl | ⟨hu, -⟩
    · simp at hp₀
    · exact tracesFrom_of_prefix hu hp₀
  | append_singleton w o _ =>
    rw [← List.append_assoc] at he
    obtain ⟨-, h⟩ := List.append_inj' he rfl
    simp only [List.cons.injEq, and_true] at h
    subst h
    exact absurd (hw p (by simp)) hp

theorem SDet.denote_det (hM : M.SDet) : M.denote.Det := by
  intro s p q hp hq hpo hqo
  exact SDet.traces_det hM (mem_traces_of_mem_denote hp hpo) (mem_traces_of_mem_denote hq hqo) hpo hqo

/-! ## Bisimulation and traces -/

theorem IsBisim.tracesFrom_subset {R : M.State → N.State → Prop} (hR : Machine.IsBisim M N R)
    {x : M.State} {y : N.State} (hxy : R x y) : M.tracesFrom x ⊆ N.tracesFrom y := by
  rintro s ⟨z, hz⟩
  induction hz generalizing y with
  | nil => exact ⟨y, .nil y⟩
  | tau h _ ih =>
    obtain ⟨y', hy', hR'⟩ := hR.forth hxy h
    obtain ⟨w, hw⟩ := ih hR'
    exact ⟨w, .tau hy' hw⟩
  | vis h _ ih =>
    obtain ⟨y', hy', hR'⟩ := hR.forth hxy h
    obtain ⟨w, hw⟩ := ih hR'
    exact ⟨w, .vis hy' hw⟩

theorem IsBisim.symm {R : M.State → N.State → Prop} (hR : Machine.IsBisim M N R) :
    Machine.IsBisim N M (fun y x => R x y) :=
  ⟨fun h hs => hR.back h hs, fun h hs => hR.forth h hs⟩

theorem traces_eq_of_bisim (h : M.Bisim N) : M.traces = N.traces := by
  obtain ⟨R, hR, h0⟩ := h
  exact Set.Subset.antisymm (IsBisim.tracesFrom_subset hR h0)
    (IsBisim.tracesFrom_subset (IsBisim.symm hR) h0)

/-- In a machine without silent steps, a nonempty trace starts with a step. -/
theorem LDet.cons_mem (hM : M.LDet) {x : M.State} {o : G.Move} {t : List G.Move} :
    o :: t ∈ M.tracesFrom x ↔ ∃ y, M.step x (some o) y ∧ t ∈ M.tracesFrom y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x₁, y₁, h₁, h₂, h₃⟩ := Run.cons_inv hz
    cases h₁ with
    | nil => exact ⟨y₁, h₂, z, h₃⟩
    | tau h _ => exact absurd h hM.tau_free
  · rintro ⟨y, hy, z, hz⟩
    exact ⟨z, .vis hy hz⟩

/-- In a deterministic machine the traces after a step are the residual. -/
theorem LDet.tracesFrom_step (hM : M.LDet) {x y : M.State} {o : G.Move}
    (h : M.step x (some o) y) (t : List G.Move) :
    t ∈ M.tracesFrom y ↔ o :: t ∈ M.tracesFrom x := by
  rw [LDet.cons_mem hM]
  exact ⟨fun ht => ⟨y, h, ht⟩, fun ⟨y', h', ht⟩ => hM.det h h' ▸ ht⟩

theorem LDet.bisim_of_traces (hM : M.LDet) (hN : N.LDet) (h : M.traces = N.traces) :
    M.Bisim N := by
  refine ⟨fun x y => M.tracesFrom x = N.tracesFrom y, ⟨?_, ?_⟩, h⟩
  · intro x x' y l hxy hx
    cases l with
    | none => exact absurd hx hM.tau_free
    | some o =>
      have : [o] ∈ N.tracesFrom y := hxy ▸ ((LDet.cons_mem hM).2 ⟨x', hx, _, .nil _⟩)
      obtain ⟨y', hy, -⟩ := (LDet.cons_mem hN).1 this
      refine ⟨y', hy, Set.ext fun t => ?_⟩
      rw [LDet.tracesFrom_step hM hx, LDet.tracesFrom_step hN hy, hxy]
  · intro x y y' l hxy hy
    cases l with
    | none => exact absurd hy hN.tau_free
    | some o =>
      have : [o] ∈ M.tracesFrom x := hxy ▸ ((LDet.cons_mem hN).2 ⟨y', hy, _, .nil _⟩)
      obtain ⟨x', hx, -⟩ := (LDet.cons_mem hM).1 this
      refine ⟨x', hx, Set.ext fun t => ?_⟩
      rw [LDet.tracesFrom_step hM hx, LDet.tracesFrom_step hN hy, hxy]

theorem SDet.lDet (hM : M.SDet) (htau : ∀ {x y : M.State}, ¬ M.step x none y) : M.LDet where
  tau_free := htau
  det {_ _ _ o} h h' := by
    by_cases ho : G.IsO o
    · exact hM.oDet h h' ho
    · exact (hM.nonO h h' ho ho).2

end Silmaril.Proofs.Games.Abstract.Machine
