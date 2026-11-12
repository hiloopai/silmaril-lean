module

public import Silmaril.Proofs.Games.DivLTSComp.Follow
public import Silmaril.Games.DivComp.Defs

/-!
# Projecting staged runs of a composite system

`Proj L₁ L₂`: a staged run of `L₁.comp L₂` together with its two projections,
staged runs of `L₁` and of `L₂` whose traces interact (`Zip`) to the visible
traces at each stage.

* `exists_proj`: a staged run of the composite, given increment by increment
  with an interaction of the increments (`comp_run` per segment), projects to
  such a pair of staged runs, keeping any property `Q` of the chosen
  increments (dependent choice).
* `Proj.toInf`: for systems denoting their strategies, a projected run whose
  hidden part grows without bound is an infinite interaction of the
  divergence-observing strategies `ofLTS L₁` and `ofLTS L₂`
  (`Silmaril.Games.DivComp`): each side's stages are plays, and a side that grows
  without bound converges to one of its infinite plays (`infRun_of_stages`).

New proofs.
-/

public section

namespace Silmaril.Proofs.Games.DivLTSComp

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- Traces of a system denoting its strategy are plays of its divergence-observing strategy. -/
theorem mem_ofLTS_of_run {L : LTS E F} {σ : Strategy E F} (hL : L.Denotes σ)
    {u : List (Move E F)} {y : L.State} (h : L.Run L.init u y) :
    u ∈ (DStrategy.ofLTS L).toStrategy := by
  have hu : u ∈ σ := (hL u).1 ⟨y, h⟩
  show u ∈ Strategy.ofLTS L
  rw [hL.ofLTS_eq]
  exact hu

/-- The limit of a staged run growing without bound is an infinite play. -/
theorem lim_mem_inf {L : LTS E F} {σ : Strategy E F} (hL : L.Denotes σ)
    {a : ℕ → L.State} {s : Chain (Move E F)} (h : Stages L a s) (hu : s.Unbounded) :
    s.lim ∈ (DStrategy.ofLTS L).inf := by
  obtain ⟨r, hr, hru⟩ := infRun_of_stages h
  refine ⟨⟨r, hru hu, hr.symm⟩, fun q ⟨n, hq⟩ => ?_⟩
  have hn : s n ∈ σ := (hL (s n)).1 ⟨_, h.run n⟩
  exact (σ.legal (σ.of_prefix hn hq))

/-- A staged run of the composite with its projections. -/
structure Proj (L₁ : LTS E F) (L₂ : LTS F G) : Type u where
  /-- The composite states. -/
  z : ℕ → (L₁.comp L₂).State
  /-- The lower traces. -/
  s : Chain (Move E F)
  /-- The upper traces. -/
  t : Chain (Move F G)
  /-- The visible traces. -/
  p : Chain (Move E G)
  zip : ∀ n, Zip (s n) (t n) (p n)
  st₁ : Stages L₁ (fun n => (z n).1) s
  st₂ : Stages L₂ (fun n => (z n).2) t
  mono_p : p.Mono

/-- **Projection of a staged composite run**, keeping a property of the increments. -/
theorem exists_proj {L₁ : LTS E F} {L₂ : LTS F G} (z : ℕ → (L₁.comp L₂).State)
    (p : Chain (Move E G)) {s₀ : List (Move E F)} {t₀ : List (Move F G)}
    (hz₀ : Zip s₀ t₀ (p 0)) (h₁ : L₁.Run L₁.init s₀ (z 0).1) (h₂ : L₂.Run L₂.init t₀ (z 0).2)
    (Q : ℕ → List (Move E F) → List (Move F G) → Prop)
    (hstep : ∀ n, ∃ ds dt dp, p (n + 1) = p n ++ dp ∧ Zip ds dt dp ∧
      L₁.Run (z n).1 ds (z (n + 1)).1 ∧ L₂.Run (z n).2 dt (z (n + 1)).2 ∧ Q n ds dt) :
    ∃ π : Proj L₁ L₂, π.z = z ∧ π.p = p ∧
      ∀ n, ∃ ds dt, π.s (n + 1) = π.s n ++ ds ∧ π.t (n + 1) = π.t n ++ dt ∧ Q n ds dt := by
  choose ds dt dp hp hz hr₁ hr₂ hq using hstep
  let s : Chain (Move E F) := fun n => Nat.rec s₀ (fun k acc => acc ++ ds k) n
  let t : Chain (Move F G) := fun n => Nat.rec t₀ (fun k acc => acc ++ dt k) n
  have hs : ∀ n, s (n + 1) = s n ++ ds n := fun _ => rfl
  have ht : ∀ n, t (n + 1) = t n ++ dt n := fun _ => rfl
  have hzip : ∀ n, Zip (s n) (t n) (p n) := by
    intro n
    induction n with
    | zero => exact hz₀
    | succ n ih => rw [hs, ht, hp]; exact zip_append ih (hz n)
  have hmono : p.Mono := fun n => ⟨dp n, (hp n).symm⟩
  exact ⟨⟨z, s, t, p, hzip, ⟨h₁, fun n => ⟨ds n, hs n, hr₁ n⟩⟩,
    ⟨h₂, fun n => ⟨dt n, ht n, hr₂ n⟩⟩, hmono⟩, rfl, rfl,
    fun n => ⟨ds n, dt n, hs n, ht n, hq n⟩⟩

/-- **A projected run whose hidden part grows without bound is an infinite interaction.** -/
theorem Proj.toInf {L₁ : LTS E F} {L₂ : LTS F G} {σ : Strategy E F} {τ : Strategy F G}
    (hL₁ : L₁.Denotes σ) (hL₂ : L₂.Denotes τ) (π : Proj L₁ L₂)
    (hu : ∀ k, ∃ n, k ≤ (π.s n).length + (π.t n).length) :
    ∃ i : DStrategy.InfInteraction (DStrategy.ofLTS L₁) (DStrategy.ofLTS L₂),
      i.s = π.s ∧ i.t = π.t ∧ i.p = π.p :=
  ⟨{ s := π.s, t := π.t, p := π.p, zip := π.zip
     mem_s := fun n => mem_ofLTS_of_run hL₁ (π.st₁.run n)
     mem_t := fun n => mem_ofLTS_of_run hL₂ (π.st₂.run n)
     mono_s := π.st₁.mono, mono_t := π.st₂.mono, mono_p := π.mono_p
     unbounded := hu
     lim_s := lim_mem_inf hL₁ π.st₁
     lim_t := lim_mem_inf hL₂ π.st₂ }, rfl, rfl, rfl⟩

end Silmaril.Proofs.Games.DivLTSComp
