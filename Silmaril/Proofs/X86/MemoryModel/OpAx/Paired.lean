module

public import Silmaril.Proofs.X86.MemoryModel.OpAx.Run

/-!
# Runs pair the halves of each locked read-modify-write: proofs

The candidate `g.x` built from a run (`Proofs.run_explains`) records each `rmw` step's read and
write units in `g.rmw`. This file proves the converse direction of that bookkeeping: every
locked read unit and locked write unit of one thread at consecutive positions form a recorded
pair (`Paired`), so the candidate satisfies `OpAx.RmwPaired` (`run_explains_paired`). Without
it `Explains` would allow `x.rmw = []`, which makes `Exec.atomicB` trivially true.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.OpAx.Proofs

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.OpAx
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush Byte Mem)
open Silmaril.X86.MemoryModel.Litmus (ACfg AStep)

/-- `RmwPaired`, on a history. -/
def Paired (g : G) : Prop :=
  ∀ a < g.us.length, ∀ b < g.us.length, (uev g.us a).isR = true → (uev g.us b).isW = true →
    (uev g.us a).locked = true → (uev g.us b).locked = true →
      (uev g.us a).tid = (uev g.us b).tid → (uev g.us b).pos = (uev g.us a).pos + 1 →
        (a, b) ∈ g.rmw

theorem paired_init : Paired G.init := by
  intro a ha; simp [G.init] at ha

/-- Appending one unlocked unit (a load, a store or a fence) keeps the pairing. -/
theorem paired_snoc1 {g g' : G} (hP : Paired g) {p : Ev × List Byte} (hus : g'.us = g.us ++ [p])
    (hrmw : g'.rmw = g.rmw) (hp : p.1.locked = false) : Paired g' := by
  intro a ha b hb hR hW hla hlb ht hpos
  rw [hrmw]
  rw [hus] at ha hb hR hW hla hlb ht hpos
  rcases uev_cases1 ha with ⟨ha', ea⟩ | ⟨-, ea⟩
  · rcases uev_cases1 hb with ⟨hb', eb⟩ | ⟨-, eb⟩
    · rw [ea] at hR hla ht hpos; rw [eb] at hW hlb ht hpos
      exact hP a ha' b hb' hR hW hla hlb ht hpos
    · rw [eb, hp] at hlb; cases hlb
  · rw [ea, hp] at hla; cases hla

/-- A locked read-modify-write step records exactly its own pair. -/
theorem paired_rmw {P : List (List (XEvent Nat))} {init : Tso.Mem} {c : ACfg} {g : G}
    (H : Inv P init c g) (hP : Paired g) {i a : Nat} {old new : List Byte} :
    Paired (g.rmwStep i (.rmw i a old new)) := by
  have hus : (g.rmwStep i (.rmw i a old new)).us = g.us ++
      [({ tid := i, pos := 2 * g.cnt i, act := .read, addr := a, size := old.length,
            locked := true }, old),
        ({ tid := i, pos := 2 * g.cnt i + 1, act := .write, addr := a, size := new.length,
            locked := true, data := new }, [])] := rfl
  have hrmw : (g.rmwStep i (.rmw i a old new)).rmw = g.rmw ++ [(g.us.length, g.us.length + 1)] :=
    rfl
  have oldpos : ∀ u < g.us.length, (uev g.us u).tid = i → (uev g.us u).pos < 2 * g.cnt i :=
    fun u hu ht => by have := H.book.posLt u hu; rw [ht] at this; exact this
  intro x hx y hy hR hW hlx hly ht hpos
  rw [hrmw]
  rw [hus] at hx hy hR hW hlx hly ht hpos
  rcases uev_cases2 hx with ⟨hx', ex⟩ | ⟨hx', ex⟩ | ⟨hx', ex⟩ <;>
    rcases uev_cases2 hy with ⟨hy', ey⟩ | ⟨hy', ey⟩ | ⟨hy', ey⟩ <;>
    rw [ex] at hR hlx ht hpos <;> rw [ey] at hW hly ht hpos
  · exact List.mem_append_left _ (hP x hx' y hy' hR hW hlx hly ht hpos)
  · simp [Ev.isW] at hW
  · have := oldpos x hx' ht; simp only at hpos; omega
  · have := oldpos y hy' ht.symm; simp only at hpos; omega
  · simp [Ev.isW] at hW
  · subst hx' hy'; exact List.mem_append_right _ (List.mem_singleton_self _)
  all_goals simp [Ev.isR] at hR

/-- Every step preserves the invariant together with the pairing. -/
theorem paired_step {P : List (List (XEvent Nat))} (hT : ThreadsOk P) {init : Tso.Mem}
    {c c' : ACfg} {g : G} (H : Inv P init c g) (hP : Paired g) (h : AStep c c') :
    ∃ g', Inv P init c' g' ∧ Paired g' := by
  cases h with
  | ev rest s s' i ev es hr hs =>
    obtain ⟨ps, hps, hmem, -⟩ := rest_head H.book hr
    have hti := hT i ps hps ev hmem
    cases hs with
    | load t a bs hv => exact ⟨_, inv_load H hr hti hv, paired_snoc1 hP rfl rfl rfl⟩
    | store t a bs => exact ⟨_, inv_store H hr hti, paired_snoc1 hP rfl rfl rfl⟩
    | rmw t a old new hemp hm _ =>
      refine ⟨_, inv_rmw H hr hti hemp hm, ?_⟩
      have ht : t = i := hti
      subst ht
      exact paired_rmw H hP
    | fence t hemp => exact ⟨_, inv_fence H hr hti hemp, paired_snoc1 hP rfl rfl rfl⟩
  | flush rest s s' hf =>
    cases hf with
    | head t a bs rest' hold =>
      obtain ⟨g', H', hus, hrmw⟩ := inv_flush H hold
      refine ⟨g', H', ?_⟩
      intro a ha b hb
      rw [hus] at ha hb ⊢
      rw [hrmw]
      exact hP a ha b hb

theorem paired_run {P : List (List (XEvent Nat))} (hT : ThreadsOk P) {init : Tso.Mem}
    {c c' : ACfg} (h : Relation.ReflTransGen AStep c c') {g : G} (H : Inv P init c g)
    (hP : Paired g) : ∃ g', Inv P init c' g' ∧ Paired g' := by
  induction h with
  | refl => exact ⟨g, H, hP⟩
  | tail _ hstep ih =>
    obtain ⟨g', H', hP'⟩ := ih
    exact paired_step hT H' hP' hstep

/-- **op-TSO ⊆ ax-TSO, with atomicity.** The explaining candidate also pairs the halves of
every locked read-modify-write, so its `atomicB` check is not vacuous. -/
theorem run_explains_paired {P : List (List (XEvent Nat))} (hT : ThreadsOk P)
    (hC : ThreadCells P) {init : Tso.Mem} {s : XState Nat} (h : Run P init s) :
    ∃ x, Explains Exec.Tso P init s x ∧ RmwPaired x := by
  obtain ⟨g, H, hP⟩ := paired_run hT h.1 (inv_init P init) paired_init
  refine ⟨g.x, final_explains H h.2 hC, ?_⟩
  intro a ha b hb
  rw [x_n] at ha hb
  exact hP a ha b hb

end Silmaril.X86.MemoryModel.OpAx.Proofs
