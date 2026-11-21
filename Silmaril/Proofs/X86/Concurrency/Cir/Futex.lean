module

public import Silmaril.X86.Concurrency.Cir.Futex.Defs
public import Silmaril.X86.Concurrency.Cir.Sync.Thms

/-!
# CIR futexes: proofs

A futex wake edge (`Exec.fsw`) is a spawn/join edge (`Exec.sw`:
a locked `rfe` at or above the control bytes), because queue bytes lie above them. So the
paths give every `fswHb` edge as a path of each model's own order, and the synchronising models
equal the plain ones. The Dekker lemma is a four-edge `ghbXl` cycle. Blocked traces only add
traces, so `AxReach` is monotone.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Futex

open Relation
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Axiomatic.BRel (union_iff seq_elim)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Litmus (AxReach XTrace)

theorem fsw_sw {x : Exec} {w r : Fin x.n} (h : x.fsw w r = true) : x.sw w r = true := by
  simp only [Exec.fsw, Exec.sw, Futex.isQAddr, Sync.isCtlAddr, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, ?_⟩ <;> simp only [qAddr, ctlAddr] at h4 h5 ⊢ <;> omega

theorem fswHb_swHb {x : Exec} {a b : Fin x.n} (h : x.fswHb a b = true) : x.swHb a b = true := by
  simp only [Exec.fswHb, Exec.swHb, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨ha, hb⟩, h⟩ := h
  refine ⟨⟨ha, hb⟩, ?_⟩
  obtain ⟨r, h1, h3⟩ := seq_elim h
  obtain ⟨w, h1, h2⟩ := seq_elim h1
  simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
  exact ⟨r, List.mem_finRange r, ⟨w, List.mem_finRange w, h1, fsw_sw h2⟩, h3⟩

theorem union_path {n : Nat} {G H : BRel n} (hH : ∀ a b, H a b = true → TransGen G.Holds a b) :
    ∀ a b, (G.union H) a b = true → TransGen G.Holds a b := by
  intro a b h
  rcases union_iff.mp h with h | h
  · exact .single h
  · exact hH a b h

theorem scF_iff (x : Exec) : x.ScF ↔ x.Sc :=
  ⟨fun h => h.1, fun h => ⟨h, BRel.acyclic_mono
    (union_path fun _ _ hab => Exec.swHb_sc (fswHb_swHb hab)) h.2⟩⟩

theorem tsoF_iff (x : Exec) : x.TsoF ↔ x.Tso :=
  ⟨fun h => h.1, fun h => ⟨h, BRel.acyclic_mono
    (union_path fun _ _ hab => Exec.swHb_ghb (fswHb_swHb hab)) h.2.2⟩⟩

theorem xlF_iff (x : Exec) : x.XlF ↔ x.Xl :=
  ⟨fun h => h.1, fun h => ⟨h, BRel.acyclic_mono
    (union_path fun _ _ hab => Exec.swHb_ghbXl (fswHb_swHb hab)) h.2.2.2⟩⟩

/-- The Dekker cycle `s →lockXl w →co q →mfence l →fr s` is a `ghbXl` cycle. -/
theorem dekker_xl {x : Exec} (hx : x.Xl) {s w q l : Fin x.n} (hs : x.lockXl s w = true)
    (hco : x.coR w q = true) (hf : x.mfence q l = true) (hfr : x.frR l s = true) : False := by
  have smT : ∀ c, x.smT c c = true := fun c => by simp [Exec.smT]
  have e1 : x.ghbXl s w = true := by simp [Exec.ghbXl, BRel.union, hs]
  have e2 : x.ghbXl w q = true := by
    have : x.comGhbXl w q = true :=
      BRel.seq_of_left smT (union_iff.mpr (.inr (union_iff.mpr (.inr hco))))
    simp [Exec.ghbXl, BRel.union, this]
  have e3 : x.ghbXl q l = true := by simp [Exec.ghbXl, BRel.union, hf]
  have e4 : x.ghbXl l s = true := by
    have : x.comGhbXl l s = true :=
      BRel.seq_of_left smT (union_iff.mpr (.inr (union_iff.mpr (.inl hfr))))
    simp [Exec.ghbXl, BRel.union, this]
  exact hx.2.2.2 s (.tail (.tail (.tail (.single e1) e2) e3) e4)

theorem forall2_mem_mono {α : Type} {trs : List α} {T U : List (List α)}
    (h : List.Forall₂ (· ∈ ·) trs T) (hl : T.length = U.length)
    (hs : ∀ k (h1 : k < T.length) (h2 : k < U.length), ∀ a ∈ T[k], a ∈ U[k]) :
    List.Forall₂ (· ∈ ·) trs U := by
  induction h generalizing U with
  | nil => cases U with
    | nil => exact .nil
    | cons _ _ => simp at hl
  | cons hab _ ih =>
    cases U with
    | nil => simp at hl
    | cons u U =>
      refine .cons (hs 0 (by simp) (by simp) _ hab) (ih (by simpa using hl) fun k h1 h2 =>
        hs (k + 1) (by simpa using h1) (by simpa using h2))

/-- Every behaviour is a behaviour with blocking. -/
theorem behavIn_bbehavIn {P : Prog} {dom : List Nat} {M : Exec → Prop} {f : _}
    (h : BehavIn P dom M f) : BBehavIn P dom M f := by
  obtain ⟨trs, h2, rest⟩ := h
  refine ⟨trs, forall2_mem_mono h2 (by simp [Prog.traces, Prog.btraces]) ?_, rest⟩
  intro k h1 h2 a ha
  simp only [Prog.traces, Prog.btraces, List.getElem_mapIdx] at ha ⊢
  exact List.mem_append_left _ ha

end Silmaril.Proofs.X86.Concurrency.Cir.Futex
