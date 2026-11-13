module

public import Silmaril.Proofs.Wasm.Models.FXTRun.Sound

/-!
# Runs of the `StepFXT` interpreter in segments

* `beqInstr_eq`, `beqFlat_eq`, `beqFlats_eq`, `beqCode_eq`, `beqFV_eq`, `beqFVs_eq`: the
  comparisons of `Silmaril.Wasm.Models.FXTRun` are sound;
* `runT_store`, `runT_frame`: the interpreter keeps the store and the frame;
* **`sameCfg_eq`**: agreeing configurations with the same store and frame are equal;
* **`segT_steps`**: a checked segment is a `StepsT` run to the given configuration;
* **`mem_of_stepsT`**: a finished behaviour after a run is a behaviour before it.

So a long run can be checked as a chain of segments, each in its own module.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXTRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXTRun
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {intr : H → Option Intr}

theorem beqInstr_eq {i j : Instr} (h : beqInstr i j = true) : i = j := by
  unfold beqInstr at h
  split at h <;> simp_all

theorem beqFlat_eq {a b : AdminFX} (h : beqFlat a b = true) : a = b := by
  unfold beqFlat at h
  split at h
  · rw [beqInstr_eq h]
  · simp_all
  · simp_all

theorem beqFlats_eq : ∀ {as bs : List AdminFX}, beqFlats as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [beqFlats, Bool.and_eq_true] at h
    rw [beqFlat_eq h.1, beqFlats_eq h.2]
  | [], _ :: _, h => absurd h (by simp [beqFlats])
  | _ :: _, [], h => absurd h (by simp [beqFlats])

theorem beqCode_eq {as bs : List AdminFX} (h : beqCode as bs = true) : as = bs := by
  unfold beqCode at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hb⟩ := h
    rw [beqFlats_eq hb]
  · simp_all

theorem beqFV_eq {a b : FVal} (h : beqFV a b = true) : a = b := by
  unfold beqFV at h
  split at h <;> simp_all

theorem beqFVs_eq : ∀ {as bs : List FVal}, beqFVs as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [beqFVs, Bool.and_eq_true] at h
    rw [beqFV_eq h.1, beqFVs_eq h.2]
  | [], _ :: _, h => absurd h (by simp [beqFVs])
  | _ :: _, [], h => absurd h (by simp [beqFVs])

theorem all_none {α : Type} : ∀ {l : List (Option α)}, l.all Option.isNone = true →
    l = List.replicate l.length none
  | [], _ => rfl
  | none :: l, h => by
    simp only [List.all_cons, Option.isNone_none, Bool.true_and] at h
    simp only [List.length_cons, List.replicate_succ]
    rw [← all_none h]
  | some _ :: _, h => absurd h (by simp)

/-- **Agreeing configurations** with the same store and frame are equal. -/
theorem sameCfg_eq {c m : ConfigT H} (h : sameCfg c m = true) (hs : c.cfg.store = m.cfg.store)
    (hf : c.cfg.frame = m.cfg.frame) : c = m := by
  obtain ⟨⟨s, K, f, code⟩, ⟨cells, q, log⟩⟩ := c
  obtain ⟨⟨s', K', f', code'⟩, ⟨cells', q', log'⟩⟩ := m
  simp only [sameCfg, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hl, hK⟩, hK'⟩, hc⟩, hce⟩, hq⟩, hlog⟩ := h
  simp only at hs hf hl hK hK' hc hce hq hlog
  subst hs hf hlog
  have hKK : K = K' := by rw [all_none hK, all_none hK', hl]
  rw [hKK, beqCode_eq hc, beqFVs_eq hce, beqFVs_eq hq]

theorem stepC_keeps {tar : Nat → Nat} {d : Nat} {c c' : ConfigT H}
    (h : stepC tar fx intr d c = some c') :
    c'.cfg.store = c.cfg.store ∧ c'.cfg.frame = c.cfg.frame := by
  unfold stepC at h
  obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, rfl⟩

/-- The interpreter keeps the store and the frame. -/
theorem runT_keeps {tar : Nat → Nat} {d : Nat} : ∀ (n : Nat) (c : ConfigT H),
    (runT tar fx intr d n c).cfg.store = c.cfg.store ∧
      (runT tar fx intr d n c).cfg.frame = c.cfg.frame
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, c => by
    unfold runT
    split
    · rename_i c' hc
      obtain ⟨h1, h2⟩ := runT_keeps n c'
      obtain ⟨h3, h4⟩ := stepC_keeps hc
      exact ⟨h1.trans h3, h2.trans h4⟩
    · exact ⟨rfl, rfl⟩

/-- **A checked segment is a run** to the given configuration. -/
theorem segT_steps {tar : Nat → Nat} {d n : Nat} {c m : ConfigT H}
    (h : segT tar fx intr d n c m = true) (hs : c.cfg.store = m.cfg.store)
    (hf : c.cfg.frame = m.cfg.frame) : StepsT P host fx intr c m := by
  have e := sameCfg_eq h ((runT_keeps n c).1.trans hs) ((runT_keeps n c).2.trans hf)
  rw [← e]
  exact runT_sound n c

/-- **A finished behaviour after a run is a behaviour before it.** -/
theorem mem_of_stepsT {c d : ConfigT H} {l : List Val} {b : Behaviour Val}
    (hr : StepsT P host fx intr c d) (h : ObsT.ret l b ∈ behavioursT P host fx intr d) :
    ObsT.ret l b ∈ behavioursT P host fx intr c := by
  rcases h with ⟨e, r, he, hc, ho⟩ | ⟨ho, -⟩
  · exact Or.inl ⟨e, r, hr.trans he, hc, ho⟩
  · exact absurd ho (by simp)

end Silmaril.Proofs.Wasm.Models.FXTRun
