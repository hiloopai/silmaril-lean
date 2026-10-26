module

public import Silmaril.X86.Features.Machine

/-!
# Transport along feature sets and extension lists

## Feature sets

`step_mono`: on a processor with more features, a step that was not a feature
fault is unchanged. `FeatureFree F exts exit m₀` says that no state reachable
from `m₀` under `F` steps to a feature fault; then every processor whose
feature set contains `F` has the same runs, the same outcome at every reachable
state, and the same returns (`FeatureFree.run_eq`, `FeatureFree.step_eq`,
`FeatureFree.returns_iff`), and the program is feature-free there too
(`FeatureFree.mono`). The converse fails: `Features.Checks` proves a one-
instruction SSE4.1 program feature-free under `baseline64 ∪ {sse41}` whose first
step under `baseline64` is `featureUD .sse41`.

## Extension lists

`Included exts exts'`: every extension of `exts` embeds (`Extension.Embeds`)
into one of `exts'`. When `exts'` is pairwise disjoint, `exts'` is a
conservative extension of `exts`: every step that `exts` decodes is the same
under `exts'` (`step_conservative`), and so is every run that only visits
such steps (`run_conservative`).
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory)

variable {F G : FeatureSet} {exts exts' : List Extension} {exit : Word}

/-! ## Feature sets: one step -/

theorem extStep_mono (hFG : F ⊆ G) {e : Extension} {x : e.Syntax} {n : Nat} {m : MState}
    (h : (extStep F e x n m).featureFault? = none) : extStep G e x n m = extStep F e x n m := by
  unfold extStep at h ⊢
  cases hm : F.missing (e.requires x) with
  | some f => rw [hm] at h; cases h
  | none => rw [FeatureSet.missing_mono hFG hm]

/-- A step that is not a feature fault is the same with more features. -/
theorem step_mono (hFG : F ⊆ G) {m : MState} (h : (step F exts exit m).featureFault? = none) :
    step G exts exit m = step F exts exit m := by
  unfold step at h ⊢
  split
  · rename_i i n hf
    simp only [hf] at h
    cases hb : baseCheck F i with
    | some o =>
      rw [hb] at h
      have := baseCheck_featureFault hb
      simp_all
    | none => rw [baseCheck_mono hFG hb]
  · rename_i base hd
    split at h
    · rename_i i n hf; exact absurd hf (hd i n)
    · split
      · rename_i e x n hx
        split
        · rename_i hp
          simp only [hx, hp, ite_true] at h
          exact extStep_mono hFG h
        · rfl
      · rfl

theorem stepOpt_mono (hFG : F ⊆ G) {m : MState} (h : (step F exts exit m).featureFault? = none) :
    stepOpt G exts exit m = stepOpt F exts exit m := by
  simp only [stepOpt, step_mono hFG h]

/-! ## Feature sets: runs -/

/-- No state reachable under `F` steps to a feature fault. -/
def FeatureFree (F : FeatureSet) (exts : List Extension) (exit : Word) (initial : MState) : Prop :=
  ∀ n m, run F exts exit n initial = some m → (step F exts exit m).featureFault? = none

namespace FeatureFree

variable {initial : MState}

/-- Feature-freedom passes to a retired successor. -/
theorem next (h : FeatureFree F exts exit initial) {next : MState}
    (hs : stepOpt F exts exit initial = some next) : FeatureFree F exts exit next := by
  intro n m hr
  apply h (n + 1) m
  rw [run_succ, hs]
  exact hr

/-- Same runs on every processor with more features. -/
theorem run_eq (h : FeatureFree F exts exit initial) (hFG : F ⊆ G) (n : Nat) :
    run G exts exit n initial = run F exts exit n initial := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, run_succ, stepOpt_mono hFG (h 0 initial rfl)]
    cases hs : stepOpt F exts exit initial with
    | none => rfl
    | some next => exact ih (h.next hs)

/-- Same outcome at every reachable state. -/
theorem step_eq (h : FeatureFree F exts exit initial) (hFG : F ⊆ G) {n : Nat} {m : MState}
    (hr : run F exts exit n initial = some m) : step G exts exit m = step F exts exit m :=
  step_mono hFG (h n m hr)

/-- Feature-free on every processor with more features. -/
theorem mono (h : FeatureFree F exts exit initial) (hFG : F ⊆ G) :
    FeatureFree G exts exit initial := by
  intro n m hr
  rw [h.run_eq hFG] at hr
  rw [h.step_eq hFG hr]
  exact h n m hr

/-- Same returns on every processor with more features. -/
theorem returns_iff (h : FeatureFree F exts exit initial) (hFG : F ⊆ G) {final : MState} :
    Returns G exts exit initial final ↔ Returns F exts exit initial final := by
  constructor
  · rintro ⟨n, mid, hr, hs⟩
    rw [h.run_eq hFG] at hr
    exact ⟨n, mid, hr, (h.step_eq hFG hr) ▸ hs⟩
  · rintro ⟨n, mid, hr, hs⟩
    exact ⟨n, mid, (h.run_eq hFG n).trans hr, (h.step_eq hFG hr).trans hs⟩

/-- The headline: a program verified feature-free under `F` has exactly the
same behaviour (runs, outcomes at reachable states, returns) on every
processor whose feature set contains `F`. -/
theorem same_behaviour (h : FeatureFree F exts exit initial) (hFG : F ⊆ G) :
    (∀ n, run G exts exit n initial = run F exts exit n initial) ∧
      (∀ n m, run F exts exit n initial = some m → step G exts exit m = step F exts exit m) ∧
      (∀ final, Returns G exts exit initial final ↔ Returns F exts exit initial final) ∧
      FeatureFree G exts exit initial :=
  ⟨h.run_eq hFG, fun _ _ hr => h.step_eq hFG hr, fun _ => h.returns_iff hFG, h.mono hFG⟩

end FeatureFree

/-! ## Extension lists -/

theorem extDecode_sound {exts : List Extension} {bytes : List Byte} {e : Extension}
    {x : e.Syntax} {n : Nat} (h : extDecode exts bytes = some ⟨e, x, n⟩) :
    e ∈ exts ∧ e.decoder.decode bytes = some (x, n) := by
  induction exts with
  | nil => cases h
  | cons d ds ih =>
    unfold extDecode at h
    split at h
    · rename_i y k hy
      cases h
      exact ⟨List.mem_cons_self .., hy⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- In a pairwise-disjoint list, the extension that decodes is the one found. -/
theorem extDecode_of_mem {exts : List Extension} (hd : Extension.PairwiseDisjoint exts)
    {e : Extension} (he : e ∈ exts) {bytes : List Byte} {x : e.Syntax} {n : Nat}
    (h : e.decoder.decode bytes = some (x, n)) : extDecode exts bytes = some ⟨e, x, n⟩ := by
  induction exts with
  | nil => cases he
  | cons d ds ih =>
    have hd' := List.pairwise_cons.mp hd
    unfold extDecode
    split
    · rename_i y k hy
      rcases List.mem_cons.mp he with rfl | hin
      · rw [h] at hy; cases hy; rfl
      · rcases hd'.1 e hin bytes with hn | hn
        · rw [hn] at hy; cases hy
        · rw [hn] at h; cases h
    · rename_i hy
      rcases List.mem_cons.mp he with rfl | hin
      · rw [h] at hy; cases hy
      · exact ih hd'.2 hin

/-- Every extension of `exts` embeds into one of `exts'`. -/
def Included (exts exts' : List Extension) : Prop :=
  ∀ e ∈ exts, ∃ e' ∈ exts', e.Embeds e'

theorem Included.of_subset (h : exts ⊆ exts') : Included exts exts' :=
  fun e he => ⟨e, h he, Extension.Embeds.refl e⟩

/-- Some decoder (integer or extension) accepts the bytes at RIP. -/
def Decodes (exts : List Extension) (m : MState) : Prop :=
  (∃ i n, Ext.fetch m.memory m.state.core.rip.toNat = .decoded i n) ∨
    (extDecode exts (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat)).isSome

/-- A pairwise-disjoint `exts'` into which `exts` is included is a conservative
extension: every step `exts` decodes is unchanged. -/
theorem step_conservative (hd : Extension.PairwiseDisjoint exts') (hinc : Included exts exts')
    {m : MState} (hdec : Decodes exts m) : step F exts' exit m = step F exts exit m := by
  unfold step
  split
  · rfl
  · rename_i base hb
    have hsome : (extDecode exts (fetchWindow m.memory maxInstrLength
        m.state.core.rip.toNat)).isSome := by
      rcases hdec with ⟨i, n, hf⟩ | hs
      · exact absurd hf (hb i n)
      · exact hs
    obtain ⟨⟨e, x, n⟩, hx⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨he, hdx⟩ := extDecode_sound hx
    obtain ⟨e', he', ι, hdι, hreq, hexec⟩ := hinc e he
    rw [hx, extDecode_of_mem hd he' (hdι _ x n hdx)]
    simp only
    split
    · unfold extStep
      rw [hreq]
      split
      · rfl
      · rw [hexec]
    · rfl

/-- Runs that only visit decoded states are unchanged by a conservative extension. -/
theorem run_conservative (hd : Extension.PairwiseDisjoint exts') (hinc : Included exts exts')
    {initial : MState}
    (hdec : ∀ n m, run F exts exit n initial = some m → Decodes exts m) (n : Nat) :
    run F exts' exit n initial = run F exts exit n initial := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, run_succ]
    have hs : stepOpt F exts' exit initial = stepOpt F exts exit initial := by
      simp only [stepOpt, step_conservative hd hinc (hdec 0 initial rfl)]
    rw [hs]
    cases h : stepOpt F exts exit initial with
    | none => rfl
    | some next =>
      apply ih
      intro k m hr
      apply hdec (k + 1) m
      rw [run_succ, h]
      exact hr

end Silmaril.X86.Features
