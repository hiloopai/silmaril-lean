module

public import Silmaril.Wasm.Models.FXTRunX.Defs
public import Silmaril.Wasm.Models.FXTRun.Thms

/-!
# The trap steps are `StepFXT` steps

`xstep_sound`, `stepX_sound`, `runX_sound`, and `checkTrapX_mem`: a checked trapping run gives
the behaviour `ObsT.ret log traps`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXTRunX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXTRun Silmaril.Wasm.Models.FXTRunX
open Silmaril.Proofs.Wasm.Models.FXTRun
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {intr : H → Option Intr}

theorem isTrap_eq {c : List AdminFX} (h : isTrap c = true) : c = [.core .trap] := by
  unfold isTrap at h
  split at h
  · rfl
  · cases h

theorem usedCont_eq {K : List (Option ContFX)} {vs u : List FVal} (h : usedCont K vs = some u) :
    ∃ k, vs = u ++ [.cont k] ∧ K[k]? = some none := by
  unfold usedCont at h
  split at h
  · rename_i u₀ k hl
    split at h
    · rename_i hk
      cases h
      exact ⟨k, lastCont_eq hl, hk⟩
    · cases h
  · cases h

/-- Every result of `rec` is a `StepFXT` step (continuation store `K`, store and table kept). -/
def XSound (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (intr : H → Option Intr) (K : List (Option ContFX)) (rec : XStepper) : Prop :=
  ∀ (g : Frame) (c c' : List AdminFX), rec g c = some c' → ∀ (s : Store H) (t : Tbl),
    StepFXT P host fx intr ⟨⟨s, K, g, c⟩, t⟩ ⟨⟨s, K, g, c'⟩, t⟩

theorem trap_T {s : Store H} {K : List (Option ContFX)} {f : Frame} {t : Tbl}
    (vs : List FVal) (rest : List AdminFX) (hne : ¬ (vs.isEmpty && rest.isEmpty) = true) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ .core .trap :: rest⟩, t⟩
      ⟨⟨s, K, f, [.core .trap]⟩, t⟩ := by
  have hne' : vs ≠ [] ∨ rest ≠ [] := by
    by_contra hc
    simp only [ne_eq, not_or, Decidable.not_not] at hc
    simp only [hc, List.isEmpty_nil, Bool.and_self, not_true_eq_false] at hne
  exact T_conv (.lift (.trapSeq (vs := vs) (rest := rest) hne')) (by simp) rfl

theorem resumeUsed_T {s : Store H} {K : List (Option ContFX)} {f : Frame} {t : Tbl}
    {vs u : List FVal} (rest : List AdminFX) {ct : TypeIdx} {hs : List OnClause}
    (h : usedCont K vs = some u) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ .fx (.resume ct hs) :: rest⟩, t⟩
      ⟨⟨s, K, f, fvals u ++ [.core .trap] ++ rest⟩, t⟩ := by
  obtain ⟨k, rfl, hk⟩ := usedCont_eq h
  have h₀ : StepFXT P host fx intr ⟨⟨s, K, f, [.contRef k, .fx (.resume ct hs)]⟩, t⟩
      ⟨⟨s, K, f, [.core .trap]⟩, t⟩ :=
    .lift (StepFX'.resumeUsed (vs := []) hk)
  exact T_conv (T_seq u rest h₀) (by simp [fvals, FVal.toAdmin]) rfl

theorem wrapTrap_T {s : Store H} {K : List (Option ContFX)} {f : Frame} {t : Tbl}
    (vs : List FVal) (rest : List AdminFX) (e : AdminFX)
    (he : StepFXT P host fx intr ⟨⟨s, K, f, [e]⟩, t⟩ ⟨⟨s, K, f, [.core .trap]⟩, t⟩) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ e :: rest⟩, t⟩
      ⟨⟨s, K, f, fvals vs ++ [.core .trap] ++ rest⟩, t⟩ :=
  T_conv (T_seq vs rest he) (by simp) rfl

theorem wrapRec_T {s : Store H} {K : List (Option ContFX)} {f : Frame} {t : Tbl}
    (vs : List FVal) (rest : List AdminFX) {e e' : AdminFX}
    (he : StepFXT P host fx intr ⟨⟨s, K, f, [e]⟩, t⟩ ⟨⟨s, K, f, [e']⟩, t⟩) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ e :: rest⟩, t⟩
      ⟨⟨s, K, f, fvals vs ++ [e'] ++ rest⟩, t⟩ :=
  T_conv (T_seq vs rest he) (by simp) rfl

/-- A label, frame or handler `mk body` at the head: a trap body, or a step inside. -/
theorem wrapArm_T {K : List (Option ContFX)} {rec : XStepper}
    (hrec : XSound P host fx intr K rec) {f g : Frame} {vs : List FVal} {rest : List AdminFX}
    {body c' : List AdminFX} {mk : List AdminFX → AdminFX} {s : Store H} {t : Tbl}
    (htrap : StepFXT P host fx intr ⟨⟨s, K, f, [mk [.core .trap]]⟩, t⟩
      ⟨⟨s, K, f, [.core .trap]⟩, t⟩)
    (hin : ∀ b b', StepFXT P host fx intr ⟨⟨s, K, g, b⟩, t⟩ ⟨⟨s, K, g, b'⟩, t⟩ →
      StepFXT P host fx intr ⟨⟨s, K, f, [mk b]⟩, t⟩ ⟨⟨s, K, f, [mk b']⟩, t⟩)
    (h : (if isTrap body = true then some (fvals vs ++ [.core .trap] ++ rest)
      else (rec g body).map fun b => fvals vs ++ [mk b] ++ rest) = some c') :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ mk body :: rest⟩, t⟩ ⟨⟨s, K, f, c'⟩, t⟩ := by
  by_cases hb : isTrap body = true
  · have h' : some (fvals vs ++ [.core .trap] ++ rest) = some c' := by
      simpa only [hb, ite_true] using h
    cases h'
    exact wrapTrap_T vs rest _ (by rw [isTrap_eq hb]; exact htrap)
  · have h' : (rec g body).map (fun b => fvals vs ++ [mk b] ++ rest) = some c' := by
      simpa only [hb, Bool.not_eq_true, Bool.false_eq_true, ite_false] using h
    obtain ⟨b, hb', hc⟩ := Option.map_eq_some_iff.mp h'
    rw [← hc]
    exact wrapRec_T vs rest (hin body b (hrec g body b hb' s t))

/-- A trap at the head. -/
theorem trapArm_T {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
    {rest c' : List AdminFX} {s : Store H} {t : Tbl}
    (h : (if (vs.isEmpty && rest.isEmpty) = true then none else some [AdminFX.core .trap]) =
      some c') :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ .core .trap :: rest⟩, t⟩
      ⟨⟨s, K, f, c'⟩, t⟩ := by
  by_cases hne : (vs.isEmpty && rest.isEmpty) = true
  · have h' : (none : Option (List AdminFX)) = some c' := by
      simpa only [hne, ite_true] using h
    cases h'
  · have h' : some [AdminFX.core .trap] = some c' := by
      simpa only [hne, Bool.not_eq_true, Bool.false_eq_true, ite_false] using h
    cases h'
    exact trap_T vs rest hne

/-- **The trap step at the head is a step.** -/
theorem trapHead_sound {K : List (Option ContFX)} {rec : XStepper}
    (hrec : XSound P host fx intr K rec) {f : Frame} {vs : List FVal} {rest : List AdminFX}
    {e : AdminFX} {c' : List AdminFX} (h : trapHead rec f K vs rest e = some c')
    (s : Store H) (t : Tbl) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ e :: rest⟩, t⟩ ⟨⟨s, K, f, c'⟩, t⟩ := by
  match e, h with
  | .core .trap, h => exact trapArm_T h
  | .fx (.resume ct hs), h =>
    have h' : (usedCont K vs).map (fun u => fvals u ++ [.core .trap] ++ rest) = some c' := h
    obtain ⟨u, hu, hc⟩ := Option.map_eq_some_iff.mp h'
    rw [← hc]
    exact resumeUsed_T rest hu
  | .label n k body, h =>
    exact wrapArm_T hrec (.lift .trapLabel) (fun _ _ hb => T_label n k hb) h
  | .frame n fi body, h =>
    exact wrapArm_T hrec (.lift .trapFrame) (fun _ _ hb => T_frame n f hb) h
  | .handler hs body, h =>
    exact wrapArm_T hrec (.lift .trapHandler) (fun _ _ hb => T_handler hs hb) h

/-- **Every trap step is a `StepFXT` step.** -/
theorem xstep_sound (K : List (Option ContFX)) :
    ∀ d : Nat, XSound P host fx intr K (xstep K d)
  | 0, _, _, _, h => nomatch h
  | d + 1, g, c, c', h => by
    intro s t
    unfold xstep at h
    split at h
    · cases h
    · rename_i vs e rest hsp
      rw [splitV_eq hsp]
      exact trapHead_sound (xstep_sound K d) h s t

theorem stepX_sound {tar : Nat → Nat} {d : Nat} {c c' : ConfigT H}
    (h : stepX tar fx intr d c = some c') : StepFXT P host fx intr c c' := by
  unfold stepX at h
  split at h
  · rename_i c₁ hc
    cases h
    exact stepC_sound hc
  · obtain ⟨code, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact xstep_sound c.cfg.conts d c.cfg.frame c.cfg.code code hx c.cfg.store c.tbl

/-- **A computed run is a `StepFXT` run.** -/
theorem runX_sound {tar : Nat → Nat} {d : Nat} :
    ∀ (n : Nat) (c : ConfigT H), StepsT P host fx intr c (runX tar fx intr d n c)
  | 0, _ => .refl
  | n + 1, c => by
    unfold runX
    split
    · rename_i c' hc
      exact Relation.ReflTransGen.head (stepX_sound hc) (runX_sound n c')
    · exact .refl

/-- **A checked trapping run gives a behaviour**: the log `log`, then a trap. -/
theorem checkTrapX_mem {tar : Nat → Nat} {d n : Nat} {c : ConfigT H} {log : List Val}
    (h : checkTrapX tar fx intr d n c log = true) :
    ObsT.ret log .traps ∈ behavioursT P host fx intr c := by
  unfold checkTrapX at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcode, hlog⟩ := h
  refine Or.inl ⟨runX tar fx intr d n c, .trap, runX_sound n c, ?_, ?_⟩
  · rw [isTrap_eq hcode]
    rfl
  · rw [hlog]
    rfl

end Silmaril.Proofs.Wasm.Models.FXTRunX
