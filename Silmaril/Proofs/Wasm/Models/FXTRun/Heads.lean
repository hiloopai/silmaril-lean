module

public import Silmaril.Proofs.Wasm.Models.FXTRun.Wrap

/-!
# The structured heads of the `StepFXT` interpreter are steps

For a step function `rec` whose results are `StepFXT` steps (`Sound`):

* **`labelHead_sound`**: values out of a label (`labelVals_T`), `br` to it or through it
  (`brOut_sound`), `return` through it (`labelRet_T`), or a step inside it;
* **`frameHead_sound`**: values out of a function frame, `return` out of it, or a step inside;
* **`susHead_sound`**: a `suspend` caught by a handler frame (`StepFX'.suspend`, `catchAt_sound`);
* **`handlerHead_sound`**: values, `br` and `return` through a handler frame, a step inside it,
  or a caught `suspend`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXTRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXTRun
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {intr : H → Option Intr}

/-- Every result of the step function `rec` at store `s` is a `StepFXT` step. -/
def Sound (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (intr : H → Option Intr) (s : Store H) (rec : Stepper) : Prop :=
  ∀ (g : Frame) (K : List (Option ContFX)) (t : Tbl) (c : List AdminFX) (K' : List (Option ContFX))
    (t' : Tbl) (c' : List AdminFX), rec g K t c = some (K', t', c') →
    StepFXT P host fx intr ⟨⟨s, K, g, c⟩, t⟩ ⟨⟨s, K', g, c'⟩, t'⟩

variable {s : Store H} {rec : Stepper} {f : Frame} {K K' : List (Option ContFX)} {t t' : Tbl}

/-! ## Labels -/

theorem labelVals_T {n : Nat} {k : List InstrFX} {body : List AdminFX} {ws : List FVal}
    (hsp : splitV body = (ws, [])) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.label n k body]⟩, t⟩ ⟨⟨s, K, f, fvals ws⟩, t⟩ := by
  have hb : body = fvals ws := by simpa using splitV_eq hsp
  rw [hb]
  exact .lift .labelVals

theorem labelRet_T {n : Nat} {k : List InstrFX} {body rest : List AdminFX} {ws : List FVal}
    (hsp : splitV body = (ws, .core (.plain .return_) :: rest)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.label n k body]⟩, t⟩
      ⟨⟨s, K, f, fvals ws ++ [.core (.plain .return_)]⟩, t⟩ := by
  rw [splitV_eq hsp]
  exact T_conv (.lift (.returnLabel (n := n) (k := k) (rest := rest))) (by simp) rfl

/-- **`br l` out of a label is a step.** -/
theorem brOut_sound {n : Nat} {k : List InstrFX} {body rest r : List AdminFX} {ws : List FVal}
    {l : LabelIdx} (hsp : splitV body = (ws, .core (.plain (.br l)) :: rest))
    (h : brOut K t n k ws l = some (K', t', r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.label n k body]⟩, t⟩ ⟨⟨s, K', f, r⟩, t'⟩ := by
  have hb := splitV_eq hsp
  unfold brOut at h
  split at h
  · rename_i hl
    split at h
    · rename_i u w hse
      cases h
      obtain ⟨hws, hn⟩ := splitEnd_eq hse
      rw [hb, hws]
      exact T_conv (.lift (.brLabelZero (n := n) (k := k) (vs' := u) (rest := rest) hl hn))
        (by simp) rfl
    · cases h
  · rename_i hl
    cases h
    rw [hb]
    exact T_conv (.lift (.brLabelSucc (n := n) (k := k) (rest := rest) (Nat.pos_of_ne_zero hl)))
      (by simp) rfl

/-- **A label head is a step.** -/
theorem labelHead_sound (hrec : Sound P host fx intr s rec) {n : Nat} {k : List InstrFX}
    {body r : List AdminFX} (h : labelHead rec f K t n k body = some (K', t', r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.label n k body]⟩, t⟩ ⟨⟨s, K', f, r⟩, t'⟩ := by
  unfold labelHead at h
  split at h
  · rename_i ws hsp
    cases h
    exact labelVals_T hsp
  · rename_i ws l rest hsp
    exact brOut_sound hsp h
  · rename_i ws rest hsp
    cases h
    exact labelRet_T hsp
  · obtain ⟨⟨K₁, t₁, b⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    cases h2
    exact T_label n k (hrec f K t body K₁ t₁ b h1)

/-! ## Function frames -/

theorem frameRet_T {n : Nat} {fi : Frame} {body rest : List AdminFX} {ws u w : List FVal}
    (hsp : splitV body = (ws, .core (.plain .return_) :: rest))
    (hse : splitEnd n ws = some (u, w)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.frame n fi body]⟩, t⟩ ⟨⟨s, K, f, fvals w⟩, t⟩ := by
  obtain ⟨hws, hn⟩ := splitEnd_eq hse
  rw [splitV_eq hsp, hws]
  exact T_conv (.lift (.returnFrame (fi := fi) (vs' := u) (rest := rest) hn)) (by simp) rfl

/-- **A function-frame head is a step.** -/
theorem frameHead_sound (hrec : Sound P host fx intr s rec) {fi : Frame} {n : Nat}
    {body r : List AdminFX} (h : frameHead rec K t n fi body = some (K', t', r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.frame n fi body]⟩, t⟩ ⟨⟨s, K', f, r⟩, t'⟩ := by
  unfold frameHead at h
  split at h
  · rename_i ws hsp
    split at h
    · rename_i hn
      cases h
      have hb : body = fvals ws := by simpa using splitV_eq hsp
      rw [hb]
      exact .lift (.frameVals hn)
    · cases h
  · rename_i ws rest hsp
    split at h
    · rename_i u w hse
      cases h
      exact frameRet_T hsp hse
    · cases h
  · obtain ⟨⟨K₁, t₁, b⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    cases h2
    exact T_frame n f (hrec fi K t body K₁ t₁ b h1)

/-! ## Handlers -/

/-- **A caught `suspend` is a step**, given the context found and its tag. -/
theorem catchAt_sound {hs : List HClause} {E : CtxV} {w : List FVal} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {r : List AdminFX} (htag : s.tag? (E.frameAt f) x = some (ta, ti))
    (hE : ¬ E.Handles ta) (h : catchAt K t hs E w ta = some (K', t', r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.handler hs (E.plug (fvals w ++ [.fx (.suspend x)]))]⟩, t⟩
      ⟨⟨s, K', f, r⟩, t'⟩ := by
  unfold catchAt at h
  split at h
  · rename_i ta' l hfind
    cases h
    have hta : ta' = ta := by simpa [HClause.tag] using List.find?_some hfind
    subst hta
    exact .lift (.suspend htag hE hfind)
  · cases h

/-- **A caught `suspend` is a step.** -/
theorem susHead_sound {tar : Nat → Nat} {d : Nat} {hs : List HClause} {body r : List AdminFX}
    (h : susHead tar s d f K t hs body = some (K', t', r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.handler hs body]⟩, t⟩ ⟨⟨s, K', f, r⟩, t'⟩ := by
  unfold susHead at h
  split at h
  · rename_i E w x hfs
    split at h
    · rename_i ta ti htag
      split at h
      · cases h
      · rename_i hE
        rw [findSus_eq hfs]
        exact catchAt_sound htag (handlesB_false (by simpa using hE)) h
    · cases h
  · cases h

theorem handlerBr_T {hs : List HClause} {body rest : List AdminFX} {ws : List FVal} {l : LabelIdx}
    (hsp : splitV body = (ws, .core (.plain (.br l)) :: rest)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.handler hs body]⟩, t⟩
      ⟨⟨s, K, f, fvals ws ++ [.core (.plain (.br l))]⟩, t⟩ := by
  rw [splitV_eq hsp]
  exact T_conv (.lift (.brHandler (hs := hs) (rest := rest))) (by simp) rfl

theorem handlerRet_T {hs : List HClause} {body rest : List AdminFX} {ws : List FVal}
    (hsp : splitV body = (ws, .core (.plain .return_) :: rest)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.handler hs body]⟩, t⟩
      ⟨⟨s, K, f, fvals ws ++ [.core (.plain .return_)]⟩, t⟩ := by
  rw [splitV_eq hsp]
  exact T_conv (.lift (.returnHandler (hs := hs) (rest := rest))) (by simp) rfl

/-- **A handler-frame head is a step.** -/
theorem handlerHead_sound (hrec : Sound P host fx intr s rec) {tar : Nat → Nat} {d : Nat}
    {hs : List HClause} {body r : List AdminFX}
    (h : handlerHead tar s rec d f K t hs body = some (K', t', r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.handler hs body]⟩, t⟩ ⟨⟨s, K', f, r⟩, t'⟩ := by
  unfold handlerHead at h
  split at h
  · rename_i ws hsp
    cases h
    have hb : body = fvals ws := by simpa using splitV_eq hsp
    rw [hb]
    exact .lift .handlerVals
  · rename_i ws l rest hsp
    cases h
    exact handlerBr_T hsp
  · rename_i ws rest hsp
    cases h
    exact handlerRet_T hsp
  · split at h
    · rename_i r₁ h1
      obtain ⟨K₁, t₁, b⟩ := r₁
      cases h
      exact T_handler hs (hrec f K t body K₁ t₁ b h1)
    · exact susHead_sound h

end Silmaril.Proofs.Wasm.Models.FXTRun
