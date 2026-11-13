module

public import Silmaril.Proofs.Wasm.Models.FXAsyncSus.Unique

/-!
# The intended `suspend` configuration is inevitable

**`inev_sus`** (see `Silmaril.Proofs.Wasm.Models.FXAsyncSus.Unique`): from the encoding of a handled
kernel `suspend` whose frame holds exactly the payload, every `StepFX'` run reaches the
configuration after the full split and the `br 0` (where `G` holds), or is stuck without a
result.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXAsyncFX (ix br1 comp)
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (plug_comp frameAt_comp)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (Deep Iso SD TermFX Inev InevP UPath
  deep_plug deep_suspend inev_of_upath)
open Silmaril.Wasm.Numerics (GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}

/-- The code below the resumer's handler frame, ending in the `block btH` label. -/
def preC (Pre : CtxV) (n : Nat) : CtxV := comp Pre (.label n [] (.seq [] .hole [br1]))

theorem deep_enc (Pre : CtxV) (n : Nat) (hR : List HClause) (E : CtxV) (P : List FVal)
    (x : TagIdx) :
    Deep (SX' x) ((preC Pre n).plug [.handler hR (E.plug (fvals P ++ [.fx (.suspend x)]))]) :=
  deep_plug (Deep.handler (V := []) (T := []) (deep_suspend E P x)) _

theorem not_term_enc (Pre : CtxV) (n : Nat) (hR : List HClause) (E : CtxV) (P : List FVal)
    (x : TagIdx) {s : Store H} {K : List (Option ContFX)} {f : Frame} :
    ¬ TermFX (⟨s, K, f,
      (preC Pre n).plug [.handler hR (E.plug (fvals P ++ [.fx (.suspend x)]))]⟩ : ConfigFX H) := by
  rintro ⟨r, hr⟩
  have hd := deep_enc Pre n hR E P x
  rw [show (preC Pre n).plug _ = _ from hr] at hd
  exact nodeep_core hd

/-- The code after a `suspend` step at the resumer's handler, under an isolated context. -/
theorem code_after {Pre₁ Pre : CtxV} {T : List AdminFX}
    (hPre : ∀ Y, Pre.plug Y = Pre₁.plug (Y ++ T)) (n : Nat) (vs : List FVal) (k : Nat) :
    (preC Pre n).plug (fvals vs ++ [.contRef k, .core (.plain (.br (ix 0)))]) =
      Pre₁.plug ([.label n [] (fvals (vs ++ [.cont k]) ++ .core (.plain (.br (ix 0))) :: [br1])] ++
        T) := by
  rw [preC, plug_comp, hPre]
  simp [CtxV.plug, FVal.toAdmin]

/-- Equal canonical forms give equal captured continuations. -/
theorem cont_eq {E E' : CtxV} (hL : (canon E').layers = (canon E).layers)
    (hq : (canon E').post = (canon E).post) (hp : (canon E').pre = (canon E).pre) :
    (⟨E'.plug⟩ : ContFX) = ⟨E.plug⟩ := by
  have h : canon E' = canon E := by
    rcases h₁ : canon E' with ⟨p₁, q₁, L₁⟩
    rcases h₂ : canon E with ⟨p₂, q₂, L₂⟩
    simp only [h₁, h₂] at hL hq hp
    rw [hL, hq, hp]
  rw [plug_eq_of_canon h]

/-- **The intended configuration after a handled `suspend` is inevitable.** -/
theorem inev_sus {Pre₁ Pre : CtxV} (hIso : Iso Pre₁) {T : List AdminFX}
    (hPre : ∀ Y, Pre.plug Y = Pre₁.plug (Y ++ T)) {E : CtxV} (hpre : (canon E).pre = [])
    {s : Store H} {K : List (Option ContFX)} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {P : List FVal} (ht : s.tag? (E.frameAt ((preC Pre (P.length + 1)).frameAt f)) x = some (ta, ti))
    (hE : ¬ E.Handles ta) {G : ConfigFX H → Prop}
    (hG : G ⟨s, K ++ [some ⟨E.plug⟩], f, Pre.plug (fvals (P ++ [.cont K.length]))⟩) :
    InevP (SD o fx) TermFX G ⟨s, K, f, (preC Pre (P.length + 1)).plug
      [.handler [.onLabel ta (ix 0)] (E.plug (fvals P ++ [.fx (.suspend x)]))]⟩ := by
  refine ⟨not_term_enc _ _ _ _ _ _, fun b hb => ?_⟩
  obtain ⟨Eo, hs, E', vs', ta', ti', l, hc, ht', hE', hcl, hbd⟩ :=
    step_sus hb (deep_enc Pre (P.length + 1) _ E P x)
  obtain ⟨rfl, rfl, hEo, hL, hq, hp⟩ := sus_unique hc.symm ht' hE' hcl ht hE
  have hEo' : Eo.plug = (preC Pre (P.length + 1)).plug := plug_eq_of_canon hEo
  have hp' : (canon E').pre ++ vs' = P := by rw [hp, hpre, List.nil_append]
  have hb' : b = ⟨s, K ++ [some ⟨E'.plug⟩], f, Pre₁.plug ([.label (P.length + 1) []
      (fvals (vs' ++ [.cont K.length]) ++ .core (.plain (.br (ix 0))) :: [br1])] ++ T)⟩ := by
    rw [hbd, hEo', code_after hPre]
  rcases hpe : (canon E').pre with _ | ⟨v, ws⟩
  · have hv : vs' = P := by rw [← hp', hpe, List.nil_append]
    have hC : (⟨E'.plug⟩ : ContFX) = ⟨E.plug⟩ := cont_eq hL hq (by rw [hpe, hpre])
    have hu := exit_unique (o := o) (fx := fx) hIso (s := s) (K := K ++ [some ⟨E.plug⟩]) (f := f)
      (vs := P ++ [.cont K.length]) (n := P.length + 1) (l := ix 0) (rest := [br1]) (T := T) rfl
      (by simp)
    rw [hb', hC, hv]
    exact inev_of_upath (UPath.one hu) (by rw [← hPre]; exact hG)
  · have hlt : (vs' ++ [FVal.cont K.length]).length < P.length + 1 := by
      have h₁ : (v :: ws ++ vs').length = P.length := by rw [← hpe, hp']
      have h₂ : ws.length + 1 + vs'.length = P.length := by
        simpa only [List.length_append, List.length_cons] using h₁
      have h₃ : (vs' ++ [FVal.cont K.length]).length = vs'.length + 1 := by simp
      omega
    rw [hb']
    exact exit_dead hIso rfl hlt G

end Silmaril.Proofs.Wasm.Models.FXAsyncSus
