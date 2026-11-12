module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.Defs
public import Silmaril.Wasm.SpecTec.Sim.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# Round 7, `BD`: context lifting at `configVD`

`Sim.Assembly` lifts a SpecTec step through the four context rules at `configV`
(`fwd_ctxtInstrs`, `fwd_ctxtLabel`, `fwd_ctxtHandler`, `fwd_ctxtFrame`). The same works at
`configVD`, in every `simEnv B`: the value-level rule lemmas (`Sim.sstep_ctxtInstrs`, …) are
stated at arbitrary values, and the typing of the pieces comes from round 7's
`MemSimd.typingFactsD_simEnv` and round 3's `Typing.typedV_admin3`. A value prefix has no memory
SIMD instruction, so its `adminsToVD` image is its `adminsToV` image (`adminsToVD_vals`).

* `fwdD_ctxtInstrs`, `fwdD_ctxtLabel`, `fwdD_ctxtHandler`, `fwdD_ctxtFrame`: the four liftings.
* `fwdD_ctxStep`: **`FwdPD` is closed under `CtxStep`**, for leaves at a fixed store (the source
  store does not change through a context).
* `step_of_ctxStep`: a `CtxStep` of Core steps is a Core step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCtx

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (storeVD stateVD configVD adminsToVD adminToVD TypedD typingFactsD_simEnv
  adminsToVD_append adminsToVD_vals adminsToVD_eq_map)

variable {H : Type} {hn : H → String}

/-- A non-empty sequence has a non-empty `adminsToVD` image. -/
theorem adminsToVD_ne_nil {l : List Admin} (h : l ≠ []) : adminsToVD l ≠ [] := by
  rw [adminsToVD_eq_map]
  exact fun he => h (List.map_eq_nil_iff.1 he)

/-- **`Step.ctxtInstrs`, forward, at `configVD`.** -/
theorem fwdD_ctxtInstrs (B : Builtins) {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : FwdPD (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdPD (simEnv B) hn ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro hc hc'
  have TD := typingFactsD_simEnv B hn
  have T := Typing.typingFacts_simEnv B hn
  have e₁ : adminsToVD (vals vs ++ is ++ rest) =
      adminsToV (vals vs) ++ adminsToVD is ++ adminsToVD rest := by
    simp only [adminsToVD_append, adminsToVD_vals]
  have e₂ : adminsToVD (vals vs ++ is' ++ rest) =
      adminsToV (vals vs) ++ adminsToVD is' ++ adminsToVD rest := by
    simp only [adminsToVD_append, adminsToVD_vals]
  obtain ⟨hst, hcode⟩ := (TD.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (TD.config _).1 hc'
  have hc₁ : TypedV (simEnv B) instrsT
      (.list (adminsToV (vals vs) ++ adminsToVD is ++ adminsToVD rest)) := e₁ ▸ hcode
  have hc₂ : TypedV (simEnv B) instrsT
      (.list (adminsToV (vals vs) ++ adminsToVD is' ++ adminsToVD rest)) := e₂ ▸ hcode'
  obtain ⟨hvi, hrest⟩ := (TD.append _ _).1 hc₁
  obtain ⟨hv, his⟩ := (TD.append _ _).1 hvi
  obtain ⟨hvi', -⟩ := (TD.append _ _).1 hc₂
  obtain ⟨-, his'⟩ := (TD.append _ _).1 hvi'
  have hin : TypedD (simEnv B) hn ⟨s, f, is⟩ := (TD.config _).2 ⟨hst, his⟩
  have hin' : TypedD (simEnv B) hn ⟨s', f', is'⟩ := (TD.config _).2 ⟨hst', his'⟩
  have hne' : adminsToV (vals vs) ≠ [] ∨ adminsToVD rest ≠ [] := by
    rcases hne with h | h
    · exact .inl (adminsToV_ne_nil (by simpa [vals] using h))
    · exact .inr (adminsToVD_ne_nil h)
  have hg := sstep_ctxtInstrs (hasStepRules_simEnv B).ctxtInstrs hst hst' (T.vals vs hv) his his'
    hrest hne' (ih hin hin')
  change SStep (simEnv B) (cfgV _ (adminsToVD (vals vs ++ is ++ rest)))
    (cfgV _ (adminsToVD (vals vs ++ is' ++ rest)))
  rw [e₁, e₂]
  exact hg

set_option maxRecDepth 100000 in
/-- **`Step.ctxtLabel`, forward, at `configVD`.** -/
theorem fwdD_ctxtLabel (B : Builtins) {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List Instr} {is is' : List Admin} (ih : FwdPD (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdPD (simEnv B) hn ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  intro hc hc'
  have TD := typingFactsD_simEnv B hn
  obtain ⟨hst, hcode⟩ := (TD.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (TD.config _).1 hc'
  obtain ⟨hn₀, hcont, his⟩ := Typing.typedV_admin3 (Typing.closedT_list "instr") rfl hcode
  obtain ⟨-, -, his'⟩ := Typing.typedV_admin3 (Typing.closedT_list "instr") rfl hcode'
  have hin : TypedD (simEnv B) hn ⟨s, f, is⟩ := (TD.config _).2 ⟨hst, his⟩
  have hin' : TypedD (simEnv B) hn ⟨s', f', is'⟩ := (TD.config _).2 ⟨hst', his'⟩
  exact sstep_ctxtLabel (hasStepRules_simEnv B).ctxtLabel hst hst' hn₀ hcont his his' (ih hin hin')

set_option maxRecDepth 100000 in
/-- **`Step.ctxtHandler`, forward, at `configVD`.** -/
theorem fwdD_ctxtHandler (B : Builtins) {s s' : Store H} {f f' : Frame} {n : Nat}
    {cs : List Catch} {is is' : List Admin} (ih : FwdPD (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdPD (simEnv B) hn ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  intro hc hc'
  have TD := typingFactsD_simEnv B hn
  obtain ⟨hst, hcode⟩ := (TD.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (TD.config _).1 hc'
  obtain ⟨hn₀, hcs, his⟩ := Typing.typedV_admin3 (Typing.closedT_list "catch") rfl hcode
  obtain ⟨-, -, his'⟩ := Typing.typedV_admin3 (Typing.closedT_list "catch") rfl hcode'
  have hin : TypedD (simEnv B) hn ⟨s, f, is⟩ := (TD.config _).2 ⟨hst, his⟩
  have hin' : TypedD (simEnv B) hn ⟨s', f', is'⟩ := (TD.config _).2 ⟨hst', his'⟩
  exact sstep_ctxtHandler (hasStepRules_simEnv B).ctxtHandler hst hst' hn₀ hcs his his'
    (ih hin hin')

set_option maxRecDepth 100000 in
/-- **`Step.ctxtFrame`, forward, at `configVD`.** -/
theorem fwdD_ctxtFrame (B : Builtins) {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (ih : FwdPD (simEnv B) hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    FwdPD (simEnv B) hn ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  intro hc hc'
  have TD := typingFactsD_simEnv B hn
  obtain ⟨hst, hcode⟩ := (TD.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (TD.config _).1 hc'
  obtain ⟨hs, hf⟩ := (TD.state _ _).1 hst
  obtain ⟨hs', -⟩ := (TD.state _ _).1 hst'
  obtain ⟨hn₀, hfi, his⟩ := Typing.typedV_admin3 (Typing.closedT_var "frame") rfl hcode
  obtain ⟨-, hfi', his'⟩ := Typing.typedV_admin3 (Typing.closedT_var "frame") rfl hcode'
  have hin : TypedD (simEnv B) hn ⟨s, fi, is⟩ := (TD.config _).2 ⟨(TD.state _ _).2 ⟨hs, hfi⟩, his⟩
  have hin' : TypedD (simEnv B) hn ⟨s', fi', is'⟩ :=
    (TD.config _).2 ⟨(TD.state _ _).2 ⟨hs', hfi'⟩, his'⟩
  exact sstep_ctxtFrame (hasStepRules_simEnv B).ctxtFrame hs hs' hf hfi hfi' hn₀ his his'
    (ih hin hin')

/-- **`FwdPD` is closed under the context constructors**, for leaves at the source store `s₀`. -/
theorem fwdD_ctxStep (B : Builtins) {L : Config H → Config H → Prop} {s₀ : Store H}
    (hL : ∀ c c', L c c' → c.store = s₀ → FwdPD (simEnv B) hn c c') :
    ∀ {c c' : Config H}, CtxStep L c c' → c.store = s₀ → FwdPD (simEnv B) hn c c'
  | _, _, .leaf h, hs => hL _ _ h hs
  | _, _, .instrs h hne, hs => fwdD_ctxtInstrs B hne (fwdD_ctxStep B hL h hs)
  | _, _, .label h, hs => fwdD_ctxtLabel B (fwdD_ctxStep B hL h hs)
  | _, _, .handler h, hs => fwdD_ctxtHandler B (fwdD_ctxStep B hL h hs)
  | _, _, .frame h, hs => fwdD_ctxtFrame B (fwdD_ctxStep B hL h hs)

/-- **A `CtxStep` of Core steps is a Core step.** -/
theorem step_of_ctxStep {P : Numerics.Profile} {host : HostSemantics H}
    {L : Config H → Config H → Prop} (hL : ∀ c c', L c c' → Step P host c c') :
    ∀ {c c' : Config H}, CtxStep L c c' → Step P host c c'
  | _, _, .leaf h => hL _ _ h
  | _, _, .instrs h hne => .ctxtInstrs (step_of_ctxStep hL h) hne
  | _, _, .label h => .ctxtLabel (step_of_ctxStep hL h)
  | _, _, .handler h => .ctxtHandler (step_of_ctxStep hL h)
  | _, _, .frame h => .ctxtFrame (step_of_ctxStep hL h)

end Silmaril.Wasm.SpecTec.Sim.Round7.HCtx
