module

public import Silmaril.Wasm.SpecTec.Sim.Round4.Defs

/-!
# Round 4: from one step to runs

Core proves subject reduction: `Step.preservation` (silmaril-lean,
`Execution/Core/Soundness/Preservation.lean`) keeps `ConfigOk c ts` along every step for a
`HostOk` host, and `Steps.safe` along runs. So validity of the source needs no hypothesis along a
run. `Bounded` is not preserved (`Round4.not_bounded_preserved`), so runs are assumed to stay
bounded (`BoundedReach`).

The frozen one-step target relates each Core step to a SpecTec step from the image of the *same*
Core configuration, up to `ConfigEq` on the successor. That does not compose: the SpecTec
successor is the image of a witness `d' ≈ c'`, which need not be valid (after `return_call_ref`
out of a frame SpecTec keeps an index the caller's module need not define), so the one-step
theorem says nothing about the next SpecTec step. `OneStepRel` states the one-step simulation
along the relation `SimRel` (witness `d ≈ c`, `Typed`), and composes:

* `steps_sim`: every Core run from a valid `c₀` that stays bounded is matched by a SpecTec run
  from the image of any witness, ending at a witness of the Core endpoint;
* `ssteps_sim`: every SpecTec run from the image of a witness is matched by a Core run;
* `vals_iff`: the observable values agree. Core reaches `s'; f'; vals vs` with the image of
  `s; f` iff SpecTec reaches the image of `s; f; vals vs`, because `ConfigEq` is equality on code
  without `CALL_REF` (`Bwd.cfgEq_deep`) and an image of a value sequence decodes to it
  (`eq_vals_of_image`).

`CodeEq` is symmetric (`codeEq_symm`), which the backward observable needs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics
open Bwd (AdminEq CodeEq ConfigEq)

variable {H : Type}

mutual
/-- `AdminEq` is symmetric. -/
theorem adminEq_symm : ∀ {a b : Admin}, AdminEq a b → AdminEq b a
  | _, _, .refl a => .refl a
  | _, _, .call ha hb => .call hb ha
  | _, _, .label h => .label (codeEq_symm h)
  | _, _, .handler h => .handler (codeEq_symm h)
  | _, _, .frame h => .frame (codeEq_symm h)

/-- `CodeEq` is symmetric. -/
theorem codeEq_symm : ∀ {l j : List Admin}, CodeEq l j → CodeEq j l
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (adminEq_symm h) (codeEq_symm t)
end

/-- `ConfigEq` is symmetric. -/
theorem configEq_symm {c d : Config H} (h : ConfigEq c d) : ConfigEq d c :=
  ⟨h.1.symm, h.2.1.symm, codeEq_symm h.2.2⟩

variable {B : Builtins} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **Core runs are SpecTec runs, along `SimRel`.** -/
theorem steps_sim (h : OneStepRel B hn P host) (hhost : HostOk host) {c₀ d₀ : Config H}
    {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReach P host c₀)
    (hd : SimRel B hn c₀ d₀) {c : Config H} (hs : Steps P host c₀ c) :
    ∃ d, SimRel B hn c d ∧ SSteps (simEnv B) (configV hn d₀) (configV hn d) := by
  induction hs with
  | refl => exact ⟨d₀, hd, .refl⟩
  | @tail c₁ c₂ h₁ h₂ ih =>
    obtain ⟨d₁, hr₁, hr⟩ := ih
    have hok := (Steps.safe hhost hc h₁).1
    obtain ⟨d₂, hr₂, hst⟩ := h.1 c₁ d₁ c₂ ts hok (hb c₁ h₁) hr₁ (hb c₂ (h₁.tail h₂)) h₂
    exact ⟨d₂, hr₂, hr.tail hst⟩

/-- **SpecTec runs are Core runs, along `SimRel`.** -/
theorem ssteps_sim (h : OneStepRel B hn P host) (hhost : HostOk host) {c₀ d₀ : Config H}
    {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReach P host c₀)
    (hd : SimRel B hn c₀ d₀) {w : Value} (hs : SSteps (simEnv B) (configV hn d₀) w) :
    ∃ c d, SimRel B hn c d ∧ w = configV hn d ∧ Steps P host c₀ c := by
  induction hs with
  | refl => exact ⟨c₀, d₀, hd, rfl, .refl⟩
  | @tail w₁ w₂ _ h₂ ih =>
    obtain ⟨c₁, d₁, hr₁, rfl, hs₁⟩ := ih
    have hok := (Steps.safe hhost hc hs₁).1
    obtain ⟨c₂, d₂, hr₂, hw, hst⟩ := h.2 c₁ d₁ ts w₂ hok (hb c₁ hs₁) hr₁ h₂
    exact ⟨c₂, d₂, hr₂, hw, hs₁.tail hst⟩

/-- A witness of a configuration without `CALL_REF` in its code is the configuration itself. -/
theorem simRel_deep {c d : Config H} (hp : Bwd.codeDeep c.code = true) (h : SimRel B hn c d) :
    d = c :=
  Bwd.cfgEq_deep hp h.1

/-- A code sequence with the image of a value sequence is that value sequence. -/
theorem eq_vals_of_image (B : Builtins) :
    ∀ {l : List Admin} {vs : List Val}, adminsToV l = adminsToV (vals vs) → l = vals vs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [vals, adminsToV] at h
  | _ :: _, [], h => by simp [vals, adminsToV] at h
  | a :: l, v :: vs, h => by
    simp only [vals, List.map_cons, adminsToV, List.cons.injEq] at h
    obtain ⟨ha, hl⟩ := h
    have hv : HasTyp (simEnv B) VarEnv.empty (.varT "val" []) (adminToV a) := by
      rw [ha, State.adminToV_toAdmin]
      exact Typing.typedV_val v _ ⟨rfl, rfl, rfl⟩
    obtain ⟨v', rfl⟩ := (Typing.stateDecode_simEnv B).val a _ ⟨rfl, rfl, rfl⟩ hv
    rw [State.adminToV_toAdmin, State.adminToV_toAdmin] at ha
    obtain rfl := Typing.valV_injective ha
    have := eq_vals_of_image B (l := l) (vs := vs) hl
    simp only [vals, List.map_cons, this]

/-- **Observable values agree.** From a valid, `Typed` source whose runs stay bounded, Core
reaches the values `vs` with a state whose image is that of `s; f` iff SpecTec reaches the image
of `s; f; vs`. (The values are compared exactly; the state through its image, since `storeV` is
not injective on invalid instructions.) -/
theorem vals_iff (h : OneStepRel B hn P host) (hhost : HostOk host) {c₀ : Config H}
    {ts : List CValType} (hc : ConfigOk c₀ ts) (hb : BoundedReach P host c₀)
    (ht : Typed (simEnv B) hn c₀) (s : Store H) (f : Frame) (vs : List Val) :
    (∃ s' f', Steps P host c₀ ⟨s', f', vals vs⟩ ∧ stateV hn s' f' = stateV hn s f) ↔
      SSteps (simEnv B) (configV hn c₀) (configV hn ⟨s, f, vals vs⟩) := by
  have h₀ : SimRel B hn c₀ c₀ := ⟨Bwd.ConfigEq.refl c₀, ht⟩
  constructor
  · rintro ⟨s', f', hs, hst⟩
    obtain ⟨d, hr, hss⟩ := steps_sim h hhost hc hb h₀ hs
    rw [simRel_deep (Bwd.codeDeep_vals vs) hr] at hss
    have e : configV hn ⟨s', f', vals vs⟩ = configV hn ⟨s, f, vals vs⟩ := by
      simp only [configV, hst]
    exact e ▸ hss
  · intro hs
    obtain ⟨c, d, hr, he, hss⟩ := ssteps_sim h hhost hc hb h₀ hs
    obtain ⟨sd, fd, cd⟩ := d
    have he' : stateV hn s f = stateV hn sd fd ∧ adminsToV (vals vs) = adminsToV cd := by
      simpa [configV] using he
    obtain rfl := eq_vals_of_image B he'.2.symm
    obtain rfl := Bwd.cfgEq_deep (Bwd.codeDeep_vals vs) (configEq_symm hr.1)
    exact ⟨sd, fd, hss, he'.1.symm⟩

end Silmaril.Wasm.SpecTec.Sim.Round4
