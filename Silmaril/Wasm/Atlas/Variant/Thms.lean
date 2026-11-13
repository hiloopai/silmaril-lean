module

public import Silmaril.Wasm.Atlas.Variant.Defs
public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Foundations.ForwardSim
public import Silmaril.Wasm.Execution.Core.Sim.Context

/-!
# Variants of Core and loose models: theorems

* `behavioursOf_eq`, `obsR_step`: Core's observations are `behavioursR` of `Step P host`;
* `behavioursR_mono`: more steps, more observations (finite runs and infinite runs);
* `base_le`, `loose_mono`: the base relation is contained in the loose one, so the base
  observations are loose observations;
* `Ctx` lifting lemmas (`Ctx.append_right`, `Ctx.vals_left`) and the same for `loose` over a
  base relation closed under the contexts (`loose_append_right`, `loose_vals_left`,
  `loose_label`, `loose_handler`, `loose_frame`, for `Step P host`);
* `behavioursR_subset_of_sim`: a lock-step simulation that maps terminal configurations to
  terminal configurations with the same result gives inclusion of observations
  (finite runs by `LockstepSim.steps`, divergence by `ForwardSim.diverges`);
* `toLooseUniv`, `toLooseExist`: the inclusion transitions into a loose chart (reflecting
  universal sentences, preserving existential ones), and `sat_of_loose`: a universal sentence
  of the loose chart holds in every chart included in it.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Variant

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **Core's observations are `behavioursR` of `Step`.** -/
theorem behavioursOf_eq (P : Profile) (host : HostSemantics H) (c : Config H) :
    behavioursOf P host c = behavioursR (Step P host) c := rfl

/-- Core's call observations are `obsR` of the Core step family. -/
theorem obsR_step (P : Profile) (x : Core.Pt H) (c : Core.Call) :
    Core.obs P x c = obsR (Step P) x c := rfl

/-- **More steps, more observations.** -/
theorem behavioursR_mono {R R' : Config H → Config H → Prop} (h : ∀ c c', R c c' → R' c c')
    (c : Config H) : behavioursR R c ⊆ behavioursR R' c := by
  rintro b (⟨c', r, hs, hc, rfl⟩ | ⟨rfl, ⟨tr, h0, ht⟩⟩)
  · exact Or.inl ⟨c', r, Relation.ReflTransGen.mono h _ _ hs, hc, rfl⟩
  · exact Or.inr ⟨rfl, tr, h0, fun n => h _ _ (ht n)⟩

/-- The base relation is contained in the loose relation. -/
theorem base_le {R Q : Config H → Config H → Prop} {c c' : Config H} (h : R c c') :
    loose R Q c c' :=
  Or.inl h

/-- **The base observations are loose observations.** -/
theorem loose_mono (R Q : Config H → Config H → Prop) (c : Config H) :
    behavioursR R c ⊆ behavioursR (loose R Q) c :=
  behavioursR_mono (fun _ _ => base_le) c

/-! ## Context lifting -/

variable {Q : Config H → Config H → Prop}

/-- A context step of `es` is a context step of `es ++ rest`. -/
theorem Ctx.append_right {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    (h : Ctx Q ⟨s, f, es⟩ ⟨s', f', es'⟩) (rest : List Admin) :
    Ctx Q ⟨s, f, es ++ rest⟩ ⟨s', f', es' ++ rest⟩ := by
  simpa [vals] using Ctx.instrs (vs := []) (rest := rest) h

/-- A context step of `es` is a context step of `val* es`. -/
theorem Ctx.vals_left {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    (h : Ctx Q ⟨s, f, es⟩ ⟨s', f', es'⟩) (vs : List Val) :
    Ctx Q ⟨s, f, vals vs ++ es⟩ ⟨s', f', vals vs ++ es'⟩ := by
  simpa using Ctx.instrs (vs := vs) (rest := []) h

variable {P : Profile} {host : HostSemantics H}

theorem loose_append_right {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    (h : loose (Step P host) Q ⟨s, f, es⟩ ⟨s', f', es'⟩) (rest : List Admin) :
    loose (Step P host) Q ⟨s, f, es ++ rest⟩ ⟨s', f', es' ++ rest⟩ :=
  h.imp (fun h => Step.append_right h rest) (fun h => h.append_right rest)

theorem loose_vals_left {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    (h : loose (Step P host) Q ⟨s, f, es⟩ ⟨s', f', es'⟩) (vs : List Val) :
    loose (Step P host) Q ⟨s, f, vals vs ++ es⟩ ⟨s', f', vals vs ++ es'⟩ :=
  h.imp (fun h => Step.vals_left h vs) (fun h => h.vals_left vs)

/-- Lifting through a value prefix and a code suffix at once. -/
theorem loose_ctx {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    (h : loose (Step P host) Q ⟨s, f, es⟩ ⟨s', f', es'⟩) (vs : List Val) (rest : List Admin) :
    loose (Step P host) Q ⟨s, f, vals vs ++ es ++ rest⟩ ⟨s', f', vals vs ++ es' ++ rest⟩ :=
  loose_append_right (loose_vals_left h vs) rest

theorem loose_label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {es es' : List Admin} (h : loose (Step P host) Q ⟨s, f, es⟩ ⟨s', f', es'⟩) :
    loose (Step P host) Q ⟨s, f, [.label n cont es]⟩ ⟨s', f', [.label n cont es']⟩ :=
  h.imp Step.ctxtLabel Ctx.label

theorem loose_handler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {es es' : List Admin} (h : loose (Step P host) Q ⟨s, f, es⟩ ⟨s', f', es'⟩) :
    loose (Step P host) Q ⟨s, f, [.handler n cs es]⟩ ⟨s', f', [.handler n cs es']⟩ :=
  h.imp Step.ctxtHandler Ctx.handler

theorem loose_frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {es es' : List Admin}
    (h : loose (Step P host) Q ⟨s, fi, es⟩ ⟨s', fi', es'⟩) :
    loose (Step P host) Q ⟨s, f, [.frame n fi es]⟩ ⟨s', f, [.frame n fi' es']⟩ :=
  h.imp Step.ctxtFrame Ctx.frame

/-! ## Simulations -/

/-- **A lock-step simulation gives inclusion of observations.** `Rel` relates configurations of
the source relation `S` to configurations of the target relation `T`; every `S` step is
matched by a `T` step, and a terminal source configuration is related only to a terminal
target configuration with the same result. -/
theorem behavioursR_subset_of_sim {S T : Config H → Config H → Prop}
    {Rel : Config H → Config H → Prop}
    (step : ∀ {c c' d : Config H}, S c c' → Rel c d → ∃ d', T d d' ∧ Rel c' d')
    (terminal : ∀ {c d : Config H} {r : Result}, Rel c d → c.code = r.toAdmin →
      d.code = r.toAdmin) {c d : Config H} (h : Rel c d) :
    behavioursR S c ⊆ behavioursR T d := by
  have sim : LockstepSim S T Rel :=
    ⟨fun hs hr => by
      obtain ⟨d', ht, hr'⟩ := step hs hr
      exact ⟨d', .single ht, hr'⟩⟩
  rintro b (⟨c', r, hs, hc, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨d', hd, hr'⟩ := sim.steps hs h
    exact Or.inl ⟨d', r, hd, terminal hr' hc, rfl⟩
  · exact Or.inr ⟨rfl, sim.toForwardSim.diverges hdiv h⟩

/-! ## Charts -/

/-- **Into a loose chart, universal sentences**: a chart whose observations are included in
the loose ones (on its domain) reflects the loose chart's universal sentences. -/
def toLooseUniv {R L : HostSemantics H → Config H → Config H → Prop} {dom dom' : Core.Pt H → Prop}
    (hdom : ∀ x, dom x → dom' x) (h : ∀ x, dom x → ∀ c, obsR R x c ⊆ obsR L x c) :
    Transition (chartR R dom) (chartR L dom') :=
  BTrans.ofSubsetUniv id id hdom h

/-- **Into a loose chart, existential sentences**: a witness is a loose witness. -/
def toLooseExist {R L : HostSemantics H → Config H → Config H → Prop} {dom dom' : Core.Pt H → Prop}
    (hdom : ∀ x, dom x → dom' x) (h : ∀ x, dom x → ∀ c, obsR R x c ⊆ obsR L x c) :
    Transition (chartR R dom) (chartR L dom') :=
  BTrans.ofSubsetExist id id hdom h

/-- **Transfer**: a universal sentence of the loose chart holds at every point whose
observations are included in the loose ones. -/
theorem sat_of_subset {obs obs' : Core.Pt H → Core.Call → Set (Behaviour Val)} {x : Core.Pt H}
    (h : ∀ c, obs x c ⊆ obs' x c) {φ : BSen Core.Call (Behaviour Val)} (hu : φ.Universal)
    (hφ : φ.Sat (obs' x)) : φ.Sat (obs x) :=
  BSen.sat_of_subset_univ h hu hφ

end Silmaril.Wasm.Atlas.Variant
