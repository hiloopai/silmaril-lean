module

public import Silmaril.Wasm.SpecTec.Sim20.Route.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms
public import Silmaril.Wasm.Versions.Thms

/-!
# The 2.0 composite route, proved in refined form

`Task.composite20` asks for a **non-empty** run of wasm-3.0 backend steps (`TransGen`) matching
each V2 step. Round 6's multi-step corollary `Round6.Int.runsR_backend` gives a possibly empty
run (`RSteps`, a `ReflTransGen`), and the one-step `wholeStepValidR_backend` cannot be chained
directly because its target `d'` is related to the Core successor only by `Bwd.ConfigEq`, under
which the encodings differ (`CALL_REF` annotations). So the composite is proved here with `RSteps`:

* `detSteps_of_steps`: a Core run from a configuration all of whose reachable configurations
  have at most one successor is a run of only-successor steps (`DetSteps`);
* `composite20R`: `Task.composite20` with `RSteps` for `TransGen` (`Task.composite20R`), proved
  from `TrackEFwd` and `runsR_backend`;
* `composite20_sim`, `composite20_steps`: the same along the copied Track E simulation
  `Silmaril.Wasm.V2.Execution.Step.toCore` / `Steps.toCore` (relation `Sim`, not a translation
  function), for one V2 step and for V2 runs. These need no `TrackEFwd` hypothesis.

Everything is about the **wasm-3.0** script; the 2.0 script's rules enter only through the census
and the per-rule theorems of `Sim20.Pure`/`Sim20.State`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (HostFinite configV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Target (DetStep DetSteps RSteps)
open Silmaril.Wasm.SpecTec.Sim.Round5.Target (BoundedReachSel)

variable {H : Type}

/-- Every configuration reachable from `c` has at most one successor. -/
def DetFrom (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c₁, Steps P host c c₁ → ∀ c₂ c₃, Step P host c₁ c₂ → Step P host c₁ c₃ → c₂ = c₃

/-- **A run from a deterministic region is a run of only-successor steps.** -/
theorem detSteps_of_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hd : DetFrom P host c) : DetSteps P host c c' := by
  revert hd
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => .refl
  | @head c₀ c₁ hstep _ ih =>
    intro hd
    have hd₁ : DetFrom P host c₁ := fun c₂ h₂ => hd c₂ (.head hstep h₂)
    have hdet : DetStep P host c₀ c₁ := ⟨hstep, fun c₃ h₃ => hd c₀ .refl _ _ h₃ hstep⟩
    exact .head hdet (ih hd₁)

/-- `RunGood` gives what `runsR_backend` needs. -/
theorem runGood_parts {P : Profile} {host : HostSemantics H} {c : Config H}
    (h : RunGood P host c) :
    (∃ ts, ConfigOk c ts) ∧ BoundedReachSel P host c ∧ DetFrom P host c :=
  ⟨(h c .refl).1, fun c₁ h₁ => (h c₁ h₁).2.1, fun c₁ h₁ => (h c₁ h₁).2.2.2⟩

/-- **The 2.0 composite route, refined** (`Task.composite20` with a possibly empty run). -/
def Task.composite20R : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice) (host20 : V2.Execution.HostSemantics H)
        (tr : V2.Execution.Config H → Config H),
        TrackEFwd (Profile.spec nd r) host20 host tr →
        ∃ B : Builtins, ∀ c c' : V2.Execution.Config H,
          V2.Execution.Step (Profile.spec nd r) host20 c c' →
          RunGood (Profile.spec nd r) host (tr c) →
          ∃ d', Sim.Bwd.ConfigEq (tr c') d' ∧
            RSteps Sim.Round6.Int.backend B (configV hn (tr c)) (configV hn d')

/-- **`Task.composite20R` holds**, at Round 6's builtins `BI`. -/
theorem composite20R : Task.composite20R := by
  intro H hn hinj host hf hh nd r host20 tr hE
  refine ⟨Sim.Round4Int.BI (Profile.spec nd r) hn host, fun c c' hstep hgood => ?_⟩
  obtain ⟨⟨ts, hok⟩, hb, hd⟩ := runGood_parts hgood
  have hrun : Steps (Profile.spec nd r) host (tr c) (tr c') := (hE c c' hstep).to_reflTransGen
  exact (Sim.Round6.Int.runsR_backend hinj hf hh).1 _ _ ts hok hb (detSteps_of_steps hrun hd)

/-- **One V2 step, along the copied Track E simulation `Step.toCore`, then Round 6**: the Core
image takes a non-empty run to a configuration related to the V2 successor, and wasm-3.0 backend
steps reach the encoding of a `ConfigEq`-twin of it. -/
theorem composite20_sim {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
    (hf : HostFinite host) (hh : HostOk host) {nd : Bool} {r : RelaxedChoice}
    {src : V2.Execution.HostSemantics H} (hosts : V2.Execution.HostCompatible src host)
    {a b : V2.Execution.Config H} {c : Config H}
    (hab : V2.Execution.Step (Profile.spec nd r) src a b) (hs : V2.Execution.Sim a c)
    {ts : List CValType} (hok : ConfigOk c ts) (hb : BoundedReachSel (Profile.spec nd r) host c)
    (hd : DetFrom (Profile.spec nd r) host c) :
    ∃ c', V2.Execution.Sim b c' ∧ Relation.TransGen (Step (Profile.spec nd r) host) c c' ∧
      ∃ d, Sim.Bwd.ConfigEq c' d ∧ RSteps Sim.Round6.Int.backend
        (Sim.Round4Int.BI (Profile.spec nd r) hn host) (configV hn c) (configV hn d) := by
  obtain ⟨c', ht, hs'⟩ := V2.Execution.Step.toCore hosts hab hs
  obtain ⟨d, hEq, hR⟩ := (Sim.Round6.Int.runsR_backend hinj hf hh).1 _ _ ts hok hb
    (detSteps_of_steps ht.to_reflTransGen hd)
  exact ⟨c', hs', ht, d, hEq, hR⟩

/-- **V2 runs, along `Steps.toCore`, then Round 6.** -/
theorem composite20_steps {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
    (hf : HostFinite host) (hh : HostOk host) {nd : Bool} {r : RelaxedChoice}
    {src : V2.Execution.HostSemantics H} (hosts : V2.Execution.HostCompatible src host)
    {a b : V2.Execution.Config H} {c : Config H}
    (hab : V2.Execution.Steps (Profile.spec nd r) src a b) (hs : V2.Execution.Sim a c)
    {ts : List CValType} (hok : ConfigOk c ts) (hb : BoundedReachSel (Profile.spec nd r) host c)
    (hd : DetFrom (Profile.spec nd r) host c) :
    ∃ c', V2.Execution.Sim b c' ∧ Steps (Profile.spec nd r) host c c' ∧
      ∃ d, Sim.Bwd.ConfigEq c' d ∧ RSteps Sim.Round6.Int.backend
        (Sim.Round4Int.BI (Profile.spec nd r) hn host) (configV hn c) (configV hn d) := by
  obtain ⟨c', ht, hs'⟩ := V2.Execution.Steps.toCore hosts hab hs
  obtain ⟨d, hEq, hR⟩ := (Sim.Round6.Int.runsR_backend hinj hf hh).1 _ _ ts hok hb
    (detSteps_of_steps ht hd)
  exact ⟨c', hs', ht, d, hEq, hR⟩

/-! ## The 1.0 route

A 1.0 run goes through the copied 1.0 → Lime1 → 2.0 simulation (`V1.Execution.Steps.toV2`, at
`v2Profile = Profile.spec`), then through `composite20_steps`. As for 2.0, the SpecTec side is
the **3.0** script; the 1.0 script enters through the census (`census_pure_10_20` and friends):
13 of 1.0's 29 `Step_pure` rules are 2.0's byte for byte. -/

/-- **V1 runs, through 2.0 and Core 3.0, then Round 6.** -/
theorem composite10_steps {hn : H → String} (hinj : Function.Injective hn)
    {host : HostSemantics H} (hf : HostFinite host) (hh : HostOk host)
    {src : Silmaril.Wasm.V1.Execution.HostSemantics H}
    {tgt : V2.Execution.HostSemantics H}
    (hosts₁ : Silmaril.Wasm.Lime1.Execution.ToV2.HostCompatible
      (src.mapCode Silmaril.Wasm.V1.Func.toLime) tgt)
    (hosts₂ : V2.Execution.HostCompatible tgt host)
    {a b : Silmaril.Wasm.V1.Execution.Config H} {e : V2.Execution.Config H} {c : Config H}
    (hab : Silmaril.Wasm.V1.Execution.Steps src a b)
    (he : Silmaril.Wasm.Lime1.Execution.ToV2.Sim a.toLime e) (hs : V2.Execution.Sim e c)
    {ts : List CValType} (hok : ConfigOk c ts) (hb : BoundedReachSel Profile.spec host c)
    (hd : DetFrom Profile.spec host c) :
    ∃ e' c', Silmaril.Wasm.Lime1.Execution.ToV2.Sim b.toLime e' ∧ V2.Execution.Sim e' c' ∧
      Steps Profile.spec host c c' ∧
      ∃ d, Sim.Bwd.ConfigEq c' d ∧ RSteps Sim.Round6.Int.backend
        (Sim.Round4Int.BI Profile.spec hn host) (configV hn c) (configV hn d) := by
  obtain ⟨e', hee, he'⟩ := Silmaril.Wasm.V1.Execution.Steps.toV2 hosts₁ hab he
  obtain ⟨c', hs', hcc, d, hEq, hR⟩ := composite20_steps hinj hf hh hosts₂ hee hs hok hb hd
  exact ⟨e', c', he', hs', hcc, d, hEq, hR⟩

end Silmaril.Wasm.SpecTec.Sim20
