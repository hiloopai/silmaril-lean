module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Route
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# `Task.composite20`, proved

`Task.composite20` asks for a **non-empty** run (`TransGen`) of wasm-3.0 backend steps for each
V2 step. `composite20R` proved it with a possibly empty run (`RSteps`), because Round 6's
multi-step corollary `runsR_backend` is stated with `ReflTransGen`. The obstruction recorded
earlier was that the one-step theorem lands on a `ConfigEq`-twin, so its results do not chain.

They do chain along Round 6's own invariant. `Round6.Target.stepsR_sim` already runs Round 6
along `SimRel` (`ConfigEq` plus typing of the witness), and it takes **exactly one** reading step
per Core step. Run on a non-empty Core run, the same induction gives a non-empty reading run
(`stepsT_sim`). Track E's obligation gives a non-empty Core run, and `RunGood` makes every step
of it go to the only successor (`detTrans_of_trans`). So:

* `detTrans_of_trans`: a non-empty run from a deterministic region is a non-empty run of
  only-successor steps;
* `stepsT_sim`: such a run is matched along `SimRel` by a non-empty run of the reading, under
  `OpenR`;
* **`composite20 : Task.composite20`**, at Round 6's builtins `BI`.

As before, this is a statement about the **wasm-3.0** script, reached from V2 through Track E's
translation; the 2.0 script enters only through the census.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (HostFinite configV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Target (DetStep OpenR Reading)
open Silmaril.Wasm.SpecTec.Sim.Round5.Target (BoundedReachSel)
open Silmaril.Wasm.SpecTec.Sim.Round4 (SimRel)
open Silmaril.Wasm.SpecTec.Sim.Round4Int (BI)

variable {H : Type}

/-- **A non-empty run from a deterministic region is a non-empty run of only-successor
steps.** -/
theorem detTrans_of_trans {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Relation.TransGen (Step P host) c c') (hd : DetFrom P host c) :
    Relation.TransGen (DetStep P host) c c' := by
  induction h with
  | single h => exact .single ⟨h, fun c₃ h₃ => hd c .refl _ _ h₃ h⟩
  | tail h₁ h₂ ih => exact ih.tail ⟨h₂, fun c₃ h₃ => hd _ h₁.to_reflTransGen _ _ h₃ h₂⟩

/-- **Non-empty deterministic Core runs are non-empty runs of the reading, along `SimRel`**,
under `OpenR`: one reading step per Core step (Round 6's `stepsR_sim`, on `TransGen`). -/
theorem stepsT_sim {Rd : Reading} {hn : H → String} {P : Profile} {host : HostSemantics H}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (O : OpenR Rd hn P host) {c₀ d₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
    (hb : BoundedReachSel P host c₀) (hd : SimRel (BI P hn host) hn c₀ d₀) {c : Config H}
    (hs : Relation.TransGen (DetStep P host) c₀ c) :
    ∃ d, SimRel (BI P hn host) hn c d ∧
      Relation.TransGen (Rd.step (BI P hn host)) (configV hn d₀) (configV hn d) := by
  induction hs with
  | single h =>
    obtain ⟨c'', d₂, -, hu, hr₂, hst⟩ := Sim.Round6.Target.fwdRelR_of_open hinj hf hh O c₀ d₀ _
      ts hc (hb c₀ .refl) (fun c' h' => hb c' (.single h')) hd h.1
    obtain rfl := hu h.2
    exact ⟨d₂, hr₂, .single hst⟩
  | @tail c₁ c₂ h₁ h₂ ih =>
    obtain ⟨d₁, hr₁, hr⟩ := ih
    have hrun : Steps P host c₀ c₁ :=
      Sim.Round6.Target.steps_of_detSteps h₁.to_reflTransGen
    have hok := (Steps.safe hh hc hrun).1
    obtain ⟨c'', d₂, -, hu, hr₂, hst⟩ := Sim.Round6.Target.fwdRelR_of_open hinj hf hh O c₁ d₁ c₂
      ts hok (hb c₁ hrun) (fun c' h' => hb c' (hrun.tail h')) hr₁ h₂.1
    obtain rfl := hu h₂.2
    exact ⟨d₂, hr₂, hr.tail hst⟩

/-- **`Task.composite20` holds**, at Round 6's builtins `BI`: every V2 step whose Track E image
only reaches good configurations is matched, up to `Bwd.ConfigEq`, by a non-empty run of
wasm-3.0 backend steps. -/
theorem composite20 : Task.composite20 := by
  intro H hn hinj host hf hh nd r host20 tr hE
  refine ⟨BI (Profile.spec nd r) hn host, fun c c' hstep hgood => ?_⟩
  obtain ⟨⟨ts, hok⟩, hb, hd⟩ := runGood_parts hgood
  have h₀ : SimRel (BI (Profile.spec nd r) hn host) hn (tr c) (tr c) :=
    ⟨Sim.Bwd.ConfigEq.refl _, Sim.Round5.Target.typed_of_configOk_sel _ hn hok (hb _ .refl)⟩
  obtain ⟨d, hr, hT⟩ := stepsT_sim hinj hf hh (Sim.Round6.Int.openR_backend hinj hf hh) hok hb
    h₀ (detTrans_of_trans (hE c c' hstep) hd)
  exact ⟨d, hr.1, hT⟩

end Silmaril.Wasm.SpecTec.Sim20
