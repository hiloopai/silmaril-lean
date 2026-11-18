module

public import Silmaril.Semantics.Region.Simulation.Defs
public import Silmaril.Semantics.Region.Semantic.Thms
import Silmaril.Proofs.Semantics.Region.Simulation

public section

namespace Silmaril.Semantics.Region

variable {Small Full Lab Event SmallStop FullStop : Type*}
variable {small : TransitionSystem Small Lab Event SmallStop}
variable {full : TransitionSystem Full Lab Event FullStop} {support : Lab → Prop}

theorem Realizes.firstExit (map : Realizes small full) {s out : Small} {trace : List Event}
    (run : FirstExit small support s trace out) {initial} (related : map.relates s initial) :
    ∃ final, FirstExit full support initial trace final ∧ map.relates out final :=
  SimulationProofs.liftExit map run related

theorem FirstExit.completes (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) : ExitsNormally full support s trace out :=
  SimulationProofs.completes det run

theorem ExitsNormally.not_diverges {s out : Full} {trace : List Event}
    (run : ExitsNormally full support s trace out) : ¬ Diverges full support s :=
  finishes_not_diverges run.finishes

theorem ExitsNormally.not_stuck {s out mid : Full} {trace eventsSoFar : List Event}
    (run : ExitsNormally full support s trace out)
    (inside : Inside full support s eventsSoFar mid) : ¬ Stuck full mid := by
  intro stuck
  rcases run.finishes.2 eventsSoFar mid inside with ⟨stop, halt⟩ | ⟨events, next, step⟩
  · exact stuck.2 stop halt
  · exact stuck.1 events next step

/-- Transfer a property of every simple first exit from a settled entry. The
witness certifies non-vacuity; determinacy makes the property hold of every
full first exit and excludes stuck states, halts and divergence before it. -/
theorem Realizes.liftProperty (map : Realizes small full) (det : Determinate full)
    {s : Small} {initial : Full} (related : map.relates s initial)
    (settled : ∃ trace out, FirstExit small support s trace out)
    (P : List Event → Small → Prop) (proved : ∀ trace out, FirstExit small support s trace out → P trace out) :
    (∃ trace final, ExitsNormally full support initial trace final) ∧
    ∀ trace final, FirstExit full support initial trace final → ∃ out, map.relates out final ∧ P trace out :=
  SimulationProofs.liftProperty map det related settled P proved

/-- The Region WP discharges the halt half of non-UB. The event half is
independent: a UB event can occur on an execution that never halts. -/
theorem noUB_of_wp {admit : Small → Prop} {ubEvent : Event → Prop} {ubStop : SmallStop → Prop}
    {Q : Lab → List Event → Small → Prop}
    (events : ∀ event, ubEvent event → ¬ MayEffect small admit support event)
    (halts : ∀ s, admit s → wp small support Q (fun stop _ _ => ¬ ubStop stop) s) :
    NoUB small admit support ubEvent ubStop :=
  ⟨events, ((wp_iff Q (fun stop _ _ => ¬ ubStop stop)).mpr halts).2⟩

/-- Non-UB removes the only stops the total contract permits. Progress and
internal termination then give a normal first exit, not just a partial proof. -/
theorem TotalHoare.firstExit_of_noUB {admit : Small → Prop} {ubEvent : Event → Prop}
    {ubStop : SmallStop → Prop} {Q : Lab → List Event → Small → Prop} {s : Small}
    (contract : TotalHoare small admit support Q (fun stop _ _ => ubStop stop))
    (safe : NoUB small admit support ubEvent ubStop) (admitted : admit s) (entry : support (small.pc s)) :
    ∃ trace out, FirstExit small support s trace out := SimulationProofs.contractExit admitted entry safe contract

theorem TotalHoare.noHalt_of_noUB {admit : Small → Prop} {ubEvent : Event → Prop}
    {ubStop : SmallStop → Prop} {Q : Lab → List Event → Small → Prop}
    (contract : TotalHoare small admit support Q (fun stop _ _ => ubStop stop))
    (safe : NoUB small admit support ubEvent ubStop) {s mid es stop} (admitted : admit s)
    (prior : Inside small support s es mid) : ¬ small.halt mid stop :=
  fun halt => safe.2 s es mid stop admitted prior halt (contract.1.2 s es mid stop admitted prior halt)

/-- Transfer a proved simple contract once all its admitted executions are
non-UB. Every full first exit refines a simple exit with the same label and
trace and a related final state. The full system cannot get stuck, halt or
diverge inside support. The returned non-UB theorem and total contract can
be reused at the next layer. Only the full system must be determinate. -/
theorem Realizes.transferContract (map : Realizes small full) (det : Determinate full)
    {admit : Small → Prop} {admitFull : Full → Prop} {ubEvent : Event → Prop}
    {ubStop : SmallStop → Prop} {ubFullStop : FullStop → Prop} {Q : Lab → List Event → Small → Prop}
    (safe : NoUB small admit support ubEvent ubStop)
    (contract : TotalHoare small admit support Q (fun stop _ _ => ubStop stop))
    (entry : ∀ s, admit s → support (small.pc s))
    (initial : ∀ t, admitFull t → ∃ s, admit s ∧ map.relates s t) :
    NoUB full admitFull support ubEvent ubFullStop ∧
    TotalHoare full admitFull support (fun label es t => ∃ s, map.relates s t ∧ Q label es s)
      (fun stop _ _ => ubFullStop stop) ∧ map.RefinesExits admit admitFull support :=
  SimulationProofs.transferContract map det safe contract entry initial

theorem Realizes.RefinesExits.comp {Larger LargerStop : Type*}
    {larger : TransitionSystem Larger Lab Event LargerStop} {first : Realizes small full} {second : Realizes full larger}
    {admit : Small → Prop} {admitFull : Full → Prop} {admitLarge : Larger → Prop}
    (left : first.RefinesExits admit admitFull support) (right : second.RefinesExits admitFull admitLarge support) :
    (first.comp second).RefinesExits admit admitLarge support := by
  intro initial es final admitted run
  obtain ⟨mid, out, ha, hr, exit, output⟩ := right initial es final admitted run
  obtain ⟨s, t, hs, enters, smallExit, leaves⟩ := left mid es out ha exit
  exact ⟨s, t, hs, ⟨mid, enters, hr⟩, smallExit, ⟨out, leaves, output⟩⟩

end Silmaril.Semantics.Region
