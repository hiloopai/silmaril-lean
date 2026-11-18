module

public import Silmaril.Semantics.Region.Semantic.Defs

/-! # Realization of a finite region execution across state interfaces -/

@[expose] public section

namespace Silmaril.Semantics.Region

variable {Small Full Larger Lab Event SmallStop FullStop LargerStop : Type*}

/-- No admitted execution can emit a UB event (including on the first exit
edge) or reach a UB halt. This inspects every reachable prefix, including
prefixes of diverging executions. It makes no progress or termination claim,
and does not identify all faults, halts or stuckness with UB. -/
def NoUB (system : TransitionSystem Small Lab Event SmallStop) (admit : Small → Prop)
    (support : Lab → Prop) (ubEvent : Event → Prop) (ubStop : SmallStop → Prop) : Prop :=
  (∀ event, ubEvent event → ¬ MayEffect system admit support event) ∧
  ∀ initial events mid stop, admit initial → Inside system support initial events mid →
    system.halt mid stop → ¬ ubStop stop

/-- A witness-producing map on steps. The relation can carry loading, ABI
or other invariant requirements in addition to state correspondence. Steps
preserve labels and event lists literally; stops are not mapped by this API. -/
structure Realizes (small : TransitionSystem Small Lab Event SmallStop)
    (full : TransitionSystem Full Lab Event FullStop) where
  relates : Small → Full → Prop
  pc : ∀ {s t}, relates s t → small.pc s = full.pc t
  step : ∀ {s t es s'}, relates s t → small.step s es s' →
    ∃ t', full.step t es t' ∧ relates s' t'

def Realizes.id (system : TransitionSystem Small Lab Event SmallStop) : Realizes system system where
  relates := Eq
  pc := congrArg system.pc
  step := fun | rfl, edge => ⟨_, edge, rfl⟩

def Realizes.comp {small : TransitionSystem Small Lab Event SmallStop}
    {full : TransitionSystem Full Lab Event FullStop} {larger : TransitionSystem Larger Lab Event LargerStop}
    (first : Realizes small full) (second : Realizes full larger) : Realizes small larger where
  relates s u := ∃ t, first.relates s t ∧ second.relates t u
  pc := fun ⟨_, left, right⟩ => (first.pc left).trans (second.pc right)
  step := fun ⟨_, left, right⟩ edge =>
    let ⟨_, middle, left'⟩ := first.step left edge
    let ⟨_, large, right'⟩ := second.step right middle
    ⟨_, large, _, left', right'⟩

/-- Normal boundary refinement from full to small, after projection by the
map: every full trace has a simple run with related endpoints. -/
def Realizes.RefinesExits {small : TransitionSystem Small Lab Event SmallStop}
    {full : TransitionSystem Full Lab Event FullStop} (map : Realizes small full)
    (admit : Small → Prop) (admitFull : Full → Prop) (support : Lab → Prop) : Prop :=
  ∀ initial es final, admitFull initial → FirstExit full support initial es final →
    ∃ s out, admit s ∧ map.relates s initial ∧ FirstExit small support s es out ∧ map.relates out final

/-- The conditions needed to convert one witnessed normal exit into a
universal finite execution result. Halt payloads are not identified with UB. -/
structure Determinate (system : TransitionSystem Full Lab Event FullStop) : Prop where
  step_unique : ∀ {s es fs t u}, system.step s es t → system.step s fs u → es = fs ∧ t = u
  step_no_halt : ∀ {s es t k}, system.step s es t → ¬ system.halt s k

/-- All executions up to first exit are accounted for, including their trace.
This intentionally says nothing about executing code at the exit address. -/
structure ExitsNormally (system : TransitionSystem Full Lab Event FullStop)
    (support : Lab → Prop) (initial : Full) (trace : List Event) (final : Full) : Prop where
  witness : FirstExit system support initial trace final
  unique : ∀ es next, FirstExit system support initial es next → es = trace ∧ next = final
  finishes : Finishes system support initial
  noHalt : ∀ es mid, Inside system support initial es mid → ∀ stop, ¬ system.halt mid stop

end Silmaril.Semantics.Region
