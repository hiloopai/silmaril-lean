module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Proofs.Wasm.Component.Reference.MachineReturnOccurrence

public section

namespace Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)}

/-- Segment storage projects each real machine transition, including a
switch to the very activation just saved. -/
theorem step_edit {before after : Config E Host} {label : Label E Host}
    (run : Step profile ready dispatch before label after) :
    segmentStorage after = (transitionEdit before label).apply (segmentStorage before) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.step_edit run

theorem step_follow {before after : Config E Host} {label : Label E Host} {place reached : Location}
    (run : Step profile ready dispatch before label after) (moved : (transitionEdit before label).follow place = some reached) :
    segmentAt (segmentStorage after) reached = segmentAt (segmentStorage before) place :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.step_follow run moved

/-- A same-slot edit preserves the entire blocked activation, not just its
Core return segment. This also preserves the exact suspended program. -/
theorem step_saved {before after : Config E Host} {label : Label E Host} {thread : ThreadId}
    (run : Step profile ready dispatch before label after)
    (kept : (transitionEdit before label).follow (.saved thread.idx 0) = some (.saved thread.idx 0)) :
    after.cont? thread = before.cont? thread :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.step_saved run kept

theorem ParkedPrefix.reaches {before after : Config E Host} {labels : List (Label E Host)} {thread : ThreadId}
    (prefixRun : ParkedPrefix profile ready dispatch thread before labels after) :
    Steps profile ready dispatch before labels after ∧ after.cont? thread = before.cont? thread :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.parkedPrefix_reaches prefixRun

theorem step_pop {before after : Config E Host} {label : Label E Host} {place : Location} {resume : Continuation E Host}
    (run : Step profile ready dispatch before label after)
    (occurs : segmentAt (segmentStorage before) place = some (.prog resume))
    (pops : (transitionEdit before label).pops place) : Popped before after label place resume :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.step_pop run occurs pops

/-- Both scheduler cursors use the same edit when their reached focus and
scheduler data are paired. It does not read the substituted frames. -/
theorem pair_edit {changes : Substitutions E Host} {left right : Config E Host}
    (paired : Related.Paired changes left right) (label : Label E Host) :
    transitionEdit left label = transitionEdit right label :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.pair_edit paired label

theorem paired_outside {changes : Substitutions E Host} {left right : Config E Host}
    (paired : Related.Paired changes left right) : Outside changes (segmentStorage left) (segmentStorage right) none :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.paired_outside paired

theorem outside_push {older : Substitutions E Host} {left right : Stacks E Host} (first second : Seg E Host)
    (paired : Outside older left right none) :
    Outside older ((Edit.push first).apply left) ((Edit.push second).apply right) (some (.active 0 0)) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.outside_push first second paired

/-- Pairing by the older relation is preserved off the mark. Newly written
or empty locations cannot inherit the selected substitution. -/
theorem outside_edit {older : Substitutions E Host} {left right : Stacks E Host} {mark : Option Location}
    (outside : Outside older left right mark) (edit : Edit E Host) :
    Outside older (edit.apply left) (edit.apply right) (mark.bind edit.follow) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.outside_edit outside edit

theorem narrow {older wider : Substitutions E Host} {left right : Config E Host}
    (paired : Related.Paired wider left right)
    (outside : Outside older (segmentStorage left) (segmentStorage right) none) : Related.Paired older left right :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.narrow paired outside

/-- After popping the selected top occurrence, all remaining frames pair by
the older relation, including suspended activations. The common focus here
only exposes that residual relation; it does not execute either continuation. -/
theorem retire_top {older wider : Substitutions E Host} {left right : Config E Host}
    {thread : Option ThreadId} {value : Ret E} {first second : Continuation E Host}
    {leftFrames rightFrames : List (Seg E Host)} {leftRest rightRest : List (Activation E Host)}
    (paired : Related.Paired wider left right)
    (outside : Outside older (segmentStorage left) (segmentStorage right) (some (.active 0 0)))
    (leftAt : left.ctl = ⟨thread, .prog (.pure value), .prog first :: leftFrames⟩ :: leftRest)
    (rightAt : right.ctl = ⟨thread, .prog (.pure value), .prog second :: rightFrames⟩ :: rightRest)
    (focus : Focus E Host) :
    Related.Paired older { left with ctl := ⟨thread, focus, leftFrames⟩ :: leftRest }
      { right with ctl := ⟨thread, focus, rightFrames⟩ :: rightRest } :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.retire_top paired outside leftAt rightAt focus

/-- Following a surviving occurrence preserves the segment, not just its
lookup key or its position in the original activation. -/
theorem prefix_survives {before after : Config E Host} {labels : List (Label E Host)} {place reached : Location}
    (run : Prefix profile ready dispatch before place labels after reached) :
    Steps profile ready dispatch before labels after ∧
      segmentAt (segmentStorage after) reached = segmentAt (segmentStorage before) place :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.prefix_survives run

theorem Prefix.append {before middle after : Config E Host} {leading trailing : List (Label E Host)}
    {place reached final : Location} (left : Prefix profile ready dispatch before place leading middle reached)
    (right : Prefix profile ready dispatch middle reached trailing after final) :
    Prefix profile ready dispatch before place (leading ++ trailing) after final :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.prefix_append left right

/-- A store read changes the focused program but does not edit any segment slot. -/
theorem Prefix.read {before : Config E Host} {thread frames rest}
    {next : CStore E → P E Host (Ret E)} (depth : Nat)
    (focused : before.ctl = ⟨thread, .prog (.op (S := Eff E Host) .get next), frames⟩ :: rest) :
    Prefix profile ready dispatch before (.active 0 depth) [.tau]
      { before with ctl := ⟨thread, .prog (next before.store), frames⟩ :: rest } (.active 0 depth) :=
  .step (.get focused) (by rw [transitionEdit, focused]; rfl) (.done _ _)

/-- Pop the actual return frame, keeping every slot below it. -/
theorem Prefix.pop_return {before : Config E Host} {thread frames rest value} {resume : Continuation E Host}
    (returning : before.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest) :
    RetainsBelowTop profile ready dispatch before [.tau]
      { before with ctl := ⟨thread, .prog (resume value), frames⟩ :: rest } :=
  fun _ => .step (.popProg returning) (by rw [transitionEdit, returning]; rfl) (.done _ _)

/-- While the marked frame survives, older slots in its activation move with it,
including through suspension, resume, and switches. This does not show that
the marked callback returns. -/
theorem Prefix.under {before after : Config E Host} {labels : List (Label E Host)} {place reached : Location}
    (run : Prefix profile ready dispatch before place labels after reached) (depth : Nat) :
    Prefix profile ready dispatch before (place.below depth) labels after (reached.below depth) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.prefix_below run depth

/-- Installing a call and popping its actual marked return preserves every older
slot. At depth zero this carries the original parked Core caller across a
returning allocator without confusing it with the allocator's own frame. -/
theorem Prefix.under_call {before entered middle after : Config E Host} {labels : List (Label E Host)}
    {thread frames rest call} {resume : Continuation E Host}
    (focused : before.ctl = ⟨thread, .prog (.op (S := Eff E Host) (.call call) resume), frames⟩ :: rest)
    (install : Step profile ready dispatch before .tau entered)
    (run : Prefix profile ready dispatch entered (.active 0 0) labels middle (.active 0 0))
    (step : Step profile ready dispatch middle .tau after)
    (pops : (transitionEdit middle .tau).pops (.active 0 0)) (depth : Nat) :
    Prefix profile ready dispatch before (.active 0 depth) (.tau :: labels ++ [.tau]) after (.active 0 depth) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.prefix_under_call focused install run step pops depth

theorem Prefix.toTrail {before after : Config E Host} {labels : List (Label E Host)} {place reached : Location}
    (run : Prefix profile ready dispatch before place labels after reached) :
    Trail profile ready dispatch before (some place) labels after (some reached) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.prefixTrail run

theorem Trail.append {before middle after : Config E Host} {leading trailing : List (Label E Host)}
    {mark reached final : Option Location} (left : Trail profile ready dispatch before mark leading middle reached)
    (right : Trail profile ready dispatch middle reached trailing after final) :
    Trail profile ready dispatch before mark (leading ++ trailing) after final :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.trailAppend left right

theorem Trail.survives {before after : Config E Host} {labels : List (Label E Host)}
    {mark : Option Location} {reached : Location}
    (run : Trail profile ready dispatch before mark labels after (some reached)) :
    ∃ place, mark = some place ∧ Prefix profile ready dispatch before place labels after reached :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.trailSurvives run

/-- Join an installation prefix (which can include pre-call reads) to the
observed return of the marked frame. The older slot regains its prior depth. -/
theorem Trail.through_return {start entered reached : Config E Host} {leading labels : List (Label E Host)}
    {thread frames rest value} {resume : Continuation E Host} {depth : Nat}
    (install : Prefix profile ready dispatch start (.active 0 depth) leading entered (.active 0 (depth + 1)))
    (marked : Trail profile ready dispatch entered (some (.active 0 0)) labels reached (some (.active 0 0)))
    (returning : reached.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest) :
    Prefix profile ready dispatch start (.active 0 depth) (leading ++ (labels ++ [.tau]))
      { reached with ctl := ⟨thread, .prog (resume value), frames⟩ :: rest } (.active 0 depth) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.trail_through_return install marked returning

/-- Continue through a local return suffix built from the same reached marked
frame. This also covers checks after the pop, before entering a sibling. -/
theorem Trail.through_return_suffix {start entered reached after : Config E Host}
    {leading labels trailing : List (Label E Host)}
    (install : ∀ depth, Prefix profile ready dispatch start (.active 0 depth) leading entered (.active 0 (depth + 1)))
    (marked : Trail profile ready dispatch entered (some (.active 0 0)) labels reached (some (.active 0 0)))
    (suffix : RetainsBelowTop profile ready dispatch reached trailing after) :
    RetainsActiveSlots profile ready dispatch start (leading ++ (labels ++ trailing)) after := by
  obtain ⟨place, same, tracked⟩ := marked.survives
  cases same
  intro depth
  have older : Prefix profile ready dispatch entered (.active 0 (depth + 1)) labels reached (.active 0 (depth + 1)) := by
    simpa only [Location.below, Nat.zero_add] using tracked.under (depth + 1)
  exact (install depth).append (older.append (suffix depth))

theorem Trail.absent {before after : Config E Host} {labels : List (Label E Host)} (run : Steps profile ready dispatch before labels after) :
    Trail profile ready dispatch before none labels after none :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.absentTrail run

/-- An absent final mark identifies a real first loss in the same tracked
run. Only a loss by popping the selected slot enters its continuation. -/
theorem Trail.first_loss {before after : Config E Host} {labels : List (Label E Host)}
    {place : Location} {resume : Continuation E Host}
    (run : Trail profile ready dispatch before (some place) labels after none)
    (occurs : segmentAt (segmentStorage before) place = some (.prog resume)) :
    ∃ leading label trailing atLoss next reached,
      labels = leading ++ label :: trailing ∧
      Prefix profile ready dispatch before place leading atLoss reached ∧
      Step profile ready dispatch atLoss label next ∧ Trail profile ready dispatch next none trailing after none ∧
      (transitionEdit atLoss label).follow reached = none ∧
      (Popped atLoss next label reached resume ∨ ¬ (transitionEdit atLoss label).pops reached) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.trailLoss run place rfl rfl occurs

/-- Every finite execution either retains the selected occurrence or has a
first removal. Only a pop of its actual top slot executes the continuation;
lockdown and overwrite do not turn a nonreturning prefix into a return. -/
theorem first_loss {before after : Config E Host} {labels : List (Label E Host)} {place : Location}
    {resume : Continuation E Host} (occurs : segmentAt (segmentStorage before) place = some (.prog resume))
    (run : Steps profile ready dispatch before labels after) :
    (∃ reached, Prefix profile ready dispatch before place labels after reached) ∨
    ∃ leading label trailing atLoss next reached,
      labels = leading ++ label :: trailing ∧
      Prefix profile ready dispatch before place leading atLoss reached ∧
      Step profile ready dispatch atLoss label next ∧ Steps profile ready dispatch next trailing after ∧
      (transitionEdit atLoss label).follow reached = none ∧
      (Popped atLoss next label reached resume ∨ ¬ (transitionEdit atLoss label).pops reached) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.first_loss occurs run

end Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
