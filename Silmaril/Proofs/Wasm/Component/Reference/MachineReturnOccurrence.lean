module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Machine.Config.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.MachineReturnOccurrence

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs
  Silmaril.Wasm.Component.Machine.ReturnFrame Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)}

private theorem map_setSlot {Item Mapped : Type} (project : Item → Mapped)
    (slots : List (Option Item)) (slot : Nat) (value : Option Item) :
    (Config.setSlot slots slot value).map (Option.map project) =
      Config.setSlot (slots.map (Option.map project)) slot (value.map project) := by
  induction slot generalizing slots with
  | zero => cases slots <;> rfl
  | succ _ ih => cases slots <;> simp [Config.setSlot, ih]

private theorem savedAt_eq {cfg : Config E Host} {thread : ThreadId} {activation : Activation E Host}
    (found : cfg.cont? thread = some activation) :
    ((segmentStorage cfg).saved[thread.idx]?.join.getD []) = activation.segs := by
  cases look : cfg.conts[thread.idx]? <;>
    simp [Config.cont?, look, Option.join] at found
  subst_vars
  simp [segmentStorage, look]

private theorem head_read {Item : Type} {storage : List (List Item)} {segment : Nat} :
    storage[0]?.bind (·[segment]?) = (storage.headD [])[segment]? := by
  cases storage <;> simp

private theorem saved_read {storage : Stacks E Host} {slot segment : Nat} :
    segmentAt storage (.saved slot segment) = (savedAt storage slot)[segment]? := by
  unfold segmentAt savedAt
  cases found : storage.saved[slot]?.join <;> simp [found]

private theorem read_block {storage : Stacks E Host} {slot : Nat} {place reached : Location}
    (moved : place.block slot = some reached) : segmentAt (storage.block slot) reached = segmentAt storage place := by
  cases place with
  | active activation segment =>
    cases activation with
    | zero =>
      simp [Location.block] at moved
      subst reached
      simp [segmentAt, Stacks.block, Config.getElem?_setSlot_self, front, head_read]
    | succ activation =>
      simp [Location.block] at moved
      subst reached
      cases storage.active <;> simp [segmentAt, Stacks.block, *]
  | saved current segment =>
    by_cases same : current = slot
    · simp [Location.block, same] at moved
    · simp [Location.block, same] at moved
      subst reached
      simp [segmentAt, Stacks.block, Config.getElem?_setSlot_ne _ _ _ _ same]

private theorem read_resume (storage : Stacks E Host) (slot : Nat) (place : Location) :
    segmentAt (storage.resume slot) (place.resume slot) = segmentAt storage place := by
  cases place with
  | active _ _ => rfl
  | saved current segment =>
    by_cases same : current = slot
    · subst current
      have here : (Location.saved slot segment).resume slot = .active 0 segment := by simp [Location.resume]
      rw [here]
      exact saved_read.symm
    · simp [Location.resume, Stacks.resume, segmentAt, same, Config.getElem?_setSlot_ne _ _ _ _ same]

private theorem source_block (storage : Stacks E Host) (slot : Nat) (place : Location) :
    segmentAt (storage.block slot) place = segmentAt storage (place.beforeBlock slot) := by
  apply read_block (place := place.beforeBlock slot)
  cases place with
  | active _ _ => rfl
  | saved current segment =>
    by_cases same : current = slot <;> simp [Location.beforeBlock, Location.block, same]

private theorem rejoin_resume (slot : Nat) (place prior : Location)
    (source : place.beforeResume slot = some prior) : prior.resume slot = place := by
  cases place with
  | active activation segment =>
    cases activation <;> simp [Location.beforeResume] at source <;> subst prior <;> simp [Location.resume]
  | saved current segment =>
    by_cases same : current = slot
    · simp [Location.beforeResume, same] at source
    · simp [Location.beforeResume, same] at source
      subst prior
      simp [Location.resume, same]

private theorem absent_resume {storage : Stacks E Host} {slot : Nat} {place : Location}
    (source : place.beforeResume slot = none) : segmentAt (storage.resume slot) place = none := by
  cases place with
  | active activation segment => cases activation <;> contradiction
  | saved current segment =>
    by_cases same : current = slot
    · subst current
      simp [segmentAt, Stacks.resume, Config.getElem?_setSlot_self]
    · simp [Location.beforeResume, same] at source

theorem read_source (storage : Stacks E Host) (edit : Edit E Host) (place : Location) :
    segmentAt (edit.apply storage) place = Source.segment storage (edit.source place) := by
  cases edit with
  | block slot => exact source_block _ _ _
  | resume slot =>
    cases source : place.beforeResume slot with
    | none => rw [Edit.source, source]; exact absent_resume source
    | some prior =>
      simpa only [Edit.source, Edit.apply, source, Option.elim, Source.segment, rejoin_resume _ _ _ source] using
        (read_resume storage slot prior)
  | switch fromSlot toSlot =>
    cases source : place.beforeResume toSlot with
    | none => rw [Edit.source, source]; exact absent_resume source
    | some prior =>
      simp only [Edit.source, Edit.apply, source, Option.elim, Source.segment]
      rw [← rejoin_resume _ _ _ source, read_resume, source_block]
  | same => cases place <;> rfl
  | clear | enter =>
    cases place with
    | active activation segment => cases activation <;> simp [Edit.source, Edit.apply, Source.segment, segmentAt]
    | saved _ _ => rfl
  | write slot frames =>
    cases place with
    | active _ _ => rfl
    | saved current segment =>
      by_cases same : current = slot
      · subst current
        simp [Edit.source, Edit.apply, Source.segment, segmentAt, Config.getElem?_setSlot_self]
      · simp [Edit.source, Edit.apply, Source.segment, segmentAt, same, Config.getElem?_setSlot_ne _ _ _ _ same]
  | exit =>
    cases place with
    | active _ _ => cases found : storage.active <;> simp [Edit.source, Edit.apply, Source.segment, segmentAt, found]
    | saved _ _ => rfl
  | push frame =>
    cases place with
    | active activation segment =>
      cases activation with
      | zero => cases segment <;> simp [Edit.source, Edit.apply, Source.segment, segmentAt, front, head_read]
      | succ _ => cases found : storage.active <;> simp [Edit.source, Edit.apply, Source.segment, segmentAt, found]
    | saved _ _ => rfl
  | pop =>
    cases place with
    | active activation segment =>
      cases activation with
      | zero =>
        change (front storage).tail[segment]? = storage.active[0]?.bind (·[segment + 1]?)
        rw [head_read]
        change (front storage).tail[segment]? = (front storage)[segment + 1]?
        cases front storage <;> simp
      | succ _ => cases found : storage.active <;> simp [Edit.source, Edit.apply, Source.segment, segmentAt, found]
    | saved _ _ => rfl

theorem follow_source {edit : Edit E Host} {place prior : Location} (source : edit.source place = .inl prior) :
    edit.follow prior = some place := by
  have block_inv (slot : Nat) (place : Location) : (place.beforeBlock slot).block slot = some place := by
    cases place with
    | active _ _ => rfl
    | saved current segment =>
      by_cases same : current = slot
      · subst current; simp [Location.beforeBlock, Location.block]
      · simp [Location.beforeBlock, Location.block, same]
  cases edit with
  | block slot => exact (congrArg (Location.block slot) (Sum.inl.inj source)).symm.trans (block_inv slot place)
  | resume slot =>
    cases came : place.beforeResume slot with
    | none => simp [Edit.source, came] at source
    | some earlier =>
      have same : earlier = prior := by simpa [Edit.source, came] using source
      subst earlier
      exact congrArg some (rejoin_resume _ _ _ came)
  | switch fromSlot toSlot =>
    cases came : place.beforeResume toSlot with
    | none => simp [Edit.source, came] at source
    | some earlier =>
      have same : earlier.beforeBlock fromSlot = prior := by simpa [Edit.source, came] using source
      subst prior
      simp [Edit.follow, block_inv, rejoin_resume _ _ _ came]
  | write slot frames =>
    cases place with
    | active _ _ => cases source; rfl
    | saved current segment =>
      by_cases same : current = slot
      · simp [Edit.source, same] at source
      · simp [Edit.source, same] at source
        subst prior
        simp [Edit.follow, same]
  | same | clear | enter | exit | push _ | pop =>
    cases place with
    | saved _ _ => cases source; rfl
    | active activation segment =>
      cases activation <;> cases segment <;> simp [Edit.source] at source <;> cases source <;> rfl

theorem outside_edit {older : Substitutions E Host} {left right : Stacks E Host} {mark : Option Location}
    (outside : Outside older left right mark) (edit : Edit E Host) :
    Outside older (edit.apply left) (edit.apply right) (mark.bind edit.follow) := by
  intro place offMark first second leftAt rightAt
  rw [read_source] at leftAt rightAt
  cases source : edit.source place with
  | inl prior =>
    rw [source] at leftAt rightAt
    apply outside prior _ first second leftAt rightAt
    intro marked
    rw [← marked, Option.bind_some, follow_source source] at offMark
    exact offMark rfl
  | inr fresh =>
    rw [source] at leftAt rightAt
    have same : first = second := Option.some.inj (leftAt.symm.trans rightAt)
    subst second
    exact .same first

private theorem pointwise {Item : Type} {before after : Item → Item → Prop} {left right : List Item}
    (paired : List.Forall₂ before left right) :
    (∀ (index : Nat) first second, left[index]? = some first → right[index]? = some second → after first second) ↔
      List.Forall₂ after left right := by
  induction paired with
  | nil => simp
  | @cons lhs rhs left right edge tail ih =>
    constructor
    · intro all
      exact .cons (all 0 lhs rhs rfl rfl) (ih.mp fun index first second lhs rhs => all (index + 1) first second lhs rhs)
    · intro mapped index first second hLeft hRight
      cases mapped with
      | cons head rest =>
        cases index with
        | zero =>
          simp at hLeft hRight
          subst first
          subst second
          exact head
        | succ index => exact ih.mpr rest index first second hLeft hRight

private theorem active_narrow {older wider : Substitutions E Host} {left right : Activation E Host}
    (paired : Related.Active wider left right)
    (all : ∀ (index : Nat) first second, left.segs[index]? = some first → right.segs[index]? = some second →
      Related.Segment older first second) : Related.Active older left right := by
  cases paired with
  | mk frames => exact .mk ((pointwise frames).mp all)

private theorem active_segment {changes : Substitutions E Host} {left right : Activation E Host}
    (paired : Related.Active changes left right) (index : Nat) {first second : Seg E Host}
    (leftAt : left.segs[index]? = some first) (rightAt : right.segs[index]? = some second) :
    Related.Segment changes first second := by
  cases paired with
  | mk frames => exact (pointwise frames).mpr frames index first second leftAt rightAt

theorem paired_outside {changes : Substitutions E Host} {left right : Config E Host}
    (paired : Related.Paired changes left right) : Outside changes (segmentStorage left) (segmentStorage right) none := by
  cases paired with
  | @mk active saved control blocked =>
    intro place _ first second leftAt rightAt
    cases place with
    | active activation segment =>
      cases foundLeft : left.ctl[activation]? with
      | none => simp [segmentAt, segmentStorage, foundLeft] at leftAt
      | some lhs =>
        cases foundRight : active[activation]? with
        | none => simp [segmentAt, segmentStorage, foundRight] at rightAt
        | some rhs =>
          exact active_segment ((pointwise control).mpr control activation lhs rhs foundLeft foundRight) segment
            (by simpa [segmentAt, segmentStorage, *] using leftAt) (by simpa [segmentAt, segmentStorage, *] using rightAt)
    | saved slot segment =>
      cases foundLeft : left.conts[slot]? with
      | none => simp [segmentAt, segmentStorage, foundLeft] at leftAt
      | some lhs =>
        cases foundRight : saved[slot]? with
        | none => simp [segmentAt, segmentStorage, foundRight] at rightAt
        | some rhs =>
          have pair := (pointwise blocked).mpr blocked slot lhs rhs foundLeft foundRight
          cases pair with
          | none => simp [segmentAt, segmentStorage, ‹left.conts[slot]? = some none›] at leftAt
          | some linked =>
            exact active_segment linked segment
              (by simpa [segmentAt, segmentStorage, *] using leftAt) (by simpa [segmentAt, segmentStorage, *] using rightAt)

theorem outside_push {older : Substitutions E Host} {left right : Stacks E Host} (first second : Seg E Host)
    (paired : Outside older left right none) :
    Outside older ((Edit.push first).apply left) ((Edit.push second).apply right) (some (.active 0 0)) := by
  intro place offMark lhs rhs leftAt rightAt
  have unmarked := outside_edit paired (.push first)
  apply unmarked place (by simp) lhs rhs leftAt
  rw [read_source] at rightAt ⊢
  cases place with
  | active activation segment =>
    cases activation <;> cases segment <;> first | exact rightAt | exact (offMark rfl).elim
  | saved _ _ => exact rightAt

theorem narrow {older wider : Substitutions E Host} {left right : Config E Host}
    (paired : Related.Paired wider left right)
    (outside : Outside older (segmentStorage left) (segmentStorage right) none) : Related.Paired older left right := by
  cases paired with
  | @mk active saved control blocked =>
    refine .mk ((pointwise control).mp ?_) ((pointwise blocked).mp ?_)
    · intro activation lhs rhs foundLeft foundRight
      apply active_narrow ((pointwise control).mpr control activation lhs rhs foundLeft foundRight)
      intro index first second leftAt rightAt
      apply outside (.active activation index) (by simp) first second
      · simp [segmentAt, segmentStorage, foundLeft, leftAt]
      · simp [segmentAt, segmentStorage, foundRight, rightAt]
    · intro slot lhs rhs foundLeft foundRight
      have pair := (pointwise blocked).mpr blocked slot lhs rhs foundLeft foundRight
      cases pair with
      | none => exact .none
      | some related =>
        apply Related.Saved.some (active_narrow related ?_)
        intro index first second leftAt rightAt
        apply outside (.saved slot index) (by simp) first second
        · simp [segmentAt, segmentStorage, foundLeft, leftAt]
        · simp [segmentAt, segmentStorage, foundRight, rightAt]

theorem pair_edit {changes : Substitutions E Host} {left right : Config E Host}
    (paired : Related.Paired changes left right) (label : Label E Host) :
    transitionEdit left label = transitionEdit right label := by
  cases paired with
  | mk control blocked =>
    cases label <;> try rfl
    unfold transitionEdit
    simp only []
    generalize left.ctl = acts at control ⊢
    cases control with
    | nil => rfl
    | cons head tail =>
      cases head with
      | @mk thread focus lhs rhs frames =>
        cases focus with
        | core _ _ => rfl
        | prog program =>
          cases program with
          | op _ _ => rfl
          | pure _ => cases frames <;> rfl

theorem retire_top {older wider : Substitutions E Host} {left right : Config E Host}
    {thread : Option ThreadId} {value : Ret E} {first second : Continuation E Host}
    {leftFrames rightFrames : List (Seg E Host)} {leftRest rightRest : List (Activation E Host)}
    (paired : Related.Paired wider left right)
    (outside : Outside older (segmentStorage left) (segmentStorage right) (some (.active 0 0)))
    (leftAt : left.ctl = ⟨thread, .prog (.pure value), .prog first :: leftFrames⟩ :: leftRest)
    (rightAt : right.ctl = ⟨thread, .prog (.pure value), .prog second :: rightFrames⟩ :: rightRest)
    (focus : Focus E Host) :
    Related.Paired older { left with ctl := ⟨thread, focus, leftFrames⟩ :: leftRest }
      { right with ctl := ⟨thread, focus, rightFrames⟩ :: rightRest } := by
  have old := outside_edit outside .pop
  have leftStore : segmentStorage { left with ctl := ⟨thread, focus, leftFrames⟩ :: leftRest } =
      (Edit.pop : Edit E Host).apply (segmentStorage left) := by simp [segmentStorage, Edit.apply, leftAt, front]
  have rightStore : segmentStorage { right with ctl := ⟨thread, focus, rightFrames⟩ :: rightRest } =
      (Edit.pop : Edit E Host).apply (segmentStorage right) := by simp [segmentStorage, Edit.apply, rightAt, front]
  apply narrow (wider := wider)
  · cases paired with
    | @mk active saved control blocked =>
      change active = ⟨thread, .prog (.pure value), .prog second :: rightFrames⟩ :: rightRest at rightAt
      rw [leftAt, rightAt] at control
      cases control with
      | cons head tail => cases head with
        | mk frames => cases frames with
          | cons _ rest => exact .mk (.cons (.mk rest) tail) blocked
  · rw [leftStore, rightStore]
    exact old

theorem read_follow {storage : Stacks E Host} {edit : Edit E Host} {place reached : Location}
    (moved : edit.follow place = some reached) : segmentAt (edit.apply storage) reached = segmentAt storage place := by
  cases edit with
  | block slot => exact read_block moved
  | resume slot =>
    have same : place.resume slot = reached := Option.some.inj moved
    subst reached
    exact read_resume _ _ _
  | switch fromSlot toSlot =>
    cases blocked : place.block fromSlot with
    | none => simp [Edit.follow, blocked] at moved
    | some intermediate =>
      simp [Edit.follow, blocked] at moved
      subst reached
      exact (read_resume _ _ _).trans (read_block blocked)
  | same =>
    cases place <;> simp [Edit.follow] at moved <;> subst reached <;> rfl
  | write slot frames =>
    cases place with
    | active _ _ => simp [Edit.follow] at moved; subst reached; rfl
    | saved current segment =>
      by_cases same : current = slot
      · simp [Edit.follow, same] at moved
      · simp [Edit.follow, same] at moved
        subst reached
        simp [segmentAt, Edit.apply, Config.getElem?_setSlot_ne _ _ _ _ same]
  | clear | enter =>
    cases place <;> simp [Edit.follow] at moved
    subst reached
    rfl
  | exit =>
    cases place with
    | active activation segment =>
      cases activation <;> simp [Edit.follow] at moved
      subst reached
      cases storage.active <;> simp [segmentAt, Edit.apply, *]
    | saved _ _ => simp [Edit.follow] at moved; subst reached; rfl
  | push frame =>
    cases place with
    | active activation segment =>
      cases activation <;> simp [Edit.follow] at moved <;> subst reached
      · simp [Edit.apply, segmentAt, front, head_read]
      · cases storage.active <;> simp [segmentAt, Edit.apply, *]
    | saved _ _ => simp [Edit.follow] at moved; subst reached; rfl
  | pop =>
    cases place with
    | active activation segment =>
      cases activation with
      | zero =>
        cases segment with
        | zero => simp [Edit.follow] at moved
        | succ segment =>
          simp [Edit.follow] at moved
          subst reached
          change (front storage).tail[segment]? = storage.active[0]?.bind (·[segment + 1]?)
          rw [head_read]
          change (front storage).tail[segment]? = (front storage)[segment + 1]?
          cases front storage <;> simp
      | succ _ =>
        simp [Edit.follow] at moved
        subst reached
        cases storage.active <;> simp [segmentAt, Edit.apply, *]
    | saved _ _ => simp [Edit.follow] at moved; subst reached; rfl

theorem step_edit {before after : Config E Host} {label : Label E Host}
    (run : Step profile ready dispatch before label after) :
    segmentStorage after = (transitionEdit before label).apply (segmentStorage before) := by
  cases run with
  | popProg focused => simp [transitionEdit, segmentStorage, Edit.apply, focused, front]
  | popCore focused =>
    simp [transitionEdit, segmentStorage, Edit.apply, focused, front]
  | threadExit focused => simp [transitionEdit, segmentStorage, Edit.apply, focused]
  | @hostDone result rest focused =>
    (cases rest <;> cases result <;> simp [transitionEdit, segmentStorage, Edit.apply, focused, hostFinish]);
      split <;> simp [Config.setCancel]
  | call focused => simp [transitionEdit, segmentStorage, Edit.apply, front, focused]
  | coreCallout focused called => simp [transitionEdit, segmentStorage, Edit.apply, front, focused, called]
  | newThread focused allocated =>
    simp [transitionEdit, segmentStorage, Edit.apply, focused, allocated, Config.setCont, map_setSlot,
      threadAct, Activation.ofProg]
  | block focused =>
    simp [transitionEdit, segmentStorage, Edit.apply, Stacks.block, front, focused, Config.setCont,
      map_setSlot, blockedAct]
  | resumeThread focused found =>
    simp only [transitionEdit, focused, Edit.apply, Stacks.resume, savedAt, savedAt_eq found]
    simp [segmentStorage, focused, Config.setCont, map_setSlot]
  | blockSwitch focused found =>
    have saved := savedAt_eq found
    simp only [segmentStorage, Config.setCont, map_setSlot, Option.map_some, blockedAct] at saved
    simp [transitionEdit, focused, Edit.apply, Stacks.resume, Stacks.block, savedAt, front, segmentStorage,
      Config.setCont, map_setSlot, blockedAct, saved]
  | trap _ | coreTrap _ _ | fault _ => rfl
  | hostInvoke _ _ | hostTick _ | hostCancel _ _ _ | hostRun _ => rfl
  | @emit _ obs _ _ _ focused =>
    cases obs <;> simp [transitionEdit, observe, Config.resolve, segmentStorage, Edit.apply, focused]
  | coreReturned focused done => simp [transitionEdit, done, segmentStorage, Edit.apply, focused]
  | callCore focused | coreInternal focused _ _ | get focused | modify focused
  | choose _ focused _ | currentThread focused | hostGet focused | hostSet focused =>
    simp [transitionEdit, segmentStorage, Edit.apply, focused]

theorem step_follow {before after : Config E Host} {label : Label E Host} {place reached : Location}
    (run : Step profile ready dispatch before label after) (moved : (transitionEdit before label).follow place = some reached) :
    segmentAt (segmentStorage after) reached = segmentAt (segmentStorage before) place := by
  rw [step_edit run]
  exact read_follow moved

theorem step_saved {before after : Config E Host} {label : Label E Host} {thread : ThreadId}
    (run : Step profile ready dispatch before label after)
    (kept : (transitionEdit before label).follow (.saved thread.idx 0) = some (.saved thread.idx 0)) :
    after.cont? thread = before.cont? thread := by
  cases run <;> try rfl
  case hostDone result rest focused =>
    (cases rest <;> cases result <;> simp [hostFinish, Config.cont?]); split <;> rfl
  case emit => simp only [Config.cont?, observe]; split <;> rfl
  case newThread focused allocated =>
    simp only [transitionEdit, focused, allocated, Edit.follow] at kept
    split at kept
    · contradiction
    · exact Config.getElem?_setSlot_ne _ _ _ _ (by assumption)
  case block focused =>
    simp only [transitionEdit, focused, Option.elim_some, Edit.follow, Location.block] at kept
    split at kept
    · contradiction
    · exact Config.getElem?_setSlot_ne _ _ _ _ (by assumption)
  case resumeThread focused found =>
    simp only [transitionEdit, focused, Edit.follow, Location.resume] at kept
    split at kept
    · cases kept
    · exact Config.getElem?_setSlot_ne _ _ _ _ (by assumption)
  case blockSwitch focused found =>
    simp only [transitionEdit, focused, Option.elim_some, Edit.follow, Location.block] at kept
    split at kept
    · contradiction
    · rename_i notBlocked
      simp only [Option.map_some, Location.resume] at kept
      split at kept
      · cases kept
      · rename_i notResumed
        exact (Config.getElem?_setSlot_ne _ _ _ _ notResumed).trans (Config.getElem?_setSlot_ne _ _ _ _ notBlocked)

theorem parkedPrefix_reaches {before after : Config E Host} {labels : List (Label E Host)} {thread : ThreadId}
    (prefixRun : ParkedPrefix profile ready dispatch thread before labels after) :
    Steps profile ready dispatch before labels after ∧ after.cont? thread = before.cont? thread := by
  induction prefixRun with
  | done => exact ⟨.refl _, rfl⟩
  | step run kept _ ih => exact ⟨.cons run ih.1, ih.2.trans (step_saved run kept)⟩

theorem step_pop {before after : Config E Host} {label : Label E Host} {place : Location} {resume : Continuation E Host}
    (run : Step profile ready dispatch before label after)
    (occurs : segmentAt (segmentStorage before) place = some (.prog resume))
    (pops : (transitionEdit before label).pops place) : Popped before after label place resume := by
  have here : place = .active 0 0 := by
    generalize transitionEdit before label = edit at pops
    cases edit <;> cases place <;> try contradiction
    rename_i activation segment
    cases activation <;> cases segment <;> simp_all [Edit.pops]
  subst place
  cases run with
  | @popProg thread value actual frames rest focused =>
    have same : actual = resume := by simpa [segmentAt, segmentStorage, focused] using occurs
    subst actual
    exact ⟨rfl, rfl, thread, value, frames, rest, focused, rfl⟩
  | popCore focused => simp [segmentAt, segmentStorage, focused] at occurs
  | coreReturned focused done => simp [transitionEdit, focused, done, Edit.pops] at pops
  | coreCallout focused called => simp [transitionEdit, focused, called, Edit.pops] at pops
  | threadExit focused | hostDone focused | call focused | callCore focused | get focused | modify focused
  | newThread focused _ | block focused | blockSwitch focused _ | resumeThread focused _
  | currentThread focused | hostGet focused | hostSet focused => simp [transitionEdit, focused, Edit.pops] at pops
  | choose _ _ _ | coreInternal _ _ _ | emit _ | trap _ | coreTrap _ _ | fault _
  | hostInvoke _ _ | hostTick _ | hostCancel _ _ _ | hostRun _ => contradiction

theorem prefix_survives {before after : Config E Host} {labels : List (Label E Host)} {place reached : Location}
    (run : Prefix profile ready dispatch before place labels after reached) :
    Steps profile ready dispatch before labels after ∧
      segmentAt (segmentStorage after) reached = segmentAt (segmentStorage before) place := by
  induction run with
  | done => exact ⟨.refl _, rfl⟩
  | step head moved _ ih => exact ⟨.cons head ih.1, ih.2.trans (step_follow head moved)⟩

theorem prefix_append {before middle after : Config E Host} {leading trailing : List (Label E Host)}
    {place reached final : Location} (left : Prefix profile ready dispatch before place leading middle reached)
    (right : Prefix profile ready dispatch middle reached trailing after final) :
    Prefix profile ready dispatch before place (leading ++ trailing) after final := by
  induction left with
  | done => exact right
  | step first moved _ ih => exact .step first moved (ih right)

private theorem block_below (place : Location) (slot depth : Nat) :
    (place.below depth).block slot = (place.block slot).map (·.below depth) := by
  cases place with
  | active activation segment => cases activation <;> rfl
  | saved current segment => by_cases same : current = slot <;> simp [Location.below, Location.block, same]

private theorem resume_below (place : Location) (slot depth : Nat) :
    (place.below depth).resume slot = (place.resume slot).below depth := by
  cases place with
  | active => rfl
  | saved current segment => by_cases same : current = slot <;> simp [Location.below, Location.resume, same]

private theorem follow_below {edit : Edit E Host} {place reached : Location}
    (moved : edit.follow place = some reached) (depth : Nat) :
    edit.follow (place.below depth) = some (reached.below depth) := by
  cases edit with
  | block slot =>
    change place.block slot = some reached at moved
    simp only [Edit.follow, block_below, moved, Option.map_some]
  | resume slot => cases moved; exact congrArg some (resume_below place slot depth)
  | switch fromSlot toSlot =>
    change (place.block fromSlot).map (Location.resume toSlot) = some reached at moved
    change ((place.below depth).block fromSlot).map (Location.resume toSlot) = _
    rw [block_below]
    cases blocked : place.block fromSlot with
    | none => simp [blocked] at moved
    | some slot =>
      simp only [blocked, Option.map_some, Option.some.injEq] at moved
      subst reached
      simpa only [Option.map_some] using congrArg some (resume_below slot toSlot depth)
  | write slot _ =>
    cases place with
    | active => cases moved; rfl
    | saved current segment =>
      by_cases same : current = slot
      · simp [Edit.follow, same] at moved
      · simp [Edit.follow, same] at moved
        subst reached
        simp [Location.below, Edit.follow, same]
  | pop =>
    cases place with
    | saved => cases moved; rfl
    | active activation segment =>
      cases activation with
      | succ => cases moved; rfl
      | zero =>
        cases segment with
        | zero => contradiction
        | succ segment =>
          change some (.active 0 segment) = some reached at moved
          cases moved
          change (Edit.pop (E := E) (Host := Host)).follow (.active 0 (segment.succ + depth)) = _
          rw [Nat.succ_add]
          rfl
  | push frame =>
    cases place with
    | saved => cases moved; rfl
    | active activation segment =>
      cases activation with
      | succ => cases moved; rfl
      | zero =>
        change some (.active 0 (segment + 1)) = some reached at moved
        cases moved
        change some (Location.active 0 (segment + depth + 1)) = some (Location.active 0 (segment + 1 + depth))
        rw [Nat.add_right_comm]
  | same | clear | enter | exit =>
    cases place with
    | saved => cases moved; rfl
    | active activation segment =>
      cases activation <;> cases moved <;> rfl

theorem prefix_below {before after : Config E Host} {labels : List (Label E Host)} {place reached : Location}
    (run : Prefix profile ready dispatch before place labels after reached) (depth : Nat) :
    Prefix profile ready dispatch before (place.below depth) labels after (reached.below depth) := by
  induction run with
  | done => exact .done _ _
  | step step moved _ ih => exact .step step (follow_below moved depth) ih

theorem prefix_pop_above {before middle after : Config E Host} {labels : List (Label E Host)} {place : Location}
    (run : Prefix profile ready dispatch before place labels middle (.active 0 0))
    (step : Step profile ready dispatch middle .tau after) (pops : (transitionEdit middle .tau).pops (.active 0 0))
    (depth : Nat) :
    Prefix profile ready dispatch before (place.below (depth + 1)) (labels ++ [.tau]) after (.active 0 depth) := by
  refine prefix_append (prefix_below run (depth + 1)) (.step step ?_ (.done _ _))
  cases edit : transitionEdit middle .tau <;> simp [edit, Edit.pops] at pops ⊢
  simp only [Location.below, Nat.zero_add]
  rfl

theorem prefix_under_call {before entered middle after : Config E Host} {labels : List (Label E Host)}
    {thread frames rest call} {resume : Continuation E Host}
    (focused : before.ctl = ⟨thread, .prog (.op (S := Eff E Host) (.call call) resume), frames⟩ :: rest)
    (install : Step profile ready dispatch before .tau entered)
    (run : Prefix profile ready dispatch entered (.active 0 0) labels middle (.active 0 0))
    (step : Step profile ready dispatch middle .tau after)
    (pops : (transitionEdit middle .tau).pops (.active 0 0)) (depth : Nat) :
    Prefix profile ready dispatch before (.active 0 depth) (.tau :: labels ++ [.tau]) after (.active 0 depth) := by
  refine .step install ?_ (prefix_pop_above run step pops depth)
  simp only [transitionEdit, focused, Edit.follow, Location.below, Nat.zero_add]

theorem prefixTrail {before after : Config E Host} {labels : List (Label E Host)} {place reached : Location}
    (run : Prefix profile ready dispatch before place labels after reached) :
    Trail profile ready dispatch before (some place) labels after (some reached) := by
  induction run with
  | done => exact .done _ _
  | step run moved _ ih => exact .step run (by simpa only [Option.bind, moved] using ih)

theorem trailAppend {before middle after : Config E Host} {leading trailing : List (Label E Host)}
    {mark reached final : Option Location} (left : Trail profile ready dispatch before mark leading middle reached)
    (right : Trail profile ready dispatch middle reached trailing after final) :
    Trail profile ready dispatch before mark (leading ++ trailing) after final := by
  induction left with
  | done => exact right
  | step first _ ih => exact .step first (ih right)

theorem trailSurvives {before after : Config E Host} {labels : List (Label E Host)}
    {mark : Option Location} {reached : Location}
    (run : Trail profile ready dispatch before mark labels after (some reached)) :
    ∃ place, mark = some place ∧ Prefix profile ready dispatch before place labels after reached := by
  generalize found : some reached = final at run
  induction run with
  | done => cases found; exact ⟨reached, rfl, .done _ _⟩
  | @step before next after mark final label labels step _ ih =>
    obtain ⟨middle, moved, tail⟩ := ih found
    cases mark with
    | none => contradiction
    | some place => exact ⟨place, rfl, .step step moved tail⟩

theorem absentTrail {before after : Config E Host} {labels : List (Label E Host)} (run : Steps profile ready dispatch before labels after) :
    Trail profile ready dispatch before none labels after none := by
  induction run with
  | refl => exact .done _ _
  | cons head _ ih => exact .step head ih

theorem trail_through_return {start entered reached : Config E Host} {leading labels : List (Label E Host)}
    {thread frames rest value} {resume : Continuation E Host} {depth : Nat}
    (install : Prefix profile ready dispatch start (.active 0 depth) leading entered (.active 0 (depth + 1)))
    (marked : Trail profile ready dispatch entered (some (.active 0 0)) labels reached (some (.active 0 0)))
    (returning : reached.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest) :
    Prefix profile ready dispatch start (.active 0 depth) (leading ++ (labels ++ [.tau]))
      { reached with ctl := ⟨thread, .prog (resume value), frames⟩ :: rest } (.active 0 depth) := by
  obtain ⟨place, identical, run⟩ := trailSurvives marked
  cases identical
  have pops : (transitionEdit reached .tau).pops (.active 0 0) := by
    rw [transitionEdit, returning]
    trivial
  apply prefix_append install
  simpa only [Location.below, Nat.zero_add] using prefix_pop_above run (.popProg returning) pops depth

theorem trailLoss {before after : Config E Host} {labels : List (Label E Host)}
    {mark final : Option Location} {resume : Continuation E Host}
    (run : Trail profile ready dispatch before mark labels after final) (place : Location)
    (started : mark = some place) (lost : final = none)
    (occurs : segmentAt (segmentStorage before) place = some (.prog resume)) :
    ∃ leading label trailing atLoss next reached,
      labels = leading ++ label :: trailing ∧
      Prefix profile ready dispatch before place leading atLoss reached ∧
      Step profile ready dispatch atLoss label next ∧ Trail profile ready dispatch next none trailing after none ∧
      (transitionEdit atLoss label).follow reached = none ∧
      (Popped atLoss next label reached resume ∨ ¬ (transitionEdit atLoss label).pops reached) := by
  induction run generalizing place with
  | done => rw [started] at lost; contradiction
  | @step before next after mark final label labels step tail ih =>
    subst mark
    cases moved : (transitionEdit before label).follow place with
    | none =>
      refine ⟨[], label, labels, before, next, place, rfl, .done _ _, step, ?_, moved, ?_⟩
      · rwa [Option.bind, moved, lost] at tail
      by_cases popped : (transitionEdit before label).pops place
      · exact .inl (step_pop step occurs popped)
      · exact .inr popped
    | some middle =>
      obtain ⟨leading, loss, trailing, atLoss, afterLoss, reached, split, track, cut, remainder, removed, kind⟩ :=
        ih middle moved lost ((step_follow step moved).trans occurs)
      exact ⟨label :: leading, loss, trailing, atLoss, afterLoss, reached, congrArg (List.cons label) split,
        .step step moved track, cut, remainder, removed, kind⟩

theorem first_loss {before after : Config E Host} {labels : List (Label E Host)} {place : Location}
    {resume : Continuation E Host} (occurs : segmentAt (segmentStorage before) place = some (.prog resume))
    (run : Steps profile ready dispatch before labels after) :
    (∃ reached, Prefix profile ready dispatch before place labels after reached) ∨
    ∃ leading label trailing atLoss next reached,
      labels = leading ++ label :: trailing ∧
      Prefix profile ready dispatch before place leading atLoss reached ∧
      Step profile ready dispatch atLoss label next ∧ Steps profile ready dispatch next trailing after ∧
      (transitionEdit atLoss label).follow reached = none ∧
      (Popped atLoss next label reached resume ∨ ¬ (transitionEdit atLoss label).pops reached) := by
  induction run generalizing place with
  | refl => exact .inl ⟨place, .done _ _⟩
  | @cons start next after label labels step rest ih =>
    cases moved : (transitionEdit start label).follow place with
    | none =>
      refine .inr ⟨[], label, labels, start, next, place, rfl, .done _ _, step, rest, moved, ?_⟩
      by_cases popped : (transitionEdit start label).pops place
      · exact .inl (step_pop step occurs popped)
      · exact .inr popped
    | some reached =>
      rcases ih ((step_follow step moved).trans occurs) with ⟨reached, tail⟩ |
        ⟨leading, loss, trailing, atLoss, afterLoss, marked, split, trail, cut, remainder, removed, kind⟩
      · exact .inl ⟨reached, .step step moved tail⟩
      · exact .inr ⟨label :: leading, loss, trailing, atLoss, afterLoss, marked, congrArg (List.cons label) split,
          .step step moved trail, cut, remainder, removed, kind⟩

end Silmaril.Proofs.Wasm.Component.Reference.MachineReturnOccurrence
