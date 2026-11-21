module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Defs

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.ReturnFrame
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)} {first second : Continuation E Host}
variable {changes : Substitutions E Host}

local notation "SegmentOf" => Related.Segment
local notation "ActiveOf" => Related.Active
local notation "SavedOf" => Related.Saved
local notation "PairedOf" => Related.Paired
local notation "ReturnedOf" => Related.Returned

private theorem listSame {Item : Type} {relation : Item → Item → Prop}
    (same : ∀ item, relation item item) (items : List Item) : List.Forall₂ relation items items := by
  induction items with
  | nil => exact .nil
  | cons item _ tail => exact .cons (same item) tail

private theorem activeSame (act : Activation E Host) : ActiveOf changes act act :=
  .mk (listSame Related.Segment.same act.segs)

private theorem savedSame (slot : Option (Activation E Host)) : SavedOf changes slot slot := by
  cases slot with
  | none => exact .none
  | some act => exact .some (activeSame act)

theorem installed (cfg : Config E Host) (thread : Option ThreadId) (body : P E Host (Ret E))
    (frames : List (Seg E Host)) (rest : List (Activation E Host)) :
    Paired first second { cfg with ctl := ⟨thread, .prog body, .prog first :: frames⟩ :: rest }
      { cfg with ctl := ⟨thread, .prog body, .prog second :: frames⟩ :: rest } :=
  .mk (.cons (.mk (.cons (.swap .here) (listSame Related.Segment.same frames))) (listSame activeSame rest))
    (listSame savedSame cfg.conts)

private theorem setSlot_pair {Item : Type} {relation : Option Item → Option Item → Prop}
    {left right : List (Option Item)} (same : relation none none) (index : Nat) {lhs rhs : Option Item}
    (slots : List.Forall₂ relation left right) (inserted : relation lhs rhs) :
    List.Forall₂ relation (Config.setSlot left index lhs) (Config.setSlot right index rhs) := by
  induction index generalizing left right with
  | zero => cases slots with
    | nil => exact .cons inserted .nil
    | cons _ tail => exact .cons inserted tail
  | succ _ ih =>
    cases slots with
    | nil => exact .cons same (ih .nil)
    | cons head tail => exact .cons head (ih tail)

private theorem getSlot_pair {left right : List (Option (Activation E Host))}
    (slots : List.Forall₂ (SavedOf changes) left right) (index : Nat) :
    SavedOf changes (left[index]?.join) (right[index]?.join) := by
  induction index generalizing left right with
  | zero => cases slots with
    | nil => exact .none
    | cons head _ => exact head
  | succ _ ih => cases slots with
    | nil => exact .none
    | cons _ tail => exact ih tail

private theorem savedNone {right : Option (Activation E Host)}
    (paired : SavedOf changes none right) : right = none := by cases paired; rfl

private theorem savedSome {left : Activation E Host} {right : Option (Activation E Host)}
    (paired : SavedOf changes (some left) right) : ∃ act, right = some act ∧ ActiveOf changes left act := by
  cases paired with
  | some act => exact ⟨_, rfl, act⟩

private theorem blockedPair (thread : ThreadId) (cont : Unit → P E Host (Ret E)) {left right}
    (frames : List.Forall₂ (SegmentOf changes) left right) :
    SavedOf changes (some (blockedAct thread cont left)) (some (blockedAct thread cont right)) :=
  .some (.mk frames)

private theorem activeHead {cfg : Config E Host} {active thread focus frames rest}
    (control : List.Forall₂ (ActiveOf changes) cfg.ctl active)
    (focused : cfg.ctl = ⟨thread, focus, frames⟩ :: rest) :
    ∃ frames' rest', active = ⟨thread, focus, frames'⟩ :: rest' ∧
      List.Forall₂ (SegmentOf changes) frames frames' ∧ List.Forall₂ (ActiveOf changes) rest rest' := by
  rw [focused] at control
  cases control with
  | cons head tail => cases head with
    | mk frame => exact ⟨_, _, rfl, frame, tail⟩

theorem retarget {left right : Config E Host} (paired : PairedOf changes left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (next : Focus E Host) (host : Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      PairedOf changes { left with host, ctl := ⟨thread, next, frames⟩ :: rest }
        { right with host, ctl := ⟨thread, next, otherFrames⟩ :: otherRest } := by
  cases paired with
  | mk control blocked =>
    obtain ⟨_, _, atRight, head, tail⟩ := activeHead control focused
    exact ⟨_, _, atRight, .mk (.cons (.mk head) tail) blocked⟩

theorem pushShared {left right : Config E Host} (paired : PairedOf changes left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (next : Focus E Host) (frame : Seg E Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      PairedOf changes { left with ctl := ⟨thread, next, frame :: frames⟩ :: rest }
        { right with ctl := ⟨thread, next, frame :: otherFrames⟩ :: otherRest } := by
  cases paired with
  | mk control blocked =>
    obtain ⟨_, _, atRight, head, tail⟩ := activeHead control focused
    exact ⟨_, _, atRight, .mk (.cons (.mk (.cons (.same frame) head)) tail) blocked⟩

theorem retargetCoreFrame {left right : Config E Host} (paired : PairedOf changes left right)
    {thread focus core coreNext frames rest}
    (focused : left.ctl = ⟨thread, focus, .core core coreNext :: frames⟩ :: rest)
    (next : Focus E Host) (host : Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, .core core coreNext :: otherFrames⟩ :: otherRest ∧
      PairedOf changes { left with host, ctl := ⟨thread, next, frames⟩ :: rest }
        { right with host, ctl := ⟨thread, next, otherFrames⟩ :: otherRest } := by
  cases paired with
  | mk control blocked =>
    obtain ⟨_, _, atRight, head, tail⟩ := activeHead control focused
    cases head with
    | cons shared older =>
      cases shared
      exact ⟨_, _, atRight, .mk (.cons (.mk older) tail) blocked⟩

theorem parkCore {left right : Config E Host} (paired : PairedOf changes left right)
    {thread core coreNext frames rest} (focused : left.ctl = ⟨some thread, .core core coreNext, frames⟩ :: rest)
    (saved : Focus E Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨some thread, .core core coreNext, otherFrames⟩ :: otherRest ∧
      PairedOf changes
        { (left.setCont thread (some ⟨some thread, saved, .core core coreNext :: frames⟩)) with ctl := rest }
        { (right.setCont thread (some ⟨some thread, saved, .core core coreNext :: otherFrames⟩)) with ctl := otherRest } := by
  cases paired with
  | mk control blocked =>
    obtain ⟨_, _, atRight, head, tail⟩ := activeHead control focused
    exact ⟨_, _, atRight, .mk tail (setSlot_pair .none thread.idx blocked (.some (.mk (.cons (.same _) head))))⟩

theorem resumeCore {left right : Config E Host} (paired : PairedOf changes left right)
    {thread focus frames rest target saved core coreNext savedFrames}
    (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (found : left.cont? target = some ⟨some target, saved, .core core coreNext :: savedFrames⟩)
    (ongoing resumed : Focus E Host) :
    ∃ otherFrames otherRest otherSaved, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      right.cont? target = some ⟨some target, saved, .core core coreNext :: otherSaved⟩ ∧
      PairedOf changes
        { (left.setCont target none) with ctl :=
          ⟨some target, resumed, .core core coreNext :: savedFrames⟩ :: ⟨thread, ongoing, frames⟩ :: rest }
        { (right.setCont target none) with ctl :=
          ⟨some target, resumed, .core core coreNext :: otherSaved⟩ :: ⟨thread, ongoing, otherFrames⟩ :: otherRest } := by
  cases paired with
  | mk control blocked =>
    obtain ⟨_, _, atRight, head, tail⟩ := activeHead control focused
    have slots := getSlot_pair blocked target.idx
    simp only [Config.cont?] at found
    rw [found] at slots
    obtain ⟨_, atSaved, savedPair⟩ := savedSome slots
    cases savedPair with
    | mk savedPair =>
      cases savedPair with
      | cons shared older =>
        cases shared
        exact ⟨_, _, _, atRight, atSaved,
          .mk (.cons (.mk (.cons (.same _) older)) (.cons (.mk head) tail)) (setSlot_pair .none target.idx blocked .none)⟩

theorem weaken {wider : Substitutions E Host} {left right : Config E Host}
    (included : ∀ {first second}, changes first second → wider first second)
    (paired : PairedOf changes left right) : PairedOf wider left right := by
  have active {left right} (frame : ActiveOf changes left right) : ActiveOf wider left right := by
    cases frame with
    | mk segments =>
      refine .mk (List.Forall₂.imp ?_ segments)
      intro _ _ segment
      cases segment with
      | same _ => exact .same _
      | swap edge => exact .swap (included edge)
  cases paired with
  | mk control blocked =>
    refine .mk (List.Forall₂.imp (fun _ _ frame => active frame) control) (List.Forall₂.imp ?_ blocked)
    intro _ _ slot
    cases slot with
    | none => exact .none
    | some frame => exact .some (active frame)

theorem push {left right : Config E Host} (paired : PairedOf changes left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (body : P E Host (Ret E)) (first second : Continuation E Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      PairedOf (Extend changes first second)
        { left with ctl := ⟨thread, .prog body, .prog first :: frames⟩ :: rest }
        { right with ctl := ⟨thread, .prog body, .prog second :: otherFrames⟩ :: otherRest } := by
  have expanded := weaken (fun edge => Extend.existing (first := first) (second := second) edge) paired
  cases expanded with
  | mk control blocked =>
    obtain ⟨_, _, atRight, head, tail⟩ := activeHead control focused
    exact ⟨_, _, atRight, .mk (.cons (.mk (.cons (.swap .current) head)) tail) blocked⟩

private theorem finished {cfg : Config E Host} {active saved left right result}
    (blocked : List.Forall₂ (SavedOf changes) cfg.conts saved)
    (tail : List.Forall₂ (ActiveOf changes) left right) :
    PairedOf changes (hostFinish result left cfg)
      (hostFinish result right { cfg with ctl := active, conts := saved }) := by
  have calls : lastCall? { cfg with ctl := active, conts := saved } = lastCall? cfg := rfl
  cases tail with
  | nil =>
    cases result <;> cases found : lastCall? cfg <;>
      simp only [hostFinish, calls, found] <;> exact .mk .nil blocked
  | cons head tail =>
    simp only [hostFinish]
    exact .mk (.cons head tail) blocked

private theorem fault {cfg : Config E Host} {active saved reason}
    (control : List.Forall₂ (ActiveOf changes) cfg.ctl active)
    (blocked : List.Forall₂ (SavedOf changes) cfg.conts saved)
    (failed : Fault cfg reason) : Fault { cfg with ctl := active, conts := saved } reason := by
  cases failed with
  | blockNoThread focused =>
    obtain ⟨_, _, atRight, _, _⟩ := activeHead control focused
    exact .blockNoThread atRight
  | @switchMissing thread target cont _ _ focused missing =>
    obtain ⟨_, _, atRight, frames, _⟩ := activeHead control focused
    have slots := getSlot_pair (setSlot_pair .none thread.idx blocked (blockedPair thread cont frames)) target.idx
    simp only [Config.cont?, Config.setCont] at missing
    simp only [missing] at slots
    exact .switchMissing atRight (savedNone slots)
  | @resumeMissing _ thread _ _ _ focused missing =>
    obtain ⟨_, _, atRight, _, _⟩ := activeHead control focused
    have slots := getSlot_pair blocked thread.idx
    rw [Config.cont?] at missing
    rw [missing] at slots
    exact .resumeMissing atRight (savedNone slots)
  | calloutBadRet focused bad =>
    obtain ⟨_, _, atRight, frames, _⟩ := activeHead control focused
    cases frames with
    | cons head _ => cases head; exact .calloutBadRet atRight bad

private theorem hostReady {cfg : Config E Host} {active saved}
    (control : List.Forall₂ (ActiveOf changes) cfg.ctl active) (enabled : HostReadyCfg cfg) :
    HostReadyCfg { cfg with ctl := active, conts := saved } := by
  obtain ⟨empty, unlocked, nesting⟩ := enabled
  rw [empty] at control
  cases control
  exact ⟨rfl, unlocked, nesting⟩

theorem step {left right next : Config E Host} {label : Label E Host}
    (paired : PairedOf changes left right) (run : Step profile ready dispatch left label next) :
    (∃ next', Step profile ready dispatch right label next' ∧ PairedOf changes next next') ∨
    (∃ next', Step profile ready dispatch right label next' ∧ ReturnedOf changes left right label next next') := by
  cases paired with
  | mk control blocked =>
    cases run with
    | popProg focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      cases frames with
      | cons head frames => cases head with
        | same => exact .inl ⟨_, .popProg atRight, .mk (.cons (.mk frames) tail) blocked⟩
        | swap edge => exact .inr ⟨_, .popProg atRight, .mk edge focused atRight⟩
    | popCore focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      cases frames with
      | cons head frames => cases head; exact .inl ⟨_, .popCore atRight, .mk (.cons (.mk frames) tail) blocked⟩
    | threadExit focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      cases frames
      exact .inl ⟨_, .threadExit atRight, .mk tail blocked⟩
    | hostDone focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      cases frames
      exact .inl ⟨_, .hostDone atRight, finished blocked tail⟩
    | call focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .call atRight, .mk (.cons (.mk (.cons (.same _) frames)) tail) blocked⟩
    | callCore focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .callCore atRight, .mk (.cons (.mk frames) tail) blocked⟩
    | coreInternal focused status inner =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .coreInternal atRight status inner, .mk (.cons (.mk frames) tail) blocked⟩
    | coreReturned focused status =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .coreReturned atRight status, .mk (.cons (.mk frames) tail) blocked⟩
    | coreTrap focused status =>
      obtain ⟨_, _, atRight, _, _⟩ := activeHead control focused
      exact .inl ⟨_, .coreTrap atRight status, .mk .nil blocked⟩
    | coreCallout focused status =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .coreCallout atRight status, .mk (.cons (.mk (.cons (.same _) frames)) tail) blocked⟩
    | get focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .get atRight, .mk (.cons (.mk frames) tail) blocked⟩
    | modify focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .modify atRight, .mk (.cons (.mk frames) tail) blocked⟩
    | trap focused =>
      obtain ⟨_, _, atRight, _, _⟩ := activeHead control focused
      exact .inl ⟨_, .trap atRight, .mk .nil blocked⟩
    | choose response focused allowed =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .choose response atRight allowed, .mk (.cons (.mk frames) tail) blocked⟩
    | currentThread focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .currentThread atRight, .mk (.cons (.mk frames) tail) blocked⟩
    | @newThread _ body _ _ _ _ thread focused allocated =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .newThread atRight allocated,
        .mk (.cons (.mk frames) tail) (setSlot_pair .none thread.idx blocked (savedSame (some (threadAct dispatch thread body))))⟩
    | @block thread cont _ _ focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .block atRight,
        .mk tail (setSlot_pair .none thread.idx blocked (.some (.mk (focus := .prog (cont ())) frames)))⟩
    | @blockSwitch thread target cont _ _ _ focused found =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      have slots := setSlot_pair .none thread.idx blocked (blockedPair thread cont frames)
      have slot := getSlot_pair slots target.idx
      simp only [Config.cont?, Config.setCont] at found
      simp only [found] at slot
      obtain ⟨_, found', savedAct⟩ := savedSome slot
      exact .inl ⟨_, .blockSwitch atRight found', .mk (.cons savedAct tail) (setSlot_pair .none target.idx slots .none)⟩
    | @resumeThread _ target _ _ _ _ focused found =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      have slot := getSlot_pair blocked target.idx
      rw [Config.cont?] at found
      rw [found] at slot
      obtain ⟨_, found', savedAct⟩ := savedSome slot
      exact .inl ⟨_, .resumeThread atRight found', .mk (.cons savedAct (.cons (.mk frames) tail))
        (setSlot_pair .none target.idx blocked .none)⟩
    | hostGet focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .hostGet atRight, .mk (.cons (.mk frames) tail) blocked⟩
    | hostSet focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      exact .inl ⟨_, .hostSet atRight, .mk (.cons (.mk frames) tail) blocked⟩
    | @emit _ obs _ _ _ focused =>
      obtain ⟨_, _, atRight, frames, tail⟩ := activeHead control focused
      refine .inl ⟨_, .emit atRight, ?_⟩
      cases obs <;> exact .mk (.cons (.mk frames) tail) blocked
    | fault failed => exact .inl ⟨_, .fault (fault control blocked failed), .mk .nil blocked⟩
    | hostInvoke enabled fresh => exact .inl ⟨_, .hostInvoke (hostReady control enabled) fresh, .mk (.cons (activeSame _) .nil) blocked⟩
    | hostTick enabled => exact .inl ⟨_, .hostTick (hostReady control enabled), .mk (.cons (activeSame _) .nil) blocked⟩
    | hostCancel enabled pending unresolved =>
      exact .inl
        ⟨_, .hostCancel (hostReady control enabled) pending unresolved, .mk (.cons (activeSame _) .nil) blocked⟩
    | hostRun enabled => exact .inl ⟨_, .hostRun (hostReady control enabled), .mk (.cons (activeSame _) .nil) blocked⟩

theorem steps {left right next : Config E Host} {labels : List (Label E Host)}
    (paired : PairedOf changes left right) (run : Steps profile ready dispatch left labels next) :
    (∃ next', Steps profile ready dispatch right labels next' ∧ PairedOf changes next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      Steps profile ready dispatch left leading atLeft ∧
      Steps profile ready dispatch right leading atRight ∧ PairedOf changes atLeft atRight ∧
      ReturnedOf changes atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      Steps profile ready dispatch afterLeft trailing next) := by
  induction run generalizing right with
  | refl => exact .inl ⟨_, .refl _, paired⟩
  | cons head tail ih =>
    rcases step paired head with ⟨_, pairedHead, pairedNext⟩ | ⟨_, pairedHead, boundary⟩
    · rcases ih pairedNext with ⟨_, pairedTail, final⟩ | ⟨leading, _, _, _, _, _, _, split, lhs, rhs, middle, cut, pop, pop', rest⟩
      · exact .inl ⟨_, .cons pairedHead pairedTail, final⟩
      · exact .inr ⟨_ :: leading, _, _, _, _, _, _, congrArg (List.cons _) split,
          .cons head lhs, .cons pairedHead rhs, middle, cut, pop, pop', rest⟩
    · exact .inr ⟨[], _, _, _, _, _, _, rfl, .refl _, .refl _, paired, boundary, head, pairedHead, tail⟩

end Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame
