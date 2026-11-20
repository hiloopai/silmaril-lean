module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Width.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {pointer : FlatValue}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem refineShape {stringLeaf fits : Field → Prop} (depth : Nat) (field : Field)
    (shape : AggregateShape stringLeaf depth field)
    (reached : ∀ leaf, Field.Descendant field leaf → stringLeaf leaf → fits leaf) : AggregateShape fits depth field := by
  induction depth generalizing field with
  | zero =>
    cases shape with
    | handle handle => exact .handle handle
    | string leaf => exact .string (reached field (.self field) leaf)
  | succ depth ih =>
    cases shape with
    | handle handle => exact .handle handle
    | string leaf => exact .string (reached field (.self field) leaf)
    | aggregate children =>
      refine .aggregate fun child member => ih child (children child member) ?_
      exact fun leaf path string => reached leaf (.aggregate member path) string

private theorem placementFits (destination : RecordDestination) (store : CStore (core3 grow)) (field : Field) (address : Nat)
    (placed : placement destination store (layout destination.width field.type) address = .ok ()) :
    ∃ bytes, (core3 grow).memSize? store.core destination.memory = some bytes ∧ SlotFits destination.width bytes field address := by
  let area := layout destination.width field.type
  have aligned : address % area.alignment.bytes = 0 := by
    by_contra invalid
    simp [placement, area, invalid] at placed
    change Except.error TrapReason.unalignedPointer = .ok () at placed
    contradiction
  cases sized : (core3 grow).memSize? store.core destination.memory with
  | none => simp [placement, area, aligned, sized] at placed
  | some bytes =>
    refine ⟨bytes, rfl, aligned, ?_⟩
    change address + area.size ≤ bytes
    by_contra invalid
    simp [placement, area, aligned, sized, Nat.lt_of_not_ge invalid] at placed

private theorem initialFrame {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (next : call.ReferenceNext)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    ChildFrameOver older call.checked (call.reference next) call.cursor call.cursor := by
  have segments : ∀ frames, List.Forall₂ (ReturnFrame.Related.Segment older) frames frames :=
    fun _ => List.forall₂_same.mpr fun frame _ => .same frame
  have active : ∀ act, ReturnFrame.Related.Active older act act := fun ⟨_, _, frames⟩ => .mk (segments frames)
  have saved : ∀ act, ReturnFrame.Related.Saved older act act
    | none => .none
    | some act => .some (active act)
  exact ⟨rfl, rfl, rfl, rfl, List.forall₂_same.mpr fun act _ => saved act, rfl,
    segments call.cursor.frames, List.forall₂_same.mpr fun act _ => active act⟩

theorem parked (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : ParkedShape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedBody call depth next profile ready bindings) := by
  apply call.parked_after_placement linked
  intro admitted placed
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ _ compiled
  change placement call.destination call.start.store (layout call.destination.width (sig.payload call.tag)) (flatNat pointer) = .ok () at placed
  rw [← matched.type_eq] at placed
  obtain ⟨bytes, sized, slot⟩ := placementFits call.destination call.start.store call.field (flatNat pointer) placed
  have fits : AggregateShape (StringField.Fits call.destination) depth call.field := by
    apply refineShape depth call.field shape
    intro leaf path leafShape
    obtain ⟨item, equal⟩ := leafShape
    rw [← equal] at path
    have checked := (call.destination.compiled_payload_descendant call.inst (sig.payload call.tag)
      call.payload (.memory (flatNat pointer)) (plan := plan) compiled admitted path).2
    exact ⟨item, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked⟩
  unfold ParkedBody
  have layoutMatch : call.field.LayoutMatches call.field.type := matched.type_eq.symm ▸ matched
  exact nested_rule call.destination call.inst depth call.field (flatNat pointer)
    (call.destination.check_width call.start.store linked.destination) sized realloc fits layoutMatch slot
    0 call.reply next call.checked (call.reference next) call.cursor call.cursor (initialFrame call next _)
    (Core3.Grows.refl _) rfl (call.reference_at linked next) _ (fun _ _ _ _ frame _ checked canonical => ⟨frame, checked, canonical⟩)

theorem parkedList {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (linked : call.Linked bindings)
    (element : TypeOf) (entries : List Field) (depth : Nat) (next : call.ReferenceNext)
    (compiledList : call.field = .dynamic (.list element) element entries)
    (shapes : ∀ item ∈ entries, ParkedShape depth item) {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedListBody call element entries depth next profile ready bindings) := by
  apply call.parked_after_admission linked
  intro admitted _ prepared
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ _ compiled
  have layoutMatch : call.field.LayoutMatches call.field.type := matched.type_eq.symm ▸ matched
  have matchingEntries : Field.EntriesMatch entries element := by
    rw [compiledList] at layoutMatch
    cases layoutMatch with
    | list children => exact children
  have fit (item : Field) (member : item ∈ entries) : AggregateShape (StringField.Fits call.destination) depth item := by
    apply refineShape depth item (shapes item member)
    intro leaf path leafShape
    obtain ⟨string, equal⟩ := leafShape
    rw [← equal] at path
    have descent : call.field.Descendant string.field := compiledList ▸ Field.Descendant.dynamic member path
    have checked := (call.destination.compiled_payload_descendant call.inst (sig.payload call.tag)
      call.payload route.output (plan := plan) compiled admitted descent).2
    exact ⟨string, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked⟩
  have width := call.destination.check_width call.start.store linked.destination
  have sizeExists : ((core3 grow).memSize? call.start.store.core call.destination.memory).isSome = true := by
    apply Core3.memAddrType?_isSome_iff.mp
    change ((core3 grow).memAddrType? call.start.store.core call.destination.memory).isSome = true
    rw [width]
    rfl
  obtain ⟨bytes, sized⟩ := Option.isSome_iff_exists.mp sizeExists
  have preparedEntries : Record.prepare call.checked.store call.checked.host.writer (Field.listObjects entries) = .ok () := by
    change Record.prepare call.start.store call.start.host.writer (Field.listObjects entries) = .ok ()
    simpa only [compiledList, Field.objects] using prepared
  have checkAt : call.checked.ctl = call.cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (call.destination.context call.inst) call.destination.width (.dynamic (.list element) element entries) 0 route.output >>= call.reply) := by
    conv_lhs => unfold PayloadRoot.Site.checked
    rw [compiledList]
    rfl
  have canonAt := call.reference_at linked next
  rw [compiledList] at canonAt
  have valueMode : CanonicalTree.EntryMode.forOutput call.destination.width (.list element) route.output = .value := by
    cases route <;> rfl
  unfold ParkedListBody
  exact value_entries_replay call.destination call.inst (.list element) element entries depth 0 route.output call.reply next valueMode
    matchingEntries realloc fit ((initialFrame call next _).collection_replay call.destination call.inst (.list element) element entries 0
      route.output call.reply next width sized preparedEntries checkAt canonAt)

private theorem fitListTree {stringLeaf fits : Field → Prop} (depth : Nat) (field : Field)
    (shape : ListTreeShape stringLeaf depth field)
    (reached : ∀ leaf, Field.Descendant field leaf → stringLeaf leaf → fits leaf) : ListTreeShape fits depth field := by
  induction depth generalizing field with
  | zero =>
    cases shape with
    | handle handle => exact .handle handle
    | string leaf => exact .string (reached field (.self field) leaf)
    | scalar payload nonString => exact .scalar payload nonString
  | succ depth ih =>
    cases shape with
    | handle handle => exact .handle handle
    | string leaf => exact .string (reached field (.self field) leaf)
    | scalar payload nonString => exact .scalar payload nonString
    | aggregate children =>
      exact .aggregate fun item member => ih item (children item member) fun leaf path => reached leaf (.aggregate member path)
    | list children =>
      exact .list fun item member => ih item (children item member) fun leaf path => reached leaf (.dynamic member path)
    | map records children =>
      refine .map records ?_
      intro entry member fields equal item inFields
      exact ih item (children entry member fields equal item inFields) fun leaf path =>
        reached leaf (.dynamic member (equal ▸ .aggregate inFields path))
    | sum child =>
      refine .sum ?_
      intro item equal
      subst equal
      exact ih item (child item rfl) fun leaf path => reached leaf (.sum path)
    | fixed children =>
      exact .fixed fun item member => ih item (children item member) fun leaf path => reached leaf (.fixed member path)

private theorem linkedAllocator {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route)
    (linked : call.Linked bindings) : Field.AllocatorFor call.destination.realloc call.field := by
  intro child path pointer
  obtain ⟨plan, compiled⟩ := linked.compiled
  have certificate := Record.preflightValue_layout _ _ _ _ _ _ compiled
  have rootPointer := path.containsPtr certificate pointer
  cases option : call.destination.realloc with
  | some addr => exact ⟨addr, rfl⟩
  | none =>
    have rejected : Lower.checkOptions (call.destination.context (grow := grow) call.inst)
        (sig.payload call.tag) route.output = .error .reallocRequired := by
      simp [Lower.checkOptions, RecordDestination.context, rootPointer, option, Option.isNone]
      rfl
    simp only [Record.preflightValue, compileValue, rejected, bind, Except.bind, Except.mapError] at compiled
    split at compiled <;> contradiction

theorem parkedListTree (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : ParkedListTreeShape depth call.field) :
    PayloadRoot.Cut call profile ready bindings (ParkedListTreeBody call depth next profile ready bindings) := by
  apply call.parked_after_placement linked
  intro admitted placed
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ _ compiled
  change placement call.destination call.start.store (layout call.destination.width (sig.payload call.tag)) (flatNat pointer) = .ok () at placed
  rw [← matched.type_eq] at placed
  obtain ⟨bytes, sized, slot⟩ := placementFits call.destination call.start.store call.field (flatNat pointer) placed
  have fits : ListTreeShape (StringField.Fits call.destination) depth call.field := by
    apply fitListTree depth call.field shape
    intro leaf path leafShape
    obtain ⟨item, equal⟩ := leafShape
    rw [← equal] at path
    have checked := (call.destination.compiled_payload_descendant call.inst (sig.payload call.tag)
      call.payload (.memory (flatNat pointer)) (plan := plan) compiled admitted path).2
    exact ⟨item, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked⟩
  unfold ParkedListTreeBody
  exact list_tree_rule call.destination call.inst depth call.field (flatNat pointer)
    (call.destination.check_width call.start.store linked.destination) sized (linkedAllocator call linked)
    fits (matched.type_eq.symm ▸ matched) slot
    0 call.reply next call.checked (call.reference next) call.cursor call.cursor (initialFrame call next _)
    (Core3.Grows.refl _) rfl (call.reference_at linked next) _ (fun _ _ _ _ frame _ checked canonical => ⟨frame, checked, canonical⟩)

theorem parkedRecursiveValue {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (linked : call.Linked bindings)
    (type element : TypeOf) (entries : List Field) (depth : Nat) (next : call.ReferenceNext)
    (compiledRoot : call.field = .dynamic type element entries)
    (mode : CanonicalTree.EntryMode.forOutput call.destination.width type route.output = .value)
    (shapes : ∀ item ∈ entries, ParkedListTreeShape depth item) {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedRecursiveValueBody call type element entries depth next profile ready bindings) := by
  apply call.parked_after_admission linked
  intro admitted _ prepared
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ _ compiled
  have layoutMatch : call.field.LayoutMatches call.field.type := matched.type_eq.symm ▸ matched
  have matchingEntries : Field.EntriesMatch entries element := by
    rw [compiledRoot] at layoutMatch
    cases layoutMatch with
    | list children => exact children
    | map children => exact children
  have fit (item : Field) (member : item ∈ entries) : ListTreeShape (StringField.Fits call.destination) depth item := by
    apply fitListTree depth item (shapes item member)
    intro leaf path leafShape
    obtain ⟨string, equal⟩ := leafShape
    rw [← equal] at path
    have descent : call.field.Descendant string.field := compiledRoot ▸ Field.Descendant.dynamic member path
    have checked := (call.destination.compiled_payload_descendant call.inst (sig.payload call.tag)
      call.payload route.output (plan := plan) compiled admitted descent).2
    exact ⟨string, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked⟩
  have width := call.destination.check_width call.start.store linked.destination
  have sizeExists : ((core3 grow).memSize? call.start.store.core call.destination.memory).isSome = true := by
    apply Core3.memAddrType?_isSome_iff.mp
    change ((core3 grow).memAddrType? call.start.store.core call.destination.memory).isSome = true
    rw [width]
    rfl
  obtain ⟨bytes, sized⟩ := Option.isSome_iff_exists.mp sizeExists
  have preparedEntries : Record.prepare call.checked.store call.checked.host.writer (Field.listObjects entries) = .ok () := by
    change Record.prepare call.start.store call.start.host.writer (Field.listObjects entries) = .ok ()
    simpa only [compiledRoot, Field.objects] using prepared
  have checkAt : call.checked.ctl = call.cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (call.destination.context call.inst) call.destination.width (.dynamic type element entries) 0 route.output >>= call.reply) := by
    conv_lhs => unfold PayloadRoot.Site.checked
    rw [compiledRoot]
    rfl
  have canonAt := call.reference_at linked next
  rw [compiledRoot] at canonAt
  unfold ParkedRecursiveValueBody
  refine recursive_value_replay call.destination call.inst type element entries 0 route.output _ call.reply next _ mode matchingEntries ?_ ?_
    ((initialFrame call next _).collection_replay call.destination call.inst type element entries 0
      route.output call.reply next width sized preparedEntries checkAt canonAt)
  · intro store bytes width sized item member address placement
    have layoutAt := entries_match_of_mem matchingEntries member
    exact list_tree_rule call.destination call.inst depth item address width sized (fun _ _ _ => ⟨_, realloc⟩) (fit item member)
      (layoutAt.type_eq.symm ▸ layoutAt) placement
  · exact fun _ _ _ _ _ frame _ checked canonical => ⟨frame, checked, canonical⟩

private theorem flatAllocatingRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId) (depth : Nat) (item : Field)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (allocator : Field.AllocatorFor destination.realloc item)
    (fit : FlatAllocatingLeaf (StringField.Fits destination) depth item)
    (matched : item.LayoutMatches item.type) :
    FlatFieldRule (flatAllocating profile ready bindings older destination inst depth) older origin destination inst item := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
  rcases fit with leaf | scalar | ⟨type, element, entries, rfl, children⟩
  · exact .inl (mixed_flat_rule destination inst item present (allocator item (.self item)) leaf
      index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends)
  · obtain ⟨type, payload, rfl, data⟩ := scalar
    have reachedWidth : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width :=
      growth.memAddrType present
    have width : ptrTypeIn left.store (destination.context inst) = destination.width := by
      simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, reachedWidth]
    obtain ⟨store, result, chk, ref, checkRun, canonRun, labels, status⟩ :=
      local_data_leaf_frame (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings))
        destination inst type data payload index .flat origin left right (frame.store ▸ growth) width rfl
        frame.store check canon frame.thread checkNext canonNext checkAt canonAt
    refine .inr (.inl ⟨⟨type, payload, rfl, data⟩, store, result, chk, ref, checkRun, canonRun, labels, ?_⟩)
    cases result with
    | error _ => exact status
    | ok words =>
      exact ⟨status.2.1, status.2.2,
        ends words _ _ _ _ ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
          status.1 rfl rfl⟩
  · have certs : Field.EntriesMatch entries element ∧ CanonicalTree.EntryMode.forOutput destination.width type .flat = .value := by
      cases matched with
      | list matching => exact ⟨matching, rfl⟩
      | map matching => exact ⟨matching, rfl⟩
    refine .inr (.inr ⟨type, element, entries, rfl, ?_⟩)
    cases prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) with
    | error issue =>
      exact dynamic_refused_before_allocation destination inst type element entries .flat index
        left right check canon checkNext canonNext frame.store issue prepared checkAt
    | ok result =>
      cases result
      obtain ⟨reachedBytes, reachedSize, _⟩ := growth.memSize sized
      refine recursive_value_replay destination inst type element entries index .flat _ checkNext canonNext finish certs.2 certs.1 ?_ ?_
        (frame.collection_replay destination inst type element entries index .flat checkNext canonNext
          (growth.memAddrType present) reachedSize prepared checkAt canonAt)
      · intro store bytes width sized entry member address placement
        have layoutAt := entries_match_of_mem certs.1 member
        exact list_tree_rule destination inst depth entry address width sized
          (fun leaf path => allocator leaf (.dynamic member path)) (children entry member)
          (layoutAt.type_eq.symm ▸ layoutAt) placement
      · exact fun _ _ _ _ _ frame grown checked canonical => ends _ _ _ _ _ frame (growth.trans grown) checked canonical

theorem parkedFlat {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (flatDepth entryDepth : Nat) (next : call.ReferenceNext) (shape : ParkedFlatShape flatDepth entryDepth call.field) :
    PayloadRoot.Cut call profile ready bindings (ParkedFlatBody call flatDepth entryDepth next profile ready bindings) := by
  apply call.parked_after_fit linked
  intro admitted
  obtain ⟨plan, compiled⟩ := linked.compiled
  have width := call.destination.check_width call.start.store linked.destination
  have sizeExists : ((core3 grow).memSize? call.start.store.core call.destination.memory).isSome = true := by
    apply Core3.memAddrType?_isSome_iff.mp
    change ((core3 grow).memAddrType? call.start.store.core call.destination.memory).isSome = true
    rw [width]
    rfl
  obtain ⟨bytes, sized⟩ := Option.isSome_iff_exists.mp sizeExists
  let leaf := fun item => FlatAllocatingLeaf (StringField.Fits call.destination) entryDepth item ∧
    item.LayoutMatches item.type ∧ Field.AllocatorFor call.destination.realloc item
  have fits : FlatNestedFits leaf flatDepth call.field := by
    apply flat_nested_refine flatDepth call.field shape
    intro item path leafShape
    have facts := call.destination.compiled_payload_descendant call.inst (sig.payload call.tag) call.payload .flat
      (plan := plan) compiled admitted path
    refine ⟨?_, facts.1, fun child descent => linkedAllocator call linked child (path.trans descent)⟩
    rcases leafShape with (handle | ⟨string, equal⟩) | scalar | ⟨type, element, entries, equal, children⟩
    · exact .inl (.inl handle)
    · exact .inl (.inr ⟨string, equal, by
        rw [← equal] at facts
        simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using facts.2⟩)
    · exact .inr (.inl scalar)
    · subst item
      refine .inr (.inr ⟨type, element, entries, rfl, ?_⟩)
      intro entry member
      apply fitListTree entryDepth entry (children entry member)
      intro descendant descent stringLeaf
      obtain ⟨string, equal⟩ := stringLeaf
      rw [← equal] at descent
      have checked := (Field.Descendant.dynamic member descent).fits facts.1 Quirks.none
        call.destination.encoding call.destination.width facts.2
      exact ⟨string, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked.2⟩
  unfold ParkedFlatBody
  exact nested_flat_rule call.destination call.inst leaf _
    (fun item fit => flatAllocatingRule call.destination call.inst entryDepth item width sized fit.2.2 fit.1 fit.2.1)
    flatDepth call.field fits
    (fun path => call.destination.compiled_payload_sum_tag call.inst (sig.payload call.tag) call.payload .flat compiled admitted path)
    0 call.reply next call.checked (call.reference next) call.cursor call.cursor (initialFrame call next _)
    (Core3.Grows.refl _) rfl (call.reference_at linked next) _ (fun _ _ _ _ _ frame _ checked canonical => ⟨frame, checked, canonical⟩)

private theorem primitiveShapes (primitive : WIT.Primitive) (payload : Payload (.prim primitive))
    (depth : Nat) : ParkedListTreeShape depth (.data (.prim primitive) payload) ∧
      FlatAllocatingLeaf (fun field => ∃ item : StringField, item.field = field) depth (.data (.prim primitive) payload) := by
  by_cases string : primitive = .string
  · subst primitive
    obtain ⟨value, typed⟩ := payload
    cases typed with
    | int kind _ => cases kind
    | string valid =>
      exact ⟨.string ⟨⟨_, valid⟩, rfl⟩, .inl (.inr ⟨⟨_, valid⟩, rfl⟩)⟩
  · exact ⟨.scalar payload (.primitive string), .inr (.inl ⟨_, payload, rfl, .primitive string⟩)⟩

private theorem compiledShapes (item : Field) (compiled : item.Emitted)
    (memoryDepth flatDepth : Nat) (memoryBound : sizeOf item ≤ memoryDepth) (flatBound : sizeOf item ≤ flatDepth) :
    ParkedListTreeShape memoryDepth item ∧ ParkedFlatShape flatDepth memoryDepth item := by
  induction measured : sizeOf item using Nat.strong_induction_on generalizing item memoryDepth flatDepth with
  | _ budget inductionHypothesis =>
  have recurse (child : Field) (smaller : sizeOf child < sizeOf item) (emitted : child.Emitted)
      (memoryDepth flatDepth : Nat)
      (memoryBound : sizeOf child ≤ memoryDepth) (flatBound : sizeOf child ≤ flatDepth) :
      ParkedListTreeShape memoryDepth child ∧ ParkedFlatShape flatDepth memoryDepth child :=
    inductionHypothesis _ (measured ▸ smaller) child emitted memoryDepth flatDepth memoryBound flatBound rfl
  have positive : 0 < sizeOf item := by cases item <;> simp only [Field.data.sizeOf_spec, Field.endpoint.sizeOf_spec,
    Field.context.sizeOf_spec, Field.owner.sizeOf_spec, Field.aggregate.sizeOf_spec, Field.fixed.sizeOf_spec,
    Field.dynamic.sizeOf_spec, Field.sum.sizeOf_spec] <;> omega
  cases memoryDepth with
  | zero => omega
  | succ memoryDepth =>
    cases flatDepth with
    | zero => omega
    | succ flatDepth =>
      cases compiled with
      | primitive payload => exact primitiveShapes _ payload _
      | enum payload schema => exact ⟨.scalar payload (.enum schema), .inr (.inl ⟨_, payload, rfl, .enum schema⟩)⟩
      | flags payload schema => exact ⟨.scalar payload (.flags schema), .inr (.inl ⟨_, payload, rfl, .flags schema⟩)⟩
      | endpoint | context | owner => exact ⟨.handle trivial, .inl (.inl trivial)⟩
      | aggregate children =>
        refine ⟨.aggregate ?_, ?_⟩
        · intro child member
          have smaller := List.sizeOf_lt_of_mem member
          simp only [Field.aggregate.sizeOf_spec] at memoryBound flatBound
          exact (recurse child (by simp only [Field.aggregate.sizeOf_spec]; omega)
            (children child member)
            memoryDepth flatDepth (by omega) (by omega)).1
        · intro child member
          have smaller := List.sizeOf_lt_of_mem member
          simp only [Field.aggregate.sizeOf_spec] at memoryBound flatBound
          exact (recurse child (by simp only [Field.aggregate.sizeOf_spec]; omega)
            (children child member)
            (memoryDepth + 1) flatDepth (by omega) (by omega)).2
      | fixed children =>
        refine ⟨.fixed ?_, ?_⟩
        · intro child member
          have smaller := List.sizeOf_lt_of_mem member
          simp only [Field.fixed.sizeOf_spec] at memoryBound flatBound
          exact (recurse child (by simp only [Field.fixed.sizeOf_spec]; omega)
            (children child member)
            memoryDepth flatDepth (by omega) (by omega)).1
        · intro child member
          have smaller := List.sizeOf_lt_of_mem member
          simp only [Field.fixed.sizeOf_spec] at memoryBound flatBound
          exact (recurse child (by simp only [Field.fixed.sizeOf_spec]; omega)
            (children child member)
            (memoryDepth + 1) flatDepth (by omega) (by omega)).2
      | list children =>
        refine ⟨.list ?_, .inr (.inr ⟨_, _, _, rfl, ?_⟩)⟩
        · intro child member
          have smaller := List.sizeOf_lt_of_mem member
          simp only [Field.dynamic.sizeOf_spec] at memoryBound flatBound
          exact (recurse child (by simp only [Field.dynamic.sizeOf_spec]; omega)
            (children child member)
            memoryDepth flatDepth (by omega) (by omega)).1
        · intro child member
          have smaller := List.sizeOf_lt_of_mem member
          simp only [Field.dynamic.sizeOf_spec] at memoryBound flatBound
          exact (recurse child (by simp only [Field.dynamic.sizeOf_spec]; omega)
            (children child member)
            (memoryDepth + 1) flatDepth (by omega) (by omega)).1
      | @map key element entries pairs values =>
        have entryShape (entry : Field) (member : entry ∈ entries) :
            ∃ fields, entry = .aggregate (.record (mapEntryFields key element)) fields ∧
              ∀ child ∈ fields, ParkedListTreeShape memoryDepth child := by
          obtain ⟨checked, value, rfl⟩ := pairs entry member
          refine ⟨_, rfl, ?_⟩
          intro child inFields
          rcases List.mem_cons.mp inFields with rfl | inTail
          · exact (primitiveShapes _ checked _).1
          · have equal : child = value := List.mem_singleton.mp inTail
            subst child
            have smaller := List.sizeOf_lt_of_mem member
            simp only [Field.aggregate.sizeOf_spec, List.cons.sizeOf_spec] at smaller
            simp only [Field.dynamic.sizeOf_spec] at memoryBound flatBound
            exact (recurse value (by simp only [Field.dynamic.sizeOf_spec]; omega) (values checked value member)
              memoryDepth flatDepth (by omega) (by omega)).1
        refine ⟨.map ?_ ?_, .inr (.inr ⟨_, _, _, rfl, ?_⟩)⟩
        · exact fun entry member => let ⟨fields, equal, _⟩ := entryShape entry member; ⟨fields, equal⟩
        · intro entry member fields equal
          obtain ⟨found, same, children⟩ := entryShape entry member
          exact (Field.aggregate.inj (same.symm.trans equal)).2 ▸ children
        · intro entry member
          obtain ⟨fields, rfl, children⟩ := entryShape entry member
          exact .aggregate children
      | sum children =>
        rename_i type arms tag selected
        cases selected with
        | none => exact ⟨.sum (fun _ equal => nomatch equal), fun _ member => nomatch member⟩
        | some child =>
          simp only [Field.sum.sizeOf_spec, Option.some.sizeOf_spec] at memoryBound flatBound
          refine ⟨.sum ?_, ?_⟩
          · intro selected equal
            cases equal
            exact (recurse child (by simp only [Field.sum.sizeOf_spec, Option.some.sizeOf_spec]; omega)
              (children child rfl) memoryDepth flatDepth (by omega) (by omega)).1
          · intro selected member
            have equal : selected = child := List.mem_singleton.mp member
            subst selected
            exact (recurse child (by simp only [Field.sum.sizeOf_spec, Option.some.sizeOf_spec]; omega)
              (children child rfl) (memoryDepth + 1) flatDepth (by omega) (by omega)).2

theorem parkedCompiledMemory (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (next : call.ReferenceNext) :
    ∃ depth, PayloadRoot.Cut call profile ready bindings (ParkedListTreeBody call depth next profile ready bindings) :=
  ⟨sizeOf call.field, parkedListTree call linked _ next
    (compiledShapes call.field linked.emitted _ _ (Nat.le_refl _) (Nat.le_refl _)).1⟩

theorem parkedCompiledFlat {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (next : call.ReferenceNext) :
    ∃ flatDepth entryDepth, PayloadRoot.Cut call profile ready bindings
      (ParkedFlatBody call flatDepth entryDepth next profile ready bindings) :=
  ⟨sizeOf call.field, sizeOf call.field, parkedFlat call linked _ _ next
    (compiledShapes call.field linked.emitted _ _ (Nat.le_refl _) (Nat.le_refl _)).2⟩

private theorem pairedCoreHead {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical : List (Seg (core3 grow) (HostState sig))}
    (paired : List.Forall₂ (ReturnFrame.Related.Segment older) (.core call.core call.resume :: checked) canonical) :
    ∃ tail, canonical = .core call.core call.resume :: tail ∧ List.Forall₂ (ReturnFrame.Related.Segment older) checked tail := by
  cases paired with
  | cons head tails => cases head with | same => exact ⟨_, rfl, tails⟩

theorem resumeReturned {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route)
    (value : route.output.Result) {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {reached reference : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older reached reference check canon) {segments}
    (caller : check.frames = .core call.core call.resume :: segments)
    (checked : reached.ctl = check.control (call.reply (.ok value)))
    (canonical : reference.ctl = canon.control (call.referenceReply value)) :
    let reply := route.reply call.destination call.start.host.nextTicket (.ok value)
    let dispatch := specDispatch ready (host bindings)
    ∃ left right, Steps profile ready dispatch reached [.tau, .tau, .tau] left ∧
      Steps profile ready dispatch reference [.tau] right ∧ left.store = right.store ∧
      left.host = reached.host.record reply.1 ∧ right.host = reference.host ∧
      List.Forall₂ (ReturnFrame.Related.Active older) left.ctl right.ctl := by
  have paired := frame.frames
  rw [caller] at paired
  obtain ⟨referenceSegments, referenceCaller, tails⟩ := pairedCoreHead call paired
  let reply := route.reply call.destination call.start.host.nextTicket (.ok value)
  rw [Cursor.control, caller] at checked
  rw [Cursor.control, referenceCaller] at canonical
  have checkRun := Plain.give_completion_steps (profile := profile) (ready := ready) (bindings := bindings) reply checked
  have referenceRun : Steps profile ready (specDispatch ready (host bindings)) reference [.tau]
      { reference with ctl := ⟨canon.thread, .core ((core3 grow).resume reference.store.core call.core (.values reply.2))
        call.resume, referenceSegments⟩ :: canon.rest } := .cons (.popCore canonical) (.refl _)
  refine ⟨_, _, checkRun, referenceRun, frame.store, rfl, rfl, ?_⟩
  rw [frame.store, frame.thread]
  exact .cons (.mk tails) frame.rest

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence
