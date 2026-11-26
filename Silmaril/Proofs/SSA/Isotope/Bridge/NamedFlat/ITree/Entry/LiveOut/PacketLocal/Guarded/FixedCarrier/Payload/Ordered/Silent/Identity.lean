module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Identity.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Thms
import Silmaril.Semantics.Elgot.Partition.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Scan.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Reachable.Thms
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (iter liftPure mapReturn partitionStep iter_partition iter_partition_outer)
open Silmaril.Elgot.ITree (Tree diverge iterate_fixpoint iterate_uniformity iterate_pure_loop vis_bind)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Transfer region)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Head ConfigurationEnumeration Table)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint exit_type)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit Packets numberedInterface requestTypes restoreAt encodeValue)
open LiveBit (rawWithLiterals)
open PayloadRecognition (packetValue)
open Syntax (Payload StatePrimitives)

attribute [local instance] requestTypes

universe v

variable {Φ : Type} {slots : List Bool}

private theorem cast_value {A B : Syntax.Ty} (same : A = B) (value : Payload A) :
    (cast (congrArg Payload same) value).val = value.val := by
  cases same
  rfl

private theorem step_cast {A B : Syntax.Ty} (eq : A = B) (row : Row Φ (layout slots) A) (caller : Payload Bit)
    (packet : Payload B) :
    activeStep (cast (congrArg (Row Φ (layout slots)) eq) row) caller packet =
      activeStep row caller (cast (congrArg Payload eq.symm) packet) := by
  cases eq
  rfl

variable (p : Profile Φ slots) (caller : Payload Bit)

local notation "inner" => partitionStep (p.rawStep caller) p.isJump
private def phaseAt {L : List Syntax.Ty} (q : Packet L) : Phase L := ⟨.inr q⟩

private theorem inner_jump {i j : Fin (layout slots).length} {typed : (layout slots).get j = (layout slots).get i}
    (jump : p i = .jump j typed) (value : Payload ((layout slots).get i)) :
    inner (phaseAt ⟨i, value⟩) = pure (.inr (phaseAt (jumpPacket j typed value))) := by
  simp [partitionStep, phaseAt, Profile.rawStep, Profile.isJump, jump, Row.step]

private theorem follow {fuel : Nat} {i : Fin (layout slots).length} {result : Result (layout slots).length 1}
    (found : p.scan fuel i = some result) :
    ∃ j, ∃ same : (layout slots).get j = (layout slots).get i, result = .ret j 0 ∧
      ∀ value : Payload ((layout slots).get i),
        iter inner (phaseAt ⟨i, value⟩) = activeStep (p j) caller (cast (congrArg Payload same.symm) value) := by
  induction fuel generalizing i with
  | zero => cases found
  | succ fuel ih =>
    unfold Profile.scan at found
    rw [search] at found
    cases row : p i with
    | jump j typed =>
      have tail : p.scan fuel j = some result := by
        simpa [Profile.silent, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row, Profile.scan] using found
      obtain ⟨k, same, tag, execute⟩ := ih tail
      refine ⟨k, same.trans typed, tag, fun value => ?_⟩
      rw [congrFun (iterate_fixpoint inner) (phaseAt ⟨i, value⟩), inner_jump p caller row]
      simp only [pure_bind, Sum.elim_inr]
      exact (execute (jumpPacket j typed value).2).trans (by simp [jumpPacket, cast_cast])
    | request op ty routes =>
      have terminal : result = .ret i 0 := by
        simpa [Profile.silent, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row] using found.symm
      refine ⟨i, rfl, terminal, fun value => ?_⟩
      rw [iter_partition_outer _ _ _ (by simp [phaseAt, Profile.isJump, row])]
      simp [phaseAt, Profile.rawStep, row, Row.step]
    | ret tag bit ty fields =>
      have terminal : result = .ret i 0 := by
        simpa [Profile.silent, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row] using found.symm
      refine ⟨i, rfl, terminal, fun value => ?_⟩
      rw [iter_partition_outer _ _ _ (by simp [phaseAt, Profile.isJump, row])]
      simp [phaseAt, Profile.rawStep, row, Row.step]

private theorem exhausted {i : Fin (layout slots).length} (none : p.scan (layout slots).length i = none)
    (value : Payload ((layout slots).get i)) : iter inner (phaseAt ⟨i, value⟩) = diverge := by
  obtain ⟨labels, start, steps⟩ := scan_exhausted_path (p.silent (fun _ => false)).labelRows i none
  let At (n : Nat) := {q : Packet (layout slots) // q.1 = labels n}
  have advance (n : Nat) (q : At n) :
      ∃ next : At (n + 1), inner (phaseAt q.val) = pure (.inr (phaseAt next.val)) := by
    obtain ⟨⟨i, payload⟩, position⟩ := q
    change i = labels n at position
    subst i
    have edge := steps n
    cases row : p (labels n) with
    | jump j typed =>
      have next : j = labels (n + 1) := by simpa [Profile.silent, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row] using edge
      exact ⟨⟨jumpPacket j typed payload, next⟩, inner_jump p caller row payload⟩
    | request | ret => simp [Profile.silent, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row] at edge
  let path : (n : Nat) → At n := Nat.rec ⟨⟨i, value⟩, start.symm⟩ (fun n q => (advance n q).choose)
  let encode (n : ULift.{1} Nat) : Phase (layout slots) := phaseAt (path n.down).val
  let loop (n : ULift.{1} Nat) : Tree (Request Φ) ((Transfer Runtime ⊕ Phase (layout slots)) ⊕ ULift.{1} Nat) :=
    pure (.inr ⟨n.down + 1⟩)
  have commute : (loop >=> liftPure (Sum.map id encode)) = (liftPure encode >=> inner) := by
    funext n
    change (pure (.inr ⟨n.down + 1⟩) >>= liftPure (Sum.map id encode)) = (pure (encode n) >>= inner)
    simp only [pure_bind, liftPure, Function.comp_apply, Sum.map_inr]
    exact (advance n.down (path n.down)).choose_spec.symm
  have same := congrFun (iterate_uniformity loop inner encode commute) ⟨0⟩
  change iter loop ⟨0⟩ = (pure (phaseAt ⟨i, value⟩) >>= iter inner) at same
  rw [pure_bind] at same
  exact same.symm.trans (iterate_pure_loop (fun n : ULift.{1} Nat => ⟨n.down + 1⟩) ⟨0⟩)

theorem normalize : iter (p.rawStep caller) = iter (p.normalStep caller) := by
  rw [← iter_partition (p.rawStep caller) p.isJump]
  congr 1
  funext phase
  rcases phase with ⟨result | ⟨i, payload⟩⟩
  · rw [iter_partition_outer _ _ _ rfl]
    rfl
  · change iter inner (phaseAt ⟨i, payload⟩) = p.normalStep caller (phaseAt ⟨i, payload⟩)
    cases found : p.scan (layout slots).length i with
    | none =>
      rw [exhausted p caller found]
      have empty : p.resolved (layout slots).length i = none := by rw [Profile.resolved, found]
      simp only [Profile.normalStep, phaseAt, empty]
    | some result =>
      obtain ⟨j, same, rfl, execute⟩ := follow p caller found
      rw [execute payload]
      simp only [phaseAt, Profile.normalStep, Profile.resolved, found, dite_eq_left same]
      exact (step_cast same (p j) caller payload).symm

private theorem specialize_identity {A B : Syntax.Ty} (eq : A = B) (row : Row Φ (layout slots) A) :
    LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.specialize
        (cast (congrArg (Syntax.Expr [B, Bit]) eq.symm) (.var 0)) row.guarded =
      (cast (congrArg (Row Φ (layout slots)) eq) row).guarded := by
  cases eq
  cases row with
  | jump | ret => rfl
  | request op typed routes =>
    cases typed
    rfl

private theorem scan_selected (selected : Tag → Bool) :
    (p.silent selected).labelRows = (p.silent (fun _ => false)).labelRows := by
  funext i
  cases row : p i <;> simp [Profile.silent,
    LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row]

private theorem resolve_found (selected : Tag → Bool) (fuel : Nat) (i j : Fin (layout slots).length)
    (found : p.scan fuel i = some (.ret j 0)) :
    ∃ eq : (layout slots).get j = (layout slots).get i,
      (p.silent selected).resolve fuel i = some (cast (congrArg (Row Φ (layout slots)) eq) (p j)).guarded := by
  induction fuel generalizing i with
  | zero => cases found
  | succ fuel ih =>
    unfold Profile.scan at found
    rw [search] at found
    cases row : p i with
    | jump k same =>
      have next : p.scan fuel k = some (.ret j 0) := by
        simpa [Profile.scan, Profile.silent,
          LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row] using found
      obtain ⟨eq, exposed⟩ := ih k next
      refine ⟨eq.trans same, ?_⟩
      rw [LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.resolve]
      simp only [Profile.silent, row]
      change ((p.silent selected).resolve fuel k).map _ = _
      rw [exposed]
      apply congrArg some
      exact (specialize_identity same (cast (congrArg (Row Φ (layout slots)) eq) (p j))).trans
        (congrArg Row.guarded (cast_cast _ _ (p j)))
    | request op typed routes =>
      have same : i = j := by
        simpa [Profile.silent,
          LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row] using found
      subst j
      refine ⟨rfl, ?_⟩
      simp [LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.resolve,
        Profile.silent, row]
    | ret tag bit typed fields =>
      have same : i = j := by
        simpa [Profile.silent,
          LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.labelRows, row] using found
      subst j
      refine ⟨rfl, ?_⟩
      simp [LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table.resolve,
        Profile.silent, row]

include caller in
private theorem normalize_control (selected : Tag → Bool) (i : Fin (layout slots).length) :
    (p.endpoint selected).control.row i = ((p.resolved (layout slots).length i).map Row.guarded).getD .diverge := by
  change ((p.silent selected).resolve (layout slots).length i).getD .diverge = _
  cases found : p.scan (layout slots).length i with
  | none =>
    have empty : (p.silent selected).resolve (layout slots).length i = none :=
      ((p.silent selected).resolve_none_iff _ i).mpr (by rw [scan_selected p]; exact found)
    rw [Profile.resolved, found, empty]
    rfl
  | some result =>
    obtain ⟨j, _, rfl, _⟩ := follow p caller found
    obtain ⟨eq, exposed⟩ := resolve_found p selected _ i j found
    rw [exposed, Profile.resolved, found]
    simp only [dite_eq_left eq, Option.map_some, Option.getD_some]
    rfl

private theorem arg_eval {A : Syntax.Ty} (h : A = Bit) (caller : Payload Bit) (packet : Payload A) :
    (cast (congrArg (Syntax.Expr [A, Bit]) h) (.var 0)).eval ((Syntax.emptyBindings.push caller).push packet) =
      cast (congrArg Payload h) packet := by
  cases h
  rfl

theorem roots (selected : Tag → Bool) : RootAgrees (p.endpoint selected) caller (p.tree caller) := by
  rintro ⟨i, input⟩
  have output : (p.endpoint selected).output i = ((p.resolved (layout slots).length i).map Row.output).getD
      (recordExpr (bitExpr false) (bitExpr false)) := rfl
  have body : p.normalStep caller ⟨.inr ⟨i, input⟩⟩ =
      (p.resolved (layout slots).length i).elim diverge (fun row => activeStep row caller input) := by
    change (match p.resolved (layout slots).length i with
      | some row => activeStep row caller input
      | none => diverge) = _
    cases p.resolved (layout slots).length i <;> rfl
  unfold Profile.tree
  rw [congrFun (iterate_fixpoint (p.normalStep caller))]
  have head : (p.endpoint selected).control.head caller ⟨i, input⟩ =
      match ((p.resolved (layout slots).length i).map Row.guarded).getD .diverge with
      | .exit i => Head.exit i (selected i)
      | .diverge => Head.diverge
      | .request op arg next typed => Head.request op
          (arg.eval ((Syntax.emptyBindings.push caller).push input))
          (fun j v => ⟨next j, cast (congrArg Payload (typed j).symm) v⟩) := by
    unfold Table.head
    rw [show (p.endpoint selected).control.row (⟨i, input⟩ : Packet (layout slots)).1 =
      ((p.resolved (layout slots).length i).map Row.guarded).getD .diverge from
      normalize_control p caller selected i]
    dsimp only [Table.bindings]
    cases ((p.resolved (layout slots).length i).map Row.guarded).getD .diverge <;> rfl
  rw [body, head]
  cases found : p.resolved (layout slots).length i with
  | none => simp
  | some row =>
    cases row with
    | jump => simp [activeStep, Row.guarded]
    | ret tag bit eq fields =>
      simp only [Option.elim_some, Option.map_some, Option.getD_some, activeStep, Row.guarded, pure_bind, Sum.elim_inr]
      rw [congrFun (iterate_fixpoint (p.normalStep caller))]
      simp only [Profile.normalStep, pure_bind, Sum.elim_inl]
      have same : (p.endpoint selected).returnPacket caller ⟨i, input⟩ tag =
          returnPacket (R := layout slots) (.ret tag bit eq fields) caller input tag := by
        unfold Endpoint.returnPacket returnPacket
        rw [show (p.endpoint selected).output i = (Row.ret tag bit eq fields).output from by rw [output, found]; rfl]
        rfl
      rw [← same]
      rfl
    | request op eq routes =>
      simp only [Option.elim_some, Option.map_some, Option.getD_some, activeStep, Row.guarded,
        pure_bind, Sum.elim_inr, query, vis_bind]
      exact congrArg (fun arg : Payload Bit => Silmaril.Elgot.ITree.vis (Request.call op arg)
        (fun reply => p.tree caller ⟨routes.dest reply.1,
          cast (congrArg Payload (routes.typed reply.1).symm) reply.2⟩)) (arg_eval eq caller input).symm


theorem restore_block {K : Type 1} (keys : Fin ((layout slots).length + 2) ≃ K)
    (i : Fin (layout slots).length) (input : Value Runtime) :
    restoreAt keys (i.val, input) = (keys (i.castAdd 2), input) := by
  unfold restoreAt
  rw [dite_eq_left (show i.val < (layout slots).length + 2 by omega)]
  rfl

private theorem restore_exit {K : Type 1} (keys : Fin ((layout slots).length + 2) ≃ K)
    (i : Tag) (input : Value Runtime) :
    restoreAt keys ((i.natAdd (layout slots).length).val, input) = (keys (i.natAdd (layout slots).length), input) := by
  unfold restoreAt
  rw [dite_eq_left (i.natAdd (layout slots).length).isLt]

private theorem request_agreement (literals : Φ → Option Bool) (op : Φ) :
    ∀ packet : Payload Bit, rawWithLiterals literals op (encodeValue ULift.up packet.val) =
      (query op packet >>= fun reply => pure (Recognize.replyValue ULift.up reply.down)) := by
  rintro ⟨value, typed⟩
  cases typed with
  | inl typedUnit => cases typedUnit; exact query_agrees op ⟨.inl .unit, .inl .unit⟩
  | inr typedUnit => cases typedUnit; exact query_agrees op ⟨.inr .unit, .inr .unit⟩

private theorem jump_eval (literals : Φ → Option Bool) (j : Fin (layout slots).length)
    (packet : Value Runtime) (env : Env Runtime) :
    region (rawWithLiterals literals) (extend env (.pair packet .unit)) (jumpAt j).erase =
      pure (j.val, .pair packet .unit) := by
  simp only [jumpAt, Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, pure_bind]
  rfl

private theorem ret_eval {A : Syntax.Ty} {bit : Bool} (literals : Φ → Option Bool) (i : Tag)
    (eq : A = slotType bit) (fields : Fields Φ bit) (agree : fields.Agrees literals)
    (caller : Payload Bit) (packet : Payload A) (env : Env Runtime) :
    region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up packet.val) .unit))
      (fields.rowAt (d := (layout slots).length) i).erase =
      pure ((i.natAdd (layout slots).length).val, packetValue (returnPacket (.ret i bit eq fields : Row Φ (layout slots) A) caller packet i)) := by
  subst A
  change _ = pure ((i.natAdd (layout slots).length).val, encodeValue ULift.up
    (cast (congrArg Payload (exit_type (A := PayloadType) i).symm)
      (fields.output.eval ((Syntax.emptyBindings.push caller).push packet))).val)
  rw [cast_value (exit_type (A := PayloadType) i).symm]
  exact fields.eval_row_at literals agree i env packet _

theorem row_replay {κ K : Type 1} {P : FlatInstitution.Signature.{0, 0} κ}
    (names : Fin ((layout slots).length + 2) ≃ K) (i : Fin (layout slots).length)
    (row : Row P.Instr (layout slots) ((layout slots).get i))
    (literals : P.Instr → Option Bool) (agrees : row.Agrees literals) (caller : Payload Bit)
    (packet : Payload ((layout slots).get i)) (env : Env Runtime) :
    (row.step caller packet >>= liftPure (Sum.map id (encodePhase names))) =
      (region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up packet.val) .unit)) row.code.erase >>=
        fun q => pure (.inr (restoreAt names q))) := by
  cases row with
  | jump j typed =>
    simp only [Row.step, Row.code, jump_eval, pure_bind, liftPure, Function.comp_apply, Sum.map_inr,
      encodePhase, jumpPacket, restore_block]
    rw [cast_value typed.symm]
  | ret tag bit eq fields =>
    have agrees : fields.Agrees literals := agrees
    simp only [Row.step, Row.code, ret_eval literals tag eq fields agrees caller packet env,
      activeStep, pure_bind, liftPure, Function.comp_apply, Sum.map_inr, encodePhase, restore_exit]
    rfl
  | request op eq routes =>
    let incoming := cast (congrArg Payload eq) packet
    have run := Recognize.eval_request_at (P := P) (opcode := op) ULift.up query (rawWithLiterals literals) routes.dest routes.fallback
      (request_agreement literals op) env incoming
    change region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up incoming.val) .unit))
      (Recognize.requestAt op routes.dest routes.fallback).erase = _ at run
    have same : incoming.val = packet.val := cast_value eq packet
    rw [same] at run
    simp only [Row.step, Row.code, run, activeStep, bind_assoc, pure_bind, liftPure, Function.comp_apply,
      Sum.map_inr, encodePhase, restore_block]
    congr 1
    funext r
    rw [cast_value (routes.typed r.down.1).symm]

section Named

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ}
  {seed first second : V} {names : Fin ((layout slots).length + 2) ≃ K} {source : CFG V K P.Instr}
  {literals : P.Instr → Option Bool}
  (ck : Identity.Checked (P := P) (slots := slots) (seed := seed) (first := first) (second := second)
    (names := names) source literals)
  (input : V → Value Runtime) (entry : Payload Bit)

local notation "instr" => rawWithLiterals literals
local notation "I" => numberedInterface (κ := κ) seed names
local notation "store" => fun (r : V × Nat) => input (Prod.fst r)
local notation "out" => fun q => FiniteCFG.packedTreeOutput (treeExitNumber (Interface.exits (I)) q)

private theorem entry_eval (seedValue : input seed = encodeValue ULift.up entry.val) :
    ck.admitted.versioned.source.entry.evalJump (treeModel instr) store =
      pure (encodePhase names (phaseAt ⟨0, entry⟩)) := by
  rw [ck.readback.entry_eval instr store (fun _ => encodeValue ULift.up entry.val) (fun _ => seedValue.symm)]
  simp only [Identity.Profile.expected, Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, pure_bind, phaseAt, encodePhase]
  exact congrArg pure (restore_block names 0 (.pair (encodeValue ULift.up entry.val) .unit))

private theorem step_eval (phase : Phase (layout slots)) :
    (ck.profile.rawStep entry phase >>= liftPure (Sum.map id (encodePhase names))) =
      mapReturn (CFG.Cyclic.stepSSA (treeModel instr) ck.admitted.versioned.source.blocks store)
        (liftPure out) (encodePhase names phase) := by
  rcases phase with ⟨p | ⟨i, packet⟩⟩
  · simp only [Profile.rawStep, pure_bind, liftPure, Function.comp_apply, Sum.map_inl, id_eq]
    exact (ck.readback.exit_eval instr store (packetValue p) p.1).symm
  · let env : Env Runtime := fun _ => .unit
    change _ = mapReturn (CFG.Cyclic.stepSSA (treeModel instr) ck.admitted.versioned.source.blocks store)
      (liftPure out) (names (i.castAdd 2), Value.pair (encodeValue ULift.up packet.val) .unit)
    unfold mapReturn
    rw [ck.readback.block_eval instr store env]
    simp only [Identity.Profile.expected, bind_assoc]
    simp only [pure_bind, Sum.elim_inr, Function.comp_apply]
    exact row_replay names i (ck.profile i) literals (ck.literals_agree i) entry packet env

theorem named_tree (seedValue : input seed = encodeValue ULift.up entry.val) :
    LiveOut.observeRaw instr (I).exits (fun _ => [first, second]) source input = ck.profile.tree entry ⟨0, entry⟩ :=
  (Guarded.observe_eq_of_steps (a := ck.admitted) (input := store) (phaseAt (⟨0, entry⟩ : Packet (layout slots)))
    (ck.profile.rawStep entry) (encodePhase names) (entry_eval ck input entry seedValue)
    (step_eval ck input entry)).trans (congrFun (normalize ck.profile entry) _)

theorem native_observation [DecidableEq P.Instr] {σ : Type v}
    (seedValue : input seed = encodeValue ULift.up entry.val)
    (selected : Tag → Bool) (raw : Typed P.Instr [Bit] Outputs)
    (valid : (ck.profile.endpoint selected).checkNative raw = true) (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedNumbered source names first second input literals prim s selected =
      Shape.denote (withExitUB raw selected) (Syntax.model prim ((ck.profile.endpoint selected).control.bindings entry)) s := by
  unfold observeNamedNumbered
  rw [named_tree ck input entry seedValue]
  let g := ck.profile.endpoint selected
  exact (observe_roots_on g entry prim (ck.profile.tree entry) (roots ck.profile entry selected)
    (constructorDecoder PayloadType) constructorDecoder_return ⟨0, entry⟩ s).trans
      (g.observe_entry_state raw valid entry prim s).symm

end Named

section Compare

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} [DecidableEq P.Instr]
  {seed first second : V} {names : Fin ((layout slots).length + 2) ≃ K} {source target : CFG V K P.Instr}
  {literals : P.Instr → Option Bool}
  (left : Identity.Checked (P := P) (slots := slots) (seed := seed) (first := first) (second := second)
    (names := names) source literals)
  (right : Identity.Checked (P := P) (slots := slots) (seed := seed) (first := first) (second := second)
    (names := names) target literals)
  (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
  (caller : Payload Bit) (store store' : V → Value Runtime)
  (configs : ConfigurationEnumeration (layout slots))

local notation "verdict" => Identity.compare? (some left) (some right) raw raw' selected selected'
  caller store store' configs

theorem none_iff :
    verdict = none ↔ Silent.matchesCaller caller (store seed) = false ∨
      Silent.matchesCaller caller (store' seed) = false ∨
      (left.profile.endpoint selected).checkNative raw = false ∨
      (right.profile.endpoint selected').checkNative raw' = false := by
  cases l : Silent.matchesCaller caller (store seed) <;>
    cases r : Silent.matchesCaller caller (store' seed) <;>
    cases nativeL : (left.profile.endpoint selected).checkNative raw <;>
    cases nativeR : (right.profile.endpoint selected').checkNative raw' <;>
    simp [Identity.compare?, Endpoint.checkReachable?, Endpoint.checkAllInterpreters?, l, r, nativeL, nativeR]

variable (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller.val)
  (valid : (left.profile.endpoint selected).checkNative raw = true)
  (valid' : (right.profile.endpoint selected').checkNative raw' = true)

include seedValue seedValue' in
private theorem compare_eq :
    verdict = (left.profile.endpoint selected).checkReachable? (right.profile.endpoint selected')
      raw raw' outputCodes caller caller replyPackets configs configs := by
  simp [Identity.compare?, (Silent.matchesCaller_iff caller _).mpr seedValue,
    (Silent.matchesCaller_iff caller _).mpr seedValue']

include seedValue seedValue' valid valid'

theorem acceptance_sound {σ : Type v} (yes : verdict = some true) (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedNumbered source names first second store literals prim s selected ≤
      observeNamedNumbered target names first second store' literals prim s selected' := by
  rw [compare_eq left right raw raw' selected selected' caller store store' configs seedValue seedValue'] at yes
  rw [native_observation left store caller seedValue selected raw valid prim s,
    native_observation right store' caller seedValue' selected' raw' valid' prim s]
  exact Endpoint.checkReachable_sound valid valid' yes prim s

theorem acceptance_iff :
    verdict = some true ↔
      ∀ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        observeNamedNumbered source names first second store literals prim s selected ≤
          observeNamedNumbered target names first second store' literals prim s selected' := by
  constructor
  · intro yes σ prim s
    exact acceptance_sound left right raw raw' selected selected' caller store store' configs
      seedValue seedValue' valid valid' yes prim s
  · intro named
    rw [compare_eq left right raw raw' selected selected' caller store store' configs seedValue seedValue']
    apply (Endpoint.checkReachable_accepts_iff valid valid').mpr
    intro σ prim s
    simpa only [native_observation left store caller seedValue selected raw valid prim s,
      native_observation right store' caller seedValue' selected' raw' valid' prim s] using! named σ prim s

theorem rejection_iff :
    verdict = some false ↔
      ∃ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        ¬ observeNamedNumbered source names first second store literals prim s selected ≤
          observeNamedNumbered target names first second store' literals prim s selected' := by
  classical
  have accepted := acceptance_iff left right raw raw' selected selected' caller store store'
    configs seedValue seedValue' valid valid'
  have supported : verdict ≠ none := by
    rw [ne_eq, none_iff]
    simp [(Silent.matchesCaller_iff caller _).mpr seedValue,
      (Silent.matchesCaller_iff caller _).mpr seedValue', valid, valid']
  cases checked : verdict with
  | none => exact (supported checked).elim
  | some answer =>
    simp only [checked, Option.some.injEq] at accepted ⊢
    simp only [Bool.eq_false_iff, ne_eq, accepted, not_forall]

end Compare

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity
