module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Defs

public import Silmaril.Semantics.Elgot.Partition.Defs
import Silmaril.Semantics.Elgot.Partition.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix
open LambdaSSA (FiniteCFG Flat Region)
open LambdaSSA.Semantics (Env extend extend_zero extend_succ)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive Transfer region splitTransfer term term_rename)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Expr PacketType PrimitiveSignature Slot)
open Silmaril.Elgot (iter liftPure partitionTransfer partitionStepByTarget iter_partition_target)
open Silmaril.Elgot.ITree (Tree diverge diverge_bind iterate_fixpoint iterate_uniformity)

universe u w
variable {E : Type w → Type w} {F : Type} {α : Type u}
  {Γ : List PacketType} {exits blocks captures count : Nat}
  {sig : PrimitiveSignature F} {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}

theorem load_ambient (frame : Frame Γ) (values : Values Γ α) (env : Env α) (i : Nat) :
    frame.load values env (frame.shift + i) = env i := by
  induction frame generalizing env i with
  | entry => simp [Frame.load, Frame.shift]
  | push ty prev ih =>
    simp only [Frame.load, Frame.shift, Nat.add_assoc]
    rw [ih, show 2 + i = (i + 1) + 1 by omega]
    rfl

theorem load_slot (frame : Frame Γ) (values : Values Γ α) (env : Env α) (i : Nat)
    (packet : env i = frame.pack values) {ty : PacketType} (slot : Slot Γ ty) :
    frame.load values env (frame.position i slot) = values slot := by
  induction frame generalizing env i with
  | entry =>
    cases slot with
    | here => exact packet
    | there old => cases old
  | push ty prev ih =>
    cases slot with
    | here =>
      simp only [Frame.position, Frame.load]
      rw [show prev.shift = prev.shift + 0 by simp, load_ambient]
      rfl
    | there old =>
      simp only [Frame.position, Frame.load]
      exact ih _ _ 1 rfl old

private theorem unpack_tree (instr : Primitive E F α) (frame : Frame Γ) (values : Values Γ α)
    (env : Env α) (i : Nat) (body : Region F) (packet : env i = frame.pack values) :
    region instr env (frame.unpack i body) = region instr (frame.load values env) body := by
  induction frame generalizing env i with
  | entry => rfl
  | push ty prev ih =>
    simp only [Frame.unpack, region, term, pure_bind, packet, Frame.pack, Frame.load]
    exact ih _ _ 1 rfl

private theorem operand_tree (instr : Primitive E F α) (layout : Positions Γ)
    (env : Env α) (values : Values Γ α) {ty : PacketType} (value : Expr Γ ty)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (layout slot) = values slot) :
    term instr env (operand layout value) = pure (evalOperand values value) := by
  induction value with
  | var slot => simp only [operand, term, evalOperand, agree]
  | unit => rfl
  | pair left right hl hr => simp only [operand, term, evalOperand, hl, hr, pure_bind]

private theorem exit_transfer (blocks : Nat) (port : Fin exits) (value : Value α) :
    splitTransfer blocks (blocks + port.val, value) = .inl (port.val, value) := by
  simp [splitTransfer, show ¬ blocks + port.val < blocks by omega]

private theorem local_transfer (label : Fin blocks) (value : Value α) :
    splitTransfer blocks (label.val, value) = .inr (label, value) := by
  simp [splitTransfer, label.isLt]

private theorem bind_agrees {ty : PacketType} (layout : Positions Γ) (env : Env α) (values : Values Γ α)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (layout slot) = values slot)
    (payload : Value α) {τ : PacketType} (slot : Slot (ty :: Γ) τ) :
    extend env payload (bindPosition layout slot) = bindReply values payload slot := by
  cases slot with
  | here => rfl
  | there old => exact agree old

/-- Restored slots agree before the tail. Each selected case extends that
agreement with its payload, so the literal leaf sees the same packet
operands at any nesting depth. -/
private theorem case_tree {newBlocks : Nat} {β : Type u}
    (instr : Primitive E F α) (old : Fin blocks → Fin newBlocks) (layout : Positions Γ)
    (env : Env α) (values : Values Γ α)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (layout slot) = values slot)
    (tail : CaseTail packets outputs Γ) (finish : (Transfer α ⊕ BlockInput α newBlocks) → Tree E β) :
    (region instr env (CaseTail.erase old layout tail) >>= fun out => finish (splitTransfer newBlocks out)) =
      (CaseTail.run values tail >>= fun out => finish (Sum.map id (fun state => (old state.1, state.2)) out)) := by
  induction tail generalizing env with
  | jump label packet =>
    rw [CaseTail.erase, region, bind_assoc, operand_tree instr layout env values packet agree, pure_bind]
    cases label with
    | inl target => simp only [Sum.elim_inl, pure_bind, local_transfer, CaseTail.run, Sum.map_inr]
    | inr port => simp only [Sum.elim_inr, pure_bind, exit_transfer, CaseTail.run, Sum.map_inl, id_eq]
  | case test left right ihLeft ihRight =>
    simp only [CaseTail.erase, region, operand_tree instr layout env values test agree, pure_bind, CaseTail.run]
    cases evalOperand values test with
    | inl payload => exact ihLeft (bindPosition layout) _ _ (bind_agrees layout env values agree payload)
    | inr payload => exact ihRight (bindPosition layout) _ _ (bind_agrees layout env values agree payload)
    | atom _ | unit | pair _ _ => simp only [diverge_bind]

private theorem finish_old {newBlocks : Nat} (inner : BlockInput α newBlocks → Bool)
    (old : Fin blocks → Fin newBlocks) (outside : ∀ i packet, inner (old i, packet) = false)
    (run : BlockInput α newBlocks → Tree E (Transfer α ⊕ BlockInput α newBlocks))
    (out : Transfer α ⊕ BlockInput α blocks) :
    Sum.elim pure run (partitionTransfer inner (Sum.map id (fun state => (old state.1, state.2)) out)) =
      pure (Sum.map id (fun state => (old state.1, state.2)) out) := by
  rcases out with result | ⟨label, packet⟩
  · rfl
  · simp only [Sum.map_inr, partitionTransfer, outside, Bool.false_eq_true, ite_false, Sum.elim_inl]

private theorem unsplit_step (instr : Primitive E F α) (row : Row sig packets outputs Γ)
    (env : Env α) (values : Values Γ α)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (position slot) = values slot) :
    (region instr env (row.erase) >>= fun out => pure (splitTransfer blocks out)) =
      row.run instr values := by
  induction row generalizing env with
  | exit port value =>
    simp only [Row.erase, region, operand_tree instr position env values value agree, pure_bind,
      exit_transfer, Row.run]
  | jump target value =>
    simp only [Row.erase, region, operand_tree instr position env values value agree, pure_bind,
      local_transfer, Row.run]
  | branch tail =>
    change (region instr env (CaseTail.erase id position tail) >>= fun out => pure (splitTransfer blocks out)) = _
    rw [case_tree instr id position env values agree tail pure]
    have identity (out : Transfer α ⊕ BlockInput α blocks) :
        Sum.map id (fun state => (id state.1, state.2)) out = out := by cases out <;> rfl
    simp only [Row.run, identity, bind_pure]
  | request op arg tail ih =>
    simp only [Row.erase, region, term, operand_tree instr position env values arg agree, pure_bind,
      bind_assoc, Row.run]
    apply bind_congr
    intro reply
    apply ih
    intro τ slot
    cases slot with
    | here => rfl
    | there old => exact agree old

private noncomputable def step (instr : Primitive E F α) (env : Env α)
    (graph : FiniteCFG F blocks exits captures) (p : BlockInput α blocks) :
    Tree E (Transfer α ⊕ BlockInput α blocks) :=
  region instr (extend env p.2) (graph.block p.1).erase >>= fun out => pure (splitTransfer blocks out)

/-- The emitted request makes one observable call and then transfers the
same frame paired with the reply to its assigned continuation. -/
private theorem request_cell_step {newBlocks : Nat}
    (instr : Primitive E F α) (ambient : Env α) (graph : FiniteCFG F newBlocks exits captures)
    (frame : Frame Γ) (values : Values Γ α) (op : F) (arg : Expr Γ (sig.argument op))
    (head next : Fin newBlocks) (row : (graph.block head).erase = frame.requestCell op arg next) :
    step instr ambient graph (head, frame.pack values) =
      (instr op (evalOperand values arg) >>= fun reply =>
        pure (.inr (next, (Frame.push (sig.reply op) frame).pack (bindReply values reply)))) := by
  unfold step
  rw [row, Frame.requestCell, unpack_tree instr frame values _ 0 _ rfl]
  have saved : frame.load values (extend ambient (frame.pack values)) frame.shift = frame.pack values := by
    simpa only [Nat.add_zero, extend_zero] using
      load_ambient frame values (extend ambient (frame.pack values)) 0
  simp only [region, term, operand_tree instr _ _ values arg
      (load_slot frame values (extend ambient (frame.pack values)) 0 rfl), bind_assoc, pure_bind, extend_succ, extend_zero, saved, local_transfer, Frame.pack, bindReply]

/-- Evaluate a prefix to its first old transfer. Only a successor in the
fresh suffix can recurse in this inner run. -/
private theorem follow {newBlocks : Nat}
    (instr : Primitive E F α) (env : Env α) (graph : FiniteCFG F newBlocks exits captures)
    (inner : BlockInput α newBlocks → Bool) (old : Fin blocks → Fin newBlocks)
    (oldOutside : ∀ i packet, inner (old i, packet) = false)
    (row : Row sig packets outputs Γ) (frame : Frame Γ) (values : Values Γ α)
    (labels : Fin (row.requests + 1) → Fin newBlocks)
    (freshInside : ∀ (i : Fin row.requests) packet, inner (labels i.succ, packet) = true)
    (rows : ∀ i, (graph.block (labels i)).erase = (row.cells old frame labels i).2) :
    iter (partitionStepByTarget (step instr env graph) inner) (labels 0, frame.pack values) =
      Sum.map id (fun state => (old state.1, state.2)) <$> row.run instr values := by
  induction row with
  | exit port value =>
    rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env graph) inner)) (labels 0, frame.pack values)]
    simp only [partitionStepByTarget, step, rows 0, Row.cells, map_eq_pure_bind, bind_assoc, pure_bind]
    rw [unpack_tree instr frame values _ 0 _ rfl]
    simp only [region, operand_tree instr _ _ values value (load_slot frame values (extend env (frame.pack values)) 0 rfl),
      pure_bind, exit_transfer, partitionTransfer, Sum.elim_inl, Row.run, Sum.map_inl, id_eq]
  | jump target value =>
    rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env graph) inner)) (labels 0, frame.pack values)]
    simp only [partitionStepByTarget, step, rows 0, Row.cells, map_eq_pure_bind, bind_assoc, pure_bind]
    rw [unpack_tree instr frame values _ 0 _ rfl]
    simp only [region, operand_tree instr _ _ values value (load_slot frame values (extend env (frame.pack values)) 0 rfl),
      pure_bind, local_transfer, partitionTransfer, oldOutside, Bool.false_eq_true, ite_false, Sum.elim_inl,
      Row.run, Sum.map_inr]
  | branch tail =>
    rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env graph) inner)) (labels 0, frame.pack values)]
    simp only [partitionStepByTarget, step, rows 0, Row.cells, map_eq_pure_bind, bind_assoc, pure_bind]
    rw [unpack_tree instr frame values _ 0 _ rfl,
      case_tree instr old (frame.position 0) _ values (load_slot frame values (extend env (frame.pack values)) 0 rfl) tail
        (fun out => Sum.elim pure (iter (partitionStepByTarget (step instr env graph) inner))
          (partitionTransfer inner out))]
    simp only [Row.run, finish_old inner old oldOutside]
  | request op arg tail ih =>
    rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env graph) inner)) (labels 0, frame.pack values)]
    let next := labels (0 : Fin (tail.requests + 1)).succ
    have head : (graph.block (labels 0)).erase = frame.requestCell op arg next := by
      simpa only [Row.cells, Fin.cases_zero, next] using rows 0
    simp only [partitionStepByTarget, request_cell_step instr env graph frame values op arg _ _ head,
      map_eq_pure_bind, bind_assoc, pure_bind, partitionTransfer, Frame.pack, bindReply, Row.run, next]
    apply bind_congr
    intro reply
    erw [freshInside (0 : Fin (tail.requests + 1)) (.pair (frame.pack values) reply)]
    simp only [ite_true, Sum.elim_inr]
    exact ih (.push (sig.reply op) frame) (bindReply values reply) (labels ∘ Fin.succ)
      (fun i packet => freshInside i.succ packet) (fun i => by
        have equation := rows i.succ
        simp only [Row.cells] at equation
        erw [Fin.cases_succ] at equation
        exact equation)

variable {source : FiniteCFG F blocks exits captures}
  (s : Shape sig outputs packets source) (emitted : Emitted s)

theorem table_chain (i : Fin (s.row.requests + 1)) :
    s.table (chainLabel s.selected s.row.requests i) = s.chain i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Shape.table, chainLabel, oldLabel]
  · simp [Shape.table, chainLabel, freshLabel]

theorem table_old (i : Fin blocks) (other : i ≠ s.selected) :
    s.table (oldLabel s.row.requests i) =
      (packets i, (source.block i).erase.renameLabels (moveExit blocks s.row.requests)) := by
  simp [Shape.table, oldLabel, other]

private theorem first_packet {newBlocks : Nat} (row : Row sig packets outputs Γ) (frame : Frame Γ)
    (old : Fin blocks → Fin newBlocks) (labels : Fin (row.requests + 1) → Fin newBlocks) :
    (row.cells old frame labels 0).1 = frame.packet := by
  cases row <;> rfl

theorem old_packet (i : Fin blocks) : (s.table (oldLabel s.row.requests i)).1 = packets i := by
  by_cases selected : i = s.selected
  · subst i
    change (s.table (chainLabel s.selected s.row.requests 0)).1 = _
    rw [table_chain]
    exact first_packet _ _ _ _
  · rw [table_old s i selected]

private theorem entry_run (instr : Primitive E F α) (env : Env α)
    (graph : FiniteCFG F blocks exits captures) (start : Fin blocks) (seed : LambdaSSA.Tm F)
    (entry : graph.entry.erase = .br start.val seed) :
    region instr env graph.erase =
      term instr env seed >>= fun packet => iter (step instr env graph) (start, packet) := by
  simp only [FiniteCFG.erase, region, entry, bind_assoc, pure_bind, local_transfer, Sum.elim_inr]
  rfl

/-- Run the same flat row with two continuations that agree on its
relocated labels. This includes malformed raw operands that diverge. -/
private theorem rename_transfer {n labels : Nat} {β : Type u}
    (instr : Primitive E F α) (env : Env α) (row : Flat F labels n)
    (rename : Nat → Nat) (before after : Transfer α → Tree E β)
    (agree : ∀ i value, after (rename i, value) = before (i, value)) :
    (region instr env (row.erase.renameLabels rename) >>= after) = (region instr env row.erase >>= before) := by
  induction row generalizing env with
  | br label arg => simp only [Flat.erase, Region.renameLabels, region, bind_assoc, pure_bind, agree]
  | let₁ arg body ih => simp only [Flat.erase, Region.renameLabels, region, bind_assoc, ih]
  | let₂ arg body ih =>
    simp only [Flat.erase, Region.renameLabels, region, bind_assoc]
    apply bind_congr
    intro value
    cases value <;> first
      | exact ih _
      | change (diverge >>= after) = (diverge >>= before); rw [diverge_bind, diverge_bind]
  | case arg left right hl hr =>
    simp only [Flat.erase, Region.renameLabels, region, bind_assoc]
    apply bind_congr
    intro value
    cases value <;> first
      | exact hl _
      | exact hr _
      | change (diverge >>= after) = (diverge >>= before); rw [diverge_bind, diverge_bind]

private def embed (count : Nat) (state : BlockInput α blocks) : BlockInput α (blocks + count) :=
  (oldLabel count state.1, state.2)

private theorem relocate_transfer (count label : Nat) (value : Value α) :
    splitTransfer (blocks + count) (moveExit blocks count label, value) =
      Sum.map id (embed count) (splitTransfer blocks (label, value)) := by
  by_cases internal : label < blocks
  · have moved : label < blocks + count := by omega
    simp [moveExit, splitTransfer, internal, moved, embed, oldLabel]
  · have moved : ¬ blocks + count + (label - blocks) < blocks + count := by omega
    simp [moveExit, splitTransfer, internal, moved]

private theorem relocated_step {n labels : Nat} (instr : Primitive E F α) (env : Env α)
    (row : Flat F labels n) (count : Nat) :
    (region instr env (row.erase.renameLabels (moveExit blocks count)) >>= fun out =>
      pure (splitTransfer (blocks + count) out)) =
    Sum.map id (embed count) <$> (region instr env row.erase >>= fun out =>
      pure (splitTransfer blocks out)) := by
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  apply rename_transfer
  intro label payload
  rw [relocate_transfer]

private theorem unchanged (instr : Primitive E F α) (env : Env α) (i : Fin blocks)
    (other : i ≠ s.selected) (packet : Value α) :
    step instr env emitted.code (embed s.row.requests (i, packet)) =
      Sum.map id (embed s.row.requests) <$> step instr env source (i, packet) := by
  unfold step
  change (region instr (extend env packet) (emitted.code.block (oldLabel s.row.requests i)).erase >>= _) = _
  rw [emitted.row_eq, table_old s i other]
  exact relocated_step instr (extend env packet) (source.block i) s.row.requests

theorem unchanged_step (instr : Primitive E F α) (env : Env α) (i : Fin blocks)
    (other : i ≠ s.selected) (packet : Value α) :
    blockStep instr emitted.code env (oldLabel s.row.requests i, packet) =
      Sum.map id (fun state => (oldLabel s.row.requests state.1, state.2)) <$>
        blockStep instr source env (i, packet) := by
  change blockStep instr emitted.code env (embed s.row.requests (i, packet)) =
    Sum.map id (embed s.row.requests) <$> blockStep instr source env (i, packet)
  simpa only [blockStep, transfer, map_eq_pure_bind, step] using unchanged s emitted instr env i other packet

private def inFresh (oldBlocks : Nat) (p : BlockInput α count) : Bool :=
  decide (oldBlocks ≤ p.1.val)

private theorem fresh_inside (i : Fin (s.row.requests)) (packet : Value α) :
    inFresh blocks (chainLabel s.selected s.row.requests i.succ, packet) = true := by
  simp [inFresh, chainLabel, freshLabel]

private theorem old_outside (count : Nat) (i : Fin blocks) (packet : Value α) :
    inFresh blocks (embed count (i, packet)) = false := by
  simp [inFresh, embed, oldLabel, Nat.not_le_of_lt i.isLt]

private theorem step_square (instr : Primitive E F α) (env : Env α) (p : BlockInput α blocks) :
    (Sum.map id (embed s.row.requests) <$> step instr env source p) =
      iter (partitionStepByTarget (step instr env emitted.code) (inFresh blocks)) (embed s.row.requests p) := by
  rcases p with ⟨i, packet⟩
  by_cases selected : i = s.selected
  · subst i
    let values : Values [packets s.selected] α := readSlots position (extend env packet)
    have original : step instr env source (s.selected, packet) = s.row.run instr values := by
      change (region instr (extend env packet) (source.block s.selected).erase >>= _) = _
      rw [s.row_eq, unsplit_step instr s.row (extend env packet) values (fun _ => rfl)]
    rw [original]
    exact (follow instr env emitted.code (inFresh blocks) (oldLabel s.row.requests)
      (old_outside s.row.requests) s.row (.entry (packets s.selected)) values (chainLabel s.selected s.row.requests)
      (fresh_inside s) (fun j => by rw [emitted.row_eq, table_chain s]; rfl)).symm
  · rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env emitted.code) (inFresh blocks)))
      (embed s.row.requests (i, packet))]
    simp only [partitionStepByTarget, unchanged s emitted instr env i selected packet,
      map_eq_pure_bind, bind_assoc, pure_bind]
    apply bind_congr
    intro out
    exact (finish_old (inFresh blocks) (oldLabel s.row.requests) (old_outside s.row.requests) _ out).symm

private theorem old_run (instr : Primitive E F α) (env : Env α) (p : BlockInput α blocks) :
    iter (step instr env source) p = iter (step instr env emitted.code) (embed s.row.requests p) := by
  let phases := partitionStepByTarget (step instr env emitted.code) (inFresh blocks)
  have simulation := iterate_uniformity (step instr env source) (iter phases) (embed s.row.requests) (by
    funext state
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind]
    exact step_square s emitted instr env state)
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, phases, iter_partition_target] using
    congrFun simulation p

theorem preserves_run (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env emitted.code.erase := by
  rw [entry_run instr env source s.entry _ s.entry_eq,
    entry_run instr env emitted.code (oldLabel s.row.requests s.entry) _ (emitted.entry_eq.trans s.entry_eq)]
  exact bind_congr fun packet => old_run s emitted instr env (s.entry, packet)

private theorem relocated_old_run (graph : FiniteCFG F (blocks + count) exits captures)
    (rows : ∀ i : Fin blocks, (graph.block (oldLabel count i)).erase =
      (source.block i).erase.renameLabels (moveExit blocks count))
    (instr : Primitive E F α) (env : Env α) (p : BlockInput α blocks) :
    iter (step instr env source) p = iter (step instr env graph) (embed count p) := by
  have simulation := iterate_uniformity (step instr env source) (step instr env graph) (embed count) (by
    funext state
    rcases state with ⟨i, packet⟩
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind]
    change Sum.map id (embed count) <$> step instr env source (i, packet) =
      (region instr (extend env packet) (graph.block (oldLabel count i)).erase >>= fun out =>
        pure (splitTransfer (blocks + count) out))
    rw [rows]
    exact (relocated_step instr (extend env packet) (source.block i) count).symm)
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using congrFun simulation p

namespace BranchEntry

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.BranchEntry
open Silmaril.Isotope.Bridge.NamedFlat.Capture (packEnv)

private theorem packed_input_tree (instr : Primitive E F α) (env : Env α) (context : List PacketType) :
    term instr env (Region.packedInputValue context) = pure (packEnv context.length env) := by
  induction context generalizing env with
  | nil => rfl
  | cons ty rest ih =>
    have older : term instr env ((Region.packedInputValue rest).rename Nat.succ) =
        term instr (env ∘ Nat.succ) (Region.packedInputValue rest) :=
      term_rename instr _ (fun _ => rfl)
    simp only [Region.packedInputValue, term, older, ih, pure_bind, List.length_cons, packEnv]

variable {context : BoundCtx PacketType captures}


theorem materialized_run (m : Materialized context source) (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env m.code.erase := by
  rw [entry_run instr env m.code (Fin.last blocks) _ m.entry_eq,
    packed_input_tree instr env context.toList, BoundCtx.length_toList, pure_bind,
    congrFun (iterate_fixpoint (step instr env m.code)) (Fin.last blocks, packEnv captures env)]
  change (region instr env source.entry.erase >>= fun out =>
    Sum.elim pure (iter (step instr env source)) (splitTransfer blocks out)) =
    ((region instr (extend env (packEnv captures env)) (m.code.block (Fin.last blocks)).erase >>= fun out =>
      pure (splitTransfer (blocks + 1) out)) >>= Sum.elim pure (iter (step instr env m.code)))
  rw [m.dispatch_eq, Silmaril.Isotope.Bridge.NamedFlat.Capture.unpack_tree instr m.written context env env, m.written_eq]
  simp only [bind_assoc, pure_bind]
  symm
  apply rename_transfer
  intro index value
  rw [relocate_transfer]
  cases splitTransfer blocks (index, value) with
  | inl out => rfl
  | inr next => exact (relocated_old_run m.code m.row_eq instr env next).symm

theorem seed_from_entry {A : Type 1} {Events : Type → Type}
    (instr : Primitive Events F A) (env : Env A)
    (seed : Silmaril.SSA.LambdaRTL.Val (Fin captures))
    (term_eq : packetTerm seed = (Region.packedInputValue context.toList : LambdaSSA.Tm F)) :
    packetValue env seed = packEnv captures env := by
  apply (Silmaril.Elgot.ITree.ret_inj (E := Events)).mp
  change (pure _ : Tree Events _) = pure _
  rw [← packet_term_tree instr env, term_eq, packed_input_tree, BoundCtx.length_toList]

theorem compiled_seed {A : Type 1} {Events : Type → Type}
    (built : Compiled sig context packets outputs source) (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.publicReadback.provenance.seed = packEnv captures env :=
  seed_from_entry instr env _ (Region.br.inj (built.publicReadback.provenance.sourceEntry.symm.trans
    (built.split.emitted.entry_eq.trans built.prepared.emitted.entry_eq))).2

end BranchEntry

namespace EffectfulEntry

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry

variable {context : BoundCtx PacketType captures} {Δ : List PacketType}

private theorem pack_scope (instr : Primitive E F α) (frame : Frame Γ) (layout : Positions Γ)
    (env : Env α) :
    term instr env (packScope frame layout) = pure (frame.pack (readSlots layout env)) := by
  induction frame with
  | entry => rfl
  | push ty prev ih =>
    simp only [packScope, term, ih, pure_bind, Frame.pack, readSlots]
    rfl

private theorem case_congr {β : Type u} (instr : Primitive E F α) (env target : Env α)
    (test test' : LambdaSSA.Tm F) (left right left' right' : Region F)
    (finish finish' : Transfer α → Tree E β) (test_eq : term instr env test = term instr target test')
    (hl : ∀ value, (region instr (extend env value) left >>= finish) =
      (region instr (extend target value) left' >>= finish'))
    (hr : ∀ value, (region instr (extend env value) right >>= finish) =
      (region instr (extend target value) right' >>= finish')) :
    (region instr env (.case test left right) >>= finish) =
      (region instr target (.case test' left' right') >>= finish') := by
  simp only [region, bind_assoc, test_eq]
  apply bind_congr
  intro value
  cases value with
  | inl payload => exact hl payload
  | inr payload => exact hr payload
  | atom _ | unit | pair _ _ => simp only [diverge_bind]

private theorem pure_path_run {β : Type u} (instr : Primitive E F α)
    (oldFinish : (Transfer α ⊕ BlockInput α blocks) → Tree E β)
    (newFinish : (Transfer α ⊕ BlockInput α (blocks + count)) → Tree E β)
    (routes : ∀ out, newFinish (Sum.map id (embed count) out) = oldFinish out)
    (tail : CaseTail packets outputs Γ) (env target : Env α) (layout : Positions Γ)
    (agree : ∀ {ty} (slot : Slot Γ ty), target (layout slot) = env (position slot)) :
    (region instr env (CaseTail.erase id position tail) >>= fun out => oldFinish (splitTransfer blocks out)) =
      (region instr target (CaseTail.erase (oldLabel count) layout tail) >>=
        fun out => newFinish (splitTransfer (blocks + count) out)) := by
  rw [case_tree instr id position env (readSlots position env) (fun _ => rfl),
    case_tree instr (oldLabel count) layout target (readSlots position env) agree]
  apply bind_congr
  intro out
  have identity : Sum.map id (fun state : BlockInput α blocks => (id state.1, state.2)) out = out := by
    cases out <;> rfl
  rw [identity]
  exact (routes out).symm

private theorem jump_to_frame {newBlocks : Nat} {β : Type u}
    (instr : Primitive E F α) (target : Env α)
    (frame : Frame Γ) (layout : Positions Γ) (values : Values Γ α)
    (agree : ∀ {ty} (slot : Slot Γ ty), target (layout slot) = values slot)
    (label : Fin newBlocks) (finish : (Transfer α ⊕ BlockInput α newBlocks) → Tree E β) :
    (region instr target (.br label.val (packScope frame layout)) >>= fun out =>
      finish (splitTransfer newBlocks out)) = finish (.inr (label, frame.pack values)) := by
  have slots : @readSlots Γ α layout target = @values := by funext ty slot; exact agree slot
  simp only [region, pack_scope, slots, pure_bind, local_transfer]

/-- The same single-leaf simulation works at any pair of suffix labels.
A request tail reaches an old label or an exit and resumes the outer run. -/
private theorem request_run (instr : Primitive E F α) (ambient : Env α)
    (graph : FiniteCFG F (blocks + count) exits captures)
    (oldFinish : (Transfer α ⊕ BlockInput α blocks) → Tree E (Transfer α))
    (routes : ∀ out,
      Sum.elim pure (iter (step instr ambient graph)) (Sum.map id (embed count) out) = oldFinish out)
    (req : Request sig packets outputs Γ) (labels : Fin 2 → Fin (blocks + count))
    (fresh : ∀ i, blocks ≤ (labels i).val)
    (rows : ∀ i, (graph.block (labels i)).erase = (req.cellsAt (oldLabel count) labels i).2)
    (env target : Env α) (layout : Positions Γ)
    (agree : ∀ {ty} (slot : Slot Γ ty), target (layout slot) = env (position slot)) :
    (region instr env req.row.erase >>= fun out => oldFinish (splitTransfer blocks out)) =
      (region instr target (.br (labels 0).val (packScope req.frame layout)) >>= fun out =>
        Sum.elim pure (iter (step instr ambient graph)) (splitTransfer (blocks + count) out)) := by
  let vals : Values Γ α := readSlots position env
  let start : BlockInput α (blocks + count) := (labels 0, req.frame.pack vals)
  let body := step instr ambient graph
  let phases := partitionStepByTarget body (inFresh blocks)
  have chain := follow instr ambient graph (inFresh blocks) (oldLabel count) (old_outside count)
    req.row req.frame vals labels (fun i packet => by simp [inFresh, fresh i.succ]) rows
  have flatten : iter body start = iter phases start >>= Sum.elim pure (iter body) := by
    rw [← iter_partition_target body (inFresh blocks)]
    exact congrFun (iterate_fixpoint (iter phases)) _
  have unsplit := unsplit_step instr req.row env vals (fun _ => rfl)
  have original :
      (region instr env req.row.erase >>= fun out => oldFinish (splitTransfer blocks out)) =
        req.row.run instr vals >>= oldFinish := by
    rw [← unsplit]
    simp only [bind_assoc, pure_bind]
  have outlined := jump_to_frame instr target req.frame layout vals agree (labels 0) (Sum.elim pure (iter body))
  change _ = iter body start at outlined
  change iter phases start = _ at chain
  rw [original, outlined, flatten, chain]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  exact bind_congr fun out => (routes out).symm

private theorem outlined_entry (m : Outlined sig context packets outputs source)
    (instr : Primitive E F α) (ambient : Env α) :
    region instr ambient source.erase = region instr ambient m.code.erase := by
  let oldFinish : (Transfer α ⊕ BlockInput α blocks) → Tree E (Transfer α) :=
    Sum.elim pure (iter (step instr ambient source))
  let newFinish : (Transfer α ⊕ BlockInput α (blocks + 2)) → Tree E (Transfer α) :=
    Sum.elim pure (iter (step instr ambient m.code))
  have routes (out : Transfer α ⊕ BlockInput α blocks) :
      newFinish (Sum.map id (embed 2) out) = oldFinish out := by
    cases out with
    | inl r => rfl
    | inr state => exact (relocated_old_run m.code m.old_eq instr ambient state).symm
  let req := m.selection.request
  have leaf (env : Env α) := request_run instr ambient m.code oldFinish routes req (freshLabel blocks)
    (fun i => by simp [freshLabel]) m.leaf_eq env env position (fun _ => rfl)
  have path_eq {Γ : List PacketType} (path : Path packets outputs m.selection.scope Γ) (env : Env α) :
      (region instr env (path.erase id req.row.erase) >>= fun out => oldFinish (splitTransfer blocks out)) =
      (region instr env (path.erase (oldLabel 2) req.jump) >>= fun out => newFinish (splitTransfer (blocks + 2) out)) := by
    induction path generalizing env with
    | here => exact leaf env
    | left test selected other ih =>
      exact case_congr instr env env _ _ _ _ _ _ _ _ rfl (fun value => ih (extend env value))
        (fun value => pure_path_run instr oldFinish newFinish routes other (extend env value) _ position (fun _ => rfl))
    | right test other selected ih =>
      exact case_congr instr env env _ _ _ _ _ _ _ _ rfl
        (fun value => pure_path_run instr oldFinish newFinish routes other (extend env value) _ position (fun _ => rfl))
        (fun value => ih (extend env value))
  change (region instr ambient source.entry.erase >>= fun out => oldFinish (splitTransfer blocks out)) =
    (region instr ambient m.code.entry.erase >>= fun out => newFinish (splitTransfer (blocks + 2) out))
  rw [m.sourceEntry, m.entry_eq]
  exact path_eq m.selection.path ambient

theorem preserves_run (m : Outlined sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env m.code.erase :=
  outlined_entry m instr env

theorem compiled_seed {A : Type 1} {Events : Type → Type}
    (built : Compiled sig context packets outputs source) (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.publicReadback.provenance.seed = Silmaril.Isotope.Bridge.NamedFlat.Capture.packEnv captures env :=
  BranchEntry.seed_from_entry instr env _
    (Region.br.inj (built.publicReadback.provenance.sourceEntry.symm.trans built.prepared.emitted.entry_eq)).2

namespace Multiple

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple
  (EntryTree)

private theorem continuation_run {β : Type u}
    (instr : Primitive E F α) (ambient : Env α) (graph : FiniteCFG F (blocks + count) exits captures)
    (finish : (Transfer α ⊕ BlockInput α (blocks + count)) → Tree E β)
    (frame : Frame Γ) (values : Values Γ α) (label : Fin (blocks + count)) (body : Region F)
    (row : (graph.block label).erase = frame.unpack 0 body)
    (unroll : finish (.inr (label, frame.pack values)) = step instr ambient graph (label, frame.pack values) >>= finish) :
    finish (.inr (label, frame.pack values)) =
      (region instr (frame.load values (extend ambient (frame.pack values))) body >>= fun out =>
        finish (splitTransfer (blocks + count) out)) := by
  simp only [unroll, step, row, bind_assoc, pure_bind]
  rw [unpack_tree instr frame values _ 0 _ rfl]

private theorem extend_agreement {ty : PacketType}
    (env target : Env α) (layout : Positions Γ)
    (agree : ∀ {τ} (slot : Slot Γ τ), target (layout slot) = env (position slot))
    (payload : Value α) {τ : PacketType} (slot : Slot (ty :: Γ) τ) :
    extend target payload (bindPosition layout slot) = extend env payload (position slot) := by
  cases slot with
  | here => rfl
  | there old => exact agree old

/-- Each fresh transfer may unfold one emitted step. The continuation
at old labels is abstract, so the same argument works for a single
partitioned visit or for the complete run of an outlined entry. -/
private theorem tree_run {β : Type u} (instr : Primitive E F α) (ambient : Env α)
    (graph : FiniteCFG F (blocks + count) exits captures)
    (oldFinish : (Transfer α ⊕ BlockInput α blocks) → Tree E β)
    (newFinish : (Transfer α ⊕ BlockInput α (blocks + count)) → Tree E β)
    (routes : ∀ out, newFinish (Sum.map id (embed count) out) = oldFinish out)
    (unroll : ∀ (label : Fin (blocks + count)) (packet : Value α), blocks ≤ label.val →
      newFinish (.inr (label, packet)) = step instr ambient graph (label, packet) >>= newFinish)
    {n : Nat} (tree : EntryTree sig packets outputs Γ n)
    (labels : Fin n → Fin (blocks + count)) (fresh : ∀ i, blocks ≤ (labels i).val)
    (rows : ∀ i, (graph.block (labels i)).erase = (tree.cells (oldLabel count) labels i).2)
    (env target : Env α) (layout : Positions Γ)
    (agree : ∀ {ty} (slot : Slot Γ ty), target (layout slot) = env (position slot)) :
    (region instr env tree.written >>= fun out => oldFinish (splitTransfer blocks out)) =
      (region instr target (tree.entryAt (oldLabel count) labels layout) >>= fun out =>
        newFinish (splitTransfer (blocks + count) out)) := by
  induction tree generalizing env target with
  | pure tail => exact pure_path_run instr oldFinish newFinish routes tail env target layout agree
  | @request Γ leaf =>
    let vals : Values Γ α := readSlots position env
    let replyFrame := Frame.push (sig.reply leaf.op) leaf.frame
    have head : (graph.block (labels 0)).erase = leaf.frame.requestCell leaf.op leaf.arg (labels 1) :=
      rows 0
    have replyRow : (graph.block (labels 1)).erase =
        replyFrame.unpack 0 (CaseTail.erase (oldLabel count) (replyFrame.position 0) leaf.tail) :=
      rows 1
    rw [EntryTree.written, EntryTree.entryAt,
      jump_to_frame instr target leaf.frame layout vals agree (labels 0) newFinish,
      unroll _ _ (fresh 0), request_cell_step instr ambient graph leaf.frame vals leaf.op leaf.arg _ _ head]
    simp only [Request.row, Row.erase, region, term, operand_tree instr position env vals leaf.arg (fun _ => rfl),
      bind_assoc, pure_bind]
    apply bind_congr
    intro reply
    let replyValues : Values (sig.reply leaf.op :: Γ) α := bindReply vals reply
    rw [continuation_run instr ambient graph newFinish replyFrame replyValues (labels 1) _ replyRow
      (unroll _ _ (fresh 1))]
    apply pure_path_run instr oldFinish newFinish routes
    intro ty slot
    rw [load_slot replyFrame replyValues _ 0 rfl]
    cases slot <;> rfl
  | @requestThen Γ n op arg frame next ih =>
    let pairLabels := fun i : Fin 2 => labels (i.castAdd n)
    let childLabels := fun i : Fin n => labels (i.natAdd 2)
    let replyFrame := Frame.push (sig.reply op) frame
    let vals : Values Γ α := readSlots position env
    have head : (graph.block (pairLabels 0)).erase = frame.requestCell op arg (pairLabels 1) := by
      simpa only [EntryTree.cells, appendTable_left, Fin.cases_zero, pairLabels] using rows ((0 : Fin 2).castAdd n)
    have replyRow : (graph.block (pairLabels 1)).erase =
        replyFrame.unpack 0 (next.entryAt (oldLabel count) childLabels (replyFrame.position 0)) := by
      simpa only [EntryTree.cells, appendTable_left, show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,
        Fin.cases_succ, pairLabels, childLabels, replyFrame] using rows ((1 : Fin 2).castAdd n)
    rw [EntryTree.written, EntryTree.entryAt,
      jump_to_frame instr target frame layout vals agree (pairLabels 0) newFinish,
      unroll _ _ (fresh _), request_cell_step instr ambient graph frame vals op arg _ _ head]
    simp only [region, term, operand_tree instr position env vals arg (fun _ => rfl), bind_assoc, pure_bind]
    apply bind_congr
    intro reply
    let replyValues : Values (sig.reply op :: Γ) α := bindReply vals reply
    rw [continuation_run instr ambient graph newFinish replyFrame replyValues (pairLabels 1) _ replyRow
      (unroll _ _ (fresh _))]
    apply ih childLabels
    · exact fun i => fresh (i.natAdd 2)
    · intro i
      simpa only [EntryTree.cells, appendTable_right, childLabels] using rows (i.natAdd 2)
    · intro ty slot
      rw [load_slot replyFrame replyValues _ 0 rfl]
      cases slot <;> rfl
  | @unpack Γ a b n value frame next ih =>
    let head := labels ((0 : Fin 1).castAdd n)
    let childLabels := fun i : Fin n => labels (i.natAdd 1)
    let vals : Values Γ α := readSlots position env
    let loaded := frame.load vals (extend ambient (frame.pack vals))
    have restored : ∀ {ty} (slot : Slot Γ ty), loaded (frame.position 0 slot) = env (position slot) :=
      load_slot frame vals _ 0 rfl
    have headRow : (graph.block head).erase = frame.unpack 0
        (.let₂ (operand (frame.position 0) value)
          (next.entryAt (oldLabel count) childLabels (bindPosition (bindPosition (frame.position 0))))) := by
      simpa only [EntryTree.cells, appendTable_left, head, childLabels] using rows ((0 : Fin 1).castAdd n)
    rw [EntryTree.written, EntryTree.entryAt,
      jump_to_frame instr target frame layout vals agree head newFinish,
      continuation_run instr ambient graph newFinish frame vals head _ headRow (unroll _ _ (fresh _))]
    have restoredValue :
        term instr (frame.load vals (extend ambient (frame.pack vals))) (operand (frame.position 0) value) =
          pure (evalOperand vals value) :=
      operand_tree instr (frame.position 0) loaded vals value restored
    simp only [region, operand_tree instr position env vals value (fun _ => rfl), restoredValue, pure_bind]
    cases evalOperand vals value with
    | pair left right =>
      apply ih childLabels
      · exact fun i => fresh (i.natAdd 1)
      · intro i
        simpa only [EntryTree.cells, appendTable_right, childLabels] using rows (i.natAdd 1)
      · exact extend_agreement _ _ _ (extend_agreement env loaded _ restored left) right
    | atom _ | unit | inl _ | inr _ => simp only [diverge_bind]
  | case test left right ihLeft ihRight =>
    simp only [EntryTree.written, EntryTree.entryAt]
    apply case_congr
    · rw [operand_tree instr position env (readSlots position env) test (fun _ => rfl),
        operand_tree instr layout target (readSlots position env) test agree]
    · intro payload
      apply ihLeft
      · exact fun i => fresh (i.castAdd _)
      · intro i
        simpa only [EntryTree.cells, appendTable_left] using rows (i.castAdd _)
      · exact extend_agreement env target layout agree payload
    · intro payload
      apply ihRight
      · exact fun i => fresh (i.natAdd _)
      · intro i
        simpa only [EntryTree.cells, appendTable_right] using rows (i.natAdd _)
      · exact extend_agreement env target layout agree payload

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple
  renaming Outlined → MultiOutlined, Compiled → MultiCompiled

theorem preserves_run (m : MultiOutlined sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env m.emitted.code.erase := by
  let oldFinish : (Transfer α ⊕ BlockInput α blocks) → Tree E (Transfer α) :=
    Sum.elim pure (iter (step instr env source))
  let newFinish : (Transfer α ⊕ BlockInput α (blocks + m.count)) → Tree E (Transfer α) :=
    Sum.elim pure (iter (step instr env m.emitted.code))
  have routes (out : Transfer α ⊕ BlockInput α blocks) :
      newFinish (Sum.map id (embed m.count) out) = oldFinish out := by
    cases out with
    | inl value => rfl
    | inr state => exact (relocated_old_run m.emitted.code m.emitted.old_eq instr env state).symm
  change (region instr env source.entry.erase >>= fun out => oldFinish (splitTransfer blocks out)) =
    (region instr env m.emitted.code.entry.erase >>= fun out => newFinish (splitTransfer (blocks + m.count) out))
  rw [m.emitted.sourceEntry, m.emitted.entry_eq]
  exact tree_run instr env m.emitted.code oldFinish newFinish routes
    (fun label packet _ => congrFun (iterate_fixpoint (step instr env m.emitted.code)) (label, packet))
    m.tree (freshLabel blocks) (fun i => by simp [freshLabel]) m.emitted.leaf_eq env env position (fun _ => rfl)

theorem compiled_seed {A : Type 1} {Events : Type → Type}
    (built : MultiCompiled sig context packets outputs source) (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.publicReadback.provenance.seed = Silmaril.Isotope.Bridge.NamedFlat.Capture.packEnv captures env :=
  BranchEntry.seed_from_entry instr env _
    (Region.br.inj (built.publicReadback.provenance.sourceEntry.symm.trans built.prepared.emitted.entry_eq)).2

namespace Computed

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed
  (Residual Operand Requests Scheduled Substitution Boundary Lifted scheduleCase scheduleCases scheduleWithBindings
    scheduleCaseWithBindings scheduleJumpWithBindings hoistWithBindings substExpr renameExpr bindSubstitution liftSubstitution hoist scheduleJump)

variable {Δ Θ : List PacketType}

private theorem residual_tree (instr : Primitive E F α) (layout : Positions Γ)
    (env : Env α) (values : Values Γ α) {ty : PacketType} (value : Residual Γ ty)
    (agree : ∀ {t} (slot : Slot Γ t), env (layout slot) = values slot) :
    term instr env (value.erase layout) = pure (value.eval values) := by
  induction value with
  | var slot => simp only [Residual.erase, term, Residual.eval, agree]
  | unit => rfl
  | pair left right ihLeft ihRight => simp only [Residual.erase, term, Residual.eval, ihLeft, ihRight, pure_bind]
  | inl value ih => simp only [Residual.erase, term, Residual.eval, ih, pure_bind]
  | inr value ih => simp only [Residual.erase, term, Residual.eval, ih, pure_bind]

/-- Compose the actual term interpretations of the scheduled let binders. -/
private def bindRequests (instr : Primitive E F α) :
    {β : Type u} → {Γ Δ : List PacketType} → Requests sig Γ Δ → Env α → (Env α → Tree E β) → Tree E β
  | _, _, _, .done, env, finish => finish env
  | _, _, _, .request op arg next, env, finish =>
    term instr env (.op op (arg.erase position)) >>= fun reply =>
      bindRequests instr next (extend env reply) finish
  | _, _, _, .unpack value next, env, finish =>
    term instr env (value.erase position) >>= fun
      | .pair left right => bindRequests instr next (extend (extend env left) right) finish
      | _ => diverge
  | _, _, _, .choose test left l right r next, env, finish =>
    (term instr env (test.erase position) >>= fun
      | .inl payload => bindRequests instr left (extend env payload) fun arm => pure (l.eval (readSlots position arm))
      | .inr payload => bindRequests instr right (extend env payload) fun arm => pure (r.eval (readSlots position arm))
      | _ => diverge) >>= fun result =>
    bindRequests instr next (extend env result) finish

private theorem bind_append {β : Type u} (instr : Primitive E F α) (env : Env α)
    (left : Requests sig Γ Δ) (right : Requests sig Δ Θ) (finish : Env α → Tree E β) :
    bindRequests instr (left.append right) env finish =
      bindRequests instr left env (fun mid => bindRequests instr right mid finish) := by
  induction left generalizing env with
  | done => rfl
  | request op arg next ih => simp only [Requests.append, bindRequests, ih]
  | unpack value next ih =>
    simp only [Requests.append, bindRequests]
    apply bind_congr
    intro result
    cases result <;> first | exact ih _ right | rfl
  | choose test left l right r rest _ _ ih =>
    simp only [Requests.append, bindRequests, ih]

/-- At every completed schedule, each older ambient slot is still
available at its shifted lexical index. -/
private theorem bind_scope_congr {β : Type u} (instr : Primitive E F α) (env : Env α)
    (requests : Requests sig Γ Δ) (left right : Env α → Tree E β)
    (equal : ∀ final, (∀ i, final (requests.shift i) = env i) → left final = right final) :
    bindRequests instr requests env left = bindRequests instr requests env right := by
  induction requests generalizing env with
  | done => exact equal env (fun _ => rfl)
  | request op arg next ih =>
    simp only [bindRequests]
    apply bind_congr
    intro reply
    apply ih
    intro final older
    exact equal final (fun i => older (i + 1))
  | unpack value next ih =>
    simp only [bindRequests]
    apply bind_congr
    intro result
    cases result with
    | pair left right =>
      apply ih
      intro final older
      exact equal final (fun i => older (i + 2))
    | atom _ | unit | inl _ | inr _ => rfl
  | choose test left l right r next _ _ ih =>
    simp only [bindRequests]
    apply bind_congr
    intro result
    apply ih
    intro final older
    exact equal final (fun i => older (i + 1))

theorem slots_position (requests : Requests sig Γ Δ) {ty : PacketType} (slot : Slot Γ ty) :
    position (requests.slots slot) = requests.shift (position slot) := by
  induction requests with
  | done => rfl
  | request op arg next ih => exact ih (.there slot)
  | unpack value next ih => exact ih (.there (.there slot))
  | choose _ _ _ _ _ next _ _ ih => exact ih (.there slot)

private theorem shift_append (left : Requests sig Γ Δ) (right : Requests sig Δ Θ) (i : Nat) :
    (left.append right).shift i = right.shift (left.shift i) := by
  induction left generalizing i <;> simp only [Requests.append, Requests.shift, *]

private theorem eval_subst (values : Substitution Γ Δ) (env target : Env α) {ty : PacketType}
    (value : Residual Γ ty)
    (agree : ∀ {t} (slot : Slot Γ t), Residual.eval (readSlots position target) (values slot) = env (position slot)) :
    Residual.eval (readSlots position target) (substExpr values value) = Residual.eval (readSlots position env) value := by
  induction value with
  | var slot => exact agree slot
  | unit => rfl
  | pair left right ihLeft ihRight => simp only [substExpr, Residual.eval, ihLeft, ihRight]
  | inl value ih | inr value ih => simp only [substExpr, Residual.eval, ih]

private theorem eval_weaken (requests : Requests sig Γ Δ) (env target : Env α) {ty : PacketType}
    (value : Residual Γ ty) (older : ∀ i, target (requests.shift i) = env i) :
    Residual.eval (readSlots position target) (renameExpr requests.slots value) =
      Residual.eval (readSlots position env) value := by
  apply eval_subst
  intro t slot
  change target (position (requests.slots slot)) = env (position slot)
  rw [slots_position, older]

private theorem eval_lift {a : PacketType} (values : Substitution Γ Δ) (env target : Env α)
    (payload : Value α)
    (agree : ∀ {t} (slot : Slot Γ t), (values slot).eval (readSlots position target) = env (position slot))
    {t : PacketType} (slot : Slot (a :: Γ) t) :
    (liftSubstitution values slot).eval (readSlots position (extend target payload)) =
      extend env payload (position slot) := by
  cases slot with
  | here => rfl
  | there old =>
    change (renameExpr (fun slot => .there slot) (values old)).eval
      (readSlots position (extend target payload)) = env (position old)
    exact (eval_subst (fun slot => .var (.there slot)) target (extend target payload)
      (values old) (fun _ => rfl)).trans (agree old)

private theorem schedule_run {β : Type u} (instr : Primitive E F α) {ty : PacketType}
    (arg : Operand sig Γ ty) (values : Substitution Γ Δ) (env target : Env α)
    (agree : ∀ {t} (slot : Slot Γ t), Residual.eval (readSlots position target) (values slot) = env (position slot))
    (finish : Value α → Tree E β) :
    let scheduled := arg.scheduleWith values
    bindRequests instr scheduled.requests target (fun final => finish (Residual.eval (readSlots position final)
      scheduled.value)) = term instr env arg.written >>= finish := by
  induction arg generalizing Δ env target β with
  | pure value =>
    simp only [Operand.scheduleWith, bindRequests, Operand.written,
      eval_subst values env target value agree, residual_tree instr position env (readSlots position env) value
        (fun _ => rfl), pure_bind]
  | @pair Γ _ _ left right ihLeft ihRight =>
    let l := left.scheduleWith values
    let r := right.scheduleWith (l.requests.weaken values)
    change bindRequests instr (l.requests.append r.requests) target
      (fun final => finish (Residual.eval (readSlots position final) (.pair (renameExpr r.requests.slots l.value) r.value))) = _
    rw [bind_append]
    calc
      _ = bindRequests instr l.requests target (fun mid =>
          term instr env right.written >>= fun y => finish (.pair (Residual.eval (readSlots position mid) l.value) y)) := by
        apply bind_scope_congr
        intro mid older
        have agreeRight {t : PacketType} (slot : Slot Γ t) :
            Residual.eval (readSlots position mid) (l.requests.weaken values slot) = env (position slot) :=
          (eval_weaken l.requests target mid (values slot) older).trans (agree slot)
        rw [← ihRight (l.requests.weaken values) env mid agreeRight
          (fun y => finish (.pair (Residual.eval (readSlots position mid) l.value) y))]
        apply bind_scope_congr
        intro final retained
        simp only [Residual.eval, eval_weaken r.requests mid final l.value retained]
        rfl
      _ = _ := by
        simpa only [Operand.written, term, bind_assoc, pure_bind] using
          ihLeft values env target agree (fun x => term instr env right.written >>= fun y => finish (.pair x y))
  | inl value ih =>
    simpa only [Operand.scheduleWith, Operand.written, Residual.eval, term, bind_assoc, pure_bind] using
      ih values env target agree (fun payload => finish (.inl payload))
  | inr value ih =>
    simpa only [Operand.scheduleWith, Operand.written, Residual.eval, term, bind_assoc, pure_bind] using
      ih values env target agree (fun payload => finish (.inr payload))
  | call op arg ih =>
    let s := arg.scheduleWith values
    change bindRequests instr (s.requests.append (.request op s.value .done)) target
      (fun final => finish (Residual.eval (readSlots position final) (.var .here))) = _
    rw [bind_append]
    calc
      _ = bindRequests instr s.requests target (fun mid =>
          instr op (Residual.eval (readSlots position mid) s.value) >>= finish) := by
        apply bind_scope_congr
        intro mid _
        simp only [bindRequests, term, residual_tree instr position mid (readSlots position mid) s.value
          (fun _ => rfl), pure_bind, Residual.eval, readSlots, position, extend_zero]
      _ = _ := by
        simpa only [Operand.written, term, bind_assoc] using
          ih values env target agree (fun value => instr op value >>= finish)
  | @let₁ Γ a _ value body ihValue ihBody =>
    let initializer := value.scheduleWith values
    let bodyValues : Substitution (a :: Γ) initializer.scope := bindSubstitution initializer.value (initializer.requests.weaken values)
    let scheduledBody := body.scheduleWith bodyValues
    change bindRequests instr (initializer.requests.append scheduledBody.requests) target
      (fun final => finish (Residual.eval (readSlots position final) scheduledBody.value)) = _
    rw [bind_append]
    calc
      _ = bindRequests instr initializer.requests target (fun mid =>
          term instr (extend env (Residual.eval (readSlots position mid) initializer.value)) body.written >>= finish) := by
        apply bind_scope_congr
        intro mid older
        apply ihBody bodyValues _ mid
        intro t slot
        cases slot with
        | here => rfl
        | there slot => exact (eval_weaken initializer.requests target mid (values slot) older).trans (agree slot)
      _ = _ := by
        simpa only [Operand.written, term, bind_assoc] using
          ihValue values env target agree (fun result => term instr (extend env result) body.written >>= finish)

  | @let₂ Γ a b _ value body ihValue ihBody =>
    let initializer := value.scheduleWith values
    let unpack : Requests sig initializer.scope (b :: a :: initializer.scope) :=
      .unpack initializer.value .done
    let initialized := initializer.requests.append unpack
    let bodyValues : Substitution (b :: a :: Γ) (b :: a :: initializer.scope) :=
      bindSubstitution (.var .here) (bindSubstitution (.var (.there .here)) (initialized.weaken values))
    let scheduledBody := body.scheduleWith bodyValues
    let finishInit : Value α → Tree E β := fun
      | .pair left right => term instr (extend (extend env left) right) body.written >>= finish
      | _ => diverge
    change bindRequests instr ((initializer.requests.append unpack).append scheduledBody.requests) target
      (fun final => finish (Residual.eval (readSlots position final) scheduledBody.value)) = _
    rw [bind_append, bind_append]
    calc
      _ = bindRequests instr initializer.requests target
          (fun mid => finishInit (Residual.eval (readSlots position mid) initializer.value)) := by
        apply bind_scope_congr
        intro mid older
        simp only [unpack, bindRequests, residual_tree instr position mid (readSlots position mid)
          initializer.value (fun _ => rfl), pure_bind, finishInit]
        cases Residual.eval (readSlots position mid) initializer.value with
        | pair left right =>
          apply ihBody bodyValues
          intro t slot
          cases slot with
          | here => rfl
          | there slot =>
            cases slot with
            | here => rfl
            | there slot =>
              apply (eval_weaken initialized target _ (values slot) ?_).trans (agree slot)
              intro i
              rw [show initialized.shift i = initializer.requests.shift i + 2 from
                shift_append initializer.requests unpack i]
              exact older i
        | atom _ | unit | inl _ | inr _ => rfl
      _ = _ := by
        rw [ihValue values env target agree finishInit]
        simp only [Operand.written, term, bind_assoc]
        apply bind_congr
        intro result
        cases result <;> simp only [finishInit, diverge_bind]

  | @case Γ a b c test left right ihTest ihLeft ihRight =>
    let tested := test.scheduleWith values
    let retained : Substitution Γ tested.scope := tested.requests.weaken values
    let l := left.scheduleWith (liftSubstitution retained)
    let r := right.scheduleWith (liftSubstitution retained)
    let finishTest : Value α → Tree E β := fun
      | .inl payload => term instr (extend env payload) left.written >>= finish
      | .inr payload => term instr (extend env payload) right.written >>= finish
      | _ => diverge
    change bindRequests instr
      (tested.requests.append (.choose tested.value l.requests l.value r.requests r.value .done)) target
      (fun final => finish (Residual.eval (readSlots position final) (.var .here))) = _
    rw [bind_append]
    calc
      _ = bindRequests instr tested.requests target
          (fun mid => finishTest (tested.value.eval (readSlots position mid))) := by
        apply bind_scope_congr
        intro mid older
        have kept {t : PacketType} (slot : Slot Γ t) :
            (retained slot).eval (readSlots position mid) = env (position slot) :=
          (eval_weaken tested.requests target mid (values slot) older).trans (agree slot)
        simp only [bindRequests, residual_tree instr position mid (readSlots position mid) tested.value
          (fun _ => rfl), pure_bind, Residual.eval, readSlots, position, extend_zero, finishTest]
        cases tested.value.eval (readSlots position mid) with
        | inl payload =>
          dsimp only
          rw [ihLeft (liftSubstitution retained) (extend env payload) (extend mid payload)
            (eval_lift retained env mid payload kept) pure, bind_pure]
        | inr payload =>
          dsimp only
          rw [ihRight (liftSubstitution retained) (extend env payload) (extend mid payload)
            (eval_lift retained env mid payload kept) pure, bind_pure]
        | atom _ | unit | pair _ _ => exact diverge_bind _
      _ = _ := by
        rw [ihTest values env target agree finishTest]
        simp only [Operand.written, term, bind_assoc]
        apply bind_congr
        intro value
        cases value <;> simp only [finishTest, diverge_bind]

private theorem term_wrap (instr : Primitive E F α) (env : Env α)
    (requests : Requests sig Γ Δ) (body : LambdaSSA.Tm F) :
    term instr env (requests.wrap LambdaSSA.Tm.let₁ LambdaSSA.Tm.let₂ body) =
      bindRequests instr requests env (fun final => term instr final body) := by
  induction requests generalizing env body with
  | done => rfl
  | request op arg next ih => simp only [Requests.wrap, term, bindRequests, ih]
  | unpack value next ih =>
    simp only [Requests.wrap, term, bindRequests]
    apply bind_congr
    intro result
    cases result <;> first | exact ih _ _ | rfl
  | choose test left l right r next ihLeft ihRight ihNext =>
    simp only [Requests.wrap, term, bindRequests, ihNext]
    congr 1
    apply bind_congr
    intro value
    cases value with
    | inl payload =>
      dsimp only
      rw [ihLeft (extend env payload) (l.erase position)]
      apply bind_scope_congr
      intro arm _
      exact residual_tree instr position arm (readSlots position arm) l (fun _ => rfl)
    | inr payload =>
      dsimp only
      rw [ihRight (extend env payload) (r.erase position)]
      apply bind_scope_congr
      intro arm _
      exact residual_tree instr position arm (readSlots position arm) r (fun _ => rfl)
    | atom _ | unit | pair _ _ => rfl

private theorem region_wrap (instr : Primitive E F α) (env : Env α)
    (requests : Requests sig Γ Δ) (body : Region F) :
    region instr env (requests.wrap Region.let₁ Region.let₂ body) =
      bindRequests instr requests env (fun final => region instr final body) := by
  induction requests generalizing env with
  | done => rfl
  | request op arg next ih => simp only [Requests.wrap, region, bindRequests, ih]
  | unpack value next ih =>
    simp only [Requests.wrap, region, bindRequests]
    apply bind_congr
    intro result
    cases result <;> first | exact ih _ | rfl
  | choose test left l right r next _ _ ihNext =>
    have selected := term_wrap instr env (.choose test left l right r .done) (.var 0)
    simp only [Requests.wrap, term, bindRequests, extend_zero, bind_pure] at selected
    simp only [Requests.wrap, region, term, bindRequests, ihNext, selected]


theorem operand_run (instr : Primitive E F α) (env : Env α) {ty : PacketType} (arg : Operand sig Γ ty) :
    term instr env arg.written = term instr env arg.schedule.term := by
  rw [Scheduled.term, term_wrap]
  calc
    _ = bindRequests instr arg.schedule.requests env (fun final =>
        pure (Residual.eval (readSlots position final) arg.schedule.value)) := by
      simpa only [Operand.schedule, Operand.scheduleAt, bind_pure] using
        (schedule_run instr arg (fun slot => .var slot) env env (fun _ => rfl) pure).symm
    _ = _ := by
      apply bind_scope_congr
      intro final _
      exact (residual_tree instr position final (readSlots position final) arg.schedule.value (fun _ => rfl)).symm

private theorem schedule_case_run (instr : Primitive E F α) (env : Env α) {a b : PacketType}
    (arg : Operand sig Γ (.coprod a b)) (left right : Region F) :
    region instr env (.case arg.written left right) = region instr env (scheduleCase arg left right) := by
  let finish : Value α → Tree E (Transfer α) := fun
    | .inl payload => region instr (extend env payload) left
    | .inr payload => region instr (extend env payload) right
    | _ => diverge
  let scheduled := arg.schedule
  rw [scheduleCase, scheduleCaseWithBindings, Scheduled.wrapRegion, region_wrap]
  calc
    _ = bindRequests instr scheduled.requests env
        (fun final => finish (Residual.eval (readSlots position final) scheduled.value)) :=
      (schedule_run instr arg (fun slot => .var slot) env env (fun _ => rfl) finish).symm
    _ = _ := by
      apply bind_scope_congr
      intro final older
      have branch (r : Region F) (payload : Value α) :
          region instr (extend env payload) r =
            region instr (extend final payload) (r.renameVars (Silmaril.DeBruijn.lift scheduled.requests.shift)) := by
        symm
        apply LambdaSSA.Semantics.Interaction.region_renameVars
        intro i
        cases i with
        | zero => rfl
        | succ i => exact older i
      simp only [region, residual_tree instr position final (readSlots position final)
        arg.schedule.value (fun _ => rfl), pure_bind, finish]
      cases Residual.eval (readSlots position final) scheduled.value with
      | inl payload => exact branch left payload
      | inr payload => exact branch right payload
      | atom _ | unit | pair _ _ => rfl

private theorem hoist_run (instr : Primitive E F α) (env : Env α) (outer : F)
    (argument : Operand sig Γ (sig.argument outer)) (tail : Region F) :
    region instr env (.let₁ (.op outer argument.written) tail) =
      region instr env (hoist outer argument tail) := by
  rw [hoist, hoistWithBindings, Scheduled.wrapRegion, region_wrap]
  let s := argument.schedule
  calc
    _ = bindRequests instr s.requests env (fun final =>
        instr outer (Residual.eval (readSlots position final) s.value) >>= fun reply =>
          region instr (extend env reply) tail) := by
      simpa only [s, Operand.schedule, Operand.scheduleAt, region, term, bind_assoc] using
        (schedule_run instr argument (fun slot => .var slot) env env (fun _ => rfl)
          (fun arg => instr outer arg >>= fun reply => region instr (extend env reply) tail)).symm
    _ = _ := by
      apply bind_scope_congr
      intro final older
      simp only [region, term, residual_tree instr position final (readSlots position final)
        argument.schedule.value (fun _ => rfl), pure_bind]
      apply bind_congr
      intro reply
      symm
      apply LambdaSSA.Semantics.Interaction.region_renameVars
      intro i
      cases i with
      | zero => rfl
      | succ i => exact older i

private theorem schedule_jump_run (instr : Primitive E F α) (env : Env α) (label : Nat)
    {ty : PacketType} (argument : Operand sig Γ ty) :
    region instr env (.br label argument.written) = region instr env (scheduleJump label argument) := by
  rw [scheduleJump, scheduleJumpWithBindings, Scheduled.wrapRegion, region_wrap]
  calc
    _ = bindRequests instr argument.schedule.requests env (fun final =>
        pure (label, Residual.eval (readSlots position final) argument.schedule.value)) := by
      simpa only [region, Operand.schedule, Operand.scheduleAt] using
        (schedule_run instr argument (fun slot => .var slot) env env (fun _ => rfl)
          (fun packet => pure (label, packet))).symm
    _ = _ := by
      apply bind_scope_congr
      intro final _
      simp only [region, residual_tree instr position final (readSlots position final)
        argument.schedule.value (fun _ => rfl), pure_bind]

private theorem schedule_with_bindings_run [DecidableEq F] (instr : Primitive E F α) (env : Env α)
    {labels : Nat} {types : Fin labels → PacketType} (Γ : List PacketType) (written : Region F)
    (prepared : Region F × Silmaril.Isotope.Bridge.NamedFlat.BindingTypes PacketType)
    (accepted : scheduleWithBindings sig types Γ written = some prepared) :
    region instr env written = region instr env prepared.1 := by
  induction written generalizing Γ env prepared with
  | br label arg =>
    simp only [scheduleWithBindings] at accepted
    split at accepted
    · obtain ⟨⟨argument, sourceEq⟩, _, rfl⟩ := Option.map_eq_some_iff.mp accepted
      change _ = region instr env (scheduleJump label argument)
      rw [sourceEq]
      exact schedule_jump_run instr env label argument
    · cases accepted
  | let₁ value tail ih =>
    cases value
    case op op argument =>
      simp only [scheduleWithBindings, Option.bind_eq_some_iff, Option.map_eq_some_iff] at accepted
      obtain ⟨⟨arg, sourceEq⟩, _, next, checked, rfl⟩ := accepted
      change _ = region instr env (hoist op arg next.1)
      rw [← hoist_run instr env op arg next.1, ← sourceEq]
      simp only [region]
      exact bind_congr fun reply => ih (extend env reply) (sig.reply op :: Γ) next checked
    all_goals
      simp only [scheduleWithBindings, Option.bind_eq_some_iff, Option.map_eq_some_iff] at accepted
      obtain ⟨⟨ty, _⟩, _, next, checked, rfl⟩ := accepted
      change _ = region instr env (.let₁ _ next.1)
      simp only [region]
      exact bind_congr fun reply => ih (extend env reply) (ty :: Γ) next checked
  | let₂ value tail ih =>
    simp only [scheduleWithBindings, Option.bind_eq_some_iff, Option.map_eq_some_iff] at accepted
    obtain ⟨⟨a, b⟩, _, next, checked, rfl⟩ := accepted
    change _ = region instr env (.let₂ _ next.1)
    simp only [region]
    apply bind_congr
    intro result
    cases result with
    | pair left right => exact ih (extend (extend env left) right) (b :: a :: Γ) next checked
    | atom _ | unit | inl _ | inr _ => rfl
  | case test left right ihLeft ihRight =>
    simp only [scheduleWithBindings, Option.bind_eq_some_iff, Option.map_eq_some_iff] at accepted
    obtain ⟨found, _, left', hl, right', hr, rfl⟩ := accepted
    change _ = region instr env (scheduleCase found.operand left'.1 right'.1)
    rw [← schedule_case_run instr env found.operand left'.1 right'.1, ← found.source_eq]
    simp only [region]
    apply bind_congr
    intro result
    cases result with
    | inl payload => exact ihLeft (extend env payload) _ left' hl
    | inr payload => exact ihRight (extend env payload) _ right' hr
    | atom _ | unit | pair _ _ => rfl
  | cfg _ _ _ _ _ => cases accepted

theorem schedule_cases_run [DecidableEq F] (instr : Primitive E F α) (env : Env α)
    {labels : Nat} {types : Fin labels → PacketType} (Γ : List PacketType) (written prepared : Region F)
    (accepted : scheduleCases sig types Γ written = some prepared) :
    region instr env written = region instr env prepared := by
  obtain ⟨result, checked, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact schedule_with_bindings_run instr env Γ written result checked

private theorem boundary_run {labels : Nat} {types : Fin labels → PacketType}
    (boundary : Boundary sig context types) (instr : Primitive E F α) (env : Env α) :
    region instr env boundary.written = region instr env boundary.lower := by
  cases boundary with
  | request outer argument tail =>
    exact hoist_run instr env outer argument tail.erase
  | jump label argument =>
    exact schedule_jump_run instr env label.val argument

theorem preserves_run (lifted : Lifted sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env lifted.code.erase := by
  simp only [Lifted.code, FiniteCFG.erase, region, lifted.source_eq, lifted.entry_eq,
    boundary_run lifted.boundary instr env]

namespace Block

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block (ScheduledTransfer)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block
  renaming Shape → BlockShape, Emitted → BlockEmitted

private noncomputable def visitFinish {newBlocks : Nat} (oldBlocks : Nat)
    (body : BlockInput α newBlocks → Tree E (Transfer α ⊕ BlockInput α newBlocks))
    (out : Transfer α ⊕ BlockInput α newBlocks) : Tree E (Transfer α ⊕ BlockInput α newBlocks) :=
  Sum.elim pure (iter (partitionStepByTarget body (inFresh oldBlocks)))
    (partitionTransfer (inFresh oldBlocks) out)

private theorem visit_unroll {newBlocks : Nat} (oldBlocks : Nat)
    (body : BlockInput α newBlocks → Tree E (Transfer α ⊕ BlockInput α newBlocks))
    (state : BlockInput α newBlocks) :
    iter (partitionStepByTarget body (inFresh oldBlocks)) state = body state >>= visitFinish oldBlocks body := by
  rw [congrFun (iterate_fixpoint (partitionStepByTarget body (inFresh oldBlocks))) state]
  simp only [partitionStepByTarget, map_eq_pure_bind, bind_assoc, pure_bind]
  rfl

private theorem outlined_visit {n : Nat} (instr : Primitive E F α) (ambient : Env α)
    (graph : FiniteCFG F (blocks + count) exits captures) (i : Fin blocks) (packet : Value α)
    (tree : EntryTree sig packets outputs [packets i] n)
    (sourceRow : region instr (extend ambient packet) (source.block i).erase =
      region instr (extend ambient packet) tree.written)
    (labels : Fin n → Fin (blocks + count)) (fresh : ∀ j, blocks ≤ (labels j).val)
    (head : (graph.block (oldLabel count i)).erase = tree.entry (oldLabel count) labels)
    (rows : ∀ j, (graph.block (labels j)).erase = (tree.cells (oldLabel count) labels j).2) :
    Sum.map id (embed count) <$> step instr ambient source (i, packet) =
      iter (partitionStepByTarget (step instr ambient graph) (inFresh blocks)) (embed count (i, packet)) := by
  let env := extend ambient packet
  let body := step instr ambient graph
  let finish := visitFinish blocks body
  rw [visit_unroll]
  change (Sum.map id (embed count) <$> (region instr env (source.block i).erase >>=
      fun out => pure (splitTransfer blocks out))) =
    ((region instr env (graph.block (oldLabel count i)).erase >>=
      fun out => pure (splitTransfer (blocks + count) out)) >>= finish)
  change region instr env (source.block i).erase = region instr env tree.written at sourceRow
  rw [sourceRow]
  simp only [head, map_eq_pure_bind, bind_assoc, pure_bind, EntryTree.entry]
  apply tree_run instr ambient graph (fun out => pure (Sum.map id (embed count) out)) finish
  · exact finish_old (inFresh blocks) (oldLabel count) (old_outside count) _
  · intro label value inside
    have freshDestination : inFresh blocks (label, value) = true := by simp [inFresh, inside]
    change Sum.elim pure (iter (partitionStepByTarget body (inFresh blocks)))
      (partitionTransfer (inFresh blocks) (.inr (label, value))) = _
    rw [partitionTransfer, freshDestination]
    exact visit_unroll blocks body (label, value)
  · exact fresh
  · exact rows
  · intro ty slot
    rfl

private theorem scheduled_visit {transfer : Region F} (instr : Primitive E F α) (ambient : Env α)
    (graph : FiniteCFG F (blocks + count) exits captures) (i : Fin blocks) (packet : Value α)
    (row : ScheduledTransfer sig packets outputs (packets i) transfer)
    (sourceRow : region instr (extend ambient packet) (source.block i).erase =
      region instr (extend ambient packet) transfer)
    (labels : Fin row.count → Fin (blocks + count)) (fresh : ∀ j, blocks ≤ (labels j).val)
    (head : (graph.block (oldLabel count i)).erase = row.tree.entry (oldLabel count) labels)
    (rows : ∀ j, (graph.block (labels j)).erase = (row.tree.cells (oldLabel count) labels j).2) :
    Sum.map id (embed count) <$> step instr ambient source (i, packet) =
      iter (partitionStepByTarget (step instr ambient graph) (inFresh blocks)) (embed count (i, packet)) := by
  refine outlined_visit instr ambient graph i packet row.tree ?_ labels fresh head rows
  let env := extend ambient packet
  calc
    _ = region instr env transfer := sourceRow
    _ = region instr env row.boundary.written := congrArg (region instr env) row.source_eq
    _ = region instr env row.boundary.lower := boundary_run row.boundary instr env
    _ = _ := congrArg (region instr env) row.tree_eq

private theorem unchanged_visit (instr : Primitive E F α) (ambient : Env α)
    (graph : FiniteCFG F (blocks + count) exits captures) (i : Fin blocks) (packet : Value α)
    (row : (graph.block (oldLabel count i)).erase =
      (source.block i).erase.renameLabels (moveExit blocks count)) :
    Sum.map id (embed count) <$> step instr ambient source (i, packet) =
      iter (partitionStepByTarget (step instr ambient graph) (inFresh blocks)) (embed count (i, packet)) := by
  have relocated : step instr ambient graph (embed count (i, packet)) =
      Sum.map id (embed count) <$> step instr ambient source (i, packet) := by
    change (region instr (extend ambient packet) (graph.block (oldLabel count i)).erase >>= _) = _
    rw [row]
    exact relocated_step instr (extend ambient packet) (source.block i) count
  rw [visit_unroll, relocated]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  exact bind_congr fun out => (finish_old (inFresh blocks) (oldLabel count) (old_outside count) _ out).symm

private theorem visit_of_square (instr : Primitive E F α) (ambient : Env α)
    (graph : FiniteCFG F (blocks + count) exits captures) (state : BlockInput α blocks)
    (square : Sum.map id (embed count) <$> step instr ambient source state =
      iter (partitionStepByTarget (step instr ambient graph) (inFresh blocks)) (embed count state)) :
    (Sum.map id (fun next => (oldLabel count next.1, next.2)) <$> blockStep instr source ambient state) =
      iter (partitionStepByTarget (blockStep instr graph ambient)
        (fun next => decide (blocks ≤ next.1.val))) (oldLabel count state.1, state.2) := by
  have steps {n : Nat} (g : FiniteCFG F n exits captures) :
      blockStep instr g ambient = step instr ambient g := by
    funext p
    simp only [blockStep, transfer, map_eq_pure_bind, step]
  rw [steps, steps]
  change (Sum.map id (embed count) <$> step instr ambient source state) =
    iter (partitionStepByTarget (step instr ambient graph) (inFresh blocks)) (embed count state)
  exact square

/-- Factor the emitted run into visits. The outer iterator handles every
transfer to an original label, independently of which row emitted it. -/
private theorem run_of_visits (instr : Primitive E F α) (ambient : Env α)
    (graph : FiniteCFG F (blocks + count) exits captures) (start : Fin blocks) (seed : LambdaSSA.Tm F)
    (sourceEntry : source.entry.erase = .br start.val seed) (emittedEntry : graph.entry.erase = source.entry.erase)
    (square : ∀ state, Sum.map id (embed count) <$> step instr ambient source state =
      iter (partitionStepByTarget (step instr ambient graph) (inFresh blocks)) (embed count state)) :
    region instr ambient source.erase = region instr ambient graph.erase := by
  rw [entry_run instr ambient source start _ sourceEntry,
    entry_run instr ambient graph (oldLabel count start) _ (emittedEntry.trans sourceEntry)]
  let phases := partitionStepByTarget (step instr ambient graph) (inFresh blocks)
  have simulation := iterate_uniformity (step instr ambient source) (iter phases) (embed count) (by
    funext state
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind]
    exact square state)
  apply bind_congr
  intro packet
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, phases, iter_partition_target, embed] using
    congrFun simulation (start, packet)

variable (s : BlockShape sig packets outputs source) (emitted : BlockEmitted s)

private theorem step_square (instr : Primitive E F α) (ambient : Env α) (state : BlockInput α blocks) :
    Sum.map id (embed s.count) <$> step instr ambient source state =
      iter (partitionStepByTarget (step instr ambient emitted.code) (inFresh blocks)) (embed s.count state) := by
  rcases state with ⟨i, packet⟩
  by_cases chosen : i = s.selected
  · subst i
    let row : ScheduledTransfer sig packets outputs (packets s.selected) (source.block s.selected).erase :=
      ⟨s.boundary, s.source_eq, s.count, s.tree, s.tree_eq⟩
    apply scheduled_visit instr ambient emitted.code s.selected packet row rfl (freshLabel blocks)
    · intro j
      simp [freshLabel]
    · rw [emitted.row_eq]
      simp [BlockShape.table, oldLabel, appendTable_left, row]
    · intro j
      rw [emitted.row_eq]
      simp [BlockShape.table, freshLabel, appendTable_right, row]
  · apply unchanged_visit instr ambient emitted.code i packet
    rw [emitted.row_eq]
    simp [BlockShape.table, oldLabel, appendTable_left, chosen]

theorem visit (instr : Primitive E F α) (ambient : Env α) (state : BlockInput α blocks) :
    (Sum.map id (fun next => (oldLabel s.count next.1, next.2)) <$> blockStep instr source ambient state) =
      iter (partitionStepByTarget (blockStep instr emitted.code ambient)
        (fun next => decide (blocks ≤ next.1.val))) (oldLabel s.count state.1, state.2) :=
  visit_of_square instr ambient emitted.code state (step_square s emitted instr ambient state)

theorem preserves_run (instr : Primitive E F α) (ambient : Env α) :
    region instr ambient source.erase = region instr ambient emitted.code.erase :=
  run_of_visits instr ambient emitted.code s.start _ s.entry_eq emitted.entry_eq (step_square s emitted instr ambient)

namespace Graph

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph
  renaming Shape → GraphShape, Emitted → GraphEmitted, Row → GraphRow

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph
  (transferOperand foldedTransfer)

private theorem transfer_operand_run (instr : Primitive E F α) (env : Env α) (written : Region F)
    (label : Nat) (arg : LambdaSSA.Tm F) (accepted : transferOperand written = some (label, arg)) :
    region instr env written = region instr env (.br label arg) := by
  induction written generalizing env label arg with
  | br target value =>
    cases accepted
    rfl
  | let₁ value tail ih =>
    simp only [transferOperand, Option.map_eq_some_iff] at accepted
    obtain ⟨⟨target, operand⟩, read, equal⟩ := accepted
    cases equal
    simp only [region, term, bind_assoc]
    exact bind_congr fun reply => ih (extend env reply) target operand read
  | let₂ value tail ih =>
    simp only [transferOperand, Option.map_eq_some_iff] at accepted
    obtain ⟨⟨target, operand⟩, read, equal⟩ := accepted
    cases equal
    simp only [region, term, bind_assoc]
    apply bind_congr
    intro reply
    cases reply with
    | pair left right => exact ih (extend (extend env left) right) target operand read
    | atom _ | unit | inl _ | inr _ => simp only [diverge_bind]
  | case _ _ _ _ _ | cfg _ _ _ _ _ => cases accepted

private theorem folded_transfer_run (instr : Primitive E F α) (env : Env α) (written transfer : Region F)
    (accepted : foldedTransfer written = some transfer) :
    region instr env written = region instr env transfer := by
  simp only [foldedTransfer, Option.map_eq_some_iff] at accepted
  obtain ⟨⟨label, arg⟩, read, rfl⟩ := accepted
  exact transfer_operand_run instr env written label arg read

variable (g : GraphShape sig packets outputs source) (result : GraphEmitted g)

theorem old_cell (i : Fin blocks) :
    g.table (oldLabel g.count i) = (packets i, (g.row i).head (g.fresh i)) := by
  simp only [GraphShape.table, oldLabel, appendTable_left]

theorem fresh_cell (i : Fin blocks) (j : Fin (g.row i).count) :
    g.table (g.fresh i j) = (g.row i).cell (g.fresh i) j := by
  simp only [GraphShape.table, GraphShape.fresh, GraphShape.count, freshLabel, appendTable_right]
  exact congrArg (fun slot : (i : Fin blocks) × Fin (g.row i).count =>
    (g.row slot.1).cell (g.fresh slot.1) slot.2) (finSigmaFinEquiv.symm_apply_apply ⟨i, j⟩)

private theorem step_square (instr : Primitive E F α) (ambient : Env α) (state : BlockInput α blocks) :
    Sum.map id (embed g.count) <$> step instr ambient source state =
      iter (partitionStepByTarget (step instr ambient result.code) (inFresh blocks)) (embed g.count state) := by
  rcases state with ⟨i, packet⟩
  have atRow (row : GraphRow sig packets outputs (packets i) (source.block i).erase)
      (labels : Fin row.count → Fin (blocks + g.count))
      (fresh : ∀ j, blocks ≤ (labels j).val)
      (head : (result.code.block (oldLabel g.count i)).erase = row.head labels)
      (cells : ∀ j, (result.code.block (labels j)).erase = (row.cell labels j).2) :
      Sum.map id (embed g.count) <$> step instr ambient source (i, packet) =
        iter (partitionStepByTarget (step instr ambient result.code) (inFresh blocks)) (embed g.count (i, packet)) := by
    cases row with
    | scheduled row origin =>
      refine scheduled_visit instr ambient result.code i packet row ?_ labels fresh head cells
      rcases origin with same | folded
      · rw [same]
      · exact folded_transfer_run instr (extend ambient packet) _ _ folded
    | outlined _ tree origin =>
      refine outlined_visit instr ambient result.code i packet tree ?_ labels fresh head cells
      rcases origin with same | scheduled
      · exact congrArg (region instr (extend ambient packet)) same
      · obtain ⟨check, accepted⟩ := scheduled
        let _ : DecidableEq F := check
        exact schedule_cases_run instr (extend ambient packet) _ _ _ accepted
    | unchanged _ _ => exact unchanged_visit instr ambient result.code i packet head
  apply atRow (g.row i) (g.fresh i)
  · intro j
    exact Fin.le_coe_natAdd blocks (finSigmaFinEquiv ⟨i, j⟩ : Fin g.count)
  · rw [result.row_eq, old_cell]
  · intro j
    rw [result.row_eq, fresh_cell]

theorem visit (instr : Primitive E F α) (ambient : Env α) (state : BlockInput α blocks) :
    (Sum.map id (fun next => (oldLabel g.count next.1, next.2)) <$> blockStep instr source ambient state) =
      iter (partitionStepByTarget (blockStep instr result.code ambient)
        (fun next => decide (blocks ≤ next.1.val))) (oldLabel g.count state.1, state.2) :=
  visit_of_square instr ambient result.code state (step_square g result instr ambient state)

theorem preserves_run (instr : Primitive E F α) (ambient : Env α) :
    region instr ambient source.erase = region instr ambient result.code.erase :=
  run_of_visits instr ambient result.code g.start _ g.entry_eq result.entry_eq (step_square g result instr ambient)

end Graph

end Block

end Computed

end Multiple

end EffectfulEntry

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix
