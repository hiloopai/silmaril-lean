module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Dispatch.Defs
import Silmaril.Semantics.Elgot.Partition.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (iter liftPure mapReturn partitionStep iter_partition iter_partition_outer)
open Silmaril.Elgot.ITree (Tree diverge iterate_fixpoint iterate_uniformity iterate_pure_loop vis_bind)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Transfer region)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category (splitPayload)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (Head ConfigurationEnumeration StateTransition)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit Packets numberedInterface requestTypes encodeValue restoreAt bitValue)
open PayloadRecognition (packetValue)
open Identity (layout Phase)
open Syntax (Payload StatePrimitives)
open Relation (ReflTransGen)

attribute [local instance] requestTypes

universe v

variable {Φ : Type} {slots : List Bool}
  (p : PacketDispatch.Profile Φ slots) (caller : Payload Bit)

local notation "g" => p.control (fun _ => false)

private def phaseAt {R : List Syntax.Ty} (q : Packet R) : Phase R := ⟨.inr q⟩

set_option backward.isDefEq.respectTransparency false in
theorem scan_head (fuel : Nat) (q : Packet (layout slots)) :
    (p.scan caller fuel q).map Prod.snd = (g).scan caller fuel q := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih =>
    rw [Profile.scan]
    erw [LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Table.scan.eq_def]
    cases step : (g).step caller q with
    | inl next =>
      simpa only [step] using ih next
    | inr head =>
      simp only [step, Option.map_some]

theorem scan_path {fuel : Nat} {q origin : Packet (layout slots)}
    {head : Head (Recognize.signature Φ) (layout slots)}
    (found : p.scan caller fuel q = some (origin, head)) :
    ReflTransGen (fun a b => (g).step caller a = .inl b) q origin ∧ (g).step caller origin = .inr head := by
  induction fuel generalizing q with
  | zero => cases found
  | succ fuel ih =>
    rw [Profile.scan] at found
    cases step : (g).step caller q with
    | inl next =>
      rw [step] at found
      obtain ⟨path, ready⟩ := ih found
      exact ⟨.head step path, ready⟩
    | inr ready =>
      rw [step] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      exact ⟨.refl, step⟩

private def silent (phase : Phase (layout slots)) : Bool :=
  match phase.down with
  | .inl _ => false
  | .inr q => ((g).step caller q).isLeft

local notation "inner" => partitionStep (p.rawStep caller) (silent p caller)

private theorem inner_silent {q next : Packet (layout slots)} (step : (g).step caller q = .inl next) :
    inner (phaseAt q) = pure (.inr (phaseAt next)) := by
  simp [partitionStep, silent, phaseAt, Profile.rawStep, step]

private theorem inner_ready {q : Packet (layout slots)} {head : Head (Recognize.signature Φ) (layout slots)}
    (step : (g).step caller q = .inr head) :
    iter inner (phaseAt q) = headBody (p.returnPacket caller q) head := by
  rw [iter_partition_outer _ _ _ (by simp [silent, phaseAt, step])]
  simp [Profile.rawStep, phaseAt, step]

private theorem inner_path {q origin : Packet (layout slots)}
    (path : ReflTransGen (fun a b => (g).step caller a = .inl b) q origin) :
    iter inner (phaseAt q) = iter inner (phaseAt origin) := by
  induction path with
  | refl => rfl
  | @tail prev next _ edge ih =>
    refine ih.trans ?_
    rw [congrFun (iterate_fixpoint inner) (phaseAt prev), inner_silent p caller edge]
    simp only [pure_bind, Sum.elim_inr]

private theorem inner_exhausted (configs : ConfigurationEnumeration (layout slots)) (q : Packet (layout slots))
    (notFound : p.scan caller configs.configs.length q = none) :
    iter inner (phaseAt q) = diverge := by
  have exhausted : (g).scan caller configs.configs.length q = none := by
    rw [← scan_head p caller, notFound]
    rfl
  obtain ⟨path, start, hops, _⟩ := (g).exhausted_replay configs caller q exhausted
  let encode (i : ULift.{1} Nat) : Phase (layout slots) := phaseAt (path i.down)
  let loop (i : ULift.{1} Nat) : Tree (Request Φ) ((Transfer Runtime ⊕ Phase (layout slots)) ⊕ ULift.{1} Nat) :=
    pure (.inr ⟨i.down + 1⟩)
  have commute : (loop >=> liftPure (Sum.map id encode)) = (liftPure encode >=> inner) := by
    funext i
    change (pure (.inr ⟨i.down + 1⟩) >>= liftPure (Sum.map id encode)) = (pure (encode i) >>= inner)
    simp only [pure_bind, liftPure, Function.comp_apply, Sum.map_inr]
    exact (inner_silent p caller (hops i.down)).symm
  have same := congrFun (iterate_uniformity loop inner encode commute) ⟨0⟩
  change iter loop ⟨0⟩ = (pure (phaseAt (path 0)) >>= iter inner) at same
  rw [pure_bind, start] at same
  exact same.symm.trans (iterate_pure_loop (fun n : ULift.{1} Nat => ⟨n.down + 1⟩) ⟨0⟩)

theorem normalize (configs : ConfigurationEnumeration (layout slots)) :
    iter (p.rawStep caller) = iter (p.normalStep configs caller) := by
  rw [← iter_partition (p.rawStep caller) (silent p caller)]
  congr 1
  funext phase
  rcases phase with ⟨result | q⟩
  · rw [iter_partition_outer _ _ _ rfl]
    rfl
  · change iter inner (phaseAt q) = p.normalStep configs caller (phaseAt q)
    cases found : p.scan caller configs.configs.length q with
    | none =>
      rw [inner_exhausted p caller configs q found]
      simp only [Profile.normalStep, phaseAt, found]
    | some pair =>
      obtain ⟨origin, head⟩ := pair
      obtain ⟨path, ready⟩ := scan_path p caller found
      rw [inner_path p caller path, inner_ready p caller ready]
      simp only [Profile.normalStep, phaseAt, found]

private theorem cast_value {A B : Syntax.Ty} (same : A = B) (value : Payload A) :
    (cast (congrArg Payload same) value).val = value.val := by
  cases same
  rfl

private theorem eval_cast {Γ : List Syntax.Ty} {A B : Syntax.Ty} (same : A = B)
    (e : Syntax.Expr Γ A) (env : Syntax.Bindings Γ) :
    (cast (congrArg (Syntax.Expr Γ) same) e).eval env =
      cast (congrArg Payload same) (e.eval env) := by
  cases same
  rfl

private theorem arm_value {Γ : List Syntax.Ty} (arm : Arm (layout slots)) (literal incoming : Bool) (env : Syntax.Bindings Γ) :
    encodeValue ULift.up ((arm.operand literal incoming).eval env).val =
      if (if arm.useLiteral then literal else incoming) then .inr .unit else .inl .unit := by
  rw [Arm.operand, eval_cast arm.typed.symm, cast_value arm.typed.symm]
  cases (if arm.useLiteral then literal else incoming) <;> rfl

open LiveBit (rawWithLiterals)
open Identity (encodePhase)

private theorem base_step (q : Packet (layout slots))
    (row : Identity.Row Φ (layout slots) ((layout slots).get q.1))
    (isRow : p q.1 = .base row) :
    p.rawStep caller (phaseAt q) = row.step caller q.2 := by
  simp only [Profile.rawStep, phaseAt, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Table.step, Profile.control]
  erw [isRow]
  cases row with
  | jump target same =>
    simp only [Row.control, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Row.step, Identity.Row.step, Identity.jumpPacket]
    erw [eval_cast same.symm]
    rfl
  | ret tag bit typed fs =>
    simp only [Row.control, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Row.step, Identity.Row.guarded, Identity.Row.step, Identity.activeStep]
    change headBody (p.returnPacket caller q) (.exit tag false) = _
    simp only [headBody, Profile.returnPacket, isRow]
  | request op typed routes =>
    simp only [Row.control, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Row.step, Identity.Row.guarded, Identity.Row.step, Identity.activeStep]
    change headBody (p.returnPacket caller q) (.request op _ _) = _
    simp only [headBody]
    erw [eval_cast typed]
    rfl

private theorem case_eval {A : Syntax.Ty} (literals : Φ → Option Bool)
    {K : Type 1} (names : Fin ((layout slots).length + 2) ≃ K) (env : Env Runtime)
    (typed : A = Bit) (packet : Payload A) (opcode : Φ) (literal : Bool)
    (agrees : literals opcode = some literal) (left right : Arm (layout slots)) :
    (match splitPayload (cast (congrArg Payload typed) packet) with
     | .inl _ => pure (names (left.target.castAdd 2),
         .pair (if (if left.useLiteral then literal else false) then .inr .unit else .inl .unit) .unit)
     | .inr _ => pure (names (right.target.castAdd 2),
         .pair (if (if right.useLiteral then literal else true) then .inr .unit else .inl .unit) .unit)) =
    (region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up packet.val) .unit))
      (Row.code (.bitCase typed opcode literal left right : Row Φ (layout slots) A)).erase >>= liftPure (restoreAt names)) := by
  subst A
  rcases packet with ⟨value, typed⟩
  cases typed with
  | inl t =>
    cases t
    cases literal <;> cases h : left.useLiteral <;> simp [Row.code, Arm.code, Flat.erase, Morphism.CaseSSA.erase, region,
      LambdaSSA.Semantics.Interaction.term, pure_bind, liftPure, Identity.restore_block, splitPayload, encodeValue, h, rawWithLiterals, agrees, bitValue]
  | inr t =>
    cases t
    cases literal <;> cases h : right.useLiteral <;> simp [Row.code, Arm.code, Flat.erase, Morphism.CaseSSA.erase, region,
      LambdaSSA.Semantics.Interaction.term, pure_bind, liftPure, Identity.restore_block, splitPayload, encodeValue, h, rawWithLiterals, agrees, bitValue]

section Named

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ}
  {seed first second : V} {names : Fin ((layout slots).length + 2) ≃ K} {source : CFG V K P.Instr}
  {literals : P.Instr → Option Bool}
  (ck : PacketDispatch.Checked (P := P) (slots := slots) (seed := seed) (first := first) (second := second)
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
  simp only [PacketDispatch.Profile.expected, Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, pure_bind, phaseAt, encodePhase]
  exact congrArg pure (Identity.restore_block names 0 (.pair (encodeValue ULift.up entry.val) .unit))

private theorem step_eval (phase : Phase (layout slots)) :
    (ck.profile.rawStep entry phase >>= liftPure (Sum.map id (encodePhase names))) =
      mapReturn (CFG.Cyclic.stepSSA (treeModel instr) ck.admitted.versioned.source.blocks store)
        (liftPure out) (encodePhase names phase) := by
  rcases phase with ⟨result | ⟨i, packet⟩⟩
  · simp only [Profile.rawStep, pure_bind, liftPure, Function.comp_apply, Sum.map_inl, id_eq]
    exact (ck.readback.exit_eval instr store (packetValue result) result.1).symm
  · let env : Env Runtime := fun _ => .unit
    change _ = mapReturn (CFG.Cyclic.stepSSA (treeModel instr) ck.admitted.versioned.source.blocks store)
      (liftPure out) (names (i.castAdd 2), Value.pair (encodeValue ULift.up packet.val) .unit)
    unfold mapReturn
    rw [ck.readback.block_eval instr store env]
    simp only [PacketDispatch.Profile.expected, bind_assoc, pure_bind, Sum.elim_inr, Function.comp_apply]
    cases row : ck.profile i with
    | base base =>
      rw [show ck.profile.rawStep entry ⟨.inr ⟨i, packet⟩⟩ = _ from base_step ck.profile entry ⟨i, packet⟩ base row]
      exact Identity.row_replay names i base literals (by simpa [row, Row.Agrees] using ck.literals_agree i)
        entry packet env
    | bitCase typed opcode literal left right =>
      have agrees : literals opcode = some literal := by
        simpa [row, Row.Agrees] using ck.literals_agree i
      have run := case_eval literals names env typed packet opcode literal agrees left right
      change (ck.profile.rawStep entry ⟨.inr ⟨i, packet⟩⟩ >>= _) =
        (region instr (extend env (.pair (encodeValue ULift.up packet.val) .unit))
          (Row.bitCase typed opcode literal left right : Row P.Instr (layout slots) _).code.erase >>= _)
      have steps : (ck.profile.control (fun _ => false)).step entry ⟨i, packet⟩ =
          match splitPayload (cast (congrArg Payload typed) packet) with
          | .inl a => .inl ⟨left.target, (left.operand literal false).eval (((Syntax.emptyBindings.push entry).push packet).push a)⟩
          | .inr b => .inl ⟨right.target, (right.operand literal true).eval (((Syntax.emptyBindings.push entry).push packet).push b)⟩ := by
        change (ck.profile i).control.step (fun _ => false) ((Syntax.emptyBindings.push entry).push packet) = _
        rw [row]
        simp only [Row.control, LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Row.step]
        erw [eval_cast typed]
        simp only [Syntax.Expr.eval, Syntax.Bindings.push, Fin.cases_zero]
        cases splitPayload (cast (congrArg Payload typed) packet) <;> rfl
      have evaluated := congrArg (fun t : Tree (Request P.Instr) (K × Value Runtime) =>
        t >>= fun x => pure (Sum.inr (α := Transfer Runtime) x)) run
      rw [bind_assoc] at evaluated
      simp only [liftPure, Function.comp_apply, pure_bind] at evaluated
      rw [← evaluated]
      simp only [Profile.rawStep]
      erw [steps]
      cases splitPayload (cast (congrArg Payload typed) packet) <;>
        simp only [pure_bind, liftPure, Function.comp_apply, Sum.map_inr, encodePhase, arm_value]

theorem named_tree (configs : ConfigurationEnumeration (layout slots))
    (seedValue : input seed = encodeValue ULift.up entry.val) :
    LiveOut.observeRaw instr (I).exits (fun _ => [first, second]) source input =
      ck.profile.tree configs entry ⟨0, entry⟩ :=
  (Guarded.observe_eq_of_steps (a := ck.admitted) (input := store) (phaseAt (⟨0, entry⟩ : Packet (layout slots)))
    (ck.profile.rawStep entry) (encodePhase names) (entry_eval ck input entry seedValue)
    (step_eval ck input entry)).trans (congrFun (normalize ck.profile entry configs) _)

end Named

open Silmaril.Elgot.ITree (ret vis out_ret out_vis out_diverge diverge_bind)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration (close_branch close_terminal)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (pack unpack)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (denote_exitContinuation)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)

theorem tree_root (configs : ConfigurationEnumeration (layout slots)) (q : Packet (layout slots)) :
    p.tree configs caller q =
      match p.scan caller configs.configs.length q with
      | none => diverge
      | some (origin, .exit tag _) => ret (packedReturn (p.returnPacket caller origin tag))
      | some (_, .diverge) => diverge
      | some (_, .request f arg next) =>
        vis (.call f arg) (fun r => p.tree configs caller (next r.1 r.2)) := by
  cases found : p.scan caller configs.configs.length q with
  | none =>
    unfold Profile.tree
    rw [congrFun (iterate_fixpoint (p.normalStep configs caller))]
    simp only [Profile.normalStep, found, diverge_bind]
  | some pair =>
    obtain ⟨origin, head⟩ := pair
    unfold Profile.tree
    rw [congrFun (iterate_fixpoint (p.normalStep configs caller)) ⟨.inr q⟩]
    simp only [Profile.normalStep, found]
    cases head with
    | exit tag marked =>
      simp only [headBody, pure_bind, Sum.elim_inr]
      rw [congrFun (iterate_fixpoint (p.normalStep configs caller))]
      simp only [Profile.normalStep, pure_bind, Sum.elim_inl]
      rfl
    | diverge => simp only [headBody, diverge_bind]
    | request f arg next =>
      simp only [headBody, query, vis_bind, pure_bind, Sum.elim_inr]

private theorem decorate_return {σ : Type v} (prim : StatePrimitives Φ σ) (selected : Tag → Bool)
    (a : Packet Outputs) (s : σ) :
    decorateOn prim selected (WithTop.some {Outcome.ret a.1 a.2.val s}) PayloadType =
      if selected a.1 then ⊤ else WithTop.some {Outcome.ret a.1 a.2.val s} := by
  simp only [decorateOn, denote_exitContinuation]
  cases h : selected a.1 <;> simp [h, Behaviour.bind, Behaviour.possible]
  ext o
  cases o <;> simp [Outcome.bind, h]

theorem observe_step (configs : ConfigurationEnumeration (layout slots)) (q : Packet (layout slots))
    {σ : Type v} (prim : StatePrimitives Φ σ) (s : σ) (selected : Tag → Bool) :
    p.observeAt configs caller q prim s selected =
      match p.scan caller configs.configs.length q with
      | none => WithTop.some {Outcome.diverge}
      | some (origin, .exit tag _) =>
        if selected tag then ⊤ else WithTop.some {Outcome.ret tag (p.returnPacket caller origin tag).2.val s}
      | some (_, .diverge) => WithTop.some {Outcome.diverge}
      | some (_, .request f arg next) =>
        match prim f arg s with
        | .ret a t => let r := unpack a; p.observeAt configs caller (next r.1 r.2) prim t selected
        | .fault t => WithTop.some {Outcome.fault t}
        | .diverge => WithTop.some {Outcome.diverge} := by
  unfold Profile.observeAt
  rw [tree_root p caller configs q]
  have stop (tree : RunTree Φ) (o : Outcome Exits.length (RunTree Φ) σ)
      (row : treeStepOn prim tree s (constructorDecoder PayloadType) = terminalOn o) :
      observeOn prim tree s (constructorDecoder PayloadType) = WithTop.some {projectOn o} := by
    rw [observeOn]
    have terminal : feedbackOn prim (constructorDecoder PayloadType) (.block 0 (.atom tree) s) =
        WithTop.some {Feedback.external Loop Exits o} := row
    rw [close_terminal terminal]
    simp
  have div : decorateOn prim selected
      (observeOn prim diverge s (constructorDecoder PayloadType)) PayloadType =
        WithTop.some {Outcome.diverge} := by
    rw [stop _ .diverge (by simp [treeStepOn])]
    simp [decorateOn, projectOn, Behaviour.bind, Behaviour.possible]
    ext o
    cases o <;> simp [Outcome.bind]
  cases found : p.scan caller configs.configs.length q with
  | none => exact div
  | some pair =>
    obtain ⟨origin, head⟩ := pair
    cases head with
    | diverge => exact div
    | exit tag marked =>
      let a := p.returnPacket caller origin tag
      have row : treeStepOn prim (ret (packedReturn a)) s (constructorDecoder PayloadType) =
          terminalOn (.ret a.1 (encodeValue (fun _ => diverge) a.2.val) s) := by
        simp only [treeStepOn, out_ret, Part.some_dom, ↓reduceDIte, Part.get_some, constructorDecoder_return]
      rw [stop _ _ row]
      change decorateOn prim selected
          (WithTop.some {Outcome.ret a.1 (encodeValue (fun _ => ()) (encodeValue (fun _ => diverge) a.2.val)) s}) _ = _
      rw [lower_lift, decorate_return]
      have tag_eq : a.1 = tag := by
        unfold a Profile.returnPacket
        cases p origin.1 <;> rfl
      exact congrArg (fun i => if selected i then ⊤ else WithTop.some {Outcome.ret i a.2.val s}) tag_eq
    | request f arg next =>
      let k (r : Packet Packets) := p.tree configs caller (next r.1 r.2)
      have row : treeStepOn prim (vis (.call f arg) k) s (constructorDecoder PayloadType) =
        match prim f arg s with
        | .ret a t => WithTop.some {Outcome.ret (Feedback.internal Loop Exits 0) (.atom (k (unpack a))) t}
        | .fault t => terminalOn (.fault t)
        | .diverge => terminalOn .diverge := by
        simp only [treeStepOn, out_vis, Part.some_dom, ↓reduceDIte, Part.get_some]
        cases prim f arg s <;> rfl
      cases h : prim f arg s with
      | ret a t =>
        rw [h] at row
        unfold observeOn
        have branch : feedbackOn prim (constructorDecoder PayloadType) (.block 0 (.atom (vis (.call f arg) k)) s) =
            WithTop.some {Outcome.ret (Feedback.internal Loop Exits 0) (.atom (k (unpack a))) t} := row
        rw [close_branch branch]
        simp only [h, k]
      | fault t =>
        rw [h] at row
        rw [stop _ (.fault t) row]
        simp only [h]
        simp [decorateOn, projectOn, Behaviour.bind, Behaviour.possible]
        ext o
        cases o <;> simp [Outcome.bind]
      | diverge =>
        rw [h] at row
        rw [stop _ .diverge row]
        simp only [h]
        simp [decorateOn, projectOn, Behaviour.bind, Behaviour.possible]
        ext o
        cases o <;> simp [Outcome.bind]

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch
