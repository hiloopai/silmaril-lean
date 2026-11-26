module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Identity.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Dispatch.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Thms
import Mathlib.Tactic.FinCases
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Recognize.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Reachable.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Thms

/-! # A named request changes its loop packet before taking an ordered exit -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests

open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree vis vis_bind iterate_fixpoint HasTrace out_ret hasTrace_vis_exchange_iff)
open Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet pack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table ReplyEnumeration ConfigurationEnumeration)

private inductive Op where | poll | flip | literal (bit : Bool)
  deriving DecidableEq

private inductive Reg : Type 1 where
  | seed | arg | alt | again | rest | left | tail | right | impossible
  deriving DecidableEq

private inductive Label : Type 1 where
  | loop | left | right | first | second
  deriving DecidableEq

private abbrev Bit := Recognize.Bit
private abbrev Packets := Recognize.Packets
private abbrev Replies := Packets

attribute [local instance] Recognize.requestTypes

private abbrev nativeSig := Recognize.signature Op

private abbrev SortName := ULift.{1} Empty
private abbrev bit : Ty SortName := .coprod .unit .unit
private instance : HasTy Op (Ty SortName) :=
  ⟨(fun
    | .poll | .flip => bit
    | .literal _ => .unit), fun
    | .poll => LambdaSSA.Region.packedExitType [bit, .unit, .unit]
    | .flip | .literal _ => bit⟩
private instance : HasEff Op Bool := ⟨fun
  | .poll | .flip => true
  | .literal _ => false⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName := { Instr := Op }
private instance : DecidableEq signature.Instr := inferInstanceAs (DecidableEq Op)

private def labels : Fin 5 ≃ Label where
  toFun i := if i = 0 then .loop else if i = 1 then .left else if i = 2 then .right
    else if i = 3 then .first else .second
  invFun
    | .loop => 0
    | .left => 1
    | .right => 2
    | .first => 3
    | .second => 4
  left_inv := by decide +kernel
  right_inv := by intro label; cases label <;> rfl

private def ports : Interface SortName Reg Label := Recognize.interface .seed labels

private def fields (_ : Label) : List (Reg × Ty SortName) := []
private def loopReg (alternate : Bool) : Reg := if alternate then .alt else .arg

/-- The final arm is required by the named sum syntax. Its empty payload
can never be supplied by the shared typed request. -/
private def source (alternate : Bool) (reroute prequery : Bool := false) : CFG Reg Label signature.Instr :=
  let param := loopReg alternate
  let poll : CFG.Body Reg Label signature.Instr := .term (.case (.app .poll (.var param))
    .again (.br .loop (.var .again))
    .rest (.case (.val (.var .rest))
      .left (.br (if reroute then .right else .left) (.var .left))
      .tail (.case (.val (.var .tail))
        .right (.br .right (.var .right)) .impossible (.br .right .unit))))
  let body := if prequery then .let1 param (.app .flip (.var param)) poll else poll
  ⟨.term (.br .loop (.var .seed)),
    [(.loop, ⟨param, body⟩),
     (.left, ⟨.arg, .term (.br .first .unit)⟩),
     (.right, ⟨.arg, .term (.br .second .unit)⟩)]⟩

private def arguments (i : Fin 3) : Ty SortName := if i = 0 then bit else .unit
private def admitNamed (alternate : Bool) (reroute prequery : Bool := false) :=
  PacketLocal.admit (P := signature) ports fields (source alternate reroute prequery) arguments

private def admitted (alternate : Bool) (reroute prequery : Bool := false) :
    Admission signature ports fields (source alternate reroute prequery) :=
  (admitNamed alternate reroute prequery).get
    (by cases alternate <;> cases reroute <;> cases prequery <;> decide +kernel)

private def leftBit : Syntax.Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def rightBit : Syntax.Payload Bit := ⟨.inr .unit, .inr .unit⟩
private def unitPacket : Syntax.Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩

private inductive Event : Type → Type where
  | poll (arg : Bool) : Event (Packet Replies)

private abbrev Runtime := ULift.{1} Unit

universe u

private def isRight {A : Type u} : Value A → Bool
  | .inr _ => true
  | _ => false

private def query : Query nativeSig Event :=
  fun _ p => vis (.poll (isRight p.val)) fun reply => pure ⟨reply⟩

private def raw : Primitive Event signature.Instr Runtime :=
  fun
    | .poll, x => vis (.poll (isRight x)) fun reply => pure (Recognize.replyValue ULift.up reply)
    | .flip, x => pure (if isRight x then .inl .unit else .inr .unit)
    | .literal b, _ => pure (Recognize.bitValue b)

private def input (x : Syntax.Payload Bit) : Reg × Nat → Value Runtime :=
  fun reg => if reg = (.seed, 0) then Recognize.encodeValue ULift.up x.val else .unit

-- The compiled entry really sends the extra unit field. The native entry
-- forwards its caller directly, so this is an encoding equation.
example : (admitted false).versioned.table.code.entry =
    .br ⟨0, by decide +kernel⟩ (.pair (.bv ⟨0, by decide⟩) .unit) := rfl

-- The named compiler installs a leading product decoder before the query.
example : (admitted false).versioned.table.code.block ⟨0, by decide +kernel⟩ =
    .let₂ (.bv 0) (.case (.op .poll (.bv 1))
      (.br ⟨0, by decide +kernel⟩ (.pair (.bv 0) .unit))
      (.case (.bv 0)
        (.br ⟨1, by decide +kernel⟩ (.pair (.bv 0) .unit))
        (.case (.bv 0)
          (.br ⟨2, by decide +kernel⟩ (.pair (.bv 0) .unit))
          (.br ⟨2, by decide +kernel⟩ (.pair .unit .unit))))) := rfl

private theorem agrees : Recognize.QueryAgreement (P := signature) .poll ULift.up query raw := by
  intro argument
  have key : isRight (Recognize.encodeValue ULift.up argument.val : Value Runtime) = isRight argument.val := by
    cases argument.val <;> rfl
  simp only [raw, query, key, vis_bind, pure_bind]

private def adapter (alternate : Bool) (caller : Syntax.Payload Bit) (reroute prequery : Bool := false) :=
  Recognize.recognizeAdapter (seed := Reg.seed) (names := labels) (admitted alternate reroute prequery)
    .poll ULift.up query raw (input caller) agrees caller rfl

private theorem recognized (alternate reroute : Bool) :
    (Recognize.recognize (seed := Reg.seed) (names := labels) (admitted alternate reroute) .poll).isSome = true := by
  cases alternate <;> cases reroute <;> decide +kernel

private def checkedAdapter (alternate : Bool) (caller : Syntax.Payload Bit) (reroute : Bool := false) :=
  (adapter alternate caller reroute).get (by
    unfold adapter Recognize.recognizeAdapter
    rw [Option.isSome_map]
    exact recognized alternate reroute)

private abbrev nativeRoutes := (checkedAdapter false leftBit).1
private abbrev native := Recognize.guardedTable Op.poll nativeRoutes
private abbrev rerouted := Recognize.guardedTable Op.poll (checkedAdapter false leftBit true).1

private def firstUnitDestination (table : Table nativeSig Packets) : Option Nat :=
  match table.row 0 with
  | .request _ _ next _ => some (next 1).val
  | .exit .. | .diverge => none

-- The guarded heads use the destinations extracted from the compiled row.
example : firstUnitDestination native = some 1 ∧ firstUnitDestination rerouted = some 2 :=
  ⟨rfl, rfl⟩

example : native ≠ rerouted := fun eq => (by decide : some (1 : Nat) ≠ some 2)
  (congrArg firstUnitDestination eq)

-- A separate primitive before the poll changes the query bit. The named
-- compiler accepts it, but this recognizer requires the exact request row.
example : (admitNamed false false true).isSome = true := by decide +kernel

example : (adapter false leftBit false true).isNone = true := by decide +kernel

private def packets : List (Packet Packets) :=
  [⟨0, leftBit⟩, ⟨0, rightBit⟩, ⟨1, unitPacket⟩, ⟨2, unitPacket⟩]

private theorem packets_complete (packet : Packet Packets) : packet ∈ packets := by
  obtain ⟨i, value, typed⟩ := packet
  fin_cases i
  · cases typed with
    | inl typed => cases typed; exact List.Mem.head _
    | inr typed => cases typed; exact List.Mem.tail _ (List.Mem.head _)
  · cases typed
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · cases typed
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private def replies : ReplyEnumeration nativeSig := ⟨fun _ => packets, fun _ => packets_complete⟩
private def inventory : ConfigurationEnumeration Packets := ⟨packets, packets_complete⟩
private def diagonal : List (Packet Packets × Packet Packets) := packets.map fun p => (p, p)

private noncomputable def observation (alternate : Bool) (reroute : Bool := false) :=
  LiveOut.observeRaw raw ports.exits (fun k => (fields k).map Prod.fst) (source alternate reroute)
    (fun reg => input leftBit (reg, 0))

example : observation false = observation true :=
  observe_eq_of_checkProduct ((checkedAdapter false leftBit).2) ((checkedAdapter true leftBit).2)
    replies diagonal (by decide +kernel) (fun _ => rfl)

example : (match native.searchProduct native leftBit leftBit replies inventory inventory with
    | .accepted _ => true
    | .mismatch .. => false) = true := by decide +kernel

example : observation false = observation true := by
  obtain ⟨pairs, accepted⟩ := (native.searchProduct_accepts_iff native leftBit leftBit replies inventory
    inventory).mpr ⟨diagonal, by decide +kernel⟩
  exact observe_eq_of_searchProduct ((checkedAdapter false leftBit).2) ((checkedAdapter true leftBit).2)
    replies inventory inventory pairs accepted (fun _ => rfl)

private theorem observe_routes (reroute : Bool) : observation false reroute =
    iter (step (Recognize.guardedTable Op.poll (checkedAdapter false leftBit reroute).1)
      leftBit query (unitExit (α := Runtime))) (atBlock ⟨0, leftBit⟩) :=
  (checkedAdapter false leftBit reroute).2.observe_eq

-- The derived adapter computes the actual rerouted named runner.
example : observation false true =
    iter (step rerouted leftBit query (unitExit (α := Runtime))) (atBlock ⟨0, leftBit⟩) :=
  observe_routes true

-- Shared reply tag one reaches different ordinary ordered exits.
example : (match native.searchProduct rerouted leftBit leftBit replies inventory inventory with
    | .accepted _ => none
    | .mismatch pair path => some (pair.1.1.val, pair.2.1.val, path.map fun edge => edge.1.2.1.val)) =
    some (1, 2, [0, 1]) := by decide +kernel

private def runStep := step native leftBit query (unitExit (α := Runtime))

private theorem native_reply (reply : Packet Packets) :
    (⟨nativeRoutes.destination reply.1,
      cast (congrArg Syntax.Payload (nativeRoutes.packet reply.1).symm) reply.2⟩ : Packet Packets) = reply := by
  obtain ⟨i, payload⟩ := reply
  fin_cases i <;> rfl

private theorem runsPoll (x : Syntax.Payload Bit) :
    iter runStep (atBlock ⟨0, x⟩) =
      vis (.poll (isRight x.val)) (fun reply => iter runStep (atBlock reply)) := by
  rw [congrFun (iterate_fixpoint runStep) (atBlock ⟨0, x⟩)]
  change ((query .poll x >>= fun p => pure (Sum.inr (atBlock (R := Packets)
    ⟨nativeRoutes.destination p.down.1,
      cast (congrArg Syntax.Payload (nativeRoutes.packet p.down.1).symm) p.down.2⟩)
    : Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  simp only [native_reply, query, vis_bind, pure_bind, Sum.elim_inr]

private theorem runsRight :
    iter runStep (atBlock ⟨2, unitPacket⟩) = pure (unitExit 1) := by
  rw [congrFun (iterate_fixpoint runStep) (atBlock ⟨2, unitPacket⟩)]
  change ((pure (.inr (atExit (R := Packets) 1)) : Tree Event (Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  rw [pure_bind]
  change iter runStep (atExit 1) = _
  rw [congrFun (iterate_fixpoint runStep) (atExit 1)]
  change ((pure (.inl (unitExit 1)) : Tree Event (Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  rw [pure_bind]
  rfl

-- Reply tag zero changes the loop argument from left to right. Reply tag
-- two then leaves at the second ordered exit.
example : HasTrace (observation false)
    (.exchange (.poll false) ⟨0, rightBit⟩
      (.exchange (.poll true) ⟨2, unitPacket⟩ (.result (unitExit 1)))) := by
  rw [observe_routes false]
  change HasTrace (iter runStep (atBlock ⟨0, leftBit⟩)) _
  rw [runsPoll]
  apply (hasTrace_vis_exchange_iff _ _ _ _).mpr
  rw [runsPoll]
  apply (hasTrace_vis_exchange_iff _ _ _ _).mpr
  rw [runsRight]
  exact out_ret _

section FixedCarrier

open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag resultBehaviour result_order)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)

private def checkedReadback (reroute : Bool) :=
  (Recognize.recognize (seed := Reg.seed) (names := labels) (admitted false reroute) .poll).get
    (recognized false reroute)

private abbrev inferred (reroute : Bool) := Recognize.guardedTable Op.poll (checkedReadback reroute).routes

private theorem nativeValid (reroute : Bool) : (inferred reroute).checkNative (inferred reroute).native = true := by
  cases reroute <;> decide +kernel

private def states : StateInventory 2 := ⟨List.finRange 2, List.mem_finRange⟩

/-- Change the packet and machine state before returning reply tag one. -/
private def rerouteInterpreter : Syntax.Primitives Op 2 :=
  InterpreterScript.interpret [
    InterpreterScript.Row.success (S := nativeSig) ⟨.poll, leftBit, 0⟩ ⟨0, rightBit⟩ 1,
    InterpreterScript.Row.success (S := nativeSig) ⟨.poll, rightBit, 1⟩ ⟨1, unitPacket⟩ 1]

private noncomputable def named (reroute : Bool) (prim : Syntax.Primitives Op 2)
    (selected : Tag → Bool := fun _ => false) :=
  FixedCarrier.observeNamed (source false reroute) labels (fun reg => input leftBit (reg, 0)) prim 0 selected

private theorem named_classifies (reroute : Bool) (prim : Syntax.Primitives Op 2)
    (selected : Tag → Bool := fun _ => false) :
    named reroute prim selected =
      resultBehaviour ((FixedCarrier.withSelectedExits Op.poll (checkedReadback reroute).routes selected).runFinite
        leftBit prim inventory states ⟨0, leftBit⟩ 0) :=
  FixedCarrier.observeNamed_runFinite (checkedReadback reroute) leftBit _ rfl prim inventory states 0 selected

example : named false rerouteInterpreter = resultBehaviour (.ret 0 1) := by
  rw [named_classifies]
  rfl

example : named true rerouteInterpreter = resultBehaviour (.ret 1 1) := by
  rw [named_classifies]
  rfl

private theorem rerouteWitness : ¬ named false rerouteInterpreter ≤ named true rerouteInterpreter := by
  rw [named_classifies false, named_classifies true, result_order]
  change ¬ (Result.ret (0 : Fin 2) (1 : Fin 2)).refines (.ret 1 1)
  decide

-- Both exact native readbacks pass. The verdict uses a typed, total
-- deterministic interpreter at the original named endpoints.
example : (inferred false).checkAllInterpreters? (inferred true)
    (inferred false).native (inferred true).native leftBit leftBit replies inventory inventory states = some false := by
  apply (FixedCarrier.rejection_iff (checkedReadback false) (checkedReadback true) leftBit (fun reg => input leftBit (reg, 0)) rfl
    replies inventory states _ _ (nativeValid false) (nativeValid true)).mpr
  exact ⟨rerouteInterpreter, 0, rerouteWitness⟩

private def selectedExit (i : Tag) : Bool := i == 1

private abbrev decorated (reroute : Bool) :=
  FixedCarrier.withSelectedExits Op.poll (checkedReadback reroute).routes selectedExit

private theorem originalSelected : named false rerouteInterpreter selectedExit = resultBehaviour (.ret 0 1) := by
  rw [named_classifies false _ selectedExit]
  rfl

private theorem reroutedSelected : named true rerouteInterpreter selectedExit = ⊤ := by
  rw [named_classifies true _ selectedExit]
  rfl

private def selectedPairs : List (Packet Packets × Packet Packets) :=
  (⟨1, unitPacket⟩, ⟨2, unitPacket⟩) :: diagonal

private theorem selectedProduct :
    (decorated false).checkProduct (decorated true) leftBit leftBit replies selectedPairs = true := by
  decide +kernel

-- Both checks reuse the original native representatives and their readbacks.
example : (decorated false).checkAllInterpreters? (decorated true)
    (inferred false).native (inferred true).native leftBit leftBit replies inventory inventory states = some true := by
  apply (FixedCarrier.acceptance_iff (checkedReadback false) (checkedReadback true) leftBit
    (fun reg => input leftBit (reg, 0)) rfl replies inventory states _ _
    (nativeValid false) (nativeValid true) selectedExit selectedExit).mpr
  intro prim s
  rw [FixedCarrier.observeNamed_native (checkedReadback false) leftBit _ rfl prim inventory states _
      (nativeValid false) s selectedExit,
    FixedCarrier.observeNamed_native (checkedReadback true) leftBit _ rfl prim inventory states _
      (nativeValid true) s selectedExit]
  exact (decorated false).checkProduct_sound (decorated true) _ _ (nativeValid false) (nativeValid true)
    leftBit leftBit replies selectedPairs selectedProduct prim s

example : (decorated true).checkAllInterpreters? (decorated false)
    (inferred true).native (inferred false).native leftBit leftBit replies inventory inventory states = some false := by
  apply (FixedCarrier.rejection_iff (checkedReadback true) (checkedReadback false) leftBit
    (fun reg => input leftBit (reg, 0)) rfl replies inventory states _ _
    (nativeValid true) (nativeValid false) selectedExit selectedExit).mpr
  refine ⟨rerouteInterpreter, 0, ?_⟩
  change ¬ named true rerouteInterpreter selectedExit ≤ named false rerouteInterpreter selectedExit
  rw [reroutedSelected, originalSelected]
  change ¬ resultBehaviour (.ub : Result 2 2) ≤ resultBehaviour (.ret 0 1)
  rw [result_order]
  decide

example : named false (fun _ _ _ => .fault 1) selectedExit = resultBehaviour (.fault 1) := by
  rw [named_classifies false _ selectedExit]
  rfl

private def repeating : Syntax.Primitives Op 2 :=
  fun _ arg s => .ret (pack (L := Packets) ⟨0, arg⟩) (if s = 0 then 1 else 0)

private theorem repeating_cycle :
    (decorated false).runFinite leftBit repeating inventory states ⟨0, leftBit⟩ 0 = .diverge := by
  decide +kernel

-- Every request resumes the original loop with the alternating machine state.
example : named false repeating selectedExit = resultBehaviour .diverge := by
  rw [named_classifies false repeating selectedExit, repeating_cycle]

namespace LiveBitRegression

open FixedCarrier (resultWithPayload)

private def exitBits (value : Bool) (i : Tag) : Bool := if i = 0 then value else false
private def literalOps (value : Bool) (i : Tag) : Op := .literal (exitBits value i)

private def liveSource (value : Bool) : CFG Reg Label signature.Instr :=
  let g := source false
  { g with blocks := g.blocks.map fun (k, row) =>
      match k with
      | .left => (k, { row with body := .let1 .left (.app (literalOps value 0) .unit) row.body })
      | .right => (k, { row with body := .let1 .left (.app (literalOps value 1) .unit) row.body })
      | _ => (k, row) }

private def liveAdmission? (value : Bool) :=
  PacketLocal.admit (P := signature) ports (FixedCarrier.LiveBit.fields Reg.left) (liveSource value) arguments

private def liveAdmitted (value : Bool) :
    Admission signature ports (FixedCarrier.LiveBit.fields Reg.left) (liveSource value) :=
  (liveAdmission? value).get (by cases value <;> decide +kernel)

private def liveChecked? (value : Bool) :=
  Recognize.recognize (seed := Reg.seed) (names := labels) (liveAdmitted value) .poll
    (fun i => some (literalOps value i))

-- The other program's assignment is rejected by exact lexical readback.
example : (Recognize.recognize (seed := Reg.seed) (names := labels) (liveAdmitted true) .poll
    (fun i => some (literalOps false i))).isNone = true := by decide +kernel

private def liveChecked (value : Bool) :=
  (liveChecked? value).get (by cases value <;> decide +kernel)

private abbrev liveControl (value : Bool) := Recognize.guardedTable Op.poll (liveChecked value).routes

private theorem liveNativeValid (value : Bool) : (liveControl value).checkNative (inferred false).native = true := by
  cases value <;> decide +kernel

private def literals : Op → Option Bool
  | .literal b => some b
  | _ => none

private theorem literalsAgree (value : Bool) (i : Tag) :
    literals (literalOps value i) = some (exitBits value i) := rfl

private def callerStore (r : Reg) := input leftBit (r, 0)

private noncomputable def observed (value : Bool) (selected : Tag → Bool := fun _ => false) :=
  FixedCarrier.LiveBit.observeNamed (liveSource value) labels .left callerStore literals rerouteInterpreter 0 selected

private theorem classified (value : Bool) (selected : Tag → Bool) :
    observed value selected = resultWithPayload (fun i => Recognize.exitPayload (some (exitBits value i)))
      ((FixedCarrier.withSelectedExits Op.poll (liveChecked value).routes selected).runFinite
        leftBit rerouteInterpreter inventory states ⟨0, leftBit⟩ 0) :=
  FixedCarrier.LiveBit.observeNamed_runFinite (liveChecked value) leftBit callerStore rfl literals (literalsAgree value)
    rerouteInterpreter inventory states 0 selected

private theorem liveReturned (value : Bool) :
    observed value = resultWithPayload (fun i => Recognize.exitPayload (some (exitBits value i))) (.ret 0 1) := by
  cases value <;> rw [classified] <;> rfl

example (value : Bool) :
    LambdaSSA.UB.Overlay.Shape.denote (FixedCarrier.LiveBit.nativeEndpoint (inferred false).native (exitBits value) (fun _ => false))
      (Syntax.model rerouteInterpreter ((liveControl value).bindings leftBit)) 0 =
        resultWithPayload (fun i => Recognize.exitPayload (some (exitBits value i))) (.ret 0 1) :=
  (FixedCarrier.LiveBit.observeNamed_native (liveChecked value) leftBit callerStore rfl literals
    (literalsAgree value) rerouteInterpreter inventory states _ (liveNativeValid value) 0 _).symm.trans
    (liveReturned value)

private theorem differingLiveOut : ¬ observed false ≤ observed true := by
  rw [liveReturned false, liveReturned true, ← FixedCarrier.LiveBit.compare_iff]
  decide +kernel

-- Both controls return unit at the same position in state one under this script.
-- The negative verdict is caused by the projected assignment.
example : FixedCarrier.LiveBit.check? .poll .poll (liveChecked false).routes (liveChecked true).routes
    (inferred false).native (inferred false).native (exitBits false) (exitBits true)
    (fun _ => false) (fun _ => false) leftBit replies inventory states = some false := by
  apply (FixedCarrier.LiveBit.rejection_iff (liveChecked false) (liveChecked true) leftBit callerStore rfl
    literals (literalsAgree false) (literalsAgree true) replies inventory states _ _
    (liveNativeValid false) (liveNativeValid true) _ _).mpr
  exact ⟨rerouteInterpreter, 0, differingLiveOut⟩

-- Selecting that ordered exit erases the whole payload on each endpoint.
example (value : Bool) : observed value (fun i => i == 0) = ⊤ := by
  cases value <;> rw [classified] <;> rfl

end LiveBitRegression

end FixedCarrier

namespace DynamicLiveOut

open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open FixedCarrier.LiveBit (PayloadType payloadExpr)
open FixedCarrier.PayloadRecognition (Checked recognize compare? outputPacket)

private abbrev Incoming : List Syntax.Ty := [Bit, Bit, .unit]
private abbrev Outputs := Payload.Exits PayloadType

private def targets (backedge : Bool) (tag : Fin 3) : Fin 3 :=
  if tag = 0 then if backedge then 0 else 1 else 2

private abbrev control (selected : Tag → Bool) (backedge : Bool := false) : Table nativeSig Incoming where
  entry := 0
  row := Fin.cases (motive := fun i : Fin 3 => Row nativeSig Incoming [Incoming.get i, Bit])
    (.request .poll (.var 0) (targets backedge) (by cases backedge <;> intro i <;> fin_cases i <;> rfl))
    (Fin.cases (motive := fun i : Fin 2 => Row nativeSig Incoming [Incoming.get i.succ, Bit])
      (.exit 0) (fun _ => .exit 1))
  selected := selected

private abbrev endpoint (fixed : Bool) (selected : Tag → Bool) (backedge : Bool := false) : Endpoint nativeSig Incoming PayloadType where
  control := control selected backedge
  output := Fin.cases (motive := fun i : Fin 3 => Syntax.Expr [Incoming.get i, Bit] PayloadType)
    (payloadExpr false)
    (Fin.cases (motive := fun i : Fin 2 => Syntax.Expr [Incoming.get i.succ, Bit] PayloadType)
      (if fixed then payloadExpr false else .pair .unit (.pair (.var 0) .unit))
      (fun _ => payloadExpr false))

private abbrev outgoing := outputPacket

private def payloadBit (value : Value Unit) : Bool :=
  match value with
  | .pair .unit (.pair (.inr .unit) .unit) => true
  | _ => false

private def codes : Fin 4 ≃ Packet Outputs where
  toFun i := outgoing (if i.val < 2 then 0 else 1) (i.val % 2 == 1)
  invFun p := ⟨p.1.val * 2 + (if payloadBit p.2.val then 1 else 0), by
    have bounded := p.1.isLt
    change p.1.val < 2 at bounded
    split <;> omega⟩
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    rintro ⟨tag, value, typed⟩
    fin_cases tag <;>
      cases typed with
      | pair old field =>
        cases old
        cases field with
        | pair bit tail =>
          cases tail
          cases bit with
          | inl bit => cases bit; rfl
          | inr bit => cases bit; rfl

private def packets : List (Packet Incoming) :=
  [⟨0, leftBit⟩, ⟨0, rightBit⟩, ⟨1, leftBit⟩, ⟨1, rightBit⟩, ⟨2, unitPacket⟩]

private def configs : ConfigurationEnumeration Incoming := ⟨packets, by
  rintro ⟨i, value, typed⟩
  fin_cases i
  · cases typed with
    | inl h => cases h; exact List.Mem.head _
    | inr h => cases h; exact List.Mem.tail _ (List.Mem.head _)
  · cases typed with
    | inl h => cases h; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | inr h => cases h; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · cases typed
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

private def script (bit : Bool) : Syntax.Primitives Op 2 :=
  InterpreterScript.interpret [
    InterpreterScript.Row.success (S := nativeSig) ⟨.poll, leftBit, 0⟩
      ⟨0, if bit then rightBit else leftBit⟩ 1]

private def noSelection : Tag → Bool := fun _ => false
private abbrev dynamic := endpoint false noSelection
private abbrev fixed := endpoint true noSelection
private abbrev marked := endpoint false (fun i => i == 0)

private theorem valid (fixed : Bool) (selected : Tag → Bool) (backedge : Bool := false) :
    (endpoint fixed selected backedge).checkNative (endpoint fixed selected backedge).native = true := by
  have exactCheck : (endpoint fixed noSelection backedge).checkNative (endpoint fixed noSelection backedge).native = true := by
    cases fixed <;> cases backedge <;> decide +kernel
  exact exactCheck

private noncomputable def observed (fixed : Bool) (selected : Tag → Bool) (prim : Syntax.Primitives Op 2) :=
  LambdaSSA.UB.Overlay.Shape.denote
    (CFG.Dependent.Native.withExitUB (endpoint fixed selected).native selected)
    (Syntax.model prim ((control selected).bindings leftBit)) 0

private theorem observesDynamic (bit : Bool) : observed false noSelection (script bit) =
    WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 bit).2.val (1 : Fin 2)} := by
  unfold observed
  rw [dynamic.observe_entry codes _ (valid false noSelection) leftBit _ configs states]
  cases bit <;> rfl

private theorem observesFixed : observed true noSelection (script true) =
    WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 false).2.val (1 : Fin 2)} := by
  unfold observed
  rw [fixed.observe_entry codes _ (valid true noSelection) leftBit _ configs states]
  rfl

-- A single ordered exit exposes either payload under the two shared scripts.
example : observed false noSelection (script false) = WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 false).2.val (1 : Fin 2)} :=
  observesDynamic false

example : observed false noSelection (script true) = WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 true).2.val (1 : Fin 2)} :=
  observesDynamic true

example : observed false (fun i => i == 0) (script true) = ⊤ := by
  unfold observed
  rw [marked.observe_entry codes _ (valid false _) leftBit _ configs states]
  rfl

private theorem witness : ¬ observed false noSelection (script true) ≤ observed true noSelection (script true) := by
  rw [observesDynamic true, observesFixed]
  simp [WithTop.coe_le_coe, outgoing]
  intro eq; cases eq

-- The fixed projection is a different typed native readback.
example : dynamic.checkNative fixed.native = false := by decide +kernel

private def namedSource (fixed : Bool) (backedge : Bool) : CFG Reg Label signature.Instr :=
  let finish : CFG.Body Reg Label signature.Instr := .term (.br .first .unit)
  let assign := fun label => CFG.Body.let1 .left (.app (.literal false) .unit) (.term (.br label .unit))
  ⟨.term (.br .loop (.var .seed)),
    [(.loop, ⟨.arg, .term (.case (.app .poll (.var .arg))
      .again (.br (if backedge then .loop else .left) (.var .again))
      .rest (.case (.val (.var .rest))
        .left (.br .right (.var .left))
        .tail (.case (.val (.var .tail))
          .right (.br .right (.var .right)) .impossible (.br .right .unit))))⟩),
     (.left, ⟨.left, if fixed then assign .first else finish⟩),
     (.right, ⟨.arg, assign .second⟩)]⟩

private def argumentTypes (i : Fin 3) : Ty SortName := if i = 2 then .unit else bit

private def namedAdmission (fixed backedge : Bool) :
    Admission signature ports (FixedCarrier.LiveBit.fields Reg.left) (namedSource fixed backedge) :=
  (PacketLocal.admit (P := signature) ports (FixedCarrier.LiveBit.fields Reg.left)
    (namedSource fixed backedge) argumentTypes).get (by cases fixed <;> cases backedge <;> decide +kernel)

private def literalValues : Op → Option Bool
  | .literal bit => some bit
  | _ => none

private def recognized? (fixed backedge : Bool) :=
  recognize (namedAdmission fixed backedge) .poll literalValues

private def checked (fixed backedge : Bool) :
    Checked (namedAdmission fixed backedge) .poll literalValues :=
  (recognized? fixed backedge).get (by cases fixed <;> cases backedge <;> decide +kernel)

private theorem recognized_eq (fixed backedge : Bool) :
    recognized? fixed backedge = some (checked fixed backedge) := by
  cases fixed <;> cases backedge <;> rfl

-- A missing literal interpretation cannot produce a semantic comparison.
example : compare?
    (recognize (namedAdmission false false) .poll (fun _ => none))
    (recognize (namedAdmission true false) .poll (fun _ => none))
    dynamic.native fixed.native noSelection noSelection codes leftBit leftBit replies configs states = none := by
  rfl

private theorem inferred_native (fixed backedge : Bool) (selected : Tag → Bool) :
    ((checked fixed backedge).profile.endpoint .poll selected).checkNative
      (endpoint fixed selected backedge).native = true := by
  have h := (show ∀ f b : Bool,
      ((checked f b).profile.endpoint .poll noSelection).checkNative
        (endpoint f noSelection b).native = true by intro f b; cases f <;> cases b <;> decide +kernel) fixed backedge
  exact h

private def seedStore (r : Reg) := input leftBit (r, 0)

private noncomputable def namedObserved (fixed backedge : Bool) (selected : Tag → Bool)
    (prim : Syntax.Primitives Op 2) (s : Fin 2 := 0) :=
  FixedCarrier.LiveBit.observeNamed (namedSource fixed backedge) labels .left seedStore literalValues prim s selected

private theorem named_observes (fixed backedge : Bool) (selected : Tag → Bool)
    (prim : Syntax.Primitives Op 2) (s : Fin 2) :
    namedObserved fixed backedge selected prim s =
      LambdaSSA.UB.Overlay.Shape.denote
        (CFG.Dependent.Native.withExitUB (endpoint fixed selected backedge).native selected)
        (Syntax.model prim ((control selected backedge).bindings leftBit)) s :=
  (checked fixed backedge).observe_native selected leftBit seedStore rfl _
    (inferred_native fixed backedge selected) codes prim configs states s

example (bit : Bool) : namedObserved false false noSelection (script bit) =
    WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 bit).2.val (1 : Fin 2)} :=
  (named_observes false false noSelection (script bit) 0).trans (observesDynamic bit)

private theorem fixed_returns :
    namedObserved true false noSelection (script true) =
      WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 false).2.val (1 : Fin 2)} :=
  (named_observes true false noSelection (script true) 0).trans observesFixed

private theorem named_witness :
    ¬ namedObserved false false noSelection (script true) ≤ namedObserved true false noSelection (script true) := by
  rw [named_observes false false noSelection, named_observes true false noSelection]
  exact witness

example : compare? (recognized? false false) (recognized? true false)
    dynamic.native fixed.native noSelection noSelection codes leftBit leftBit replies configs states = some false := by
  rw [recognized_eq false false, recognized_eq true false]
  apply (FixedCarrier.PayloadRecognition.rejection_iff (checked false false) (checked true false)
    leftBit leftBit seedStore seedStore rfl rfl _ _ noSelection noSelection codes replies configs states
    (inferred_native false false noSelection) (inferred_native true false noSelection)).mpr
  exact ⟨script true, 0, named_witness⟩

example (fixed bit : Bool) : namedObserved fixed false (fun i => i == 0) (script bit) = ⊤ := by
  rw [named_observes fixed false, (endpoint fixed _).observe_entry codes _ (valid fixed _) leftBit _ configs states]
  cases fixed <;> cases bit <;> rfl

private def backedgeScript : Syntax.Primitives Op 2 :=
  InterpreterScript.interpret [
    InterpreterScript.Row.success (S := nativeSig) ⟨.poll, leftBit, 0⟩ ⟨0, rightBit⟩ 1,
    InterpreterScript.Row.success (S := nativeSig) ⟨.poll, rightBit, 1⟩ ⟨1, unitPacket⟩ 1]

-- The bit reply revisits the request with a different packet and state.
-- The next reply returns at the second ordered exit.
example : namedObserved false true noSelection backedgeScript =
    WithTop.some {Outcome.ret (1 : Tag) (outgoing 1 false).2.val (1 : Fin 2)} := by
  rw [named_observes false true noSelection,
    (endpoint false noSelection true).observe_entry codes _ (valid false noSelection true) leftBit _ configs states]
  rfl

example : compare? (recognized? false true) (recognized? false true)
    (endpoint false noSelection true).native (endpoint false noSelection true).native
    noSelection noSelection codes leftBit leftBit replies configs states = some true := by
  rw [recognized_eq false true]
  apply (FixedCarrier.PayloadRecognition.acceptance_iff (checked false true) (checked false true)
    leftBit leftBit seedStore seedStore rfl rfl _ _ noSelection noSelection codes replies configs states
    (inferred_native false true noSelection) (inferred_native false true noSelection)).mpr
  intro prim s
  exact le_rfl

namespace Ordered

open FixedCarrier.OrderedLiveOut (bitExpr recordExpr)

private abbrev projected := FixedCarrier.OrderedLiveOut.outputPacket

private abbrev Out := FixedCarrier.OrderedLiveOut.Outputs
private abbrev outputType := FixedCarrier.OrderedLiveOut.PayloadType

private def orderedSource (fixed : Bool) (backedge : Bool := false) : CFG Reg Label signature.Instr :=
  let g := namedSource fixed backedge
  { g with blocks := g.blocks.map fun (label, row) =>
      if label = .left ∨ label = .right then
        let terminal := if label = .right && backedge && !fixed then
          CFG.Body.let1 .left (.app (.literal true) .unit) (.term (.br .second .unit))
          else row.body
        (label, { row with body := .let1 .alt (.app (.literal true) .unit) terminal })
      else (label, row) }

private def orderedAdmission (fixed : Bool) (backedge : Bool := false) :
    Admission signature ports (FixedCarrier.OrderedLiveOut.fields Reg.alt Reg.left) (orderedSource fixed backedge) :=
  (PacketLocal.admit ports (FixedCarrier.OrderedLiveOut.fields Reg.alt Reg.left)
    (orderedSource fixed backedge) argumentTypes).get (by cases fixed <;> cases backedge <;> decide +kernel)

private def inferred? (fixed : Bool) (backedge : Bool := false) :=
  FixedCarrier.OrderedLiveOut.recognize (orderedAdmission fixed backedge) .poll literalValues

private def inferred (fixed : Bool) (backedge : Bool := false) :
    FixedCarrier.OrderedLiveOut.Checked (orderedAdmission fixed backedge) .poll literalValues :=
  (inferred? fixed backedge).get (by cases fixed <;> cases backedge <;> decide +kernel)

private theorem accepted (fixed : Bool) (backedge : Bool := false) :
    inferred? fixed backedge = some (inferred fixed backedge) := by
  cases fixed <;> cases backedge <;> rfl

-- The first write is common; only the second field's operand changes.
example : (inferred false).profile.atBit.first = .literal (.literal true) true := rfl
example : (inferred false).profile.atBit.second = .read := rfl
example : (inferred true).profile.atBit.second = .literal (.literal false) false := rfl

private def retainFirstSource : CFG Reg Label signature.Instr :=
  let g := orderedSource true
  { g with blocks := g.blocks.map fun (label, row) =>
      if label = .left then
        (label, ⟨.alt, .let1 .left (.app (.literal false) .unit) (.term (.br .first .unit))⟩)
      else (label, row) }

private def retainFirstAdmission :
    Admission signature ports (FixedCarrier.OrderedLiveOut.fields Reg.alt Reg.left) retainFirstSource :=
  (PacketLocal.admit ports (FixedCarrier.OrderedLiveOut.fields Reg.alt Reg.left)
    retainFirstSource argumentTypes).get (by decide +kernel)

-- Retention can occupy the first slot as well as the second.
example : ((FixedCarrier.OrderedLiveOut.recognize retainFirstAdmission .poll literalValues).map
    (fun c => c.profile.atBit.first)) = some .read := rfl

private abbrev nativeEndpoint (fixed : Bool) (selected : Tag → Bool) (backedge : Bool := false) :
    Endpoint nativeSig Incoming outputType where
  control := control selected backedge
  output := Fin.cases (motive := fun i : Fin 3 => Syntax.Expr [Incoming.get i, Bit] outputType)
    (recordExpr (bitExpr false) (bitExpr false))
    (Fin.cases (motive := fun i : Fin 2 => Syntax.Expr [Incoming.get i.succ, Bit] outputType)
      (recordExpr (bitExpr true) (if fixed then bitExpr false else .var 0))
      (Fin.cases (recordExpr (bitExpr true) (bitExpr (backedge && !fixed))) (fun i => Fin.elim0 i)))

private theorem exactNative (fixed : Bool) (selected : Tag → Bool) (backedge : Bool := false) :
    ((inferred fixed backedge).profile.endpoint .poll selected).checkNative
      (nativeEndpoint fixed selected backedge).native = true := by
  have readback : ((inferred fixed backedge).profile.endpoint .poll noSelection).checkNative
      (nativeEndpoint fixed noSelection backedge).native = true := by
    cases fixed <;> cases backedge <;> decide +kernel
  exact readback

private abbrev orderedCodes := FixedCarrier.OrderedLiveOut.outputCodes

private noncomputable def observedNamed (fixed : Bool) (selected : Tag → Bool := noSelection) :=
  FixedCarrier.OrderedLiveOut.observeNamed (orderedSource fixed) labels .alt .left seedStore literalValues
    (script true) 0 selected

private theorem returned (fixed : Bool) :
    observedNamed fixed = WithTop.some {Outcome.ret (0 : Tag) (projected 0 true (!fixed)).2.val (1 : Fin 2)} := by
  unfold observedNamed
  rw [(inferred fixed).observe_native noSelection leftBit seedStore rfl _ (exactNative fixed noSelection)
    orderedCodes (script true) configs states 0]
  exact (((inferred fixed).profile.endpoint .poll noSelection).observe_entry orderedCodes _
    (exactNative fixed noSelection) leftBit (script true) configs states 0).trans (by cases fixed <;> rfl)

example : observedNamed false = WithTop.some {Outcome.ret (0 : Tag) (projected 0 true true).2.val (1 : Fin 2)} :=
  returned false

example : observedNamed true = WithTop.some {Outcome.ret (0 : Tag) (projected 0 true false).2.val (1 : Fin 2)} :=
  returned true

private theorem differentSecond : ¬ observedNamed false ≤ observedNamed true := by
  rw [returned false, returned true]
  simp [WithTop.coe_le_coe, projected, FixedCarrier.OrderedLiveOut.outputPacket]
  intro same
  cases same

example : FixedCarrier.OrderedLiveOut.compare? (inferred? false) (inferred? true)
    (nativeEndpoint false noSelection).native (nativeEndpoint true noSelection).native
    noSelection noSelection orderedCodes leftBit leftBit replies configs states = some false := by
  rw [accepted false, accepted true]
  apply (FixedCarrier.OrderedLiveOut.rejection_iff (inferred false) (inferred true)
    leftBit leftBit seedStore seedStore rfl rfl _ _ noSelection noSelection orderedCodes replies configs states
    (exactNative false noSelection) (exactNative true noSelection)).mpr
  exact ⟨script true, 0, differentSecond⟩

-- Selected UB hides the whole ordered record, including the differing bit.
example (fixed : Bool) : observedNamed fixed (fun i => i == 0) = ⊤ := by
  let selected : Tag → Bool := fun i => i == 0
  unfold observedNamed
  rw [(inferred fixed).observe_native selected leftBit seedStore rfl _ (exactNative fixed selected)
    orderedCodes (script true) configs states 0]
  have observation := ((inferred fixed).profile.endpoint .poll selected).observe_entry orderedCodes _
    (exactNative fixed selected) leftBit (script true) configs states 0
  refine observation.trans ?_
  have run : ((inferred fixed).profile.endpoint .poll selected).runFinite orderedCodes leftBit
      (script true) configs states ⟨0, leftBit⟩ 0 = .ub := by
    cases fixed <;> decide +kernel
  rw [run]
  rfl

private def firstSelected : Tag → Bool := fun i => i == 0

private abbrev ranked := (inferred false).profile.endpoint .poll firstSelected
private abbrev cyclic := (inferred false true).profile.endpoint .poll noSelection

example : ranked.control.entryCheck = true := by decide +kernel
example : cyclic.control.entryCheck = false := by decide +kernel
example : ranked.control.rankedCutoff cyclic.control = 2 := by decide +kernel

private def natHandler : Syntax.StatePrimitives signature.Instr Nat :=
  fun _ _ s => if s = 0 then .ret (pack (L := Replies) ⟨0, rightBit⟩) 1 else .diverge

private noncomputable def onNat (backedge : Bool) (selected : Tag → Bool) :=
  FixedCarrier.OrderedLiveOut.observeNamedOn (orderedSource false backedge) labels .alt .left seedStore
    literalValues natHandler 0 selected

private theorem rankedNat : onNat false firstSelected = ⊤ := by
  have original := (inferred false).observe_native_on firstSelected leftBit seedStore rfl _
    (exactNative false firstSelected) natHandler 0
  have atEntry := ranked.observe_entry_state (nativeEndpoint false firstSelected).native
    (exactNative false firstSelected) leftBit natHandler 0
  refine original.trans (atEntry.trans ?_)
  rw [ranked.observe_state_step]
  change ranked.observeAt leftBit natHandler ⟨1, rightBit⟩ 1 = ⊤
  rw [ranked.observe_state_step]
  rfl

private theorem cyclicNat : onNat true noSelection = WithTop.some {Outcome.diverge} := by
  have original := (inferred false true).observe_native_on noSelection leftBit seedStore rfl _
    (exactNative false noSelection true) natHandler 0
  have atEntry := cyclic.observe_entry_state (nativeEndpoint false noSelection true).native
    (exactNative false noSelection true) leftBit natHandler 0
  refine original.trans (atEntry.trans ?_)
  rw [cyclic.observe_state_step]
  change cyclic.observeAt leftBit natHandler ⟨0, rightBit⟩ 1 = WithTop.some {Outcome.diverge}
  rw [cyclic.observe_state_step]
  rfl

-- The original ranked runner returns through the selected exit. The
-- unranked runner takes the internal edge, then sees primitive divergence.
example : FixedCarrier.OrderedLiveOut.compareRanked? (inferred? false) (inferred? false true)
    (nativeEndpoint false firstSelected).native (nativeEndpoint false noSelection true).native
    firstSelected noSelection orderedCodes leftBit FixedCarrier.OrderedLiveOut.replyPackets
    FixedCarrier.OrderedLiveOut.configurations = some false := by
  rw [accepted false, accepted false true]
  apply (FixedCarrier.OrderedLiveOut.ranked_rejection_iff (inferred false) (inferred false true)
    leftBit seedStore seedStore rfl rfl _ _ firstSelected noSelection orderedCodes
    FixedCarrier.OrderedLiveOut.replyPackets FixedCarrier.OrderedLiveOut.configurations
    (exactNative false firstSelected) (exactNative false noSelection true) (.inl (by decide +kernel))).mpr
  refine ⟨Nat, natHandler, 0, ?_⟩
  change ¬ onNat false firstSelected ≤ onNat true noSelection
  rw [rankedNat, cyclicNat]
  simp

example : FixedCarrier.OrderedLiveOut.compareRanked? (inferred? false true) (inferred? false true)
    (nativeEndpoint false noSelection true).native (nativeEndpoint false noSelection true).native
    noSelection noSelection orderedCodes leftBit FixedCarrier.OrderedLiveOut.replyPackets
    FixedCarrier.OrderedLiveOut.configurations = none := rfl

example : FixedCarrier.OrderedLiveOut.compareRanked? (inferred? false) (inferred? false)
    (nativeEndpoint false firstSelected).native (nativeEndpoint false firstSelected).native
    firstSelected firstSelected orderedCodes leftBit FixedCarrier.OrderedLiveOut.replyPackets
    FixedCarrier.OrderedLiveOut.configurations = some true := by
  rw [accepted false]
  apply (FixedCarrier.OrderedLiveOut.ranked_acceptance_iff (inferred false) (inferred false)
    leftBit seedStore seedStore rfl rfl _ _ firstSelected firstSelected orderedCodes
    FixedCarrier.OrderedLiveOut.replyPackets FixedCarrier.OrderedLiveOut.configurations
    (exactNative false firstSelected) (exactNative false firstSelected) (.inl (by decide +kernel))).mpr
  intro σ prim s
  exact le_rfl

private abbrev loopEndpoint (fixed : Bool) (selected : Tag → Bool) :=
  (inferred fixed true).profile.endpoint .poll selected

private def retry : Syntax.StatePrimitives signature.Instr Nat :=
  fun _ _ n => .ret (pack (L := Replies) ⟨0, leftBit⟩) (n + 1)

private def retryThenExit : Syntax.StatePrimitives signature.Instr Nat :=
  fun _ _ n => if n = 0 then .ret (pack (L := Replies) ⟨0, rightBit⟩) 1
    else .ret (pack (L := Replies) ⟨1, unitPacket⟩) (n + 1)

private noncomputable def observeCycle (fixed : Bool) (selected : Tag → Bool)
    (prim : Syntax.StatePrimitives signature.Instr Nat) :=
  FixedCarrier.OrderedLiveOut.observeNamedOn (orderedSource fixed true) labels .alt .left seedStore
    literalValues prim 0 selected

private theorem cycle_native (fixed : Bool) (selected : Tag → Bool)
    (prim : Syntax.StatePrimitives signature.Instr Nat) :
    observeCycle fixed selected prim = (loopEndpoint fixed selected).observeAt leftBit prim ⟨0, leftBit⟩ 0 :=
  ((inferred fixed true).observe_native_on selected leftBit seedStore rfl _
    (exactNative fixed selected true) prim 0).trans
    ((loopEndpoint fixed selected).observe_entry_state _ (exactNative fixed selected true) leftBit prim 0)

-- Both named graphs replay infinitely under the same state-changing handler.
private theorem cycle_infinite (fixed : Bool) :
    observeCycle fixed noSelection retry = WithTop.some {Outcome.diverge} := by
  rw [cycle_native]
  exact (loopEndpoint fixed noSelection).observe_infinite leftBit retry (fun _ => ⟨0, leftBit⟩)
    (fun n => n) (by intro n; cases fixed <;> rfl)

example : observeCycle false noSelection retry = observeCycle true noSelection retry :=
  (cycle_infinite false).trans (cycle_infinite true).symm

private theorem cycle_exits (fixed : Bool) :
    observeCycle fixed noSelection retryThenExit =
      WithTop.some {Outcome.ret (1 : Tag) (projected 1 true (!fixed)).2.val (2 : Nat)} := by
  cases fixed <;> rw [cycle_native]
  all_goals
    rw [Endpoint.observe_state_step]
    rw [show Head.execute retryThenExit _ 0 = .repeat (⟨0, rightBit⟩ : Packet Incoming) 1 from rfl]
    dsimp only
    rw [Endpoint.observe_state_step]
    rw [show Head.execute retryThenExit _ 1 = .repeat (⟨2, unitPacket⟩ : Packet Incoming) 2 from rfl]
    dsimp only
    rw [Endpoint.observe_state_step]
    rfl

private theorem cycle_distinguished :
    ¬ observeCycle false noSelection retryThenExit ≤ observeCycle true noSelection retryThenExit := by
  rw [cycle_exits false, cycle_exits true]
  simp [WithTop.coe_le_coe, projected, FixedCarrier.OrderedLiveOut.outputPacket]
  intro same
  cases same

example : (loopEndpoint false noSelection).control.entryCheck = false ∧
    (loopEndpoint true noSelection).control.entryCheck = false := by decide +kernel

example : (loopEndpoint false noSelection).reachableCutoff (loopEndpoint true noSelection)
    leftBit leftBit replies configs configs = 3 := by
  decide +kernel

example : FixedCarrier.OrderedLiveOut.compareReachable? (inferred? false true) (inferred? true true)
    (nativeEndpoint false noSelection true).native (nativeEndpoint true noSelection true).native
    noSelection noSelection leftBit = some false := by
  rw [accepted false true, accepted true true]
  apply (FixedCarrier.OrderedLiveOut.reachable_rejection_iff (inferred false true) (inferred true true)
    leftBit seedStore seedStore rfl rfl _ _ noSelection noSelection
    (exactNative false noSelection true) (exactNative true noSelection true)).mpr
  exact ⟨Nat, retryThenExit, 0, cycle_distinguished⟩

-- The same rejected readback is unsupported if substituted for the left endpoint.
example : FixedCarrier.OrderedLiveOut.compareReachable? (inferred? false true) (inferred? true true)
    (nativeEndpoint true noSelection true).native (nativeEndpoint true noSelection true).native
    noSelection noSelection leftBit = none := by decide +kernel

private def secondSelected : Tag → Bool := fun i => i == 1

example : FixedCarrier.OrderedLiveOut.compareReachable? (inferred? false true) (inferred? true true)
    (nativeEndpoint false secondSelected true).native (nativeEndpoint true secondSelected true).native
    secondSelected secondSelected leftBit = some true := by
  rw [accepted false true, accepted true true]
  apply (FixedCarrier.OrderedLiveOut.reachable_acceptance_iff (inferred false true) (inferred true true)
    leftBit seedStore seedStore rfl rfl _ _ secondSelected secondSelected
    (exactNative false secondSelected true) (exactNative true secondSelected true)).mpr
  intro σ prim state
  rw [(inferred false true).observe_native_on secondSelected leftBit seedStore rfl _
        (exactNative false secondSelected true),
    (inferred true true).observe_native_on secondSelected leftBit seedStore rfl _
        (exactNative true secondSelected true),
    (loopEndpoint false secondSelected).observe_entry_state _ (exactNative false secondSelected true),
    (loopEndpoint true secondSelected).observe_entry_state _ (exactNative true secondSelected true)]
  apply (loopEndpoint false secondSelected).closed_relation_sound (loopEndpoint true secondSelected)
    leftBit leftBit prim (fun p q => p = q ∧ (p.1 = 0 ∨ p.1 = 2)) _ ⟨rfl, .inl rfl⟩ state
  intro p q related
  obtain ⟨rfl, live⟩ := related
  obtain ⟨i, value⟩ := p
  fin_cases i
  · refine ⟨rfl, rfl, ?_⟩
    rintro ⟨i, answer⟩
    fin_cases i
    · exact ⟨rfl, .inl rfl⟩
    · exact ⟨rfl, .inr rfl⟩
    · exact ⟨rfl, .inr rfl⟩
  · simp at live
  · trivial

namespace SilentCycle

open FixedCarrier.OrderedLiveOut.Silent (compare? compare_acceptance_iff compare_rejection_iff compare_none_iff)
open FixedCarrier.OrderedLiveOut.Silent (Checked recognize)
open FixedCarrier.OrderedLiveOut (observeNamedOn)

private def source (loop : Bool) : CFG Reg Label signature.Instr :=
  let g := orderedSource false
  { g with blocks := g.blocks.map fun (label, row) =>
      if loop && label == .left then (label, ⟨.left, .term (.br .left (.var .left))⟩) else (label, row) }

private def admitted (loop : Bool) :
    Admission signature ports (FixedCarrier.OrderedLiveOut.fields Reg.alt Reg.left) (source loop) :=
  (PacketLocal.admit ports (FixedCarrier.OrderedLiveOut.fields Reg.alt Reg.left)
    (source loop) argumentTypes).get (by cases loop <;> decide +kernel)

private def checked? (loop : Bool) := recognize (admitted loop) .poll literalValues

private def checked (loop : Bool) : Checked (admitted loop) .poll literalValues :=
  (checked? loop).get (by cases loop <;> decide +kernel)

private theorem checked_eq (loop : Bool) : checked? loop = some (checked loop) := by
  cases loop <;> rfl

private abbrev originalNative (loop : Bool) (selected : Tag → Bool) :
    Endpoint nativeSig Incoming outputType :=
  let g := nativeEndpoint false selected
  { g with control := { g.control with
      row := Fin.cases (motive := fun i : Fin 3 => Row nativeSig Incoming [Incoming.get i, Bit])
        (g.control.row 0) (Fin.cases (if loop then .diverge else g.control.row 1)
          (Fin.cases (g.control.row 2) (fun i => Fin.elim0 i))) } }

private theorem exact (loop : Bool) (selected : Tag → Bool) :
    ((checked loop).profile.endpoint .poll selected).checkNative (originalNative loop selected).native = true := by
  have same : ((checked loop).profile.endpoint .poll noSelection).checkNative
      (originalNative loop noSelection).native = true := by
    cases loop <;> decide +kernel
  cases loop <;> exact same

private def handler (bitReply : Bool) : Syntax.StatePrimitives signature.Instr Nat :=
  fun _ _ n => if n = 0 then
    .ret (pack (L := Replies) (if bitReply then ⟨0, rightBit⟩ else ⟨1, unitPacket⟩)) 1
  else .fault n

private noncomputable def observe (loop bitReply : Bool) (selected : Tag → Bool) :=
  observeNamedOn (source loop) labels .alt .left seedStore literalValues (handler bitReply) 0 selected

private theorem observe_exact (loop bitReply : Bool) (selected : Tag → Bool) :
    observe loop bitReply selected =
      ((checked loop).profile.endpoint .poll selected).observeAt leftBit (handler bitReply) ⟨0, leftBit⟩ 0 :=
  ((checked loop).observe_native_on selected leftBit seedStore rfl _ (exact loop selected) (handler bitReply) 0).trans
    (((checked loop).profile.endpoint .poll selected).observe_entry_state _
      (exact loop selected) leftBit (handler bitReply) 0)

-- The shared reply changes the packet and state. Another request would fault.
private theorem diverges (selected : Tag → Bool) :
    observe true true selected = WithTop.some {Outcome.diverge} := by
  rw [observe_exact, Endpoint.observe_state_step]
  rw [show Head.execute (handler true) _ 0 =
    .repeat (⟨1, rightBit⟩ : Packet Incoming) 1 from rfl]
  dsimp only
  rw [Endpoint.observe_state_step]
  rfl

private theorem ordinary :
    observe false true noSelection = WithTop.some {Outcome.ret (0 : Tag) (projected 0 true true).2.val 1} := by
  rw [observe_exact, Endpoint.observe_state_step]
  rw [show Head.execute (handler true) _ 0 =
    .repeat (⟨1, rightBit⟩ : Packet Incoming) 1 from rfl]
  dsimp only
  rw [Endpoint.observe_state_step]
  rfl

private theorem selected : observe false true firstSelected = ⊤ := by
  rw [observe_exact, Endpoint.observe_state_step]
  rw [show Head.execute (handler true) _ 0 =
    .repeat (⟨1, rightBit⟩ : Packet Incoming) 1 from rfl]
  dsimp only
  rw [Endpoint.observe_state_step]
  rfl

private theorem ordinaryMismatch : ¬ observe true true noSelection ≤ observe false true noSelection := by
  rw [diverges, ordinary]
  simp [WithTop.coe_le_coe]

private theorem reverseUB : ¬ observe false true firstSelected ≤ observe true true noSelection := by
  rw [selected, diverges]
  simp

-- A unit reply still returns both fields at the ordinary alternate exit.
example : observe true false firstSelected = WithTop.some {Outcome.ret (1 : Tag) (projected 1 true false).2.val 1} := by
  rw [observe_exact, Endpoint.observe_state_step]
  rw [show Head.execute (handler false) _ 0 =
    .repeat (⟨2, unitPacket⟩ : Packet Incoming) 1 from rfl]
  dsimp only
  rw [Endpoint.observe_state_step]
  rfl


-- At the reached silent packet, the tree has no request root.
example :
    FixedCarrier.PayloadRecognition.packetTree ((checked true).profile.endpoint .poll noSelection)
      leftBit ⟨1, rightBit⟩ = Silmaril.Elgot.ITree.diverge :=
  FixedCarrier.PayloadRecognition.roots ((checked true).profile.endpoint .poll noSelection) leftBit ⟨1, rightBit⟩

example : compare? (checked? true) (checked? false)
    (originalNative true noSelection).native (originalNative false noSelection).native
    noSelection noSelection leftBit seedStore seedStore = some false := by
  rw [checked_eq true, checked_eq false]
  apply (compare_rejection_iff (checked true) (checked false) leftBit seedStore seedStore
    _ _ noSelection noSelection rfl rfl (exact true noSelection) (exact false noSelection)).mpr
  exact ⟨Nat, handler true, 0, ordinaryMismatch⟩

example : compare? (checked? false) (checked? true)
    (originalNative false firstSelected).native (originalNative true noSelection).native
    firstSelected noSelection leftBit seedStore seedStore = some false := by
  rw [checked_eq false, checked_eq true]
  apply (compare_rejection_iff (checked false) (checked true) leftBit seedStore seedStore
    _ _ firstSelected noSelection rfl rfl (exact false firstSelected) (exact true noSelection)).mpr
  exact ⟨Nat, handler true, 0, reverseUB⟩

example : compare? (checked? true) (checked? false)
    (originalNative true noSelection).native (originalNative false firstSelected).native
    noSelection firstSelected leftBit seedStore seedStore = some true := by
  rw [checked_eq true, checked_eq false]
  apply (compare_acceptance_iff (checked true) (checked false) leftBit seedStore seedStore
    _ _ noSelection firstSelected rfl rfl (exact true noSelection) (exact false firstSelected)).mpr
  intro σ prim state
  rw [(checked true).observe_native_on noSelection leftBit seedStore rfl _ (exact true noSelection),
    (checked false).observe_native_on firstSelected leftBit seedStore rfl _ (exact false firstSelected),
    Endpoint.observe_entry_state _ _ (exact true noSelection),
    Endpoint.observe_entry_state _ _ (exact false firstSelected)]
  apply ((checked true).profile.endpoint .poll noSelection).closed_relation_sound
    ((checked false).profile.endpoint .poll firstSelected) leftBit leftBit prim Eq _ rfl state
  rintro p q rfl
  obtain ⟨i, packet⟩ := p
  fin_cases i
  · exact ⟨rfl, rfl, fun _ => rfl⟩
  · trivial
  · rfl

-- An otherwise checked pair with the wrong runtime seed stays unknown.
example : compare? (checked? true) (checked? false)
    (originalNative true noSelection).native (originalNative false firstSelected).native
    noSelection firstSelected leftBit seedStore (fun _ => .inr .unit) = none := by
  rw [checked_eq true, checked_eq false]
  apply (compare_none_iff (checked true) (checked false) leftBit seedStore (fun _ => .inr .unit)
    _ _ noSelection firstSelected).mpr
  exact .inr (.inl rfl)

end SilentCycle


namespace IdentityTransfer

open FixedCarrier.OrderedLiveOut.Identity
open FixedCarrier.OrderedLiveOut (fields)

private abbrev slots : List Bool := [true, true, false]
private abbrev L := layout slots
private abbrev Labels := ULift.{1} (Fin 6)
private def keys : Fin 6 ≃ Labels := Equiv.ulift.symm

-- A Bit reply enters row 1. Row 1 forwards the packet to row 2.
-- Row 2 either returns both fields or forwards it back to row 1.
private def source (cycle : Bool) (target : Fin 6 := 2) : CFG Reg Labels signature.Instr :=
  ⟨.term (.br (keys 0) (.var .seed)),
    [(keys 0, ⟨.arg, .term (.case (.app .poll (.var .arg))
      .again (.br (keys 1) (.var .again))
      .rest (.case (.val (.var .rest))
        .left (.br (keys 3) (.var .left))
        .tail (.case (.val (.var .tail))
          .right (.br (keys 3) (.var .right)) .impossible (.br (keys 3) .unit))))⟩),
     (keys 1, ⟨.again, .term (.br (keys target) (.var .again))⟩),
     (keys 2, ⟨.left, if cycle then .term (.br (keys 1) (.var .left))
       else .let1 .alt (.app (.literal true) .unit) (.term (.br (keys 4) .unit))⟩),
     (keys 3, ⟨.arg, .let1 .alt (.app (.literal true) .unit)
       (.let1 .left (.app (.literal false) .unit) (.term (.br (keys 5) .unit)))⟩)]⟩

private def inferred? (cycle : Bool) (target : Fin 6 := 2) :=
  admit? (P := signature) (slots := slots) (seed := Reg.seed) (first := Reg.alt) (second := Reg.left)
    (names := keys) (source cycle target) literalValues

private def checked (cycle : Bool) :
    FixedCarrier.OrderedLiveOut.Identity.Checked (P := signature) (slots := slots) (seed := Reg.seed)
      (first := Reg.alt) (second := Reg.left) (names := keys) (source cycle) literalValues :=
  (inferred? cycle).get (by cases cycle <;> decide +kernel)

private theorem checked_eq (cycle : Bool) : inferred? cycle = some (checked cycle) := by
  cases cycle <;> rfl

private abbrev native (cycle : Bool) (selected : Tag → Bool) : Endpoint nativeSig L outputType where
  control := {
    entry := 0
    row := Fin.cases (motive := fun i : Fin 4 => Row nativeSig L [L.get i, Bit])
      (.request .poll (.var 0) (fun i => if i = 0 then 1 else 3) (by intro i; fin_cases i <;> rfl))
      (Fin.cases (if cycle then .diverge else .exit 0)
        (Fin.cases (if cycle then .diverge else .exit 0)
          (Fin.cases (.exit 1) (fun i => Fin.elim0 i))))
    selected := selected }
  output := Fin.cases (motive := fun i : Fin 4 => Syntax.Expr [L.get i, Bit] outputType)
    (recordExpr (bitExpr false) (bitExpr false))
    (Fin.cases (recordExpr (bitExpr true) (.var 0))
      (Fin.cases (recordExpr (bitExpr true) (.var 0))
        (Fin.cases (recordExpr (bitExpr true) (bitExpr false)) (fun i => Fin.elim0 i))))

private theorem exact (cycle : Bool) (selected : Tag → Bool) :
    ((checked cycle).profile.endpoint selected).checkNative (native cycle selected).native = true := by
  have unselected : ((checked cycle).profile.endpoint noSelection).checkNative (native cycle noSelection).native = true := by
    cases cycle <;> decide +kernel
  cases cycle <;> exact unselected

private def handler : Syntax.StatePrimitives signature.Instr Nat :=
  fun _ _ n => if n = 0 then .ret (pack (L := Replies) ⟨0, rightBit⟩) 1 else .fault n

private noncomputable def observe (cycle : Bool) (selected : Tag → Bool) :=
  observeNamedNumbered (source cycle) keys .alt .left seedStore literalValues handler 0 selected

private theorem exposed (cycle : Bool) :
    observe cycle noSelection =
      ((checked cycle).profile.endpoint noSelection).observeAt leftBit handler ⟨1, rightBit⟩ 1 := by
  let g := (checked cycle).profile.endpoint noSelection
  have admitted := (checked cycle).observe_native_on seedStore leftBit rfl noSelection
    (native cycle noSelection).native (exact cycle noSelection) handler 0
  have start := g.observe_entry_state _ (exact cycle noSelection) leftBit handler 0
  refine (admitted.trans start).trans ?_
  cases cycle <;> exact g.observe_state_step leftBit handler ⟨0, leftBit⟩ 0

private theorem cycle_diverges : observe true noSelection = WithTop.some {Outcome.diverge} :=
  (exposed true).trans (((checked true).profile.endpoint noSelection).observe_state_step leftBit handler ⟨1, rightBit⟩ 1)

private theorem chain_returns : observe false noSelection =
    WithTop.some {Outcome.ret (0 : Tag) (projected 0 true true).2.val (1 : Nat)} :=
  (exposed false).trans (((checked false).profile.endpoint noSelection).observe_state_step leftBit handler ⟨1, rightBit⟩ 1)

example : ¬ observe true noSelection ≤ observe false noSelection := by
  rw [cycle_diverges, chain_returns]
  simp [WithTop.coe_le_coe]

-- The full scan keeps the second relay as the origin of the returning fields.
example : (checked false).profile.scan 4 1 = some (.ret 2 0) := by decide +kernel
example : (checked true).profile.scan 4 1 = none := by decide +kernel

-- The declared exit slot and the ill-typed unit slot are both rejected.
example : (inferred? true 4).isNone = true := by decide +kernel
example : (inferred? true 3).isNone = true := by decide +kernel

private def wrongOperand : CFG Reg Labels signature.Instr :=
  let g := source true
  { g with blocks := g.blocks.map fun (k, row) =>
      if k == keys 1 then (k, ⟨.again, .term (.br (keys 2) (.var .seed))⟩) else (k, row) }

example : (admit? (P := signature) (slots := slots) (seed := Reg.seed) (first := Reg.alt)
    (second := Reg.left) (names := keys) wrongOperand literalValues).isNone = true := by
  decide +kernel

private def configurations : ConfigurationEnumeration L :=
  ⟨[⟨0, leftBit⟩, ⟨0, rightBit⟩, ⟨1, leftBit⟩, ⟨1, rightBit⟩,
    ⟨2, leftBit⟩, ⟨2, rightBit⟩, ⟨3, unitPacket⟩], by
    rintro ⟨i, value, typed⟩
    fin_cases i
    · cases typed with
      | inl h => cases h; decide +kernel
      | inr h => cases h; decide +kernel
    · cases typed with
      | inl h => cases h; decide +kernel
      | inr h => cases h; decide +kernel
    · cases typed with
      | inl h => cases h; decide +kernel
      | inr h => cases h; decide +kernel
    · cases typed
      decide +kernel⟩

example : compare? (inferred? true) (inferred? false)
    (native true noSelection).native (native false noSelection).native
    noSelection noSelection leftBit seedStore seedStore configurations = some false := by
  rw [checked_eq true, checked_eq false]
  apply (compare_rejection_iff (checked true) (checked false) _ _ noSelection noSelection
    leftBit seedStore seedStore configurations rfl rfl (exact true noSelection) (exact false noSelection)).mpr
  refine ⟨Nat, handler, 0, ?_⟩
  change ¬ observe true noSelection ≤ observe false noSelection
  rw [cycle_diverges, chain_returns]
  simp [WithTop.coe_le_coe]

example : compare? (inferred? true) (inferred? false)
    (native true noSelection).native (native false noSelection).native
    noSelection noSelection leftBit seedStore (fun _ => .inr .unit) configurations = none := by
  rw [checked_eq true, checked_eq false]
  apply (compare_none_iff (checked true) (checked false) _ _ noSelection noSelection
    leftBit seedStore (fun _ => .inr .unit) configurations).mpr
  exact .inr (.inl rfl)

end IdentityTransfer

namespace PacketDispatch

open FixedCarrier.OrderedLiveOut (fields PayloadType)
open FixedCarrier.OrderedLiveOut.Identity (layout observeNamedNumbered)
open FixedCarrier.OrderedLiveOut.PacketDispatch

private abbrev slots : List Bool := [true, true, false]
private abbrev L := layout slots
private abbrev Labels := ULift.{1} (Fin 6)
private def keys : Fin 6 ≃ Labels := Equiv.ulift.symm

-- A successful reply supplies false to row 1. The finishing variant
-- revisits row 1 with true before returning from row 2.
private def source (cycle : Bool) (target : Fin 6 := 2) (wrongDecoder : Bool := false) :
    CFG Reg Labels signature.Instr :=
  let branch (discriminator : Reg) := .term (.case (.val (.var discriminator))
    .left (.br (keys 1) (.var .alt))
    .right (.br (keys target) (.var .again)))
  ⟨.term (.br (keys 0) (.var .seed)),
    [(keys 0, ⟨.arg, .term (.case (.app .poll (.var .arg))
      .again (.br (keys 1) (.var .again))
      .rest (.case (.val (.var .rest))
        .left (.br (keys 3) (.var .left))
        .tail (.case (.val (.var .tail))
          .right (.br (keys 3) (.var .right)) .impossible (.br (keys 3) .unit))))⟩),
     (keys 1, ⟨.again, .let1 .alt (.app (.literal (!cycle)) .unit)
       (branch (if wrongDecoder then .alt else .again))⟩),
     (keys 2, ⟨.left, .let1 .alt (.app (.literal true) .unit) (.term (.br (keys 4) .unit))⟩),
     (keys 3, ⟨.arg, .let1 .alt (.app (.literal true) .unit)
       (.let1 .left (.app (.literal false) .unit) (.term (.br (keys 5) .unit)))⟩)]⟩

private def inferred? (cycle : Bool) (target : Fin 6 := 2) (wrongDecoder : Bool := false) :=
  admit? (P := signature) (slots := slots) (seed := Reg.seed) (first := Reg.alt) (second := Reg.left)
    (names := keys) (source cycle target wrongDecoder) literalValues

private def checked (cycle : Bool) :
    FixedCarrier.OrderedLiveOut.PacketDispatch.Checked (P := signature) (slots := slots) (seed := Reg.seed)
      (first := Reg.alt) (second := Reg.left) (names := keys) (source cycle) literalValues :=
  (inferred? cycle).get (by cases cycle <;> decide +kernel)

private abbrev configurations : ConfigurationEnumeration L := IdentityTransfer.configurations

private def handler : Syntax.StatePrimitives signature.Instr Nat :=
  fun _ _ n => if n = 0 then .ret (pack (L := Replies) ⟨0, leftBit⟩) 1 else .fault n

private noncomputable def observe (cycle : Bool) (selected : Tag → Bool) :=
  observeNamedNumbered (source cycle) keys .alt .left seedStore literalValues handler 0 selected

private theorem afterReply (cycle : Bool) (selected : Tag → Bool) :
    observe cycle selected =
      (checked cycle).profile.observeAt configurations leftBit ⟨1, leftBit⟩ handler 1 selected := by
  unfold observe
  rw [(checked cycle).observe_normalized seedStore leftBit configurations rfl,
    (checked cycle).profile.observe_step leftBit configurations ⟨0, leftBit⟩]
  cases cycle <;> rfl

private theorem loop_diverges : observe true noSelection = WithTop.some {Outcome.diverge} := by
  rw [afterReply, (checked true).profile.observe_step leftBit configurations ⟨1, leftBit⟩]
  rfl

private theorem changed_returns : observe false noSelection =
    WithTop.some {Outcome.ret (0 : Tag) (projected 0 true true).2.val (1 : Nat)} := by
  rw [afterReply, (checked false).profile.observe_step leftBit configurations ⟨1, leftBit⟩]
  rfl

private theorem changed_selected : observe false firstSelected = ⊤ := by
  rw [afterReply, (checked false).profile.observe_step leftBit configurations ⟨1, leftBit⟩]
  rfl

example : ¬ observe true noSelection ≤ observe false noSelection := by
  rw [loop_diverges, changed_returns]
  simp [WithTop.coe_le_coe]

example : ¬ observe false firstSelected ≤ observe true noSelection := by
  rw [changed_selected, loop_diverges]
  simp

example : ((checked false).profile.control noSelection).step leftBit ⟨1, leftBit⟩ = .inl ⟨1, rightBit⟩ := by
  rfl

example : ((checked false).profile.control noSelection).step leftBit ⟨1, rightBit⟩ = .inl ⟨2, rightBit⟩ := by
  rfl

example : ((checked true).profile.control noSelection).step leftBit ⟨1, leftBit⟩ = .inl ⟨1, leftBit⟩ := by
  rfl

private abbrev native (cycle : Bool) := (checked cycle).profile.control noSelection

private def callers : CallerEnumeration Bit :=
  ⟨[leftBit, rightBit], by
    rintro ⟨x, typed⟩
    cases typed with
    | inl h => cases h; exact List.Mem.head _
    | inr h => cases h; exact List.Mem.tail _ (List.Mem.head _)⟩

-- The unit-return packed view is separated by the same control mismatch.
example : (native true).checkEntries? (native false) (native true).native (native false).native
    callers id id replies configurations configurations = some false := by
  rfl

-- The alternate discriminator passes typed packet-local admission.
example : (PacketLocal.admit (P := signature) (Recognize.numberedInterface Reg.seed keys)
    (FixedCarrier.OrderedLiveOut.fields Reg.alt Reg.left) (source false 2 true)
    (FixedCarrier.OrderedLiveOut.Identity.argumentType (slots := slots))).isSome = true := by
  decide +kernel

-- Exact readback declines the changed discriminator and invalid targets.
example : (inferred? false 2 true).isNone = true := by decide +kernel
example : (inferred? false 4).isNone = true := by decide +kernel
example : (inferred? false 3).isNone = true := by decide +kernel

end PacketDispatch

end Ordered

end DynamicLiveOut

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests
