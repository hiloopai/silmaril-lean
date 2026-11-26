module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Identity.Defs

import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Identity

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (liftPure)
open Silmaril.Elgot.ITree (Tree)
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
variable {slots : List Bool}

theorem restore_block {K : Type 1} (keys : Fin ((layout slots).length + 2) ≃ K)
    (i : Fin (layout slots).length) (input : Value Runtime) :
    restoreAt keys (i.val, input) = (keys (i.castAdd 2), input) :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity.restore_block keys i input

theorem row_replay {κ K : Type 1} {P : FlatInstitution.Signature.{0, 0} κ}
    (names : Fin ((layout slots).length + 2) ≃ K) (i : Fin (layout slots).length)
    (row : Row P.Instr (layout slots) ((layout slots).get i))
    (literals : P.Instr → Option Bool) (agrees : row.Agrees literals) (caller : Payload Bit)
    (packet : Payload ((layout slots).get i)) (env : Env Runtime) :
    (row.step caller packet >>= liftPure (Sum.map id (encodePhase names))) =
      (region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up packet.val) .unit)) row.code.erase >>=
        fun q => pure (.inr (restoreAt names q))) :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity.row_replay names i row literals agrees caller packet env

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

/-- The complete original named tree equals the normalized tree, including
cycles that exhaust the finite silent scan. -/
theorem Checked.named_tree (seedValue : input seed = encodeValue ULift.up entry.val) :
    LiveOut.observeRaw instr (I).exits (fun _ => [first, second]) source input = ck.profile.tree entry ⟨0, entry⟩ :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity.named_tree
    ck input entry seedValue

/-- Exact normalized native readback preserves the original named
observation at every deterministic handler and admitted typed caller. -/
theorem Checked.observe_native_on [DecidableEq P.Instr] {σ : Type v}
    (seedValue : input seed = encodeValue ULift.up entry.val)
    (selected : Tag → Bool) (raw : Typed P.Instr [Bit] Outputs)
    (valid : (ck.profile.endpoint selected).checkNative raw = true) (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedNumbered source names first second input literals prim s selected =
      Shape.denote (withExitUB raw selected) (Syntax.model prim ((ck.profile.endpoint selected).control.bindings entry)) s :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity.native_observation
    ck input entry seedValue selected raw valid prim s

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

/-- With both recognitions present, unknown records a failed caller
binding or normalized native readback. -/
theorem compare_none_iff :
    verdict = none ↔ Silent.matchesCaller caller (store seed) = false ∨
      Silent.matchesCaller caller (store' seed) = false ∨
      (left.profile.endpoint selected).checkNative raw = false ∨
      (right.profile.endpoint selected').checkNative raw' = false :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity.none_iff
    left right raw raw' selected selected' caller store store' configs

variable (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller.val)
  (valid : (left.profile.endpoint selected).checkNative raw = true)
  (valid' : (right.profile.endpoint selected').checkNative raw' = true)

include seedValue seedValue' valid valid'

/-- The checker is sound for original named observations in any store universe. -/
theorem compare_acceptance_sound {σ : Type v} (yes : verdict = some true) (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedNumbered source names first second store literals prim s selected ≤
      observeNamedNumbered target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity.acceptance_sound
    left right raw raw' selected selected' caller store store' configs seedValue seedValue' valid valid' yes prim s

/-- For exact readbacks and caller bindings, the cutoff decides the
original named refinement over all deterministic stores of type `Type`. -/
theorem compare_acceptance_iff :
    verdict = some true ↔
      ∀ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        observeNamedNumbered source names first second store literals prim s selected ≤
          observeNamedNumbered target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity.acceptance_iff
    left right raw raw' selected selected' caller store store' configs seedValue seedValue' valid valid'

/-- A negative verdict is equivalent to a counterexample at the original named endpoints. -/
theorem compare_rejection_iff :
    verdict = some false ↔
      ∃ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        ¬ observeNamedNumbered source names first second store literals prim s selected ≤
          observeNamedNumbered target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity.rejection_iff
    left right raw raw' selected selected' caller store store' configs seedValue seedValue' valid valid'

end Compare

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity
