module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Dispatch.Defs

import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Dispatch

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot.ITree (ret vis diverge)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet unpack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit numberedInterface requestTypes encodeValue)
open Identity (layout observeNamedNumbered)
open LiveBit (rawWithLiterals)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (Payload StatePrimitives)

attribute [local instance] requestTypes

universe v
variable {Φ : Type} {slots : List Bool}
  (p : Profile Φ slots) (caller : Payload Bit)

/-- Expose the first request, ordered return or divergence after traversing
silent edges between full typed configurations. -/
theorem Profile.tree_root (configs : ConfigurationEnumeration (layout slots)) (q : Packet (layout slots)) :
    p.tree configs caller q =
      match p.scan caller configs.configs.length q with
      | none => diverge
      | some (origin, .exit tag _) => ret (packedReturn (p.returnPacket caller origin tag))
      | some (_, .diverge) => diverge
      | some (_, .request f arg next) =>
        vis (.call f arg) (fun r => p.tree configs caller (next r.1 r.2)) :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch.tree_root p caller configs q

/-- Run at the normalized head with the original handler state and the
returning configuration's ordered fields. -/
theorem Profile.observe_step (configs : ConfigurationEnumeration (layout slots)) (q : Packet (layout slots))
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
        | .diverge => WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch.observe_step p caller configs q prim s selected

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

/-- Exact compiler readback relates the complete original weak tree to
typed normalization, including a packet changed on a silent transfer. -/
theorem Checked.named_tree (configs : ConfigurationEnumeration (layout slots))
    (seedValue : input seed = encodeValue ULift.up entry.val) :
    LiveOut.observeRaw instr (I).exits (fun _ => [first, second]) source input =
      ck.profile.tree configs entry ⟨0, entry⟩ :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch.named_tree ck input entry configs seedValue

/-- Caller agreement connects the actual named observer to the typed normalized
observer, with the same ordered exits, live-out fields and deterministic handler. -/
theorem Checked.observe_normalized (configs : ConfigurationEnumeration (layout slots))
    (seedValue : input seed = encodeValue ULift.up entry.val)
    {σ : Type v} (prim : StatePrimitives P.Instr σ) (s : σ) (selected : Tag → Bool) :
    observeNamedNumbered source names first second input literals prim s selected =
      ck.profile.observeAt configs entry ⟨0, entry⟩ prim s selected := by
  unfold observeNamedNumbered Profile.observeAt
  rw [ck.named_tree input entry configs seedValue]

end Named

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch
