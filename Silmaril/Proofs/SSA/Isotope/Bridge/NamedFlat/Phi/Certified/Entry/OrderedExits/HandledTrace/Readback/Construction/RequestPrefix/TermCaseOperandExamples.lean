module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Native.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.TermCaseOperandExamples

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Transfer region splitTransfer)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree Trace HasTrace vis iterate_fixpoint vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature)
open EffectfulEntry.Multiple.Computed.Native renaming Compiled → Scheduled, compile → compileNative

private abbrev bit : PacketType := .coprod .unit .unit
private abbrev choice : PacketType := .coprod bit bit
private abbrev control : PacketType := .coprod bit choice

private abbrev sig : PrimitiveSignature (Fin 3) :=
  ⟨fun _ => .product bit bit, fun op => if op.val = 0 then choice else if op.val = 1 then bit else control⟩
private abbrev Events := Event sig.Request sig.Reply

private def inputs : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) control
private def packets (_ : Fin 1) : PacketType := control
private def outputs (_ : Fin 2) : PacketType := bit

/-- The request argument has a term case in its first field. The case
uses a primitive reply to select whether to make another request, then
the common consumer sees that result and the older capture. -/
private def source : FiniteCFG (Fin 3) 1 2 2 where
  entry := .br 0 (.bv 0)
  block _ := .case (.bv 0)
    (.let₁ (.op 2 (.pair (.case (.op 0 (.pair (.bv 0) (.bv 3)))
      (.op 1 (.pair (.bv 0) (.bv 4))) (.bv 0)) (.bv 3))) (.br 0 (.bv 0)))
    (.case (.bv 0) (.br 1 (.bv 0)) (.br 2 (.bv 0)))

private def build := compileNative sig inputs packets outputs source
private def built : Scheduled sig inputs packets outputs source := build.get (by decide +kernel)

example : built.code.entry = source.entry := by decide +kernel
example : built.code.block 0 = .case (.bv 0)
    (.let₁ (.op 0 (.pair (.bv 0) (.bv 3)))
      (.let₁ (.case (.bv 0) (.let₁ (.op 1 (.pair (.bv 0) (.bv 5))) (.bv 0)) (.bv 0))
        (.let₁ (.op 2 (.pair (.bv 0) (.bv 5))) (.br 0 (.bv 0)))))
    (.case (.bv 0) (.br 1 (.bv 0)) (.br 2 (.bv 0))) :=
  by decide +kernel

/-- Both bare injection arms get their sum type from the exit. -/
private def injected : FiniteCFG (Fin 3) 0 1 1 where
  entry := .br 0 (.case (.bv 0) (.inl .unit) (.inr .unit))
  block := Fin.elim0

private def injectionInputs : BoundCtx PacketType 1 := .snoc .nil bit
private def injectionOutputs (_ : Fin 1) : PacketType := bit
private def buildInjected := compileNative sig injectionInputs Fin.elim0 injectionOutputs injected
private def builtInjected : Scheduled sig injectionInputs Fin.elim0 injectionOutputs injected :=
  buildInjected.get (by decide +kernel)

example : builtInjected.code.entry =
    .let₁ (.case (.bv 0) (.inl .unit) (.inr .unit)) (.br 0 (.bv 0)) := by decide +kernel

-- The same emitted code still needs the scheduler's binder ascription.
example : let _ := sig.typing
    NamedFlat.checkExpected builtInjected.code injectionInputs Fin.elim0 injectionOutputs = false :=
  by decide +kernel

private def heterogeneous (_ : Fin 1) : PacketType := .coprod .unit bit

-- The right arm of the written case provides unit where the exit expects bit.
example : (compileNative sig injectionInputs Fin.elim0 heterogeneous injected).isNone = true :=
  by decide +kernel

-- Even an explicit ascription is checked against both written arms.
example : let _ := sig.typing
    NamedFlat.checkWithBindings builtInjected.code injectionInputs Fin.elim0 heterogeneous
      (.node (some (heterogeneous 0)) .empty .empty .empty) Fin.elim0 = false :=
  by decide +kernel

-- The inner ascription is needed within the selected arm of the outer case,
-- at a position inside the outer let's initializer.
private def nestedInjection : FiniteCFG (Fin 3) 0 1 1 where
  entry := .br 0 (.case (.bv 0) (.case (.bv 1) (.inl .unit) (.inr .unit)) (.inr .unit))
  block := Fin.elim0

example : (compileNative sig injectionInputs Fin.elim0 injectionOutputs nestedInjection).isSome = true :=
  by decide +kernel

private def injectedValue (left : Bool) : Denote bit :=
  if left then .inl ⟨⟩ else .inr ⟨⟩

private def injectedEnv (left : Bool) : Env Atom := fun _ => bit.encode (injectedValue left)

/-- The original term case and actual packed runner agree on both input tags,
including the tag in the value returned at the ordered exit. -/
theorem packed_injected (left : Bool) :
    builtInjected.observe sig.primitive (fun _ => .unit) (NamedFlat.Capture.packEnv 1 (injectedEnv left)) =
      pure (FiniteCFG.packedTreeOutput (0, bit.encode (injectedValue left))) := by
  rw [builtInjected.packed_run]
  have entry : injected.entry.erase = .br 0 (.case (.var 0) (.inl .unit) (.inr .unit)) := rfl
  cases left <;>
    simp [FiniteCFG.erase, entry, region, LambdaSSA.Semantics.Interaction.term, injectedEnv, injectedValue,
      Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.encode, splitTransfer]

private def first : Denote bit := .inl ⟨⟩
private def saved : Denote bit := .inr ⟨⟩
private def env : Env Atom := fun i => if i = 0 then control.encode (.inl first) else bit.encode saved

private def pollKey (payload : Denote bit) : sig.Request := ⟨0, (payload, saved)⟩
private def armKey (payload : Denote bit) : sig.Request := ⟨1, (payload, saved)⟩
private def consumeKey (value : Denote bit) : sig.Request := ⟨2, (value, saved)⟩

private theorem request_tree (req : sig.Request) :
    sig.primitive req.1 ((sig.argument req.1).encode req.2) =
      vis (.ask req) (fun reply : sig.Reply req => pure ((sig.reply req.1).encode reply)) := by
  cases req with
  | mk op arg =>
    unfold PrimitiveSignature.primitive
    rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode]

private noncomputable def step (state : BlockInput Atom 1) :
    Tree Events (Transfer Atom ⊕ BlockInput Atom 1) :=
  region sig.primitive (extend env state.2) (source.block state.1).erase >>= fun out =>
    pure (splitTransfer 1 out)

private noncomputable def afterCase (value : Denote bit) : Tree Events (Transfer Atom) :=
  vis (.ask (consumeKey value)) fun reply : sig.Reply (consumeKey value) =>
    iter step (0, control.encode reply)

private theorem written_row : (source.block 0).erase = .case (.var 0)
      (.let₁ (.op 2 (.pair (.case (.op 0 (.pair (.var 0) (.var 3)))
        (.op 1 (.pair (.var 0) (.var 4))) (.var 0)) (.var 3))) (.br 0 (.var 0)))
      (.case (.var 0) (.br 1 (.var 0)) (.br 2 (.var 0))) := rfl

private theorem visit (current : Denote bit) :
    iter step (0, control.encode (.inl current)) =
      vis (.ask (pollKey current)) fun reply : sig.Reply (pollKey current) =>
        match reply with
        | .inl payload => vis (.ask (armKey payload)) fun next : sig.Reply (armKey payload) => afterCase next
        | .inr payload => afterCase payload := by
  rw [congrFun (iterate_fixpoint step) (0, control.encode (.inl current))]
  have packet : extend env (control.encode (.inl current)) 0 = .inl (bit.encode current) := rfl
  simp only [step, written_row, region, LambdaSSA.Semantics.Interaction.term,
    packet, bind_assoc, pure_bind]
  let poll := pollKey current
  change (sig.primitive poll.1 ((sig.argument poll.1).encode poll.2) >>= _) = _
  rw [request_tree poll, vis_bind]
  simp only [pure_bind]
  apply congrArg (vis (E := Events) (.ask poll))
  funext reply
  have consume (value : Denote bit) :
      (sig.primitive 2 (.pair (bit.encode value) (bit.encode saved)) >>= fun next =>
        Sum.elim pure (iter step) (splitTransfer 1 (0, next))) = afterCase value := by
    let req := consumeKey value
    change (sig.primitive req.1 ((sig.argument req.1).encode req.2) >>= _) = _
    rw [request_tree req, vis_bind]
    simp only [pure_bind]
    rfl
  cases reply with
  | inl payload =>
    have encoded : (sig.reply poll.1).encode (.inl payload) = .inl (bit.encode payload) := rfl
    simp only [encoded]
    let req := armKey payload
    change (sig.primitive req.1 ((sig.argument req.1).encode req.2) >>= _) = _
    rw [request_tree req, vis_bind]
    simp only [pure_bind]
    apply congrArg (vis (E := Events) (.ask req))
    funext value
    exact consume value
  | inr payload =>
    have encoded : (sig.reply poll.1).encode (.inr payload) = .inr (bit.encode payload) := rfl
    simp only [encoded, pure_bind]
    exact consume payload

private theorem exit_run (left : Bool) (payload : Denote bit) :
    iter step (0, control.encode (.inr (if left then .inl payload else .inr payload))) =
      pure (if left then 0 else 1, bit.encode payload) := by
  rw [congrFun (iterate_fixpoint step) (0, control.encode (.inr (if left then .inl payload else .inr payload)))]
  cases left <;>
    simp [step, written_row, region, LambdaSSA.Semantics.Interaction.term, extend,
      choice, Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.encode, splitTransfer]

private theorem start : region sig.primitive env source.erase = iter step (0, control.encode (.inl first)) := by
  have entry : source.entry.erase = .br 0 (.var 0) := rfl
  simp only [FiniteCFG.erase, region, entry, LambdaSSA.Semantics.Interaction.term, pure_bind]
  rw [show splitTransfer 1 (0, env 0) = .inr (0, control.encode (.inl first)) from rfl, Sum.elim_inr]
  rfl

private def trace (left : Bool) : Trace Events (Transfer Atom) :=
  .exchange (.ask (pollKey first)) (.inl first)
    (.exchange (.ask (armKey first)) saved
      (.exchange (.ask (consumeKey saved)) (.inl saved)
        (.exchange (.ask (pollKey saved)) (.inr first)
          (.exchange (.ask (consumeKey first)) (.inr (if left then .inl first else .inr first))
            (.result (FiniteCFG.packedTreeOutput (if left then 0 else 1, bit.encode first)))))))

/-- The first visit takes the effectful case arm. After the backedge the
other arm skips that request, and the same payload can reach either exit. -/
theorem packed_exits (left : Bool) :
    HasTrace (built.observe sig.primitive (fun _ => .unit) (NamedFlat.Capture.packEnv 2 env)) (trace left) := by
  rw [built.packed_run, start, visit first, vis_bind]
  unfold trace
  erw [hasTrace_vis_exchange_iff]
  rw [vis_bind]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (afterCase saved >>= _) _
  rw [afterCase, vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [visit saved, vis_bind]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (afterCase first >>= _) _
  rw [afterCase, vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [exit_run left first, pure_bind]
  exact out_ret _

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.TermCaseOperandExamples
