module

public import Silmaril.Wasm.Execution.Core.Soundness.PresBasic
public import Silmaril.Wasm.Execution.Core.Soundness.PresControl
public import Silmaril.Wasm.Execution.Core.Soundness.StateFacts

@[expose] public section

/-! # Preservation: wiring of the control rules

`PresConcl`-level wrappers of the `AdminsOk`-level replacement lemmas of
`PresControl.lean`, in the shape of the cases of `Step.preservation_gen`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

theorem CtxUnder.types_frame {s : Store H} {f : Frame} {Cf Ct : Context}
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf) : Ct.types = f.module.types := by
  have : Ct.types = Cf.types := congrArg TypeCtx.types hu.toTypeCtx
  rw [this, hf.types_eq]

theorem pres_block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct (vals vs ++ [.plain (.block bt body)]) it →
      PresConcl ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
        ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (Step.block_presCtl hty hwf (hu.types_frame hf) hbt hm)

theorem pres_loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct (vals vs ++ [.plain (.loop bt body)]) it →
      PresConcl ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
        ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (Step.loop_presCtl hty hwf (hu.types_frame hf) hbt hm)

theorem pres_ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} (_hc : c ≠ 0) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [constI32 c, .plain (.if_ bt b₁ b₂)] it →
      PresConcl ⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩
        ⟨s, f, [.plain (.block bt b₁)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu _ _ hty
  exact PresConcl.same hs hf hu (Step.ifTrue_presCtl hty)

theorem pres_ifFalse {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [constI32 0, .plain (.if_ bt b₁ b₂)] it →
      PresConcl ⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩
        ⟨s, f, [.plain (.block bt b₂)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu _ _ hty
  exact PresConcl.same hs hf hu (Step.ifFalse_presCtl hty)

theorem pres_labelVals {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.label n cont (vals vs)] it →
      PresConcl ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu _ _ hty
  exact PresConcl.same hs hf hu (Step.labelVals_presCtl hty)

theorem pres_brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} (hl : l.toNat = 0)
    (hn : vs.length = n) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)] it →
      PresConcl ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩
        ⟨s, f, vals vs ++ expression cont⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (Step.brLabelZero_presCtl hty hwf hl hn)

theorem pres_brLabelSucc {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val} {l : LabelIdx} {rest : List Admin} (hl : 0 < l.toNat) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)] it →
      PresConcl ⟨s, f, [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (Step.brLabelSucc_presCtl hty hwf hl)

theorem pres_brHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
    {l : LabelIdx} {rest : List Admin} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)] it →
      PresConcl ⟨s, f, [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.plain (.br l)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  exact PresConcl.same hs hf hu
    (Step.brHandler_presCtl hty hwf (AdminsOk.regular hs hts hwf hty).2.1)

theorem pres_tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct (vals vs ++ [.plain (.tryTable bt cs body)]) it →
      PresConcl ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
        ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩
        Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (Step.tryTable_presCtl hty hwf (hu.types_frame hf) hbt hm)

theorem pres_handlerVals {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.handler n cs (vals vs)] it →
      PresConcl ⟨s, f, [.handler n cs (vals vs)]⟩ ⟨s, f, vals vs⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu _ _ hty
  exact PresConcl.same hs hf hu (Step.handlerVals_presCtl hty)

end Silmaril.Wasm.Execution.Core
