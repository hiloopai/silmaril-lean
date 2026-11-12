module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.AggregateAll

/-!
# The forward recursion on every configuration

`forward_all` is `FwdMem.forward_upTo` with the fragment `Covered3 mem` removed:
the motive carries only `StoreOk c.store`, which the context rules pass to the inner
configuration unchanged (they keep the store). The base cases dispatch on the instruction:

* vectors: the bitwise operators by its proof's lemmas, the rest (`VecArith`) by
  `Open4.vector`;
* memory: every scalar constructor by round 2/3's lemmas (with `SliceTotal`, now proved), the
  memory SIMD ones (`VecMemI`) by `Open4.vecMem`;
* aggregates: at every frame, every constructor by `fwd_aggregate_any` (packed fields,
  `array.new_elem-alloc`, `array.new_data-oob`, `array.init_data-oob2`/`-num` included), except
  `array.new_data-num` and `array.init_data-zero`, from `Open4`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Integrate (StoreOk Extra)
open FwdMem (FwdUp fwdUp_of_fwdP)

variable {H : Type}

section Sub

variable {B : Builtins} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The `VectorStep`s: the bitwise constructors are proved, the others are `Open4.vector`. -/
theorem fwd_vector4 (hI : IntNumeric.IntB B) (hV : FwdSimdAgg.VVB B) (O : Open4 B hn P)
    {s : Store H} {f : Frame} {is is' : List Admin} (h : VectorStep P is is') :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have h' := h
  cases h with
  | vecUnOp op a => exact FwdSimdAgg.fwd_vecUnOp hV op a
  | vecBinOp op a b => exact FwdSimdAgg.fwd_vecBinOp hI hV op a b
  | vecTernOp op a b c => exact FwdSimdAgg.fwd_vecTernOp hV op a b c
  | vecTestOp op a => exact FwdSimdAgg.fwd_vecTestOp op a
  | _ => exact O.vector _ _ _ _ h' (by simp [VecArith, vconst])

/-- The `MemoryStep`s: every scalar constructor is proved, the memory SIMD ones are
`Open4.vecMem`. -/
theorem fwd_memory4 (A : Whole.Assumptions B hn host) (X : Extra (simEnv B))
    (hF : Floats.FloatB P B) (Bf : FwdMem.BytesFuns (simEnv B)) (O : Open4 B hn P)
    {c c' : Config H} (h : MemoryStep P c c') (hs : StoreOk c.store) :
    FwdP (simEnv B) hn c c' := by
  have T : TypingFacts (simEnv B) hn := A.typing
  have St : State.StateTyping (simEnv B) := A.state
  have hT' := FwdMem.sliceTotal
  have hv := O.vecMem _ _ h
  cases h with
  | loadIntOob hm h₁ => exact Memory.fwd_loadIntOob B T St X.mem hm h₁
  | loadIntVal hm hl => exact FwdMem.fwd_loadIntVal B T St X.mem Bf (.inl hT') hm hl
  | loadPackOob hm h₁ => exact Memory.fwd_loadPackOob B T St X.mem hm h₁
  | loadPackVal hm hl => exact FwdMem.fwd_loadPackVal B T St X.mem Bf hF (.inl hT') hm hl
  | loadFloatOob hm h₁ => exact Memory.fwd_loadFloatOob B T St X.mem hm h₁
  | loadFloatVal hm hl => exact FwdMem.fwd_loadFloatVal B T St X.mem Bf (.inl hT') hm hl
  | storeIntOob hm h₁ => exact Memory.fwd_storeIntOob B T St X.mem hm h₁
  | storeIntVal hm h₁ => exact FwdMem.fwd_storeIntVal B T St X.mem Bf (.inl hT') hm h₁
  | storePackOob hm h₁ => exact Memory.fwd_storePackOob B T St X.mem hm h₁
  | storePackVal hm h₁ => exact FwdMem.fwd_storePackVal B T St X.mem Bf hF (.inl hT') hm h₁
  | storeFloatOob hm h₁ => exact FwdMem.fwd_storeFloatOob B T St X.mem hm h₁
  | storeFloatVal hm h₁ => exact FwdMem.fwd_storeFloatVal B T St X.mem Bf (.inl hT') hm h₁
  | size hm =>
    exact Memory.fwd_memorySize B T St X.mem hm (hs.mem hm).1 (Integrate.pages_lt (hs.mem hm).2 _)
  | growSucceed hm hg _ =>
    exact Memory.fwd_memoryGrowSucceed B T St X.grow X.inst hm hg (hs.mem hm).1
      (Integrate.pages_lt (hs.mem hm).2 _)
  | growFail hm hp => exact State.fwd_memoryGrowFail B T St hm hp
  | fillOob hm h₁ => exact Memory.fwd_memoryFillOob B T St hm h₁
  | fillZero hm h₁ => exact Memory.fwd_memoryFillZero B T St hm h₁
  | @fillSucc s f x a i n v ma mi hm h₁ hnz =>
    exact Memory.fwd_memoryFillSucc B T St hm h₁ hnz
      (Integrate.succ_lt a hnz h₁ (hs.mem hm).2)
  | copyOob h₁ h₂ h₃ => exact Memory.fwd_memoryCopyOob B T St h₁ h₂ h₃
  | copyZero h₁ h₂ h₃ => exact Memory.fwd_memoryCopyZero B T St h₁ h₂ h₃
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hle =>
    exact Memory.fwd_memoryCopyLe B T St h₁ h₂ h₃ hnz hle
      ⟨Integrate.succ_lt a₁ hnz h₃.1 (hs.mem h₁).2, Integrate.succ_lt a₂ hnz h₃.2 (hs.mem h₂).2⟩
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hgt =>
    exact Memory.fwd_memoryCopyGt B T St h₁ h₂ h₃ hnz hgt
      ⟨Integrate.add_le_pow a₁ h₃.1 (hs.mem h₁).2, Integrate.add_le_pow a₂ h₃.2 (hs.mem h₂).2⟩
  | initOob hm hd h₁ => exact Memory.fwd_memoryInitOob B T St hm hd h₁
  | initZero hm hd h₁ => exact Memory.fwd_memoryInitZero B T St hm hd h₁
  | @initSucc s f x y a i j n ma da mi di byte hm hd h₁ hnz hb =>
    exact Memory.fwd_memoryInitSucc B T St hm hd h₁ hnz hb
      ⟨Integrate.succ_lt a hnz h₁.1 (hs.mem hm).2, Integrate.succ_lt .i32 hnz h₁.2 (hs.data hd)⟩
  | dataDrop h₁ => exact State.fwd_dataDrop B T St h₁
  | _ => exact hv (by simp [VecMemI, aconst]) hs

/-- The `AggregateStep`s, at every frame: `fwd_aggregate_any`, with `array.new_data-num` and
`array.init_data-zero` from `Open4`. -/
theorem fwd_aggregate4 (A : Whole.Assumptions B hn host) (X : Extra (simEnv B))
    (hF : Floats.FloatB P B) (hV : FwdSimdAgg.VVB B) (Z : ZBytes.ZB B)
    (XI : ExpandInv (simEnv B)) (O : Open4 B hn P) {c c' : Config H}
    (h : AggregateStep c c') (hs : StoreOk c.store) : FwdP (simEnv B) hn c c' :=
  fwd_aggregate_any hF hV Z XI A.typing A.rTyping A.rStore X.agg O.newDataNum O.initDataZero h
    hs.aggs

end Sub

/-- **The forward simulation with no coverage restriction, up to call annotations.** Under the
families' `Assumptions`, `Integrate.Extra`, `FloatB P B`, `BytesFuns`, `FwdSimdAgg.VVB B`,
`ZBytes.ZB B`, `ExpandInv` (both proved for `Prims.builtins`) and the per-class obligations `Open4`, every Core step from a configuration with a bounded store is a
SpecTec `Step` of the images in `simEnv B` to the image of a typed configuration `ConfigEq`-related
to Core's successor, whenever both configurations are typed. -/
theorem forward_all {B : Builtins} {hn : H → String} {P : Numerics.Profile}
    {host : HostSemantics H} (A : Whole.Assumptions B hn host) (X : Extra (simEnv B))
    (hF : Floats.FloatB P B) (Bf : FwdMem.BytesFuns (simEnv B)) (hV : FwdSimdAgg.VVB B)
    (Z : ZBytes.ZB B) (XI : ExpandInv (simEnv B)) (O : Open4 B hn P) {c c' : Config H}
    (h : Step P host c c') : StoreOk c.store → FwdUp (simEnv B) hn c c' :=
  have T := A.typing
  have Ty := A.ctrlTyping
  have U {c c' : Config H} : FwdP (simEnv B) hn c c' → FwdUp (simEnv B) hn c c' := fwdUp_of_fwdP
  Step.rec (motive := fun c c' _ => StoreOk c.store → FwdUp (simEnv B) hn c c')
    (fun hs _ => U (IntNumeric.fwd_parametric T hs))
    (fun hs _ => U (Whole.fwd_numeric_covered A hF hs))
    (fun hs _ => U (fwd_vector4 A.intB hV O hs))
    (fun hs _ => U (State.fwd_variable_ B T A.state hs))
    (fun hs hc => U (Memory.fwd_table_bounded B T A.state X.mem X.grow X.inst hs hc.tables))
    (fun hs hc => U (fwd_memory4 A X hF Bf O hs hc))
    (fun hs _ => U (RefsGC.fwd_reference B T A.rTyping A.rFuns A.rStore A.refOk hs))
    (fun hs hc => U (fwd_aggregate4 A X hF hV Z XI O hs hc))
    (fun _ hne ih hc => FwdMem.fwdUp_ctxtInstrs T hne (ih hc))
    (fun _ ih hc => FwdMem.fwdUp_ctxtLabel T (ih hc))
    (fun _ ih hc => FwdMem.fwdUp_ctxtHandler T (ih hc))
    (fun _ ih hc => FwdMem.fwdUp_ctxtFrame T (ih hc))
    (fun h₁ h₂ _ => U (fwd_block B T Ty A.ctrlState h₁ h₂))
    (fun h₁ h₂ _ => U (fwd_loop B T Ty A.ctrlState h₁ h₂))
    (fun h₁ _ => U (fwd_ifTrue B T Ty h₁))
    (fun _ => U (fwd_ifFalse B T Ty))
    (fun _ => U (fwd_labelVals B T))
    (fun h₁ h₂ _ => U (fwd_brLabelZero B T Ty h₁ h₂))
    (fun h₁ _ => U (fwd_brLabelSucc B T Ty h₁))
    (fun _ => U (fwd_brHandler B T Ty))
    (fun h₁ _ => U (fwd_brIfTrue B T Ty h₁))
    (fun _ => U (fwd_brIfFalse B T Ty))
    (fun h₁ _ => U (fwd_brTableLt B T Ty h₁))
    (fun h₁ _ => U (fwd_brTableGe B T Ty h₁))
    (fun _ => U (fwd_brOnNullNull B T Ty))
    (fun h₁ _ => U (fwd_brOnNullAddr B T Ty h₁))
    (fun _ => U (fwd_brOnNonNullNull B T Ty))
    (fun h₁ _ => U (fwd_brOnNonNullAddr B T Ty h₁))
    (fun h₁ _ => U (RefsGC.fwd_brOnCastSucceed B T A.rTyping A.rStore A.refOk h₁))
    (fun h₁ _ => U (RefsGC.fwd_brOnCastFail B T A.rTyping A.rStore A.refOk h₁))
    (fun h₁ _ => U (RefsGC.fwd_brOnCastFailSucceed B T A.rTyping A.rStore A.refOk h₁))
    (fun h₁ _ => U (RefsGC.fwd_brOnCastFailFail B T A.rTyping A.rStore A.refOk h₁))
    (fun h₁ h₂ _ => U (fwd_call B T Ty A.ctrlState h₁ h₂))
    (fun h₁ _ => U (fwd_callRefNull B T Ty h₁))
    (fun h₁ h₂ h₃ h₄ h₅ _ => U (fwd_callRefFunc B T Ty A.ctrlState A.ctrlCall A.ctrlHost
      h₁ h₂ h₃ h₄ h₅))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ _ => U (fwd_callRefHost B T Ty A.ctrlState A.ctrlCall A.ctrlHost
      h₁ h₂ h₃ h₄ h₅ h₆))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ _ => U (fwd_callRefHostDiv B T Ty A.ctrlState A.ctrlCall A.ctrlHost
      h₁ h₂ h₃ h₄ h₅ h₆))
    (fun h₁ h₂ _ => U (fwd_returnCall B T Ty A.ctrlState h₁ h₂))
    (fun h₁ _ => U (fwd_returnCallRefLabel B T Ty h₁))
    (fun h₁ _ => U (fwd_returnCallRefHandler B T Ty h₁))
    (fun h₁ _ => U (fwd_returnCallRefFrameNull B T Ty h₁))
    (fun h₁ h₂ h₃ h₄ _ =>
      FwdMem.fwdUp_returnCallRefFrameAddr T Ty A.ctrlState A.ctrlCall h₁ h₂ h₃ h₄)
    (fun _ => U (fwd_callIndirect B T Ty))
    (fun _ => U (fwd_returnCallIndirect B T Ty))
    (fun h₁ _ => U (fwd_frameVals B T h₁))
    (fun h₁ _ => U (fwd_returnFrame B T Ty h₁))
    (fun _ => U (fwd_returnLabel B T))
    (fun _ => U (fwd_returnHandler B T))
    (fun h₁ h₂ h₃ _ => U (Exn.fwd_throw B T A.exnTyping A.exnHelpers h₁ h₂ h₃))
    (fun _ => U (Exn.fwd_throwRefNull B T))
    (fun h₁ _ => U (Exn.fwd_throwRefInstrs B T A.exnTyping h₁))
    (fun _ => U (Exn.fwd_throwRefLabel B T A.exnTyping))
    (fun _ => U (Exn.fwd_throwRefFrame B T A.exnTyping))
    (fun _ => U (Exn.fwd_throwRefHandlerEmpty B T A.exnTyping))
    (fun h₁ h₂ _ => U (Exn.fwd_throwRefHandlerCatch B T A.exnTyping A.exnHelpers h₁ h₂))
    (fun h₁ h₂ _ => U (Exn.fwd_throwRefHandlerCatchRef B T A.exnTyping A.exnHelpers h₁ h₂))
    (fun _ => U (Exn.fwd_throwRefHandlerCatchAll B T A.exnTyping))
    (fun _ => U (Exn.fwd_throwRefHandlerCatchAllRef B T A.exnTyping))
    (fun h₁ _ => U (Exn.fwd_throwRefHandlerNext B T A.exnTyping A.exnHelpers h₁))
    (fun h₁ h₂ _ => U (Exn.fwd_tryTable B T A.exnTyping A.exnHelpers h₁ h₂))
    (fun _ => U (Exn.fwd_handlerVals B T))
    (fun h₁ _ => U (fwd_trapInstrs B T h₁))
    (fun _ => U (fwd_trapLabel B T))
    (fun _ => U (fwd_trapHandler B T))
    (fun _ => U (fwd_trapFrame B T))
    h

/-- **Family V's interfaces give `Open4.vector`**: `Vec.fwd_vector` proves every `VectorStep`
from `VecTyping`, `VecAgree` and `FloatTyping` (the last proved, `Floats.floatTyping_simEnv`). -/
theorem open4Vector_of_agree {B : Builtins} {hn : H → String} {P : Numerics.Profile}
    (T : TypingFacts (simEnv B) hn) (Ty : Vec.VecTyping (simEnv B)) (Ag : Vec.VecAgree (simEnv B) P)
    (s : Store H) (f : Frame) (is is' : List Admin) (h : VectorStep P is is')
    (_ : ∃ i, Admin.plain i ∈ is ∧ VecArith i = true) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  Vec.simEnv_fwd_vector B T Ty Ag (Floats.floatTyping_simEnv B) h

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
