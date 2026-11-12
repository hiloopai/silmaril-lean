module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.TypedD
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# Round 7, memory SIMD: the predicate of the backward recursion on the extended domain

Round 6 runs its backward recursion under `Round6.Target.NoCastV`: round 5's `ReadValidS` and no
cast redex. `ReadValidS` asks the active code to be in `Round4.AdminsBnd`, which rejects the four
memory SIMD instructions, so it fails on the extended domain `BoundedSelM`. This file gives its
`M` analogue:

* `ReadValidSM`: `ReadValidS` with `AdminsBndM` for `Round4.AdminsBnd`;
* `NoCastVM`: `ReadValidSM` and no cast redex;
* `noCastVM_closed`: **`NoCastVM` is closed under SpecTec's context decompositions** (the
  `closed` field of `OpenRM` at `V := NoCastVM`);
* `noCastVM_entry`: **`NoCastVM` holds at every valid `BoundedSelM` configuration without a cast
  redex** (the `entry` field);
* `readValidS_of_readValidSM`, `noCastV_of_noCastVM`: off memory SIMD code they are round 6's
  predicates, so round 6's per-rule leaves (stated under `NoCastV`) apply there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round6.MemSimd (AdminsMS)
open Round6.Target (CastRedex CtxClosedVals not_castRedex_mid not_castRedex_label
  not_castRedex_handler not_castRedex_frame)
open Round5.Read (codeSeg codeSeg_append codeSeg_of_ok)

variable {H : Type}

/-- **`Round5.Read.ReadValidS` admitting memory SIMD code**: the store bounds, index resolution
and reference liveness (`Round5.Bwd.ReadValidR`), the aggregate segment indices, the active code
in `AdminsBndM`, and a bounded frame module. -/
structure ReadValidSM (c : Config H) : Prop where
  /-- Store bounds, index resolution and reference liveness. -/
  r : Round5.Bwd.ReadValidR c
  /-- The aggregate instructions' segment indices resolve. -/
  seg : codeSeg c.store c.frame c.code
  /-- The active code is in the extended bounded fragment (memory SIMD admitted). -/
  bnd : AdminsBndM c.code
  /-- The frame's module is bounded. -/
  frame : Round4.ModuleBnd c.frame.module

/-- **`ReadValidSM` and no cast redex**: the `M` analogue of `Round6.Target.NoCastV`. -/
def NoCastVM (c : Config H) : Prop := ReadValidSM c ∧ ¬ CastRedex c.code

/-- `ReadValidS` implies `ReadValidSM`. -/
theorem readValidSM_of_readValidS {c : Config H} (h : Round5.Read.ReadValidS c) :
    ReadValidSM c :=
  ⟨h.r, h.seg, adminsBndM_of _ h.bnd, h.frame⟩

/-- Off memory SIMD code, `ReadValidSM` is `ReadValidS`. -/
theorem readValidS_of_readValidSM {c : Config H} (h : ReadValidSM c) (hm : AdminsMS c.code) :
    Round5.Read.ReadValidS c :=
  ⟨h.r, h.seg, adminsBnd_of _ h.bnd hm, h.frame⟩

/-- Off memory SIMD code, `NoCastVM` is round 6's `NoCastV`. -/
theorem noCastV_of_noCastVM {c : Config H} (h : NoCastVM c) (hm : AdminsMS c.code) :
    Round6.Target.NoCastV c :=
  ⟨readValidS_of_readValidSM h.1 hm, h.2⟩

/-- **A valid `BoundedM` configuration satisfies `ReadValidSM`** (`Round5.Read.readValidS_of_bounded`
with `BoundedM`). -/
theorem readValidSM_of_boundedM {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hb : BoundedM c) : ReadValidSM c := by
  have hr := Round5.Bwd.readValidR_of_configOk hc hb.store
  obtain ⟨C, hst, hcode⟩ := hc
  exact ⟨hr, codeSeg_of_ok hst.1 (Round4Int.ctxRes_of_stateOk hst) (StateOk.types hst) hcode,
    hb.code, hb.frame⟩

/-- **`ReadValidSM` survives the context decompositions** of the backward recursion. -/
theorem readValidSM_ctxClosed : Round4Read.CtxClosed (ReadValidSM (H := H)) where
  mid s f a b c h := ⟨Round5.Bwd.readValidR_ctxClosed.mid s f a b c h.r,
    (codeSeg_append.1 (codeSeg_append.1 h.seg).1).2,
    (adminsBndM_append.1 (adminsBndM_append.1 h.bnd).1).2, h.frame⟩
  label s f n cont body h :=
    ⟨Round5.Bwd.readValidR_ctxClosed.label s f n cont body h.r, h.seg.1, h.bnd.1.2, h.frame⟩
  handler s f n cs body h :=
    ⟨Round5.Bwd.readValidR_ctxClosed.handler s f n cs body h.r, h.seg.1, h.bnd.1, h.frame⟩
  frame s f fi n body h :=
    ⟨Round5.Bwd.readValidR_ctxClosed.frame s f fi n body h.r, h.seg.1, h.bnd.1.2, h.bnd.1.1⟩

/-- **`NoCastVM` is closed under SpecTec's context decompositions**: the `closed` field of
`OpenRM` at `V := NoCastVM`. -/
theorem noCastVM_closed : CtxClosedVals (NoCastVM (H := H)) where
  mid s f vs b c h := ⟨readValidSM_ctxClosed.mid s f (vals vs) b c h.1, not_castRedex_mid h.2⟩
  label s f n cont body h :=
    ⟨readValidSM_ctxClosed.label s f n cont body h.1, not_castRedex_label h.2⟩
  handler s f n cs body h :=
    ⟨readValidSM_ctxClosed.handler s f n cs body h.1, not_castRedex_handler h.2⟩
  frame s f fi n body h :=
    ⟨readValidSM_ctxClosed.frame s f fi n body h.1, not_castRedex_frame h.2⟩

/-- **`NoCastVM` holds at every valid `BoundedSelM` source without a cast redex**: the `entry`
field of `OpenRM` at `V := NoCastVM`. -/
theorem noCastVM_entry (c : Config H) (ts : List CValType) (hc : ConfigOk c ts)
    (hb : BoundedSelM c) (hx : ¬ CastRedex c.code) : NoCastVM c :=
  ⟨readValidSM_of_boundedM hc hb.1.1, hx⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
