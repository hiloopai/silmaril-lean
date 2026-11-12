module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.RMCode.Image

/-!
# Round 8, memory SIMD: the named host store keeps the validity facts

`noCastV_hostC`: round 6's `NoCastV` (`Round5.Read.ReadValidS` and no cast redex) moves from `c`
to `hostC hn c`. The validity facts read the store's tables, memories, segments, aggregates and
exception instances, and the function instances only through their number (`refLive`), which
`hostifyS` keeps.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMCode

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String}

theorem storeOk_hostifyS {s : Store H} (h : Integrate.StoreOk s) :
    Integrate.StoreOk (hostifyS hn s) :=
  ⟨h.tables, ⟨h.aggs.arrays, h.aggs.elems, h.aggs.datas⟩, h.mems⟩

theorem idxOk_hostifyS {s : Store H} {f : Frame} {i : Instr} (h : Round4Read.Instr.IdxOk s f i) :
    Round4Read.Instr.IdxOk (hostifyS hn s) f i := by
  cases i <;> exact h

theorem segOk_hostifyS {s : Store H} {f : Frame} {i : Instr} (h : Round5.Read.Instr.SegOk s f i) :
    Round5.Read.Instr.SegOk (hostifyS hn s) f i := by
  cases i <;> exact h

theorem refLive_hostifyS {s : Store H} : ∀ {r : Ref}, Round5.Bwd.refLive s r → Round5.Bwd.refLive (hostifyS hn s) r
  | .func a, h => by
    simp only [Round5.Bwd.refLive, hostifyS, List.getElem?_map, Option.isSome_map] at h ⊢
    exact h
  | .extern r, h => refLive_hostifyS (r := r) h
  | .null, h | .i31 _, h | .struct _, h | .array _, h | .exn _, h | .host _, h => h

mutual
theorem adminIdx_hostifyS {s : Store H} {f : Frame} :
    ∀ {a : Admin}, Round4Read.adminIdx s f a → Round4Read.adminIdx (hostifyS hn s) f a
  | .plain _, h => idxOk_hostifyS h
  | .label _ _ b, h => codeIdx_hostifyS (l := b) h
  | .handler _ _ b, h => codeIdx_hostifyS (l := b) h
  | .frame _ _ b, h => codeIdx_hostifyS (l := b) h
  | .ref _, h | .callRefType _, h | .returnCallRefType _, h | .trap, h => h

theorem codeIdx_hostifyS {s : Store H} {f : Frame} :
    ∀ {l : List Admin}, Round4Read.codeIdx s f l → Round4Read.codeIdx (hostifyS hn s) f l
  | [], h => h
  | _ :: _, h => ⟨adminIdx_hostifyS h.1, codeIdx_hostifyS h.2⟩
end

mutual
theorem adminLive_hostifyS {s : Store H} :
    ∀ {a : Admin}, Round5.Bwd.adminLive s a → Round5.Bwd.adminLive (hostifyS hn s) a
  | .ref _, h => refLive_hostifyS h
  | .label _ _ b, h => codeLive_hostifyS (l := b) h
  | .handler _ _ b, h => codeLive_hostifyS (l := b) h
  | .frame _ _ b, h => codeLive_hostifyS (l := b) h
  | .plain _, h | .callRefType _, h | .returnCallRefType _, h | .trap, h => h

theorem codeLive_hostifyS {s : Store H} :
    ∀ {l : List Admin}, Round5.Bwd.codeLive s l → Round5.Bwd.codeLive (hostifyS hn s) l
  | [], h => h
  | _ :: _, h => ⟨adminLive_hostifyS h.1, codeLive_hostifyS h.2⟩
end

mutual
theorem adminSeg_hostifyS {s : Store H} {f : Frame} :
    ∀ {a : Admin}, Round5.Read.adminSeg s f a → Round5.Read.adminSeg (hostifyS hn s) f a
  | .plain _, h => segOk_hostifyS h
  | .label _ _ b, h => codeSeg_hostifyS (l := b) h
  | .handler _ _ b, h => codeSeg_hostifyS (l := b) h
  | .frame _ _ b, h => codeSeg_hostifyS (l := b) h
  | .ref _, h | .callRefType _, h | .returnCallRefType _, h | .trap, h => h

theorem codeSeg_hostifyS {s : Store H} {f : Frame} :
    ∀ {l : List Admin}, Round5.Read.codeSeg s f l → Round5.Read.codeSeg (hostifyS hn s) f l
  | [], h => h
  | _ :: _, h => ⟨adminSeg_hostifyS h.1, codeSeg_hostifyS h.2⟩
end

/-- **`ReadValidS` moves to the named host store.** -/
theorem readValidS_hostC {c : Config H} (h : Round5.Read.ReadValidS c) :
    Round5.Read.ReadValidS (hostC hn c) :=
  ⟨⟨⟨storeOk_hostifyS h.r.read.store, codeIdx_hostifyS h.r.read.idx⟩,
      codeLive_hostifyS h.r.live⟩, codeSeg_hostifyS h.seg, h.bnd, h.frame⟩

/-- **Round 6's `NoCastV` moves to the named host store.** -/
theorem noCastV_hostC {c : Config H} (h : Round6.Target.NoCastV c) :
    Round6.Target.NoCastV (hostC hn c) :=
  ⟨readValidS_hostC h.1, h.2⟩

end Silmaril.Wasm.SpecTec.Sim.Round8.RMCode
