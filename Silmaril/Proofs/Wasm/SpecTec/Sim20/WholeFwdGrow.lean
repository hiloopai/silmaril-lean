module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowFwd

/-!
# A restricted forward 2.0 half, at builtins that grow

`Task.wholeStepValid` (forward and backward, all typed configurations) is refuted
(`not_wholeStepValid`): the wasm-2.0 script has no `Step/ctxt-instrs` (V2's deviation 1), so
`NOP NOP` is stuck. Excluding `ctxt-instrs` is not enough on its own: `UNREACHABLE` reduces to
`TRAP` in V2 by `Step.pure` alone, with no context rule, and the script cannot lift that step,
because `Step/pure` types its code as `instr*` and `TRAP` is not an `instr`
(`not_fwd_noCtxt`). So a true forward statement has to restrict the redex further.

This module states and proves one for the redexes the script handles at the top of the code,
without any structural rule: the four growth steps.

* `GrowStep20 P`: V2's `tableGrowSucceed`, `tableGrowFail`, `memoryGrowSucceed` and
  `memoryGrowFail`, with V2's own premises (`GrowStep20.step` embeds it in `Step`). No context rule
  is involved.
* `GrowLike20 P B`: `B` extends the spec's numerics (`IntB`, `FloatB P`), answers no inert
  primitive, and answers `$growtable`/`$growmemory` exactly as V2 grows (`GrowAnswers20` and
  `GrowCalls20`). `growB P` is such (`growLike20_growB`).
* `fwd_growStep20`: at such builtins, every `GrowStep20` step from a configuration whose image is
  typed, and whose memories are whole pages, is a SpecTec step between the images. The match is
  exact (the successor is V2's own), and it covers both outcomes of growth.
* **`Task.wholeStepGrow20`** (proved, `wholeStepGrow20`): at every injective encoding, host and
  spec profile there are `GrowLike20` builtins at which the forward half holds on `GrowStep20`
  and the backward half holds on every `GoodW` configuration.

`WholePages` is a real side condition, not a convenience. `memory.grow-succeed` returns
`|bytes| / (64 · $Ki)` converted from `rat` to `nat`, which is undefined unless the quotient is
whole (`pages_of_cvt`), while V2's `MemInst.pages` truncates.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

variable {H : Type}

/-! ## The fragment -/

/-- Every memory of the store has a whole number of pages. -/
def WholePages (s : Store H) : Prop := ∀ mi ∈ s.mems, mi.bytes.size % 65536 = 0

/-- **The growth steps of V2**, at the top of the code: V2's four `grow` constructors, with their
premises. No structural rule (`ctxt-instrs`, `ctxt-label`, `ctxt-frame`) is involved. -/
inductive GrowStep20 (P : Profile) : Config H → Config H → Prop where
  | tableGrowSucceed {s : Store H} {f : Frame} {x : TableIdx} {n : BitVec 32} {r : Ref}
      {a : TableAddr} {ti ti' : TableInst} (ha : f.module.tableAddr? x = some a)
      (ht : s.tableInst? a = some ti) (hg : ti.grow? n.toNat r = some ti')
      (hp : P.growMaySucceed .table a ti.refs.length n.toNat) :
      GrowStep20 P ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩
        ⟨s.setTableInst a ti', f, [constI32 (BitVec.ofNat 32 ti.refs.length)]⟩
  | tableGrowFail {s : Store H} {f : Frame} {x : TableIdx} {n : BitVec 32} {r : Ref}
      {a : TableAddr} {ti : TableInst} (ha : f.module.tableAddr? x = some a)
      (ht : s.tableInst? a = some ti)
      (hp : P.growMayFail .table a ti.refs.length n.toNat ∨ ti.grow? n.toNat r = none) :
      GrowStep20 P ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩
        ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩
  | memoryGrowSucceed {s : Store H} {f : Frame} {n : BitVec 32} {a : MemAddr}
      {mi mi' : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
      (hm : s.memInst? a = some mi) (hg : mi.grow? n.toNat = some mi')
      (hp : P.growMaySucceed .memory a mi.pages n.toNat) :
      GrowStep20 P ⟨s, f, [constI32 n, .plain .memoryGrow]⟩
        ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩
  | memoryGrowFail {s : Store H} {f : Frame} {n : BitVec 32} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hp : P.growMayFail .memory a mi.pages n.toNat ∨ mi.grow? n.toNat = none) :
      GrowStep20 P ⟨s, f, [constI32 n, .plain .memoryGrow]⟩
        ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩

/-- Every growth step is a V2 step. -/
theorem GrowStep20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : GrowStep20 P c c') : Step P host c c' := by
  cases h with
  | tableGrowSucceed ha ht hg hp => exact .tableGrowSucceed ha ht hg hp
  | tableGrowFail ha ht hp => exact .tableGrowFail ha ht hp
  | memoryGrowSucceed ha hm hg hp => exact .memoryGrowSucceed ha hm hg hp
  | memoryGrowFail ha hm hp => exact .memoryGrowFail ha hm hp

/-! ## Builtins that grow as V2 does -/

/-- **Builtins like `growB`**: the spec's numerics, no inert primitive, and V2's growth answered
in both directions. -/
structure GrowLike20 (P : Profile) (B : Builtins) : Prop where
  int : Sim.IntNumeric.IntB B
  float : Sim.Floats.FloatB P B
  inert : InertEnv (simEnv20 B)
  answers : GrowAnswers20 B
  calls : GrowCalls20 B

theorem growLike20_growB (P : Profile) : GrowLike20 P (growB P) :=
  ⟨intB_growB P, floatB_growB P, inertEnv20_growB P, growAnswers20_growB P, growCalls20_growB P⟩

/-! ## The forward half on the fragment -/

/-- A memory found at an address is a memory of the store. -/
theorem mem_of_memInst {s : Store H} {a : Nat} {mi : MemInst} (h : s.memInst? a = some mi) :
    mi ∈ s.mems :=
  List.mem_of_getElem? h

/-- **The forward half on growth steps**: at builtins answering V2's growth, every V2 growth step
from a configuration whose image is typed and whose memories are whole pages is a step of the
wasm-2.0 script, to the image of V2's own successor. -/
theorem fwd_growStep20 {B : Builtins} {hn : H → String} {P : Profile} (hG : GrowCalls20 B)
    {c c' : Config H} (hc : Typed20 (simEnv20 B) hn c) (hw : WholePages c.store)
    (h : GrowStep20 P c c') : SStepB (simEnv20 B) (configV hn c) (configV hn c') := by
  have hz := typedV_state_of_typed20 hc
  cases h with
  | tableGrowSucceed ha ht hg _ => exact sstepB_of_fires20 (fires_tableGrowSucceed hG hz ha ht hg)
  | tableGrowFail _ _ _ => exact sstepB_of_fires20 (fires_tableGrowFail hz)
  | memoryGrowSucceed ha hm hg _ =>
    exact sstepB_of_fires20 (fires_memGrowSucceed hG hz ha hm hg (hw _ (mem_of_memInst hm)))
  | memoryGrowFail _ _ _ => exact sstepB_of_fires20 (fires_memGrowFail hz)

/-! ## The target -/

/-- **A two-sided 2.0 statement at builtins that grow** (proved below): there are `GrowLike20`
builtins at which
* forward: every V2 growth step (`GrowStep20`) from a typed configuration with whole pages is a
  SpecTec step between the images;
* backward: every SpecTec step from the image of a `GoodW` configuration is the image of a V2
  step. -/
def Task.wholeStepGrow20 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
      GrowLike20 (Profile.spec nd r) B ∧
      (∀ c c' : Config H, Typed20 (simEnv20 B) hn c → WholePages c.store →
        GrowStep20 (Profile.spec nd r) c c' →
        SStepB (simEnv20 B) (configV hn c) (configV hn c')) ∧
      (∀ (c : Config H) (w : Value), GoodW c → SStepB (simEnv20 B) (configV hn c) w →
        ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c')

/-- **`Task.wholeStepGrow20` holds**, at `growB`. -/
theorem wholeStepGrow20 : Task.wholeStepGrow20 := by
  intro H hn _ host nd r
  refine ⟨growB (Profile.spec nd r), growLike20_growB _, fun c c' hc hw h => ?_,
    fun c w hg hs => wholeStepBwdW_growB nd r c w hg hs⟩
  exact fwd_growStep20 (growCalls20_growB _) hc hw h

/-! ## Excluding `ctxt-instrs` alone is not enough -/

/-- **A forward half restricted only to steps without `ctxt-instrs` is false**, at every builtins:
V2's `UNREACHABLE ~> TRAP` is `Step.pure` (no context rule), from a typed configuration, and the
script has no step there. -/
theorem not_fwd_noCtxt (B : Builtins) (hn : H → String) (P : Profile) :
    ¬ ∀ (s : Store H) (f : Frame) (is is' : List Admin), Typed20 (simEnv20 B) hn ⟨s, f, is⟩ →
      PureStep P is is' → SStepB (simEnv20 B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) :=
  fun h => stuck_unreachable B _ _ (h {} {} _ _ (typed20_unreachable B hn) .unreachable)

end Silmaril.Wasm.SpecTec.Sim20.Whole
