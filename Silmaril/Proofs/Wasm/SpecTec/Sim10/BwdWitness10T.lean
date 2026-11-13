module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdWhole10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreNest10TEx

/-!
# A witness for the backward half with stores (track v10)

Round 4's `labelStoreCfg10` is a trapping `i32.store` under a label, over a store that holds one
memory and one function whose body is `i32.store`. Its image is not typed in `simEnv10`
(`not_typed10_labelStoreCfg`), so round 4's backward theorem `wholeStepBwd10B` says nothing
about it; it is typed in `simEnv10T`, and the corrected script steps from it
(`sstep10T_labelStoreCfg`).

* `goodV1_labelStoreCfg10`: it satisfies `GoodV1` (the store instruction's memory exists, the
  function has no result, there are no tables, and no `select` or `global.set` is active).
* **`bwd10S_labelStoreCfg`**: `wholeStepBwd10S` applies there: every `simEnv10T` step from its
  image is the image of a V1 step; in particular the step `sstep10T_labelStoreCfg` is.

* **`wholeStep10_bothT`**: round 4's `wholeStep10_both` with steps read in `simEnv10T`; the
  backward direction holds at every `GoodV1` configuration, the forward one still on the fragment
  typed in `simEnv10`.

`DeepMem` (an instruction at any depth of labels and frames) gives `SelOk` and `GSetOk` at code
without `select` and `global.set` (`selOk_of_not_deepMem`, `gsetOk_of_not_deepMem`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (labelStoreCfg10 labelStoreCfg10' storeFnMemStore10
  storeRedex10 sstep10T_labelStoreCfg not_typed10_labelStoreCfg)

variable {H : Type}

/-! ## Instructions at any depth -/

/-- `a` occurs in `code`, or in the body of a label or frame of `code`, at any depth. -/
inductive DeepMem (a : Admin) : List Admin → Prop where
  | here {code : List Admin} : a ∈ code → DeepMem a code
  | label {code body : List Admin} {n : Nat} {cont : V1.Expr} :
      .label n cont body ∈ code → DeepMem a body → DeepMem a code
  | frame {code body : List Admin} {n : Nat} {fi : Frame} :
      .frame n fi body ∈ code → DeepMem a body → DeepMem a code

theorem deepMem_of_active {code w : List Admin} (h : Active code w) {a : Admin} (ha : a ∈ w) :
    DeepMem a code := by
  induction h with
  | piece => exact .here (by simp [ha])
  | label hm _ ih => exact .label hm (ih ha)
  | frame hm _ ih => exact .frame hm (ih ha)

theorem deepMem_of_activeF {f f' : Frame} {code w : List Admin} (h : ActiveF f code f' w)
    {a : Admin} (ha : a ∈ w) : DeepMem a code := by
  induction h with
  | piece => exact .here (by simp [ha])
  | label hm _ ih => exact .label hm (ih ha)
  | frame hm _ ih => exact .frame hm (ih ha)

/-- Code with no `select` at any depth satisfies `SelOk`. -/
theorem selOk_of_not_deepMem {code : List Admin} (h : ¬ DeepMem (.source .select) code) :
    SelOk code := fun _ _ _ ha =>
  absurd (deepMem_of_active ha (by simp)) h

/-- Code with no `global.set` at any depth satisfies `GSetOk`. -/
theorem gsetOk_of_not_deepMem {s : Store H} {f : Frame} {code : List Admin}
    (h : ∀ x, ¬ DeepMem (.source (.globalSet x)) code) : GSetOk s f code :=
  fun _ _ x _ _ ha => absurd (deepMem_of_activeF ha (by simp)) (h x)

/-! ## The witness -/

theorem storeRedex10_eq : storeRedex10 = [.source (.intConst .i32 0), .source (.intConst .i32 0),
    .source (.intStore .i32 none ⟨0, 0⟩)] := rfl

/-- Nothing but values and a store occurs in `storeRedex10`, at any depth. -/
theorem deepMem_storeRedex10 {a : Admin} (h : DeepMem a storeRedex10) :
    a ∈ storeRedex10 := by
  cases h with
  | here h => exact h
  | label hm _ => simp [storeRedex10_eq] at hm
  | frame hm _ => simp [storeRedex10_eq] at hm

/-- What occurs in `labelStoreCfg10`'s code, at any depth. -/
theorem deepMem_labelStore10 {a : Admin} (h : DeepMem a labelStoreCfg10.code) :
    a = .label 0 [] storeRedex10 ∨ a ∈ storeRedex10 := by
  cases h with
  | here h => exact .inl (by simpa [labelStoreCfg10] using h)
  | label hm hb =>
    simp only [labelStoreCfg10, List.mem_singleton, Execution.Runtime.AdminInstr.label.injEq] at hm
    obtain ⟨-, -, rfl⟩ := hm
    exact .inr (deepMem_storeRedex10 hb)
  | frame hm _ => simp [labelStoreCfg10] at hm

/-- **`labelStoreCfg10` satisfies `GoodV1`.** -/
theorem goodV1_labelStoreCfg10 : GoodV1 labelStoreCfg10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [labelStoreCfg10, storeRedex10_eq, ResOkL10, ResOkA10, InstrResOk10,
      V1.Execution.frameMemory, StoreFix.memStoreFrame10, storeFnMemStore10]
  · refine ⟨fun fi hfi => ?_, fun t ht => ?_⟩
    · have e : fi = .wasm ⟨[], []⟩ {} ⟨⟨0⟩, [], [.intStore .i32 none ⟨0, 0⟩]⟩ := by
        simpa [labelStoreCfg10, storeFnMemStore10] using hfi
      subst e
      decide
    · simp [labelStoreCfg10, storeFnMemStore10] at ht
  · refine selOk_of_not_deepMem fun h => ?_
    rcases deepMem_labelStore10 h with h | h
    · cases h
    · simp [storeRedex10_eq] at h
  · refine gsetOk_of_not_deepMem fun x h => ?_
    rcases deepMem_labelStore10 h with h | h
    · cases h
    · simp [storeRedex10_eq] at h

/-- **The backward half with stores at `labelStoreCfg10`**: every step of the corrected script
from its image is the image of a V1 step. Round 4's `wholeStepBwd10B` does not apply there, since
the image is not typed in `simEnv10`. -/
theorem bwd10S_labelStoreCfg (host : HostSemantics Empty) (nd : Bool) (r : RelaxedChoice)
    {w : Value} (hs : SStepB (simEnv10T (fwdB10 nd r)) (configV Empty.elim labelStoreCfg10) w) :
    ∃ c', w = configV Empty.elim c' ∧ Step host labelStoreCfg10 c' :=
  wholeStepBwd10S goodV1_labelStoreCfg10 hs

/-- **Non-vacuity**: at `labelStoreCfg10`, the image is untyped in `simEnv10`, the corrected script
steps, and the step reads back as a V1 step. -/
theorem bwd10S_labelStoreCfg_nonvacuous (host : HostSemantics Empty) (nd : Bool)
    (r : RelaxedChoice) :
    ¬ Typed10 (simEnv10 (fwdB10 nd r)) Empty.elim labelStoreCfg10 ∧
      SStepB (simEnv10T (fwdB10 nd r)) (configV Empty.elim labelStoreCfg10)
        (configV Empty.elim labelStoreCfg10') ∧
      ∃ c', configV Empty.elim labelStoreCfg10' = configV Empty.elim c' ∧
        Step host labelStoreCfg10 c' :=
  ⟨not_typed10_labelStoreCfg _, sstep10T_labelStoreCfg _,
    bwd10S_labelStoreCfg host nd r (sstep10T_labelStoreCfg _)⟩

/-! ## Both halves in `simEnv10T` -/

/-- **Both halves of the 1.0 whole step in `simEnv10T`** at `fwdB10 nd r`: round 4's
`wholeStep10_both` with steps read in the corrected script. The backward direction is
`wholeStepBwd10S` (any `GoodV1` configuration); the typing in `simEnv10` (hence no stores),
`Plain10` and alignment are what the forward direction (`wholeStep10_fwdT`) still needs. Unlike
round 4's statement, `hn` need not be injective. -/
theorem wholeStep10_bothT {hn : H → String} {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {c : Config H} (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn c)
    (hg : GoodV1 c) (hpl : Plain10 c.code) (hal : MemsAligned10 c.store) (w : Value) :
    SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) w ↔
      ∃ c', w = configV hn c' ∧ Step host c c' := by
  constructor
  · exact wholeStepBwd10S hg
  · rintro ⟨c', rfl, h⟩
    exact StoreAgree.wholeStep10_fwdT hc hg hpl hal h

end Silmaril.Wasm.SpecTec.Sim10.Whole
