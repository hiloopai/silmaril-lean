module

public import Silmaril.Wasm.Wasmi.Runs.Defs
public import Silmaril.Wasm.Wasmi.RoundFree.Thms
public import Silmaril.Proofs.Wasm.Wasmi.Runs.Obs

/-!
# Every run of the wasmi 0.40.0 model on the rounding witness calls

Proofs in `Silmaril.Proofs.Wasm.Wasmi.Runs.{Generic,Quirk,Inv,Obs}`. the wasmi results on the
harness's 16 signalling-NaN failures were single runs (`Observed.wasmi_returns`,
`Observed.model_returns`), and its every-run results covered Core's value results only
(`Observed.core_returns_iff`). Here both models' **full behaviour sets** of a witness call,
traps, exceptions and divergence included:

* `quirk_steps`: a quirk step starts at a pending quirk redex and goes to `fire` of the code,
  so quirk steps are deterministic (`ctx_quirk_inv`; the first sanity lemma of track wasmi);
* `core_obs`: Core 3.0 has exactly `returns [t.const z]` for the `z` the profile allows;
* `model_obs`: the wasmi 0.40.0 model has exactly `returns [t.const z]` for the `z` that
  `wUnOpP` allows: the input on a NaN, Core's results otherwise;
* **`witness_obs`**: on each of the 16 witness calls the model's behaviour set is
  `{returns [t.const x]}`, the input: **no other observation**; `witness_disjoint`: it shares no
  behaviour with Core; `sixteen_full`: both, for all 16;
* `agree_obs`: away from the quirk (a non-NaN input), the model's and Core's behaviour sets are
  equal;
* `refines_iff`, `refines_iff_spec`, `refines_iff_canonical`: the model's behaviour set on a
  witness call is contained in Core's exactly when the model's result is a Core result: at the
  spec's NaN policy, exactly when the input is not a signalling NaN; at the canonical one,
  exactly when it is not a NaN other than `posNaN`. `harness_refines`: on the vendored
  testsuite's rounding inputs (`HarnessIn`, a textual audit), the calls on which the model's
  behaviour set is not contained in Core's are exactly the 16 of the harness;
* `known_full`: with `RoundFree.repro_obs` (#2046 in the 0.40.0 model returns `7` and nothing
  else) and `Wasmi.wasmi_f`/`Wasmi.core_f`, both reproducers are now known as full behaviour
  sets in every model involved.

The generic statements (`Silmaril.Proofs.Wasm.Wasmi.Runs.RoundFn.model_behaviours`,
`core_behaviours`) hold for any store with a function `local.get 0; t.op` and every host.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.Runs

open Silmaril Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi.Observed
open Silmaril.Proofs.Wasm.Wasmi.Observed (roundFn_store isRound_of_mem sNaN_facts unOp_ne)

variable {H : Type}

/-- **Quirk steps are deterministic**: from a pending redex, to the fired code. -/
theorem quirk_steps {c c' : Config H} (h : Variant.Ctx Quirk c c') :
    pending c.code = true ∧ c' = ⟨c.store, c.frame, fire c.code⟩ :=
  Silmaril.Proofs.Wasm.Wasmi.Runs.ctx_quirk_inv h

/-- **Core 3.0's full behaviour set** on a witness call. -/
theorem core_obs (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    (x : FloatValue t) :
    Core.obs P roundPt (roundCall t op x) =
      {b | ∃ z, floatUnOpP P t op x z ∧ b = .returns [fval t z]} := by
  obtain ⟨R⟩ := roundFn_store (t := t) hop
  exact Silmaril.Proofs.Wasm.Wasmi.Runs.RoundFn.core_behaviours R x

/-- **The wasmi 0.40.0 model's full behaviour set** on a witness call. -/
theorem model_obs (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    (x : FloatValue t) :
    Observed.obs P roundPt (roundCall t op x) =
      {b | ∃ z, wUnOpP P t op x z ∧ b = .returns [fval t z]} := by
  obtain ⟨R⟩ := roundFn_store (t := t) hop
  exact Silmaril.Proofs.Wasm.Wasmi.Runs.RoundFn.model_behaviours R x

/-- On a NaN input the model returns the input and does nothing else. -/
theorem nan_obs (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    {x : FloatValue t} (hx : isNaNB t x = true) :
    Observed.obs P roundPt (roundCall t op x) = {.returns [fval t x]} := by
  rw [model_obs P hop]
  ext b
  simp [wUnOpP, isRound_of_mem hop, hx]

/-- **No other observation**: on each witness call the model returns the input, and that is
its only behaviour. -/
theorem witness_obs (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    {x : FloatValue t} (hx : x ∈ sNaNs t) :
    Observed.obs P roundPt (roundCall t op x) = {.returns [fval t x]} :=
  nan_obs P hop (sNaN_facts hx).2.1

/-- **On each witness call the model and Core share no behaviour.** -/
theorem witness_disjoint (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    {x : FloatValue t} (hx : x ∈ sNaNs t) :
    Disjoint (Observed.obs P roundPt (roundCall t op x)) (Core.obs P roundPt (roundCall t op x)) := by
  rw [witness_obs P hop hx, core_obs P hop, Set.disjoint_singleton_left]
  rintro ⟨z, hz, he⟩
  have hzx : z = x := by
    simp only [Behaviour.returns.injEq, List.cons.injEq, and_true, fval, Val.num.injEq] at he
    cases he
    rfl
  exact unOp_ne (isRound_of_mem hop) (sNaN_facts hx).1 hz hzx

/-- **The 16 harness failures, as full behaviour sets.** -/
theorem sixteen_full (P : Profile) :
    ∀ t : FloatType, ∀ op ∈ roundOps, ∀ x ∈ sNaNs t,
      Observed.obs P roundPt (roundCall t op x) = {.returns [fval t x]} ∧
        Disjoint (Observed.obs P roundPt (roundCall t op x)) (Core.obs P roundPt (roundCall t op x)) :=
  fun _ _ hop _ hx => ⟨witness_obs P hop hx, witness_disjoint P hop hx⟩

/-- **Away from the quirk the two behaviour sets are equal.** -/
theorem agree_obs (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    {x : FloatValue t} (hx : isNaNB t x = false) :
    Observed.obs P roundPt (roundCall t op x) = Core.obs P roundPt (roundCall t op x) := by
  rw [model_obs P hop, core_obs P hop]
  simp [wUnOpP, hx]

theorem floatUnOpP_self (P : Profile) (t : FloatType) (op : FloatUnOp) (x : FloatValue t) :
    floatUnOpP P t op x (floatUnOp t op x) := by
  unfold floatUnOpP
  cases P.nan with
  | spec => exact floatUnOpRel_self t op x
  | canonical => rfl

/-- **The model refines Core on a witness call exactly when its result is a Core result.** -/
theorem refines_iff (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    (x : FloatValue t) :
    Observed.obs P roundPt (roundCall t op x) ⊆ Core.obs P roundPt (roundCall t op x) ↔
      Behaviour.returns [fval t (wUnOp t op x)] ∈ Core.obs P roundPt (roundCall t op x) := by
  cases hx : isNaNB t x
  · have hw : wUnOp t op x = floatUnOp t op x := by simp [wUnOp, hx]
    rw [agree_obs P hop hx, hw, core_obs P hop]
    exact iff_of_true subset_rfl ⟨_, floatUnOpP_self P t op x, rfl⟩
  · have hw : wUnOp t op x = x := by simp [wUnOp, hx, isRound_of_mem hop]
    rw [nan_obs P hop hx, hw, Set.singleton_subset_iff]

/-- **At the spec's NaN policy the model refines Core on a witness call exactly when the input
is not a signalling NaN.** -/
theorem refines_iff_spec (P : Profile) (hP : P.nan = .spec) {t : FloatType} {op : FloatUnOp}
    (hop : op ∈ roundOps) (x : FloatValue t) :
    Observed.obs P roundPt (roundCall t op x) ⊆ Core.obs P roundPt (roundCall t op x) ↔
      ¬ Silmaril.Proofs.Wasm.Wasmi.Observed.SNaN t x := by
  rw [refines_iff P hop, ← disagree_iff_spec P hP hop, not_not]

/-- **At the canonical NaN policy the model refines Core on a witness call exactly when the
input is not a NaN other than `posNaN`.** -/
theorem refines_iff_canonical (P : Profile) (hP : P.nan = .canonical) {t : FloatType}
    {op : FloatUnOp} (hop : op ∈ roundOps) (x : FloatValue t) :
    Observed.obs P roundPt (roundCall t op x) ⊆ Core.obs P roundPt (roundCall t op x) ↔
      ¬ (isNaNB t x = true ∧ x ≠ posNaN t) := by
  rw [refines_iff P hop, ← disagree_iff_canonical P hP hop, not_not]

/-- **On the testsuite's rounding inputs, the calls where the model's behaviour set leaves
Core's are exactly the 16 of the harness** (spec NaN policy). -/
theorem harness_refines (P : Profile) (hP : P.nan = .spec) :
    ∀ t : FloatType, ∀ op ∈ roundOps, ∀ x : FloatValue t, HarnessIn t x →
      (¬ Observed.obs P roundPt (roundCall t op x) ⊆ Core.obs P roundPt (roundCall t op x) ↔
        x ∈ sNaNs t) := by
  intro t op hop x hx
  rw [refines_iff P hop]
  exact harness_spec P hP t op hop x hx

/-- **Both reproducers as full behaviour sets.** Issue #2046: the 0.40.0 model and Core return
`7` and nothing else, wasmi 2.0.0 returns `5` and nothing else. The signalling-NaN witnesses:
the 0.40.0 model returns the input and nothing else, disjoint from Core. -/
theorem known_full (P : Profile) :
    (Observed.obs P Wasmi.reproPt Wasmi.reproCall = {.returns [Val.i32 7]} ∧
      Core.obs P Wasmi.reproPt Wasmi.reproCall = {.returns [Val.i32 7]} ∧
      Wasmi.obs P Wasmi.reproPt Wasmi.reproCall = {.returns [Val.i32 5]}) ∧
    ∀ t : FloatType, ∀ op ∈ roundOps, ∀ x ∈ sNaNs t,
      Observed.obs P roundPt (roundCall t op x) = {.returns [fval t x]} ∧
        Disjoint (Observed.obs P roundPt (roundCall t op x)) (Core.obs P roundPt (roundCall t op x)) :=
  ⟨⟨RoundFree.repro_obs P, Wasmi.core_f P, Wasmi.wasmi_f P⟩, sixteen_full P⟩

end Silmaril.Wasm.Wasmi.Runs
