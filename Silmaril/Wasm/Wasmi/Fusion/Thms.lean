module

public import Silmaril.Wasm.Wasmi.Fusion.Defs
public import Silmaril.Proofs.Wasm.Wasmi.Fusion.Run

/-!
# The select fusion of wasmi 2.0.0, as the harness probes observe it

Proofs in `Silmaril.Proofs.Wasm.Wasmi.Fusion.Run`. The probe `issue2046.wast` of the conformance
harness runs the reproducer of issue #2046 and variants of it on wasmi 2.0.0. For `f 5 1`
(spec results `7`, `7`, `5`, `5`) it observes:

| body | spec / Core 3.0 | `Wasmi.obs` (`fuse`) | `obsW` (`fuseW`) | wasmi 2.0.0 (probe) |
|---|---|---|---|---|
| `reproBody` (`0 != b`) | `7` | `5` | `5` | `5` |
| `swapBody` (`b != 0`) | `7` | `7` | `5` | `5` |
| `eqBody` (`0 == b`) | `5` | `5` | `7` | `7` |
| `eqzBody` (`eqz b`) | `5` | `5` | `7` | `7` |

The first three columns are theorems, at every profile, each a single behaviour (`returns`
and nothing else):

* `core_variants`: Core 3.0;
* `model_blind`: the model of `Silmaril.Wasm.Wasmi` is Core on the three variants, because they
  have no `fuse` shape (`Wasmi.obs_of_patFree`). So the probe observes behaviours of
  wasmi 2.0.0 that the model does not have: **the model is incomplete** for wasmi 2.0.0.
  `LooseAll.wasmi200_le` and `LooseAll.transfer` speak about the model, so they do not cover
  these runs of the implementation;
* `wider_variants`, `wider_repro`: the wider translation `fuseW` has exactly the probe's
  observations on all four.

The last column is the harness's observation (`tools/wasm-conformance/probes/`), recorded here,
not proved. Whether `fuseW` is wasmi 2.0.0's whole fusion is not known: the probes are a
sample of shapes, not a derivation from wasmi's translator. New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.Fusion

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Proofs.Wasm.Wasmi.Fusion

/-- **Core 3.0 on the probe's variants**, every profile: `7`, `5`, `5` and nothing else. -/
theorem core_variants (P : Numerics.Profile) :
    Core.obs P (ptOf swapBody) reproCall = {.returns [Val.i32 7]} ∧
      Core.obs P (ptOf eqBody) reproCall = {.returns [Val.i32 5]} ∧
      Core.obs P (ptOf eqzBody) reproCall = {.returns [Val.i32 5]} :=
  ⟨behaviours_of swap_checks P, behaviours_of eq_checks P, behaviours_of eqz_checks P⟩

/-- **The model of `Silmaril.Wasm.Wasmi` does not see the variants**: on each its observations are
Core's. -/
theorem model_blind (P : Numerics.Profile) :
    Wasmi.obs P (ptOf swapBody) reproCall = {.returns [Val.i32 7]} ∧
      Wasmi.obs P (ptOf eqBody) reproCall = {.returns [Val.i32 5]} ∧
      Wasmi.obs P (ptOf eqzBody) reproCall = {.returns [Val.i32 5]} := by
  rw [Wasmi.obs_of_patFree P swap_patFree, Wasmi.obs_of_patFree P eq_patFree,
    Wasmi.obs_of_patFree P eqz_patFree]
  exact core_variants P

/-- **The wider model on the variants**: `5`, `7`, `7`, as the probe observes. -/
theorem wider_variants (P : Numerics.Profile) :
    obsW P (ptOf swapBody) reproCall = {.returns [Val.i32 5]} ∧
      obsW P (ptOf eqBody) reproCall = {.returns [Val.i32 7]} ∧
      obsW P (ptOf eqzBody) reproCall = {.returns [Val.i32 7]} := by
  refine ⟨?_, ?_, ?_⟩
  · show Core.obs P (fuseStoreW (storeOf swapBody), _) reproCall = _
    rw [fuseStoreW_swap]
    exact behaviours_of swapW_checks P
  · show Core.obs P (fuseStoreW (storeOf eqBody), _) reproCall = _
    rw [fuseStoreW_eq]
    exact behaviours_of eqW_checks P
  · show Core.obs P (fuseStoreW (storeOf eqzBody), _) reproCall = _
    rw [fuseStoreW_eqz]
    exact behaviours_of eqzW_checks P

/-- **The wider model on the reproducer** is the model of `Silmaril.Wasm.Wasmi`: `5`. -/
theorem wider_repro (P : Numerics.Profile) :
    obsW P reproPt reproCall = {.returns [Val.i32 5]} := by
  show Core.obs P (fuseStoreW reproStore, _) reproCall = _
  rw [fuseStoreW_repro]
  exact Silmaril.Proofs.Wasm.Wasmi.wasmi_f P

/-- **The two models differ on each variant**, and agree on the reproducer. -/
theorem models_differ (P : Numerics.Profile) :
    obsW P reproPt reproCall = Wasmi.obs P reproPt reproCall ∧
      obsW P (ptOf swapBody) reproCall ≠ Wasmi.obs P (ptOf swapBody) reproCall ∧
      obsW P (ptOf eqBody) reproCall ≠ Wasmi.obs P (ptOf eqBody) reproCall ∧
      obsW P (ptOf eqzBody) reproCall ≠ Wasmi.obs P (ptOf eqzBody) reproCall := by
  obtain ⟨h₁, h₂, h₃⟩ := wider_variants P
  obtain ⟨m₁, m₂, m₃⟩ := model_blind P
  refine ⟨by rw [wider_repro, Wasmi.wasmi_f], ?_, ?_, ?_⟩
  · rw [h₁, m₁]; exact fun h => absurd (Set.singleton_eq_singleton_iff.mp h) (by decide)
  · rw [h₂, m₂]; exact fun h => absurd (Set.singleton_eq_singleton_iff.mp h) (by decide)
  · rw [h₃, m₃]; exact fun h => absurd (Set.singleton_eq_singleton_iff.mp h) (by decide)

end Silmaril.Wasm.Wasmi.Fusion
