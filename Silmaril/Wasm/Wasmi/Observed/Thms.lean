module

public import Silmaril.Wasm.Wasmi.Observed.Defs
public import Silmaril.Wasm.Wasmi.Thms
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Core
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Witness
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Loose
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Gap
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Repro
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Quiet
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Complete

/-!
# The harness's wasmi divergences: disagreement with Core, and the loose models

Proofs in `Silmaril.Proofs.Wasm.Wasmi.Observed.{Nan,Run,Core,Witness,Loose,Gap}`.

**The 16 signalling-NaN failures** (`f32.wast`/`f64.wast` 2456-2518): for each rounding
operator `op` (`floor`, `ceil`, `trunc`, `nearest`), each float type `t` and each signalling
input `x ∈ sNaNs t`, the call `roundCall t op x` of the witness store, at **every** profile:

* `wasmi_returns`: the wasmi 0.40.0 model returns `x` unchanged (the observed `0xffa00000`);
* `core_returns_iff`: Core 3.0 returns exactly the results the profile allows for `t.op x`
  (every run, by the every-run program logic `Silmaril.Wasm.Logic.Hoare`), and `core_not`: never
  `x` itself;
* `disagree`: the safety sentence `φ t op x` ("no observation returns `x`") holds in Core and
  fails in the wasmi 0.40.0 model; `sixteen`: all 16 at once;
* `not_conformant`: the wasmi 0.40.0 model is not contained in Core.

**The loose models.** `Loose.core_le`, `Loose.wasmi_le`: Core and the wasmi 0.40.0 model refine
the loose model of wasmi 0.40.0, at every point (no host assumption: the variant changes no
function code); `Loose.transfer`; `Loose.witness`: on each witness the loose model returns both
`x` and a Core result. `LooseAll` admits Core, wasmi 0.40.0 and wasmi 2.0.0 (`LooseAll.core_le`,
`LooseAll.wasmi040_le`, `LooseAll.wasmi200_le`, the last for hosts parametric in function code)
and has the observations of both versions on both reproducers (`LooseAll.witnesses`).

**The version gap** (`global.wast:373`): `gap_core`, Core 3.0 instantiates `gapMod` at every
profile and host; `gap_wasmi`, wasmi's `instantiate?` refuses it.

**Which inputs the rounding quirk disagrees on.** `model_returns`: on every input `x` the model
returns `wUnOp t op x`. `disagree_iff_spec`: at the spec's NaN policy this result is outside
Core exactly when `x` is a signalling NaN (on a quiet NaN the spec allows the input back, since
every rounding operator maps a NaN to a NaN, `Proofs…Quiet.round_nan`); `disagree_iff_canonical`:
at the canonical NaN policy, exactly when `x` is a NaN other than `posNaN`. On the vendored
testsuite's rounding inputs (`HarnessIn`: its eight NaN inputs `nanIns`, or a non-NaN), this
gives `harness_spec`, the disagreements are exactly the 16 signalling cases, and
`harness_canonical`, 24 at the canonical policy (adding `-nan`). That the vendored testsuite has
no other rounding input is a textual audit (`docs/projects/wasm-wasi.md`), not a theorem.

**Issue #2046.** `returns7`: the wasmi 0.40.0 model returns `7` on the reproducer, as the probe
observes (its Core run never meets a pending quirk redex); `versions_differ`: wasmi 2.0.0 does
not.

**Not proved here.** That the model has no *other* observation of a witness call or of the
reproducer (the results above are single runs; the every-run logic covers Core only), and that
the model is Core on all code without rounding operators.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.Observed

open Silmaril Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim (HostParametric)
open Silmaril.Wasm.Atlas
open Silmaril.Proofs.Wasm.Wasmi.Observed (roundFn_store isRound_of_mem sNaN_facts unOp_ne SNaN)

variable {H : Type}

/-- The call `t.op x` of the witness store. -/
def roundCall (t : FloatType) (op : FloatUnOp) (x : FloatValue t) : Core.Call :=
  (roundAddr t op, [fval t x])

/-- **wasmi 0.40.0 returns a signalling input unchanged**, every profile. -/
theorem wasmi_returns (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    {x : FloatValue t} (hx : x ∈ sNaNs t) :
    Behaviour.returns [fval t x] ∈ obs P roundPt (roundCall t op x) := by
  obtain ⟨R⟩ := roundFn_store (t := t) hop
  exact .inl ⟨_, .values [fval t x], R.wasmi_run (isRound_of_mem hop) (sNaN_facts hx).2.1,
    rfl, rfl⟩

/-- **Core 3.0's value results** of a witness call: exactly the allowed results of `t.op x`. -/
theorem core_returns_iff (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    (x : FloatValue t) (vs : List Val) :
    Behaviour.returns vs ∈ Core.obs P roundPt (roundCall t op x) ↔
      ∃ z, floatUnOpP P t op x z ∧ vs = [fval t z] := by
  obtain ⟨R⟩ := roundFn_store (t := t) hop
  exact R.core_returns_iff x vs

/-- **Core 3.0 never returns a signalling input of a rounding operator.** -/
theorem core_not (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    {x : FloatValue t} (hx : x ∈ sNaNs t) :
    Behaviour.returns [fval t x] ∉ Core.obs P roundPt (roundCall t op x) := by
  rw [core_returns_iff P hop]
  rintro ⟨z, hz, h⟩
  have hzx : z = x := by
    simp only [List.cons.injEq, and_true, fval, Val.num.injEq] at h
    cases h
    rfl
  exact unOp_ne (isRound_of_mem hop) (sNaN_facts hx).1 hz hzx

/-- Core 3.0 returns some allowed result. -/
theorem core_has (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    (x : FloatValue t) :
    ∃ z, floatUnOpP P t op x z ∧ Behaviour.returns [fval t z] ∈ Core.obs P roundPt (roundCall t op x) := by
  obtain ⟨z, hz⟩ := floatUnOpP_nonempty P t op x
  exact ⟨z, hz, (core_returns_iff P hop x _).2 ⟨z, hz, rfl⟩⟩

/-- The safety sentence "no observation of `t.op x` returns `x`". -/
def φ (t : FloatType) (op : FloatUnOp) (x : FloatValue t) : BSen Core.Call (Behaviour Val) :=
  .always (roundCall t op x) (· ≠ .returns [fval t x])

theorem φ_universal (t : FloatType) (op : FloatUnOp) (x : FloatValue t) : (φ t op x).Universal :=
  trivial

/-- **Disagreement**: `φ` holds in Core 3.0 and fails in the wasmi 0.40.0 model. -/
theorem disagree (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    {x : FloatValue t} (hx : x ∈ sNaNs t) :
    (φ t op x).Sat (Core.obs P roundPt) ∧ ¬ (φ t op x).Sat (obs P roundPt) := by
  refine ⟨fun b hb hbx => ?_, fun h => h _ (wasmi_returns P hop hx) rfl⟩
  subst hbx
  exact core_not P hop hx hb

/-- **The 16 failures of the harness**: both float types, the four rounding operators, the two
signalling inputs of each type. -/
theorem sixteen (P : Profile) :
    ∀ t : FloatType, ∀ op ∈ roundOps, ∀ x ∈ sNaNs t,
      (φ t op x).Sat (Core.obs P roundPt) ∧ ¬ (φ t op x).Sat (obs P roundPt) :=
  fun _ _ hop _ hx => disagree P hop hx

/-- **The wasmi 0.40.0 model is not conformant**, at every profile. -/
theorem not_conformant (P : Profile) :
    ¬ ∀ (x : Core.Pt Empty) c, obs P x c ⊆ Core.obs P x c := by
  intro h
  have hop : FloatUnOp.floor ∈ roundOps := by simp [roundOps]
  have hx : (0xffa00000#32 : FloatValue .f32) ∈ sNaNs .f32 := .head _
  exact core_not P hop hx (h _ _ (wasmi_returns P hop hx))

namespace Loose

/-- **Core refines the loose model of wasmi 0.40.0.** -/
theorem core_le (P : Profile) (x : Core.Pt H) (c : Core.Call) : Core.obs P x c ⊆ obs P x c :=
  Variant.loose_mono _ _ _

/-- **wasmi 0.40.0 refines its loose model**, at every point. -/
theorem wasmi_le (P : Profile) (x : Core.Pt H) (c : Core.Call) :
    Observed.obs P x c ⊆ obs P x c :=
  Variant.behavioursR_mono (fun _ _ => Silmaril.Proofs.Wasm.Wasmi.Observed.step_le) _

/-- **Transfer**: a universal sentence of the loose model holds for Core and for wasmi 0.40.0. -/
theorem transfer (P : Profile) {x : Core.Pt H} {φ : BSen Core.Call (Behaviour Val)}
    (h : φ.Sat (obs P x)) (hu : φ.Universal) :
    φ.Sat (Core.obs P x) ∧ φ.Sat (Observed.obs P x) :=
  ⟨BSen.sat_of_subset_univ (core_le P x) hu h, BSen.sat_of_subset_univ (wasmi_le P x) hu h⟩

/-- **On each witness the loose model returns both the input and a Core result.** -/
theorem witness (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    {x : FloatValue t} (hx : x ∈ sNaNs t) :
    Behaviour.returns [fval t x] ∈ obs P roundPt (roundCall t op x) ∧
      ∃ z, z ≠ x ∧ Behaviour.returns [fval t z] ∈ obs P roundPt (roundCall t op x) := by
  refine ⟨wasmi_le P _ _ (wasmi_returns P hop hx), ?_⟩
  obtain ⟨z, hz, hm⟩ := core_has P hop x
  exact ⟨z, unOp_ne (isRound_of_mem hop) (sNaN_facts hx).1 hz, core_le P _ _ hm⟩

end Loose

namespace LooseAll

/-- **Core refines the loose model of all modelled wasmi versions.** -/
theorem core_le (P : Profile) (x : Core.Pt H) (c : Core.Call) : Core.obs P x c ⊆ obs P x c :=
  Variant.loose_mono _ _ _

/-- **wasmi 0.40.0 refines `LooseAll`**, at every point. -/
theorem wasmi040_le (P : Profile) (x : Core.Pt H) (c : Core.Call) :
    Observed.obs P x c ⊆ obs P x c :=
  (Loose.wasmi_le P x c).trans
    (Variant.behavioursR_mono (fun _ _ => Silmaril.Proofs.Wasm.Wasmi.Observed.loose_le_all) _)

/-- **wasmi 2.0.0 refines `LooseAll`**, for hosts parametric in function code. -/
theorem wasmi200_le (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2) (c : Core.Call) :
    Wasmi.obs P x c ⊆ obs P x c :=
  (Wasmi.Loose.wasmi_le P hh c).trans
    (Variant.behavioursR_mono (fun _ _ => Silmaril.Proofs.Wasm.Wasmi.Observed.loose200_le_all) _)

/-- **Transfer**: a universal sentence of `LooseAll` holds for Core, wasmi 0.40.0 and (for hosts
parametric in function code) wasmi 2.0.0. -/
theorem transfer (P : Profile) {x : Core.Pt H} {φ : BSen Core.Call (Behaviour Val)}
    (h : φ.Sat (obs P x)) (hu : φ.Universal) (hh : HostParametric x.2) :
    φ.Sat (Core.obs P x) ∧ φ.Sat (Observed.obs P x) ∧ φ.Sat (Wasmi.obs P x) :=
  ⟨BSen.sat_of_subset_univ (core_le P x) hu h, BSen.sat_of_subset_univ (wasmi040_le P x) hu h,
    BSen.sat_of_subset_univ (wasmi200_le P hh) hu h⟩

/-- **`LooseAll` has both versions' observations on both reproducers**: `7` and `5` on issue
#2046, and on each signalling-NaN witness the input and a Core result. -/
theorem witnesses (P : Profile) :
    (Behaviour.returns [Val.i32 7] ∈ obs P reproPt reproCall ∧
      Behaviour.returns [Val.i32 5] ∈ obs P reproPt reproCall) ∧
    ∀ t : FloatType, ∀ op ∈ roundOps, ∀ x ∈ sNaNs t,
      Behaviour.returns [fval t x] ∈ obs P roundPt (roundCall t op x) ∧
        ∃ z, z ≠ x ∧ Behaviour.returns [fval t z] ∈ obs P roundPt (roundCall t op x) := by
  refine ⟨⟨core_le P _ _ (by rw [Wasmi.core_f]; rfl),
    wasmi200_le P Wasmi.repro_hostParametric _ (by rw [Wasmi.wasmi_f]; rfl)⟩, ?_⟩
  intro t op hop x hx
  refine ⟨wasmi040_le P _ _ (wasmi_returns P hop hx), ?_⟩
  obtain ⟨z, hz, hm⟩ := core_has P hop x
  exact ⟨z, unOp_ne (isRound_of_mem hop) (sNaN_facts hx).1 hz, core_le P _ _ hm⟩

end LooseAll

/-! ## Which inputs the rounding quirk disagrees on -/

/-- **The wasmi 0.40.0 model returns `wUnOp t op x`** on every call of the witness store. -/
theorem model_returns (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    (x : FloatValue t) :
    Behaviour.returns [fval t (wUnOp t op x)] ∈ obs P roundPt (roundCall t op x) :=
  Silmaril.Proofs.Wasm.Wasmi.Observed.model_returns P hop x

/-- Core returns the model's result exactly when the profile allows it. -/
theorem core_returns_wUnOp (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    (x : FloatValue t) :
    Behaviour.returns [fval t (wUnOp t op x)] ∈ Core.obs P roundPt (roundCall t op x) ↔
      floatUnOpP P t op x (wUnOp t op x) := by
  rw [core_returns_iff P hop]
  refine ⟨fun ⟨z, hz, h⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  have hzx : wUnOp t op x = z := by
    simp only [List.cons.injEq, and_true, fval, Val.num.injEq] at h
    cases h
    rfl
  rwa [hzx]

/-- **At the spec's NaN policy the model's result is outside Core exactly on signalling NaNs**,
for every input of every witness function. -/
theorem disagree_iff_spec (P : Profile) (hP : P.nan = .spec) {t : FloatType} {op : FloatUnOp}
    (hop : op ∈ roundOps) (x : FloatValue t) :
    Behaviour.returns [fval t (wUnOp t op x)] ∉ Core.obs P roundPt (roundCall t op x) ↔
      SNaN t x := by
  rw [core_returns_wUnOp P hop, Silmaril.Proofs.Wasm.Wasmi.Observed.allowed_spec hP]
  simp [isRound_of_mem hop]

/-- **At the canonical NaN policy the model's result is outside Core exactly on NaNs other than
the positive canonical one.** -/
theorem disagree_iff_canonical (P : Profile) (hP : P.nan = .canonical) {t : FloatType}
    {op : FloatUnOp} (hop : op ∈ roundOps) (x : FloatValue t) :
    Behaviour.returns [fval t (wUnOp t op x)] ∉ Core.obs P roundPt (roundCall t op x) ↔
      isNaNB t x = true ∧ x ≠ posNaN t := by
  rw [core_returns_wUnOp P hop, Silmaril.Proofs.Wasm.Wasmi.Observed.allowed_canonical hP]
  simp [isRound_of_mem hop]

/-- An input of a rounding operator in the vendored testsuite: one of its NaN inputs, or not a
NaN (every other rounding input of `f32.wast`, `f64.wast`, `float_misc.wast` and `block.wast`). -/
def HarnessIn (t : FloatType) (x : FloatValue t) : Prop := x ∈ nanIns t ∨ isNaNB t x = false

/-- **The 16 failures are all the disagreements at the spec's NaN policy**: on the testsuite's
rounding inputs, the model's result is outside Core exactly on the signalling inputs `sNaNs`
(two per type and operator, 16 in all). -/
theorem harness_spec (P : Profile) (hP : P.nan = .spec) :
    ∀ t : FloatType, ∀ op ∈ roundOps, ∀ x : FloatValue t, HarnessIn t x →
      (Behaviour.returns [fval t (wUnOp t op x)] ∉ Core.obs P roundPt (roundCall t op x) ↔
        x ∈ sNaNs t) := by
  intro t op hop x hx
  rw [disagree_iff_spec P hP hop]
  rcases hx with hx | hx
  · exact (Silmaril.Proofs.Wasm.Wasmi.Observed.nanIns_facts hx).2
  · refine iff_of_false (fun h => ?_) (fun h => ?_)
    · rw [Silmaril.Proofs.Wasm.Wasmi.Observed.snan_isNaN h] at hx
      cases hx
    · rw [(sNaN_facts h).2.1] at hx
      cases hx

/-- **At the canonical NaN policy there are 24**: on the testsuite's rounding inputs, the
model's result is outside Core exactly on the NaN inputs other than `nan` (the signalling ones
and `-nan`, three per type and operator). -/
theorem harness_canonical (P : Profile) (hP : P.nan = .canonical) :
    ∀ t : FloatType, ∀ op ∈ roundOps, ∀ x : FloatValue t, HarnessIn t x →
      (Behaviour.returns [fval t (wUnOp t op x)] ∉ Core.obs P roundPt (roundCall t op x) ↔
        x ∈ nanIns t ∧ x ≠ posNaN t) := by
  intro t op hop x hx
  rw [disagree_iff_canonical P hP hop]
  rcases hx with hx | hx
  · simp [hx, (Silmaril.Proofs.Wasm.Wasmi.Observed.nanIns_facts hx).1]
  · refine iff_of_false (fun h => ?_) (fun h => ?_)
    · rw [h.1] at hx
      cases hx
    · rw [(Silmaril.Proofs.Wasm.Wasmi.Observed.nanIns_facts h.1).1] at hx
      cases hx

/-! ## Issue #2046 in the wasmi 0.40.0 model -/

/-- **wasmi 0.40.0 returns `7` on the issue-#2046 reproducer**, at every profile, as the local
probe observes: the Core 3.0 run of `f 5 1` never meets a pending quirk redex, so it is a run of
the model. -/
theorem returns7 (P : Profile) : Behaviour.returns [Val.i32 7] ∈ obs P reproPt reproCall :=
  Silmaril.Proofs.Wasm.Wasmi.Observed.returns7 P

/-- **The two versions disagree on issue #2046**: wasmi 0.40.0 returns `7`, which wasmi 2.0.0
never returns (it returns `5` and nothing else). -/
theorem versions_differ (P : Profile) :
    Behaviour.returns [Val.i32 7] ∈ obs P reproPt reproCall ∧
      Behaviour.returns [Val.i32 7] ∉ Wasmi.obs P reproPt reproCall := by
  refine ⟨returns7 P, fun h => ?_⟩
  rw [Wasmi.wasmi_f] at h
  exact absurd h (by decide)

/-! ## The version gap -/

/-- **Core 3.0 instantiates the module of `global.wast:373`**, every profile and host. -/
theorem gap_core (P : Profile) (host : HostSemantics Empty) :
    ∃ c : Config Empty, Instantiate P host ({} : Store Empty) gapMod [] c ∧
      ∀ g ∈ c.store.globals, g.value = Val.i32 0 :=
  Silmaril.Proofs.Wasm.Wasmi.Observed.gap_core P host

/-- **wasmi (0.40.0 and 2.0.0) refuses it.** -/
theorem gap_wasmi : instantiate? ({} : Store Empty) gapMod = none :=
  Silmaril.Proofs.Wasm.Wasmi.Observed.gap_wasmi

end Silmaril.Wasm.Wasmi.Observed
