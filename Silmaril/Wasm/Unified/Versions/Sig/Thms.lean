module

public import Silmaril.Wasm.Unified.Versions.Sig.Defs
public import Silmaril.Wasm.Models.Features.Thms

/-!
# Version feature signatures: inclusions and separations

* `vsig_sub`: **an inclusion of feature sets is an inclusion of signatures** (`FSig.Sub`), so
  `vincl h : vsig S ⟶ vsig T` is a signature morphism of the unified institution, and
  inclusions compose (`FSig.incl_comp`);
* the version lattice: `sub_10_20`, `sub_20_30`, `sub_30_FX`, `sub_10_lime1`, `sub_lime1_30`,
  `sub_20_wasmi`;
* separations by one opcode: `table.grow ∈ 2.0 \ 1.0`, `return_call ∈ 3.0 \ 2.0`,
  `resume ∈ FX \ 3.0`, `memory.copy ∈ Lime1 \ 1.0`, `try_table ∈ 3.0 \ wasmi`,
  `i64.add128 ∈ wasmi \ 3.0`;
* `sub_lime1_20`: **at the opcode level Lime1 is inside 2.0**, although `lime1 ≰ v20` as feature
  sets (`Silmaril.Wasm.Models.lime1_not_le_v20`): the only Lime1 capability outside 2.0 is
  `extConst`, which has no opcode (a validation difference, not a signature difference).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm.Models

theorem inB_mono {S T : FeatureSet} (h : S ≤ T) {o : Opcode} (ho : inB S o = true) :
    inB T o = true := by
  unfold inB at ho ⊢
  cases hn : need o with
  | none => simp [hn] at ho
  | some l =>
    simp only [hn, List.all_eq_true] at ho ⊢
    exact fun c hc => has_of_le h (ho c hc)

/-- **Inclusions of feature sets are inclusions of signatures.** -/
theorem vsig_sub {S T : FeatureSet} (h : S ≤ T) : FSig.Sub (vsig S) (vsig T) :=
  ⟨fun _ ho => inB_mono h ho, fun _ _ => rfl⟩

/-- The signature morphism of an inclusion of feature sets. -/
def vincl {S T : FeatureSet} (h : S ≤ T) : vsig S ⟶ vsig T := FSig.incl (vsig_sub h)

theorem sub_10_20 : FSig.Sub bsig10 bsig20 := vsig_sub v10_le_v20
theorem sub_20_30 : FSig.Sub bsig20 bsig30 := vsig_sub v20_le_v30
theorem sub_30_FX : FSig.Sub bsig30 bsigFX := vsig_sub v30_le_wasmFX
theorem sub_lime1_30 : FSig.Sub bsigLime1 bsig30 := vsig_sub lime1_le_v30
theorem sub_20_wasmi : FSig.Sub bsig20 bsigWasmi := vsig_sub v20_le_wasmi200

theorem v10_le_lime1 : v10 ≤ lime1 := leB_iff.mp (by decide)
theorem sub_10_lime1 : FSig.Sub bsig10 bsigLime1 := vsig_sub v10_le_lime1

/-- Membership in a version signature is decided by `inB`. -/
theorem mem_vsig {S : FeatureSet} {o : Opcode} : o ∈ (vsig S).ops ↔ inB S o = true := Iff.rfl

theorem tableGrow_sep : opTableGrow ∈ bsig20.ops ∧ opTableGrow ∉ bsig10.ops :=
  ⟨show inB _ opTableGrow = true by decide,
    fun h => absurd (show inB _ opTableGrow = true from h) (by decide)⟩

theorem returnCall_sep : opReturnCall ∈ bsig30.ops ∧ opReturnCall ∉ bsig20.ops :=
  ⟨show inB _ opReturnCall = true by decide,
    fun h => absurd (show inB _ opReturnCall = true from h) (by decide)⟩

theorem resume_sep : opResume ∈ bsigFX.ops ∧ opResume ∉ bsig30.ops :=
  ⟨show inB _ opResume = true by decide,
    fun h => absurd (show inB _ opResume = true from h) (by decide)⟩

theorem memoryCopy_sep : opMemoryCopy ∈ bsigLime1.ops ∧ opMemoryCopy ∉ bsig10.ops :=
  ⟨show inB _ opMemoryCopy = true by decide,
    fun h => absurd (show inB _ opMemoryCopy = true from h) (by decide)⟩

theorem tryTable_sep : opTryTable ∈ bsig30.ops ∧ opTryTable ∉ bsigWasmi.ops :=
  ⟨show inB _ opTryTable = true by decide,
    fun h => absurd (show inB _ opTryTable = true from h) (by decide)⟩

theorem add128_sep : opI64Add128 ∈ bsigWasmi.ops ∧ opI64Add128 ∉ bsig30.ops :=
  ⟨show inB _ opI64Add128 = true by decide,
    fun h => absurd (show inB _ opI64Add128 = true from h) (by decide)⟩

/-- No opcode needs `extConst`. -/
theorem need_no_extConst {o : Opcode} {l : List Cap} (h : need o = some l) :
    Cap.extConst ∉ l := by
  obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h
  cases k <;> decide

/-- Every Lime1 capability other than `extConst` is a 2.0 capability. -/
theorem lime1_v20_caps (c : Cap) (hc : c ≠ .extConst) (h : lime1.has c = true) :
    v20.has c = true := by
  cases c <;> first | exact absurd rfl hc | revert h; decide

/-- **Lime1 is inside 2.0 at the opcode level.** -/
theorem sub_lime1_20 : FSig.Sub bsigLime1 bsig20 := by
  refine ⟨fun o ho => ?_, fun _ _ => rfl⟩
  have ho' : inB lime1 o = true := ho
  show inB v20 o = true
  unfold inB at ho' ⊢
  cases hn : need o with
  | none => simp [hn] at ho'
  | some l =>
    simp only [hn, List.all_eq_true] at ho' ⊢
    exact fun c hc =>
      lime1_v20_caps c (fun e => need_no_extConst hn (e ▸ hc)) (ho' c hc)

end Silmaril.Wasm.Unified.Versions
