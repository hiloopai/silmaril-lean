module

public import Silmaril.Proofs.Wasm.Auto2.Kernel.ElemInit

/-!
# The kernel-cheap instantiation is the specification's

`instantiateOnceK?_eq`: `instantiateOnceK? = instantiateOnce?`; `instK?_eq`: `instK? m` is the
instance of `instance? m` when `validate? m` succeeds; `bytesEqL_eq`; and the front end's checks
over `instK?` are the specification ones (`checkAmongX_eq_K`, `liftAmong_eq_K`, `fnBody?_eq_K`,
`cexWith_eq_K`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Kernel

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.Kernel
open Silmaril.Wasm.Verify (instance? instImps instFrom)

variable {H : Type}

theorem initDataSegK?_eq : @initDataSegK? H = initDataSeg? evalConst? := by
  funext s f k d
  simp only [initDataSegK?, initDataSeg?, memoryInitLoopK_eq]
  rfl

theorem initDataListK?_eq : @initDataListK? H = initDataList? evalConst? := by
  funext s f l
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, d⟩ := p
    simp only [initDataListK?, initDataList?, initDataSegK?_eq]
    split <;> simp_all

theorem initElemSegK?_eq : @initElemSegK? H = initElemSeg? evalConst? := by
  funext s f k e
  simp only [initElemSegK?, initElemSeg?, tableInitLoopK_eq]
  rfl

theorem initElemListK?_eq : @initElemListK? H = initElemList? evalConst? := by
  funext s f l
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, e⟩ := p
    simp only [initElemListK?, initElemList?, initElemSegK?_eq]
    split <;> simp_all

theorem initSegmentsK?_eq : @initSegmentsK? H = initSegments? evalConst? := by
  funext s f m
  simp only [initSegmentsK?, initSegments?, initData?, initElem?, initDataListK?_eq,
    initElemListK?_eq]
  rfl

theorem prepareDirectK?_eq : @prepareDirectK? H = instantiateDirect? := by
  funext s m xas
  simp only [prepareDirectK?, instantiateDirect?, prepareDirect?, initSegmentsK?_eq]
  rfl

/-- **The instantiation with closed-form data segments is the specification's.** -/
theorem instantiateOnceK?_eq : @instantiateOnceK? H = instantiateOnce? := by
  funext s m xas
  simp only [instantiateOnceK?, instantiateOnce?, prepareDirectK?_eq]
  rfl

theorem imports_nil_of_validate {m : Module} {mt : CModuleType} (h : validate? m = some mt)
    (hi : m.imports = []) : mt.imports = [] := by
  cases validate?_sound h with
  | mk _ himports =>
    rw [hi] at himports
    cases himports
    rfl

/-- **The instance without validation**: when `validate? m` succeeds, `instK? m` is the instance
`instance? m` computes. -/
theorem instK?_eq {m : Module} (hv : (validate? m).isSome = true) :
    instK? m = (instance? m).map (·.2) := by
  unfold instK?
  split
  · rename_i hi
    have hi : m.imports = [] := List.isEmpty_iff.mp hi
    obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp hv
    have hmi := imports_nil_of_validate hmt hi
    obtain ⟨imps, exps⟩ := mt
    simp only at hmi
    subst hmi
    simp only [instance?, hmt, Option.bind_some, List.all_nil, ↓reduceIte, CExternType.funcs,
      List.mapM_nil, Option.pure_def, instImps, instImpsK, instantiateOnceK?_eq, List.length_nil,
      List.range_zero, List.map_nil]
    rcases instantiateOnce? (Silmaril.Wasm.Game.importStore []) m [] with _ | ⟨s, f, _ | st⟩ <;>
      simp [instFrom, Option.map_map, Function.comp_def]
  · rfl

/-- **Byte lists compared by list recursion.** -/
theorem bytesEqL_eq (l r : List UInt8) : bytesEqL l r = decide (l = r) := by
  induction l generalizing r with
  | nil => cases r <;> rfl
  | cons a l ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      show (Nat.beq a.toNat b.toNat && bytesEqL l r) = decide (a :: l = b :: r)
      rw [ih]
      by_cases hab : a = b
      · subst hab
        simp [Nat.beq_refl]
      · have hne : a.toNat ≠ b.toNat := fun h => hab (UInt8.toNat_inj.mp h)
        have : Nat.beq a.toNat b.toNat = false := by
          cases hq : Nat.beq a.toNat b.toNat
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hq) hne
        simp [this, hab]

theorem sumCheckXK_eq : sumCheckXK = Silmaril.Wasm.Auto.Bridge.sumCheckX := by
  funext A B
  cases A <;> cases B <;> try rfl
  rename_i A B
  simp only [sumCheckXK, Silmaril.Wasm.Auto.Bridge.sumCheckX, bytesEqL_eq]
  congr 3
  simp [ByteArray.ext_iff, Array.toList_inj]

/-- **The chunk check of a certificate over `instK?`.** -/
theorem checkAmongX_eq_K {m₁ m₂ : Module} (h₁ : (validate? m₁).isSome = true)
    (h₂ : (validate? m₂).isSome = true) (js : List Nat) :
    Silmaril.Wasm.Auto.Bridge.checkAmong m₁ m₂ js = checkAmongXK m₁ m₂ js := by
  unfold Silmaril.Wasm.Auto.Bridge.checkAmong checkAmongXK
  rw [instK?_eq h₁, instK?_eq h₂, sumCheckXK_eq]
  cases instance? m₁ <;> cases instance? m₂ <;> rfl

/-- The e-graph side conditions over `instK?`. -/
theorem liftAmong_eq_K {m₁ m₂ : Module} (h₁ : (validate? m₁).isSome = true)
    (h₂ : (validate? m₂).isSome = true) (js : List Nat) :
    Silmaril.Wasm.Auto.Bridge.liftAmong m₁ m₂ js = liftAmongK m₁ m₂ js := by
  unfold Silmaril.Wasm.Auto.Bridge.liftAmong liftAmongK
  rw [instK?_eq h₁, instK?_eq h₂]
  cases instance? m₁ <;> cases instance? m₂ <;> rfl

/-- The body of an export over `instK?`. -/
theorem fnBody?_eq_K {m : Module} (h : (validate? m).isSome = true) (j : Nat) :
    Silmaril.Wasm.Auto.Bridge.fnBody? m j = fnBodyK? m j := by
  unfold Silmaril.Wasm.Auto.Bridge.fnBody? fnBodyK?
  rw [instK?_eq h]
  cases instance? m <;> rfl

/-- A test of a refinement over `instK?`. -/
theorem cexWith_eq_K {m₁ m₂ : Module} (h₁ : (validate? m₁).isSome = true)
    (h₂ : (validate? m₂).isSome = true) (run : Silmaril.Wasm.Auto.Front.Runner)
    (R : Silmaril.Wasm.Auto.Front.Rel) (j : Nat) (vs : List Val) :
    Silmaril.Wasm.Auto.Front.cexWith run R m₁ m₂ j vs = cexWithK run R m₁ m₂ j vs := by
  unfold Silmaril.Wasm.Auto.Front.cexWith cexWithK
  rw [instK?_eq h₁, instK?_eq h₂]
  cases instance? m₁ <;> cases instance? m₂ <;> rfl

end Silmaril.Proofs.Wasm.Auto2.Kernel
