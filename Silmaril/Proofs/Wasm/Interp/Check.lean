module

public import Silmaril.Wasm.Interp.Defs

@[expose] public section

/-!
# Executable forms of the hypotheses of native adequacy (proofs)

`storeChk_of_storeChkB`: the Boolean `storeChkB` implies `StoreChk`;
`nativeFuncsOk_of_nativeFuncsB`: the Boolean `nativeFuncsB` implies silmaril-lean's
`Binaryen.NativeFuncsOk`. Both are decided by kernel evaluation on concrete stores. New proofs.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- `storeChkB` is sound. -/
theorem storeChk_of_storeChkB {F : List (FuncInst H)} (h : storeChkB F = true) : StoreChk F := by
  intro a fi fn ps rs hfi hcode hty
  have hmem : fi ∈ F := List.mem_of_getElem? hfi
  have hb : funcChkB F fi = true := List.all_eq_true.mp h fi hmem
  simpa only [funcChkB, hcode, hty] using hb

mutual
/-- `instrNative` is sound. -/
theorem instrNative_sound (i : Instr) (h : instrNative i = true) :
    Binaryen.instrInNativeProfile i := by
  cases i with
  | block bt body =>
    have h' : Binaryen.nativeBlockType bt = true ∧ instrsNative body = true := by
      simpa only [instrNative, Bool.and_eq_true] using h
    rw [Binaryen.instrInNativeProfile.eq_def]
    exact ⟨h'.1, fun j _ => instrsNative_sound body h'.2 j.1 j.2⟩
  | loop bt body =>
    have h' : Binaryen.nativeBlockType bt = true ∧ instrsNative body = true := by
      simpa only [instrNative, Bool.and_eq_true] using h
    rw [Binaryen.instrInNativeProfile.eq_def]
    exact ⟨h'.1, fun j _ => instrsNative_sound body h'.2 j.1 j.2⟩
  | if_ bt b₁ b₂ =>
    have h' : (Binaryen.nativeBlockType bt = true ∧ instrsNative b₁ = true) ∧
        instrsNative b₂ = true := by
      simpa only [instrNative, Bool.and_eq_true] using h
    rw [Binaryen.instrInNativeProfile.eq_def]
    exact ⟨h'.1.1, fun j _ => instrsNative_sound b₁ h'.1.2 j.1 j.2,
      fun j _ => instrsNative_sound b₂ h'.2 j.1 j.2⟩
  | _ => exact Binaryen.instrInNativeProfile_of_flat (by simpa only [instrNative] using h)

/-- `instrsNative` is sound. -/
theorem instrsNative_sound (is : List Instr) (h : instrsNative is = true) :
    ∀ i ∈ is, Binaryen.instrInNativeProfile i := by
  intro i hi
  cases is with
  | nil => exact absurd hi List.not_mem_nil
  | cons j js =>
    have h' : instrNative j = true ∧ instrsNative js = true := by
      simpa only [instrsNative, Bool.and_eq_true] using h
    rcases List.mem_cons.mp hi with hij | hi'
    · exact hij ▸ instrNative_sound j h'.1
    · exact instrsNative_sound js h'.2 i hi'
end

/-- `nativeFuncsB` is sound. -/
theorem nativeFuncsOk_of_nativeFuncsB {F : List (FuncInst H)} (h : nativeFuncsB F = true) :
    Binaryen.NativeFuncsOk F := by
  intro fi hfi
  have hb := List.all_eq_true.mp h fi hfi
  revert hb
  rcases hc : fi.code with fn | x
  · intro hb
    exact ⟨fn, rfl, instrsNative_sound fn.body hb⟩
  · intro hb
    cases hb

end Silmaril.Wasm.Interp
