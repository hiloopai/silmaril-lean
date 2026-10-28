module

public import Silmaril.Numeric.Ieee754.Std.Isa

/-!
# WebAssembly's NaN rule as a point of the NaN-policy lattice

WebAssembly Core 3.0 §4.3.3 (`nans_N`) lets a floating-point operation return,
when it returns a NaN:

* a *canonical* NaN of either sign (all-ones exponent, significand field
  exactly the quiet bit) when every NaN operand is canonical (or there is none);
* otherwise any *arithmetic* NaN (a quiet NaN, any payload, either sign).

`NaNSpec.wasm` states this rule on `Std` interchange encodings. It sits strictly
inside the quiet-NaN policy and contains both the x86 SSE and the RISC-V NaN
functions, so every `Std` x86 SSE or RISC-V result is a result WebAssembly
admits, for every operation built from `runOp` (all arithmetic, for any rounding
direction). Together with `OpSpec.mono` this gives, for instance,
`Isa.x86SSE.add_wasm`:

```
ofFun x86SSE ⊆ wasm ⊆ quietNaN ⊆ anyNaN ⊆ anything
ofFun riscv  ⊆ wasm
```

`Numeric.Float.Wasm` proves the corresponding facts for the older
`Numeric.Float.Profile` implementation against the repository's WebAssembly
numerics.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

namespace Interchange

variable (F : Interchange)

/-- WebAssembly's canonical NaN, of either sign. -/
def isCanonicalNaN (b : Fields) : Prop := b.exp = F.expMax ∧ b.frac = 2 ^ (F.t - 1)

instance (b : Fields) : Decidable (F.isCanonicalNaN b) := by
  unfold isCanonicalNaN; infer_instance

theorem isCanonicalNaN_quiet (b : Fields) (h : F.isCanonicalNaN b) :
    F.isNaN b = true ∧ F.isQuiet b = true := by
  obtain ⟨he, hf⟩ := h
  simp [isNaN, isQuiet, he, hf, Nat.testBit_two_pow_self]

theorem quiet_canonical (b : Fields) (h : F.isCanonicalNaN b) : F.isCanonicalNaN (F.quiet b) := by
  obtain ⟨he, hf⟩ := h
  refine ⟨he, ?_⟩
  simp [quiet, hf]

end Interchange

namespace NaNSpec

/-- WebAssembly Core 3.0 §4.3.3 `nans_N`. -/
def wasm (F : Interchange) : NaNSpec := fun ins out =>
  if ∀ i ∈ ins, F.isNaN i = true → F.isCanonicalNaN i then F.isCanonicalNaN out
  else quietNaN F.encoding ins out

theorem wasm_le_quietNaN (F : Interchange) : wasm F ≤ quietNaN F.encoding := by
  intro ins out h
  unfold wasm at h
  split_ifs at h
  · exact F.isCanonicalNaN_quiet out h
  · exact h

theorem x86SSE_le_wasm (F : Interchange) :
    ofFun (Isa.x86SSE.nan F.encoding) ≤ wasm F := by
  intro ins out h
  simp only [ofFun] at h
  subst h
  have hq := Isa.x86SSE_nan_le_propagating F.encoding ins _ rfl
  unfold wasm
  split_ifs with hall
  · change F.isCanonicalNaN (NaNFun.x86SSE F.encoding (F.encoding.defaultNaN true) ins)
    unfold NaNFun.x86SSE
    split
    next i hi =>
      have hmem := List.mem_of_find?_eq_some hi
      have hnan : F.encoding.isNaN i = true := by simpa using List.find?_some hi
      exact F.quiet_canonical i (hall i hmem hnan)
    next => exact ⟨rfl, rfl⟩
  · exact hq.1

theorem riscv_le_wasm (F : Interchange) : ofFun (Isa.riscv.nan F.encoding) ≤ wasm F := by
  intro ins out h
  simp only [ofFun] at h
  subst h
  have hc : F.isCanonicalNaN (Isa.riscv.nan F.encoding ins) := ⟨rfl, rfl⟩
  unfold wasm
  split_ifs
  · exact hc
  · exact F.isCanonicalNaN_quiet _ hc

/-- WebAssembly's rule is strictly more exact than "any quiet NaN": a
non-canonical quiet NaN is not admitted when no operand is a NaN. -/
theorem quietNaN_not_le_wasm : ¬ quietNaN Interchange.binary32.encoding ≤ wasm Interchange.binary32 := by
  intro h
  have := h [] ⟨false, 255, 2 ^ 22 + 1⟩ (by simp only [quietNaN]; decide)
  simp only [wasm, List.not_mem_nil, false_implies, implies_true, ite_true,
    Interchange.isCanonicalNaN] at this
  revert this
  decide

/-- x86 SSE results are not all canonical, so the RISC-V point is not above it. -/
theorem x86SSE_not_le_riscv :
    ¬ ofFun (Isa.x86SSE.nan Interchange.binary32.encoding) ≤
      ofFun (Isa.riscv.nan Interchange.binary32.encoding) := by
  intro h
  have := h [⟨false, 255, 1⟩] _ rfl
  simp only [ofFun] at this
  revert this
  decide

end NaNSpec

namespace Isa

/-- Every x86 SSE sum, in every format and rounding direction, is a result
WebAssembly's NaN rule admits (and is otherwise the specified IEEE result). -/
theorem x86SSE_add_wasm (F : Interchange) (mode : RoundingMode) (x y : Fields) :
    OpSpec F.encoding (NaNSpec.wasm F) .afterRounding mode [x, y]
      (exactAdd mode (F.decode x) (F.decode y)) (x86SSE.add F.encoding mode x y).1
      (x86SSE.add F.encoding mode x y).2 :=
  (x86SSE.add_spec F.encoding mode x y).mono (NaNSpec.x86SSE_le_wasm F)

theorem riscv_add_wasm (F : Interchange) (mode : RoundingMode) (x y : Fields) :
    OpSpec F.encoding (NaNSpec.wasm F) .afterRounding mode [x, y]
      (exactAdd mode (F.decode x) (F.decode y)) (riscv.add F.encoding mode x y).1
      (riscv.add F.encoding mode x y).2 :=
  (riscv.add_spec F.encoding mode x y).mono (NaNSpec.riscv_le_wasm F)

theorem x86SSE_mul_wasm (F : Interchange) (mode : RoundingMode) (x y : Fields) :
    OpSpec F.encoding (NaNSpec.wasm F) .afterRounding mode [x, y]
      (exactMul (F.decode x) (F.decode y)) (x86SSE.mul F.encoding mode x y).1
      (x86SSE.mul F.encoding mode x y).2 :=
  (x86SSE.mul_spec F.encoding mode x y).mono (NaNSpec.x86SSE_le_wasm F)

theorem x86SSE_div_wasm (F : Interchange) (mode : RoundingMode) (x y : Fields) :
    OpSpec F.encoding (NaNSpec.wasm F) .afterRounding mode [x, y]
      (exactDiv (F.decode x) (F.decode y)) (x86SSE.div F.encoding mode x y).1
      (x86SSE.div F.encoding mode x y).2 :=
  (x86SSE.div_spec F.encoding mode x y).mono (NaNSpec.x86SSE_le_wasm F)

theorem x86SSE_sqrt_wasm (F : Interchange) (mode : RoundingMode) (x : Fields) :
    OpSpec F.encoding (NaNSpec.wasm F) .afterRounding mode [x]
      (exactSqrt (F.decode x)) (x86SSE.sqrt F.encoding mode x).1
      (x86SSE.sqrt F.encoding mode x).2 :=
  (x86SSE.sqrt_spec F.encoding mode x).mono (NaNSpec.x86SSE_le_wasm F)

end Isa

end Silmaril.Numeric.Ieee754.Std
