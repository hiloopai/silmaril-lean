module

public import Silmaril.Wasm.Models.Syntax.Thms
public import Silmaril.Wasm.Wasmi.Defs

/-!
# wasmi 2.0.0's instruction set and the feature set `wasmi200`

`Silmaril.Wasm.Wasmi.Supported` is the instruction-level stand-in, on Core 3.0 syntax, for the
feature set `FeatureSet.wasmi200` (`docs/projects/spectec/README.md` §1.1, §4). They are reconciled as
follows.

* `wasmi200_lacks`: `wasmi200` has none of `typedFuncRef`, `gcImm`, `gcMut`, `exn` (by
  `decide`);
* `supportedI_of_inFeatB`, `supported_of_insInFeatB`: **every instruction (sequence) of
  `wasmi200` is `Supported`**, recursively through bodies;
* `not_inFeatB_of_supported`: the converse fails: a typed `select` over a GC reference type is
  `Supported` (an instruction-level check that ignores type annotations) but not of
  `wasmi200`. `Supported` is therefore the coarser of the two, and the theorems about the wasmi
  model that assume `StoreSupported` apply to every store whose function bodies are instruction
  sequences of `wasmi200`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm

/-- `wasmi200` has no typed function references, GC or exception handling. -/
theorem wasmi200_lacks :
    wasmi200.has .typedFuncRef = false ∧ wasmi200.has .gcImm = false ∧
      wasmi200.has .gcMut = false ∧ wasmi200.has .exn = false := by
  decide

/-- **Every instruction of `wasmi200` is supported by wasmi 2.0.0.** -/
theorem supportedI_of_inFeatB (i : Instr) (h : Instr.inFeatB wasmi200 i = true) :
    Silmaril.Wasm.Wasmi.SupportedI i = true := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := wasmi200_lacks
  revert h
  induction i using Instr.rec
    (motive_2 := fun l => Instr.insInFeatB wasmi200 l = true → Silmaril.Wasm.Wasmi.Supported l = true)
  all_goals simp_all [Instr.inFeatB, Instr.insInFeatB, Instr.headB, Silmaril.Wasm.Wasmi.SupportedI,
    Silmaril.Wasm.Wasmi.Supported]

/-- **Every instruction sequence of `wasmi200` is supported by wasmi 2.0.0.** -/
theorem supported_of_insInFeatB (is : List Instr) (h : Instr.insInFeatB wasmi200 is = true) :
    Silmaril.Wasm.Wasmi.Supported is = true := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [Instr.insInFeatB, Bool.and_eq_true] at h
    simp only [Silmaril.Wasm.Wasmi.Supported, supportedI_of_inFeatB i h.1, ih h.2, Bool.and_self]

/-- A typed `select` over `(ref null any)`. -/
def selectAnyRef : Instr := .select (some [.ref ⟨true, .abstract .any⟩])

/-- **The converse fails**: `selectAnyRef` is supported but not of `wasmi200`. -/
theorem not_inFeatB_of_supported :
    Silmaril.Wasm.Wasmi.SupportedI selectAnyRef = true ∧
      Instr.inFeatB wasmi200 selectAnyRef = false := by
  decide

end Silmaril.Wasm.Models
