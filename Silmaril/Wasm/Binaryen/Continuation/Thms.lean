module

public import Silmaril.Wasm.Binaryen.Continuation.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Thms
import Silmaril.Proofs.Wasm.Binaryen.Continuation.Syntax

public section

namespace Silmaril.Wasm.Binaryen.Continuation

open Validation

theorem Raw.read_lower (raw : Raw) : Raw.read raw.lower = some raw :=
  Proofs.Wasm.Binaryen.Continuation.read_lower raw

theorem Raw.lower_of_read {ops : List Instr} {raw : Raw} (ok : Raw.read ops = some raw) :
    raw.lower = ops := Proofs.Wasm.Binaryen.Continuation.lower_of_read ok

theorem Raw.read_eq_some_iff {ops : List Instr} {raw : Raw} :
    Raw.read ops = some raw ↔ raw.lower = ops :=
  ⟨Raw.lower_of_read, fun eq => eq ▸ raw.read_lower⟩

theorem Raw.lower_injective : Function.Injective Raw.lower := by
  intro left right same
  exact Option.some.inj (left.read_lower.symm.trans ((congrArg Raw.read same).trans right.read_lower))

def Raw.coreEquiv : Raw ≃ { ops : List Instr // (Raw.read ops).isSome = true } where
  toFun raw := ⟨raw.lower, by simp [raw.read_lower]⟩
  invFun ops := (Raw.read ops.val).get ops.property
  left_inv raw := Raw.lower_injective (Raw.lower_of_read (Option.some_get _).symm)
  right_inv ops := Subtype.ext (Raw.lower_of_read (Option.some_get _).symm)

theorem Raw.lower_toBinaryen (raw : Raw) : BExpr.lowerList raw.toBinaryen = raw.lower :=
  lowerList_liftInstrs raw.lower

theorem Raw.ofBinaryen_toBinaryen (raw : Raw) : Raw.ofBinaryen raw.toBinaryen = some raw := by
  simp only [Raw.ofBinaryen, raw.lower_toBinaryen, raw.read_lower]

/-- Read any folding in the supported language; rebuilding chooses the structured lift,
not necessarily the original operand tree. -/
theorem Raw.ofBinaryen_eq_some_iff {forest : List BExpr} {raw : Raw} :
    Raw.ofBinaryen forest = some raw ↔ BExpr.lowerList raw.toBinaryen = BExpr.lowerList forest := by
  rw [raw.lower_toBinaryen]; exact Raw.read_eq_some_iff

theorem Code.core_erase {ctx inputs outputs raw} (code : Code ctx inputs outputs raw) :
    code.toCore.erase = code.erase.lower := Proofs.Wasm.Binaryen.Continuation.core_erase code

theorem Code.sound {ctx inputs outputs raw} (code : Code ctx inputs outputs raw) :
    InstrsOk ctx raw.lower (.plain inputs outputs) :=
  code.core_erase ▸ code.toCore.sound

theorem Code.binaryen_square {ctx inputs outputs raw} (code : Code ctx inputs outputs raw) :
    BExpr.lowerList code.erase.toBinaryen = code.toCore.erase := by
  rw [Raw.lower_toBinaryen, code.core_erase]

/-- Read-back from the actual intrinsic Core erasure recovers the continuation syntax. -/
theorem Code.read_core {ctx inputs outputs raw} (code : Code ctx inputs outputs raw) :
    Raw.read code.toCore.erase = some code.erase := by
  rw [code.core_erase, Raw.read_lower]

theorem Code.same_erasure_iff {ctx inputs outputs leftRaw rightRaw}
    (left : Code ctx inputs outputs leftRaw) (right : Code ctx inputs outputs rightRaw) :
    left.toCore.erase = right.toCore.erase ↔ left.erase = right.erase := by
  rw [left.core_erase, right.core_erase]
  exact ⟨fun same => Raw.lower_injective same, congrArg Raw.lower⟩

theorem Code.cuts {ctx inputs outputs raw} (code : Code ctx inputs outputs raw) :
    Cuts ctx inputs outputs raw.lower := Proofs.Wasm.Binaryen.Continuation.cuts_of_code code

/-- The independently specified exact-cut Core fragment is precisely the image
of the typed compiler, identifying intrinsic witnesses only by erasure. -/
theorem Code.core_image_iff {ctx inputs outputs ops} :
    (∃ raw, ∃ code : Code ctx inputs outputs raw, code.toCore.erase = ops) ↔
      Cuts ctx inputs outputs ops := by
  constructor
  · rintro ⟨raw, code, equal⟩; rw [← equal, code.core_erase]; exact code.cuts
  · intro cuts; obtain ⟨raw, ⟨code⟩, equal⟩ := Proofs.Wasm.Binaryen.Continuation.code_of_cuts cuts
    exact ⟨raw, code, code.core_erase.trans equal⟩

/-- Read Core's actual intrinsic body, not a second encoding of its typing
derivation. On the exact-cut fragment the returned syntax is unique, even
when the inferred typing witnesses are not. -/
theorem Code.lift_core {ctx inputs outputs} (body : Intrinsic.Body ctx (.plain inputs outputs))
    (exactCuts : Cuts ctx inputs outputs body.erase) :
    ∃ raw, Nonempty (Code ctx inputs outputs raw) ∧ Raw.read body.erase = some raw := by
  obtain ⟨raw, ⟨code⟩, equal⟩ := Proofs.Wasm.Binaryen.Continuation.code_of_cuts exactCuts
  exact ⟨raw, ⟨code⟩, Raw.read_eq_some_iff.mpr equal⟩

end Silmaril.Wasm.Binaryen.Continuation
