module

public import Silmaril.Proofs.Wasm.Component.Reference.SoundI
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusImp

/-!
# Soundness with imports on the litmus component `fwdS`

`fwdS` (import `g: func(u32) -> u32` lowered into a core module that re-exports it as `f`,
lifted) is wired as `SimpleI.toRef` assumes (`fwdS_inst`: its core module imports `"env" "g"` at
exactly the flat type a `canon lower` allocates, checked by kernel evaluation of the validator),
float-free and within the flat arities, and the host `g(n) = n + 1` (`fwdG`) answers in the IR's
types (`fwdG_ok`). Hence `fwd_sound`: at every profile and component choice profile, every
reference behaviour of `f(x)` under the host `answerHost P fwdG` is matched by the IR
denotation over `impSem P`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Numerics (Profile)

/-- The validated import types of `fwdCore3`, summarised. -/
def fwdImportsSummary : Bool :=
  match Silmaril.Wasm.Validation.validate? fwdCore3 with
  | some mt => decide (mt.imports =
      [.func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨[.int .i32], [.int .i32]⟩)])
  | none => false

theorem fwdImportsSummary_eq : fwdImportsSummary = true := by decide +kernel

theorem fwd_importTypes : ∃ mt, Silmaril.Wasm.Validation.validate? fwdCore3 = some mt ∧
    mt.imports = fwdS.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩) := by
  have h : fwdImportsSummary = true := fwdImportsSummary_eq
  unfold fwdImportsSummary at h
  split at h
  next mt hmt => exact ⟨mt, hmt, of_decide_eq_true h⟩
  next => cases h

/-- **`fwdS` is wired as `SimpleI.toRef` assumes.** -/
theorem fwdS_inst : fwdS.Inst :=
  ⟨⟨fwdInst, fwd_isInst⟩, rfl, by decide, rfl, fwd_importTypes⟩

theorem fwdS_floatFree : fwdS.FloatFree := by
  unfold SimpleI.FloatFree
  decide

theorem fwdS_arity : fwdS.Arity := by
  unfold SimpleI.Arity
  decide

/-- The host `g(n) = n + 1` answers in the IR's types. -/
theorem fwdG_ok : fwdS.HostOk fwdG := by
  intro k hk ws rs h
  have hk0 : k = 0 := by simpa [fwdS] using hk
  subst hk0
  match ws, h with
  | [.u32 x], h =>
    have hrs : rs = [toRefVal (.u32 (BitVec.ofNat 32 (x.toNat + 1)))] := by
      simp only [fwdG, toRefVal, List.map_cons, List.map_nil, Option.some.injEq] at h
      rw [← h]
      simp only [toRefVal, BitVec.toNat_ofNat]
      congr 2
    exact ⟨[.u32 (BitVec.ofNat 32 (x.toNat + 1))], hrs, rfl⟩

/-- **Soundness with imports on `fwdS`** (every profile and component choice profile, all
`x`): every reference behaviour of `f(x)` under the host `g(n) = n + 1` is matched by the IR
denotation (`IRObsI`). -/
theorem fwd_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (x : BitVec 32) :
    ∀ b ∈ exportBehavioursI prof (answerHost P fwdG) () fwdS.toRef fwdS.imports "f"
        [toRefVal (.u32 x)],
      IRObsI (fwdS.toComp.den (impSem P)) ⟨0, by decide⟩ [.u32 x] fwdG b :=
  simpleI_sound P prof fwdS fwdS_good fwdS_inst fwdS_floatFree fwdS_arity fwdG fwdG_ok
    ⟨0, by decide⟩ [.u32 x] rfl

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
