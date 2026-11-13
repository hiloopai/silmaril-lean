module

public import Silmaril.Wasm.SpecTec.Sim20.VecLane.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLanePackV

/-!
# The float vector operators as quantifiers of the corrected script

The rules `vunop`, `vbinop-val` and `vrelop` of `Step_pure` quantify the operator at the family
`vunop_(sh)` (`vbinop_(sh)`, `vrelop_(sh)`), with `sh` bound in the scope. At a float shape the
corrected family's first two instances match, and every float operator is one of their nullary
cases (`VecAgree.hasTypInsts_float`). So **`hasTyp_floatOp20V`**: in `simEnv20V B`, in every scope
without type variables binding `sh` to a float shape, each V2 float operator has the family's type.
In `simEnv20T B` the fourteen float-only operators do not (`VecRefute`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V vunopFix20 vbinopFix20 vrelopFix20)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (FloatSh fNames famForm_vunop famForm_vbinop famForm_vrelop
  typDecl FamForm findTyp_fam_simEnv20V hasTypInsts_float)

variable {B : Builtins}

theorem floatSh_shapeV (s : FloatShape) : FloatSh (shapeV (.float s)) := by
  cases s
  · exact ⟨"F32", _, Or.inl rfl, rfl⟩
  · exact ⟨"F64", _, Or.inr rfl, rfl⟩

/-- A float operator at a family read in a scope binding `sh` to a float shape. -/
theorem hasTyp_famFloat {f : String} {d d' : Def} (hf : FamForm d d' f)
    (hV : (simEnv20V B).findTyp? f = some (typDecl d')) {ρ : VarEnv}
    {s : FloatShape} (fsh : ρ.findVal? "sh" = some (shapeV (.float s))) {o : String}
    (ho : o ∈ fNames f) (hl : (fNames f).length ≤ 8) :
    HasTyp (simEnv20V B) ρ (.varT f [.expA (.varE "sh")]) (caseNilV o) := by
  obtain ⟨ps, ji, bs, pats, -, h₂⟩ := hf
  have hl' : localTyp? ρ f [.expA (.varE "sh")] = none := rfl
  have he : evalArgs 18 (simEnv20V B) ρ [.expA (.varE "sh")] = .ok [.val (shapeV (.float s))] := by
    simp [evalArgs, evalArg, evalExp, fsh, Res.ofOption]
  refine ⟨19, ?_⟩
  simp only [hasTyp, hl', hV, h₂, Res.ofOption]
  rw [he]
  exact hasTypInsts_float 2 hl (floatSh_shapeV s) ho

end Silmaril.Wasm.SpecTec.Sim20.VecLane
