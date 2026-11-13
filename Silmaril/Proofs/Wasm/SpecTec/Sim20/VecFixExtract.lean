module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixCase
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixLane
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixShape
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixPrem

/-!
# The vector errata: every valid `VEXTRACT_LANE` is an `admininstr` of `simEnv20V B`

`typedA_extract20V`: the payload is typed (`typedV_shape20V`, `typedV_sx20V`,
`typedV_laneidx20V`), the corrected case has no quantifier (`findCase_extract20V`), and its
premise holds (`premsOk_extract20V`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

variable {B : Builtins}

/-- A triple of payloads, each typed in every term-only scope (any environment). -/
theorem hasTyp_tup3G {env : Env} {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u v w : Value}
    (h₁ : TypedV env τ₁ u) (h₂ : HasTyp env (VarEnv.empty.bindVal a u) τ₂ v)
    (h₃ : TypedV env τ₃ w) :
    HasTyp env VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u, v, w]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂,
      hasTypTup_cons_iff.2 ⟨_, _, rfl,
        h₃ _ (Sim.ConfigOk.valsOnly_bindVal (Sim.ConfigOk.valsOnly_bindVal ⟨rfl, rfl, rfl⟩ _ _) _ _),
        hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩

/-- The sign option of `VEXTRACT_LANE` is an `sx?`. -/
theorem hasTyp_sxOpt20V (ρ : VarEnv) (hρ : ValsOnly ρ) (sx : Option Signedness) :
    HasTyp (simEnv20V B) ρ (.iterT (.varT "sx" []) .opt) (.opt (sx.map sxV)) := by
  rcases sx with _ | sx
  · exact hasTyp_iterT_opt_iff.2 (Or.inl rfl)
  · exact hasTyp_iterT_opt_iff.2 (Or.inr ⟨_, rfl, typedV_sx20V sx ρ hρ⟩)

/-- **Every valid `VEXTRACT_LANE` is an `admininstr` of `simEnv20V B`.** -/
theorem typedA_extract20V (s : Shape) (sx : Option Signedness) (l : LaneIdx)
    (h : (V2.Instr.vecExtractLane s sx l).immediatesValid = true) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecExtractLane s sx l)) := by
  rw [instrToV_extract]
  exact typedV_adminCase20V findCase_extract20V.1 findCase_extract20V.2
    (hasTyp_tup3G (typedV_shape20V s)
      (hasTyp_sxOpt20V _ (Sim.ConfigOk.valsOnly_bindVal ⟨rfl, rfl, rfl⟩ _ _) sx)
      (typedV_laneidx20V l))
    (premsOk_extract20V s sx l h)

end Silmaril.Wasm.SpecTec.Sim20.VecFix
