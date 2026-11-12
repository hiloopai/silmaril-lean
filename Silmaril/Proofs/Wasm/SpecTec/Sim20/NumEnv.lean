module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureCvt

/-!
# The wasm-2.0 script against the shared numeric library `Equiv.NumEnv`

The integer numerics of rounds 2–4 (`Equiv.callDef_*`) are proved for any environment with
`Equiv.NumEnv`: 25 primitive definitions (`$bool`, `$signed_`, `$iadd_`, `$ieqz_`, …) found
verbatim. For the wasm-2.0 script:

* 24 of the 25 are byte-identical in `simEnv20 B` (`numEnv20_simEnv20`, kernel `rfl`);
* the 25th, `$iextend_`, does not exist in wasm-2.0 (`findDef_iextend20`): 2.0's
  `$unop_(Inn, EXTEND n, …)` calls `$extend__` instead. Hence `not_numEnv_simEnv20`:
  **`Equiv.NumEnv (simEnv20 B)` is false**, and no `Equiv.callDef_*` lemma applies to the
  2.0 script as stated, although each of them reads only its own field.

This is the obstruction to discharging `NumAgree` by reuse: the library's lemmas take the whole
`NumEnv` where one field suffices. Upstream fix (recorded in `docs/projects/spectec/README.md`): state each
`Equiv.callDef_f` over the single lookup `env.findDef? "f" = some fDef` (and `$bool`'s, for the
tests), or split `NumEnv` into `NumEnvCore` (the 24 shared fields, `NumEnv20` here) and
`$iextend_`. `numEnv_of_numEnv20` shows the split is exact.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- The fields of `Equiv.NumEnv` other than `$iextend_`. -/
structure NumEnv20 (env : Env) : Prop where
  /-- `$bool`. -/
  boolD : env.findDef? "bool" = some Equiv.boolDef
  /-- `$signed_`. -/
  signedD : env.findDef? "signed_" = some Equiv.signedDef
  /-- `$inv_signed_`. -/
  invSignedD : env.findDef? "inv_signed_" = some Equiv.invSignedDef
  /-- `$sat_u_`. -/
  satUD : env.findDef? "sat_u_" = some Equiv.satUDef
  /-- `$sat_s_`. -/
  satSD : env.findDef? "sat_s_" = some Equiv.satSDef
  /-- `$ineg_`. -/
  inegD : env.findDef? "ineg_" = some Equiv.inegDef
  /-- `$iabs_`. -/
  iabsD : env.findDef? "iabs_" = some Equiv.iabsDef
  /-- `$iadd_`. -/
  iaddD : env.findDef? "iadd_" = some Equiv.iaddDef
  /-- `$isub_`. -/
  isubD : env.findDef? "isub_" = some Equiv.isubDef
  /-- `$imul_`. -/
  imulD : env.findDef? "imul_" = some Equiv.imulDef
  /-- `$imin_`. -/
  iminD : env.findDef? "imin_" = some Equiv.iminDef
  /-- `$imax_`. -/
  imaxD : env.findDef? "imax_" = some Equiv.imaxDef
  /-- `$iadd_sat_`. -/
  iaddSatD : env.findDef? "iadd_sat_" = some Equiv.iaddSatDef
  /-- `$isub_sat_`. -/
  isubSatD : env.findDef? "isub_sat_" = some Equiv.isubSatDef
  /-- `$ieqz_`. -/
  ieqzD : env.findDef? "ieqz_" = some Equiv.ieqzDef
  /-- `$inez_`. -/
  inezD : env.findDef? "inez_" = some Equiv.inezDef
  /-- `$ieq_`. -/
  ieqD : env.findDef? "ieq_" = some Equiv.ieqDef
  /-- `$ine_`. -/
  ineD : env.findDef? "ine_" = some Equiv.ineDef
  /-- `$ilt_`. -/
  iltD : env.findDef? "ilt_" = some Equiv.iltDef
  /-- `$igt_`. -/
  igtD : env.findDef? "igt_" = some Equiv.igtDef
  /-- `$ile_`. -/
  ileD : env.findDef? "ile_" = some Equiv.ileDef
  /-- `$ige_`. -/
  igeD : env.findDef? "ige_" = some Equiv.igeDef
  /-- `$idiv_`. -/
  idivD : env.findDef? "idiv_" = some Equiv.idivDef
  /-- `$irem_`. -/
  iremD : env.findDef? "irem_" = some Equiv.iremDef

set_option maxRecDepth 100000 in
/-- **24 of the 25 primitives of `Equiv.NumEnv` are wasm-2.0's, verbatim.** -/
theorem numEnv20_simEnv20 (B : Builtins) : NumEnv20 (simEnv20 B) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- wasm-2.0 has no `$iextend_`. -/
theorem findDef_iextend20 (B : Builtins) : (simEnv20 B).findDef? "iextend_" = none := rfl

/-- **`Equiv.NumEnv` fails for the wasm-2.0 script**, at `$iextend_` only. -/
theorem not_numEnv_simEnv20 (B : Builtins) : ¬ Equiv.NumEnv (simEnv20 B) := fun h => by
  have hx : (simEnv20 B).findDef? "iextend_" = some Equiv.iextendDef := h.iextendD
  rw [findDef_iextend20] at hx
  exact absurd hx (by simp)

/-- The split is exact: `NumEnv20` and the `$iextend_` lookup give `Equiv.NumEnv`. -/
theorem numEnv_of_numEnv20 {env : Env} (h : NumEnv20 env)
    (hx : env.findDef? "iextend_" = some Equiv.iextendDef) : Equiv.NumEnv env where
  boolD := h.boolD
  signedD := h.signedD
  invSignedD := h.invSignedD
  satUD := h.satUD
  satSD := h.satSD
  inegD := h.inegD
  iabsD := h.iabsD
  iextendD := hx
  iaddD := h.iaddD
  isubD := h.isubD
  imulD := h.imulD
  iminD := h.iminD
  imaxD := h.imaxD
  iaddSatD := h.iaddSatD
  isubSatD := h.isubSatD
  ieqzD := h.ieqzD
  inezD := h.inezD
  ieqD := h.ieqD
  ineD := h.ineD
  iltD := h.iltD
  igtD := h.igtD
  ileD := h.ileD
  igeD := h.igeD
  idivD := h.idivD
  iremD := h.iremD

/-! ## `NumTyped.numtype`, discharged -/

/-- A nullary-payload case of a closed variant type is typed, in any environment. -/
theorem typedV_closedCase20 {env : Env} {x : IL.Id} {cs : List TypCase} {op : MixopS} {t : Typ}
    {w : Value} (htd : env.findTyp? x = some ([], [.instD [] [] (.variantT cs)]))
    (hf : Silmaril.Wasm.SpecTec.Sim.IntNumeric.findCase cs op = some (t, []))
    (hw : HasTyp env VarEnv.empty t w) :
    Silmaril.Wasm.SpecTec.Sim.TypedV env (.varT x []) (.case op w) :=
  fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd
    Equiv.evalArgs_nil matchArgs_nil
    (Silmaril.Wasm.SpecTec.Sim.IntNumeric.hasTypCase_of_findCase hf hw premsOk_nil
      (Silmaril.Wasm.SpecTec.Sim.IntNumeric.quantFreeAt_of_findCase_nil hf))

set_option maxRecDepth 100000 in
/-- The wasm-2.0 `numtype`. -/
theorem findTyp_numtype20 (B : Builtins) : (simEnv20 B).findTyp? "numtype" =
    some ([], [.instD [] [] (.variantT (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d56 0))]) := rfl

/-- **`NumTyped.numtype` holds**: every V2 number type is an IL `numtype`. -/
theorem typedV_numtype20 (B : Builtins) (t : Silmaril.Wasm.NumType) :
    Silmaril.Wasm.SpecTec.Sim.TypedV (simEnv20 B) (.varT "numtype" []) (numTypeV t) := by
  rcases t with (_ | _) | (_ | _) <;>
    exact typedV_closedCase20 (findTyp_numtype20 B) rfl hasTyp_tupT_nil

/-! ## `CvtTyped`, discharged -/

set_option maxRecDepth 100000 in
/-- The wasm-2.0 `sx`. -/
theorem findTyp_sx20 (B : Builtins) : (simEnv20 B).findTyp? "sx" =
    some ([], [.instD [] [] (.variantT (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d102 0))]) := rfl

set_option maxRecDepth 100000 in
/-- The wasm-2.0 `cvtop`. -/
theorem findTyp_cvtop20 (B : Builtins) : (simEnv20 B).findTyp? "cvtop" =
    some ([], [.instD [] [] (.variantT (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d108 0))]) := rfl

/-- Every signedness is an IL `sx`. -/
theorem typedV_sx20 (B : Builtins) (s : Silmaril.Wasm.Signedness) :
    Silmaril.Wasm.SpecTec.Sim.TypedV (simEnv20 B) (.varT "sx" []) (sxV s) := by
  cases s <;> exact typedV_closedCase20 (findTyp_sx20 B) rfl hasTyp_tupT_nil

/-- **`CvtTyped` holds**: every V2 conversion operator is an IL `cvtop`. -/
theorem cvtTyped_simEnv20 (B : Builtins) : CvtTyped (simEnv20 B) := fun op => by
  cases op <;> first
    | exact typedV_closedCase20 (findTyp_cvtop20 B) rfl hasTyp_tupT_nil
    | exact typedV_closedCase20 (findTyp_cvtop20 B) rfl (typedV_sx20 B _ _ ⟨rfl, rfl, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim20.Pure
