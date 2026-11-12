module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Shuffle

/-!
# Round 5, track simd (pass 3): `VecAgreeLanes` at the concrete builtins

All seventeen fields of `VecAgreeOps` other than `convert` hold at `Prims.builtins`
(`vecAgreeLanes_builtins`). The restated conversion field `VecConvertR` follows from the
definite failure of `$vcvtop__`'s clauses (`vecConvertR_of_undef`), which is not proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30
open Round4Int (BI)

variable {H : Type} {P : Profile} {hn : H → String} {host : HostSemantics H}

/-- **`VecAgreeLanes` at the concrete builtins.** -/
theorem vecAgreeLanes_builtins : VecAgreeLanes (simEnv (BI P hn host)) P where
  intUnOp := f_intUnOp
  floatUnOp := f_floatUnOp
  intBinOp := f_intBinOp
  floatBinOp := f_floatBinOp
  intTernOp := f_intTernOp
  floatTernOp := f_floatTernOp
  intRelOp := f_intRelOp
  floatRelOp := f_floatRelOp
  shiftOp := f_shiftOp
  bitmask := f_bitmask
  swizzle := f_swizzleOp .swizzle
  relaxedSwizzle := f_swizzleOp .relaxedSwizzle
  shuffle := f_shuffle
  extUnOp := f_extUnOp
  extBinOp := f_extBinOp
  extTernOp := f_extTernOp
  narrow := f_narrow

/-- `VecAgreeOps` is `VecAgreeLanes` and the original `convert` field. -/
theorem vecAgreeOps_of_lanes {env : Env} (L : VecAgreeLanes env P)
    (hc : ∀ s t op a c, Applies env "vcvtop__"
      [.val (Vec.shapeV s), .val (Vec.shapeV t), .val (Vec.vConvertOpV op), .val (Vec.vecV a)] c ↔
      ∃ r, VecConvertRel P s t op a r ∧ c = Vec.vecV r) : VecAgreeOps env P :=
  { L with convert := hc }

/-- **`VecConvertR` at the concrete builtins, from the definite failure of `$vcvtop__`'s
clauses**: `vecOpCall` answers an allowed result whenever there is one. -/
theorem vecConvertR_of_undef
    (hu : ∀ s t op a, TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d539)
      (encConvert (s, t, op, a))) : VecConvertR (simEnv (BI P hn host)) P where
  sound s t op a c h := by
    have h' : Applies _ _ (encConvert (s, t, op, a)) c := h
    rw [applies_iff_of_undef' (findDef_Vcvtop _) ⟨_, _, _, _, rfl⟩ (hu s t op a),
      call_vecOp _ (by simp)] at h'
    simp only [vecOpCall, decodeArgs_enc encConvert_injective, Option.bind_some] at h'
    exact someVec_sound h'
  total s t op a r hr := by
    obtain ⟨c, hc⟩ := someVec_isSome (R := VecConvertRel P s t op a) ⟨r, hr⟩
    refine ⟨c, ?_⟩
    show Applies _ _ (encConvert (s, t, op, a)) c
    rw [applies_iff_of_undef' (findDef_Vcvtop _) ⟨_, _, _, _, rfl⟩ (hu s t op a),
      call_vecOp _ (by simp)]
    simpa only [vecOpCall, decodeArgs_enc encConvert_injective, Option.bind_some] using hc

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
