module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.UndefUn
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.UndefBinInt
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.UndefBinFloat
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.UndefTern
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.UndefRel
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.UndefMisc
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.UndefExt

/-!
# Round 5, track simd (pass 3): the lane-wise fields of `VecAgreeOps` at the concrete builtins

Every clause of the lane-wise operators definitely fails (`Undef*.lean`), so each call denotes
`Prims.builtins`' answer, `vecOpCall` (`Round5/Lanes/Defs.lean`), which decodes the arguments
(`decodeArgs_enc`) and answers Core's vector numerics.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30
open Round4Int (BI)

variable {H : Type} {P : Profile} {hn : H → String} {host : HostSemantics H}

/-- `Prims.builtins` answers the lane-wise operators by `vecOpCall`. -/
theorem call_vecOp (x : IL.Id) (hx : x ∈ ["vunop_", "vbinop_", "vternop_", "vrelop_", "vshiftop_",
    "vbitmaskop_", "vswizzlop_", "vshufflop_", "vextunop__", "vextbinop__", "vextternop__",
    "vnarrowop__", "vcvtop__"]) (ws : List ArgV) :
    (simEnv (BI P hn host)).builtins.call x ws = vecOpCall P x ws := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [simEnv, Env.withBuiltins, Prims.builtins, Prims.call, IntNumeric.intCall,
      Floats.floatCall, Floats.floatNames]

/-- The script's definitions are `decD`s. -/
theorem decD_of {d : Def} (h : ∃ y ps t cs, d = .decD y ps t cs) :
    ∃ y ps t cs, d = .decD y ps t cs := h

/-- `someVec` of a functional relation answers exactly its solution. -/
theorem someVec_iff {R : V128 → Prop} (hu : ∀ r r', R r → R r' → r = r') (c : Value) :
    someVec R = some c ↔ ∃ r, R r ∧ c = Vec.vecV r := by
  constructor
  · exact someVec_sound
  · rintro ⟨r, hr, rfl⟩
    exact someVec_unique hr fun r' h => hu _ _ h hr

/-- **`VecAgreeOps.intUnOp`** at the concrete builtins. -/
theorem f_intUnOp (s : IntShape) (op : VecIntUnOp) (a : V128) :
    Applies (simEnv (BI P hn host)) "vunop_"
      [.val (Vec.ishV s), .val (Vec.vIntUnOpV op), .val (Vec.vecV a)]
      (.list [Vec.vecV (vecIntUnOp s op a)]) := by
  refine (applies_iff_of_undef' (findDef_Vunop _) ⟨_, _, _, _, rfl⟩
    (undef_IntUnOp P hn host s op a)).2 ?_
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vunop_" (encIntUnOp (s, op, a)) = _
  simp [vecOpCall, decodeArgs_enc encIntUnOp_injective]

/-- **`VecAgreeOps.floatUnOp`** at the concrete builtins. -/
theorem f_floatUnOp (s : FloatShape) (op : FloatUnOp) (a : V128) :
    ∃ L, Applies (simEnv (BI P hn host)) "vunop_"
      [.val (Vec.fshV s), .val (Vec.vFloatUnOpV op), .val (Vec.vecV a)] (.list L) ∧
      ∀ c, c ∈ L ↔ ∃ r, VecFloatUnOpRel P s op a r ∧ c = Vec.vecV r := by
  refine ⟨_, (applies_iff_of_undef' (findDef_Vunop _) ⟨_, _, _, _, rfl⟩
    (undef_FloatUnOp P hn host s op a)).2 ?_, fun c => mem_vecsOf⟩
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vunop_" (encFloatUnOp (s, op, a)) = _
  simp [vecOpCall, decodeArgs_enc encFloatUnOp_injective,
    decodeArgs_none fun q => encIntUnOp_ne q (s, op, a)]

/-- **`VecAgreeOps.intBinOp`** at the concrete builtins. -/
theorem f_intBinOp (s : IntShape) (op : VecIntBinOp) (a b : V128) :
    Applies (simEnv (BI P hn host)) "vbinop_"
      [.val (Vec.ishV s), .val (Vec.vIntBinOpV op), .val (Vec.vecV a), .val (Vec.vecV b)]
      (.list [Vec.vecV (vecIntBinOp P s op a b)]) := by
  refine (applies_iff_of_undef' (findDef_Vbinop _) ⟨_, _, _, _, rfl⟩
    (undef_IntBinOp P hn host s op a b)).2 ?_
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vbinop_" (encIntBinOp (s, op, a, b)) = _
  simp [vecOpCall, decodeArgs_enc encIntBinOp_injective]

/-- **`VecAgreeOps.floatBinOp`** at the concrete builtins. -/
theorem f_floatBinOp (s : FloatShape) (op : VecFloatBinOp) (a b : V128) :
    ∃ L, Applies (simEnv (BI P hn host)) "vbinop_"
      [.val (Vec.fshV s), .val (Vec.vFloatBinOpV op), .val (Vec.vecV a), .val (Vec.vecV b)]
      (.list L) ∧ ∀ c, c ∈ L ↔ ∃ r, VecFloatBinOpRel P s op a b r ∧ c = Vec.vecV r := by
  refine ⟨_, (applies_iff_of_undef' (findDef_Vbinop _) ⟨_, _, _, _, rfl⟩
    (undef_FloatBinOp P hn host s op a b)).2 ?_, fun c => mem_vecsOf⟩
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vbinop_" (encFloatBinOp (s, op, a, b)) = _
  simp [vecOpCall, decodeArgs_enc encFloatBinOp_injective,
    decodeArgs_none fun q => encIntBinOp_ne q (s, op, a, b)]

/-- **`VecAgreeOps.intTernOp`** at the concrete builtins. -/
theorem f_intTernOp (s : IntShape) (op : VecIntTernOp) (a b c : V128) :
    Applies (simEnv (BI P hn host)) "vternop_"
      [.val (Vec.ishV s), .val (Vec.vIntTernOpV op), .val (Vec.vecV a), .val (Vec.vecV b),
        .val (Vec.vecV c)] (.list [Vec.vecV (vecIntTernOp P s op a b c)]) := by
  refine (applies_iff_of_undef' (findDef_Vternop _) ⟨_, _, _, _, rfl⟩
    (undef_IntTernOp P hn host s op a b c)).2 ?_
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vternop_" (encIntTernOp (s, op, a, b, c)) = _
  simp [vecOpCall, decodeArgs_enc encIntTernOp_injective]

/-- **`VecAgreeOps.floatTernOp`** at the concrete builtins. -/
theorem f_floatTernOp (s : FloatShape) (op : VecFloatTernOp) (a b c : V128) :
    ∃ L, Applies (simEnv (BI P hn host)) "vternop_"
      [.val (Vec.fshV s), .val (Vec.vFloatTernOpV op), .val (Vec.vecV a), .val (Vec.vecV b),
        .val (Vec.vecV c)] (.list L) ∧
      ∀ d, d ∈ L ↔ ∃ r, VecFloatTernOpRel P s op a b c r ∧ d = Vec.vecV r := by
  refine ⟨_, (applies_iff_of_undef' (findDef_Vternop _) ⟨_, _, _, _, rfl⟩
    (undef_FloatTernOp P hn host s op a b c)).2 ?_, fun d => mem_vecsOf⟩
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vternop_" (encFloatTernOp (s, op, a, b, c)) = _
  simp [vecOpCall, decodeArgs_enc encFloatTernOp_injective,
    decodeArgs_none fun q => encIntTernOp_ne q (s, op, a, b, c)]

/-- **`VecAgreeOps.intRelOp`** at the concrete builtins. -/
theorem f_intRelOp (s : IntShape) (op : IntRelOp) (a b : V128) :
    Applies (simEnv (BI P hn host)) "vrelop_"
      [.val (Vec.ishV s), .val (Vec.vIntRelOpV op), .val (Vec.vecV a), .val (Vec.vecV b)]
      (Vec.vecV (vecIntRelOp s op a b)) := by
  refine (applies_iff_of_undef' (findDef_Vrelop _) ⟨_, _, _, _, rfl⟩
    (undef_IntRelOp P hn host s op a b)).2 ?_
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vrelop_" (encIntRelOp (s, op, a, b)) = _
  simp [vecOpCall, decodeArgs_enc encIntRelOp_injective]

/-- **`VecAgreeOps.floatRelOp`** at the concrete builtins. -/
theorem f_floatRelOp (s : FloatShape) (op : FloatRelOp) (a b : V128) :
    Applies (simEnv (BI P hn host)) "vrelop_"
      [.val (Vec.fshV s), .val (Vec.vFloatRelOpV op), .val (Vec.vecV a), .val (Vec.vecV b)]
      (Vec.vecV (vecFloatRelOp s op a b)) := by
  refine (applies_iff_of_undef' (findDef_Vrelop _) ⟨_, _, _, _, rfl⟩
    (undef_FloatRelOp P hn host s op a b)).2 ?_
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vrelop_" (encFloatRelOp (s, op, a, b)) = _
  simp [vecOpCall, decodeArgs_enc encFloatRelOp_injective,
    decodeArgs_none fun q => encIntRelOp_ne q (s, op, a, b)]

/-- **`VecAgreeOps.shiftOp`** at the concrete builtins. -/
theorem f_shiftOp (s : IntShape) (op : VecShiftOp) (a : V128) (n : BitVec 32) :
    Applies (simEnv (BI P hn host)) "vshiftop_"
      [.val (Vec.ishapeV s), .val (Vec.vShiftOpV op), .val (Vec.vecV a), .val (Vec.i32NV n)]
      (Vec.vecV (vecShiftOp s op a n)) := by
  refine (applies_iff_of_undef' (findDef_Vshiftop _) ⟨_, _, _, _, rfl⟩
    (undef_ShiftOp P hn host s op a n)).2 ?_
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vshiftop_" (encShiftOp (s, op, a, n)) = _
  simp [vecOpCall, decodeArgs_enc encShiftOp_injective]

/-- **`VecAgreeOps.bitmask`** at the concrete builtins. -/
theorem f_bitmask (s : IntShape) (a : V128) :
    Applies (simEnv (BI P hn host)) "vbitmaskop_" [.val (Vec.ishapeV s), .val (Vec.vecV a)]
      (Vec.i32NV (vecBitmask s a)) := by
  refine (applies_iff_of_undef' (findDef_Vbitmaskop _) ⟨_, _, _, _, rfl⟩
    (undef_Bitmask P hn host s a)).2 ?_
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vbitmaskop_" (encBitmask (s, a)) = _
  simp [vecOpCall, decodeArgs_enc encBitmask_injective]

/-- `$vswizzlop_` at the concrete builtins. -/
theorem f_swizzleOp (op : VecSwizzleOp) (a b : V128) :
    Applies (simEnv (BI P hn host)) "vswizzlop_"
      [.val Vec.bshapeV, .val (Vec.vSwizzleOpV op), .val (Vec.vecV a), .val (Vec.vecV b)]
      (Vec.vecV (swizzleOp P op a b)) := by
  refine (applies_iff_of_undef' (findDef_Vswizzlop _) ⟨_, _, _, _, rfl⟩
    (undef_Swizzle P hn host op a b)).2 ?_
  rw [call_vecOp _ (by simp)]
  show vecOpCall P "vswizzlop_" (encSwizzle (op, a, b)) = _
  simp [vecOpCall, decodeArgs_enc encSwizzle_injective]

/-- **`VecAgreeOps.narrow`** at the concrete builtins. -/
theorem f_narrow (s t : IntShape) (sx : Signedness) (a b : V128) (c : Value) :
    Applies (simEnv (BI P hn host)) "vnarrowop__"
      [.val (Vec.ishV s), .val (Vec.ishV t), .val (Vec.sxV sx), .val (Vec.vecV a),
        .val (Vec.vecV b)] c ↔ ∃ r, VecNarrowRel s t sx a b r ∧ c = Vec.vecV r := by
  show Applies _ _ (encNarrow (s, t, sx, a, b)) c ↔ _
  rw [applies_iff_of_undef' (findDef_Vnarrowop _) ⟨_, _, _, _, rfl⟩
    (undef_Narrow P hn host s t sx a b), call_vecOp _ (by simp)]
  show vecOpCall P "vnarrowop__" (encNarrow (s, t, sx, a, b)) = _ ↔ _
  simp only [vecOpCall, decodeArgs_enc encNarrow_injective, Option.bind_some]
  exact someVec_iff (fun r r' h h' => h.trans h'.symm) c

/-- **`VecAgreeOps.extUnOp`** at the concrete builtins. -/
theorem f_extUnOp (s t : IntShape) (op : VecExtUnOp) (a : V128) (c : Value) :
    Applies (simEnv (BI P hn host)) "vextunop__"
      [.val (Vec.ishapeV s), .val (Vec.ishapeV t), .val (Vec.vExtUnOpV op), .val (Vec.vecV a)] c ↔
      ∃ r, VecExtUnOpRel s t op a r ∧ c = Vec.vecV r := by
  show Applies _ _ (encExtUnOp (s, t, op, a)) c ↔ _
  rw [applies_iff_of_undef' (findDef_Vextunop _) ⟨_, _, _, _, rfl⟩
    (undef_ExtUnOp P hn host s t op a), call_vecOp _ (by simp)]
  show vecOpCall P "vextunop__" (encExtUnOp (s, t, op, a)) = _ ↔ _
  simp only [vecOpCall, decodeArgs_enc encExtUnOp_injective, Option.bind_some]
  exact someVec_iff (fun r r' h h' => h.trans h'.symm) c

/-- **`VecAgreeOps.extBinOp`** at the concrete builtins. -/
theorem f_extBinOp (s t : IntShape) (op : VecExtBinOp) (a b : V128) (c : Value) :
    Applies (simEnv (BI P hn host)) "vextbinop__"
      [.val (Vec.ishapeV s), .val (Vec.ishapeV t), .val (Vec.vExtBinOpV op), .val (Vec.vecV a),
        .val (Vec.vecV b)] c ↔ ∃ r, VecExtBinOpRel P s t op a b r ∧ c = Vec.vecV r := by
  show Applies _ _ (encExtBinOp (s, t, op, a, b)) c ↔ _
  rw [applies_iff_of_undef' (findDef_Vextbinop _) ⟨_, _, _, _, rfl⟩
    (undef_ExtBinOp P hn host s t op a b), call_vecOp _ (by simp)]
  show vecOpCall P "vextbinop__" (encExtBinOp (s, t, op, a, b)) = _ ↔ _
  simp only [vecOpCall, decodeArgs_enc encExtBinOp_injective, Option.bind_some]
  refine someVec_iff (fun r r' h h' => ?_) c
  cases op <;> simp_all [VecExtBinOpRel]

/-- **`VecAgreeOps.extTernOp`** at the concrete builtins. -/
theorem f_extTernOp (s t : IntShape) (op : VecExtTernOp) (a b d : V128) (c : Value) :
    Applies (simEnv (BI P hn host)) "vextternop__"
      [.val (Vec.ishapeV s), .val (Vec.ishapeV t), .val (Vec.vExtTernOpV op), .val (Vec.vecV a),
        .val (Vec.vecV b), .val (Vec.vecV d)] c ↔
      ∃ r, VecExtTernOpRel P s t op a b d r ∧ c = Vec.vecV r := by
  show Applies _ _ (encExtTernOp (s, t, op, a, b, d)) c ↔ _
  rw [applies_iff_of_undef' (findDef_Vextternop _) ⟨_, _, _, _, rfl⟩
    (undef_ExtTernOp P hn host s t op a b d), call_vecOp _ (by simp)]
  show vecOpCall P "vextternop__" (encExtTernOp (s, t, op, a, b, d)) = _ ↔ _
  simp only [vecOpCall, decodeArgs_enc encExtTernOp_injective, Option.bind_some]
  exact someVec_iff (fun r r' h h' => h.trans h'.symm) c

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
