module

public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Round 6: the IL encoding of memory SIMD is typed

`typedV_vecMemV`: for **every** memory SIMD instruction `i` (no validity needed) and every `B`,
`instrToVM i` is a typed `instr` in `simEnv B`. The payloads are the vector type `V128`, the
memory index (`memidx`), the IL record `memarg` (as for `LOAD`/`STORE`), `sz`, a `laneidx`
(`u8`; Core's lane indices are `Fin (2 ^ 8)`), and for `VLOAD` an optional `vloadop_(V128)`:

* `SHAPE sz X M _ sx`, whose premise `sz * M = $vsize(V128) / 2` holds at `8 X 8`, `16 X 4`,
  `32 X 2` (`evalExp_shapePrem`);
* `SPLAT sz`, with no premise;
* `ZERO sz`, whose premise `sz >= 32` holds at `32` and `64`.

By contrast the provisional image `instrToV i` is a typed `instr` for none of them: its memory
argument is a `$record` case (`not_typedV_instrToV_memSimd`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d250)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## `vloadop_(vectype)` -/

/-- The scope of the `vloadop_` instance: `vectype` bound to `V128`. -/
abbrev vtScope : VarEnv := VarEnv.empty.bindVal "vectype" Vec.vecTypeV

set_option maxRecDepth 100000 in
theorem findTyp_vloadop : ∃ ps q, (simEnv B).findTyp? "vloadop_" =
    some (ps, [.instD q [.expA (.varE "vectype")] (.variantT (IntNumeric.instCases Original.d250 0))]) :=
  ⟨_, _, rfl⟩

/-- **`vloadop_(vectype)` holds a case typed in the instance scope**, at `vectype = V128`. -/
theorem hasTyp_vloadop {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv B) vtScope (IntNumeric.instCases Original.d250 0) op w) :
    HasTyp (simEnv B) vtScope (.varT "vloadop_" [.expA (.varE "vectype")]) (.case op w) := by
  obtain ⟨ps, q, htd⟩ := findTyp_vloadop (B := B)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd
    (evalArgs_cons (evalExp_var (by simp)) evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)
      (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩))

/-- `sz` at a width, in any term-only scope. -/
theorem hasTyp_szW {ρ : VarEnv} (hρ : ValsOnly ρ) (p : PackSize) :
    HasTyp (simEnv B) ρ (.varT "sz" []) (szV p) :=
  IntNumeric.hasTyp_sz hρ p

/-- A three-field payload, each field typed in every term-only scope. -/
theorem hasTypTup3 {σ : VarEnv} {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u v w : Value}
    (h₁ : HasTyp (simEnv B) σ τ₁ u) (h₂ : HasTyp (simEnv B) (σ.bindVal a u) τ₂ v)
    (h₃ : HasTyp (simEnv B) ((σ.bindVal a u).bindVal b v) τ₃ w) :
    HasTyp (simEnv B) σ (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u, v, w]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₃,
      hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩

/-- The scope `SHAPE sz X M _ sx`'s premise is read in. -/
abbrev shapeScope (k m : Nat) (s : Signedness) : VarEnv :=
  caseScope vtScope (.tupT [.mk "sz" (.varT "sz" []), .mk "M" (.varT "M" []),
    .mk "sx" (.varT "sx" [])]) (.tuple [pctV k, pctV m, Vec.sxV s])

/-- The premise of `SHAPE sz X M _ sx`. -/
noncomputable def shapePrem : Exp :=
  .cmpE .eqOp .boolT (.cvtE (.binE .mulOp (.numT .natT) (.projE (.uncaseE (.varE "sz") "%") 0)
    (.projE (.uncaseE (.varE "M") "%") 0)) .natT .ratT)
    (.binE .divOp (.numT .ratT) (.cvtE (.callE "vsize" [.expA (.varE "vectype")]) .natT .ratT)
      (.cvtE (.numE (.natN 2)) .natT .ratT))

/-- **`sz * M = $vsize(V128) / 2` holds when `sz * M = 64`.** -/
theorem evalExp_shapePrem {k m : Nat} (s : Signedness) (hkm : k * m = 64) :
    EvalExp (simEnv B) (shapeScope k m s) shapePrem (.bool true) := by
  have hsz : EvalExp (simEnv B) (shapeScope k m s) (.projE (.uncaseE (.varE "sz") "%") 0)
      (.num (.natN k)) := IntNumeric.evalExp_pctPayload (by simp [caseScope, typBinds, pctV])
  have hM : EvalExp (simEnv B) (shapeScope k m s) (.projE (.uncaseE (.varE "M") "%") 0)
      (.num (.natN m)) := IntNumeric.evalExp_pctPayload (by simp [caseScope, typBinds, pctV])
  have hl : EvalExp (simEnv B) (shapeScope k m s)
      (.cvtE (.binE .mulOp (.numT .natT) (.projE (.uncaseE (.varE "sz") "%") 0)
        (.projE (.uncaseE (.varE "M") "%") 0)) .natT .ratT) (.num (.ratN 64)) := by
    refine evalExp_cvtNum (evalExp_binNum hsz hM rfl) ?_
    simp [Num.cvt, hkm]
  have hv : EvalExp (simEnv B) (shapeScope k m s) (.callE "vsize" [.expA (.varE "vectype")])
      (natV 128) :=
    Vec.evalExp_call (by simp [caseScope, typBinds, VarEnv.findDef?, VarEnv.bindVal,
      VarEnv.empty])
      (evalArgs_cons (evalExp_var (by simp [caseScope, typBinds])) evalArgs_nil)
      FwdSimdAgg.applies_vsize
  have hr : EvalExp (simEnv B) (shapeScope k m s)
      (.binE .divOp (.numT .ratT) (.cvtE (.callE "vsize" [.expA (.varE "vectype")]) .natT .ratT)
        (.cvtE (.numE (.natN 2)) .natT .ratT)) (.num (.ratN 64)) := by
    refine evalExp_binNum (evalExp_cvtNum hv rfl) (evalExp_cvtNum evalExp_num rfl) ?_
    simp only [Num.bin]
    norm_num
  exact evalExp_cmpE_iff.2 ⟨_, _, hl, hr, by simp [cmpValues]⟩

/-- `SHAPE sz X M _ sx` at a shape with `sz * M = 64`. -/
theorem hasTypCase_shape (p : PackSize) (sh : Shape) (s : Signedness)
    (hkm : p.width * sh.lanes = 64) :
    HasTypCase (simEnv B) vtScope (IntNumeric.instCases Original.d250 0) "SHAPE%X%_%"
      (.tuple [szV p, pctV sh.lanes, Vec.sxV s]) :=
  IntNumeric.hasTypCase_of_findCase rfl
    (hasTypTup3 (hasTyp_szW ⟨rfl, rfl, rfl⟩ p) (Round5.SimdTy.typedV_M sh _ ⟨rfl, rfl, rfl⟩)
      (Round5.SimdTy.typedV_vsx s _ ⟨rfl, rfl, rfl⟩))
    (IntNumeric.premsOk_if (evalExp_shapePrem s hkm))

/-- The scope `ZERO sz`'s premise is read in. -/
abbrev zeroScope (k : Nat) : VarEnv :=
  caseScope vtScope (.tupT [.mk "sz" (.varT "sz" [])]) (.tuple [pctV k])

/-- `ZERO sz` at a width of at least `32`. -/
theorem hasTypCase_zero (p : PackSize) (hp : 32 ≤ p.width) :
    HasTypCase (simEnv B) vtScope (IntNumeric.instCases Original.d250 0) "ZERO"
      (.tuple [szV p]) := by
  have hsz : EvalExp (simEnv B) (zeroScope p.width) (.projE (.uncaseE (.varE "sz") "%") 0)
      (.num (.natN p.width)) := IntNumeric.evalExp_pctPayload (by simp [caseScope, typBinds, pctV])
  refine IntNumeric.hasTypCase_of_findCase rfl
    (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_szW ⟨rfl, rfl, rfl⟩ p,
      hasTypTup_nil_iff.2 rfl⟩⟩) (IntNumeric.premsOk_if ?_)
  exact evalExp_cmpNum hsz evalExp_num (by simp [Num.cmp, hp])

/-- `SPLAT sz`. -/
theorem hasTypCase_splat (p : PackSize) :
    HasTypCase (simEnv B) vtScope (IntNumeric.instCases Original.d250 0) "SPLAT" (szV p) :=
  IntNumeric.hasTypCase_of_findCase rfl (hasTyp_szW ⟨rfl, rfl, rfl⟩ p) premsOk_nil

/-- **Every `vloadop_(V128)?` image is typed.** -/
theorem hasTyp_vecLoadOpV (op : VecLoadOp) :
    HasTyp (simEnv B) vtScope (.iterT (.varT "vloadop_" [.expA (.varE "vectype")]) .opt)
      (.opt (vecLoadOpV op)) := by
  cases op with
  | full => exact hasTyp_iterT_opt_iff.2 (.inl rfl)
  | extend8x8 s =>
    exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, hasTyp_vloadop
      (hasTypCase_shape .i8 (.int .i16x8) s rfl)⟩)
  | extend16x4 s =>
    exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, hasTyp_vloadop
      (hasTypCase_shape .i16 (.int .i32x4) s rfl)⟩)
  | extend32x2 s =>
    exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, hasTyp_vloadop
      (hasTypCase_shape .i32 (.int .i64x2) s rfl)⟩)
  | splat p => exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, hasTyp_vloadop (hasTypCase_splat p)⟩)
  | zero32 =>
    exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, hasTyp_vloadop (hasTypCase_zero .i32 (by decide))⟩)
  | zero64 =>
    exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, hasTyp_vloadop (hasTypCase_zero .i64 (by decide))⟩)

/-! ## The four instructions -/

set_option maxRecDepth 100000 in
/-- `VLOAD V128 vloadop? x ao`. -/
theorem typedV_vecLoad (op : VecLoadOp) (m : MemIdx) (a : MemArg) :
    TypedV (simEnv B) (.varT "instr" []) (instrToVM (.vecLoad op m a)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    Round5.SimdTy.typedV_vectype _ ⟨rfl, rfl, rfl⟩, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      hasTyp_vecLoadOpV op, hasTypTup_cons_iff.2 ⟨_, _, rfl,
        Round5.Pos.typedV_xidx "memidx" (by simp [Round5.Pos.idxNames]) m _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, ConfigOk.typedV_memarg a _ ⟨rfl, rfl, rfl⟩,
          hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩⟩)

set_option maxRecDepth 100000 in
/-- `VLOAD_LANE V128 sz x ao j`. -/
theorem typedV_vecLoadLane (p : PackSize) (m : MemIdx) (a : MemArg) (l : LaneIdx) :
    TypedV (simEnv B) (.varT "instr" []) (instrToVM (.vecLoadLane p m a l)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    Round5.SimdTy.typedV_vectype _ ⟨rfl, rfl, rfl⟩, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      hasTyp_szW ⟨rfl, rfl, rfl⟩ p, hasTypTup_cons_iff.2 ⟨_, _, rfl,
        Round5.Pos.typedV_xidx "memidx" (by simp [Round5.Pos.idxNames]) m _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, ConfigOk.typedV_memarg a _ ⟨rfl, rfl, rfl⟩,
          hasTypTup_cons_iff.2 ⟨_, _, rfl, Round5.SimdTy.typedV_laneidx l _ ⟨rfl, rfl, rfl⟩,
            hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩⟩⟩)

set_option maxRecDepth 100000 in
/-- `VSTORE V128 x ao`. -/
theorem typedV_vecStore (m : MemIdx) (a : MemArg) :
    TypedV (simEnv B) (.varT "instr" []) (instrToVM (.vecStore m a)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTypTup3
    (Round5.SimdTy.typedV_vectype _ ⟨rfl, rfl, rfl⟩)
    (Round5.Pos.typedV_xidx "memidx" (by simp [Round5.Pos.idxNames]) m _ ⟨rfl, rfl, rfl⟩)
    (ConfigOk.typedV_memarg a _ ⟨rfl, rfl, rfl⟩))

set_option maxRecDepth 100000 in
/-- `VSTORE_LANE V128 sz x ao j`. -/
theorem typedV_vecStoreLane (p : PackSize) (m : MemIdx) (a : MemArg) (l : LaneIdx) :
    TypedV (simEnv B) (.varT "instr" []) (instrToVM (.vecStoreLane p m a l)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    Round5.SimdTy.typedV_vectype _ ⟨rfl, rfl, rfl⟩, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      hasTyp_szW ⟨rfl, rfl, rfl⟩ p, hasTypTup_cons_iff.2 ⟨_, _, rfl,
        Round5.Pos.typedV_xidx "memidx" (by simp [Round5.Pos.idxNames]) m _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, ConfigOk.typedV_memarg a _ ⟨rfl, rfl, rfl⟩,
          hasTypTup_cons_iff.2 ⟨_, _, rfl, Round5.SimdTy.typedV_laneidx l _ ⟨rfl, rfl, rfl⟩,
            hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩⟩⟩)

/-- **Every memory SIMD instruction's new image is a typed `instr`**, in every `simEnv B`,
without validity. -/
theorem typedV_vecMemV (i : Instr) (h : memSimd i = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToVM i) := by
  cases i <;> simp [memSimd] at h
  · exact typedV_vecLoad _ _ _
  · exact typedV_vecLoadLane _ _ _ _
  · exact typedV_vecStore _ _
  · exact typedV_vecStoreLane _ _ _ _

/-- Off the four constructors the new encoding is `instrToV`. -/
theorem instrToVM_of_not {i : Instr} (h : memSimd i = false) : instrToVM i = instrToV i := by
  cases i <;> simp_all [memSimd, instrToVM, vecMemV]

/-! ## The provisional images are not typed -/

/-- **A case is not a `memarg`** (a record type), in any term-only scope. -/
theorem not_hasTyp_memarg_case {σ : VarEnv} (hσ : ValsOnly σ) (op : MixopS) (w : Value) :
    ¬ HasTyp (simEnv B) σ (.varT "memarg" []) (.case op w) := by
  intro h
  have hl : localTyp? σ "memarg" [] = none := by simp [localTyp?, VarEnv.findTyp?, hσ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [ConfigOk.findTyp_memarg] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ', -, hd⟩ | hrest
  · obtain ⟨gs, he, -⟩ := hasTypDef_structT_iff.1 hd
    cases he
  · exact absurd hrest not_hasTypInsts_nil

/-- The provisional memory argument is a case. -/
theorem schemaV_memArg (a : MemArg) : ∃ op w,
    schemaV (Silmaril.Wasm.SpecTecEnc.encodeMemArg a) = .case op w := ⟨_, _, rfl⟩

/-- The provisional image of `v128.store`. -/
theorem instrToV_vecStore (m : MemIdx) (a : MemArg) :
    instrToV (.vecStore m a) = .case "VSTORE" (.tuple
      [schemaV (Silmaril.Wasm.SpecTecEnc.encodeVecType .v128),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeUnsigned m.toNat),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeMemArg a)]) := by
  simp [instrToV, schemaInstrV, Silmaril.Wasm.SpecTecEnc.encodeInstruction,
    Silmaril.Wasm.SpecTecEnc.field]

set_option maxRecDepth 100000 in
/-- **The provisional image of `v128.store` is not a typed `instr`**, in any `simEnv B`: its
memory argument is a `$record` case, not a `memarg` record. So the round-5 positive typing
cannot be extended to memory SIMD at the current `instrToV`. -/
theorem not_typedV_instrToV_vecStore (m : MemIdx) (a : MemArg) :
    ¬ TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecStore m a)) := by
  intro h
  rw [instrToV_vecStore] at h
  have hc := Typing.hasTypCase_of_closedVariant (IntNumeric.findTyp_instr' B)
    (h _ ConfigOk.valsOnly_empty)
  have hp := IntNumeric.hasTyp_of_hasTypCase hc
    (t := .tupT [.mk "vectype" (.varT "vectype" []), .mk "memidx" (.varT "memidx" []),
      .mk "memarg" (.varT "memarg" [])]) (prems := []) rfl
  obtain ⟨op, w, hw⟩ := schemaV_memArg a
  have h3 := (ConfigOk.hasTyp_triple_inv hp).2.2
  rw [hw] at h3
  exact not_hasTyp_memarg_case ⟨rfl, rfl, rfl⟩ op w h3

end Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd
