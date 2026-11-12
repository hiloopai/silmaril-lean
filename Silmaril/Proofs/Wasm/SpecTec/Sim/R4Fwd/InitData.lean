module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.DataEval

/-!
# Track r4-fwd: `array.init_data`, forward (`Step_read` 100, 101, 102)

`array.init_data-null` and `-oob1` are family R's (`Aggregates.fwd_arrayInitDataNull`,
`fwd_arrayInitDataOob₁`). The other three read the element type through `Expand` and
`$zsize(zt)`:

* `-oob2` (100) fires at Core's out-of-bounds data range;
* `-zero` (101) and `-num` (102) are `otherwise` rules, so the earlier rules must be refuted at the
  same left-hand side. Refuting `-oob2` needs `Expand` to be functional on images: whatever `zt`
  an instance picks is the image of Core's element type. This is `ExpandInv`, proved for the
  concrete `Prims.builtins` (`Prims.expand_of_dderives`, with `Expand.iff`).
* `-num` reads the field through `$zbytes_(zt, c) = $data(z, y).BYTES[j : $zsize(zt)/8]`, with `c`
  instantiated at the literal of Core's loaded word (`readField_spec`), and writes
  `$const($cunpack(zt), $cunpacknum_(zt, c))` (`evalExp_constField`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open RefsGC

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## Arithmetic -/

/-- `(e / 8)` through the rationals, at a multiple of 8. -/
theorem evalExp_divBy8 {env : Env} {ρ : VarEnv} {e : Exp} {w : Nat} (h8 : 8 ∣ w)
    (h : EvalExp env ρ e (.num (.natN w))) :
    EvalExp env ρ (.cvtE (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (w / 8))) := by
  obtain ⟨q, rfl⟩ := h8
  have e₁ : EvalExp env ρ (.cvtE e .natT .ratT) (.num (.ratN ((8 * q : Nat) : ℚ))) :=
    evalExp_cvtE_iff.2 ⟨_, _, h, rfl, rfl⟩
  have e₂ : EvalExp env ρ (.cvtE (.numE (.natN 8)) .natT .ratT) (.num (.ratN 8)) :=
    evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_num', rfl, rfl⟩
  have hq : (((8 * q : Nat) : ℚ) / 8) = ((8 * q / 8 : Nat) : ℚ) := by
    rw [Nat.mul_div_cancel_left q (by decide), Nat.cast_mul]
    exact mul_div_cancel_left₀ _ (by decide)
  have e₃ : EvalExp env ρ (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) (.num (.ratN ((8 * q / 8 : Nat) : ℚ))) :=
    evalExp_binE_iff.2 ⟨_, e₁, .inr ⟨rfl, _, e₂, by
      simp only [binValues, Num.bin, show (8 : ℚ) ≠ 0 by decide, ↓reduceIte, hq]
      rfl⟩⟩
  have hc : Num.cvt .natT (.ratN ((8 * q / 8 : Nat) : ℚ)) = some (.natN (8 * q / 8)) := by
    simp [Num.cvt]
  exact evalExp_cvtE_iff.2 ⟨_, _, e₃, hc, rfl⟩

theorem dvd_storageSize : ∀ zt : CStorageType, 0 < storageSize zt → 8 ∣ storageSize zt
  | .val (.num (.int .i32)), _ | .val (.num (.int .i64)), _ | .val (.num (.float .f32)), _
  | .val (.num (.float .f64)), _ | .val (.vec .v128), _ | .pack .i8, _ | .pack .i16, _ => by decide
  | .val (.refv _), h | .val .botv, h => by simp [storageSize] at h

/-! ## The left-hand side -/

/-- The bindings an `array.init_data` left-hand side forces. -/
theorem binds_arrayInitData {env : Env} {ρ : VarEnv} {a : Nat} {i j n : BitVec 32} {x : TypeIdx}
    {y : DataIdx}
    (hl : EvalExp env ρ (.listE [.caseE "REF.ARRAY_ADDR" (.varE "a"),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
      .caseE "ARRAY.INIT_DATA" (.tupE [.varE "x", .varE "y"])])
      (.list (adminsToV [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]))) :
    EvalExp env ρ (.varE "a") (.num (.natN a)) ∧ EvalExp env ρ (.varE "i") (pctV i.toNat) ∧
      EvalExp env ρ (.varE "j") (pctV j.toNat) ∧ EvalExp env ρ (.varE "n") (.num (.natN n.toNat)) ∧
      EvalExp env ρ (.varE "x") (Encode.toValue x) ∧ EvalExp env ρ (.varE "y") (Encode.toValue y) := by
  have hs := elems_of_list hl
  have h₄ := elems_of_tup (case_inv (evalExps_get hs 4 rfl rfl))
  exact ⟨case_inv (evalExps_get hs 0 rfl rfl), const_var (evalExps_get hs 1 rfl rfl),
    const_var (evalExps_get hs 2 rfl rfl), const_pct_var (evalExps_get hs 3 rfl rfl),
    (evalExps_cons_inv h₄).1, (evalExps_cons_inv (evalExps_cons_inv h₄).2).1⟩

/-- `array.init_data-oob1` does not fire when the array range is in bounds. -/
theorem not_arrayInitDataOob₁ {env : Env} (G : RStoreFuns env) {D : Interp} {els : Prop}
    {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a : Nat}
    {ai : ArrayInst} (ha : s.arrays[a]? = some ai) (h : i.toNat + n.toNat ≤ ai.fields.length)
    {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayInitDataOob1Rule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hz, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨ha', hi, -, hn', -⟩ := binds_arrayInitData hl
  have hif := premW_if (hp _ (List.mem_singleton_self _))
  have hb := EvalExp.unique hif (evalExp_cmpNat (op := .gtOp) (evalExp_addNat (evalExp_unpct hi) hn')
    (evalExp_len (evalExp_arrayFields G (valsOnly_scope hb) hz ha' ha)) rfl)
  simp only [List.length_map, Value.bool.injEq] at hb
  have hgt : ai.fields.length < i.toNat + n.toNat := of_decide_eq_true hb.symm
  omega

/-- `array.init_data-zero` does not fire for `n ≠ 0`. -/
theorem not_arrayInitDataZero {env : Env} {D : Interp} {els : Prop} {s : Store H} {f : Frame}
    {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a : Nat} (hn0 : n ≠ 0) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayInitDataZeroRule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  obtain ⟨-, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨-, -, -, hn', -⟩ := binds_arrayInitData hl
  have hif := premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) := eq_of_evalExp_eq hif hn' evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hn0 (BitVec.eq_of_toNat_eq (by simpa using h0))

/-! ## The element type, read off `Expand` -/

/-- The array `Expand` premise of the data rules, evaluated forward. -/
theorem evalExp_expandArray {σ : List (IL.Id × Value)}
    (hρ : ValsOnly (VarEnv.empty.bindVals σ)) {s : Store H} {f : Frame} {x : TypeIdx}
    {d : DefType} {m : Mutability} {zt : CStorageType} (hd : f.type? x = some d)
    (hz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (hx : (VarEnv.empty.bindVals σ).findVal? "x" = some (Encode.toValue x))
    (hm : (VarEnv.empty.bindVals σ).findVal? "mut?" = some (mutV m))
    (hzt : (VarEnv.empty.bindVals σ).findVal? "zt" = some (tyV zt)) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m zt).array : CCompType)]) := by
  have hty := Aggregates.evalExp_type (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (Aggregates.findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x") (evalExp_var hz)
    (evalExp_var hx)
  cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (evalExps_cons' (evalExp_case
    (evalExp_case (evalExp_tupE_of (evalExps_cons' (evalExp_optPat (x := "mut") (by decide) hm)
      (evalExps_cons' (evalExp_var hzt) evalExps_nil'))))) evalExps_nil'))

/-- **The element type an `Expand` instance picks is Core's**, given `ExpandInv`. -/
theorem zt_of_expand (XI : ExpandInv (simEnv B)) {O : ElseI} {ρ : VarEnv} (hρ : ValsOnly ρ)
    {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType} {m : Mutability} {zt : CStorageType}
    (hd : f.type? x = some d) (he : Expand d (.array (.field m zt)))
    (hz : EvalExp (simEnv B) ρ (.varE "z") (stateV hn s f))
    (hx : EvalExp (simEnv B) ρ (.varE "x") (Encode.toValue x)) {w : Value}
    (hw : EvalExp (simEnv B) ρ
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))]) w)
    (hD : DDerives (simEnv B) O "Expand" "%~~%" [] w) :
    EvalExp (simEnv B) ρ (.varE "zt") (tyV zt) := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨v₁, vs', h₁, hvs', rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨v₂, vs'', h₂, hvs'', rfl⟩ := evalExps_cons_iff.1 hvs'
  obtain rfl := evalExps_nil_iff.1 hvs''
  have hty := Aggregates.evalExp_type (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (Aggregates.findDef_none hρ _) hd hz hx
  obtain rfl := EvalExp.unique h₁ hty
  obtain ⟨ct, hct, rfl⟩ := XI O d v₂ hD
  have e₁ := (Expand.iff.1 hct).symm.trans (Expand.iff.1 he)
  obtain rfl : ct = .array (.field m zt) := Option.some.inj e₁
  have h₃ := case_inv (case_inv h₂)
  exact (evalExps_cons_inv (evalExps_cons_inv (elems_of_tup h₃)).2).1

/-! ## `array.init_data-oob2` -/

/-- The bound of `array.init_data-oob2`, `j + n * $zsize(zt)/8 > |$data(z, y).BYTES|`, evaluated. -/
theorem evalExp_initDataBound {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame}
    {y : DataIdx} {j n : BitVec 32} {zt : CStorageType} {da : Nat} {di : DataInst}
    (h0 : 0 < storageSize zt) (hdat : s.data? f y = some (da, di))
    (hz : EvalExp (simEnv B) ρ (.varE "z") (stateV hn s f))
    (hy : EvalExp (simEnv B) ρ (.varE "y") (Encode.toValue y))
    (hj : EvalExp (simEnv B) ρ (.varE "j") (pctV j.toNat))
    (hn' : EvalExp (simEnv B) ρ (.varE "n") (.num (.natN n.toNat)))
    (hzt : EvalExp (simEnv B) ρ (.varE "zt") (tyV zt)) :
    EvalExp (simEnv B) ρ (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT)
      (.projE (.uncaseE (.varE "j") "%") 0) (.cvtE (.binE .divOp (.numT .ratT)
        (.cvtE (.binE .mulOp (.numT .natT) (.varE "n") (.callE "zsize" [.expA (.varE "zt")]))
          .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.lenE (.dotE (.callE "data" [.expA (.varE "z"), .expA (.varE "y")]) "BYTES")))
      (.bool (decide (di.bytes.size < j.toNat + n.toNat * storageSize zt / 8))) := by
  have hsz := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "zsize")
    (evalArgs_cons hzt evalArgs_nil) (applies_zsize zt h0)
  have hmul := evalExp_mulNat (t := .numT .natT) hn' hsz
  have hdiv := evalExp_divBy8 (Dvd.dvd.mul_left (dvd_storageSize zt h0) _) hmul
  have hdata : EvalExp (simEnv B) ρ (.callE "data" [.expA (.varE "z"), .expA (.varE "y")])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.dataInstToValue di) := by
    obtain ⟨M, Ls, As, a, hS, hM, hA, ha, hr⟩ := Memory.dataAt_of_data? hn hdat
    exact State.evalExp_data (State.stateDefs_simEnv B) (Aggregates.findDef_none hρ _) hz hy hS hM
      hA ha hr
  have hlen := evalExp_len (evalExp_dot hdata (Memory.dataInstV_BYTES di))
  rw [Memory.bytesL_length] at hlen
  exact evalExp_cmpNat (evalExp_addNat (evalExp_unpct hj) hdiv) hlen
    (by simp [Num.cmp])

/-- `array.init_data-oob2` does not fire when the data range is in bounds, given `ExpandInv`. -/
theorem not_arrayInitDataOob₂ (XI : ExpandInv (simEnv B)) {els : Prop} {s : Store H} {f : Frame}
    {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a da : Nat} {d : DefType} {m : Mutability}
    {zt : CStorageType} {di : DataInst} (hd : f.type? x = some d)
    (he : Expand d (.array (.field m zt))) (hdat : s.data? f y = some (da, di))
    (h0 : 0 < storageSize zt) (h : j.toNat + n.toNat * storageSize zt / 8 ≤ di.bytes.size)
    {c : Value} :
    ¬ RuleBody (simEnv B) (DDerives (simEnv B) noElse) els [] [] "%~>%" arrayInitDataOob2Rule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, hev, hp⟩
  have hρ := valsOnly_scope (σ := σ) hb
  obtain ⟨hz, hl⟩ := cfgz_inv (lhs_of_concl hev)
  obtain ⟨-, -, hj, hn', hx, hy⟩ := binds_arrayInitData hl
  obtain ⟨w, hw, hD⟩ := premW_rule (hp _ (List.mem_cons_self ..))
  have hzt := zt_of_expand XI hρ hd he hz hx hw hD
  have hif := premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hb' := EvalExp.unique hif (evalExp_initDataBound hρ h0 hdat hz hy hj hn' hzt)
  simp only [Value.bool.injEq] at hb'
  have : di.bytes.size < j.toNat + n.toNat * storageSize zt / 8 := of_decide_eq_true hb'.symm
  omega

/-- **`array.init_data-oob2` (`Step_read` rule 100), forward.** -/
theorem sread_arrayInitDataOob₂ (R : RTyping (simEnv B)) (A : Aggregates.AggTypes (simEnv B))
    {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a da : Nat}
    {d : DefType} {m : Mutability} {zt : CStorageType} {di : DataInst}
    (hd : f.type? x = some d) (he : Expand d (.array (.field m zt)))
    (hdat : s.data? f y = some (da, di)) (h0 : 0 < storageSize zt)
    (h : di.bytes.size < j.toNat + n.toNat * storageSize zt / 8)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitData x y)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("y", Encode.toValue y), ("mut?", mutV m), ("zt", tyV zt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hb := evalExp_initDataBound (B := B) hρ h0 hdat (by eval_tac) (by eval_tac) (by eval_tac)
    (by eval_tac) (by eval_tac)
  rw [decide_eq_true h] at hb
  exact dderives_of_ruleAt (Aggregates.rd B).arrayInitDataOob2 σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) (QuantsOk.cons rfl (A.mut_ m _ hρ)
      (QuantsOk.cons rfl (A.storagetype _ _ hρ) QuantsOk.nil)))))))))
    (by eval_tac)
    (prems_two (.rulePr evalArgs_nil (evalExp_expandArray hρ hd rfl rfl rfl rfl)
      (A.expand _ _ he)) (.ifPr hb))

/-! ## `array.init_data-num` -/

/-- **The literal quantifier of the data rules is typed**: `c : lit_(zt)` at the literal of every
word that fits the storage type. -/
def LitTyping (env : Env) : Prop :=
  ∀ (zt : CStorageType) (k : Nat) (ρ : VarEnv), ValsOnly ρ → ρ.findVal? "zt" = some (tyV zt) →
    0 < storageSize zt → k < 2 ^ storageSize zt →
    HasTyp env ρ (.varT "lit_" [.expA (.varE "zt")]) (litV zt k)

set_option maxRecDepth 100000 in
theorem findDef_zbytes (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "zbytes_" = some (ps, t, []) := ⟨_, _, rfl⟩

/-- `$zbytes_(zt, c)` at the literal of `k`, given `ZB B`. -/
theorem applies_zbytes (Z : ZBytes.ZB B) {zt : CStorageType} (h0 : 0 < storageSize zt) {k : Nat}
    (hk : k < 2 ^ storageSize zt) :
    Applies (simEnv B) "zbytes_" [.val (tyV zt), .val (litV zt k)]
      (.list (FwdMem.leBytesV (storageSize zt / 8) k)) :=
  Prims.applies_of_noClause (findDef_zbytes B) (Z _ _ _ (zbytesCall_litV zt h0 k hk))

/-- `j + k` without wrap. -/
theorem toNat_add_ofNat {j : BitVec 32} {k : Nat} (h : j.toNat + k < 2 ^ 32) :
    (j + BitVec.ofNat 32 k).toNat = j.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32),
    Nat.mod_eq_of_lt h]

set_option maxHeartbeats 400000 in
/-- **`array.init_data-num` (`Step_read` rule 102), forward.** -/
theorem sread_arrayInitDataNum {P : Numerics.Profile} (hF : Floats.FloatB P B)
    (Z : ZBytes.ZB B) (XI : ExpandInv (simEnv B)) (LT : LitTyping (simEnv B))
    (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B)) (A : Aggregates.AggTypes (simEnv B))
    {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a da : Nat}
    {ai : ArrayInst} {d : DefType} {m : Mutability} {zt : CStorageType} {di : DataInst} {v : Val}
    (ha : s.arrays[a]? = some ai) (hd : f.type? x = some d)
    (he : Expand d (.array (.field m zt))) (hdat : s.data? f y = some (da, di))
    (h : i.toNat + n.toNat ≤ ai.fields.length ∧
      j.toNat + n.toNat * storageSize zt / 8 ≤ di.bytes.size)
    (hn0 : n ≠ 0) (hv : readField? zt di.bytes j.toNat = some v)
    (hb₁ : ai.fields.length < 2 ^ 32) (hb₂ : di.bytes.size < 2 ^ 32)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitData x y)]⟩)
      (adminsToV [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), constI32 (j + BitVec.ofNat 32 (storageSize zt / 8)),
        constI32 (n - 1), .plain (.arrayInitData x y)]) := by
  have h0 := storageSize_pos_of_readField hv
  obtain ⟨k, hk, hjb, hsl, rfl⟩ := readField_spec hv
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("y", Encode.toValue y), ("zt", tyV zt), ("c", litV zt k),
    ("mut?", mutV m)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hl : LhsIn ["ARRAY.INIT_DATA", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil))))⟩
  have hel := otherwise_of_ruleAt (Aggregates.rd B).arrayInitDataNum (readTable_simEnv B)
    (i := 102) (b := .list (adminsToV [arrRef a, constI32 i, (fieldOfLit zt k).toAdmin,
        .plain (.arraySet x), arrRef a, constI32 (i + 1),
        constI32 (j + BitVec.ofNat 32 (storageSize zt / 8)), constI32 (n - 1),
        .plain (.arrayInitData x y)])) (by decide) (exc := [99, 100, 101]) hl (by decide) (by
      intro k' hk' _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hk' : k' = 99 ∨ k' = 100 ∨ k' = 101) with rfl | rfl | rfl
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitDataOob1 hr']
        exact not_arrayInitDataOob₁ G ha h.1
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitDataOob2 hr']
        exact not_arrayInitDataOob₂ XI hd he hdat h0 h.2
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitDataZero hr']
        exact not_arrayInitDataZero hn0)
  have hsz : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (storageSize zt / 8))) :=
    evalExp_divBy8 (dvd_storageSize zt h0) (Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (evalArgs_cons (by eval_tac) evalArgs_nil) (applies_zsize zt h0))
  have hdata : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "data" [.expA (.varE "z"), .expA (.varE "y")])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.dataInstToValue di) := by
    obtain ⟨M, Ls, As, a', hS, hM, hA, ha', hr⟩ := Memory.dataAt_of_data? hn hdat
    exact State.evalExp_data (State.stateDefs_simEnv B) (Aggregates.findDef_none hρ _)
      (by eval_tac) (by eval_tac) hS hM hA ha' hr
  have hif : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "zbytes_" [.expA (.varE "zt"), .expA (.varE "c")])
        (.sliceE (.dotE (.callE "data" [.expA (.varE "z"), .expA (.varE "y")]) "BYTES")
          (.projE (.uncaseE (.varE "j") "%") 0)
          (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")]) .natT .ratT)
            (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))) (.bool true) :=
    evalExp_eq_true (Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (evalArgs_cons (by eval_tac) (evalArgs_cons (by eval_tac) evalArgs_nil))
      (applies_zbytes Z h0 hk))
      (evalExp_sliceE_iff.2 ⟨_, _, _, evalExp_dot hdata (Memory.dataInstV_BYTES di),
        evalExp_unpct (by eval_tac), hsz, by
          rw [Equiv.ExecReadAggregate.slice?_list (by simpa using hjb), hsl]; rfl⟩)
  have hb₂' : j.toNat + storageSize zt / 8 < 2 ^ 32 := by
    have : storageSize zt / 8 ≤ n.toNat * storageSize zt / 8 := by
      have : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
      exact Nat.div_le_div_right (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hi : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0) (.numE (.natN 1)))
      (.num (.natN (i + 1).toNat)) := by
    rw [FwdSimdAgg.toNat_succ h.1 hb₁ hn0]
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) evalExp_num'
  have hj : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "j") "%") 0)
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")]) .natT .ratT)
          (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.num (.natN (j + BitVec.ofNat 32 (storageSize zt / 8)).toNat)) := by
    rw [toNat_add_ofNat hb₂']
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) hsz
  have hn' : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (n - 1).toNat)) := by
    rw [toNat_sub_one hn0]
    exact evalExp_predNat (by eval_tac) (by
      have : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
      omega)
  have hcst := evalExp_constField hF hρ h0 hk (by rfl) (by rfl)
  refine dderives_of_ruleAt (Aggregates.rd B).arrayInitDataNum σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
      (QuantsOk.cons rfl (LT zt k _ hρ rfl h0 hk) (QuantsOk.cons rfl (A.mut_ m _ hρ)
        QuantsOk.nil))))))))))
    (evalExp_tup2 (by eval_tac) ?_)
    (Aggregates.prems_three (.elsePr hel) (.rulePr evalArgs_nil
      (evalExp_expandArray hρ hd rfl rfl rfl rfl) (A.expand _ _ he)) (.ifPr hif))
  have e₆ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hi evalExps_nil'))) evalExps_nil')))
  have e₇ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hj evalExps_nil'))) evalExps_nil')))
  have e₈ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hn' evalExps_nil'))) evalExps_nil')))
  have e₃ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "const" [.expA (.callE "cunpack" [.expA (.varE "zt")]),
        .expA (.callE "cunpacknum_" [.expA (.varE "zt"), .expA (.varE "c")])])
      (adminToV (fieldOfLit zt k).toAdmin) := by
    rw [adminToV_toAdmin]; exact hcst
  exact evalExp_listE_of (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' e₃ (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' e₆ (evalExps_cons' e₇ (evalExps_cons' e₈
    (evalExps_cons' (by eval_tac) evalExps_nil')))))))))

/-- **`array.init_data-num`, as a forward obligation** (bounded store). -/
theorem fwd_arrayInitDataNum {P : Numerics.Profile} (hF : Floats.FloatB P B)
    (Z : ZBytes.ZB B) (XI : ExpandInv (simEnv B)) (LT : LitTyping (simEnv B))
    (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B))
    (A : Aggregates.AggTypes (simEnv B))
    {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a da : Nat}
    {ai : ArrayInst} {d : DefType} {ft : CFieldType} {di : DataInst} {v : Val}
    (hbd : Aggregates.Bounded s) (ha : s.arrays[a]? = some ai) (hd : f.type? x = some d)
    (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (h : i.toNat + n.toNat ≤ ai.fields.length ∧
      j.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size)
    (hn0 : n ≠ 0) (hv : readField? (fieldStorage ft) di.bytes j.toNat = some v) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩
      ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
        arrRef a, constI32 (i + 1),
        constI32 (j + BitVec.ofNat 32 (storageSize (fieldStorage ft) / 8)),
        constI32 (n - 1), .plain (.arrayInitData x y)]⟩ := by
  obtain ⟨m, zt⟩ := ft
  refine RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_arrayInitDataNum hF Z XI LT R G A ha hd he hdat h hn0 hv (hbd.array ha)
    (hbd.datas di (List.mem_of_getElem? (State.Store.data?_eq_some hdat).2)) hz

/-- **`array.init_data-oob2`, as a forward obligation.** -/
theorem fwd_arrayInitDataOob₂ (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (A : Aggregates.AggTypes (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx}
    {i j n : BitVec 32} {a da : Nat} {d : DefType} {ft : CFieldType} {di : DataInst}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (h0 : 0 < storageSize (fieldStorage ft))
    (h : di.bytes.size < j.toNat + n.toNat * storageSize (fieldStorage ft) / 8) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩ ⟨s, f, [.trap]⟩ := by
  obtain ⟨m, zt⟩ := ft
  exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
    sread_arrayInitDataOob₂ R A hd he hdat h0 h hz

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
