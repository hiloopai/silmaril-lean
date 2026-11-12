module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.InitData

/-!
# Round 5, pass 3, track read: `array.new_data-num` (76), backward, under `ReadValidS`

`z; (CONST I32 i) (CONST I32 n) (ARRAY.NEW_DATA x y) ~> ($const($cunpack(zt), $cunpacknum_(zt, c)))^n
(ARRAY.NEW_FIXED x n)` with `Expand($type(z, x), ARRAY (mut? zt))` and
`$concatn_(byte, $zbytes_(zt, c)^n, $zsize(zt)/8) = $data(z, y).BYTES[i : n * $zsize(zt)/8]`.
Read back:

* `ReadValidS.seg` resolves the data segment and gives the array type with `0 < |zt|`;
  the `Expand` premise fixes `zt`;
* each `c` is the literal of a word `k < 2 ^ |zt|` whose encoding is its `$zbytes_` chunk
  (`zbytes_lit_inv`, with the typed quantifier `c* : lit_(zt)*`);
* `$concatn_` concatenates those chunks (`FwdRef.tryClauses_concatn`, by
  uniqueness), and the slice evaluates only in bounds;
* the `n` chunks of the slice are what Core's `readField?` reads (`reads_of_chunks`, the
  converse of `FwdRef.reads_spec`), so Core's `mapM` succeeds.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)
open Round4Read (decode_aconst_at)
open R4Fwd (litV fieldOfLit)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **Adjacent chunks of a byte string are what `readField?` reads**: the converse of track
fwdref's `FwdRef.reads_spec`. -/
theorem reads_of_chunks {zt : CStorageType} {bytes : ByteArray} {i w : Nat} (h0 : 0 < storageSize zt)
    (hw : w = storageSize zt / 8) :
    ∀ (ks : List Nat) (j : Nat), (∀ a ∈ ks, a < 2 ^ storageSize zt) →
      i + (j + ks.length) * w ≤ bytes.size →
      (ks.map (FwdMem.leBytesV w)).flatten =
        ((FwdMem.bytesV bytes).drop (i + j * w)).take (ks.length * w) →
      (List.range' j ks.length).mapM (fun k => readField? zt bytes (i + k * w)) =
        some (ks.map (fieldOfLit zt))
  | [], _, _, _, _ => rfl
  | a :: ks, j, hks, hb, h => by
    subst hw
    have hlen := FwdMem.leBytesV_length (storageSize zt / 8) a
    simp only [List.map_cons, List.flatten_cons, List.length_cons] at h hb
    have h₁ : FwdMem.leBytesV (storageSize zt / 8) a =
        ((FwdMem.bytesV bytes).drop (i + j * (storageSize zt / 8))).take (storageSize zt / 8) := by
      have := congrArg (List.take (storageSize zt / 8)) h
      rw [List.take_left' hlen, List.take_take, Nat.min_eq_left (by nlinarith)] at this
      exact this
    have h₂ : (ks.map (FwdMem.leBytesV (storageSize zt / 8))).flatten =
        ((FwdMem.bytesV bytes).drop (i + (j + 1) * (storageSize zt / 8))).take
          (ks.length * (storageSize zt / 8)) := by
      have := congrArg (List.drop (storageSize zt / 8)) h
      rw [List.drop_left' hlen, List.drop_take, List.drop_drop] at this
      rw [this]
      congr 2
      · rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
      · ring
    have hread : readField? zt bytes (i + j * (storageSize zt / 8)) = some (fieldOfLit zt a) := by
      refine readField_of_slice h0 (hks a List.mem_cons_self) ?_ (congrArg Value.list h₁).symm
      exact Equiv.ExecReadAggregate.slice?_list (by rw [FwdMem.bytesV_length]; nlinarith)
    have ih := reads_of_chunks h0 rfl ks (j + 1) (fun b hb' => hks b (List.mem_cons_of_mem _ hb'))
      (by nlinarith) h₂
    show (List.range' j (ks.length + 1)).mapM _ = _
    rw [List.range'_succ, List.mapM_cons, hread, ih]
    rfl

/-- A list chosen pointwise. -/
theorem exists_list_of_forall {α β : Type} {l : List α} {Q : Nat → β → Prop}
    (h : ∀ k, k < l.length → ∃ b, Q k b) :
    ∃ bs : List β, bs.length = l.length ∧ ∀ k (hk : k < bs.length), Q k bs[k] := by
  classical
  refine ⟨List.ofFn fun k : Fin l.length => (h k k.2).choose, by simp, fun k hk => ?_⟩
  simp only [List.getElem_ofFn]
  exact (h k (by simpa using hk)).choose_spec

theorem findVal_c_zt {ρ : VarEnv} {v : Value} :
    (ρ.bindVals [("c", v)]).findVal? "zt" = ρ.findVal? "zt" := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]

theorem findVal_c {ρ : VarEnv} {v : Value} : (ρ.bindVals [("c", v)]).findVal? "c" = some v := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]

/-- An argument list with a type head, inverted. -/
theorem evalArgs_typA_cons_inv {env : Env} {ρ : VarEnv} {t : Typ} {rest : List Arg}
    {ws : List ArgV} (h : EvalArgs env ρ (.typA t :: rest) ws) :
    ∃ ws', EvalArgs env ρ rest ws' ∧ ws = .typ (resolveTyp ρ t) :: ws' := by
  obtain ⟨n, h⟩ := h
  match n, h with
  | 0, h => simp [evalArgs] at h
  | 1, h => simp [evalArgs, List.mapM_cons, evalArg] at h
  | n + 2, h =>
      simp only [evalArgs, List.mapM_cons, evalArg] at h
      cases hws : List.mapM (evalArg (n + 1) env ρ) rest with
      | error err => simp [hws, bind, Except.bind] at h
      | ok ws' =>
          simp [hws, bind, Except.bind, pure, Except.pure] at h
          exact ⟨ws', ⟨n + 2, by simpa [evalArgs] using hws⟩, h.symm⟩

/-- **`Step_read` 76 (`array.new_data-num`), backward, under `ReadValidS`.** -/
theorem bwd_arrayNewDataNum : ∀ (c : Config H) (w : Value), Round5.Read.ReadValidS c →
    Fires (simEnv (BI P hn host)) "Step_read" 76 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have XI := R4Fwd.expandInv_builtins (prof := P) hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayNewDataNum hf)
  have hρ := valsOnly_bindVals σ
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  obtain ⟨CS, fcs, hCS⟩ := hq "c*" (.iterT (.varT "lit_" [.expA (.varE "zt")]) .list) (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.NEW_DATA" (.tuple [X, Y])]]) := by
    concl_inv hl
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Aggregates.adminsToV_eq_triple hcode
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₁
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₂
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := Round5.Read.head_arrayNewData (Typing.adminToV_case h₃).symm
  have eXY : X = Encode.toValue x ∧ Y = Encode.toValue y := by
    have h₃' : Value.case "ARRAY.NEW_DATA" (.tuple [Encode.toValue x, Encode.toValue y]) = _ := h₃
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₃'
    exact ⟨h₃'.1.symm, h₃'.2.symm⟩
  obtain ⟨rfl, rfl⟩ := eXY
  subst hZ
  obtain ⟨hdat', d, m, zt, hd, hexp, h0⟩ := hv.seg.2.2.1
  obtain ⟨⟨da, di⟩, hdat⟩ := Option.isSome_iff_exists.1 hdat'
  -- `zt`, from the `Expand` premise
  obtain ⟨w', hw', hD⟩ := RefsGC.premW_rule (hp _ List.mem_cons_self)
  have fzt := evalExp_varE_iff.1
    (R4Fwd.zt_of_expand XI hρ hd hexp (evalExp_var fz) (evalExp_var fx) hw' hD)
  -- the literals `c*` are typed
  obtain ⟨l, rfl, hlt⟩ := hasTyp_iterT_list_iff.1 hCS
  have hlt' := hasTypList_iff.1 hlt
  -- the element size and the slice length
  have hw8 : n.toNat * storageSize zt / 8 = n.toNat * (storageSize zt / 8) :=
    Nat.mul_div_assoc _ (R4Fwd.dvd_storageSize zt h0)
  have hzs : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "zsize" [.expA (.varE "zt")]) (.num (.natN (storageSize zt))) :=
    Vec.evalExp_call (Aggregates.findDef_none hρ _) (Equiv.evalArgs_cons (evalExp_var fzt)
      Equiv.evalArgs_nil) (R4Fwd.applies_zsize zt h0)
  have hsz := R4Fwd.evalExp_divBy8 (R4Fwd.dvd_storageSize zt h0) hzs
  have hlenE : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.binE .mulOp (.numT .natT) (.varE "n")
        (.callE "zsize" [.expA (.varE "zt")])) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT))
        .ratT .natT) (.num (.natN (n.toNat * (storageSize zt / 8)))) := by
    rw [← hw8]
    exact R4Fwd.evalExp_divBy8 (Dvd.dvd.mul_left (R4Fwd.dvd_storageSize zt h0) _)
      (RefsGC.evalExp_mulNat (t := .numT .natT) (evalExp_var fn) hzs)
  -- the premise: the chunks and their concatenation
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ (List.mem_cons_of_mem _
    List.mem_cons_self)))
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  obtain ⟨ws, hws⟩ := BwdStep.args_of_call e₁
  obtain ⟨ws₁, hws₁, rfl⟩ := evalArgs_typA_cons_inv hws
  obtain ⟨ZB, ws₂, hZB, hws₂, rfl⟩ := BwdStep.evalArgs_cons_inv hws₁
  obtain ⟨SZ, ws₃, hSZ, hws₃, rfl⟩ := BwdStep.evalArgs_cons_inv hws₂
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hws₃
  obtain rfl := EvalExp.unique hSZ hsz
  obtain ⟨l', out, rfl, fcs', fn', hlo, hbody⟩ := BwdStep.iterListN1_inv hZB
  rw [fcs, Option.some.injEq, Value.list.injEq] at fcs'
  subst fcs'
  have hln : l.length = n.toNat := by
    have := fn'.symm.trans fn
    simpa using this
  have hel : ∀ k, k < l.length → ∃ K, ∃ (hk : k < l.length) (ho : k < out.length),
      K < 2 ^ storageSize zt ∧ l[k] = litV zt K ∧
        out[k] = .list (FwdMem.leBytesV (storageSize zt / 8) K) := by
    intro k hk
    have ho : k < out.length := by omega
    have hρ' : ValsOnly ((VarEnv.empty.bindVals σ).bindVals [("c", l[k])]) :=
      ⟨hρ.1, hρ.2.1, hρ.2.2⟩
    have hA : Applies (simEnv (BI P hn host)) "zbytes_" [.val (tyV zt), .val l[k]] out[k] :=
      (applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ' _) (Equiv.evalArgs_cons
        (evalExp_var (findVal_c_zt.trans fzt)) (Equiv.evalArgs_cons (evalExp_var findVal_c)
          Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 (hbody k hk ho))
    obtain ⟨K, hK, e₁', e₂'⟩ := zbytes_lit_inv h0 fzt (hlt' _ (List.getElem_mem hk)) hA
    exact ⟨K, hk, ho, hK, e₁', e₂'⟩
  obtain ⟨ks, hksl, hks⟩ := exists_list_of_forall hel
  have hks_lt : ∀ a ∈ ks, a < 2 ^ storageSize zt := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨-, -, h, -⟩ := hks k hk
    exact h
  have el : l = ks.map (litV zt) := by
    refine List.ext_getElem (by simp [hksl]) fun k h₁ h₂ => ?_
    obtain ⟨hk', ho', hK', e, e'⟩ := hks k (by simpa using h₂)
    simpa using e
  have eout : out = (ks.map (FwdMem.leBytesV (storageSize zt / 8))).map Value.list := by
    refine List.ext_getElem (by simp [hksl]; omega) fun k h₁ h₂ => ?_
    obtain ⟨hk', ho', hK', e', e⟩ := hks k (by simpa using h₂)
    simpa using e
  subst el eout
  have hklen : ks.length = n.toNat := by simpa using hln
  obtain ⟨cs, ⟨ps, t, hdf⟩, hT⟩ := FwdRef.tryClauses_concatn (FwdRef.concatnDefs_simEnv _)
    (resolveTyp (VarEnv.empty.bindVals σ) (.varT "byte" [])) (storageSize zt / 8)
    (ks.map (FwdMem.leBytesV (storageSize zt / 8))) (by
      intro c hc
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hc
      exact FwdMem.leBytesV_length _ _)
  have hcat := Applies.unique ((applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _) hws).2
    (evalExp_callE_iff.1 e₁)) ⟨ps, t, cs, hdf, Or.inl hT⟩
  subst hcat
  -- the slice
  have hdata : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "data" [.expA (.varE "z"), .expA (.varE "y")]) (dataInstToValue di) := by
    obtain ⟨M, Ls, As, a', hS, hM, hA', ha', hr⟩ := Memory.dataAt_of_data? hn hdat
    exact State.evalExp_data (State.stateDefs_simEnv _) (Aggregates.findDef_none hρ _)
      (evalExp_var fz) (evalExp_var fy) hS hM hA' ha' hr
  obtain ⟨W, i', k', hW, hi', hk', hsl⟩ := evalExp_sliceE_iff.1 e₂
  obtain rfl := EvalExp.unique hW (RefsGC.evalExp_dot hdata (Memory.dataInstV_BYTES di))
  have ei : i' = i.toNat := by
    simpa using EvalExp.unique hi' (RefsGC.evalExp_unpct (evalExp_var fi))
  have ek : k' = n.toNat * (storageSize zt / 8) := by simpa using EvalExp.unique hk' hlenE
  subst ei ek
  have hsl' : Value.slice? (.list (FwdMem.bytesV di.bytes)) i.toNat
      (n.toNat * (storageSize zt / 8)) = some (.list (ks.map
        (FwdMem.leBytesV (storageSize zt / 8))).flatten) := hsl
  simp only [Value.slice?, FwdMem.bytesV_length] at hsl'
  split at hsl'
  · rename_i hb
    have hflat := (Value.list.inj (Option.some.inj hsl')).symm
    have hvs := reads_of_chunks (bytes := di.bytes) (i := i.toNat) h0 rfl ks 0 hks_lt
      (by rw [hklen]; simpa using hb) (by rw [hklen]; simpa using hflat)
    rw [← List.range_eq_range', hklen] at hvs
    -- the right-hand side
    have hres := FwdRef.evalExp_iterNMap_of (env := simEnv (BI P hn host))
      (b := .callE "const" [.expA (.callE "cunpack" [.expA (.varE "zt")]),
        .expA (.callE "cunpacknum_" [.expA (.varE "zt"), .expA (.varE "c")])])
      (x := "c") (F := litV zt) (G := fun a => valV (fieldOfLit zt a))
      (by rw [hklen]; exact fn) fcs fun a ha => by
        have hρ' : ValsOnly ((VarEnv.empty.bindVals σ).bindVals [("c", litV zt a)]) :=
          ⟨hρ.1, hρ.2.1, hρ.2.2⟩
        exact R4Fwd.evalExp_constField (B := BI P hn host) (Prims.floatB_builtins (prof := P) hn host)
          hρ' h0 (hks_lt a ha) (findVal_c_zt.trans fzt) findVal_c
    have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (evalExp_cat hres
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_case
        (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var fn) evalExps_nil, rfl⟩))))))
    have hb' : i.toNat + n.toNat * storageSize zt / 8 ≤ di.bytes.size := by
      rw [hw8]
      simpa [hklen] using hb
    refine ⟨_, ?_, .aggregate (.arrayNewDataNum (ft := .field m zt) hd hexp hdat h0 hb' hvs)⟩
    rw [hw, adminsToV_append, adminsToV_vals, List.map_map]
    rfl
  · cases hsl'

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
