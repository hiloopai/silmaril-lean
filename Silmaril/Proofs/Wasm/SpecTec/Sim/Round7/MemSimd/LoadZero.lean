module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadValBwd

/-!
# Round 7, memory SIMD: `v128.loadN_zero`, in bounds (`Step_read` 49), both directions

`Step_read/vload-zero-val`: `z; (CONST at i) (VLOAD V128 (ZERO N) x ao) ~> (VCONST V128 c)` when
`$ibytes_(N, j) = $mem(z, x).BYTES[i + ao.OFFSET : N/8]` and `c = $extend__(N, 128, U, j)`, with
`j : iN(N)` and `c : vec_(V128)` quantified. Core's `vecLoadVal` at `.zero32`/`.zero64` loads
`N/8` bytes and zero-extends them to 128 bits (`vecLoadResult`).

* `fires_vloadZeroVal`: the rule fires, for arbitrary typed state values, given `BytesFuns` and a
  `B` that answers the float and conversion primitives (`Floats.FloatB`).
* `fwd_vecLoadZero`: **Core's `vecLoadVal` at `.zero32`/`.zero64`, forward**, as a `Step_read`
  step in both readings.
* `bwd_vloadZeroVal`, `bwdB_vecLoadZero`: **backward**: the rule fires only in bounds, at the
  loaded word, and Core's `vecLoadVal` steps to the same vector.
* `bytesFuns_vb`, `floatB_vb`: both hypotheses hold at `withVBytes (Prims.builtins …)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateTyping)
open Memory (MemAt MemTyping memAt_of_mem?)
open FwdMem (leBytesV bytesV SliceAt BytesFuns)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

set_option maxRecDepth 100000 in
theorem findDef_extend' (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "extend__" = some (ps, t, []) := ⟨_, _, rfl⟩

/-- `$extend__(N, 128, U, %(k))` under `FloatB`: the zero extension, for `k < 2 ^ N`. -/
theorem applies_extend128 {P : Numerics.Profile} {B : Builtins} (hF : Floats.FloatB P B)
    (N k : Nat) (hk : k < 2 ^ N) (hN : N ≤ 128) :
    Applies (simEnv B) "extend__" [.val (natV N), .val (natV 128), .val (caseNilV "U"),
      .val (pctV k)] (pctV k) := by
  refine Prims.applies_of_noClause (findDef_extend' B) (hF _ _ _ ?_)
  simp only [Floats.floatCall, show "extend__" ∈ Floats.floatNames by decide, ite_true]
  show Floats.extendBits N 128 (caseNilV "U") (pctV k) = _
  have h₁ : (BitVec.ofNat N k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk
  have h₂ : k < 2 ^ 128 := lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) hN)
  simp [Floats.extendBits, IntNumeric.asSx?, caseNilV, pctV, Equiv.ExecBuiltins.asBits?,
    Equiv.bvV, natV, BitVec.toNat_setWidth, h₁]
  exact h₂

/-- The zero-extended vector keeps the loaded bits. -/
theorem toNat_setWidth128 {n : Nat} (c : BitVec n) (hn : n ≤ 128) :
    (c.setWidth 128).toNat = c.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by decide) hn))

/-! ## The rule, for arbitrary state values -/

section Rule

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))
  (Bf : BytesFuns (simEnv B))

include St M Bf in
/-- **`Step_read/vload-zero-val`** (rule 49), at `N ∈ {32, 64}`. -/
theorem fires_vloadZeroVal {P : Numerics.Profile} (hF : Floats.FloatB P B) (N : Nat)
    (hN : N = 32 ∨ N = 64) {S F m : Value} {bs : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {n k : Nat} {arg : MemArg} (hk : k < 2 ^ N)
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs)) (hsl : SliceAt bs (i.toNat + arg.offset.val) (N / 8))
    (hc : leBytesV (N / 8) k = (bs.drop (i.toNat + arg.offset.val)).take (N / 8)) :
    Fires (simEnv B) "Step_read" 49 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vloadV (some (.case "ZERO" (.tuple [pctV N]))) n arg],
      .list [.case "VCONST" (.tuple [caseNilV "V128", pctV k])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("N", .num (.natN N)), ("x", idxV n), ("ao", memargV arg),
    ("c", pctV k), ("j", pctV k)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have h128 : k < 2 ^ 128 := lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega))
  have hcT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ)
      (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV k) := by
    have h := Typing.hasTyp_vec (B := B) (ρ := VarEnv.empty.bindVals σ) (BitVec.ofNat 128 k)
      evalExp_v128
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128] at h
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "ibytes_" [.expA (.varE "N"), .expA (.varE "j")]) (.list (leBytesV (N / 8) k)) :=
    FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl)
      evalArgs_nil)) (Bf.ibytes N k)
  have e₂ := FwdMem.evalExp_memSlice (σ := σ) (ez := .varE "z") (ex := .varE "x")
    (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl) hm hB
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
    (Memory.evalExp_div8 (e := .varE "N") (by omega) (evalExp_var rfl)) hsl
  rw [← hc] at e₂
  have e₃ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "extend__" [.expA (.varE "N"), .expA (.numE (.natN 128)),
        .expA (.caseE "U" (.tupE [])), .expA (.varE "j")]) (pctV k) :=
    FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var rfl) (evalArgs_cons
      RefsGC.evalExp_num' (evalArgs_cons (evalExp_case (RefsGC.evalExp_tupE_of
        RefsGC.evalExps_nil')) (evalArgs_cons (evalExp_var rfl) evalArgs_nil))))
      (applies_extend128 hF N k hk (by omega))
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadZeroVal σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_N B) _ _ hρ)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            (QuantsOk.cons rfl hcT (QuantsOk.cons rfl (FwdMem.hasTyp_iN_var rfl hk)
              QuantsOk.nil))))))))
    (by mem_eval_tac)
    (prems_two (.ifPr (RefsGC.evalExp_eq_true e₁ e₂))
      (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) e₃)))

end Rule

/-! ## The concrete primitives with `$vbytes_` -/

section Concrete

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H} {F : Value}

/-- `withVBytes` changes only `$vbytes_`. -/
theorem call_withVBytes_of_ne (B : Builtins) {x : IL.Id} (hx : x ≠ "vbytes_") (ws : List ArgV) :
    (withVBytes B).call x ws = B.call x ws := by
  simp [withVBytes, hx]

/-- `withVBytes (Prims.builtins …)` answers the float and conversion primitives. -/
theorem floatB_vb : Floats.FloatB P (withVBytes (Prims.builtins P hn host)) := by
  intro x ws v h
  have hx : x ≠ "vbytes_" := by
    rintro rfl
    simp [Floats.floatCall, Floats.floatNames] at h
  rw [call_withVBytes_of_ne _ hx]
  exact Prims.floatB_builtins hn host x ws v h

/-- `withVBytes (Prims.builtins …)` answers `$nbytes_` and `$ibytes_` by Core's encoding. -/
theorem bytesFuns_vb : BytesFuns (simEnv (withVBytes (Prims.builtins P hn host))) where
  nbytes v := by
    obtain ⟨t, b⟩ := v
    refine Prims.applies_of_noClause (FwdMem.findDef_nbytes _) ?_
    rw [show (simEnv (withVBytes (Prims.builtins P hn host))).builtins =
      withVBytes (Prims.builtins P hn host) from rfl, call_withVBytes_of_ne _ (by decide),
      Typing.toValue_numType]
    simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames,
      FwdMem.nbytesCall, Floats.decNumType_numTypeV, Floats.decNum_numV]
  ibytes N k := by
    refine Prims.applies_of_noClause (FwdMem.findDef_ibytes _) ?_
    rw [show (simEnv (withVBytes (Prims.builtins P hn host))).builtins =
      withVBytes (Prims.builtins P hn host) from rfl, call_withVBytes_of_ne _ (by decide)]
    simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames,
      FwdMem.ibytesCall, pctV]

end Concrete

/-! ## Core's `vecLoadVal` at `.zero32`/`.zero64`, forward -/

section Forward

variable {B : Builtins} {H : Type} {hn : H → String}

/-- The load shape of a zero-extending load. -/
def zeroOp : Nat → VecLoadOp
  | 32 => .zero32
  | _ => .zero64

theorem vecLoadOpV_zeroOp {N : Nat} (hN : N = 32 ∨ N = 64) :
    Round6.MemSimd.vecLoadOpV (zeroOp N) = some (.case "ZERO" (.tuple [pctV N])) := by
  rcases hN with rfl | rfl <;> rfl

/-- **`MemoryStep.vecLoadVal` at `.zero32`/`.zero64`, forward**: from a typed state image, the
in-bounds zero-extending load is a `Step_read` step to Core's zero-extended vector, in both
readings, for a `B` with `BytesFuns` and `FloatB`. -/
theorem fwd_vecLoadZero {P : Numerics.Profile} (Bf : BytesFuns (simEnv B))
    (hF : Floats.FloatB P B) {N : Nat} (hN : N = 32 ∨ N = 64) {s : Store H} {f : Frame}
    {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {ma : Nat}
    {mi : MemInst} {c : BitVec (8 * (N / 8))}
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (N / 8) = some c) :
    SRead (simEnv B) (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad (zeroOp N) x arg)])
      [adminToV (.plain (.vecConst (c.setWidth 128)))] ∧
      Round6.Reading.SReadB (simEnv B) (cfgV (stateV hn s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (zeroOp N) x arg)])
        [adminToV (.plain (.vecConst (c.setWidth 128)))] := by
  rw [State.adminToV_aconst, instrToVM_vecLoad, vecLoadOpV_zeroOp hN]
  obtain ⟨hle, hb⟩ := FwdMem.load_bytesV hl
  have hw : 8 * (N / 8) = N := by omega
  have hk : c.toNat < 2 ^ N := lt_of_lt_of_eq c.isLt (by rw [hw])
  have hv : adminToV (.plain (.vecConst (c.setWidth 128))) =
      .case "VCONST" (.tuple [caseNilV "V128", pctV c.toNat]) := by
    show vconstV (c.setWidth 128) = _
    rw [vconstV, toNat_setWidth128 c (by omega)]
  rw [hv]
  exact sread_of_fires loadTags_noCast (lhsIn_vload _ _ _ _ _ _)
    (fires_vloadZeroVal (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _) Bf hF N hN hk
      hz x.value.isLt (memAt_of_mem? hn hm) (FwdMem.memInstV_BYTES' mi)
      (FwdMem.sliceAt_of_or (.inl FwdMem.sliceTotal) hle) hb)

end Forward

/-! ## Backward -/

section Backward

variable {B : Builtins} {H : Type} {hn : H → String} {F : Value}

/-- The premise `c = $extend__(N, 128, U, j)` at `j = %(k)` with `k < 2 ^ N`: `c` is `%(k)`. -/
theorem extendPrem_inv {P : Numerics.Profile} (hF : Floats.FloatB P B) {N k : Nat}
    (hN : N = 32 ∨ N = 64) {σ : List (IL.Id × Value)} {C : Value}
    (fN : (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN N)))
    (fJ : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV k)) (hk : k < 2 ^ N)
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.callE "extend__" [.expA (.varE "N"),
      .expA (.numE (.natN 128)), .expA (.caseE "U" (.tupE [])), .expA (.varE "j")]) C) :
    C = pctV k := by
  have hX : Applies (simEnv B) "extend__" [.val (natV N), .val (natV 128), .val (caseNilV "U"),
      .val (pctV k)] C :=
    (applies_iff_callDef (Memory.findDef_bindVals_empty σ _) (evalArgs_cons (evalExp_var fN)
      (evalArgs_cons RefsGC.evalExp_num' (evalArgs_cons (evalExp_case (RefsGC.evalExp_tupE_of
        RefsGC.evalExps_nil')) (evalArgs_cons (evalExp_var fJ) evalArgs_nil))))).2
      (evalExp_callE_iff.1 h)
  exact Applies.unique hX (applies_extend128 hF N k hk (by omega))

/-- **`Step_read/vload-zero-val`, backward** (rule 49), at `ZERO N` with `N ∈ {32, 64}`, for a
`B` that does not interpret the state accessors and answers `$ibytes_` and `$extend__` as
Core does: the memory resolves, Core's `N/8`-byte load succeeds, and the result is `VCONST` of
the zero-extended word. -/
theorem bwd_vloadZeroVal {P : Numerics.Profile} (NA : BwdRead.NoAcc B)
    (hib : ∀ (N : Nat) (c u : Value), Applies (simEnv B) "ibytes_" [.val (.num (.natN N)), .val c]
      u → ∃ k, c = pctV k ∧ u = .list (leBytesV (N / 8) k))
    (hF : Floats.FloatB P B) {N : Nat} (hN : N = 32 ∨ N = 64) {s : Store H} {f : Frame}
    {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {w : Value}
    (hf : Fires (simEnv B) "Step_read" 49 (.tuple [cfgV (stateVF F s f)
      [aconstV (Encode.toValue a) i.toNat, vloadV (some (.case "ZERO" (.tuple [pctV N]))) x.toNat
        arg], w])) :
    ∃ (ma : Nat) (mi : MemInst) (c : BitVec (8 * (N / 8))), s.mem? f x = some (ma, mi) ∧
      Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (N / 8) = some c ∧
      w = .list [.case "VCONST" (.tuple [caseNilV "V128", pctV c.toNat])] := by
  obtain ⟨σ, hq, fz, fx, fi, fao, ho, hr, hp⟩ :=
    fires_vload_inv (State.hasReadRules_simEnv B).vloadZeroVal hf
  have fN := optZero_N ho
  -- `j : iN(N)` is a numeral below `2 ^ N`.
  obtain ⟨J, fJ, hJ⟩ := hq "j" (.varT "iN" [.expA (.varE "N")]) (by simp)
  obtain ⟨k, rfl, hk⟩ := iN_inv_lt (evalExp_var fN) hJ
  -- Premise 1: `$ibytes_(N, j)` is the slice, so `j` is Core's loaded word.
  obtain ⟨V, e₁, e₂⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ List.mem_cons_self))
  have hA : Applies (simEnv B) "ibytes_" [.val (.num (.natN N)), .val (pctV k)] V :=
    (applies_iff_callDef (Memory.findDef_bindVals_empty σ _) (evalArgs_cons (evalExp_var fN)
      (evalArgs_cons (evalExp_var fJ) evalArgs_nil))).2 (evalExp_callE_iff.1 e₁)
  obtain ⟨k', hk', rfl⟩ := hib N _ V hA
  obtain rfl : k = k' := Round5.Read2.pctV_inj hk'
  obtain ⟨ma, mi, c, hm, hl, hcn⟩ := memSlice_load NA fz fx fi fao
    (Memory.evalExp_div8 (e := .varE "N") (by omega) (evalExp_var fN))
    (lt_of_lt_of_eq hk (by congr 1; omega)) e₂
  -- Premise 2: `c = $extend__(N, 128, U, j)`, the zero extension of `j`.
  obtain ⟨C, eC, eX⟩ := Bwd.eq_of_cmp (RefsGC.premW_if
    (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  obtain rfl : C = pctV k := extendPrem_inv hF hN fN fJ hk eX
  exact ⟨ma, mi, c, hm, hl, by rw [rhs_vconst (evalExp_varE_iff.1 eC) hr, hcn]⟩

/-- `$ibytes_` at `withVBytes (Prims.builtins …)`, read back. -/
theorem ibytes_inv_vb {P : Numerics.Profile} {host : HostSemantics H} (N : Nat) (c u : Value)
    (h : Applies (simEnv (withVBytes (Prims.builtins P hn host))) "ibytes_"
      [.val (.num (.natN N)), .val c] u) :
    ∃ k, c = pctV k ∧ u = .list (leBytesV (N / 8) k) := by
  have hb := Round5.Simd.applies_noClause_iff (FwdMem.findDef_ibytes _) h
  rw [show (simEnv (withVBytes (Prims.builtins P hn host))).builtins =
    withVBytes (Prims.builtins P hn host) from rfl, call_withVBytes_of_ne _ (by decide)] at hb
  have hc : FwdMem.ibytesCall (.num (.natN N)) c = some u := by
    simpa [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
      Floats.floatNames] using hb
  obtain ⟨n, rfl⟩ : ∃ n, c = pctV n := by
    unfold FwdMem.ibytesCall at hc
    split at hc <;> simp_all [pctV]
  simp only [FwdMem.ibytesCall, pctV, Option.some.injEq] at hc
  exact ⟨n, rfl, hc.symm⟩

/-- **`v128.loadN_zero` in bounds at round 6's backend reading, backward**, at the concrete
primitives with `$vbytes_` answered: the result is the image of Core's zero-extended load, and
Core's `vecLoadVal` steps there. -/
theorem bwdB_vecLoadZero {P : Numerics.Profile} {host : HostSemantics H} {N : Nat}
    (hN : N = 32 ∨ N = 64) {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {w : Value}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 49
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (zeroOp N) x arg)], w])) :
    ∃ v : BitVec 128, w = .list [adminToV (.plain (.vecConst v))] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad (zeroOp N) x arg)]⟩
        ⟨s, f, [.plain (.vecConst v)]⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f)
      [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (zeroOp N) x arg)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoad]; exact lhsIn_vload _ _ _ _ _ _
  have hf' := (Round6.Reading.firesB_read_iff _ loadTags_noCast ha).1 hf
  rw [State.adminToV_aconst, instrToVM_vecLoad, vecLoadOpV_zeroOp hN] at hf'
  obtain ⟨ma, mi, c, hm, hl, rfl⟩ := bwd_vloadZeroVal noAcc_vb ibytes_inv_vb floatB_vb hN hf'
  have hw : 8 * (N / 8) = N := by omega
  refine ⟨c.setWidth 128, ?_, ?_⟩
  · show Value.list [.case "VCONST" (.tuple [caseNilV "V128", pctV c.toNat])] =
      Value.list [vconstV (c.setWidth 128)]
    rw [vconstV, toNat_setWidth128 c (by omega)]
  · rcases hN with rfl | rfl
    · exact .memory (.vecLoadVal (op := .zero32) hm hl)
    · exact .memory (.vecLoadVal (op := .zero64) hm hl)

end Backward

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
