module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadLaneBwd

/-!
# Round 7, memory SIMD: `v128.loadKxM_sx`, in bounds (`Step_read` 45), forward

`Step_read/vload-pack-val`: `z; (CONST at i) (VLOAD V128 (SHAPE K X M _ sx) x ao) ~>
(VCONST V128 c)` under two premises:

* `($ibytes_(K, j) = $mem(z, x).BYTES[i + ao.OFFSET + k * K/8 : K/8])^(k<M)`, an iterated
  premise over `j*` with the index variable `k`;
* `c = $inv_lanes_(Jnn X M, $extend__(K, $jsizenn(Jnn), sx, j)^M) ∧ $jsizenn(Jnn) = K * 2`.

`j*` and `Jnn` are quantified and bound only by the premises; the declarative reading picks the
`M` lanes of the loaded 64 bits and the integer shape whose lane width is `2 * K`. Core's
`vecLoadVal` at `.extend8x8`/`.extend16x4`/`.extend32x2` loads 8 bytes and widens each `K`-bit
lane (`extendLanes`).

* `encL_mod`, `drop_take_encL`, `leBytesV_lane`: lane `r` of a little-endian word is the
  sub-slice `[r * b : b]` of its bytes.
* `dprem_iterListN1`, `evalExp_iterListN1`: an iterated premise over one domain with an index
  variable, and a counted iteration over one domain.
* `fires_vloadPackVal`: the rule fires, for arbitrary typed state values.
* `fwd_vecLoadPack`: **Core's `vecLoadVal` at the three widening loads, forward**, as a
  `Step_read` step in both readings at `withVBytes (Prims.builtins …)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (invLanes)
open State (aconstV idxV StateTyping)
open Memory (MemAt MemTyping memAt_of_mem?)
open FwdMem (leBytesV bytesV SliceAt)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-! ## Lanes of a little-endian word -/

/-- `encL` reads only the low `k` bytes. -/
theorem encL_mod : ∀ (k n : Nat), FwdMem.encL k (n % 256 ^ k) = FwdMem.encL k n
  | 0, _ => rfl
  | k + 1, n => by
    have h₁ : UInt8.ofNat (n % 256 ^ (k + 1)) = UInt8.ofNat n := by
      apply UInt8.toNat_inj.1
      simp only [UInt8.toNat_ofNat']
      exact Nat.mod_mod_of_dvd n (dvd_pow (by decide : 2 ^ 8 ∣ 256) (Nat.succ_ne_zero k))
    have h₂ : n % 256 ^ (k + 1) / 256 = n / 256 % 256 ^ k := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    simp only [FwdMem.encL, h₁, h₂, encL_mod k]

/-- A prefix of an encoding is the shorter encoding. -/
theorem take_encL : ∀ (b m n : Nat), b ≤ m → (FwdMem.encL m n).take b = FwdMem.encL b n
  | 0, _, _, _ => by simp [FwdMem.encL]
  | _ + 1, 0, _, h => absurd h (by omega)
  | b + 1, m + 1, n, h => by
    simp only [FwdMem.encL, List.take_succ_cons, take_encL b m (n / 256) (by omega)]

/-- **A window of an encoding is the encoding of the shifted value.** -/
theorem drop_take_encL : ∀ (a b m n : Nat), a + b ≤ m →
    ((FwdMem.encL m n).drop a).take b = FwdMem.encL b (n / 256 ^ a)
  | 0, b, m, n, h => by simpa using take_encL b m n (by omega)
  | _ + 1, _, 0, _, h => absurd h (by omega)
  | a + 1, b, m + 1, n, h => by
    simp only [FwdMem.encL, List.drop_succ_cons]
    rw [drop_take_encL a b m (n / 256) (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- **Lane `r` of a loaded 8-byte word is the sub-slice at `r * b`.** -/
theorem leBytesV_lane {bs : List Value} {ea b r c : Nat}
    (hc : leBytesV 8 c = (bs.drop ea).take 8) (hrb : r * b + b ≤ 8) :
    leBytesV b (c / 256 ^ (r * b) % 256 ^ b) = (bs.drop (ea + r * b)).take b := by
  have hw : (bs.drop (ea + r * b)).take b = (((bs.drop ea).take 8).drop (r * b)).take b := by
    rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
  rw [hw, ← hc, Round5.Read2.leBytesV_eq_map, Round5.Read2.leBytesV_eq_map, ← List.map_drop,
    ← List.map_take, drop_take_encL _ _ _ _ hrb, encL_mod]

/-- `(k * K) / 8`, through `ℚ`, at a multiple of `8`. -/
theorem evalExp_div8' {env : Env} {ρ : VarEnv} {e : Exp} {w : Nat} (hw : 8 ∣ w)
    (h : EvalExp env ρ e (.num (.natN w))) :
    EvalExp env ρ (.cvtE (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (w / 8))) := by
  have e₁ : EvalExp env ρ (.cvtE e .natT .ratT) (.num (.ratN w)) :=
    evalExp_cvtE_iff.2 ⟨_, _, h, rfl, rfl⟩
  have e₂ : EvalExp env ρ (.cvtE (.numE (.natN 8)) .natT .ratT) (.num (.ratN 8)) :=
    evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_num', rfl, rfl⟩
  have hq : ((w : ℚ) / 8) = ((w / 8 : Nat) : ℚ) := by
    obtain ⟨q, rfl⟩ := hw
    rw [Nat.mul_div_cancel_left q (by decide)]
    push_cast; ring
  have e₃ : EvalExp env ρ (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) (.num (.ratN ((w / 8 : Nat) : ℚ))) :=
    evalExp_binE_iff.2 ⟨_, e₁, .inr ⟨rfl, _, e₂, by
      simp only [binValues, Num.bin, show (8 : ℚ) ≠ 0 by decide, ↓reduceIte, hq]
      rfl⟩⟩
  have hc : Num.cvt .natT (.ratN ((w / 8 : Nat) : ℚ)) = some (.natN (w / 8)) := by
    simp only [Num.cvt, Rat.den_natCast, Rat.num_natCast, Int.toNat_natCast]
    simp only [Int.natCast_nonneg, and_self, ↓reduceIte]
  exact evalExp_cvtE_iff.2 ⟨_, _, e₃, hc, rfl⟩

/-! ## Counted iterations over one domain -/

/-- One domain `x ← y`, evaluated. -/
theorem evalDoms_one {env : Env} {ρ : VarEnv} {x y : IL.Id} {vs : List Value}
    (hy : ρ.findVal? y = some (.list vs)) (d : Nat) :
    evalDoms (d + 2) env ρ [.mk x (.varE y)] = .ok [(x, .list vs)] := by
  simp [evalDoms, domVar, domSrc, evalExp, hy]

/-- **An iterated premise `pr^(idx<k)` over one domain `x ← y`**, from one derivation per round,
under that round's bindings. -/
theorem dprem_iterListN1 {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {eₙ : Exp} {x y idx : IL.Id} {vs : List Value} {k : Nat}
    (hy : ρ.findVal? y = some (.list vs)) (hn : EvalExp env ρ eₙ (.num (.natN k)))
    (hlen : vs.length = k)
    (hr : ∀ i (hi : i < vs.length),
      DPrem env O els (ρ.bindVals [(x, vs[i]), (idx, .num (.natN i))]) pr) :
    DPrem env O els ρ (.iterPr pr (.mk (.listN eₙ (some idx)) [.mk x (.varE y)])) := by
  refine .iterListN (xvs := [(x, .list vs)]) (dls := [(x, vs)]) ⟨2, evalDoms_one hy 0⟩ hn rfl
    (by simp [domLists, Value.asList?]) (by simp [hlen]) ?_
  intro r hr'
  simp only [iterRows, List.mem_map, List.mem_range] at hr'
  obtain ⟨i, hi, rfl⟩ := hr'
  have hi' : i < vs.length := hlen ▸ hi
  have hrow : iterRow [(x, vs)] (some idx) i = [(x, vs[i]), (idx, .num (.natN i))] := by
    simp [iterRow, List.getElem?_eq_getElem hi']
  rw [hrow]
  exact hr i hi'

/-- One round per element of a single domain, at a common fuel. -/
theorem mapM_rounds_one {env : Env} {ρ : VarEnv} {b : Exp} {x : IL.Id} {d m : Nat} :
    ∀ {vs ws : List Value},
      List.Forall₂ (fun v w => evalExp d env (ρ.bindVals [(x, v)]) b = .ok w) vs ws →
      (vs.map fun w => [(x, w)]).mapM (fun r => evalExp (d + m) env (ρ.bindVals r) b) = .ok ws
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hvw hs => by
      simp only [List.map_cons, List.mapM_cons, Res.bind_eq_ok]
      exact ⟨_, evalExp_ok_of_le (by omega) hvw, _, mapM_rounds_one hs, rfl⟩

/-- **`b^k` over one domain `x ← y`**: the list of the body's values, round by round. -/
theorem evalExp_iterListN1 {env : Env} {ρ : VarEnv} {b eₙ : Exp} {x y : IL.Id}
    {vs ws : List Value} {k : Nat} (hy : ρ.findVal? y = some (.list vs))
    (hn : EvalExp env ρ eₙ (.num (.natN k))) (hlen : vs.length = k)
    (hb : List.Forall₂ (fun v w => EvalExp env (ρ.bindVals [(x, v)]) b w) vs ws) :
    EvalExp env ρ (.iterE b (.mk (.listN eₙ none) [.mk x (.varE y)])) (.list ws) := by
  obtain ⟨d, hd⟩ := Vec.forall₂_fuel hb
  obtain ⟨m, hm⟩ := hn
  refine evalExp_iterE_iff.mpr ⟨d + m + 3, ?_⟩
  have hdoms := evalDoms_one (env := env) (x := x) hy (d + m)
  have he : evalExp (d + m + 2) env ρ eₙ = .ok (.num (.natN k)) :=
    evalExp_ok_of_le (by omega) hm
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, he, Res.ofOption_eq_ok]
  refine ⟨[(x, Value.list vs)], rfl, _, rfl, k, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_cons,
    List.mapM_nil]
  refine ⟨[(x, vs)], by simp [Value.asList?], by simp [hlen], ws, ?_, rfl⟩
  rw [← hlen, Equiv.Execution.iterRows_singleton, evalRounds]
  exact mapM_rounds_one hd

/-! ## The rule, for arbitrary state values -/

/-- The body of rule 45's iterated premise. -/
abbrev packBytesPrem : Exp :=
  .cmpE .eqOp .boolT (.callE "ibytes_" [.expA (.varE "K"), .expA (.varE "j")])
    (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")
      (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT)
        (.projE (.uncaseE (.varE "i") "%") 0) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.binE .mulOp (.numT .natT) (.varE "k")
          (.varE "K")) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "K") .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))

/-- `$extend__(K, $jsizenn(Jnn), sx, j)`, the body of rule 45's result iteration. -/
abbrev packExtendE : Exp :=
  .callE "extend__" [.expA (.varE "K"), .expA (.callE "jsizenn" [.expA (.varE "Jnn")]),
    .expA (.varE "sx"), .expA (.varE "j")]

variable {B : Builtins}

/-- **One round of rule 45's byte premise**: lane `l`'s bytes are the sub-slice at `l * K/8`. -/
theorem evalExp_packBytesPrem (Bf : FwdMem.BytesFuns (simEnv B)) {σ : List (IL.Id × Value)}
    {S F m : Value} {bs : List Value} {n I K l kr : Nat} {arg : MemArg} (hK8 : 8 ∣ K)
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV S F))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV n))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (fK : (VarEnv.empty.bindVals σ).findVal? "K" = some (.num (.natN K)))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV kr))
    (fk : (VarEnv.empty.bindVals σ).findVal? "k" = some (.num (.natN l)))
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hsl : SliceAt bs (I + arg.offset.val + l * K / 8) (K / 8))
    (hc : leBytesV (K / 8) kr = (bs.drop (I + arg.offset.val + l * K / 8)).take (K / 8)) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ) packBytesPrem (.bool true) := by
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "ibytes_" [.expA (.varE "K"), .expA (.varE "j")]) (.list (leBytesV (K / 8) kr)) :=
    FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var fK) (evalArgs_cons (evalExp_var fj)
      evalArgs_nil)) (Bf.ibytes K kr)
  have eStart := RefsGC.evalExp_addNat (t := .numT .natT)
    (Memory.evalExp_effAddr (env := simEnv B) (evalExp_var fi) (evalExp_var fao))
    (evalExp_div8' (Dvd.dvd.mul_left hK8 l) (RefsGC.evalExp_mulNat (t := .numT .natT)
      (evalExp_var fk) (evalExp_var fK)))
  have e₂ := FwdMem.evalExp_memSlice (ez := .varE "z") (ex := .varE "x")
    (State.stateDefs_simEnv B) (evalExp_var fz) (evalExp_var fx) hm hB eStart
    (evalExp_div8' hK8 (evalExp_var fK)) hsl
  rw [← hc] at e₂
  exact RefsGC.evalExp_eq_true e₁ e₂

/-- Binding more values after a `bindVals` is one `bindVals`. -/
theorem bindVals_bindVals (σ r : List (IL.Id × Value)) :
    (VarEnv.empty.bindVals σ).bindVals r = VarEnv.empty.bindVals (σ ++ r) := by
  simp [VarEnv.bindVals, Map.binds, List.foldl_append]

/-- **One round of rule 45's result iteration**: `$extend__(K, $jsizenn(Jnn), sx, j)` at
`j = v`, given what `$extend__` answers there. -/
theorem evalExp_packExtend {σ : List (IL.Id × Value)} (s2 : IntShape) {K : Nat}
    {sx v w : Value}
    (fK : (VarEnv.empty.bindVals σ).findVal? "K" = some (.num (.natN K)))
    (fJ : (VarEnv.empty.bindVals σ).findVal? "Jnn" = some (Vec.intLaneV s2))
    (fsx : (VarEnv.empty.bindVals σ).findVal? "sx" = some sx)
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some v)
    (h : Applies (simEnv B) "extend__" [.val (natV K), .val (natV s2.laneWidth), .val sx, .val v]
      w) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ) packExtendE w :=
  FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var fK) (evalArgs_cons
    (FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var fJ) evalArgs_nil)
      (Round5.Simd.applies_jsizenn s2)) (evalArgs_cons (evalExp_var fsx)
        (evalArgs_cons (evalExp_var fj) evalArgs_nil)))) h

/-- `j* : iN(K)*` for a list of numerals below `2 ^ K`. -/
theorem hasTyp_iNs {σ : List (IL.Id × Value)} {K : Nat} {js : List Value}
    (fK : (VarEnv.empty.bindVals σ).findVal? "K" = some (.num (.natN K)))
    (hjT : ∀ v ∈ js, ∃ k, v = pctV k ∧ k < 2 ^ K) :
    HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.iterT (.varT "iN" [.expA (.varE "K")]) .list)
      (.list js) :=
  hasTyp_iterT_list_iff.2 ⟨js, rfl, hasTypList_iff.2 fun v hv => by
    obtain ⟨k, rfl, hk⟩ := hjT v hv
    exact FwdMem.hasTyp_iN_var fK hk⟩

variable (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))
  (Bf : FwdMem.BytesFuns (simEnv B))

include St M Bf in
/-- **`Step_read/vload-pack-val`** (rule 45), at the integer shape `s2` of the widened lanes
(lane width `K * 2`): lane `l` of `j*` is the word at the sub-slice `l * K/8`, `ws` are their
extensions, and `$inv_lanes_` of them is `r`. -/
theorem fires_vloadPackVal (s2 : IntShape) {K : Nat} (hK8 : 8 ∣ K) (hK2 : s2.laneWidth = K * 2)
    {S F m : Value} {bs : List Value} {a : AddrType} {i : BitVec a.intType.width} {n r : Nat}
    {arg : MemArg} {sx : Signedness} {js ws : List Value} (hjs : js.length = s2.lanes)
    (hjT : ∀ v ∈ js, ∃ k, v = pctV k ∧ k < 2 ^ K)
    (hrow : ∀ l (hl : l < js.length), ∃ kr, js[l] = pctV kr ∧
      SliceAt bs (i.toNat + arg.offset.val + l * K / 8) (K / 8) ∧
      leBytesV (K / 8) kr = (bs.drop (i.toNat + arg.offset.val + l * K / 8)).take (K / 8))
    (hext : List.Forall₂ (fun v w => Applies (simEnv B) "extend__"
      [.val (natV K), .val (natV s2.laneWidth), .val (Vec.sxV sx), .val v] w) js ws)
    (hinv : Applies (simEnv B) "inv_lanes_" [.val (Vec.ishV s2), .val (.list ws)] (pctV r))
    (hr : r < 2 ^ 128) (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs)) :
    Fires (simEnv B) "Step_read" 45 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vloadV (some (.case "SHAPE%X%_%" (.tuple [pctV K, pctV s2.lanes, Vec.sxV sx]))) n arg],
      .list [.case "VCONST" (.tuple [caseNilV "V128", pctV r])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("K", .num (.natN K)), ("M", pctV s2.lanes), ("sx", Vec.sxV sx),
    ("x", idxV n), ("ao", memargV arg), ("c", pctV r), ("j*", .list js),
    ("Jnn", Vec.intLaneV s2)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hcT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ)
      (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV r) := by
    have h := Typing.hasTyp_vec (B := B) (ρ := VarEnv.empty.bindVals σ) (BitVec.ofNat 128 r)
      evalExp_v128
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr] at h
  -- The iterated byte premise, one round per lane.
  have p₁ : DPrem (simEnv B) (otherwise (simEnv B)) (otherwise (simEnv B) "Step_read" [] 45
      (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        vloadV (some (.case "SHAPE%X%_%" (.tuple [pctV K, pctV s2.lanes, Vec.sxV sx]))) n arg],
        .list [.case "VCONST" (.tuple [caseNilV "V128", pctV r])]]))
      (VarEnv.empty.bindVals σ) (.iterPr (.ifPr packBytesPrem) (.mk (.listN (.projE (.uncaseE
        (.varE "M") "%") 0) (some "k")) [.mk "j" (.varE "j*")])) := by
    refine dprem_iterListN1 rfl (RefsGC.evalExp_unpct (evalExp_var rfl)) hjs fun l hl => ?_
    obtain ⟨kr, hj, hsl, hc⟩ := hrow l hl
    rw [bindVals_bindVals, hj]
    exact .ifPr (evalExp_packBytesPrem Bf hK8 rfl rfl rfl rfl rfl rfl rfl hm hB hsl hc)
  -- `c = $inv_lanes_(Jnn X M, $extend__(…)^M)` and `$jsizenn(Jnn) = K * 2`.
  have eSh : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) shapeE (Vec.ishV s2) :=
    evalExp_case (evalExp_tup2 (RefsGC.evalExp_sub_of (evalExp_var rfl)) (evalExp_var rfl))
  have eIt : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.iterE packExtendE
      (.mk (.listN (.projE (.uncaseE (.varE "M") "%") 0) none) [.mk "j" (.varE "j*")]))
      (.list ws) :=
    evalExp_iterListN1 rfl (RefsGC.evalExp_unpct (evalExp_var rfl)) hjs
      (hext.imp fun v w h => by
        rw [bindVals_bindVals]; exact evalExp_packExtend s2 rfl rfl rfl rfl h)
  have e₄ := FwdMem.evalExp_call_applies (σ := σ)
    (evalArgs_cons eSh (evalArgs_cons eIt evalArgs_nil)) hinv
  have eJs : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "jsizenn" [.expA (.varE "Jnn")]) (natV s2.laneWidth) :=
    FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var rfl) evalArgs_nil)
      (Round5.Simd.applies_jsizenn s2)
  have eK2 : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .mulOp (.numT .natT) (.varE "K") (.numE (.natN 2))) (natV s2.laneWidth) := by
    rw [hK2]; exact RefsGC.evalExp_mulNat (evalExp_var rfl) RefsGC.evalExp_num'
  have p₂ := RefsGC.evalExp_and_true (t := .boolT)
    (RefsGC.evalExp_eq_true (t := .boolT) (evalExp_var (x := "c") rfl) e₄)
    (RefsGC.evalExp_eq_true (t := .boolT) eJs eK2)
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadPackVal σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_K B) _ _ hρ)
          (QuantsOk.cons rfl (Round5.SimdTy.typedV_M (.int s2) _ hρ)
            (QuantsOk.cons rfl (ConfigOk.typedV_sx sx _ hρ)
              (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
                (QuantsOk.cons rfl hcT (QuantsOk.cons rfl (hasTyp_iNs rfl hjT)
                  (QuantsOk.cons rfl (Round5.SimdTy.typedV_jnn s2 _ hρ)
                    QuantsOk.nil)))))))))))
    (by mem_eval_tac)
    (prems_two p₁ (.ifPr p₂))

/-! ## Core's widening loads, forward -/

/-- `$extend__(N, N', sx, %(x))` under `FloatB`: Core's sign or zero extension. -/
theorem applies_extendW {P : Numerics.Profile} (hF : Floats.FloatB P B) (N N' : Nat)
    (sx : Signedness) (x : BitVec N) :
    Applies (simEnv B) "extend__" [.val (natV N), .val (natV N'), .val (Vec.sxV sx),
      .val (pctV x.toNat)]
      (pctV (match sx with | .signed => x.signExtend N' | .unsigned => x.setWidth N').toNat) := by
  refine Prims.applies_of_noClause (findDef_extend' B) (hF _ _ _ ?_)
  simp only [Floats.floatCall, show "extend__" ∈ Floats.floatNames by decide, ite_true]
  show Floats.extendBits N N' (Vec.sxV sx) (pctV x.toNat) = _
  cases sx <;> simp [Floats.extendBits, IntNumeric.asSx?, Vec.sxV, pctV, caseNilV,
    Equiv.ExecBuiltins.asBits?, Equiv.bvV, natV]

/-- Lane `k` of a widening load: the `K`-bit lane `k` of `c`, extended to `2 * K` bits. -/
def packLane (K : Nat) (sx : Signedness) {n : Nat} (c : BitVec n) (k : Nat) : BitVec (2 * K) :=
  match sx with
  | .signed => (c.extractLsb' (k * K) K).signExtend (2 * K)
  | .unsigned => (c.extractLsb' (k * K) K).setWidth (2 * K)

theorem extendLanes_eq (K M : Nat) (sx : Signedness) {n : Nat} (c : BitVec n) :
    extendLanes K M sx c = invLanes (2 * K) ((List.range M).map (packLane K sx c)) := by
  cases sx <;> rfl

/-- The lanes of a 128-bit pattern at width `w`, as `%`-numerals. -/
def lanesNatV (w m : Nat) (v : BitVec 128) : List Value :=
  (Numerics.lanesW w m v).map fun x => pctV x.toNat

theorem lanesV_int (s : IntShape) (v : BitVec 128) :
    Round5.Simd.lanesV (.int s) v = lanesNatV s.laneWidth s.lanes v := rfl

/-- **The lanes of Core's widening load** are the widened lanes. -/
theorem lanesV_extendLanes (s2 : IntShape) {K : Nat} (hK2 : s2.laneWidth = 2 * K)
    (sx : Signedness) (c : BitVec 64) :
    Round5.Simd.lanesV (.int s2) (extendLanes K s2.lanes sx c) =
      (List.range s2.lanes).map fun k => pctV (packLane K sx c k).toNat := by
  rw [lanesV_int, extendLanes_eq, hK2, lanesNatV, invLanes,
    Numerics.lanesW_invLanesW (by rw [← hK2]; exact Nat.le_of_eq s2.size) _ (by simp),
    List.map_map]
  rfl

/-- The value of lane `k` of `c`, through its bytes. -/
theorem toNat_lane (c : BitVec 64) (k b : Nat) :
    (c.extractLsb' (k * (8 * b)) (8 * b)).toNat = c.toNat / 256 ^ (k * b) % 256 ^ b := by
  have h₁ : (2 : Nat) ^ (k * (8 * b)) = 256 ^ (k * b) := by
    rw [show k * (8 * b) = 8 * (k * b) by ring, Nat.pow_mul]
  have h₂ : (2 : Nat) ^ (8 * b) = 256 ^ b := by rw [Nat.pow_mul]
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow, h₁, h₂]

variable {H : Type} {hn : H → String}

/-- Lane `l` of a widening load lies inside the loaded 8 bytes. -/
theorem lane_bound {b M l : Nat} (hbM : b * M = 8) (hl : l < M) : l * b + b ≤ 8 := by
  have h : (l + 1) * b ≤ M * b := Nat.mul_le_mul_right b hl
  rw [Nat.mul_comm M b, hbM, Nat.succ_mul] at h
  exact h

theorem mul8_div8 (l b : Nat) : l * (8 * b) / 8 = l * b := by
  rw [Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by decide)]

/-- **A widening load in bounds, forward**, at the integer shape `s2` of the widened lanes
(`K = 8 * b`, lane width `2 * K`, `b * M = 8`): from a typed state image, it is a `Step_read`
step to Core's `extendLanes`, in both readings, at `withVBytes (Prims.builtins …)`. -/
theorem fwd_vecLoadPack_shape {P : Numerics.Profile} {host : HostSemantics H} (s2 : IntShape)
    (b : Nat) (hK2 : s2.laneWidth = 2 * (8 * b)) (hbM : b * s2.lanes = 8) (sx : Signedness)
    {st : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {c : BitVec 64}
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn st f))
    (hm : st.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) 8 = some c) :
    SRead (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), vloadV (some (.case "SHAPE%X%_%" (.tuple [pctV (8 * b),
          pctV s2.lanes, Vec.sxV sx]))) x.toNat arg])
      [adminToV (.plain (.vecConst (extendLanes (8 * b) s2.lanes sx c)))] ∧
      Round6.Reading.SReadB (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), vloadV (some (.case "SHAPE%X%_%" (.tuple [pctV (8 * b),
          pctV s2.lanes, Vec.sxV sx]))) x.toNat arg])
        [adminToV (.plain (.vecConst (extendLanes (8 * b) s2.lanes sx c)))] := by
  obtain ⟨hle, hb⟩ := FwdMem.load_bytesV hl
  let js := (List.range s2.lanes).map fun k => pctV (c.extractLsb' (k * (8 * b)) (8 * b)).toNat
  have hrow : ∀ l (hl : l < js.length), ∃ kr, js[l] = pctV kr ∧
      SliceAt (bytesV mi.bytes) (i.toNat + arg.offset.val + l * (8 * b) / 8) (8 * b / 8) ∧
      leBytesV (8 * b / 8) kr = ((bytesV mi.bytes).drop
        (i.toNat + arg.offset.val + l * (8 * b) / 8)).take (8 * b / 8) := by
    intro l hl
    have hl' : l < s2.lanes := by simpa [js] using hl
    have hrb := lane_bound hbM hl'
    rw [mul8_div8, Nat.mul_div_cancel_left _ (by decide)]
    refine ⟨(c.extractLsb' (l * (8 * b)) (8 * b)).toNat,
      by simp only [js, List.getElem_map, List.getElem_range], FwdMem.sliceAt_of_or (.inl FwdMem.sliceTotal)
      (by simp only [effAddr] at hle; omega), ?_⟩
    rw [toNat_lane]
    exact leBytesV_lane hb hrb
  have hext : List.Forall₂ (fun v w => Applies (simEnv (withVBytes (Prims.builtins P hn host)))
      "extend__" [.val (natV (8 * b)), .val (natV s2.laneWidth), .val (Vec.sxV sx), .val v] w) js
      ((List.range s2.lanes).map fun k => pctV (packLane (8 * b) sx c k).toNat) := by
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun k _ => ?_))
    rw [hK2]
    cases sx
    · exact applies_extendW floatB_vb _ _ .signed _
    · exact applies_extendW floatB_vb _ _ .unsigned _
  have hinv := applies_invLanes_vb (P := P) (hn := hn) (host := host) (.int s2)
    (extendLanes (8 * b) s2.lanes sx c)
  rw [lanesV_extendLanes s2 hK2 sx c] at hinv
  have hv : adminToV (.plain (.vecConst (extendLanes (8 * b) s2.lanes sx c))) =
      .case "VCONST" (.tuple [caseNilV "V128",
        pctV (extendLanes (8 * b) s2.lanes sx c).toNat]) := rfl
  rw [State.adminToV_aconst, hv]
  exact sread_of_fires loadTags_noCast (lhsIn_vload _ _ _ _ _ _)
    (fires_vloadPackVal (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _) bytesFuns_vb
      s2 (Dvd.intro b rfl) (by rw [hK2]; ring) (by simp [js])
      (fun v hv => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hv
        exact ⟨_, rfl, BitVec.isLt _⟩)
      hrow hext hinv (BitVec.isLt _) hz x.value.isLt (memAt_of_mem? hn hm)
      (FwdMem.memInstV_BYTES' mi))

/-- **`MemoryStep.vecLoadVal` at the three widening loads, forward**, in Core's terms: from a
typed state image, an in-bounds `v128.load8x8_sx`/`16x4_sx`/`32x2_sx` is a `Step_read` step to
Core's result, in both readings, at `withVBytes (Prims.builtins …)`. -/
theorem fwd_vecLoadPack {P : Numerics.Profile} {host : HostSemantics H} {op : VecLoadOp}
    (hop : ∃ sx, op = .extend8x8 sx ∨ op = .extend16x4 sx ∨ op = .extend32x2 sx)
    {st : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {c : BitVec (8 * (op.accessWidth / 8))}
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn st f))
    (hm : st.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg)
      (op.accessWidth / 8) = some c) :
    SRead (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)])
      [adminToV (.plain (.vecConst (vecLoadResult op c)))] ∧
      Round6.Reading.SReadB (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)])
        [adminToV (.plain (.vecConst (vecLoadResult op c)))] := by
  rw [instrToVM_vecLoad]
  have hw : op.accessWidth / 8 = 8 := by
    obtain ⟨sx, rfl | rfl | rfl⟩ := hop <;> simp [VecLoadOp.accessWidth]
  revert c hl
  rw [hw]
  intro c hl
  obtain ⟨sx, rfl | rfl | rfl⟩ := hop
  · exact fwd_vecLoadPack_shape .i16x8 1 rfl rfl sx hz hm hl
  · exact fwd_vecLoadPack_shape .i32x4 2 rfl rfl sx hz hm hl
  · exact fwd_vecLoadPack_shape .i64x2 4 rfl rfl sx hz hm hl

/-- **A widening load in bounds as a `Step` step**, in both readings. -/
theorem stepFwd_vecLoadPack {P : Numerics.Profile} {host : HostSemantics H} {op : VecLoadOp}
    (hop : ∃ sx, op = .extend8x8 sx ∨ op = .extend16x4 sx ∨ op = .extend32x2 sx)
    {st : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {c : BitVec (8 * (op.accessWidth / 8))}
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn st f))
    (hm : st.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg)
      (op.accessWidth / 8) = some c) :
    SStep (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn st f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)])
        (cfgV (stateV hn st f) [adminToV (.plain (.vecConst (vecLoadResult op c)))]) ∧
      (Round6.Int.backend).step (withVBytes (Prims.builtins P hn host)) (cfgV (stateV hn st f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)])
        (cfgV (stateV hn st f) [adminToV (.plain (.vecConst (vecLoadResult op c)))]) :=
  step_of_read hz (typedV_vloadLhs a i op x arg) (typedV_vconstRhs _)
    (fwd_vecLoadPack hop hz hm hl)

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
