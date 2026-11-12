module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadPack

/-!
# Round 7, memory SIMD: `v128.loadKxM_sx`, in bounds (`Step_read` 45), backward

`Step_read/vload-pack-val` quantifies `j* : iN(K)*`, `Jnn` and `c` and binds them only by its two
premises: the iterated byte premise `($ibytes_(K, j) = $mem(z, x).BYTES[i + ao.OFFSET + k * K/8 :
K/8])^(k<M)` and `c = $inv_lanes_(Jnn X M, $extend__(K, $jsizenn(Jnn), sx, j)^M) ∧
$jsizenn(Jnn) = K * 2`. Read back at `withVBytes (Prims.builtins …)`:

* the iterated premise has one row per lane (`premW_iterListN1_inv`, inverting
  `PremW.iterListN` over one domain with an index variable), and each row's slice evaluates only
  in bounds (`memSliceAt_inv`), so lane `l` of `j*` is the `K/8`-byte word at `l * K/8`
  (`packRow_inv`);
* the last lane ends 8 bytes past the effective address, so Core's 8-byte load succeeds, and
  lane `l` of the loaded word is lane `l` of `j*` (`leBytesV_lane`, `Read2.leBytesV_inj`);
* `$jsizenn(Jnn) = K * 2` fixes the width given to `$extend__`, which is then Core's sign or zero
  extension (`applies_extendW`), so the result iteration is the list of Core's widened lanes;
* `$inv_lanes_` answers only at a shape image (`invLanes_inv`); a `%`-numeral lane forces an
  integer shape (`laneV_pct`), whose lane count is `M` and whose lane width is `K * 2`
  (`$jsizenn`), so the pattern is Core's `extendLanes` (`lanesV_extendLanes`,
  `Round5.Simd.lanesV_injective`).

* `bwd_vloadPackVal`: the inversion, at the three widening shapes.
* `bwd_vecLoadPack`, `bwdB_vecLoadPack`: in Core's terms, declarative and at round 6's backend
  reading: the result is `VCONST` of Core's widened vector and Core's `vecLoadVal` steps there.
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
open State (aconstV idxV)
open FwdMem (leBytesV bytesV)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H} {F : Value}

/-! ## Iterated premises over one domain, inverted -/

/-- One domain `x ← y` evaluates to its variable's value. -/
theorem evalDoms_one_inv {env : Env} {n : Nat} {ρ : VarEnv} {x y : IL.Id}
    {xvs : List (IL.Id × Value)} (h : evalDoms n env ρ [.mk x (.varE y)] = .ok xvs) :
    ∃ v, ρ.findVal? y = some v ∧ xvs = [(x, v)] := by
  cases n with
  | zero => simp [evalDoms] at h
  | succ n =>
    simp only [evalDoms, List.mapM_cons, List.mapM_nil, domVar, domSrc] at h
    cases h₁ : evalExp n env ρ (.varE y) with
    | error e => simp [h₁] at h
    | ok v =>
      simp [h₁] at h
      exact ⟨v, evalExp_varE_iff.1 ⟨n, h₁⟩, h.symm⟩

/-- **An iterated premise `pr^(idx<k)` over one domain `x ← y`, inverted**: the domain has `k`
elements and every round holds under that round's bindings. -/
theorem premW_iterListN1_inv {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {eₙ : Exp} {x y idx : IL.Id} {vs : List Value} {k : Nat}
    (hy : ρ.findVal? y = some (.list vs)) (hn : EvalExp env ρ eₙ (.num (.natN k)))
    (h : PremW env D els ρ (.iterPr pr (.mk (.listN eₙ (some idx)) [.mk x (.varE y)]))) :
    vs.length = k ∧ ∀ i (hi : i < vs.length),
      PremW env D els (ρ.bindVals [(x, vs[i]), (idx, .num (.natN i))]) pr := by
  cases h with
  | iterList hit => rcases hit with h | ⟨h, -⟩ <;> cases h
  | iterListN hd he hk hl hlen hr =>
    obtain ⟨d, hd⟩ := hd
    obtain ⟨v, hv, rfl⟩ := evalDoms_one_inv hd
    obtain rfl : v = .list vs := Option.some.inj (hv.symm.trans hy)
    obtain rfl := EvalExp.unique he hn
    simp only [Value.asNat?, Option.some.injEq] at hk
    subst hk
    obtain rfl : _ = [(x, vs)] := by simpa [domLists, Value.asList?] using hl.symm
    have hlen' : vs.length = k := hlen _ List.mem_cons_self
    refine ⟨hlen', fun i hi => ?_⟩
    have hrow : iterRow [(x, vs)] (some idx) i = [(x, vs[i]), (idx, .num (.natN i))] := by
      simp [iterRow, List.getElem?_eq_getElem hi]
    rw [← hrow]
    exact hr _ (by simp only [iterRows, List.mem_map, List.mem_range]; exact ⟨i, hlen' ▸ hi, rfl⟩)

/-- Two later bindings, looked up. -/
theorem findVal?_bindVals₂ (ρ : VarEnv) {x₁ x₂ y : IL.Id} (v₁ v₂ : Value) (h₁ : x₁ ≠ "_")
    (h₂ : x₂ ≠ "_") :
    (ρ.bindVals [(x₁, v₁), (x₂, v₂)]).findVal? y =
      if x₂ = y then some v₂ else if x₁ = y then some v₁ else ρ.findVal? y := by
  simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, Map.find?, h₁, h₂]

/-- One later binding, looked up. -/
theorem findVal?_bindVals₁ (ρ : VarEnv) {x y : IL.Id} (v : Value) (h : x ≠ "_") :
    (ρ.bindVals [(x, v)]).findVal? y = if x = y then some v else ρ.findVal? y := by
  simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, h]

/-! ## The slice at an offset, read back -/

/-- **The slice `$mem(z, x).BYTES[e : k]`, read back** at any start expression `e` with a known
value, for a `B` that does not interpret the state accessors. -/
theorem memSliceAt_inv {B : Builtins} (NA : BwdRead.NoAcc B) {ρ : VarEnv}
    (hρ : ρ.findDef? "mem" = none) {s : Store H} {f : Frame} {x : MemIdx} {es ek : Exp}
    {ea : Nat} {v : Value}
    (fz : ρ.findVal? "z" = some (stateVF F s f)) (fx : ρ.findVal? "x" = some (idxV x.toNat))
    (hs : EvalExp (simEnv B) ρ es (.num (.natN ea)))
    (h : EvalExp (simEnv B) ρ
      (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES") es ek) v) :
    ∃ ma mi k, s.mem? f x = some (ma, mi) ∧ EvalExp (simEnv B) ρ ek (.num (.natN k)) ∧
      Value.slice? (.list (bytesV mi.bytes)) ea k = some v := by
  obtain ⟨W, ea', k, hW, hea, hk, hsl⟩ := evalExp_sliceE_iff.1 h
  obtain ⟨Mv, hMv, hB⟩ := evalExp_dotE_iff.1 hW
  obtain ⟨ma, mi, hm, rfl⟩ := memIdx_invF B NA hρ fz fx hMv
  rw [FwdMem.memInstV_BYTES'] at hB
  obtain rfl := Option.some.inj hB
  have e : Value.num (.natN ea') = .num (.natN ea) := EvalExp.unique hea hs
  simp only [Value.num.injEq, Num.natN.injEq] at e
  subst e
  exact ⟨ma, mi, k, hm, hk, hsl⟩

/-- A slice of a list value, unfolded. -/
theorem slice?_list_inv {vs : List Value} {i n : Nat} {v : Value}
    (h : Value.slice? (.list vs) i n = some v) :
    i + n ≤ vs.length ∧ v = .list ((vs.drop i).take n) := by
  simp only [Value.slice?] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · cases h

/-! ## One row of the byte premise -/

/-- The scope of one row: lookups other than `j` and `k` are the rule's. -/
theorem rowFind {σ : List (IL.Id × Value)} {v : Value} {l : Nat} {y : IL.Id} (hj : y ≠ "j")
    (hk : y ≠ "k") :
    ((VarEnv.empty.bindVals σ).bindVals [("j", v), ("k", .num (.natN l))]).findVal? y =
      (VarEnv.empty.bindVals σ).findVal? y := by
  rw [findVal?_bindVals₂ _ _ _ (by decide) (by decide)]
  simp [Ne.symm hj, Ne.symm hk]

/-- **One row of rule 45's byte premise, read back** at the concrete primitives: the row's lane
is a word `kr` below `2 ^ (8 * b)`, the memory resolves, and the `b` bytes at `l * b` past the
effective address are `kr`'s encoding. -/
theorem packRow_inv {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : MemIdx} {I b l : Nat}
    {arg : MemArg} {v : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateVF F s f))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (fK : (VarEnv.empty.bindVals σ).findVal? "K" = some (.num (.natN (8 * b))))
    (h : EvalExp (simEnv (withVBytes (Prims.builtins P hn host)))
      ((VarEnv.empty.bindVals σ).bindVals [("j", v), ("k", .num (.natN l))]) packBytesPrem
      (.bool true)) :
    ∃ kr ma mi, v = pctV kr ∧ s.mem? f x = some (ma, mi) ∧
      Value.slice? (.list (bytesV mi.bytes)) (effAddr I arg + l * b) b =
        some (.list (leBytesV b kr)) := by
  have hρ : ValsOnly ((VarEnv.empty.bindVals σ).bindVals [("j", v), ("k", .num (.natN l))]) :=
    ⟨rfl, rfl, rfl⟩
  have fK' : ((VarEnv.empty.bindVals σ).bindVals [("j", v), ("k", .num (.natN l))]).findVal? "K" =
      some (.num (.natN (8 * b))) := (rowFind (by decide) (by decide)).trans fK
  have fj : ((VarEnv.empty.bindVals σ).bindVals [("j", v), ("k", .num (.natN l))]).findVal? "j" =
      some v := by rw [findVal?_bindVals₂ _ _ _ (by decide) (by decide)]; simp
  have fk : ((VarEnv.empty.bindVals σ).bindVals [("j", v), ("k", .num (.natN l))]).findVal? "k" =
      some (.num (.natN l)) := by rw [findVal?_bindVals₂ _ _ _ (by decide) (by decide)]; simp
  obtain ⟨V, e₁, e₂⟩ := Bwd.eq_of_cmp h
  obtain ⟨vN, vJ, eN, eJ, hA⟩ := applies_of_call2 hρ e₁
  have hvN : vN = .num (.natN (8 * b)) := EvalExp.unique eN (evalExp_var fK')
  obtain ⟨kr, hkr, hV⟩ : ∃ kr, vJ = pctV kr ∧ V = .list (leBytesV (8 * b / 8) kr) :=
    ibytes_inv_vb _ vJ V (hvN ▸ hA)
  have hvJ : v = pctV kr := (EvalExp.unique (evalExp_var fj) eJ).trans hkr
  have eStart : EvalExp (simEnv (withVBytes (Prims.builtins P hn host)))
      ((VarEnv.empty.bindVals σ).bindVals [("j", v), ("k", .num (.natN l))])
      (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT)
        (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.binE .mulOp (.numT .natT) (.varE "k")
          (.varE "K")) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.num (.natN (I + arg.offset.val + l * (8 * b) / 8))) :=
    RefsGC.evalExp_addNat (Memory.evalExp_effAddr
      (evalExp_var ((rowFind (by decide) (by decide)).trans fi))
      (evalExp_var ((rowFind (by decide) (by decide)).trans fao)))
      (evalExp_div8' (Dvd.dvd.mul_left (Dvd.intro b rfl) l) (RefsGC.evalExp_mulNat
        (evalExp_var fk) (evalExp_var fK')))
  obtain ⟨ma, mi, k', hm, hk', hsl⟩ := memSliceAt_inv noAcc_vb
    (by rw [bindVals_bindVals]; exact Memory.findDef_bindVals_empty _ _)
    ((rowFind (by decide) (by decide)).trans fz) ((rowFind (by decide) (by decide)).trans fx)
    eStart e₂
  have ek : Value.num (.natN k') = .num (.natN (8 * b / 8)) :=
    EvalExp.unique hk' (evalExp_div8' (Dvd.intro b rfl) (evalExp_var fK'))
  have hk'b : k' = b := by
    simpa only [Value.num.injEq, Num.natN.injEq, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
      using ek
  have hsl' : Value.slice? (.list (bytesV mi.bytes)) (effAddr I arg + l * b) b =
      some (.list (leBytesV b kr)) := by
    have h₁ := hsl
    rw [mul8_div8, hk'b, hV, Nat.mul_div_cancel_left _ (by decide : 0 < 8)] at h₁
    exact h₁
  exact ⟨kr, ma, mi, hvJ, hm, hsl'⟩

/-! ## The lanes, assembled -/

/-- `SHAPE (%(K)) M sx` inside an option binds `K`, `M` and `sx`. -/
theorem optShape_inv {env : Env} {ρ : VarEnv} {K M : Nat} {sxv : Value}
    (h : EvalExp env ρ (.optE (some (.caseE "SHAPE%X%_%" (.tupE [.caseE "%" (.tupE [.varE "K"]),
      .varE "M", .varE "sx"]))))
      (.opt (some (.case "SHAPE%X%_%" (.tuple [pctV K, pctV M, sxv]))))) :
    ρ.findVal? "K" = some (.num (.natN K)) ∧ ρ.findVal? "M" = some (pctV M) ∧
      ρ.findVal? "sx" = some sxv := by
  obtain ⟨u, hu, he⟩ := evalExp_optE_some_iff.1 h
  have hu' : u = .case "SHAPE%X%_%" (.tuple [pctV K, pctV M, sxv]) := by simpa using he.symm
  subst hu'
  obtain ⟨h₁, h₂⟩ := RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv hu))
  obtain ⟨h₂, h₃⟩ := RefsGC.evalExps_cons_inv h₂
  obtain ⟨h₃, -⟩ := RefsGC.evalExps_cons_inv h₃
  exact ⟨evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
    (RefsGC.case_inv h₁))).1, evalExp_varE_iff.1 h₂, evalExp_varE_iff.1 h₃⟩

/-- **The rows, assembled into Core's load**: if lane `l < M` of `js` is a word below `2 ^ (8 * b)`
encoded by the `b` bytes at `ea + l * b`, with `b * M = 8`, then Core's 8-byte load at `ea`
succeeds and `js` are the `8 * b`-bit lanes of the loaded word. -/
theorem load_of_packRows {mi : MemInst} {ea b M : Nat} {js : List Value} (hbM : b * M = 8)
    (hM : 0 < M) (hlen : js.length = M)
    (hrow : ∀ l (hl : l < js.length), ∃ kr, js[l] = pctV kr ∧ kr < 2 ^ (8 * b) ∧
      Value.slice? (.list (bytesV mi.bytes)) (ea + l * b) b = some (.list (leBytesV b kr))) :
    ∃ c : BitVec 64, Silmaril.Wasm.Execution.Memory.load mi.bytes ea 8 = some c ∧
      js = (List.range M).map fun l => pctV (c.extractLsb' (l * (8 * b)) (8 * b)).toNat := by
  obtain ⟨kr, -, -, hsl⟩ := hrow (M - 1) (by omega)
  obtain ⟨hle, -⟩ := slice?_list_inv hsl
  rw [FwdMem.bytesV_length] at hle
  have hlast : (M - 1) * b + b = 8 := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hM, Nat.mul_comm, hbM]
  obtain ⟨c, hc⟩ := Round5.Read2.load_some (mem := mi.bytes) (i := ea) (k := 8) (by omega)
  refine ⟨c, hc, ?_⟩
  have hcb := (FwdMem.load_bytesV hc).2
  apply List.ext_getElem (by simp [hlen])
  intro l h₁ h₂
  obtain ⟨kr, hj, hkr, hsl⟩ := hrow l h₁
  have hl : l < M := hlen ▸ h₁
  obtain ⟨-, hv⟩ := slice?_list_inv hsl
  have hlane := (leBytesV_lane hcb (lane_bound hbM hl)).trans (Value.list.inj hv).symm
  have hp : (2 : Nat) ^ (8 * b) = 256 ^ b := by rw [Nat.pow_mul]
  have e := Round5.Read2.leBytesV_inj (Nat.mod_lt _ (Nat.pow_pos (by decide)))
    (hp ▸ hkr) hlane
  simp only [List.getElem_map, List.getElem_range, hj, toNat_lane, e]

/-- One round of rule 45's result iteration, at a known `$jsizenn(Jnn)`. -/
theorem evalExp_packExtendJ {B : Builtins} {σ : List (IL.Id × Value)} {K N' : Nat}
    {Jv sx v w : Value}
    (fK : (VarEnv.empty.bindVals σ).findVal? "K" = some (.num (.natN K)))
    (fJ : (VarEnv.empty.bindVals σ).findVal? "Jnn" = some Jv)
    (fsx : (VarEnv.empty.bindVals σ).findVal? "sx" = some sx)
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some v)
    (hJ : Applies (simEnv B) "jsizenn" [.val Jv] (natV N'))
    (h : Applies (simEnv B) "extend__" [.val (natV K), .val (natV N'), .val sx, .val v] w) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ) packExtendE w :=
  FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var fK) (evalArgs_cons
    (FwdMem.evalExp_call_applies (evalArgs_cons (evalExp_var fJ) evalArgs_nil) hJ)
      (evalArgs_cons (evalExp_var fsx) (evalArgs_cons (evalExp_var fj) evalArgs_nil)))) h

/-- The scope of one result round: lookups other than `j` are the rule's. -/
theorem roundFind {σ : List (IL.Id × Value)} {v : Value} {y : IL.Id} (hj : y ≠ "j") :
    (VarEnv.empty.bindVals (σ ++ [("j", v)])).findVal? y =
      (VarEnv.empty.bindVals σ).findVal? y := by
  rw [← bindVals_bindVals, findVal?_bindVals₁ _ _ (by decide)]
  simp [Ne.symm hj]

/-! ## The rule, backward -/

/-- **`Step_read/vload-pack-val`, backward** (rule 45), at the concrete primitives with
`$vbytes_` answered, at the integer shape `s2` of the widened lanes (`K = 8 * b`, lane width
`2 * K`, `b * M = 8`): the memory resolves, Core's 8-byte load succeeds, and the result is
`VCONST` of Core's `extendLanes`. -/
theorem bwd_vloadPackVal (s2 : IntShape) (b : Nat) (hK2 : s2.laneWidth = 2 * (8 * b))
    (hbM : b * s2.lanes = 8) (sx : Signedness) {s : Store H} {f : Frame} {x : MemIdx}
    {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {w : Value}
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 45
      (.tuple [cfgV (stateVF F s f) [aconstV (Encode.toValue a) i.toNat,
        vloadV (some (.case "SHAPE%X%_%" (.tuple [pctV (8 * b), pctV s2.lanes, Vec.sxV sx])))
          x.toNat arg], w])) :
    ∃ (ma : Nat) (mi : MemInst) (c : BitVec 64), s.mem? f x = some (ma, mi) ∧
      Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) 8 = some c ∧
      w = .list [.case "VCONST" (.tuple [caseNilV "V128",
        pctV (extendLanes (8 * b) s2.lanes sx c).toNat])] := by
  obtain ⟨σ, hq, fz, fx, fi, fao, ho, hr, hp⟩ :=
    fires_vload_inv (State.hasReadRules_simEnv _).vloadPackVal hf
  obtain ⟨fK, fM, fsx⟩ := optShape_inv ho
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hM : 0 < s2.lanes := by cases s2 <;> decide
  -- `j* : iN(K)*`, one row of the byte premise per lane.
  obtain ⟨J, fJs, hJ⟩ := hq "j*" (.iterT (.varT "iN" [.expA (.varE "K")]) .list) (by simp)
  obtain ⟨js, rfl, hjs⟩ := hasTyp_iterT_list_iff.1 hJ
  obtain ⟨hlen, hrows⟩ := premW_iterListN1_inv fJs (RefsGC.evalExp_unpct (evalExp_var fM))
    (hp _ List.mem_cons_self)
  obtain ⟨-, ma, mi, -, hm, -⟩ := packRow_inv fz fx fi fao fK
    (RefsGC.premW_if (hrows 0 (hlen ▸ hM)))
  have hrow : ∀ l (hl : l < js.length), ∃ kr, js[l] = pctV kr ∧ kr < 2 ^ (8 * b) ∧
      Value.slice? (.list (bytesV mi.bytes)) (effAddr i.toNat arg + l * b) b =
        some (.list (leBytesV b kr)) := by
    intro l hl
    obtain ⟨kr, ma', mi', hj, hm', hsl⟩ := packRow_inv fz fx fi fao fK
      (RefsGC.premW_if (hrows l hl))
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj (hm.symm.trans hm'))
    obtain ⟨k', hk', hlt⟩ := iN_inv_lt (evalExp_var fK)
      (hasTypList_iff.1 hjs _ (List.getElem_mem hl))
    obtain rfl : kr = k' := Round5.Read2.pctV_inj (hj.symm.trans hk')
    exact ⟨kr, hj, hlt, hsl⟩
  obtain ⟨c, hl, rfl⟩ := load_of_packRows hbM hM hlen hrow
  -- `$jsizenn(Jnn) = K * 2`.
  obtain ⟨p₁, p₂⟩ := Round5.Read2.and_true_inv
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  obtain ⟨JS, eJS, eK2⟩ := Bwd.eq_of_cmp p₂
  obtain rfl : JS = natV (8 * b * 2) :=
    EvalExp.unique eK2 (RefsGC.evalExp_mulNat (evalExp_var fK) RefsGC.evalExp_num')
  obtain ⟨Jv, fJ, -⟩ := hq "Jnn" (.varT "Jnn" []) (by simp)
  have hJS : Applies (simEnv (withVBytes (Prims.builtins P hn host))) "jsizenn" [.val Jv]
      (natV (2 * (8 * b))) := by
    rw [show 2 * (8 * b) = 8 * b * 2 by ring]
    exact (applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _)
      (evalArgs_cons (evalExp_var fJ) evalArgs_nil)).2 (evalExp_callE_iff.1 eJS)
  -- `c = $inv_lanes_(Jnn X M, $extend__(K, $jsizenn(Jnn), sx, j)^M)`.
  obtain ⟨C, eC, eInv⟩ := Bwd.eq_of_cmp p₁
  obtain ⟨v₁, v₂, e₁, e₂, hA⟩ := applies_of_call2 hρ eInv
  obtain ⟨sh, v, rfl, rfl, rfl⟩ := invLanes_inv hA
  have eIt : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) (VarEnv.empty.bindVals σ)
      (.iterE packExtendE (.mk (.listN (.projE (.uncaseE (.varE "M") "%") 0) none)
        [.mk "j" (.varE "j*")]))
      (.list ((List.range s2.lanes).map fun l => pctV (packLane (8 * b) sx c l).toNat)) := by
    refine evalExp_iterListN1 fJs (RefsGC.evalExp_unpct (evalExp_var fM)) hlen
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        (List.forall₂_same.2 fun l _ => ?_)))
    have fj : (VarEnv.empty.bindVals (σ ++ [("j", pctV (c.extractLsb' (l * (8 * b))
        (8 * b)).toNat)])).findVal? "j" =
        some (pctV (c.extractLsb' (l * (8 * b)) (8 * b)).toNat) := by
      rw [← bindVals_bindVals, findVal?_bindVals₁ _ _ (by decide)]
      simp
    rw [bindVals_bindVals]
    refine evalExp_packExtendJ ((roundFind (by decide)).trans fK) ((roundFind (by decide)).trans fJ)
      ((roundFind (by decide)).trans fsx) fj hJS ?_
    cases sx
    · exact applies_extendW floatB_vb _ _ .signed _
    · exact applies_extendW floatB_vb _ _ .unsigned _
  have hlv := Value.list.inj (EvalExp.unique e₂ eIt)
  -- The shape is the integer shape of the widened lanes.
  obtain ⟨s', rfl⟩ : ∃ s' : IntShape, sh = .int s' := by
    have h0 := congrArg (·[0]?) hlv
    simp only [Round5.Simd.lanesV, List.getElem?_map, List.getElem?_range hM] at h0
    obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h0
    exact laneV_pct hy
  obtain ⟨Jv', Mv, eJ, eM, hsh⟩ : ∃ Jv' Mv, (VarEnv.empty.bindVals σ).findVal? "Jnn" = some Jv' ∧
      (VarEnv.empty.bindVals σ).findVal? "M" = some Mv ∧
      Vec.shapeV (.int s') = .case "%X%" (.tuple [Jv', Mv]) := by
    obtain ⟨u, hu, hv⟩ := evalExp_caseE_iff.1 e₁
    obtain ⟨Jv', Mv, rfl, hJ, hM⟩ := Vec.inv_tup2 hu
    exact ⟨Jv', Mv, evalExp_varE_iff.1 (evalExp_subE_iff.1 hJ), evalExp_varE_iff.1 hM, hv⟩
  have hJM : Vec.laneTypeV (.int s') = Jv' ∧ pctV (Shape.int s').lanes = Mv := by
    simpa using (Vec.shapeV_eq _).symm.trans hsh
  obtain rfl : Jv' = Jv := Option.some.inj (eJ.symm.trans fJ)
  have hlanes : s'.lanes = s2.lanes :=
    Round5.Read2.pctV_inj (hJM.2.trans (Option.some.inj (eM.symm.trans fM)))
  have hwid : s'.laneWidth = 2 * (8 * b) := by
    rw [← hJM.1] at hJS
    have h := Applies.unique (Round5.Simd.applies_jsizenn s') hJS
    simpa [natV] using h
  have hv : v = extendLanes (8 * b) s2.lanes sx c := by
    apply Round5.Simd.lanesV_injective (.int s')
    rw [hlv, ← hlanes, lanesV_extendLanes s' hwid sx c]
  refine ⟨ma, mi, c, hm, hl, ?_⟩
  rw [rhs_vconst (evalExp_varE_iff.1 eC) hr, hv]

/-- Core's `vecLoadVal` at an operator reading 8 bytes, for a word given at width 64. -/
theorem step_vecLoadVal8 {op : VecLoadOp} (hw : op.accessWidth / 8 = 8) {s : Store H} {f : Frame}
    {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {ma : Nat}
    {mi : MemInst} {c : BitVec 64} (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) 8 = some c) :
    Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩
      ⟨s, f, [.plain (.vecConst (vecLoadResult op c))]⟩ := by
  have key : ∀ (k : Nat), op.accessWidth / 8 = k → ∀ c : BitVec (8 * k),
      Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) k = some c →
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩
        ⟨s, f, [.plain (.vecConst (vecLoadResult op c))]⟩ := by
    intro k hk c hl
    subst hk
    exact .memory (.vecLoadVal hm hl)
  exact key 8 hw c hl

/-- **A widening load in bounds, backward, in Core's terms**: if rule 45 fires at the image of
`v128.load8x8_sx`, `16x4_sx` or `32x2_sx`, the result is the image of Core's widened vector, and
Core's `vecLoadVal` steps there. -/
theorem bwd_vecLoadPack {op : VecLoadOp}
    (hop : ∃ sx, op = .extend8x8 sx ∨ op = .extend16x4 sx ∨ op = .extend32x2 sx)
    {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {w : Value}
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 45
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    ∃ v : BitVec 128, w = .list [adminToV (.plain (.vecConst v))] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩
        ⟨s, f, [.plain (.vecConst v)]⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecLoad] at hf
  obtain ⟨sx, rfl | rfl | rfl⟩ := hop
  · obtain ⟨ma, mi, c, hm, hl, rfl⟩ := bwd_vloadPackVal .i16x8 1 rfl rfl sx hf
    exact ⟨_, rfl, step_vecLoadVal8 (op := .extend8x8 sx) (by simp [VecLoadOp.accessWidth]) hm hl⟩
  · obtain ⟨ma, mi, c, hm, hl, rfl⟩ := bwd_vloadPackVal .i32x4 2 rfl rfl sx hf
    exact ⟨_, rfl, step_vecLoadVal8 (op := .extend16x4 sx) (by simp [VecLoadOp.accessWidth]) hm hl⟩
  · obtain ⟨ma, mi, c, hm, hl, rfl⟩ := bwd_vloadPackVal .i64x2 4 rfl rfl sx hf
    exact ⟨_, rfl, step_vecLoadVal8 (op := .extend32x2 sx) (by simp [VecLoadOp.accessWidth]) hm hl⟩

/-- **A widening load in bounds at round 6's backend reading, backward**, at the concrete
primitives with `$vbytes_` answered: the result is the image of Core's widened vector, and Core's
`vecLoadVal` steps there. -/
theorem bwdB_vecLoadPack {op : VecLoadOp}
    (hop : ∃ sx, op = .extend8x8 sx ∨ op = .extend16x4 sx ∨ op = .extend32x2 sx)
    {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {w : Value}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 45
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    ∃ v : BitVec 128, w = .list [adminToV (.plain (.vecConst v))] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩
        ⟨s, f, [.plain (.vecConst v)]⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f)
      [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoad]; exact lhsIn_vload _ _ _ _ _ _
  exact bwd_vecLoadPack hop ((Round6.Reading.firesB_read_iff _ loadTags_noCast ha).1 hf)

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
