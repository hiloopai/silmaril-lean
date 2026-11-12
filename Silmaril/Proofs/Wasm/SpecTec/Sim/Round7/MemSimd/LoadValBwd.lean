module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.VecBound
public import Silmaril.Wasm.SpecTec.Sim.BwdRead.Thms
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Load

/-!
# Round 7, memory SIMD: `v128.load`, in bounds (`Step_read` 43), backward

`Step_read/vload-num-val` quantifies `c : vec_(V128)` and binds it only by the premise
`$vbytes_(V128, c) = $mem(z, x).BYTES[i + ao.OFFSET : 16]`. Read back:

* the slice evaluates only in bounds, so the memory resolves and Core's 16-byte load succeeds
  (`memSlice_inv`, round 5's `Read2.memSlice_inv` for any `B` that does not interpret the state
  accessors);
* `c` is a numeral below `2 ^ 128` (`vec_inv`), so `$vbytes_(V128, c)` is its 16-byte encoding
  (`VBytes`), which is injective there (`Read2.leBytesV_inj`): `c` is Core's loaded vector.

* `bwd_vloadNumVal`: the inversion, for a `B` with `NoAcc` and `VBytes`.
* `bwd_vloadFull`, `bwdB_vloadFull`: in Core's terms, declarative and at round 6's backend
  reading over `withVBytes (Prims.builtins …)`: the result is `VCONST` of Core's loaded vector and
  Core's `vecLoadVal` steps there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)
open FwdMem (bytesV leBytesV)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} {H : Type} {hn : H → String} {F : Value}

/-- **The slice `$mem(z, x).BYTES[i + ao.OFFSET : k]`, read back**, for any `B` that does not
interpret the state accessors: the memory resolves, and the slice is `Value.slice?` of its byte
image at Core's effective address. -/
theorem memSlice_inv (NA : BwdRead.NoAcc B) {ρ : VarEnv} (hρ : ρ.findDef? "mem" = none)
    {s : Store H} {f : Frame} {x : MemIdx} {I : Nat} {arg : MemArg} {ek : Exp} {v : Value}
    (fz : ρ.findVal? "z" = some (stateVF F s f)) (fx : ρ.findVal? "x" = some (idxV x.toNat))
    (fi : ρ.findVal? "i" = some (idxV I)) (fao : ρ.findVal? "ao" = some (memargV arg))
    (h : EvalExp (simEnv B) ρ
      (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")
        (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)) ek) v) :
    ∃ ma mi k, s.mem? f x = some (ma, mi) ∧ EvalExp (simEnv B) ρ ek (.num (.natN k)) ∧
      Value.slice? (.list (bytesV mi.bytes)) (effAddr I arg) k = some v := by
  obtain ⟨W, ea, k, hW, hea, hk, hsl⟩ := evalExp_sliceE_iff.1 h
  obtain ⟨Mv, hMv, hB⟩ := evalExp_dotE_iff.1 hW
  obtain ⟨ma, mi, hm, rfl⟩ := memIdx_invF B NA hρ fz fx hMv
  rw [FwdMem.memInstV_BYTES'] at hB
  obtain rfl := Option.some.inj hB
  have e : Value.num (.natN ea) = .num (.natN (I + arg.offset.val)) :=
    EvalExp.unique hea (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao))
  simp only [Value.num.injEq, Num.natN.injEq] at e
  subst e
  exact ⟨ma, mi, k, hm, hk, hsl⟩

/-- The `VCONST V128 c` right-hand side, at a bound `c = %(n)`. -/
theorem rhs_vconst {ρ : VarEnv} {n : Nat} {w : Value} (fc : ρ.findVal? "c" = some (pctV n))
    (h : EvalExp (simEnv B) ρ
      (.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"])]) w) :
    w = .list [.case "VCONST" (.tuple [caseNilV "V128", pctV n])] :=
  EvalExp.unique h (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons'
    (evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons' evalExp_v128
      (RefsGC.evalExps_cons' (evalExp_var fc) RefsGC.evalExps_nil')))) RefsGC.evalExps_nil'))

/-- **A firing `Step_read` rule at `CONST at i; VLOAD V128 o x ao`, inverted**, with its
quantifier typing: the scope binds `z`, `x`, `i` and `ao` to the operands and evaluates the load's
option to `o`. -/
theorem fires_vload_inv {k : Nat} {nm : IL.Id} {qs : List Param} {eo rh : Exp}
    {prems : List Prem} {s : Store H} {f : Frame} {A : Value} {I n : Nat} {o : Option Value}
    {arg : MemArg} {w : Value}
    (h : Equiv.Validation.HasRuleAt (simEnv B) "Step_read" "%~>%" k (.ruleD nm qs "%~>%"
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "CONST" (.tupE [.subE (.varE "at")
        (.varT "addrtype" []) (.varT "numtype" []), .varE "i"]), .caseE "VLOAD" (.tupE
        [.caseE "V128" (.tupE []), eo, .varE "x", .varE "ao"])]]), rh]) prems))
    (hf : Fires (simEnv B) "Step_read" k
      (.tuple [cfgV (stateVF F s f) [aconstV A I, vloadV o n arg], w])) :
    ∃ σ, QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateVF F s f) ∧
      (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV n) ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I) ∧
      (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg) ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) eo (.opt o) ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B)))
        (otherwise (simEnv B) "Step_read" [] k
          (.tuple [cfgV (stateVF F s f) [aconstV A I, vloadV o n arg], w]))
        (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := State.Fires.rule_eq h hf
  obtain ⟨hz, hc⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  have h₁ := RefsGC.evalExps_cons_inv (RefsGC.elems_of_list hc)
  obtain ⟨ho, fx, fao⟩ := vload_fvs (RefsGC.evalExps_cons_inv h₁.2).1
  exact ⟨σ, hq, evalExp_varE_iff.1 hz, fx, fi_of_aconst h₁.1, fao, ho, RefsGC.rhs_of_concl he,
    hp⟩

/-- **A `K`-byte slice of the memory that is the encoding of `n < 2 ^ (8 * K)`**, read back: the
memory resolves and Core's `K`-byte load reads the word `n`. -/
theorem memSlice_load (NA : BwdRead.NoAcc B) {σ : List (IL.Id × Value)} {s : Store H}
    {f : Frame} {x : MemIdx} {I K n : Nat} {arg : MemArg} {ek : Exp}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateVF F s f))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (hK : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) ek (.num (.natN K)))
    (hn : n < 2 ^ (8 * K))
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")
        (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)) ek) (.list (leBytesV K n))) :
    ∃ (ma : Nat) (mi : MemInst) (c : BitVec (8 * K)), s.mem? f x = some (ma, mi) ∧
      Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr I arg) K = some c ∧ c.toNat = n := by
  obtain ⟨ma, mi, K', hm, hK', hsl⟩ :=
    memSlice_inv NA (Memory.findDef_bindVals_empty σ _) fz fx fi fao h
  have eK : K' = K := by simpa using EvalExp.unique hK' hK
  obtain ⟨c, hl, hcn⟩ := Round5.Read2.load_of_slice (k := K) hn (eK ▸ hsl) rfl
  exact ⟨ma, mi, c, hm, hl, hcn⟩

/-- `$vbytes_(V128, %(n))` under `VBytes`, for `n < 2 ^ 128`: the 16-byte encoding of `n`. -/
theorem vbytes_inv (Vb : VBytes (simEnv B)) {n : Nat} {V : Value} (hlt : n < 2 ^ 128)
    (hA : Applies (simEnv B) "vbytes_" [.val (caseNilV "V128"), .val (pctV n)] V) :
    V = .list (leBytesV 16 n) := by
  have hn' : (BitVec.ofNat 128 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
  have hV := Vb (BitVec.ofNat 128 n)
  rw [hn'] at hV
  exact Applies.unique hA hV

/-- **`Step_read/vload-num-val`, backward** (rule 43), for a `B` that does not interpret the
state accessors and answers `$vbytes_` by Core's encoding: the memory resolves, Core's 16-byte
load succeeds, and the result is `VCONST` of the loaded vector. -/
theorem bwd_vloadNumVal (NA : BwdRead.NoAcc B) (Vb : VBytes (simEnv B)) {s : Store H}
    {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width}
    {w : Value}
    (hf : Fires (simEnv B) "Step_read" 43 (.tuple [cfgV (stateVF F s f)
      [aconstV (Encode.toValue a) i.toNat, vloadV none x.toNat arg], w])) :
    ∃ (ma : Nat) (mi : MemInst) (c : BitVec (8 * 16)), s.mem? f x = some (ma, mi) ∧
      Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) 16 = some c ∧
      w = .list [.case "VCONST" (.tuple [caseNilV "V128", pctV c.toNat])] := by
  obtain ⟨σ, hq, fz, fx, fi, fao, -, hr, hp⟩ :=
    fires_vload_inv (State.hasReadRules_simEnv B).vloadNumVal hf
  -- `c : vec_(V128)` is a numeral below `2 ^ 128`.
  obtain ⟨C, fC, hC⟩ := hq "c" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (by simp)
  obtain ⟨n, rfl, hlt⟩ := vec_inv evalExp_v128 hC
  -- The premise: `$vbytes_(V128, c)` is the slice.
  obtain ⟨V, e₁, e₂⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have hA : Applies (simEnv B) "vbytes_" [.val (caseNilV "V128"), .val (pctV n)] V :=
    (applies_iff_callDef (Memory.findDef_bindVals_empty σ _) (Equiv.evalArgs_cons evalExp_v128
      (Equiv.evalArgs_cons (evalExp_var fC) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 e₁)
  have e₂' : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) _ (.list (leBytesV 16 n)) :=
    vbytes_inv Vb hlt hA ▸ e₂
  obtain ⟨ma, mi, c, hm, hl, hcn⟩ :=
    memSlice_load NA fz fx fi fao (evalExp_vsize8 (B := B) (σ := σ)) hlt e₂'
  exact ⟨ma, mi, c, hm, hl, by rw [rhs_vconst fC hr, hcn]⟩

/-- `withVBytes (Prims.builtins …)` does not interpret the state accessors. -/
theorem noAcc_vb {P : Numerics.Profile} {host : HostSemantics H} :
    BwdRead.NoAcc (withVBytes (Prims.builtins P hn host)) where
  local_ _ := by simp [withVBytes, Prims.builtins, Prims.call, IntNumeric.intCall,
    Floats.floatCall, Floats.floatNames]
  global _ := by simp [withVBytes, Prims.builtins, Prims.call, IntNumeric.intCall,
    Floats.floatCall, Floats.floatNames]
  table _ := by simp [withVBytes, Prims.builtins, Prims.call, IntNumeric.intCall,
    Floats.floatCall, Floats.floatNames]
  mem _ := by simp [withVBytes, Prims.builtins, Prims.call, IntNumeric.intCall,
    Floats.floatCall, Floats.floatNames]
  elem _ := by simp [withVBytes, Prims.builtins, Prims.call, IntNumeric.intCall,
    Floats.floatCall, Floats.floatNames]
  data _ := by simp [withVBytes, Prims.builtins, Prims.call, IntNumeric.intCall,
    Floats.floatCall, Floats.floatNames]

/-- `vecLoadResult .full` keeps the loaded bits. -/
theorem toNat_vecLoadResult_full (c : BitVec (8 * 16)) :
    (vecLoadResult .full c).toNat = c.toNat := by
  rw [vecLoadResult, FwdMem.toNat_setWidth_of_le _ (by decide)]

/-- **`v128.load` in bounds, backward, in Core's terms**: if rule 43 fires at the image of
`v128.load`, the result is the image of Core's loaded vector, and Core's `vecLoadVal` steps
there. -/
theorem bwd_vloadFull (NA : BwdRead.NoAcc B) (Vb : VBytes (simEnv B)) {P : Numerics.Profile}
    {host : HostSemantics H} {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {w : Value}
    (hf : Fires (simEnv B) "Step_read" 43 (.tuple [cfgV (stateVF F s f)
      [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad .full x arg)], w])) :
    ∃ v : BitVec 128, w = .list [adminToV (.plain (.vecConst v))] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad .full x arg)]⟩
        ⟨s, f, [.plain (.vecConst v)]⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecLoad] at hf
  obtain ⟨ma, mi, c, hm, hl, rfl⟩ := bwd_vloadNumVal NA Vb hf
  refine ⟨vecLoadResult .full c, ?_, .memory (.vecLoadVal (op := .full) hm hl)⟩
  rw [show adminToV (.plain (.vecConst (vecLoadResult .full c))) =
    vconstV (vecLoadResult .full c) from rfl, vconstV, toNat_vecLoadResult_full]

/-- **`v128.load` in bounds at round 6's backend reading, backward**, at the concrete primitives
with `$vbytes_` answered. -/
theorem bwdB_vloadFull {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {w : Value}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 43
      (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad .full x arg)], w])) :
    ∃ v : BitVec 128, w = .list [adminToV (.plain (.vecConst v))] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad .full x arg)]⟩
        ⟨s, f, [.plain (.vecConst v)]⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f)
      [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad .full x arg)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoad]; exact lhsIn_vload _ _ _ _ _ _
  exact bwd_vloadFull noAcc_vb (vBytes_withVBytes _)
    ((Round6.Reading.firesB_read_iff _ loadTags_noCast ha).1 hf)

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
