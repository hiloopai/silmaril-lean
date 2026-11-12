module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.Grow
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms
public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Thms
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms

/-!
# Round 5: the in-bounds scalar stores, backward (`Step` 19, 21)

`store-num-val` (19) and `store-pack-val` (21) have no bounds premise: they write
`$with_mem(z, x, i + ao.OFFSET, k, b*)`, whose body updates the slice
`MEMS[…].BYTES[i : k]`. The evaluator's slice update succeeds only when `i + k` is at most the
length of the list (`Value.setSlice`), so a firing rule is in bounds (`withMem_bound`, by inverting
the call, the update and the path). In bounds, Core's `Memory.store` succeeds
(`store_of_le`), the stored bytes `b*` are read back through `$nbytes_`/`$ibytes_` (which `B`
answers with Core's little-endian encoding, `FwdMem.bytesFuns_builtins`), and the written state
is evaluated forward (`FwdMem.evalExp_withMem`) and compared by `EvalExp.unique`. The memory is
resolved by `ReadValid`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.RuntimeBridge (memInstToValue)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open BwdPureStep (fires_step codes_three payload_of_caseE head_of_caseE rhs_nil body_pair
  aconst_of_lhs storePayload head_store intStore_image floatStore_image const_int_of
  const_float_of packWidth_of)
open Round4Int (BI)
open Round4Read (ReadValid idx_last mem_of_isSome)
open FwdMem (bytesV leBytesV)
open State (idxV)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Paths and slices, inverted -/

/-- A slice update through a path, inverted. -/
theorem pathSet_slice_inv {env : Env} {ρ : VarEnv} {v w r : Value} {p : Path} {e₁ e₂ : Exp}
    (h : PathSet env ρ v (.sliceP p e₁ e₂) w r) :
    ∃ u v₁ v₂ i k u', PathGet env ρ v p u ∧ EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧
      v₁.asNat? = some i ∧ v₂.asNat? = some k ∧ u.setSlice i k w = some u' ∧
      PathSet env ρ v p u' r := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [pathSet] at h
  | succ n =>
      simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨u, hu, v₁, hv₁, v₂, hv₂, i, hi, k, hk, u', hu', hr⟩ := h
      exact ⟨u, v₁, v₂, i, k, u', ⟨n, hu⟩, ⟨n, hv₁⟩, ⟨n, hv₂⟩, hi, hk, hu', ⟨n, hr⟩⟩

/-- A successful slice update of a list stays inside it. -/
theorem le_of_setSlice {vs : List Value} {i k : Nat} {w u : Value}
    (h : Value.setSlice (.list vs) i k w = some u) : i + k ≤ vs.length := by
  cases w <;> simp only [Value.setSlice, reduceCtorEq] at h
  by_contra hc
  simp [hc] at h

/-- `B` does not answer `$with_mem`. -/
theorem call_withMem_none (P : Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : (BI P hn host).call "with_mem" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- **A `$with_mem` call that evaluates writes inside the memory**: at a resolved memory, the
start plus the count is at most the memory's size. -/
theorem withMem_bound {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {x : MemIdx}
    {ma : Nat} {mi : MemInst} {ei ej eb : Exp} {W : Value} {i j : Nat} {ws : List Value}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (idxV x.toNat))
    (hm : s.mem? f x = some (ma, mi))
    (hi : EvalExp (simEnv (BI P hn host)) ρ ei (.num (.natN i)))
    (hj : EvalExp (simEnv (BI P hn host)) ρ ej (.num (.natN j)))
    (hb : EvalExp (simEnv (BI P hn host)) ρ eb (.list ws))
    (h : EvalExp (simEnv (BI P hn host)) ρ
      (.callE "with_mem" [.expA (.varE "z"), .expA (.varE "x"), .expA ei, .expA ej, .expA eb]) W) :
    i + j ≤ mi.bytes.size := by
  have D := State.stateDefs_simEnv (BI P hn host)
  obtain ⟨hma, hmi⟩ := Memory.Store.mem?_eq_some hm
  have hbody := BwdPureStep.evalExp_call1_inv (FwdMem.withMemDef_simEnv _)
    (Prims.findDef_none_of_valsOnly hρ _) (call_withMem_none P hn host _)
    (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fx)
      (Equiv.evalArgs_cons hi (Equiv.evalArgs_cons hj (Equiv.evalArgs_cons hb
        Equiv.evalArgs_nil)))))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA
          (State.matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil))))) h
  obtain ⟨W₁, W₂, h₁, -, -⟩ := body_pair hbody
  obtain ⟨S, Wb, hS, -, hps⟩ := evalExp_updE_iff.1 h₁
  have eS : S = storeV hn s := EvalExp.unique hS (State.evalExp_sof D rfl (evalExp_var rfl))
  subst eS
  obtain ⟨u, v₁, v₂, i', k', u', hu, hv₁, hv₂, hi', hk', hsl, -⟩ := pathSet_slice_inv hps
  have e₁ : v₁ = .num (.natN i) := EvalExp.unique hv₁ (evalExp_var rfl)
  have e₂ : v₂ = .num (.natN j) := EvalExp.unique hv₂ (evalExp_var rfl)
  subst e₁ e₂
  simp only [Value.asNat?, Option.some.injEq] at hi' hk'
  subst hi' hk'
  obtain ⟨u₀, hu₀, hB⟩ := BwdPureStep.pathGet_dot_inv hu
  obtain ⟨L, iv, a, hL, hiv, ha, hLa⟩ := BwdPureStep.pathGet_idx_inv hu₀
  obtain ⟨R, hR, hRf⟩ := BwdPureStep.pathGet_dot_inv hL
  have eR := BwdPureStep.pathGet_root_inv hR
  subst eR
  rw [State.storeV_MEMS, Option.some.injEq] at hRf
  subst hRf
  have eiv : iv = .num (.natN ma) := EvalExp.unique hiv (State.evalExp_modAddr D rfl rfl rfl
    (State.frameV_MODULE f) (State.moduleV_MEMS _) (State.getElem?_map_natN hma))
  subst eiv
  simp only [Value.asNat?, Option.some.injEq] at ha
  subst ha
  simp only [Value.idx?, List.getElem?_map, hmi, Option.map_some, Option.some.injEq] at hLa
  subst hLa
  rw [FwdMem.memInstV_BYTES', Option.some.injEq] at hB
  subst hB
  have := le_of_setSlice hsl
  rwa [FwdMem.bytesV_length] at this

/-- In bounds, Core's store succeeds. -/
theorem store_of_le {mem : ByteArray} {i k : Nat} {w : BitVec (8 * k)} (h : i + k ≤ mem.size) :
    ∃ b, Silmaril.Wasm.Execution.Memory.store mem i w = some b :=
  ⟨_, (Silmaril.Wasm.Execution.Memory.writeBytes_eq_some_iff mem _ _ i).2
    ⟨by rw [Silmaril.Wasm.Execution.Memory.encodeLE_size]; exact h, rfl⟩⟩

/-- The `c` operand of a `CONST t c` element of a left-hand side is the image's payload. -/
theorem constC_of_lhs {env : Env} {ρ : VarEnv} {ent : Exp} {a : Admin} {A C : Value}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [ent, .varE "c"])) (adminToV a))
    (ha : adminToV a = .case "CONST" (.tuple [A, C])) : ρ.findVal? "c" = some C := by
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  have eu : u = .tuple [A, C] := (Value.case.inj (he.symm.trans ha)).2
  subst eu
  exact evalExp_varE_iff.1
    (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup hu)).2).1

theorem width8_num (t : NumType) : 8 * (t.width / 8) = t.width := by
  rcases t with t | t
  · exact FwdMem.width8_int t
  · exact FwdMem.width8_float t

/-- **The common part of the two value stores**: a firing `$with_mem(z, x, i + ao.OFFSET, k, b*)`
with `b*` the `k`-byte little-endian encoding of `n`, at a resolved memory, is Core's successful
store of `n`'s `k` bytes, and evaluates to the stored state. -/
theorem withMem_store {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : MemIdx}
    {arg : MemArg} {ma : Nat} {mi : MemInst} {I k : Nat} {w : BitVec (8 * k)} {ej eb : Exp}
    {W : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (hm : s.mem? f x = some (ma, mi))
    (hj : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ) ej (.num (.natN k)))
    (hb : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ) eb
      (.list (leBytesV k w.toNat)))
    (h : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)), .expA ej, .expA eb]) W) :
    ∃ b, Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr I arg) w = some b ∧
      W = stateV hn (s.setMem ma { mi with bytes := b }) f := by
  have hρ := valsOnly_bindVals σ
  have hea := Memory.evalExp_effAddr (env := simEnv (BI P hn host)) (evalExp_var fi)
    (evalExp_var fao)
  have hle := withMem_bound hρ fz fx hm hea hj hb h
  obtain ⟨b, hs⟩ := store_of_le (w := w) (i := effAddr I arg) (by simpa [effAddr] using hle)
  obtain ⟨-, hbv⟩ := FwdMem.store_bytesV hs
  obtain ⟨hma, hmi⟩ := Memory.Store.mem?_eq_some hm
  have hle' : effAddr I arg + k ≤ mi.bytes.size := by simpa [effAddr] using hle
  have hsl : Value.setSlice (.list (bytesV mi.bytes)) (effAddr I arg) k
      (.list (leBytesV k w.toNat)) = some (.list ((bytesV mi.bytes).take (effAddr I arg) ++
        leBytesV k w.toNat ++ (bytesV mi.bytes).drop (effAddr I arg + k))) := by
    simp [Value.setSlice, hle']
  have ew := FwdMem.evalExp_withMem (ez := .varE "z") (ex := .varE "x")
    (State.stateDefs_simEnv _) (FwdMem.withMemDef_simEnv _)
    (Prims.findDef_none_of_valsOnly hρ _) (evalExp_var fz) (evalExp_var fx) hea hj hb
    (State.storeV_MEMS hn s) (State.frameV_MODULE f) (State.moduleV_MEMS _)
    (State.getElem?_map_natN hma) (by simp [hmi]) (FwdMem.memInstV_BYTES' mi) hsl
    (hbv ▸ FwdMem.memInstV_setBytes mi b) (FwdMem.storeV_setMem hn s ma _)
  exact ⟨b, hs, EvalExp.unique h ew⟩

/-- `$nbytes_(nt, c)`, read back at a numeral. -/
theorem nbytes_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {v : NumVal} {V : Value}
    (fnt : ρ.findVal? "nt" = some (Encode.toValue v.type)) (fc : ρ.findVal? "c" = some (numV v))
    (h : EvalExp (simEnv (BI P hn host)) ρ
      (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")]) V) :
    V = .list (leBytesV (v.type.width / 8) v.bits.toNat) :=
  Applies.unique ((applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _)
    (Equiv.evalArgs_cons (evalExp_var fnt) (Equiv.evalArgs_cons (evalExp_var fc)
      Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 h))
    ((FwdMem.bytesFuns_builtins P hn host).nbytes v)

/-- **`store-num-val` at a numeral `v`**: the rule's successor is the image of Core's store of
`v`'s bytes, given the Core step for each successful store. -/
theorem bwd_storeNumVal_at {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : MemIdx}
    {arg : MemArg} {ma : Nat} {mi : MemInst} {I : Nat} {v : NumVal} {W : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (fnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (Encode.toValue v.type))
    (fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV v))
    (hm : s.mem? f x = some (ma, mi))
    (hp : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (State.iterVar "b" "b*")
        (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")])) (.bool true))
    (h : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)),
        .expA (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [.expA (.varE "nt")])
          .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT),
        .expA (State.iterVar "b" "b*")]) W) :
    ∃ b, Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr I arg)
        (count := v.type.width / 8) (v.bits.setWidth _) = some b ∧
      W = stateV hn (s.setMem ma { mi with bytes := b }) f := by
  have hρ := valsOnly_bindVals σ
  obtain ⟨V, e₁, e₂⟩ := Bwd.eq_of_cmp hp
  have eV := nbytes_inv hρ fnt fc e₂
  subst eV
  have hk := FwdMem.evalExp_widthNum (State.growDefs_simEnv (BI P hn host))
    (Memory.sizeDefs_simEnv _) v.type (evalExp_var fnt)
  have ew : (v.bits.setWidth (8 * (v.type.width / 8))).toNat = v.bits.toNat :=
    FwdMem.toNat_setWidth_of_le v.bits (by rw [width8_num])
  exact withMem_store fz fx fi fao hm hk (ew ▸ e₁) h

/-- **`Step/store-num-val` (19) backward, under `ReadValid`.** -/
theorem bwd_storeNumVal {c : Config H} (hv : ReadValid c) {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step" 19 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv _).storeNumVal hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨at_, i, rfl, fi⟩ := aconst_of_lhs hq (.tail _ (.head _)) h₁
  obtain ⟨NT, Pv, X, AO, hNT, hP, fx, fao, he⟩ := storePayload h₃
  have ePv : Pv = .opt none := EvalExp.unique hP (evalExp_optE_none_iff.2 rfl)
  have hif := RefsGC.premW_if (hp _ (List.mem_singleton_self _))
  obtain ⟨W, hW, rfl⟩ := rhs_nil hr
  rcases head_store (Typing.adminToV_case he).symm with ⟨t, p, m, arg, rfl⟩ | ⟨t, m, arg, rfl⟩
  · obtain ⟨rfl, hp', rfl, rfl⟩ := intStore_image he
    obtain rfl : p = none := by cases p <;> simp_all
    have fnt := evalExp_varE_iff.1 hNT
    obtain ⟨cv, rfl⟩ := const_int_of (evalExp_var fnt) h₂
    obtain ⟨ma, mi, hm⟩ := mem_of_isSome (idx_last (l := [_, _]) hv.idx)
    obtain ⟨b, hs, rfl⟩ := bwd_storeNumVal_at (v := ⟨.int t, cv⟩) fz fx fi fao fnt
      (constC_of_lhs h₂ rfl) hm hif hW
    exact ⟨_, rfl, .memory (.storeIntVal hm hs)⟩
  · obtain ⟨rfl, -, rfl, rfl⟩ := floatStore_image he
    have fnt := evalExp_varE_iff.1 hNT
    obtain ⟨cv, rfl⟩ := const_float_of (evalExp_var fnt) h₂
    obtain ⟨ma, mi, hm⟩ := mem_of_isSome (idx_last (l := [_, _]) hv.idx)
    obtain ⟨b, hs, rfl⟩ := bwd_storeNumVal_at (v := ⟨.float t, cv⟩) fz fx fi fao fnt
      (constC_of_lhs h₂ rfl) hm hif hW
    exact ⟨_, rfl, .memory (.storeFloatVal hm hs)⟩

/-- **`Step/store-pack-val` (21) backward, under `ReadValid`.** -/
theorem bwd_storePackVal {c : Config H} (hv : ReadValid c) {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step" 21 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv _).storePackVal hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨at_, i, rfl, fi⟩ := aconst_of_lhs hq (.tail _ (.head _)) h₁
  obtain ⟨NT, Pv, X, AO, hNT, hP, fx, fao, he⟩ := storePayload h₃
  have hif := RefsGC.premW_if (hp _ (List.mem_singleton_self _))
  obtain ⟨W, hW, rfl⟩ := rhs_nil hr
  have hρ := valsOnly_bindVals σ
  rcases head_store (Typing.adminToV_case he).symm with ⟨t, p, m, arg, rfl⟩ | ⟨t, m, arg, rfl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := intStore_image he
    obtain ⟨q, rfl, fn⟩ := packWidth_of hP
    obtain ⟨cv, rfl⟩ := const_int_of hNT h₂
    have fI := evalExp_varE_iff.1 (evalExp_subE_iff.1 hNT)
    have fc := constC_of_lhs h₂ rfl
    obtain ⟨ma, mi, hm⟩ := mem_of_isSome (idx_last (l := [_, _]) hv.idx)
    -- the premise `b* = $ibytes_(n, $wrap__($size(Inn), n, c))`
    obtain ⟨V, e₁, e₂⟩ := Bwd.eq_of_cmp hif
    have ewr : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
        (.callE "wrap__" [.expA (.callE "size"
          [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))]), .expA (.varE "n"),
          .expA (.varE "c")]) (Equiv.bvV (cv.setWidth q.width)) :=
      evalExp_callE_iff.2 (Floats.callDef_floatPrim (Prims.floatB_builtins hn host)
        (FwdMem.noClauses_wrap _) (Prims.findDef_none_of_valsOnly hρ _)
        (Equiv.evalArgs_cons (FwdMem.evalExp_sizeInn (Prims.findDef_none_of_valsOnly hρ) fI)
          (Equiv.evalArgs_cons (evalExp_var fn) (Equiv.evalArgs_cons (evalExp_var fc)
            Equiv.evalArgs_nil)))
        (Floats.floatCall_wrap P t.width q.width cv))
    have eV : V = .list (leBytesV (q.width / 8) (cv.setWidth q.width).toNat) :=
      Applies.unique ((applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _)
        (Equiv.evalArgs_cons (evalExp_var fn) (Equiv.evalArgs_cons ewr Equiv.evalArgs_nil))).2
        (evalExp_callE_iff.1 e₂)) ((FwdMem.bytesFuns_builtins P hn host).ibytes _ _)
    subst eV
    have ew : (cv.setWidth (8 * (q.width / 8))).toNat = (cv.setWidth q.width).toNat := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, FwdMem.width8_pack]
    obtain ⟨b, hs, rfl⟩ := withMem_store (w := cv.setWidth (8 * (q.width / 8))) fz fx fi fao hm
      (Memory.evalExp_div8 (by cases q <;> simp [PackSize.width]) (evalExp_var fn))
      (ew ▸ e₁) hW
    exact ⟨_, rfl, .memory (.storePackVal hm hs)⟩
  · obtain ⟨-, rfl, -, -⟩ := floatStore_image he
    obtain ⟨u, -, hu⟩ := evalExp_optE_some_iff.1 hP
    simp at hu

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
