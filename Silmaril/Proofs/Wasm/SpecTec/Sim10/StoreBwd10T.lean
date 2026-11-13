module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreVal10T
public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Thms

/-!
# The 1.0 successful stores in `simEnv10T`, backward at `bytesB10`

`Step` 8 (`store-num-val`) and 10 (`store-pack-val`) of the wasm-1.0 script have no bounds
premise. They write `$with_mem(z, 0, i + ao.OFFSET, w/8, b*)`, whose body updates the slice
`MEMS[f.MODULE.MEMS[0]].BYTES[i : w/8]`. The evaluator's slice update succeeds only inside the
list (`Value.setSlice`), so a firing rule is in bounds (`withMem_bound10`, by inverting the call,
the update and the path, as round 5 does for 3.0 in `Round5.BwdStep.withMem_bound`). In bounds,
V1's `writeBytes` succeeds, the stored bytes `b*` are `bytesB10`'s answer to `$bytes_` or
`$ibytes_` (V1's little-endian encoding), and the written state is evaluated forward
(`evalExp_withMem10`) and compared by `EvalExp.unique`.

* `bwd10T_storeNumVal` (rule 8, integer and float) and `bwd10T_storePackVal` (rule 10, a packed
  integer): a firing in `simEnv10T (bytesB10 P)` from the image of a `GoodV1` configuration is
  the image of V1's successful `intStore`/`floatStore`. Every evaluation is moved back to
  `simEnv10` (`evalExp_back`), which needs no typing; the memory exists by `ResOkL10`.
* `bwd10T_store`: the four store rules (7–10) together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress setMemory storeInt storeFloat)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.State (idxPayload iterVar matchExp_iterVar evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame)
open Silmaril.Wasm.SpecTec.Sim20.Whole (div8E iPay offE evalExp_div8 evalExp_addNat20 evalExp_iPay
  width_cases)
open Silmaril.Wasm.SpecTec.Sim10.Whole (sizeTE evalExp_off10 evalExp_size10 packWidth10_cases
  frameMemory_some bytesB10)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-! ## Inverting `$with_mem` -/

/-- A slice update through a path, inverted. -/
theorem pathSet_slice_inv10 {env : Env} {ρ : VarEnv} {v w r : Value} {p : Path} {e₁ e₂ : Exp}
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
theorem le_of_setSlice10 {vs : List Value} {i k : Nat} {w u : Value}
    (h : Value.setSlice (.list vs) i k w = some u) : i + k ≤ vs.length := by
  cases w <;> simp only [Value.setSlice, reduceCtorEq] at h
  by_contra hc
  simp [hc] at h

/-- `bytesB10` does not answer `$with_mem`. -/
theorem bytesB10_withMem (P : Profile) (ws : List ArgV) :
    (bytesB10 P).call "with_mem" ws = none := by
  simp [bytesB10, Sim.Floats.floatIntB, Sim.Floats.floatNames, Sim.IntNumeric.intCall]

/-- A scope of term variables binds no definition. -/
theorem findDef_bindVals10 (σ : List (IL.Id × Value)) (x : IL.Id) :
    (VarEnv.empty.bindVals σ).findDef? x = none :=
  Sim.Prims.findDef_none_of_valsOnly (Sim20.Pure.valsOnly_bindVals σ) x

/-- The memory reached by `MEMS[f.MODULE.MEMS[0]]` from the store, read back. -/
theorem memPath_inv10 {env : Env} {ρ : VarEnv} {s : Store H} {f : Frame}
    {a : Execution.Runtime.MemAddr} {m : MemInst} {u : Value} (hm : frameMemory s f = some (a, m))
    (hidx : EvalExp env ρ (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload)
      (.num (.natN a.value)))
    (hu : PathGet env ρ (storeV hn s) (.dotP (.idxP (.dotP .rootP "MEMS")
      (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload)) "BYTES") u) :
    u = bytesV m.data := by
  obtain ⟨-, hs⟩ := frameMemory_some hm
  obtain ⟨u₀, hu₀, hB⟩ := Sim.BwdPureStep.pathGet_dot_inv hu
  obtain ⟨L, iv, a', hL, hiv, ha, hLa⟩ := Sim.BwdPureStep.pathGet_idx_inv hu₀
  obtain ⟨R, hR, hRf⟩ := Sim.BwdPureStep.pathGet_dot_inv hL
  have eR := Sim.BwdPureStep.pathGet_root_inv hR
  subst eR
  have eiv : iv = .num (.natN a.value) := EvalExp.unique hiv hidx
  subst eiv
  simp only [Value.asNat?, Option.some.injEq] at ha
  subst ha
  have eL : L = .list (s.memories.map memInstV) := by
    simpa [storeV, Value.field?] using hRf.symm
  subst eL
  have eu₀ : u₀ = memInstV m := by
    simpa [Value.idx?, List.getElem?_map, hs] using hLa.symm
  subst eu₀
  simpa [memInstV, Value.field?] using hB.symm

/-- The path `MEMS[f.MODULE.MEMS[0]].BYTES[i : j]`. -/
abbrev bytesSliceP10 : Path :=
  .sliceP (.dotP (.idxP (.dotP .rootP "MEMS")
    (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload)) "BYTES") (.varE "i") (.varE "j")

/-- **A slice update of the frame's memory that succeeds is in bounds.** -/
theorem slice_bound10 {env : Env} {ρ : VarEnv} {s : Store H} {f : Frame}
    {a : Execution.Runtime.MemAddr} {m : MemInst} {i j : Nat} {Wb W : Value}
    (hm : frameMemory s f = some (a, m)) (fi : ρ.findVal? "i" = some (.num (.natN i)))
    (fj : ρ.findVal? "j" = some (.num (.natN j)))
    (hidx : EvalExp env ρ (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload)
      (.num (.natN a.value)))
    (hps : PathSet env ρ (storeV hn s) bytesSliceP10 Wb W) : i + j ≤ m.data.size := by
  obtain ⟨u, v₁, v₂, i', k', u', hu, hv₁, hv₂, hi', hk', hsl, -⟩ := pathSet_slice_inv10 hps
  have e₁ : v₁ = .num (.natN i) := EvalExp.unique hv₁ (Sim.evalExp_var fi)
  have e₂ : v₂ = .num (.natN j) := EvalExp.unique hv₂ (Sim.evalExp_var fj)
  have ei : i' = i := by rw [e₁] at hi'; exact (Option.some.inj hi').symm
  have ek : k' = j := by rw [e₂] at hk'; exact (Option.some.inj hk').symm
  have eu : u = bytesV m.data := memPath_inv10 hm hidx hu
  have hle : i' + k' ≤ (m.data.toList.map fun x => pctV x.toNat).length :=
    le_of_setSlice10 (eu ▸ hsl)
  have hlen : (m.data.toList.map fun x => pctV x.toNat).length = m.data.size := by
    simp [Sim20.Whole.byteArray_toList_length]
  rw [← ei, ← ek, ← hlen]
  exact hle

/-- **A `$with_mem` call that evaluates writes inside the memory** (1.0 encoding): the start
plus the count is at most the size of the frame's memory. -/
theorem withMem_bound10 {B : Builtins} (hwm : ∀ ws, B.call "with_mem" ws = none) {ρ : VarEnv}
    (hρ : ρ.findDef? "with_mem" = none) {ez ex ei ej eb : Exp} {s : Store H} {f : Frame}
    {a : Execution.Runtime.MemAddr} {m : MemInst} {i j : Nat} {ws : List Value} {W : Value}
    (hz : EvalExp (simEnv10 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv10 B) ρ ex (pctV 0))
    (hi : EvalExp (simEnv10 B) ρ ei (.num (.natN i)))
    (hj : EvalExp (simEnv10 B) ρ ej (.num (.natN j)))
    (hb : EvalExp (simEnv10 B) ρ eb (.list ws)) (hm : frameMemory s f = some (a, m))
    (h : EvalExp (simEnv10 B) ρ
      (.callE "with_mem" [.expA ez, .expA ex, .expA ei, .expA ej, .expA eb]) W) :
    i + j ≤ m.data.size := by
  have hbody := Sim.BwdPureStep.evalExp_call1_inv hasClause_withMem10 hρ (hwm _)
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hi (evalArgs_cons hj
      (evalArgs_cons hb evalArgs_nil)))))
    (matchArgs_cons (matchArg_expA Sim20.State.matchExp_state) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
          (matchArg_expA (matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil))))) h
  obtain ⟨W₁, W₂, h₁, -, -⟩ := Sim.BwdPureStep.body_pair hbody
  obtain ⟨S, Wb, hS, -, hps⟩ := evalExp_updE_iff.1 h₁
  have eS : S = storeV hn s := EvalExp.unique hS (Sim.evalExp_var rfl)
  refine slice_bound10 hm rfl rfl ?_ (eS ▸ hps)
  exact evalExp_idxE_iff.2 ⟨_, 0, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
    evalExp_dotE_iff.2 ⟨frameV f, Sim.evalExp_var rfl, rfl⟩, rfl⟩,
    evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, (frameMemory_some hm).1]⟩

/-! ## The `CONST` operand, with its payload -/

/-- A `CONST t c` operand of a left-hand side is a V1 value; `t` evaluates to its type and `c` is
bound to its payload. -/
theorem const_tcc10 {B : Builtins} {ρ : VarEnv} {e : Exp} {a : Admin}
    (h : EvalExp (simEnv10 B) ρ (.caseE "CONST" (.tupE [e, .varE "c"])) (adminToV a)) :
    ∃ v : Execution.Runtime.Value, a = value v ∧ EvalExp (simEnv10 B) ρ e (valTypeV v.type) ∧
      ρ.findVal? "c" = some (numV v) := by
  obtain ⟨u, -, hcu⟩ := evalExp_caseE_iff.1 h
  obtain ⟨v, rfl⟩ := Whole.admin_of_const10 hcu
  have hs := Whole.tup_of_caseE10 h (us := [valTypeV v.type, numV v])
    (by rw [Whole.adminToV_value]; rfl)
  obtain ⟨w, ws, hw, hws, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hs
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  obtain ⟨w', ws', hw', -, he'⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws
  obtain ⟨rfl, -⟩ := List.cons.inj he'
  exact ⟨v, rfl, hw, evalExp_varE_iff.1 hw'⟩

/-! ## The common write -/

/-- **The common part of the two value stores**: a firing `$with_mem(z, 0, i + ao.OFFSET, k, b*)`
with `b*` the bytes `w` at `bytesB10`, at the frame's memory, is V1's successful `writeBytes` of
`w`, and the rule's right-hand side `z'; ε` is the image of the written configuration. -/
theorem withMem_write10 {P : Profile} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {i : BitVec 32} {ao : V1.MemArg} {a : Execution.Runtime.MemAddr} {m : MemInst}
    {w : Execution.Memory.Bytes} {ej eb : Exp} {W : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao))
    (hm : frameMemory s f = some (a, m))
    (hj : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) ej (.num (.natN w.size)))
    (hb : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) eb (bytesV w))
    (h : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA ej, .expA eb], .listE []])) W) :
    ∃ b, Execution.Memory.writeBytes m.data (effectiveAddress i ao) w = some b ∧
      W = configV hn ⟨setMemory s a {m with data := b}, f, []⟩ := by
  have hwm := findDef_bindVals10 σ "with_mem"
  have hea : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) iPay offE) (.num (.natN (effectiveAddress i ao))) :=
    evalExp_addNat20 (evalExp_iPay fi) (evalExp_off10 fa)
  obtain ⟨W₁, W₂, h₁, h₂, rfl⟩ := Sim.BwdPureStep.body_pair h
  have hle := withMem_bound10 (bytesB10_withMem P) hwm (Sim.evalExp_var fz) evalExp_pct0' hea hj
    hb hm h₁
  have hwr : Execution.Memory.writeBytes m.data (effectiveAddress i ao) w =
      some (w.copySlice 0 m.data (effectiveAddress i ao) w.size) := by
    have hle' : effectiveAddress i ao + w.size ≤ m.data.size := by
      simpa [bytesV] using hle
    simp [Execution.Memory.writeBytes, hle']
  refine ⟨_, hwr, ?_⟩
  have e₁ := EvalExp.unique h₁ (evalExp_withMem10 hwm (Sim.evalExp_var fz) evalExp_pct0' hea hj hb
    hm hwr)
  have e₂ : W₂ = .list [] := EvalExp.unique h₂ (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩)
  subst e₁ e₂
  rfl

/-- The right-hand side `z'; ε` of the two write rules, through `$with_mem`, gives V1's step
when V1 writes the same bytes. -/
theorem write_step10 {P : Profile} {host : HostSemantics H} {σ : List (IL.Id × Value)}
    {c : Config H} {s : Store H} {f : Frame} {i : BitVec 32} {ao : V1.MemArg}
    {a : Execution.Runtime.MemAddr} {m : MemInst} {w : Execution.Memory.Bytes} {ej eb : Exp}
    {W : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao))
    (hm : frameMemory s f = some (a, m))
    (hj : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) ej (.num (.natN w.size)))
    (hb : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) eb (bytesV w))
    (h : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA ej, .expA eb], .listE []])) W)
    (hst : ∀ b, Execution.Memory.writeBytes m.data (effectiveAddress i ao) w = some b →
      Step host c ⟨setMemory s a {m with data := b}, f, []⟩) :
    ∃ c', W = configV hn c' ∧ Step host c c' := by
  obtain ⟨b, hw, rfl⟩ := withMem_write10 fz fi fa hm hj hb h
  exact ⟨_, rfl, hst b hw⟩

/-! ## Rule 8 -/

/-- The left-hand side of rule 8, read back. -/
theorem storeNum_lhs10 {B : Builtins} {σ : List (IL.Id × Value)} {code : List Admin}
    (hes : EvalExps (simEnv10 B) (VarEnv.empty.bindVals σ) [Sim20.Whole.constIE,
      .caseE "CONST" (.tupE [.varE "t", .varE "c"]),
      .caseE "STORE" (.tupE [.varE "t", .optE none, .varE "ao"])] (adminsToV code)) :
    ∃ (i : BitVec 32) (ty : V1.ValType) (x : BitVec ty.width) (ao : V1.MemArg) (a₃ : Admin),
      code = [value ⟨.int .i32, i⟩, value ⟨ty, x⟩, a₃] ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) ∧
      (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV ty) ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some (numV ⟨ty, x⟩) ∧
      (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) ∧
      ((∃ t', ty = .int t' ∧ a₃ = .source (.intStore t' none ao)) ∨
        (∃ t', ty = .float t' ∧ a₃ = .source (.floatStore t' ao))) := by
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Whole.codes10_three hes
  obtain ⟨i, rfl, fi⟩ := Whole.constI32_of_lhs10 h₁
  obtain ⟨⟨ty, x⟩, rfl, hty, fc⟩ := const_tcc10 h₂
  obtain ⟨ao, fa, hd⟩ := Whole.storeNum_decode (evalExp_varE_iff.1 hty) h₃
  exact ⟨i, ty, x, ao, a₃, rfl, evalExp_varE_iff.1 fi, evalExp_varE_iff.1 hty, fc, fa, hd⟩

/-- The premise `b* = $bytes_(t, c)` of rule 8, read back at `bytesB10`. -/
theorem bytes_of_prem10 {P : Profile} {ρ : VarEnv} (hρ : ρ.findDef? "bytes_" = none)
    {v : Execution.Runtime.Value} (ft : ρ.findVal? "t" = some (valTypeV v.type))
    (fc : ρ.findVal? "c" = some (numV v))
    (hp : EvalExp (simEnv10 (bytesB10 P)) ρ (.cmpE .eqOp .boolT (iterVar "b" "b*")
      (.callE "bytes_" [.expA (.varE "t"), .expA (.varE "c")])) (.bool true)) :
    EvalExp (simEnv10 (bytesB10 P)) ρ (iterVar "b" "b*")
      (bytesV (Execution.Memory.encodeLE (v.type.width / 8) v.bits.toNat)) := by
  obtain ⟨V, hb, hbytes⟩ := Sim.Bwd.eq_of_cmp hp
  have eV : V = bytesV (Execution.Memory.encodeLE (v.type.width / 8) v.bits.toNat) :=
    EvalExp.unique hbytes (Whole.evalExp_bytesCall10 hρ ft fc)
  exact eV ▸ hb

/-- **`Step/store-num-val` backwards in `simEnv10T`**, at `bytesB10`, from a `GoodV1`
configuration: V1's successful `intStore` (no pack size) or `floatStore`. -/
theorem bwd10T_storeNumVal {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10T (bytesB10 P)) "Step" 8 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  have hS : EnvSame (simEnv10 (bytesB10 P)) (simEnv10T (bytesB10 P)) := envSame10T _
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ :=
    Whole.firesCfg10_inv (hasRuleAtT hasRuleAt10_storeNumVal') hf
  obtain ⟨i, ty, x, ao, a₃, rfl, fi, ft, fc, fa, hd⟩ := storeNum_lhs10 (evalExps_back hS hes)
  have hb := bytes_of_prem10 (v := ⟨ty, x⟩) (findDef_bindVals10 σ _) ft fc
    (evalExp_back hS (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _))))
  have hj : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) (div8E sizeTE)
      (.num (.natN (Execution.Memory.encodeLE (ty.width / 8) x.toNat).size)) :=
    (Execution.Memory.encodeLE_size _ _).symm ▸
      evalExp_div8 (evalExp_size10 ty (findDef_bindVals10 σ _) (Sim.evalExp_var ft)) (width_cases ty)
  rcases hd with ⟨t', rfl, rfl⟩ | ⟨t', rfl, rfl⟩
  · obtain ⟨a, m, hm⟩ := Whole.mem_of_good3 hg (fun h => h)
    exact write_step10 fz fi fa hm hj hb (evalExp_back hS hrh) fun b hw =>
      .intStore s f t' none ao i x a m b hm ((storeInt_eq_write10 t' m.data _ x).trans hw)
  · obtain ⟨a, m, hm⟩ := Whole.mem_of_good3 hg (fun h => h)
    exact write_step10 fz fi fa hm hj hb (evalExp_back hS hrh) fun b hw =>
      .floatStore s f t' ao i x a m b hm ((storeFloat_eq_write10 t' m.data _ x).trans hw)

/-! ## Rule 10 -/

/-- The left-hand side of rule 10, read back. -/
theorem storePack_lhs10 {B : Builtins} {σ : List (IL.Id × Value)} {code : List Admin}
    (hes : EvalExps (simEnv10 B) (VarEnv.empty.bindVals σ) [Sim20.Whole.constIE,
      .caseE "CONST" (.tupE [Whole.innE10, .varE "c"]),
      .caseE "STORE" (.tupE [Whole.innE10, .optE (some (.caseE "%" (.tupE [.varE "n"]))),
        .varE "ao"])] (adminsToV code)) :
    ∃ (i : BitVec 32) (t : IntType) (x : BitVec t.width) (sz : V1.PackSize) (ao : V1.MemArg),
      code = [value ⟨.int .i32, i⟩, value ⟨.int t, x⟩, .source (.intStore t (some sz) ao)] ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) ∧
      (VarEnv.empty.bindVals σ).findVal? "Inn" = some (valTypeV (.int t)) ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) ∧
      (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) ∧
      (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := by
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Whole.codes10_three hes
  obtain ⟨i, rfl, fi⟩ := Whole.constI32_of_lhs10 h₁
  obtain ⟨⟨ty, x⟩, rfl, hty, fc⟩ := const_tcc10 h₂
  have fInn := Whole.inn_of_eval10 hty
  obtain ⟨t, sz, ao, rfl, rfl, fa, fn⟩ := Whole.storePack_decode fInn h₃
  exact ⟨i, t, x, sz, ao, rfl, evalExp_varE_iff.1 fi, fInn, fc, fn, fa⟩

/-- **`Step/store-pack-val` backwards in `simEnv10T`**, at `bytesB10`, from a `GoodV1`
configuration: V1's successful packed `intStore`. -/
theorem bwd10T_storePackVal {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10T (bytesB10 P)) "Step" 10 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  have hS : EnvSame (simEnv10 (bytesB10 P)) (simEnv10T (bytesB10 P)) := envSame10T _
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ :=
    Whole.firesCfg10_inv (hasRuleAtT hasRuleAt10_storePackVal') hf
  obtain ⟨i, t, x, sz, ao, rfl, fi, fInn, fc, fn, fa⟩ := storePack_lhs10 (evalExps_back hS hes)
  obtain ⟨a, m, hm⟩ := Whole.mem_of_good3 hg (fun h => h)
  obtain ⟨V, hb, hbytes⟩ :=
    Sim.Bwd.eq_of_cmp (evalExp_back hS (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _))))
  have eV : V = bytesV (Execution.Memory.encodeLE (sz.width / 8) (x.setWidth sz.width).toNat) :=
    EvalExp.unique hbytes (evalExp_packBytes10 fInn fc fn
      (findDef_bindVals10 σ _) (findDef_bindVals10 σ _) (findDef_bindVals10 σ _))
  have hj : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) (div8E (.varE "n"))
      (.num (.natN (Execution.Memory.encodeLE (sz.width / 8) (x.setWidth sz.width).toNat).size)) :=
    (Execution.Memory.encodeLE_size _ _).symm ▸
      evalExp_div8 (Sim.evalExp_var fn) (packWidth10_cases sz)
  exact write_step10 fz fi fa hm hj (eV ▸ hb) (evalExp_back hS hrh) fun b hw =>
    .intStore s f t (some sz) ao i x a m b hm ((storeIntPack_eq_write10 t sz m.data _ x).trans hw)

/-! ## The four store rules -/

/-- **The four store rules backwards in `simEnv10T`**, at `bytesB10`, from a `GoodV1`
configuration. -/
theorem bwd10T_store {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value} {k : Nat}
    (hk : 7 ≤ k ∧ k ≤ 10) (hg : GoodV1 c)
    (hf : Fires (simEnv10T (bytesB10 P)) "Step" k (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨h₁, h₂⟩ := hk
  match k, h₁, h₂, hf with
  | 7, _, _, hf => exact bwd10T_storeNumTrap hg hf
  | 8, _, _, hf => exact bwd10T_storeNumVal hg hf
  | 9, _, _, hf => exact bwd10T_storePackTrap hg hf
  | 10, _, _, hf => exact bwd10T_storePackVal hg hf

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
