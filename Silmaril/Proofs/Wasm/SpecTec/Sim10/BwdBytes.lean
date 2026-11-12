module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLoadVal
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemTrap
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.ConstBound

/-!
# The 1.0 load rules backwards at `bytesB10` (round 4, pass 2)

At `floatIntB` the rules `load-num-val` and `load-pack-val` never fire, because `$bytes_` and
`$ibytes_` are inert (`Inert`). At `bytesB10` they fire, so the backward half needs them as real
obligations. This module proves them.

* **`bwd10_loadNumVal`**: if `load-num-val` (`Step_read` 9) fires at `bytesB10 P` from the image
  of a `GoodV1` configuration, V1 makes the same load. `$bytes_(t, c)` answers only at the image
  `numV ⟨t, b⟩` of a V1 number (`decNum`), the slice of the frame's memory is V1's `readBytes`,
  and the bytes are injective (`bytesV10_injective`), so `b` is the number V1's `loadInt` or
  `loadFloat` decodes (`Memory.decodeLE_encodeLE`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress loadInt loadFloat)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst MemAddr)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_addNat20 evalExp_div8 evalExp_iPay width_cases)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-! ## Inversions -/

/-- An `if a = b` premise that holds: both sides denote one value. -/
theorem eq_of_evalExp_eqTrue {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp}
    (h : EvalExp env ρ (.cmpE .eqOp .boolT e₁ e₂) (.bool true)) :
    ∃ u, EvalExp env ρ e₁ u ∧ EvalExp env ρ e₂ u := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e : v₁ = v₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hc
  subst e
  exact ⟨v₁, h₁, h₂⟩

/-- A call to a builtin with no clauses denotes what the builtins answer on its arguments. -/
theorem call_of_callDef_nil {env : Env} {ρ : VarEnv} {x : IL.Id} {ps : List Param} {t : Typ}
    {args : List Arg} {v : Value} (hρ : ρ.findDef? x = none)
    (hd : env.findDef? x = some (ps, t, [])) (h : EvalExp env ρ (.callE x args) v) :
    ∃ ws, EvalArgs env ρ args ws ∧ env.builtins.call x ws = some v := by
  obtain ⟨ws, ps', t', cs, ha, hd', hc⟩ := Equiv.ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 h)
  rw [hρ, Option.getD_none, hd] at hd'
  have hcs : cs = [] := (Prod.ext_iff.1 (Prod.ext_iff.1 (Option.some.inj hd')).2).2.symm
  subst hcs
  rcases hc with hc | ⟨-, hb⟩
  · exact absurd hc Equiv.ExecBuiltins.not_tryClauses_nil
  · rw [hρ, Option.getD_none] at hb
    exact ⟨ws, ha, hb⟩

/-- `decNum` answers only at an image. -/
theorem eq_of_decNum {t : NumType} {v : Value} {b : BitVec t.width}
    (h : Sim.Floats.decNum t v = some b) : v = Silmaril.Wasm.SpecTec.Sim.numV ⟨t, b⟩ := by
  unfold Sim.Floats.decNum at h
  split at h
  · rename_i hex
    cases h
    exact (Classical.choose_spec hex).symm
  · cases h

/-- `$bytes_(t, c)` at `bytesB10`, inverted: `c` is the image of a number of type `t`. -/
theorem bytesCall10_inv {P : Profile} {ρ : VarEnv} {t : V1.ValType} {u : Value}
    (hρ : ρ.findDef? "bytes_" = none) (ft : ρ.findVal? "t" = some (valTypeV t))
    {cv : Value} (fc : ρ.findVal? "c" = some cv)
    (h : EvalExp (simEnv10 (bytesB10 P)) ρ
      (.callE "bytes_" [.expA (.varE "t"), .expA (.varE "c")]) u) :
    ∃ b : BitVec t.width, cv = numV ⟨t, b⟩ ∧
      u = bytesV (Execution.Memory.encodeLE (t.width / 8) b.toNat) := by
  obtain ⟨ps, ty, hd⟩ := findDef_bytes10 (B := bytesB10 P)
  obtain ⟨ws, ha, hb⟩ := call_of_callDef_nil hρ hd h
  have hws : ws = [.val (valTypeV t), .val cv] :=
    Equiv.ExecNumeric.evalArgs_unique ha
      (evalArgs_cons (Sim.evalExp_var ft) (evalArgs_cons (Sim.evalExp_var fc) evalArgs_nil))
  rw [hws, simEnv10, Env.builtins_withBuiltins, bytesB10_bytes, bytesCall10_type,
    bytesAns10] at hb
  obtain ⟨b, hdec, hu⟩ := Option.map_eq_some_iff.1 hb
  refine ⟨b, ?_, hu.symm⟩
  have hc := eq_of_decNum hdec
  rw [hc]
  rcases t with t | t <;> rfl

/-- The slice of the frame's memory, inverted: it is V1's `readBytes`. -/
theorem loadSlice10_inv {B : Builtins} {ρ : VarEnv} {e : Exp} {w : Nat} {s : Store H} {f : Frame}
    {c : BitVec 32} {ao : V1.MemArg} {a : MemAddr} {m : MemInst} {u : Value}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV c.toNat))
    (fa : ρ.findVal? "ao" = some (memargV ao)) (hρ : ρ.findDef? "mem" = none)
    (he : EvalExp (simEnv10 B) ρ e (.num (.natN w)))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (hm : frameMemory s f = some (a, m))
    (h : EvalExp (simEnv10 B) ρ (loadSliceE10 e) u) :
    ∃ r, Execution.Memory.readBytes m.data (effectiveAddress c ao) (w / 8) = some r ∧
      u = bytesV r := by
  obtain ⟨wv, i, k, h₁, h₂, h₃, hs⟩ := evalExp_sliceE_iff.1 h
  have hmem : EvalExp (simEnv10 B) ρ (.dotE Sim20.Whole.mem0E "BYTES")
      (.list (Sim.Memory.bytesL m.data)) := by
    rw [← bytesV_eq_bytesL10]
    exact evalExp_dotE_iff.2 ⟨memInstV m, evalExp_mem0_10 hρ fz hm, rfl⟩
  have e₁ : wv = .list (Sim.Memory.bytesL m.data) := EvalExp.unique h₁ hmem
  have e₂ : Value.num (.natN i) = .num (.natN (effectiveAddress c ao)) :=
    EvalExp.unique h₂ (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off10 fa))
  have e₃ : Value.num (.natN k) = .num (.natN (w / 8)) := EvalExp.unique h₃ (evalExp_div8 he hw)
  have hi : i = effectiveAddress c ao := Num.natN.inj (Value.num.inj e₂)
  have hk : k = w / 8 := Num.natN.inj (Value.num.inj e₃)
  rw [e₁, hi, hk, Sim.Memory.slice?_bytesL] at hs
  obtain ⟨r, hr, hu⟩ := Option.map_eq_some_iff.1 hs
  exact ⟨r, hr, by rw [← hu, bytesV_eq_bytesL10]⟩

/-! ## V1's side -/

/-- Reading the encoding of `b` is an unpacked load of `b`. -/
theorem load_of_readBytes {t : V1.ValType} {mem : Execution.Memory.Bytes} {start : Nat}
    {b : BitVec t.width}
    (h : Execution.Memory.readBytes mem start (t.width / 8) =
      some (Execution.Memory.encodeLE (t.width / 8) b.toNat)) :
    (Execution.Memory.load mem start (t.width / 8)).map (fun x => x.setWidth t.width) = some b := by
  have hw : 8 * (t.width / 8) = t.width := by rcases t with (_ | _) | (_ | _) <;> rfl
  have hlt : b.toNat < 256 ^ (t.width / 8) := by
    have h₁ := b.isLt
    have h₂ : (256 : Nat) ^ (t.width / 8) = 2 ^ t.width := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, hw]
    omega
  simp only [Execution.Memory.load, h, Option.map_some, Option.some.injEq,
    Execution.Memory.decodeLE_encodeLE, Nat.mod_eq_of_lt hlt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h₃ : b.toNat < 2 ^ (8 * (t.width / 8)) := by rw [hw]; exact b.isLt
  rw [Nat.mod_eq_of_lt h₃, Nat.mod_eq_of_lt b.isLt]

theorem loadInt_of_readBytes {t : IntType} {mem : Execution.Memory.Bytes} {start : Nat}
    {b : BitVec t.width}
    (h : Execution.Memory.readBytes mem start (t.width / 8) =
      some (Execution.Memory.encodeLE (t.width / 8) b.toNat)) :
    loadInt t none mem start = some (.int t b) := by
  have hl : Option.map (fun x => x.setWidth t.width)
      (Execution.Memory.load mem start (t.width / 8)) = some b := load_of_readBytes (t := .int t) h
  have e : loadInt t none mem start = (Option.map (fun x => x.setWidth t.width)
      (Execution.Memory.load mem start (t.width / 8))).map (Execution.Runtime.Value.int t) := by
    simp only [loadInt, Option.map_map]
    rfl
  rw [e, hl]
  rfl

theorem loadFloat_of_readBytes {t : FloatType} {mem : Execution.Memory.Bytes} {start : Nat}
    {b : BitVec t.width}
    (h : Execution.Memory.readBytes mem start (t.width / 8) =
      some (Execution.Memory.encodeLE (t.width / 8) b.toNat)) :
    loadFloat t mem start = some (.float t b) := by
  have hl : Option.map (fun x => x.setWidth t.width)
      (Execution.Memory.load mem start (t.width / 8)) = some b := load_of_readBytes (t := .float t) h
  have e : loadFloat t mem start = (Option.map (fun x => x.setWidth t.width)
      (Execution.Memory.load mem start (t.width / 8))).map (Execution.Runtime.Value.float t) := by
    simp only [loadFloat, Option.map_map]
    rfl
  rw [e, hl]
  rfl

/-! ## `load-num-val` backwards -/

/-- The right-hand side `CONST t c` of `load-num-val`, inverted. -/
theorem constRhs10_inv {B : Builtins} {ρ : VarEnv} {t : V1.ValType} {cv : Value} {w : List Value}
    (ft : ρ.findVal? "t" = some (valTypeV t)) (fc : ρ.findVal? "c" = some cv)
    (h : EvalExp (simEnv10 B) ρ (.listE [.caseE "CONST" (.tupE [.varE "t", .varE "c"])])
      (.list w)) :
    w = [.case "CONST" (.tuple [valTypeV t, cv])] := by
  have h' : EvalExp (simEnv10 B) ρ (.listE [.caseE "CONST" (.tupE [.varE "t", .varE "c"])])
      (.list [.case "CONST" (.tuple [valTypeV t, cv])]) :=
    Sim.evalExp_list1 (Sim.evalExp_case (Sim.evalExp_tup2 (Sim.evalExp_var ft) (Sim.evalExp_var fc)))
  exact Value.list.inj (EvalExp.unique h h')

/-- The image of a loaded value. -/
theorem adminsToV_value1 (v : Execution.Runtime.Value) :
    adminsToV [value v] = [.case "CONST" (.tuple [valTypeV v.type, numV v])] := by
  rw [adminsToV_map10, List.map_singleton, adminToV_value]
  rfl

/-- What a firing of `load-num-val` at `bytesB10` says, from the scope of the rule. -/
theorem loadNumVal_scope {P : Profile} {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32}
    {t : V1.ValType} {ao : V1.MemArg} {cv : Value} {w : List Value}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (ft : ρ.findVal? "t" = some (valTypeV t)) (fa : ρ.findVal? "ao" = some (memargV ao))
    (fc : ρ.findVal? "c" = some cv) (hρ : ρ.findDef? "bytes_" = none)
    (hρ' : ρ.findDef? "mem" = none) (hρ'' : ρ.findDef? "size" = none)
    (hrh : EvalExp (simEnv10 (bytesB10 P)) ρ
      (.listE [.caseE "CONST" (.tupE [.varE "t", .varE "c"])]) (.list w))
    (hprem : EvalExp (simEnv10 (bytesB10 P)) ρ (.cmpE .eqOp .boolT
      (.callE "bytes_" [.expA (.varE "t"), .expA (.varE "c")]) (loadSliceE10 sizeTE)) (.bool true)) :
    ∃ b : BitVec t.width, w = adminsToV [value ⟨t, b⟩] ∧ ∀ a m, frameMemory s f = some (a, m) →
      Execution.Memory.readBytes m.data (effectiveAddress i ao) (t.width / 8) =
        some (Execution.Memory.encodeLE (t.width / 8) b.toNat) := by
  have hw : w = [.case "CONST" (.tuple [valTypeV t, cv])] := constRhs10_inv ft fc hrh
  obtain ⟨u, hu₁, hu₂⟩ := eq_of_evalExp_eqTrue hprem
  obtain ⟨b, hcv, hub⟩ := bytesCall10_inv hρ ft fc hu₁
  refine ⟨b, by rw [hw, hcv, adminsToV_value1], fun a m hm => ?_⟩
  obtain ⟨r, hr, hur⟩ := loadSlice10_inv fz fi fa hρ'
    (evalExp_size10 t hρ'' (Sim.evalExp_var ft)) (width_cases t) hm hu₂
  rw [hr, bytesV10_injective (hur.symm.trans hub)]

/-- **`Step_read/load-num-val` backwards** at `bytesB10`, at a `GoodV1` configuration. -/
theorem bwd10_loadNumVal {P : Profile} {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c)
    (hf : Fires (simEnv10 (bytesB10 P)) "Step_read" 9 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_loadNumVal' _) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨t, ao, ft, fa, hd⟩ := loadNum_decode h₂
  obtain ⟨cv, fc, -⟩ := hq "c" (.varT "val_" [.expA (.varE "t")]) (by simp)
  obtain ⟨b, hval, hread⟩ := loadNumVal_scope fz (evalExp_varE_iff.1 fi) ft fa fc rfl rfl rfl hrh
    (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  rcases hd with ⟨t', rfl, rfl⟩ | ⟨t', rfl, rfl⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
    exact ⟨_, hval, .intLoad s f t' none ao i a m _ hm (loadInt_of_readBytes (hread a m hm))⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
    exact ⟨_, hval, .floatLoad s f t' ao i a m _ hm (loadFloat_of_readBytes (hread a m hm))⟩

/-! ## `load-pack-val` backwards -/

/-- `LOAD Inn (n _ sx) ao`, read back with `Inn` and `sx`. -/
theorem loadPack_decode' {B : Builtins} {ρ : VarEnv} {a : Admin}
    (h : EvalExp (simEnv10 B) ρ (.caseE "LOAD" (.tupE [innE10, .optE (some (.caseE "%_%" (.tupE
      [.caseE "%" (.tupE [.varE "n"]), .varE "sx"]))), .varE "ao"])) (adminToV a)) :
    ∃ t sz sx ao, a = .source (.intLoad t (some (sz, sx)) ao) ∧
      ρ.findVal? "ao" = some (memargV ao) ∧ ρ.findVal? "n" = some (.num (.natN sz.width)) ∧
      ρ.findVal? "Inn" = some (valTypeV (.int t)) ∧ ρ.findVal? "sx" = some (Sim20.sxV sx) := by
  obtain ⟨t, sz, sx, ao, rfl, fa, fn⟩ := loadPack_decode h
  have hs := tup_of_caseE10 h (us := [valTypeV (.int t),
    .opt (some (.case "%_%" (.tuple [szV sz, Sim20.sxV sx]))), memargV ao]) rfl
  have fInn : ρ.findVal? "Inn" = some (valTypeV (.int t)) := inn_of_eval10 (fst_of3 hs)
  obtain ⟨u, hu, hpu⟩ := evalExp_optE_some_iff.1 (Sim20.Whole.snd_of3 hs)
  have eu : u = .case "%_%" (.tuple [szV sz, Sim20.sxV sx]) := by simpa using hpu.symm
  subst eu
  obtain ⟨w₁, us₁, -, hrest, he₁⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 (tup_of_caseV hu)
  have eus : us₁ = [Sim20.sxV sx] := (List.cons.inj he₁).2.symm
  subst eus
  obtain ⟨w₂, us₂, hsx, -, he₂⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hrest
  have ew₂ : w₂ = Sim20.sxV sx := (List.cons.inj he₂).1.symm
  exact ⟨t, sz, sx, ao, rfl, fa, fn, fInn, evalExp_varE_iff.1 (ew₂ ▸ hsx)⟩

/-- Reading the encoding of a narrow `x` is the packed load of its extension. -/
theorem loadPack_of_readBytes {t : IntType} {sz : V1.PackSize} {sx : Signedness}
    {mem : Execution.Memory.Bytes} {start : Nat} {x : BitVec sz.width}
    (h : Execution.Memory.readBytes mem start (sz.width / 8) =
      some (Execution.Memory.encodeLE (sz.width / 8) x.toNat)) :
    loadInt t (some (sz, sx)) mem start = some (.int t (extPack10 t sx x)) := by
  have hw : 8 * (sz.width / 8) = sz.width := by cases sz <;> rfl
  have hlt : x.toNat < 256 ^ (sz.width / 8) := by
    have h₂ : (256 : Nat) ^ (sz.width / 8) = 2 ^ sz.width := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, hw]
    rw [h₂]
    exact x.isLt
  have hl : Execution.Memory.load mem start (sz.width / 8) =
      some (BitVec.ofNat (8 * (sz.width / 8)) x.toNat) := by
    simp only [Execution.Memory.load, h, Option.map_some, Execution.Memory.decodeLE_encodeLE,
      Nat.mod_eq_of_lt hlt]
  simp only [loadInt, hl, Option.map_some]
  cases sz <;> cases sx <;> simp [extPack10] <;> rfl

/-- **`Step_read/load-pack-val` backwards** at `bytesB10`, at a `GoodV1` configuration. -/
theorem bwd10_loadPackVal {P : Profile} {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c)
    (hf : Fires (simEnv10 (bytesB10 P)) "Step_read" 11 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_loadPackVal' _) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨t, sz, sx, ao, rfl, fa, fn, fInn, fsx⟩ := loadPack_decode' h₂
  obtain ⟨cv, fc, hty⟩ := hq "c" (.varT "iN" [.expA (.varE "n")]) (by simp)
  obtain ⟨k, rfl, hk⟩ := iN_inv_lt10 (Sim.evalExp_var fn) hty
  let x : BitVec sz.width := BitVec.ofNat _ k
  have hxk : x.toNat = k := by simp [x, Nat.mod_eq_of_lt hk]
  have fc' : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) := by rw [hxk]; exact fc
  have hrhs : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [innE10, extendE10])])
      (.list (adminsToV [value ⟨.int t, extPack10 t sx x⟩])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact Sim.evalExp_list1 (Sim.evalExp_case (Sim.evalExp_tup2
      (evalExp_subE_iff.2 (Sim.evalExp_var fInn)) (evalExp_extend10 rfl rfl fInn fn fsx fc')))
  have hval : w = adminsToV [value ⟨.int t, extPack10 t sx x⟩] :=
    Value.list.inj (EvalExp.unique hrh hrhs)
  have hprem := Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _))
  obtain ⟨u, hu₁, hu₂⟩ := eq_of_evalExp_eqTrue hprem
  have hub : u = bytesV (Execution.Memory.encodeLE (sz.width / 8) x.toNat) :=
    EvalExp.unique hu₁ (evalExp_ibytesCall10 rfl fn fc')
  obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
  obtain ⟨r, hr, hur⟩ := loadSlice10_inv fz (evalExp_varE_iff.1 fi) fa rfl
    (Sim.evalExp_var fn) (packWidth10_cases sz) hm hu₂
  have hread : Execution.Memory.readBytes m.data (effectiveAddress i ao) (sz.width / 8) =
      some (Execution.Memory.encodeLE (sz.width / 8) x.toNat) := by
    rw [hr, bytesV10_injective (hur.symm.trans hub)]
  exact ⟨_, hval, .intLoad s f t (some (sz, sx)) ao i a m _ hm (loadPack_of_readBytes hread)⟩

/-! ## `memory.grow-succeed` backwards -/

/-- The pattern `% n`, read back. -/
theorem var_of_pct10 {env : Env} {ρ : VarEnv} {k : Nat}
    (h : EvalExp env ρ (.caseE "%" (.tupE [.varE "n"])) (pctV k)) :
    ρ.findVal? "n" = some (.num (.natN k)) := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  have eu : u = .tuple [.num (.natN k)] := by
    simp only [pctV, Value.case.injEq] at hcu
    exact hcu.2.symm
  subst eu
  obtain ⟨v, hv, hn⟩ := Sim20.Whole.tup1_inv' hu
  have ev : v = .num (.natN k) := (List.cons.inj (Value.tuple.inj hv)).1.symm
  exact evalExp_varE_iff.1 (ev ▸ hn)

/-- The premise `$growmemory($mem(z, 0), n) = mi` at `bytesB10`, read back: `mi` is V1's grown
memory. -/
theorem growPrem10_inv {P : Profile} {ρ : VarEnv} {m : MemInst} {n : Nat}
    (em : EvalExp (simEnv10 (bytesB10 P)) ρ Sim20.Whole.mem0E (memInstV m))
    (fn : ρ.findVal? "n" = some (.num (.natN n))) (hd : ρ.findDef? "growmemory" = none)
    (h : EvalExp (simEnv10 (bytesB10 P)) ρ
      (.cmpE .eqOp .boolT Sim20.Whole.growMemCallE (.varE "mi")) (.bool true)) :
    ∃ d, Execution.Memory.grow? m.data m.max n = some d ∧
      ρ.findVal? "mi" = some (memInstV {m with data := d}) := by
  obtain ⟨u, e₁, e₂⟩ := eq_of_evalExp_eqTrue h
  obtain ⟨M, N, eM, eN, hA⟩ := Sim20.Whole.applies_of_call2' hd e₁
  have hM : M = memInstV m := EvalExp.unique eM em
  have hN : N = .num (.natN n) := EvalExp.unique eN (Sim.evalExp_var fn)
  subst hM hN
  have hB := Sim20.Whole.growmemory10_builtin hA
  rw [bytesB10_growmemory] at hB
  obtain ⟨d, hgr, hu⟩ := Option.map_eq_some_iff.1 hB
  exact ⟨d, hgr, by rw [evalExp_varE_iff.1 e₂, ← hu]⟩

/-- **`Step/memory.grow-succeed` backwards** at `bytesB10`, at a `GoodV1` configuration: V1's
`memoryGrow` with `Memory.Grow.success`. -/
theorem bwd10_memGrowSucceed {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10 (bytesB10 P)) "Step" 11 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_memGrowSucceed _) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨n, rfl, hn⟩ := constI32_of_lhs10 h₁
  have fn := var_of_pct10 hn
  obtain rfl := head10_memoryGrow (head10_of_caseE h₂)
  obtain ⟨a, m, hfm, -⟩ := memory_of_good hg
  obtain ⟨d, hgr, fmi⟩ := growPrem10_inv (evalExp_mem0_10 rfl fz hfm) fn rfl
    (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  obtain ⟨hal, hlt⟩ := grow_bounds10 hgr
  exact ⟨_, EvalExp.unique hrh (growRhs10 rfl rfl rfl fz fmi hfm hal hlt),
    .memoryGrow s f a m n _ d hfm (.success d hgr)⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
