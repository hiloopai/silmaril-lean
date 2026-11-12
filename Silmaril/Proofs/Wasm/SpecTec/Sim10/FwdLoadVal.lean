module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdGrow
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdLoad

/-!
# The successful loads forward, at `bytesB10` (round 4)

1.0's

  `z; (CONST I32 i) (LOAD t ao) ~> (CONST t c)`, if `$bytes_(t, c) = $mem(z, 0).BYTES[i + ao.OFFSET : $size(t)/8]`
  `z; (CONST I32 i) (LOAD Inn (n _ sx) ao) ~> (CONST Inn $extend__(n, $size(Inn), sx, c))`,
    if `$ibytes_(n, c) = $mem(z, 0).BYTES[i + ao.OFFSET : n/8]`

(`Step_read` 9 `load-num-val` and 11 `load-pack-val`, transcribed and checked by kernel `rfl`).
As in 2.0 (`Sim20.Whole.fires_loadNumVal`), `c` is a quantifier bound only by the premise, so no
inverse of `$bytes_` is needed: forward, `c` is bound to the value V1 reads.

* V1's side (`load_some`, `loadNum_some`, `loadPack_some`): a successful `Memory.load` of `k`
  bytes reads a slice `r` with `encodeLE k (decodeLE r) = r` (silmaril's
  `V2.Execution.encodeLE_decodeLE`, with `decodeLE_lt`), so the slice is the little-endian
  encoding of the value read.
* The slice premise is evaluated at the 1.0 `$mem` (`evalExp_loadSlice10`), with round 2's
  `Sim.Memory.slice?_bytesL`.
* `$bytes_` and `$ibytes_` are answered by `bytesB10` (`bytesCall10_numV`, `ibytesCall10_pct`).
* `$extend__(n, $size(Inn), sx, c)` is the sign or zero extension (`Sim.Floats.floatCall_extend`),
  which is V1's packed load; `c : iN(n)` is typed by `hasTyp_iN_of_uN10`.

So **`FwdLoads10 (bytesB10 P) hn` holds** (`fwdLoads10_bytesB10`), and the forward 1.0 half at
`bytesB10` needs no open obligation (`wholeStepFwd10_bytesB10''`).
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
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV stateT evalExp_case evalExp_tup2
  evalExp_tup3 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one)
open Silmaril.Wasm.SpecTec.Sim20.Whole (constIE mem0E div8E iPay offE evalExp_addNat20 evalExp_div8
  evalExp_iPay evalExp_eqTrue width_cases)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## V1's side: a successful load reads the encoding of its value -/

/-- `readBytes` returns exactly `count` bytes. -/
theorem readBytes_size10 {mem r : Execution.Memory.Bytes} {start count : Nat}
    (h : Execution.Memory.readBytes mem start count = some r) : r.size = count := by
  unfold Execution.Memory.readBytes at h
  split at h
  · rename_i hle
    cases h
    simp only [ByteArray.size_extract]
    omega
  · cases h

/-- **A successful `Memory.load` reads the little-endian encoding of its value.** -/
theorem load_some {mem : Execution.Memory.Bytes} {start count : Nat} {x : BitVec (8 * count)}
    (h : Execution.Memory.load mem start count = some x) :
    Execution.Memory.readBytes mem start count =
      some (Execution.Memory.encodeLE count x.toNat) := by
  unfold Execution.Memory.load at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  have hs := readBytes_size10 hr
  have hlt : Execution.Memory.decodeLE r < 2 ^ (8 * count) := by
    have h₁ := V2.Execution.decodeLE_lt r
    rw [hs] at h₁
    rwa [Nat.pow_mul]
  rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have h₂ := V2.Execution.encodeLE_decodeLE r
  rw [hs] at h₂
  rw [h₂]

/-- `setWidth` to a width at least the source's keeps the number. -/
theorem toNat_setWidth_le10 {n m : Nat} (x : BitVec n) (h : n ≤ m) :
    (x.setWidth m).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))

/-- **An unpacked load reads the encoding of its value**: `loadInt` (no pack) and `loadFloat`
answer `⟨t, b⟩` where the bytes read are `encodeLE (t.width/8) b`. -/
theorem loadNum_some {t : V1.ValType} {mem : Execution.Memory.Bytes} {start : Nat}
    {x : BitVec (8 * (t.width / 8))} (h : Execution.Memory.load mem start (t.width / 8) = some x) :
    Execution.Memory.readBytes mem start (t.width / 8) = some (Execution.Memory.encodeLE
      (t.width / 8) (x.setWidth t.width).toNat) := by
  rw [toNat_setWidth_le10 x (Nat.mul_div_le t.width 8)]
  exact load_some h

theorem loadInt_none_some {t : IntType} {mem : Execution.Memory.Bytes} {start : Nat}
    {v : Execution.Runtime.Value} (h : loadInt t none mem start = some v) :
    ∃ b : BitVec t.width, v = ⟨.int t, b⟩ ∧ Execution.Memory.readBytes mem start (t.width / 8) =
      some (Execution.Memory.encodeLE (t.width / 8) b.toNat) := by
  simp only [loadInt] at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨_, rfl, loadNum_some (t := .int t) hx⟩

theorem loadFloat_some {t : FloatType} {mem : Execution.Memory.Bytes} {start : Nat}
    {v : Execution.Runtime.Value} (h : loadFloat t mem start = some v) :
    ∃ b : BitVec t.width, v = ⟨.float t, b⟩ ∧ Execution.Memory.readBytes mem start (t.width / 8) =
      some (Execution.Memory.encodeLE (t.width / 8) b.toNat) := by
  simp only [loadFloat] at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨_, rfl, loadNum_some (t := .float t) hx⟩

/-- V1's packed extension. -/
def extPack10 (t : IntType) (sx : Signedness) {n : Nat} (x : BitVec n) : BitVec t.width :=
  match sx with
  | .unsigned => x.setWidth t.width
  | .signed => x.signExtend t.width

/-- **A packed load reads the encoding of the narrow value it extends.** -/
theorem loadPack_some {t : IntType} {sz : V1.PackSize} {sx : Signedness}
    {mem : Execution.Memory.Bytes} {start : Nat} {v : Execution.Runtime.Value}
    (h : loadInt t (some (sz, sx)) mem start = some v) :
    ∃ x : BitVec sz.width, v = ⟨.int t, extPack10 t sx x⟩ ∧
      Execution.Memory.readBytes mem start (sz.width / 8) =
        some (Execution.Memory.encodeLE (sz.width / 8) x.toNat) := by
  simp only [loadInt] at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  have hr := load_some hx
  cases sz <;> cases sx <;> exact ⟨x, rfl, hr⟩

/-! ## The rules, transcribed -/

/-- `$mem(z, 0).BYTES[i + ao.OFFSET : w/8]`. -/
abbrev loadSliceE10 (w : Exp) : Exp :=
  .sliceE (.dotE mem0E "BYTES") (.binE .addOp (.numT .natT) iPay offE) (div8E w)

/-- `Step_read/load-num-val` of 1.0. -/
def loadNumValRule10 : Rule :=
  .ruleD "load-num-val" [.expP "z" (.varT "state" []), .expP "i" valI32T',
    .expP "t" (.varT "valtype" []), .expP "ao" (.varT "memarg" []),
    .expP "c" (.varT "val_" [.expA (.varE "t")])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "LOAD" (.tupE [.varE "t", .optE none, .varE "ao"])]]),
      .listE [.caseE "CONST" (.tupE [.varE "t", .varE "c"])]])
    [.ifPr (.cmpE .eqOp .boolT (.callE "bytes_" [.expA (.varE "t"), .expA (.varE "c")])
      (loadSliceE10 sizeTE))]

/-- `$extend__(n, $size(Inn), sx, c)`. -/
abbrev extendE10 : Exp :=
  .callE "extend__" [.expA (.varE "n"), .expA (.callE "size" [.expA innE10]), .expA (.varE "sx"),
    .expA (.varE "c")]

/-- `Step_read/load-pack-val` of 1.0. -/
def loadPackValRule10 : Rule :=
  .ruleD "load-pack-val" [.expP "z" (.varT "state" []), .expP "i" valI32T',
    .expP "Inn" (.varT "Inn" []), .expP "n" (.varT "n" []), .expP "sx" (.varT "sx" []),
    .expP "ao" (.varT "memarg" []), .expP "c" (.varT "iN" [.expA (.varE "n")])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "LOAD" (.tupE [innE10, .optE (some (.caseE "%_%" (.tupE [.caseE "%" (.tupE
        [.varE "n"]), .varE "sx"]))), .varE "ao"])]]),
      .listE [.caseE "CONST" (.tupE [innE10, extendE10])]])
    [.ifPr (.cmpE .eqOp .boolT (.callE "ibytes_" [.expA (.varE "n"), .expA (.varE "c")])
      (loadSliceE10 (.varE "n")))]

variable (B) in
theorem hasRuleAt10_loadNumVal' :
    HasRuleAt (simEnv10 B) "Step_read" "%~>%" 9 loadNumValRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable (B) in
theorem hasRuleAt10_loadPackVal' :
    HasRuleAt (simEnv10 B) "Step_read" "%~>%" 11 loadPackValRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## The premise -/

theorem bytesV_eq_bytesL10 (b : ByteArray) : bytesV b = .list (Sim.Memory.bytesL b) :=
  Sim20.Whole.bytesV_eq_bytesL b

/-- **The slice of the frame's memory**, at a read V1 makes. -/
theorem evalExp_loadSlice10 {ρ : VarEnv} {e : Exp} {w : Nat} {s : Store H} {f : Frame}
    {c : BitVec 32} {ao : V1.MemArg} {a : MemAddr} {m : MemInst} {r : Execution.Memory.Bytes}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV c.toNat))
    (fa : ρ.findVal? "ao" = some (memargV ao)) (hρ : ρ.findDef? "mem" = none)
    (he : EvalExp (simEnv10 B) ρ e (.num (.natN w)))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (hm : frameMemory s f = some (a, m))
    (hb : Execution.Memory.readBytes m.data (effectiveAddress c ao) (w / 8) = some r) :
    EvalExp (simEnv10 B) ρ (loadSliceE10 e) (bytesV r) := by
  have hmem : EvalExp (simEnv10 B) ρ (.dotE mem0E "BYTES") (.list (Sim.Memory.bytesL m.data)) := by
    rw [← bytesV_eq_bytesL10]
    exact evalExp_dotE_iff.2 ⟨memInstV m, evalExp_mem0_10 hρ fz hm, rfl⟩
  have hsl : (Value.list (Sim.Memory.bytesL m.data)).slice? (effectiveAddress c ao) (w / 8) =
      some (bytesV r) := by
    rw [Sim.Memory.slice?_bytesL, hb, bytesV_eq_bytesL10]
    rfl
  exact evalExp_sliceE_iff.2 ⟨_, _, _, hmem, evalExp_addNat20 (evalExp_iPay fi) (evalExp_off10 fa),
    evalExp_div8 he hw, hsl⟩

/-- `$bytes_(t, c)` at `bytesB10`, at the image of a V1 number. -/
theorem evalExp_bytesCall10 {P : Profile} {ρ : VarEnv} {v : Execution.Runtime.Value}
    (hρ : ρ.findDef? "bytes_" = none) (ft : ρ.findVal? "t" = some (valTypeV v.type))
    (fc : ρ.findVal? "c" = some (numV v)) :
    EvalExp (simEnv10 (bytesB10 P)) ρ (.callE "bytes_" [.expA (.varE "t"), .expA (.varE "c")])
      (bytesV (Execution.Memory.encodeLE (v.type.width / 8) v.bits.toNat)) := by
  obtain ⟨ps, t, hd⟩ := findDef_bytes10 (B := bytesB10 P)
  refine evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd
    (evalArgs_cons (Sim.evalExp_var ft) (evalArgs_cons (Sim.evalExp_var fc) evalArgs_nil)) ?_)
  rw [simEnv10, Env.builtins_withBuiltins, bytesB10_bytes, bytesCall10_numV]
  rfl

/-- `$ibytes_(n, c)` at `bytesB10`. -/
theorem evalExp_ibytesCall10 {P : Profile} {ρ : VarEnv} {n k : Nat}
    (hρ : ρ.findDef? "ibytes_" = none) (fn : ρ.findVal? "n" = some (.num (.natN n)))
    (fc : ρ.findVal? "c" = some (pctV k)) :
    EvalExp (simEnv10 (bytesB10 P)) ρ (.callE "ibytes_" [.expA (.varE "n"), .expA (.varE "c")])
      (bytesV (Execution.Memory.encodeLE (n / 8) k)) := by
  obtain ⟨ps, t, hd⟩ := findDef_ibytes10 (B := bytesB10 P)
  refine evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd
    (evalArgs_cons (Sim.evalExp_var fn) (evalArgs_cons (Sim.evalExp_var fc) evalArgs_nil)) ?_)
  rw [simEnv10, Env.builtins_withBuiltins, bytesB10_ibytes, ibytesCall10_pct]
  rfl

/-! ## `load-num-val` -/

/-- The scope of `load-num-val`. -/
abbrev loadNumValScope (z : Value) (c : BitVec 32) (ao : V1.MemArg) (v : Execution.Runtime.Value) :
    List (IL.Id × Value) :=
  [("z", z), ("i", pctV c.toNat), ("t", valTypeV v.type), ("ao", memargV ao), ("c", numV v)]

/-- **`load-num-val` fires forward** at `bytesB10`, at a V1 read of the value `v`. -/
theorem fires10_loadNumVal {P : Profile} {s : Store H} {f : Frame} {c : BitVec 32}
    {ao : V1.MemArg} {a : MemAddr} {m : MemInst} {v : Execution.Runtime.Value} {code : List Admin}
    (hcode : adminsToV code = [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]),
      .case "LOAD" (.tuple [valTypeV v.type, .opt none, memargV ao])])
    (hz : TypedV (simEnv10 (bytesB10 P)) stateT (stateV hn s f))
    (hc : TypedV (simEnv10 (bytesB10 P)) valI32T (pctV c.toNat))
    (hm : frameMemory s f = some (a, m))
    (hb : Execution.Memory.readBytes m.data (effectiveAddress c ao) (v.type.width / 8) =
      some (Execution.Memory.encodeLE (v.type.width / 8) v.bits.toNat)) :
    Fires (simEnv10 (bytesB10 P)) "Step_read" 9
      (.tuple [configV hn ⟨s, f, code⟩, .list (adminsToV [value v])]) := by
  let σ := loadNumValScope (stateV hn s f) c ao v
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v.type) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV v) := rfl
  have hlhs : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE
      [.varE "z", .listE [constIE, .caseE "LOAD" (.tupE [.varE "t", .optE none, .varE "ao"])]]))
      (configV hn ⟨s, f, code⟩) := by
    rw [configV_eq_cfgV10, hcode]
    exact evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
      (evalExp_case (evalExp_tup3 (Sim.evalExp_var ft) (evalExp_optE_none_iff.2 rfl)
        (Sim.evalExp_var fa)))))
  have hrhs : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "t", .varE "c"])]) (.list (adminsToV [value v])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact evalExp_list1 (evalExp_case (evalExp_tup2 (Sim.evalExp_var ft) (Sim.evalExp_var fc)))
  have hprem : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "bytes_" [.expA (.varE "t"), .expA (.varE "c")])
        (loadSliceE10 sizeTE)) (.bool true) :=
    evalExp_eqTrue (evalExp_bytesCall10 rfl ft fc) (evalExp_loadSlice10 fz fi fa rfl
      (evalExp_size10 v.type rfl (Sim.evalExp_var ft)) (width_cases v.type) hm hb)
  exact fires_of_ruleAt (hasRuleAt10_loadNumVal' _) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons ft (typedV_valtype10 v.type _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fa (typedV_memarg10 ao _ ⟨rfl, rfl, rfl⟩)
          (QuantsOk.cons fc (hasTyp_valNum10 v (Sim.evalExp_var ft)) QuantsOk.nil)))))
    (evalExp_tup2 hlhs hrhs) (prems_one (.ifPr hprem))

/-! ## `load-pack-val` -/

/-- `iN(N)` holds every natural below `2 ^ N` in 1.0 (2.0's `hasTyp_iN_of_uN20`, ported). -/
theorem hasTyp_iN_of_uN10 {ρ : VarEnv} {e : Exp} {N n : Nat}
    (he : EvalExp (simEnv10 B) ρ e (Equiv.natV N)) (hn : n < 2 ^ N) :
    HasTyp (simEnv10 B) ρ (.varT "iN" [.expA e]) (pctV n) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_iN10 (B := B)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 (hasTyp_uN10 (Sim.evalExp_var (by simp)) hn)))

/-- The scope of `load-pack-val`. -/
abbrev loadPackValScope (z : Value) (c : BitVec 32) (t : IntType) (sz : V1.PackSize)
    (sx : Signedness) (ao : V1.MemArg) (k : Nat) : List (IL.Id × Value) :=
  [("z", z), ("i", pctV c.toNat), ("Inn", valTypeV (.int t)), ("n", .num (.natN sz.width)),
    ("sx", Sim20.sxV sx), ("ao", memargV ao), ("c", pctV k)]

/-- `$extend__(n, $size(Inn), sx, c)` is V1's extension, at `bytesB10`. -/
theorem evalExp_extend10 {P : Profile} {ρ : VarEnv} {t : IntType} {sz : V1.PackSize}
    {sx : Signedness} {x : BitVec sz.width}
    (hρ₁ : ρ.findDef? "extend__" = none) (hρ₂ : ρ.findDef? "size" = none)
    (fInn : ρ.findVal? "Inn" = some (valTypeV (.int t)))
    (fn : ρ.findVal? "n" = some (.num (.natN sz.width))) (fsx : ρ.findVal? "sx" = some (Sim20.sxV sx))
    (fc : ρ.findVal? "c" = some (pctV x.toNat)) :
    EvalExp (simEnv10 (bytesB10 P)) ρ extendE10 (pctV (extPack10 t sx x).toNat) := by
  have hsz : EvalExp (simEnv10 (bytesB10 P)) ρ (.callE "size" [.expA innE10])
      (.num (.natN t.width)) :=
    evalExp_size10 (.int t) hρ₂ (evalExp_subE_iff.2 (Sim.evalExp_var fInn))
  have hsx : Sim20.sxV sx = Sim.sxV sx := by cases sx <;> rfl
  have hc : Sim.Floats.floatCall P "extend__" [.val (Equiv.natV sz.width),
      .val (Equiv.natV t.width), .val (Sim.sxV sx), .val (pctV x.toNat)] =
      some (pctV (extPack10 t sx x).toNat) := by
    rw [Sim.Floats.floatCall_extend]
    cases sx <;> rfl
  refine evalExp_callE_iff.2 (callDef_floatPrim10 (floatB_bytesB10 P) ⟨_, _, rfl⟩ hρ₁
    (evalArgs_cons (Sim.evalExp_var fn) (evalArgs_cons hsz (evalArgs_cons (Sim.evalExp_var fsx)
      (evalArgs_cons (Sim.evalExp_var fc) evalArgs_nil)))) ?_)
  rw [hsx]
  exact hc

/-- **`load-pack-val` fires forward** at `bytesB10`, at a V1 read of the narrow value `x`. -/
theorem fires10_loadPackVal {P : Profile} {s : Store H} {f : Frame} {c : BitVec 32}
    {t : IntType} {sz : V1.PackSize} {sx : Signedness} {ao : V1.MemArg} {a : MemAddr}
    {m : MemInst} {x : BitVec sz.width}
    (hz : TypedV (simEnv10 (bytesB10 P)) stateT (stateV hn s f))
    (hc : TypedV (simEnv10 (bytesB10 P)) valI32T (pctV c.toNat))
    (hm : frameMemory s f = some (a, m))
    (hb : Execution.Memory.readBytes m.data (effectiveAddress c ao) (sz.width / 8) =
      some (Execution.Memory.encodeLE (sz.width / 8) x.toNat)) :
    Fires (simEnv10 (bytesB10 P)) "Step_read" 11 (.tuple [configV hn ⟨s, f, [value (.int .i32 c),
      .source (.intLoad t (some (sz, sx)) ao)]⟩,
      .list (adminsToV [value ⟨.int t, extPack10 t sx x⟩])]) := by
  let σ := loadPackValScope (stateV hn s f) c t sz sx ao x.toNat
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (valTypeV (.int t)) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fsx : (VarEnv.empty.bindVals σ).findVal? "sx" = some (Sim20.sxV sx) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) := rfl
  have hrhs : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [innE10, extendE10])])
      (.list (adminsToV [value ⟨.int t, extPack10 t sx x⟩])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (Sim.evalExp_var fInn))
      (evalExp_extend10 rfl rfl fInn fn fsx fc)))
  have hprem : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "ibytes_" [.expA (.varE "n"), .expA (.varE "c")])
        (loadSliceE10 (.varE "n"))) (.bool true) :=
    evalExp_eqTrue (evalExp_ibytesCall10 rfl fn fc) (evalExp_loadSlice10 fz fi fa rfl
      (Sim.evalExp_var fn) (packWidth10_cases sz) hm hb)
  exact fires_of_ruleAt (hasRuleAt10_loadPackVal' _) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fInn (typedV_inn10 t _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fn (typedV_n10 _ _ ⟨rfl, rfl, rfl⟩)
          (QuantsOk.cons fsx (typedV_sx10 sx _ ⟨rfl, rfl, rfl⟩)
            (QuantsOk.cons fa (typedV_memarg10 ao _ ⟨rfl, rfl, rfl⟩)
              (QuantsOk.cons fc (hasTyp_iN_of_uN10 (Sim.evalExp_var fn) x.isLt)
                QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_loadPackLhs10 fz fi fInn fn fsx fa) hrhs) (prems_one (.ifPr hprem))

/-! ## The loads, forward -/

/-- **A successful integer load, forward**, at `bytesB10`: `load-num-val` or `load-pack-val`. -/
theorem fwdAt10_intLoad_bytesB10 {P : Profile} (s : Store H) (f : Frame) (t : IntType)
    (packed : Option (V1.PackSize × Signedness)) (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr)
    (m : MemInst) (v : Execution.Runtime.Value) (hm : frameMemory s f = some (a, m))
    (hv : loadInt t packed m.data (effectiveAddress c arg) = some v) :
    FwdAt10 (bytesB10 P) hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩
      ⟨s, f, [value v]⟩ := by
  rcases packed with _ | ⟨sz, sx⟩
  · obtain ⟨b, rfl, hb⟩ := loadInt_none_some hv
    refine fwdAt10_of_sread fun hz hcode => sread10_of_fires (fires10_loadNumVal (v := ⟨.int t, b⟩)
      ?_ hz (typedV_head32_10 hcode) hm hb)
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  · obtain ⟨x, rfl, hb⟩ := loadPack_some hv
    exact fwdAt10_of_sread fun hz hcode =>
      sread10_of_fires (fires10_loadPackVal hz (typedV_head32_10 hcode) hm hb)

/-- **A successful float load, forward**, at `bytesB10`: `load-num-val`. -/
theorem fwdAt10_floatLoad_bytesB10 {P : Profile} (s : Store H) (f : Frame) (t : FloatType)
    (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value)
    (hm : frameMemory s f = some (a, m)) (hv : loadFloat t m.data (effectiveAddress c arg) = some v) :
    FwdAt10 (bytesB10 P) hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩
      ⟨s, f, [value v]⟩ := by
  obtain ⟨b, rfl, hb⟩ := loadFloat_some hv
  refine fwdAt10_of_sread fun hz hcode => sread10_of_fires (fires10_loadNumVal (v := ⟨.float t, b⟩)
    ?_ hz (typedV_head32_10 hcode) hm hb)
  rw [adminsToV_map10, List.map_cons, adminToV_value]
  rfl

/-- **`FwdLoads10` holds at `bytesB10`**: the last two forward obligations of the 1.0 half. -/
theorem fwdLoads10_bytesB10 (P : Profile) : FwdLoads10 (bytesB10 P) hn where
  intLoad s f t packed arg c a m v hm hv := fwdAt10_intLoad_bytesB10 s f t packed arg c a m v hm hv
  floatLoad s f t arg c a m v hm hv := fwdAt10_floatLoad_bytesB10 s f t arg c a m v hm hv

/-- **The forward 1.0 half at `bytesB10`, with no open obligation**: every V1 step from a
configuration with typed image, `Plain10` code, `GSetOk` and aligned memories is a step of the
1.0 script between the images. -/
theorem wholeStepFwd10_bytesB10'' {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (simEnv10 (bytesB10 (Profile.spec nd r))) hn c)
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store)
    (h : Step host c c') :
    SStepB (simEnv10 (bytesB10 (Profile.spec nd r))) (configV hn c) (configV hn c') :=
  wholeStepFwd10_bytesB10' (fwdLoads10_bytesB10 _) hc hpl hg hal h

end Silmaril.Wasm.SpecTec.Sim10.Whole
