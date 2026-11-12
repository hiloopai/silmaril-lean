module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdTable

/-!
# The 1.0 script forward at the load traps, `memory.size` and `memory.grow-fail`

* `fwdAt10_intLoadTrap`, `fwdAt10_floatLoadTrap`: `Step_read/load-num-trap` (8) and
  `load-pack-trap` (10). V1 traps when `loadInt`/`loadFloat` answer `none`, which happens exactly
  out of bounds (`oob_of_loadInt_none`, `oob_of_loadFloat_none`); that is the rules' premise
  `i + ao.OFFSET + w/8 > |$mem(z, 0).BYTES|`, evaluated with round 2's environment-generic lemmas.
  The quantifiers `t : valtype`, `Inn : Inn`, `n : n`, `sx : sx`, `ao : memarg` hold every V1
  operand (`typedV_inn10`, `typedV_sx10`, `typedV_memarg10`).
* `fwdAt10_memorySize`: `Step_read/memory.size` (12) answers `n` under
  `n * 64 * $Ki = |$mem(z, 0).BYTES|`. V1 answers `size m.data = m.data.size / 65536` truncated to
  32 bits. The two agree **only at a page-aligned memory of fewer than `2^32` pages**
  (`MemAligned10`): at a one-byte memory V1 answers 0 and no `n` satisfies the premise. So the
  `memorySize` field of `FwdRestQ10` is restated under `MemAligned10`, which V1's `grow?` keeps
  (it requires and preserves alignment, and caps the size at `65536` pages).
* `fwdAt10_memGrowFail`: `Step/memory.grow-fail` (12) has no premise; V1's `Grow.failure` writes
  the memory back unchanged (`setMemory_self`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress loadInt loadFloat setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst MemAddr)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV ValsOnly stateT evalExp_case evalExp_tup2
  evalExp_tup3 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one prems_nil)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memorySizeRule memGrowFailRule20 evalExp_constN
  evalExp_addNat20 evalExp_div8 evalExp_iPay evalExp_trapRhs cmpValues_gtOp_nat20 width_cases)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## The quantifier types -/

set_option maxRecDepth 8000000 in
theorem findTyp_memarg10 : (simEnv10 B).findTyp? "memarg" = some ([], [.instD [] []
    (.structT [.mk "ALIGN" (.varT "u32" []) [] [], .mk "OFFSET" (.varT "u32" []) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_Inn10 : (simEnv10 B).findTyp? "Inn" = some ([], [.instD [] [] (.variantT
    [.mk "I32" (.tupT []) [] [], .mk "I64" (.tupT []) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_sx10 : (simEnv10 B).findTyp? "sx" = some ([], [.instD [] [] (.variantT
    [.mk "U" (.tupT []) [] [], .mk "S" (.tupT []) [] []])]) := rfl

/-- `u32` holds every natural below `2^32`. -/
theorem typedV_u32_10 {k : Nat} (hk : k < 2 ^ 32) :
    TypedV (simEnv10 B) (.varT "u32" []) (pctV k) :=
  typedV_aliasG10 findTyp_u32_10 (hasTyp_uN10 evalExp_num hk)

/-- **Every V1 memory argument is a `memarg`.** -/
theorem typedV_memarg10 (a : V1.MemArg) : TypedV (simEnv10 B) (.varT "memarg" []) (memargV a) :=
  Sim20.Whole.typedV_structG findTyp_memarg10 (Sim20.Whole.hasTypFields_consG
    (typedV_u32_10 a.align.isLt) (Sim20.Whole.hasTypFields_oneG (typedV_u32_10 a.offset.isLt)))

/-- Every integer type is an `Inn`. -/
theorem typedV_inn10 (t : IntType) :
    TypedV (simEnv10 B) (.varT "Inn" []) (valTypeV (.int t)) := by
  cases t <;> exact Sim20.Pure.typedV_closedCase20 findTyp_Inn10 rfl hasTyp_tupT_nil

/-- Every signedness is an `sx`. -/
theorem typedV_sx10 (s : Signedness) : TypedV (simEnv10 B) (.varT "sx" []) (Sim20.sxV s) := by
  cases s <;> exact Sim20.Pure.typedV_closedCase20 findTyp_sx10 rfl hasTyp_tupT_nil

/-! ## V1 out of bounds -/

/-- `Memory.load` fails only out of bounds. -/
theorem oob_of_load_none {m : Execution.Memory.Bytes} {start count : Nat}
    (h : Execution.Memory.load m start count = none) : m.size < start + count := by
  by_contra hc
  simp [Execution.Memory.load, Execution.Memory.readBytes, Nat.le_of_not_lt hc] at h

/-- **`loadInt` answers `none` only out of bounds.** -/
theorem oob_of_loadInt_none {t : IntType} {p : Option (V1.PackSize × Signedness)}
    {m : Execution.Memory.Bytes} {start : Nat} (h : loadInt t p m start = none) :
    m.size < start + ((p.map (·.1.width)).getD t.width) / 8 := by
  rcases p with _ | ⟨q, sx⟩
  · exact oob_of_load_none (Option.map_eq_none_iff.1 h)
  · exact oob_of_load_none (Option.map_eq_none_iff.1 h)

/-- **`loadFloat` answers `none` only out of bounds.** -/
theorem oob_of_loadFloat_none {t : FloatType} {m : Execution.Memory.Bytes} {start : Nat}
    (h : loadFloat t m start = none) : m.size < start + t.width / 8 :=
  oob_of_load_none (Option.map_eq_none_iff.1 h)

/-! ## The trap premise, forward -/

/-- **The trap premise holds** out of bounds, at the 1.0 encoding. -/
theorem trapPrem10 {ρ : VarEnv} {e : Exp} {s : Store H} {f : Frame} {c : BitVec 32}
    {ao : V1.MemArg} {w : Nat} {a : MemAddr} {m : MemInst}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV c.toNat))
    (fa : ρ.findVal? "ao" = some (memargV ao)) (hρ : ρ.findDef? "mem" = none)
    (he : EvalExp (simEnv10 B) ρ e (.num (.natN w)))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress c ao + w / 8) :
    EvalExp (simEnv10 B) ρ (.cmpE .gtOp (.numT .natT) (Sim20.Whole.addrE (Sim20.Whole.div8E e))
      Sim20.Whole.memLenE) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_addNat20 (evalExp_addNat20 (evalExp_iPay fi)
    (evalExp_off10 fa)) (evalExp_div8 he hw), evalExp_memLen10 hρ fz hm,
    cmpValues_gtOp_nat20 hlt⟩

/-! ## `load-num-trap` -/

/-- The scope of `load-num-trap`. -/
abbrev loadNumScope (z : Value) (c : BitVec 32) (t : V1.ValType) (ao : V1.MemArg) :
    List (IL.Id × Value) :=
  [("z", z), ("i", pctV c.toNat), ("t", valTypeV t), ("ao", memargV ao)]

/-- **`load-num-trap` fires forward** out of bounds, at a load of type `t` without packing. -/
theorem fires10_loadNumTrap {s : Store H} {f : Frame} {c : BitVec 32} {t : V1.ValType}
    {ao : V1.MemArg} {a : MemAddr} {m : MemInst} {code : List Admin}
    (hcode : adminsToV code = [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]),
      .case "LOAD" (.tuple [valTypeV t, .opt none, memargV ao])])
    (hz : TypedV (simEnv10 B) stateT (stateV hn s f))
    (hc : TypedV (simEnv10 B) valI32T (pctV c.toNat)) (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress c ao + t.width / 8) :
    Fires (simEnv10 B) "Step_read" 8
      (.tuple [configV hn ⟨s, f, code⟩, .list (adminsToV [.trap])]) := by
  let σ := loadNumScope (stateV hn s f) c t ao
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV t) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have hlhs : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z",
      .listE [Sim20.Whole.constIE, .caseE "LOAD" (.tupE [.varE "t", .optE none, .varE "ao"])]]))
      (configV hn ⟨s, f, code⟩) := by
    rw [configV_eq_cfgV10, hcode]
    exact evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
      (evalExp_case (evalExp_tup3 (Sim.evalExp_var ft) (evalExp_optE_none_iff.2 rfl)
        (Sim.evalExp_var fa)))))
  exact fires_of_ruleAt (hasRuleAt10_loadNumTrap B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons ft (typedV_valtype10 t _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fa (typedV_memarg10 ao _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))
    (evalExp_tup2 hlhs evalExp_trapRhs)
    (prems_one (.ifPr (trapPrem10 fz fi fa rfl (evalExp_size10 t rfl (Sim.evalExp_var ft))
      (width_cases t) hm hlt)))

/-! ## `load-pack-trap` -/

/-- The scope of `load-pack-trap`. -/
abbrev loadPackScope (z : Value) (c : BitVec 32) (t : IntType) (sz : V1.PackSize)
    (sx : Signedness) (ao : V1.MemArg) : List (IL.Id × Value) :=
  [("z", z), ("i", pctV c.toNat), ("Inn", valTypeV (.int t)), ("n", .num (.natN sz.width)),
    ("sx", Sim20.sxV sx), ("ao", memargV ao)]

/-- The image of a packed load. -/
theorem adminsToV_loadPack10 (c : BitVec 32) (t : IntType) (sz : V1.PackSize) (sx : Signedness)
    (ao : V1.MemArg) :
    adminsToV [value (.int .i32 c), .source (.intLoad t (some (sz, sx)) ao)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]), .case "LOAD" (.tuple
        [valTypeV (.int t), .opt (some (.case "%_%" (.tuple [szV sz, Sim20.sxV sx]))),
          memargV ao])] := by
  rw [adminsToV_map10, List.map_cons, adminToV_value]
  rfl

/-- The left-hand side of `load-pack-trap`, evaluated. -/
theorem evalExp_loadPackLhs10 {ρ : VarEnv} {s : Store H} {f : Frame} {c : BitVec 32}
    {t : IntType} {sz : V1.PackSize} {sx : Signedness} {ao : V1.MemArg}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV c.toNat))
    (fInn : ρ.findVal? "Inn" = some (valTypeV (.int t)))
    (fn : ρ.findVal? "n" = some (.num (.natN sz.width))) (fsx : ρ.findVal? "sx" = some (Sim20.sxV sx))
    (fa : ρ.findVal? "ao" = some (memargV ao)) :
    EvalExp (simEnv10 B) ρ (.caseE "%;%" (.tupE [.varE "z", .listE [Sim20.Whole.constIE,
      .caseE "LOAD" (.tupE [innE10, .optE (some (.caseE "%_%" (.tupE [.caseE "%" (.tupE
        [.varE "n"]), .varE "sx"]))), .varE "ao"])]]))
      (configV hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t (some (sz, sx)) ao)]⟩) := by
  have hsz : EvalExp (simEnv10 B) ρ (.caseE "%" (.tupE [.varE "n"])) (szV sz) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (Sim.evalExp_var fn) evalExps_nil, rfl⟩)
  have hop : EvalExp (simEnv10 B) ρ (.optE (some (.caseE "%_%" (.tupE [.caseE "%" (.tupE
      [.varE "n"]), .varE "sx"])))) (.opt (some (.case "%_%" (.tuple [szV sz, Sim20.sxV sx])))) :=
    evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tup2 hsz (Sim.evalExp_var fsx)), rfl⟩
  rw [configV_eq_cfgV10, adminsToV_loadPack10]
  exact evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
    (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
    (evalExp_case (evalExp_tup3 (evalExp_subE_iff.2 (Sim.evalExp_var fInn)) hop
      (Sim.evalExp_var fa)))))

/-- **`load-pack-trap` fires forward** out of bounds. -/
theorem fires10_loadPackTrap {s : Store H} {f : Frame} {c : BitVec 32} {t : IntType}
    {sz : V1.PackSize} {sx : Signedness} {ao : V1.MemArg} {a : MemAddr} {m : MemInst}
    (hz : TypedV (simEnv10 B) stateT (stateV hn s f))
    (hc : TypedV (simEnv10 B) valI32T (pctV c.toNat)) (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress c ao + sz.width / 8) :
    Fires (simEnv10 B) "Step_read" 10 (.tuple [configV hn ⟨s, f, [value (.int .i32 c),
      .source (.intLoad t (some (sz, sx)) ao)]⟩, .list (adminsToV [.trap])]) := by
  let σ := loadPackScope (stateV hn s f) c t sz sx ao
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (valTypeV (.int t)) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fsx : (VarEnv.empty.bindVals σ).findVal? "sx" = some (Sim20.sxV sx) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  exact fires_of_ruleAt (hasRuleAt10_loadPackTrap B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fInn (typedV_inn10 t _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fn (typedV_n10 _ _ ⟨rfl, rfl, rfl⟩)
          (QuantsOk.cons fsx (typedV_sx10 sx _ ⟨rfl, rfl, rfl⟩)
            (QuantsOk.cons fa (typedV_memarg10 ao _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))))
    (evalExp_tup2 (evalExp_loadPackLhs10 fz fi fInn fn fsx fa) evalExp_trapRhs)
    (prems_one (.ifPr (trapPrem10 fz fi fa rfl (Sim.evalExp_var fn) (packWidth10_cases sz) hm
      hlt)))

/-! ## The load traps, forward -/

/-- The index of a typed `CONST I32 c; i` is a `val_(I32)`. -/
theorem typedV_head32_10 {c : BitVec 32} {i : V1.Instr}
    (h : TypedV (simEnv10 B) adminsT (.list (adminsToV [value (.int .i32 c), .source i]))) :
    TypedV (simEnv10 B) valI32T (pctV c.toNat) :=
  typedV_valI32_of_const10 (by
    have h' := typedV_head10 h
    rwa [adminToV_value] at h')

/-- **`load` of an integer out of bounds, forward**: `load-num-trap` or `load-pack-trap`. -/
theorem fwdAt10_intLoadTrap (s : Store H) (f : Frame) (t : IntType)
    (packed : Option (V1.PackSize × Signedness)) (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr)
    (m : MemInst) (hm : frameMemory s f = some (a, m))
    (hnone : loadInt t packed m.data (effectiveAddress c arg) = none) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩
      ⟨s, f, [.trap]⟩ := by
  have hlt := oob_of_loadInt_none hnone
  rcases packed with _ | ⟨sz, sx⟩
  · refine fwdAt10_of_sread fun hz hcode => sread10_of_fires (fires10_loadNumTrap (t := .int t)
      ?_ hz (typedV_head32_10 hcode) hm hlt)
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  · exact fwdAt10_of_sread fun hz hcode =>
      sread10_of_fires (fires10_loadPackTrap hz (typedV_head32_10 hcode) hm hlt)

/-- **`load` of a float out of bounds, forward**: `load-num-trap`. -/
theorem fwdAt10_floatLoadTrap (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg)
    (c : BitVec 32) (a : MemAddr) (m : MemInst) (hm : frameMemory s f = some (a, m))
    (hnone : loadFloat t m.data (effectiveAddress c arg) = none) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10_of_sread fun hz hcode => sread10_of_fires (fires10_loadNumTrap (t := .float t)
    ?_ hz (typedV_head32_10 hcode) hm (oob_of_loadFloat_none hnone))
  rw [adminsToV_map10, List.map_cons, adminToV_value]
  rfl

/-! ## `memory.size` -/

/-- **A page-aligned memory of fewer than `2^32` pages**: where V1's `memory.size` and the
script's agree. -/
def MemAligned10 (m : MemInst) : Prop :=
  m.data.size % Execution.Memory.pageSize = 0 ∧ Execution.Memory.size m.data < 2 ^ 32

/-- `n * 64 * $Ki` at `n = k`. -/
theorem evalExp_pages10 {ρ : VarEnv} {k : Nat} (fn : ρ.findVal? "n" = some (.num (.natN k)))
    (hρ : ρ.findDef? "Ki" = none) :
    EvalExp (simEnv10 B) ρ (.binE .mulOp (.numT .natT) (.binE .mulOp (.numT .natT) (.varE "n")
      (.numE (.natN 64))) (.callE "Ki" [])) (.num (.natN (k * 64 * 1024))) :=
  evalExp_binE_iff.2 ⟨.num (.natN (k * 64)), evalExp_binE_iff.2 ⟨_, Sim.evalExp_var fn, .inr ⟨rfl, _,
    evalExp_numE_iff.2 rfl, by simp [binValues, Num.bin, Res.ofOption]⟩⟩, .inr ⟨rfl, _,
    evalExp_ki10 hρ, by simp [binValues, Num.bin, Res.ofOption]⟩⟩

/-- **`memory.size` forward**, at a page-aligned memory of fewer than `2^32` pages. -/
theorem fwdAt10_memorySize (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst)
    (hm : frameMemory s f = some (a, m)) (hal : MemAligned10 m) :
    FwdAt10 B hn ⟨s, f, [.source .memorySize]⟩
      ⟨s, f, [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩ := by
  refine fwdAt10_of_sread fun hz _ => sread10_of_fires (k := 12) ?_
  set k := Execution.Memory.size m.data with hk
  have hkm : k * 64 * 1024 = m.data.size := by
    have h₁ := Nat.div_add_mod m.data.size Execution.Memory.pageSize
    have h₂ : m.data.size % Execution.Memory.pageSize = 0 := hal.1
    simp only [Execution.Memory.size, Execution.Memory.pageSize] at hk h₁ h₂ ⊢
    omega
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN k))]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN k)) := rfl
  have hrhs := adminsToV_memorySize (m := m) hkm hal.2
  erw [hrhs]
  exact fires_of_ruleAt (hasRuleAt10_memorySize B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fn (typedV_n10 _ _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (Sim.evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))))
      (evalExp_list1 (evalExp_constN fn)))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_pages10 fn rfl,
      evalExp_memLen10 rfl fz hm, cmpValues_eq_true_iff.2 (by rw [hkm])⟩)))

/-! ## `memory.grow-fail` -/

/-- **`memory.grow` failing, forward**: `Step/memory.grow-fail`, which has no premise. -/
theorem fwdAt10_memGrowFail (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst) (c : BitVec 32)
    (hm : frameMemory s f = some (a, m)) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
      ⟨setMemory s a {m with data := m.data}, f, [value (.int .i32 (-1))]⟩ := by
  rw [setMemory_self (frameMemory_some hm).2]
  intro hz _ _ _
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN c.toNat))]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN c.toNat)) := rfl
  have hlhs : configV hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list [.case "CONST" (.tuple [caseNilV "I32",
        pctV c.toNat]), caseNilV "MEMORY.GROW"]]) := by
    rw [configV_eq_cfgV10, adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) Sim20.Whole.growFailRhs
      (configV hn ⟨s, f, [value ⟨.int .i32, -1⟩]⟩) :=
    evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup2
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_minusOne10 rfl) evalExps_nil,
        rfl⟩))))))
  refine sstepB10_of_fires (k := 12) ?_
  rw [hlhs]
  exact fires_of_ruleAt (hasRuleAt10_memGrowFail B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fn (typedV_n10 _ _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (evalExp_case (evalExp_tupE_iff.2
        ⟨_, evalExps_cons (Sim.evalExp_var fn) evalExps_nil, rfl⟩))))
      Sim20.Pure.evalExp_caseNil))) he)
    prems_nil

end Silmaril.Wasm.SpecTec.Sim10.Whole
