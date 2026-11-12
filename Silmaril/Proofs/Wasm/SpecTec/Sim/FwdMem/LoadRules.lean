module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.Eval
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms

/-!
# The value load rules, for arbitrary state values

`Step_read/load-num-val` (39), for integer and float number types alike (`sread_loadNumVal`), and
`Step_read/load-pack-val` (41, `sread_loadPackVal`), constructed at `simEnv B` for a state value
whose memory at `x` has bytes `bs`. The premise `$nbytes_(nt, c) = bs[ea : k]` (or
`$ibytes_(n, c) = …`) is discharged by `BytesFuns` and the slice `SliceAt bs ea k`; the loaded
constant `c` is typed by the typing track's `typedDep_num` (or `hasTyp_iN_var`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateDefs StateTyping GrowDefs)
open Memory (MemAt MemTyping)

/-- `$size(nt) / 8`, for every number type. -/
theorem evalExp_widthNum {env : Env} (G : GrowDefs env) (Z : Memory.SizeDefs env)
    {σ : List (IL.Id × Value)} (t : NumType)
    (hnt : EvalExp env (VarEnv.empty.bindVals σ) (.varE "nt") (Encode.toValue t)) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (t.width / 8))) := by
  cases t with
  | int t => exact Memory.evalExp_widthInt G t hnt
  | float t =>
    exact Memory.evalExp_div8 (by cases t <;> decide)
      (Memory.evalExp_sizeFloat Z (Memory.findDef_bindVals_empty σ _) t hnt)

/-- A call answered by `Applies`, in a scope of term variables built by `bindVals`. -/
theorem evalExp_call_applies {env : Env} {σ : List (IL.Id × Value)} {x : IL.Id} {args : List Arg}
    {ws : List ArgV} {v : Value} (ha : EvalArgs env (VarEnv.empty.bindVals σ) args ws)
    (h : Silmaril.SpecTec.Equiv.ExecNumeric.Applies env x ws v) :
    EvalExp env (VarEnv.empty.bindVals σ) (.callE x args) v :=
  evalExp_callE_iff.2
    ((Silmaril.SpecTec.Equiv.ExecNumeric.applies_iff_callDef
      (Memory.findDef_bindVals_empty σ _) ha).1 h)

/-- The slice `$mem(z, x).BYTES[ea : k]`. -/
theorem evalExp_memSlice {env : Env} (D : StateDefs env) {σ : List (IL.Id × Value)}
    {ez ex ei ek : Exp} {S F m : Value} {bs : List Value} {n ea k : Nat}
    (hz : EvalExp env (VarEnv.empty.bindVals σ) ez (stV S F))
    (hx : EvalExp env (VarEnv.empty.bindVals σ) ex (idxV n)) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hi : EvalExp env (VarEnv.empty.bindVals σ) ei (.num (.natN ea)))
    (hk : EvalExp env (VarEnv.empty.bindVals σ) ek (.num (.natN k))) (hsl : SliceAt bs ea k) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.sliceE (.dotE (.callE "mem" [.expA ez, .expA ex]) "BYTES") ei ek)
      (.list ((bs.drop ea).take k)) :=
  evalExp_sliceE_iff.2 ⟨_, ea, k, RefsGC.evalExp_dot (Memory.evalExp_mem_of D hz hx hm) hB, hi, hk,
    hsl.1⟩

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))
  (Bf : BytesFuns (simEnv B))

include St M Bf in
/-- `Step_read/load-num-val`: `z; (CONST at i) (LOAD nt x ao) ~> (CONST nt c)` when
`$nbytes_(nt, c) = $mem(z, x).BYTES[i + ao.OFFSET : $size(nt)/8]`. -/
theorem sread_loadNumVal (h : HasRuleAt (simEnv B) "Step_read" "%~>%" 39 loadNumValRule)
    {S F m : Value} {bs : List Value} {a : AddrType} {i : BitVec a.intType.width} {v : NumVal}
    {n : Nat} {arg : MemArg} (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hsl : SliceAt bs (i.toNat + arg.offset.val) (v.type.width / 8))
    (hc : leBytesV (v.type.width / 8) v.bits.toNat =
      (bs.drop (i.toNat + arg.offset.val)).take (v.type.width / 8)) :
    SRead (simEnv B) (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        .case "LOAD" (.tuple [Encode.toValue v.type, .opt none, idxV n, memargV arg])])
      [.case "CONST" (.tuple [Encode.toValue v.type, numV v])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("nt", Encode.toValue v.type), ("x", idxV n),
    ("ao", memargV arg), ("c", numV v)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hcT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "num_" [.expA (.varE "nt")])
      (numV v) :=
    Typing.typedDep_num "nt" v _ hρ (by rw [← Typing.toValue_numType]; rfl)
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")])
      (.list (leBytesV (v.type.width / 8) v.bits.toNat)) :=
    evalExp_call_applies (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl)
      evalArgs_nil)) (Bf.nbytes v)
  have e₂ := evalExp_memSlice (σ := σ) (ez := .varE "z") (ex := .varE "x")
    (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl) hm hB
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
    (evalExp_widthNum (State.growDefs_simEnv B) (Memory.sizeDefs_simEnv B) v.type
      (evalExp_var rfl)) hsl
  rw [← hc] at e₂
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.numtype _ _ hρ)
        (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
          (QuantsOk.cons rfl hcT QuantsOk.nil)))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_eq_true e₁ e₂)))

include St M Bf in
/-- `Step_read/load-pack-val`: `z; (CONST at i) (LOAD Inn (n _ sx) x ao) ~>
(CONST Inn $extend__(n, $size(Inn), sx, c))` when `$ibytes_(n, c) = $mem(z, x).BYTES[… : n/8]`.
The result `r` is `$extend__`'s answer (`hr`). -/
theorem sread_loadPackVal (h : HasRuleAt (simEnv B) "Step_read" "%~>%" 41 loadPackValRule)
    {S F m r : Value} {bs : List Value} {a : AddrType} {i : BitVec a.intType.width}
    {t : IntType} {sz : PackSize} {sx : Signedness} {n k : Nat} {arg : MemArg}
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs)) (hk : k < 2 ^ sz.width)
    (hsl : SliceAt bs (i.toNat + arg.offset.val) (sz.width / 8))
    (hc : leBytesV (sz.width / 8) k = (bs.drop (i.toNat + arg.offset.val)).take (sz.width / 8))
    (hr : ∀ σ : List (IL.Id × Value), (∀ y, (VarEnv.empty.bindVals σ).findDef? y = none) →
      (VarEnv.empty.bindVals σ).findVal? "n" = some (natV sz.width) →
      (VarEnv.empty.bindVals σ).findVal? "Inn" = some (Encode.toValue (NumType.int t)) →
      (VarEnv.empty.bindVals σ).findVal? "sx" = some (sxV sx) →
      (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV k) →
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.callE "extend__" [.expA (.varE "n"), .expA (.callE "size"
          [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))]), .expA (.varE "sx"),
          .expA (.varE "c")]) r) :
    SRead (simEnv B) (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        .case "LOAD" (.tuple [Encode.toValue (NumType.int t),
          .opt (some (.case "%_%" (.tuple [szV sz, sxV sx]))), idxV n, memargV arg])])
      [.case "CONST" (.tuple [Encode.toValue (NumType.int t), r])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("Inn", Encode.toValue (NumType.int t)), ("n", .num (.natN sz.width)),
    ("sx", sxV sx), ("x", idxV n), ("ao", memargV arg), ("c", pctV k)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hcT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "iN" [.expA (.varE "n")])
      (pctV k) := hasTyp_iN_var rfl hk
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "ibytes_" [.expA (.varE "n"), .expA (.varE "c")])
      (.list (leBytesV (sz.width / 8) k)) :=
    evalExp_call_applies (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl)
      evalArgs_nil)) (Bf.ibytes sz.width k)
  have e₂ := evalExp_memSlice (σ := σ) (ez := .varE "z") (ex := .varE "x")
    (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl) hm hB
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
    (Memory.evalExp_div8 (e := .varE "n") (by cases sz <;> simp [PackSize.width])
      (evalExp_var rfl)) hsl
  rw [← hc] at e₂
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.inn t _ hρ)
        (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (M.sx sx _ hρ)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            (QuantsOk.cons rfl hcT QuantsOk.nil)))))))))
    (evalExp_tup2 (by mem_eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons'
      (evalExp_case (evalExp_tup2 (RefsGC.evalExp_sub_of (evalExp_var rfl))
        (hr σ (Memory.findDef_bindVals_empty σ) rfl rfl rfl rfl)))
      RefsGC.evalExps_nil')))
    (prems_one (.ifPr (RefsGC.evalExp_eq_true e₁ e₂)))

end Silmaril.Wasm.SpecTec.Sim.FwdMem
