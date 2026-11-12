module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.LoadRules

/-!
# The store rules, for arbitrary state values

`Step/store-num-oob` (18) for every number type (`sstep_storeNumOob`; the integer case is the
memory track's `sstep_storeIntOob`, the float case is new), `Step/store-num-val` (19,
`sstep_storeNumVal`) and `Step/store-pack-val` (21, `sstep_storePackVal`), at `simEnv B`. The
written state is `$with_mem`'s (`evalExp_withMem`); the quantified `b*` is typed by
`hasTyp_bytes`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.ExecStepRules (storeNumOobRule storeNumValRule storePackValRule)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateDefs StateTyping GrowDefs)
open Memory (MemAt MemTyping)

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))

include St M in
/-- `Step/store-num-oob`, for every number type. -/
theorem sstep_storeNumOob (h : HasRuleAt (simEnv B) "Step" "%~>%" 18 storeNumOobRule)
    {S F m : Value} {bs : List Value} {a : AddrType} {i : BitVec a.intType.width} {v : NumVal}
    {n : Nat} {arg : MemArg} (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + v.type.width / 8) :
    SStep (simEnv B) (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        .case "CONST" (.tuple [Encode.toValue v.type, numV v]),
        .case "STORE" (.tuple [Encode.toValue v.type, .opt none, idxV n, memargV arg])])
      (cfgV (stV S F) [.case "TRAP" (.tuple [])]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("nt", Encode.toValue v.type), ("c", numV v),
    ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hcT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "num_" [.expA (.varE "nt")])
      (numV v) :=
    Typing.typedDep_num "nt" v _ hρ (by rw [← Typing.toValue_numType]; rfl)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.numtype _ _ hρ)
        (QuantsOk.cons rfl hcT (QuantsOk.cons rfl (St.idx n hn _ hρ)
          (QuantsOk.cons rfl (M.memarg arg _ hρ) QuantsOk.nil)))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
        (evalExp_widthNum (State.growDefs_simEnv B) (Memory.sizeDefs_simEnv B) v.type
          (evalExp_var rfl)))
      (Memory.evalExp_memBytesLen (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl)
        hm hB) hoob)))

include St M in
/-- `Step/store-num-val`: `z; (CONST at i) (CONST nt c) (STORE nt x ao) ~>
$with_mem(z, x, i + ao.OFFSET, $size(nt)/8, b*); ε` with `b* = $nbytes_(nt, c)`. -/
theorem sstep_storeNumVal (Bf : BytesFuns (simEnv B))
    (h : HasRuleAt (simEnv B) "Step" "%~>%" 19 storeNumValRule)
    {S F M' m m' S' : Value} {Ls As bs : List Value} {ma : Nat} {a : AddrType}
    {i : BitVec a.intType.width} {v : NumVal} {n : Nat} {arg : MemArg}
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hS : S.field? "MEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M')
    (hA : M'.field? "MEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN ma)))
    (hm : Ls[ma]? = some m) (hB : m.field? "BYTES" = some (.list bs))
    (hsl : SliceAt bs (i.toNat + arg.offset.val) (v.type.width / 8))
    (hm' : m.setField "BYTES" (.list (bs.take (i.toNat + arg.offset.val) ++
      leBytesV (v.type.width / 8) v.bits.toNat ++
      bs.drop (i.toNat + arg.offset.val + v.type.width / 8))) = some m')
    (hS' : S.setField "MEMS" (.list (Ls.set ma m')) = some S') :
    SStep (simEnv B) (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        .case "CONST" (.tuple [Encode.toValue v.type, numV v]),
        .case "STORE" (.tuple [Encode.toValue v.type, .opt none, idxV n, memargV arg])])
      (cfgV (stV S' F) []) := by
  let ws := leBytesV (v.type.width / 8) v.bits.toNat
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("nt", Encode.toValue v.type), ("c", numV v),
    ("x", idxV n), ("ao", memargV arg), ("b*", .list ws)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hcT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "num_" [.expA (.varE "nt")])
      (numV v) :=
    Typing.typedDep_num "nt" v _ hρ (by rw [← Typing.toValue_numType]; rfl)
  have hbT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.iterT (.varT "byte" []) .list)
      (.list ws) := hasTyp_bytes hρ _
  have hw := evalExp_widthNum (σ := σ) (State.growDefs_simEnv B) (Memory.sizeDefs_simEnv B)
    v.type (evalExp_var rfl)
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "nbytes_" [.expA (.varE "nt"), .expA (.varE "c")]) (.list ws) :=
    evalExp_call_applies (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl)
      evalArgs_nil)) (Bf.nbytes v)
  have ewm := evalExp_withMem (ez := .varE "z") (ex := .varE "x") (eb := State.iterVar "b" "b*")
    (State.stateDefs_simEnv B) (withMemDef_simEnv B)
    (Memory.findDef_bindVals_empty σ _) (evalExp_var rfl) (evalExp_var rfl)
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl)) hw
    (Equiv.Execution.evalExp_iterPat (by decide) rfl) hS hM hA ha hm hB (hsl.2 ws) hm' hS'
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.numtype _ _ hρ)
        (QuantsOk.cons rfl hcT (QuantsOk.cons rfl (St.idx n hn _ hρ)
          (QuantsOk.cons rfl (M.memarg arg _ hρ) (QuantsOk.cons rfl hbT QuantsOk.nil))))))))
    (evalExp_tup2 (by mem_eval_tac) (evalExp_case (evalExp_tup2 ewm
      (RefsGC.evalExp_listE_of RefsGC.evalExps_nil'))))
    (prems_one (.ifPr (RefsGC.evalExp_eq_true
      (Equiv.Execution.evalExp_iterPat (by decide) rfl) e₁)))

include St M in
/-- `Step/store-pack-val`: as `store-num-val`, with `b* = $ibytes_(n, $wrap__($size(Inn), n, c))`;
`k` is `$wrap__`'s answer (`hwr`). -/
theorem sstep_storePackVal (Bf : BytesFuns (simEnv B))
    (h : HasRuleAt (simEnv B) "Step" "%~>%" 21 storePackValRule)
    {S F M' m m' S' : Value} {Ls As bs : List Value} {ma : Nat} {a : AddrType}
    {i : BitVec a.intType.width} {t : IntType} {c : BitVec t.width} {sz : PackSize} {n k : Nat}
    {arg : MemArg} (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hS : S.field? "MEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M')
    (hA : M'.field? "MEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN ma)))
    (hm : Ls[ma]? = some m) (hB : m.field? "BYTES" = some (.list bs))
    (hsl : SliceAt bs (i.toNat + arg.offset.val) (sz.width / 8))
    (hm' : m.setField "BYTES" (.list (bs.take (i.toNat + arg.offset.val) ++
      leBytesV (sz.width / 8) k ++ bs.drop (i.toNat + arg.offset.val + sz.width / 8))) = some m')
    (hS' : S.setField "MEMS" (.list (Ls.set ma m')) = some S')
    (hwr : ∀ σ : List (IL.Id × Value), (∀ y, (VarEnv.empty.bindVals σ).findDef? y = none) →
      (VarEnv.empty.bindVals σ).findVal? "n" = some (natV sz.width) →
      (VarEnv.empty.bindVals σ).findVal? "Inn" = some (Encode.toValue (NumType.int t)) →
      (VarEnv.empty.bindVals σ).findVal? "c" = some (idxV c.toNat) →
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.callE "wrap__" [.expA (.callE "size"
          [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))]), .expA (.varE "n"),
          .expA (.varE "c")]) (pctV k)) :
    SStep (simEnv B) (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        aconstV (Encode.toValue (NumType.int t)) c.toNat,
        .case "STORE" (.tuple [Encode.toValue (NumType.int t),
          .opt (some (.case "%" (.tuple [szV sz]))), idxV n, memargV arg])])
      (cfgV (stV S' F) []) := by
  let ws := leBytesV (sz.width / 8) k
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("Inn", Encode.toValue (NumType.int t)), ("c", idxV c.toNat),
    ("n", .num (.natN sz.width)), ("x", idxV n), ("ao", memargV arg), ("b*", .list ws)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hbT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.iterT (.varT "byte" []) .list)
      (.list ws) := hasTyp_bytes hρ _
  have hw := Memory.evalExp_div8 (ρ := VarEnv.empty.bindVals σ) (env := simEnv B)
    (by cases sz <;> simp [PackSize.width]) (evalExp_var (x := "n") rfl)
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "ibytes_" [.expA (.varE "n"), .expA (.callE "wrap__" [.expA (.callE "size"
          [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))]), .expA (.varE "n"),
          .expA (.varE "c")])]) (.list ws) :=
    evalExp_call_applies (evalArgs_cons (evalExp_var rfl) (evalArgs_cons
      (hwr σ (Memory.findDef_bindVals_empty σ) rfl rfl rfl) evalArgs_nil)) (Bf.ibytes sz.width k)
  have ewm := evalExp_withMem (ez := .varE "z") (ex := .varE "x") (eb := State.iterVar "b" "b*")
    (State.stateDefs_simEnv B) (withMemDef_simEnv B)
    (Memory.findDef_bindVals_empty σ _) (evalExp_var rfl) (evalExp_var rfl)
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl)) hw
    (Equiv.Execution.evalExp_iterPat (by decide) rfl) hS hM hA ha hm hB (hsl.2 ws) hm' hS'
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.inn t _ hρ)
        (QuantsOk.cons rfl (M.numInn "Inn" t c _ hρ rfl) (QuantsOk.cons rfl (St.nat _ _ hρ)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            (QuantsOk.cons rfl hbT QuantsOk.nil)))))))))
    (evalExp_tup2 (by mem_eval_tac) (evalExp_case (evalExp_tup2 ewm
      (RefsGC.evalExp_listE_of RefsGC.evalExps_nil'))))
    (prems_one (.ifPr (RefsGC.evalExp_eq_true
      (Equiv.Execution.evalExp_iterPat (by decide) rfl) e₁)))

end Silmaril.Wasm.SpecTec.Sim.FwdMem
