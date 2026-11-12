module

public import Silmaril.Wasm.SpecTec.Sim.R4Fwd.Defs

/-!
# Track r4-fwd: `array.new_elem-alloc` (`Step_read` rule 74), forward

`z; (CONST I32 i) (CONST I32 n) (ARRAY.NEW_ELEM x y) ~> ref^n (ARRAY.NEW_FIXED x n)` with the
premise `ref^n = $elem(z, y).REFS[i : n]`. The quantifier `ref*` is instantiated at Core's
`(ei.refs.drop i).take n`; the slice is in bounds (`i + n ≤ |refs|`, Core's premise) and, since
upstream item U2, the evaluator's slice is defined there (`slice?_list`). No assumption beyond
family R's `RTyping` and `RStoreFuns` is used.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open RefsGC

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins} {H : Type} {hn : H → String}

/-- The admin images of a sequence of references. -/
theorem adminsToV_refs (rs : List Ref) : adminsToV (rs.map .ref) = rs.map refToValue := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, adminsToV, ih]; rfl

theorem adminsToV_app : ∀ (l r : List Admin), adminsToV (l ++ r) = adminsToV l ++ adminsToV r
  | [], _ => rfl
  | a :: l, r => by simp only [List.cons_append, adminsToV, adminsToV_app l r]

/-- **`array.new_elem-alloc` (`Step_read` rule 74), forward.** -/
theorem sread_arrayNewElemAlloc (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B))
    {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i n : BitVec 32} {ea : Nat}
    {ei : ElemInst} (he : s.elem? f y = some (ea, ei)) (h : i.toNat + n.toNat ≤ ei.refs.length)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewElem x y)]⟩)
      (adminsToV (((ei.refs.drop i.toNat).take n.toNat).map .ref ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])) := by
  have hlen : ((ei.refs.drop i.toNat).take n.toNat).length = n.toNat := by
    simp only [List.length_take, List.length_drop]; omega
  let rv : List Value := ((ei.refs.drop i.toNat).take n.toNat).map refToValue
  have hrv : rv.length = n.toNat := by rw [List.length_map]; exact hlen
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("n", .num (.natN n.toNat)), ("x", Encode.toValue x), ("y", Encode.toValue y),
    ("ref*", .list rv)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hn' : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN rv.length)) := by
    rw [hrv]; rfl
  have hd : (VarEnv.empty.bindVals σ).findVal? "ref*" = some (.list rv) := rfl
  have hit : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.iterE (.varE "ref") (.mk (.listN (.varE "n") none) [.mk "ref" (.varE "ref*")]))
      (.list rv) :=
    Equiv.ExecReadAggregate.evalExp_iterNVar (by decide) hn' hd
  have hcon : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.iterE (.subE (.varE "ref") (.varT "ref" []) (.varT "instr" []))
        (.mk (.listN (.varE "n") none) [.mk "ref" (.varE "ref*")])) (.list (rv.map id)) :=
    evalExp_iterNMap hn' hd fun w _ =>
      evalExp_sub_of (evalExp_var (findVal_bind1 (by decide)))
  have htyp : TypedV (simEnv B) (.iterT (.varT "ref" []) .list) (.list rv) :=
    typedV_list_iff.2 fun w hw => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hw
      exact Typing.typedV_ref r
  have hsl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.sliceE (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE "y")]) "REFS")
        (.projE (.uncaseE (.varE "i") "%") 0) (.varE "n")) (.list rv) :=
    evalExp_sliceE_iff.2 ⟨_, _, _, evalExp_elemRefs G hρ he (by eval_tac) (by eval_tac),
      evalExp_unpct (by eval_tac), by eval_tac,
      by rw [Equiv.ExecReadAggregate.slice?_list (by simpa using h)]
         simp [rv, List.map_drop, List.map_take]⟩
  have hout : adminsToV (((ei.refs.drop i.toNat).take n.toNat).map .ref ++
      [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]) =
      rv.map id ++ adminsToV [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)] := by
    rw [adminsToV_app, adminsToV_refs, List.map_id]
  rw [hout]
  exact dderives_of_ruleAt (Aggregates.rd B).arrayNewElemAlloc σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ)
      (QuantsOk.cons rfl (htyp _ hρ) QuantsOk.nil))))))
    (evalExp_tup2 (by eval_tac) (evalExp_cat hcon (by eval_tac)))
    (prems_one (.ifPr (evalExp_eq_true hit hsl)))

/-- **`array.new_elem-alloc`, as a forward obligation.** -/
theorem fwd_arrayNewElemAlloc (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i n : BitVec 32} {ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
    (h : i.toNat + n.toNat ≤ ei.refs.length) :
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewElem x y)]⟩
      ⟨s, f, ((ei.refs.drop i.toNat).take n.toNat).map .ref ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩ :=
  RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ => sread_arrayNewElemAlloc (x := x) (hn := hn) R G he h hz

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
