module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.InitData

/-!
# Track r4-fwd: `array.new_data-oob` (`Step_read` 75), forward

The trap rule of `array.new_data`: `Expand` gives the element type, and
`i + n * $zsize(zt)/8 > |$data(z, y).BYTES|` is Core's out-of-bounds premise. `array.new_data-num`
(76) is not proved: its premise `$concatn_(byte, $zbytes_(zt, c)^n, $zsize(zt)/8) = …` needs
`$concatn_` evaluated over `n` chunks.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open RefsGC

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins} {H : Type} {hn : H → String}

/-- The bound of `array.new_data-oob`, `i + n * $zsize(zt)/8 > |$data(z, y).BYTES|`, evaluated. -/
theorem evalExp_newDataBound {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame}
    {y : DataIdx} {i n : BitVec 32} {zt : CStorageType} {da : Nat} {di : DataInst}
    (h0 : 0 < storageSize zt) (hdat : s.data? f y = some (da, di))
    (hz : EvalExp (simEnv B) ρ (.varE "z") (stateV hn s f))
    (hy : EvalExp (simEnv B) ρ (.varE "y") (Encode.toValue y))
    (hi : EvalExp (simEnv B) ρ (.varE "i") (pctV i.toNat))
    (hn' : EvalExp (simEnv B) ρ (.varE "n") (.num (.natN n.toNat)))
    (hzt : EvalExp (simEnv B) ρ (.varE "zt") (tyV zt)) :
    EvalExp (simEnv B) ρ (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT)
      (.projE (.uncaseE (.varE "i") "%") 0) (.cvtE (.binE .divOp (.numT .ratT)
        (.cvtE (.binE .mulOp (.numT .natT) (.varE "n") (.callE "zsize" [.expA (.varE "zt")]))
          .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.lenE (.dotE (.callE "data" [.expA (.varE "z"), .expA (.varE "y")]) "BYTES")))
      (.bool (decide (di.bytes.size < i.toNat + n.toNat * storageSize zt / 8))) := by
  have hsz := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "zsize")
    (evalArgs_cons hzt evalArgs_nil) (applies_zsize zt h0)
  have hmul := evalExp_mulNat (t := .numT .natT) hn' hsz
  have hdiv := evalExp_divBy8 (Dvd.dvd.mul_left (dvd_storageSize zt h0) _) hmul
  have hdata : EvalExp (simEnv B) ρ (.callE "data" [.expA (.varE "z"), .expA (.varE "y")])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.dataInstToValue di) := by
    obtain ⟨M, Ls, As, a, hS, hM, hA, ha, hr⟩ := Memory.dataAt_of_data? hn hdat
    exact State.evalExp_data (State.stateDefs_simEnv B) (Aggregates.findDef_none hρ _) hz hy hS hM
      hA ha hr
  have hlen := evalExp_len (evalExp_dot hdata (Memory.dataInstV_BYTES di))
  rw [Memory.bytesL_length] at hlen
  exact evalExp_cmpNat (evalExp_addNat (evalExp_unpct hi) hdiv) hlen
    (by simp [Num.cmp])

/-- **`array.new_data-oob` (`Step_read` rule 75), forward.** -/
theorem sread_arrayNewDataOob (R : RTyping (simEnv B)) (A : Aggregates.AggTypes (simEnv B))
    {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i n : BitVec 32} {da : Nat}
    {d : DefType} {m : Mutability} {zt : CStorageType} {di : DataInst}
    (hd : f.type? x = some d) (he : Expand d (.array (.field m zt)))
    (hdat : s.data? f y = some (da, di)) (h0 : 0 < storageSize zt)
    (h : di.bytes.size < i.toNat + n.toNat * storageSize zt / 8)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩)
      (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("n", .num (.natN n.toNat)), ("x", Encode.toValue x), ("y", Encode.toValue y),
    ("mut?", mutV m), ("zt", tyV zt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hb := evalExp_newDataBound (B := B) hρ h0 hdat (by eval_tac) (by eval_tac) (by eval_tac)
    (by eval_tac) (by eval_tac)
  rw [decide_eq_true h] at hb
  exact dderives_of_ruleAt (Aggregates.rd B).arrayNewDataOob σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) (QuantsOk.cons rfl (A.mut_ m _ hρ)
      (QuantsOk.cons rfl (A.storagetype _ _ hρ) QuantsOk.nil)))))))
    (by eval_tac)
    (prems_two (.rulePr evalArgs_nil (evalExp_expandArray hρ hd rfl rfl rfl rfl)
      (A.expand _ _ he)) (.ifPr hb))

/-- **`array.new_data-oob`, as a forward obligation.** -/
theorem fwd_arrayNewDataOob (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (A : Aggregates.AggTypes (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx}
    {i n : BitVec 32} {da : Nat} {d : DefType} {ft : CFieldType} {di : DataInst}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (h0 : 0 < storageSize (fieldStorage ft))
    (h : di.bytes.size < i.toNat + n.toNat * storageSize (fieldStorage ft) / 8) :
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩
      ⟨s, f, [.trap]⟩ := by
  obtain ⟨m, zt⟩ := ft
  exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
    sread_arrayNewDataOob R A hd he hdat h0 h hz

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
