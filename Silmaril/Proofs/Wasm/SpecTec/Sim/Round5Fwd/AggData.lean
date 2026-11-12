module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.AggCopy

/-!
# Round 5: `R4Fwd/NewData.lean` on bounded types

A copy of the aggregate lemmas of `R4Fwd/NewData.lean` that take `Aggregates.AggTypes`, each renamed with a
suffix `B`, taking `AggTypesB` (the bounded restatement) and a local instance
`Fact (Round4.ModuleBnd f.module)`; the bounds are discharged by `AggTypesB`'s auto-parameters.
The proofs are otherwise unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

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

open R4Fwd

variable {env : Env} {B : Builtins} {H : Type} {hn : H → String} {P : Numerics.Profile}

/-- **`array.new_data-oob` (`Step_read` rule 75), forward.** -/
theorem sread_arrayNewDataOobB (R : RTyping (simEnv B)) (A : AggTypesB (simEnv B))
    {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {y : DataIdx} {i n : BitVec 32} {da : Nat}
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
theorem fwd_arrayNewDataOobB (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (A : AggTypesB (simEnv B)) {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {y : DataIdx}
    {i n : BitVec 32} {da : Nat} {d : DefType} {ft : CFieldType} {di : DataInst}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (h0 : 0 < storageSize (fieldStorage ft))
    (h : di.bytes.size < i.toNat + n.toNat * storageSize (fieldStorage ft) / 8) :
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩
      ⟨s, f, [.trap]⟩ := by
  obtain ⟨m, zt⟩ := ft
  exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
    sread_arrayNewDataOobB R A hd he hdat h0 h hz

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
