module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.AggRead

/-!
# Round 5: `Aggregates/Struct.lean` on bounded types

A copy of the aggregate lemmas of `Aggregates/Struct.lean` that take `Aggregates.AggTypes`, each renamed with a
suffix `B`, taking `AggTypesB` (the bounded restatement) and a local instance
`Fact (Round4.ModuleBnd f.module)`; the bounds are discharged by `AggTypesB`'s auto-parameters.
The proofs are otherwise unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV tyV_list)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.ExecStepRules
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open RefsGC

open Aggregates

variable {env : Env} {B : Builtins} {H : Type} {hn : H → String} {P : Numerics.Profile}

/-- **`struct.get-struct` (rule 71), forward, for an unpacked field.** -/
theorem sread_structGetStructValB (h₀ : HasRuleAt env "Step_read" "%~>%" 71 structGetStructRule)
    (R : RTyping env) (D : AggDefs env) (SD : State.StateDefs env) (A : AggTypesB env)
    (U : UnpackDef env) {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {i : FieldIdx} {a : Nat}
    {si : StructInst} {v : Val} {d : DefType} {fs : Ty (.list .field)} {m : Mutability}
    {t : CValType} (hs : s.structs[a]? = some si) (hf : si.fields[i.toNat]? = some (.val v))
    (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hi : fs.toList[i.toNat]? = some (.field m (.val t)))
    (hz : TypedV env stateT (stateV hn s f)) :
    SRead env (configV hn ⟨s, f, [.ref (.struct a), .plain (.structGet none x i)]⟩)
      (adminsToV [v.toAdmin]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("sx?", .opt none), ("x", Encode.toValue x), ("i", Encode.toValue i),
    ("zt*", .list (fs.toList.map (tyV ∘ fieldStorage))),
    ("mut?*", .list (fs.toList.map (mutV ∘ fieldMut)))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hii : EvalExp env (VarEnv.empty.bindVals σ) (.projE (.uncaseE (.varE "i") "%") 0)
      (.num (.natN i.toNat)) := evalExp_unpct (by eval_tac)
  have hfv : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.dotE (.idxE (.callE "structinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
        (.projE (.uncaseE (.varE "i") "%") 0)) (valV v) :=
    evalExp_idx (evalExp_structFieldsAt D hρ (by eval_tac) (by eval_tac) hs) hii
      (by simp [hf, fieldValV])
  have hzt : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.iterE (.varE "zt") (.mk .list [.mk "zt" (.varE "zt*")]))
        (.projE (.uncaseE (.varE "i") "%") 0)) (tyV (Ty.val t : CStorageType)) :=
    evalExp_idx (by eval_tac) hii (by simp [hi, fieldStorage])
  have hun : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "unpackfield_" [.expA (.idxE (.iterE (.varE "zt") (.mk .list [.mk "zt" (.varE "zt*")]))
          (.projE (.uncaseE (.varE "i") "%") 0)),
        .expA (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")])),
        .expA (.idxE (.dotE (.idxE (.callE "structinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
          (.projE (.uncaseE (.varE "i") "%") 0))]) (valV v) :=
    evalExp_unpackfield U (findDef_none hρ _) hzt (by eval_tac) hfv
  obtain ⟨tz, tm⟩ := typed_fieldListsB A fs.toList
  refine dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.sxOpt none _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.fieldidx _ i.value.isLt _ hρ) (QuantsOk.cons rfl (tz _ hρ)
      (QuantsOk.cons rfl (tm _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_list1 (evalExp_sub_of ?_)))
    (prems_one (.rulePr evalArgs_nil (evalExp_expandStruct D SD hρ hd rfl rfl rfl rfl)
      (A.expand _ _ he)))
  rw [adminToV_toAdmin]
  exact hun

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
