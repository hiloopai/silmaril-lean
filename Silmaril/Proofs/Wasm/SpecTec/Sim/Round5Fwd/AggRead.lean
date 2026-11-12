module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.AggBase

/-!
# Round 5: `Aggregates/Read.lean` on bounded types

A copy of the aggregate lemmas of `Aggregates/Read.lean` that take `Aggregates.AggTypes`, each renamed with a
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
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open RefsGC

open Aggregates

variable {env : Env} {B : Builtins} {H : Type} {hn : H → String} {P : Numerics.Profile}

/-- **`array.get-array` (rule 79), forward, for an unpacked field.** -/
theorem sread_arrayGetArrayValB (h₀ : HasRuleAt env "Step_read" "%~>%" 79 arrayGetArrayRule)
    (R : RTyping env) (D : AggDefs env) (SD : State.StateDefs env) (A : AggTypesB env)
    (U : UnpackDef env) {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {i : BitVec 32} {a : Nat}
    {ai : ArrayInst} {v : Val} {d : DefType} {m : Mutability} {t : CValType}
    (ha : s.arrays[a]? = some ai) (hf : ai.fields[i.toNat]? = some (.val v))
    (hd : f.type? x = some d) (he : Expand d (.array (.field m (.val t))))
    (hz : TypedV env stateT (stateV hn s f)) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet none x)]⟩)
      (adminsToV [v.toAdmin]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("sx?", .opt none), ("x", Encode.toValue x),
    ("zt", tyV (Ty.val t : CStorageType)), ("mut?", mutV m)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hfv : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
        (.projE (.uncaseE (.varE "i") "%") 0)) (valV v) :=
    evalExp_idx (evalExp_arrayFieldsAt D hρ (by eval_tac) (by eval_tac) ha)
      (evalExp_unpct (by eval_tac)) (by simp [hf, fieldValV])
  have hun : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "unpackfield_" [.expA (.varE "zt"),
        .expA (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")])),
        .expA (.idxE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
          (.projE (.uncaseE (.varE "i") "%") 0))]) (valV v) :=
    evalExp_unpackfield U (findDef_none hρ _) (by eval_tac) (by eval_tac) hfv
  have hty := evalExp_type D SD (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x")
    (by eval_tac) (by eval_tac)
  have hex : EvalExp env (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m (Ty.val t)).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  refine dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.sxOpt none _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
      (QuantsOk.cons rfl (A.mut_ m _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_list1 (evalExp_sub_of ?_)))
    (prems_one (.rulePr evalArgs_nil hex (A.expand _ _ he)))
  rw [adminToV_toAdmin]
  exact hun

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
