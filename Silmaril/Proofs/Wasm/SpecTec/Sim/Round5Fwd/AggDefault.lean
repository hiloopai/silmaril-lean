module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.AggAlloc

/-!
# Round 5: `R4Fwd/PackedDefault.lean` on bounded types

A copy of the aggregate lemmas of `R4Fwd/PackedDefault.lean` that take `Aggregates.AggTypes`, each renamed with a
suffix `B`, taking `AggTypesB` (the bounded restatement) and a local instance
`Fact (Round4.ModuleBnd f.module)`; the bounds are discharged by `AggTypesB`'s auto-parameters.
The proofs are otherwise unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Aggregates (fieldMut evalExp_expandStruct  aggDefs_simEnv
  iterRows_pair)
open RefsGC (RTyping evalExp_tupE_of evalExps_cons' evalExps_nil')
open FwdSimdAgg (forall₂_of_mapM forall₂_mem_zip typedV_vals)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins} {H : Type} {hn : H → String}

open R4Fwd

variable {env : Env} {B : Builtins} {H : Type} {hn : H → String} {P : Numerics.Profile}

set_option maxHeartbeats 400000 in
/-- **`struct.new_default` (`Step_read` rule 69), forward, at every field storage type.** -/
theorem sread_structNewDefaultAnyB (R : RTyping (simEnv B)) (A : AggTypesB (simEnv B))
    {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hdef : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some vs)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [.plain (.structNewDefault x)]⟩)
      (adminsToV (vals vs ++ [.plain (.structNew x)])) := by
  have hF := FwdSimdAgg.forall₂_of_mapM hdef
  have hlen : fs.toList.length = vs.length := hF.length_eq
  let ps := fs.toList.zip vs
  have hp₁ : ps.map Prod.fst = fs.toList := List.map_fst_zip (le_of_eq hlen)
  have hp₂ : ps.map Prod.snd = vs := List.map_snd_zip (le_of_eq hlen.symm)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", Encode.toValue x),
    ("val*", .list (vs.map valV)), ("mut?*", .list (fs.toList.map (mutV ∘ fieldMut))),
    ("zt*", .list (fs.toList.map (tyV ∘ fieldStorage)))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hlhs : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
        (.mk .list [.mk "val" (.varE "val*")])) (.list ((vs.map valV).map id)) :=
    evalExp_iterMap rfl fun _ _ => RefsGC.evalExp_sub_of (evalExp_var rfl)
  have hvals : vs.map valV = ps.map (valV ∘ Prod.snd) := by
    rw [← List.map_map, hp₂]
  have hzts : fs.toList.map (tyV ∘ fieldStorage) = ps.map (tyV ∘ fieldStorage ∘ Prod.fst) := by
    conv_lhs => rw [← hp₁, List.map_map]
    rfl
  have hdoms : EvalDoms (simEnv B) (VarEnv.empty.bindVals σ)
      [.mk "val" (.varE "val*"), .mk "zt" (.varE "zt*")]
      [("val", .list (vs.map valV)), ("zt", .list (fs.toList.map (tyV ∘ fieldStorage)))] :=
    have hy₁ : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (vs.map valV)) := rfl
    have hy₂ : (VarEnv.empty.bindVals σ).findVal? "zt*" =
        some (.list (fs.toList.map (tyV ∘ fieldStorage))) := rfl
    ⟨3, by simp [evalDoms, domVar, domSrc, evalExp, hy₁, hy₂]⟩
  have hrow : ∀ r ∈ iterRows [("val", ps.map (valV ∘ Prod.snd)),
      ("zt", ps.map (tyV ∘ fieldStorage ∘ Prod.fst))] none ps.length,
      DPrem (simEnv B) (otherwise (simEnv B)) (otherwise (simEnv B) "Step_read" [] 69
        (.tuple [configV hn ⟨s, f, [.plain (.structNewDefault x)]⟩,
          .list (vs.map valV ++ [.case "STRUCT.NEW" (Encode.toValue x)])]))
        ((VarEnv.empty.bindVals σ).bindVals r)
        (.ifPr (.cmpE .eqOp .boolT (.callE "default_" [.expA (.callE "unpack"
          [.expA (.varE "zt")])]) (.optE (some (.varE "val"))))) := by
    intro r hr
    rw [iterRows_pair] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    have hdp : defaultVal? (fieldStorage p.1).unpack = some p.2 := forall₂_mem_zip hF p hp
    exact .ifPr (evalExp_defaultUnpack_any (zt := fieldStorage p.1) ⟨rfl, rfl, rfl⟩
      (by simp only [Function.comp_apply]; rfl) rfl hdp)
  obtain ⟨tz, tm⟩ := typed_fieldListsB A fs.toList
  have key := dderives_of_ruleAt (O := otherwise (simEnv B))
    ((Aggregates.rd B).structNewDefault) σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (typedV_vals vs _ hρ) (QuantsOk.cons rfl (tm _ hρ)
      (QuantsOk.cons rfl (tz _ hρ) QuantsOk.nil)))))
    (evalExp_tup2 (by eval_tac) (evalExp_cat (by simpa using hlhs) (by eval_tac)))
    (prems_two (.rulePr evalArgs_nil
        (evalExp_expandStruct (aggDefs_simEnv B) (State.stateDefs_simEnv B) hρ hd rfl rfl rfl rfl)
        (A.expand _ _ he))
      (.iterList (.inl rfl) hdoms (by simp) (by simp [domLists, Value.asList?, hvals, hzts])
        (by simp) hrow))
  have e₁ : adminsToV (vals vs ++ [.plain (.structNew x)]) =
      vs.map valV ++ [.case "STRUCT.NEW" (Encode.toValue x)] := by
    rw [Sim.adminsToV_append, Sim.adminsToV_vals]
    rfl
  rw [e₁]
  exact key

/-- **`array.new_default` (`Step_read` rule 72), forward, at every element storage type.** -/
theorem sread_arrayNewDefaultAnyB (R : RTyping (simEnv B)) (A : AggTypesB (simEnv B))
    {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {n : BitVec 32} {d : DefType} {m : Mutability}
    {zt : CStorageType} {v : Val} (hd : f.type? x = some d) (he : Expand d (.array (.field m zt)))
    (hv : defaultVal? zt.unpack = some v) (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [constI32 n, .plain (.arrayNewDefault x)]⟩)
      (adminsToV (vals (List.replicate n.toNat v) ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("val", valV v), ("mut?", mutV m), ("zt", tyV zt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hrep := Vec.evalExp_iterListN_nodom (env := simEnv B) (ρ := VarEnv.empty.bindVals σ)
    (b := .subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (eₙ := .varE "n")
    (k := n.toNat) (by eval_tac) (RefsGC.evalExp_sub_of (evalExp_var rfl))
  have hty := Aggregates.evalExp_type (aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (Aggregates.findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x") (by eval_tac) (by eval_tac)
  have hex : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m zt).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  have key := dderives_of_ruleAt (O := otherwise (simEnv B))
    ((Aggregates.rd B).arrayNewDefault) σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (Typing.typedV_val v _ hρ)
      (QuantsOk.cons rfl (A.mut_ m _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
        QuantsOk.nil))))))
    (evalExp_tup2 (by eval_tac) (evalExp_cat hrep (by eval_tac)))
    (prems_two (.rulePr evalArgs_nil hex (A.expand _ _ he))
      (.ifPr (evalExp_defaultUnpack_any hρ rfl rfl hv)))
  have e₁ : adminsToV (vals (List.replicate n.toNat v) ++
      [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]) =
      List.replicate n.toNat (valV v) ++
        [.case "ARRAY.NEW_FIXED" (.tuple [Encode.toValue x, .case "%" (.tuple [.num (.natN n.toNat)])])] := by
    rw [Sim.adminsToV_append, Sim.adminsToV_vals, List.map_replicate]
    rfl
  rw [e₁]
  exact key

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
