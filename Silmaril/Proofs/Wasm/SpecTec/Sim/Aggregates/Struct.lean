module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Store
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms

/-!
# Aggregates: structure fields (`struct.get-struct`, `struct.set-struct`), forward

The struct rules quantify over the field list as two parallel sequences `mut?*` and `zt*` and
rebuild the composite type in their `Expand` premise as `STRUCT (%% mut? zt)*`, an iteration over
two domains. `evalExp_iterMap2` evaluates such an iteration pointwise; `evalExp_structFields`
instantiates it at the image of a Core field list. Both rules are then proved forward for unpacked
fields, as in `Read.lean`/`Store.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

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

/-! ## Two-domain iterations -/

section Iter

variable {env : Env} {ρ : VarEnv} {b : Exp} {x₁ x₂ : IL.Id} {α : Type} {g₁ g₂ g : α → Value}

/-- The rows of a two-domain iteration over parallel images of one list. -/
theorem iterRows_pair (ps : List α) :
    iterRows [(x₁, ps.map g₁), (x₂, ps.map g₂)] none ps.length =
      ps.map fun p => [(x₁, g₁ p), (x₂, g₂ p)] := by
  apply List.ext_getElem
  · simp [iterRows]
  · intro i h₁ h₂
    have hi : i < ps.length := by simpa [iterRows] using h₁
    simp [iterRows, iterRow, hi]

/-- A pointwise evaluation over a list has one fuel level for all elements. -/
theorem uniform_fuel2 :
    ∀ ps : List α, (∀ p ∈ ps, EvalExp env (ρ.bindVals [(x₁, g₁ p), (x₂, g₂ p)]) b (g p)) →
      ∃ N, ∀ p ∈ ps, evalExp N env (ρ.bindVals [(x₁, g₁ p), (x₂, g₂ p)]) b = .ok (g p)
  | [], _ => ⟨0, fun _ h => nomatch h⟩
  | p :: ps, h => by
      obtain ⟨n, hn⟩ := h p (List.mem_cons_self ..)
      obtain ⟨N, hN⟩ := uniform_fuel2 ps fun u hu => h u (List.mem_cons_of_mem _ hu)
      refine ⟨max n N, fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact evalExp_ok_of_le (by omega) hn
      · exact evalExp_ok_of_le (by omega) (hN u hu)

/-- The rounds of a pointwise body over two domains. -/
theorem mapM_rounds_map2 {N : Nat} :
    ∀ ps : List α, (∀ p ∈ ps, evalExp N env (ρ.bindVals [(x₁, g₁ p), (x₂, g₂ p)]) b = .ok (g p)) →
      (ps.map fun p => [(x₁, g₁ p), (x₂, g₂ p)]).mapM (fun r => evalExp N env (ρ.bindVals r) b) =
        .ok (ps.map g)
  | [], _ => rfl
  | p :: ps, h => by
      have hp := h p (List.mem_cons_self ..)
      have ih := mapM_rounds_map2 ps fun u hu => h u (List.mem_cons_of_mem _ hu)
      simp only [List.map_cons, List.mapM_cons, hp, ih]
      rfl

/-- `evalIterList` over two parallel domains, with a pointwise body. -/
theorem evalIterList_map2 {N : Nat} {ps : List α}
    (h : ∀ p ∈ ps, evalExp N env (ρ.bindVals [(x₁, g₁ p), (x₂, g₂ p)]) b = .ok (g p)) :
    evalIterList (N + 2) env ρ b
      [(x₁, Value.list (ps.map g₁)), (x₂, Value.list (ps.map g₂))] none ps.length =
      .ok (.list (ps.map g)) := by
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok]
  refine ⟨[(x₁, ps.map g₁), (x₂, ps.map g₂)], by simp [Value.asList?], by simp, ps.map g, ?_, rfl⟩
  rw [iterRows_pair, evalRounds]
  exact mapM_rounds_map2 ps h

/-- **A `*` iteration over two parallel domains** with a pointwise body denotes the pointwise
image. -/
theorem evalExp_iterMap2 {y₁ y₂ : IL.Id} {ps : List α}
    (hy₁ : ρ.findVal? y₁ = some (.list (ps.map g₁))) (hy₂ : ρ.findVal? y₂ = some (.list (ps.map g₂)))
    (hb : ∀ p ∈ ps, EvalExp env (ρ.bindVals [(x₁, g₁ p), (x₂, g₂ p)]) b (g p)) :
    EvalExp env ρ (.iterE b (.mk .list [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)]))
      (.list (ps.map g)) := by
  obtain ⟨N, hN⟩ := uniform_fuel2 ps hb
  have hdoms : evalDoms (N + 3) env ρ [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)] =
      .ok [(x₁, Value.list (ps.map g₁)), (x₂, Value.list (ps.map g₂))] := by
    simp [evalDoms, domVar, domSrc, evalExp, hy₁, hy₂]
  have hl := evalIterList_map2 (b := b) (N := N + 1) fun p hp =>
    evalExp_ok_of_le (by omega) (hN p hp)
  refine evalExp_iterE_iff.mpr ⟨N + 4, ?_⟩
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, Value.asList?,
    List.isEmpty_cons]
  refine ⟨_, rfl, trivial, (ps.map g₁).length, by simp, ?_⟩
  simpa using hl

/-- **A `^n` iteration over two parallel domains**, the counter bound to their length. -/
theorem evalExp_iterNMap2 {y₁ y₂ c : IL.Id} {ps : List α}
    (hc : ρ.findVal? c = some (.num (.natN ps.length)))
    (hy₁ : ρ.findVal? y₁ = some (.list (ps.map g₁))) (hy₂ : ρ.findVal? y₂ = some (.list (ps.map g₂)))
    (hb : ∀ p ∈ ps, EvalExp env (ρ.bindVals [(x₁, g₁ p), (x₂, g₂ p)]) b (g p)) :
    EvalExp env ρ (.iterE b (.mk (.listN (.varE c) none) [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)]))
      (.list (ps.map g)) := by
  obtain ⟨N, hN⟩ := uniform_fuel2 ps hb
  have hdoms : evalDoms (N + 3) env ρ [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)] =
      .ok [(x₁, Value.list (ps.map g₁)), (x₂, Value.list (ps.map g₂))] := by
    simp [evalDoms, domVar, domSrc, evalExp, hy₁, hy₂]
  have hcount : evalExp (N + 3) env ρ (.varE c) = .ok (.num (.natN ps.length)) := by
    simp [evalExp, hc]
  have hl := evalIterList_map2 (b := b) (N := N + 1) fun p hp =>
    evalExp_ok_of_le (by omega) (hN p hp)
  refine evalExp_iterE_iff.mpr ⟨N + 4, ?_⟩
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hcount]
  exact ⟨_, rfl, _, rfl, ps.length, rfl, hl⟩

end Iter

/-! ## Field lists -/

/-- The mutability of a field type. -/
def fieldMut : CFieldType → Mutability
  | .field m _ => m

/-- `tyV` of a field type is `%% mut? zt` of its parts. -/
theorem tyV_field (ft : CFieldType) :
    tyV ft = .case "%%" (.tuple [mutV (fieldMut ft), tyV (fieldStorage ft)]) := by
  cases ft
  rfl

/-- The `STRUCT (%% mut? zt)*` premise pattern, at the bindings `mut?* , zt*` of a field list. -/
theorem evalExp_structFields {env : Env} {ρ : VarEnv} (fs : List CFieldType)
    (hm : ρ.findVal? "mut?*" = some (.list (fs.map (mutV ∘ fieldMut))))
    (hz : ρ.findVal? "zt*" = some (.list (fs.map (tyV ∘ fieldStorage)))) :
    EvalExp env ρ (.iterE (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
        .varE "zt"])) (.mk .list [.mk "mut?" (.varE "mut?*"), .mk "zt" (.varE "zt*")]))
      (.list (fs.map tyV)) := by
  refine evalExp_iterMap2 (g₁ := mutV ∘ fieldMut) (g₂ := tyV ∘ fieldStorage) hm hz ?_
  intro ft _
  rw [tyV_field]
  cases ft with
  | field m zt => cases m <;> (simp only [Function.comp, fieldMut, fieldStorage, mutV]; eval_tac)

variable {env : Env} {H : Type} {hn : H → String}

/-- The `Expand` premise of the struct rules, evaluated at the image of `f.type? x = some d`. -/
theorem evalExp_expandStruct (D : AggDefs env) (SD : State.StateDefs env) {σ : List (IL.Id × Value)}
    (hρ : ValsOnly (VarEnv.empty.bindVals σ)) {s : Store H} {f : Frame} {x : TypeIdx}
    {d : DefType} {fs : Ty (.list .field)} (hd : f.type? x = some d)
    (hz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (hx : (VarEnv.empty.bindVals σ).findVal? "x" = some (Encode.toValue x))
    (hm : (VarEnv.empty.bindVals σ).findVal? "mut?*" = some (.list (fs.toList.map (mutV ∘ fieldMut))))
    (hzt : (VarEnv.empty.bindVals σ).findVal? "zt*" =
      some (.list (fs.toList.map (tyV ∘ fieldStorage)))) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "STRUCT" (.caseE "%" (.tupE [.iterE (.caseE "%%" (.tupE [.iterE (.varE "mut")
          (.mk .opt [.mk "mut" (.varE "mut?")]), .varE "zt"])) (.mk .list [.mk "mut?" (.varE "mut?*"),
            .mk "zt" (.varE "zt*")])]))])
      (.tuple [CT.defType d, tyV (Ty.struct fs : CCompType)]) := by
  have hty := evalExp_type D SD (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x")
    (evalExp_var hz) (evalExp_var hx)
  have hfl := evalExp_structFields (env := env) fs.toList hm hzt
  have hst : tyV (Ty.struct fs : CCompType) = .case "STRUCT" (.case "%" (.tuple [.list (fs.toList.map tyV)])) := by
    simp only [tyV, tyV_list]
    rfl
  rw [hst]
  exact evalExp_tupE_of (evalExps_cons' hty (evalExps_cons' (evalExp_case (evalExp_case
    (evalExp_tupE_of (evalExps_cons' hfl evalExps_nil')))) evalExps_nil'))

/-- The typing of the `zt*` and `mut?*` bindings of a field list. -/
theorem typed_fieldLists (A : AggTypes env) (fs : List CFieldType) :
    TypedV env (.iterT storagetypeT .list) (.list (fs.map (tyV ∘ fieldStorage))) ∧
      TypedV env (.iterT mutOptT .list) (.list (fs.map (mutV ∘ fieldMut))) := by
  constructor
  · refine typedV_list_iff.2 fun v hv => ?_
    obtain ⟨ft, -, rfl⟩ := List.mem_map.1 hv
    exact A.storagetype _
  · refine typedV_list_iff.2 fun v hv => ?_
    obtain ⟨ft, -, rfl⟩ := List.mem_map.1 hv
    exact A.mut_ _

/-- **`struct.get-struct` (rule 71), forward, for an unpacked field.** -/
theorem sread_structGetStructVal (h₀ : HasRuleAt env "Step_read" "%~>%" 71 structGetStructRule)
    (R : RTyping env) (D : AggDefs env) (SD : State.StateDefs env) (A : AggTypes env)
    (U : UnpackDef env) {s : Store H} {f : Frame} {x : TypeIdx} {i : FieldIdx} {a : Nat}
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
  obtain ⟨tz, tm⟩ := typed_fieldLists A fs.toList
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

/-- **`struct.set-struct` (`Step` rule 31), forward, for an unpacked field.** -/
theorem fwd_structSetStructVal (h₀ : HasRuleAt env "Step" "%~>%" 31 structSetStructRule)
    (T : TypingFacts env hn) (R : RTyping env) (D : AggDefs env) (SD : State.StateDefs env)
    (A : AggTypes env) (P : PackDef env) {s : Store H} {f : Frame} {x : TypeIdx} {i : FieldIdx}
    {v : Val} {a : Nat} {d : DefType} {fs : Ty (.list .field)} {m : Mutability} {t : CValType}
    {si : StructInst} (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hi : fs.toList[i.toNat]? = some (.field m (.val t))) (hs : s.structs[a]? = some si)
    (hf : i.toNat < si.fields.length) :
    FwdP env hn ⟨s, f, [.ref (.struct a), v.toAdmin, .plain (.structSet x i)]⟩
      ⟨s.setStructField a i.toNat (packField (.val t) v), f, []⟩ := by
  intro hc _
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("val", adminToV v.toAdmin), ("x", Encode.toValue x), ("i", Encode.toValue i),
    ("zt*", .list (fs.toList.map (tyV ∘ fieldStorage))),
    ("mut?*", .list (fs.toList.map (mutV ∘ fieldMut)))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV env valT (adminToV v.toAdmin) :=
    typed_toAdmin R v (typed_head T (typed_tail T hcode))
  have hii : EvalExp env (VarEnv.empty.bindVals σ) (.projE (.uncaseE (.varE "i") "%") 0)
      (.num (.natN i.toNat)) := evalExp_unpct (by eval_tac)
  have hzt : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.iterE (.varE "zt") (.mk .list [.mk "zt" (.varE "zt*")]))
        (.projE (.uncaseE (.varE "i") "%") 0)) (tyV (Ty.val t : CStorageType)) :=
    evalExp_idx (by eval_tac) hii (by simp [hi, fieldStorage])
  have hpk : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "packfield_" [.expA (.idxE (.iterE (.varE "zt") (.mk .list [.mk "zt" (.varE "zt*")]))
        (.projE (.uncaseE (.varE "i") "%") 0)), .expA (.varE "val")])
      (fieldValV (packField (.val t) v)) := by
    have := evalExp_packfield P (findDef_none hρ _) hzt (e₂ := .varE "val") (by eval_tac)
    simpa [packField, fieldValV, adminToV_toAdmin] using this
  have hw := evalExp_withStruct D SD (findDef_none hρ _) (ez := .varE "z") (ea := .varE "a")
    (ei := .projE (.uncaseE (.varE "i") "%") 0) hs hf (by eval_tac) (by eval_tac) hii hpk
  obtain ⟨tz, tm⟩ := typed_fieldLists A fs.toList
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (hv _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.fieldidx _ i.value.isLt _ hρ) (QuantsOk.cons rfl (tz _ hρ)
      (QuantsOk.cons rfl (tm _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_case (evalExp_tup2 hw (by eval_tac))))
    (prems_one (.rulePr evalArgs_nil (evalExp_expandStruct D SD hρ hd rfl rfl rfl rfl)
      (A.expand _ _ he)))

end Silmaril.Wasm.SpecTec.Sim.Aggregates
