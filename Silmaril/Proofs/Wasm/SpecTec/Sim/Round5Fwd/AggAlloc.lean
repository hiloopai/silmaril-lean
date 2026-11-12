module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.AggArms

/-!
# Round 5: `R4Fwd/PackedAlloc.lean` on bounded types

A copy of the aggregate lemmas of `R4Fwd/PackedAlloc.lean` that take `Aggregates.AggTypes`, each renamed with a
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
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV evalExp_iterPat)
open Silmaril.SpecTec.Equiv.ExecStepRules
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open RefsGC
open Aggregates (fieldMut evalExp_type evalExp_arrayinst evalExp_structinst
  evalExp_addArray evalExp_addStruct evalExpFields_two' evalExp_fieldBody evalExp_iterNMap2
   findDef_none prems_three)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins} {H : Type} {hn : H → String} {P : Numerics.Profile}

open R4Fwd

variable {env : Env} {B : Builtins} {H : Type} {hn : H → String} {P : Numerics.Profile}

/-- **`array.new_fixed` (`Step` rule 32), forward, at every element storage type**, for packable
operands. -/
theorem fwd_arrayNewFixedAnyB (hF : Floats.FloatB P B) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (A : AggTypesB (simEnv B)) {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx}
    {n : Fin (2 ^ 32)} {d : DefType} {m : Mutability} {zt : CStorageType} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array (.field m zt)))
    (hvn : vs.length = n.val) (hp : ∀ v ∈ vs, packable zt v = true) :
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩
      ⟨s.addArray ⟨d, vs.map (packField zt)⟩, f, [arrRef s.arrays.length]⟩ := by
  intro hc hc'
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  obtain ⟨hz', -⟩ := (T.config _).1 hc'
  obtain ⟨hst', -⟩ := (T.state _ _).1 hz'
  have hcode' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs))) :=
    ((T.append _ _).1 (by rw [← Sim.adminsToV_append]; exact hcode)).1
  have hvals : TypedV (simEnv B) valsT (.list (vs.map valV)) := by
    simpa [Sim.adminsToV_vals] using T.vals vs hcode'
  let ai : ArrayInst := ⟨d, vs.map (packField zt)⟩
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN n.val)),
    ("val*", .list (vs.map valV)), ("x", Encode.toValue x), ("ai", arrayInstV ai),
    ("a", .num (.natN s.arrays.length)), ("mut?", mutV m), ("zt", tyV zt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hlen : (vs.map valV).length = n.val := by simp [hvn]
  have hiter : ∀ (b : Exp) (g : Value → Value),
      (∀ w ∈ vs.map valV, EvalExp (simEnv B) ((VarEnv.empty.bindVals σ).bindVals [("val", w)]) b
        (g w)) →
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.iterE b (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
        (.list ((vs.map valV).map g)) := fun b g hb =>
    Sim.evalExp_iterNMap (by rw [hlen]; rfl) rfl hb
  have hlhs := hiter (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) id
    (fun w _ => evalExp_sub_of (evalExp_var rfl))
  have hflds := hiter (.callE "packfield_" [.expA (.varE "zt"), .expA (.varE "val")]) (packImg zt)
    (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      rw [packImg_valV]
      exact Vec.evalExp_call (findDef_none ⟨rfl, rfl, rfl⟩ _)
        (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl) evalArgs_nil))
        (applies_packfield hF zt v (hp v hv)))
  have hmap : (vs.map valV).map (packImg zt) = (vs.map (packField zt)).map fieldValV := by
    simp only [List.map_map]
    exact List.map_congr_left fun v _ => packImg_valV zt v
  rw [hmap] at hflds
  have hty := evalExp_type (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x") (by eval_tac) (by eval_tac)
  have hex : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m zt).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  have hai : arrayInstV ai = .struct [("TYPE", CT.defType d),
      ("FIELDS", .list ((vs.map (packField zt)).map fieldValV))] := rfl
  have hif : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .andOp .boolT
        (.cmpE .eqOp .boolT (.varE "a") (.lenE (.callE "arrayinst" [.expA (.varE "z")])))
        (.cmpE .eqOp .boolT (.varE "ai") (.strE [.mk "TYPE" (.callE "type" [.expA (.varE "z"),
          .expA (.varE "x")]), .mk "FIELDS" (.iterE (.callE "packfield_" [.expA (.varE "zt"),
            .expA (.varE "val")]) (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))])))
      (.bool true) := by
    refine RefsGC.evalExp_and_true (RefsGC.evalExp_eq_true (by eval_tac) ?_)
      (RefsGC.evalExp_eq_true (by eval_tac) ?_)
    · have := evalExp_len (evalExp_arrayinst (Aggregates.aggDefs_simEnv B) (findDef_none hρ _)
        (e := .varE "z") (s := s) (f := f) (hn := hn) (by eval_tac))
      simpa using this
    · rw [hai]
      exact evalExp_strE_iff.2 ⟨_, evalExpFields_two' hty hflds, rfl⟩
  have hadd := evalExp_addArray (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (findDef_none hρ _) (ez := .varE "z") (el := .listE [.varE "ai"]) (ai := ai) (by eval_tac)
    (by eval_tac)
  have key := dderives_of_ruleAt (O := otherwise (simEnv B)) (Aggregates.st B).arrayNewFixed σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (hvals _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (A.arrayOfStore hn _ ai hst' (by simp [Store.addArray, ai]) _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (A.mut_ m _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
        QuantsOk.nil))))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (by eval_tac)
      (evalExp_cat (by simpa using hlhs) (by eval_tac))))
      (evalExp_case (evalExp_tup2 hadd (by eval_tac))))
    (prems_two (.rulePr evalArgs_nil hex (A.expand _ _ he)) (.ifPr hif))
  have e₁ : adminsToV (vals vs ++ [.plain (.arrayNewFixed x n)]) = vs.map valV ++
      [.case "ARRAY.NEW_FIXED" (.tuple [Encode.toValue x, .case "%" (.tuple [.num (.natN n.val)])])] := by
    rw [Sim.adminsToV_append, Sim.adminsToV_vals]
    rfl
  unfold SStep configV
  rw [e₁]
  exact key

/-- **`struct.new` (`Step` rule 29), forward, at every field storage type**, for packable
operands. -/
theorem fwd_structNewAnyB (hF : Floats.FloatB P B) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (A : AggTypesB (simEnv B)) {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx}
    {d : DefType} {fs : Ty (.list .field)} {vs : List Val} (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hvn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2 = true) :
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩
      ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩, f,
        [.ref (.struct s.structs.length)]⟩ := by
  intro hc hc'
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  obtain ⟨hz', -⟩ := (T.config _).1 hc'
  obtain ⟨hst', -⟩ := (T.state _ _).1 hz'
  have hcode' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs))) :=
    ((T.append _ _).1 (by rw [← Sim.adminsToV_append]; exact hcode)).1
  have hvals : TypedV (simEnv B) valsT (.list (vs.map valV)) := by
    simpa [Sim.adminsToV_vals] using T.vals vs hcode'
  have hfl : fs.toList.length = vs.length := by rw [hvn]; rfl
  let si : StructInst := ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN vs.length)),
    ("val*", .list (vs.map valV)), ("x", Encode.toValue x), ("si", structInstV si),
    ("a", .num (.natN s.structs.length)), ("mut?*", .list (fs.toList.map (mutV ∘ fieldMut))),
    ("zt*", .list (fs.toList.map (tyV ∘ fieldStorage)))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hlhs : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
        (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")])) (.list (vs.map valV)) := by
    have := Sim.evalExp_iterNMap (env := simEnv B) (ρ := VarEnv.empty.bindVals σ) (x := "val")
      (b := .subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (g := id) (c := "n")
      (y := "val*") (ws := vs.map valV) (by rw [List.length_map]; rfl) rfl
      (fun w _ => evalExp_sub_of (evalExp_var rfl))
    simpa using this
  have hty := evalExp_type (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x") (by eval_tac) (by eval_tac)
  have hexp : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.iterE (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
        .varE "zt"])) (.mk (.listN (.varE "n") none) [.mk "mut?" (.varE "mut?*"),
          .mk "zt" (.varE "zt*")])) (.list (fs.toList.map tyV)) :=
    evalExp_iterNMap2 (ps := fs.toList) (g₁ := mutV ∘ fieldMut) (g₂ := tyV ∘ fieldStorage)
      (by rw [hfl]; rfl) rfl rfl fun ft _ => evalExp_fieldBody ft
  have hst : tyV (Ty.struct fs : CCompType) =
      .case "STRUCT" (.case "%" (.tuple [.list (fs.toList.map tyV)])) := by
    simp only [tyV, tyV_list]
    rfl
  have hex : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "STRUCT" (.caseE "%" (.tupE [.iterE (.caseE "%%" (.tupE [.iterE (.varE "mut")
          (.mk .opt [.mk "mut" (.varE "mut?")]), .varE "zt"])) (.mk (.listN (.varE "n") none)
            [.mk "mut?" (.varE "mut?*"), .mk "zt" (.varE "zt*")])]))])
      (.tuple [CT.defType d, tyV (Ty.struct fs : CCompType)]) := by
    rw [hst]
    exact evalExp_tupE_of (evalExps_cons' hty (evalExps_cons' (evalExp_case (evalExp_case
      (evalExp_tupE_of (evalExps_cons' hexp evalExps_nil')))) evalExps_nil'))
  let ps := fs.toList.zip vs
  have hp₁ : ps.map (fun p => valV p.2) = vs.map valV := by
    have h : ps.map Prod.snd = vs := List.map_snd_zip (Nat.le_of_eq hfl.symm)
    rw [← h, List.map_map]
    rfl
  have hp₂ : ps.map (fun p => tyV (fieldStorage p.1)) = fs.toList.map (tyV ∘ fieldStorage) := by
    have h : ps.map Prod.fst = fs.toList := List.map_fst_zip (Nat.le_of_eq hfl)
    rw [← h, List.map_map]
    rfl
  have hflds : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.iterE (.callE "packfield_" [.expA (.varE "zt"), .expA (.varE "val")])
        (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*"), .mk "zt" (.varE "zt*")]))
      (.list (ps.map fun p => fieldValV (packField (fieldStorage p.1) p.2))) :=
    evalExp_iterNMap2 (env := simEnv B) (ρ := VarEnv.empty.bindVals σ) (ps := ps)
      (x₁ := "val") (x₂ := "zt") (y₁ := "val*") (y₂ := "zt*") (c := "n")
      (g₁ := fun p => valV p.2) (g₂ := fun p => tyV (fieldStorage p.1))
      (g := fun p => fieldValV (packField (fieldStorage p.1) p.2))
      (b := .callE "packfield_" [.expA (.varE "zt"), .expA (.varE "val")])
      (by simp [ps, hfl]; rfl) (by rw [hp₁]; rfl) (by rw [hp₂]; rfl)
      (fun p hpm => Vec.evalExp_call (findDef_none ⟨rfl, rfl, rfl⟩ _)
        (evalArgs_cons (evalExp_var rfl) (evalArgs_cons (evalExp_var rfl) evalArgs_nil))
        (applies_packfield hF (fieldStorage p.1) p.2 (hp p hpm)))
  have hsi : structInstV si = .struct [("TYPE", CT.defType d),
      ("FIELDS", .list (ps.map fun p => fieldValV (packField (fieldStorage p.1) p.2)))] := by
    simp only [si, structInstV, List.map_map]
    rfl
  have hif₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "si") (.strE [.mk "TYPE" (.callE "type" [.expA (.varE "z"),
        .expA (.varE "x")]), .mk "FIELDS" (.iterE (.callE "packfield_" [.expA (.varE "zt"),
          .expA (.varE "val")]) (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*"),
            .mk "zt" (.varE "zt*")]))])) (.bool true) := by
    refine RefsGC.evalExp_eq_true (by eval_tac) ?_
    rw [hsi]
    exact evalExp_strE_iff.2 ⟨_, evalExpFields_two' hty hflds, rfl⟩
  have hif₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "a") (.lenE (.callE "structinst" [.expA (.varE "z")])))
      (.bool true) := by
    refine RefsGC.evalExp_eq_true (by eval_tac) ?_
    have := evalExp_len (evalExp_structinst (Aggregates.aggDefs_simEnv B) (findDef_none hρ _)
      (e := .varE "z") (s := s) (f := f) (hn := hn) (by eval_tac))
    simpa using this
  have hadd := evalExp_addStruct (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (findDef_none hρ _) (ez := .varE "z") (el := .listE [.varE "si"]) (si := si) (by eval_tac)
    (by eval_tac)
  obtain ⟨tz, tm⟩ := typed_fieldListsB A fs.toList
  have key := dderives_of_ruleAt (O := otherwise (simEnv B)) (Aggregates.st B).structNew σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (hvals _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (A.structOfStore hn _ si hst' (by simp [Store.addStruct, si]) _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ) (QuantsOk.cons rfl (tm _ hρ) (QuantsOk.cons rfl (tz _ hρ)
        QuantsOk.nil))))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (by eval_tac) (evalExp_cat hlhs (by eval_tac))))
      (evalExp_case (evalExp_tup2 hadd (by eval_tac))))
    (prems_three (.rulePr evalArgs_nil hex (A.expand _ _ he)) (.ifPr hif₁) (.ifPr hif₂))
  have e₁ : adminsToV (vals vs ++ [.plain (.structNew x)]) = vs.map valV ++
      [.case "STRUCT.NEW" (Encode.toValue x)] := by
    rw [Sim.adminsToV_append, Sim.adminsToV_vals]
    rfl
  unfold SStep configV
  rw [e₁]
  exact key

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
