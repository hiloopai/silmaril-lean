module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdSimdAgg.Default

/-!
# Track `fwd-simd-agg`: `struct.new_default`, `array.new_default`, forward

`Step_read` rules 69 and 72 (`Equiv.ExecRead.structNewDefaultRule`, `arrayNewDefaultRule`), at
`simEnv B`, for unpacked fields. Both read the composite type through the `Expand` premise
(`AggTypes.expand`) and each default through `$default_($unpack(zt)) = ?(val)`
(`evalExp_defaultUnpack`). `struct.new_default`'s premise is an iteration over the two parallel
domains `val*`, `zt*`, built with `DPrem.iterList` on the rows of `Aggregates.iterRows_pair`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_nil)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Aggregates (AggTypes fieldMut evalExp_expandStruct typed_fieldLists aggDefs_simEnv
  iterRows_pair)
open RefsGC (RTyping evalExp_tupE_of evalExps_cons' evalExps_nil')

variable {B : Builtins} {H : Type} {hn : H → String}

/-- A successful `mapM` relates every element to its image. -/
theorem forall₂_of_mapM {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {vs : List β}, l.mapM g = some vs → List.Forall₂ (fun a b => g a = some b) l vs
  | [], vs, h => by
    obtain rfl : [] = vs := by simpa using h
    exact .nil
  | a :: l, vs, h => by
    cases ha : g a with
    | none => simp [List.mapM_cons, ha] at h
    | some b =>
      cases hl : l.mapM g with
      | none => simp [List.mapM_cons, ha, hl] at h
      | some bs =>
        obtain rfl : b :: bs = vs := by simpa [List.mapM_cons, ha, hl] using h
        exact .cons ha (forall₂_of_mapM hl)

/-- The members of a `zip` of `Forall₂`-related lists are related. -/
theorem forall₂_mem_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {vs : List β}, List.Forall₂ R l vs → ∀ p ∈ l.zip vs, R p.1 p.2
  | [], [], .nil, _, hp => nomatch hp
  | _ :: _, _ :: _, .cons hr h, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hr
    · exact forall₂_mem_zip h p hp

/-- Every element of a list of Core values is a typed `val`. -/
theorem typedV_vals (vs : List Val) :
    TypedV (simEnv B) (.iterT (.varT "val" []) .list) (.list (vs.map valV)) :=
  typedV_list_iff.2 fun w hw => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hw
    exact Typing.typedV_val v

set_option maxHeartbeats 400000 in
/-- **`struct.new_default` (`Step_read` rule 69), forward, for unpacked fields.** -/
theorem sread_structNewDefault (R : RTyping (simEnv B)) (A : AggTypes (simEnv B)) {s : Store H}
    {f : Frame} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hu : ∀ ft ∈ fs.toList, ∃ m t, ft = .field m (.val t))
    (hdef : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some vs)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [.plain (.structNewDefault x)]⟩)
      (adminsToV (vals vs ++ [.plain (.structNew x)])) := by
  have hF := forall₂_of_mapM hdef
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
    obtain ⟨m, t, hft⟩ := hu p.1 (List.of_mem_zip hp).1
    have hdp : defaultVal? (fieldStorage p.1).unpack = some p.2 := forall₂_mem_zip hF p hp
    rw [hft] at hdp
    exact .ifPr (evalExp_defaultUnpack (t := t) ⟨rfl, rfl, rfl⟩
      (by simp only [Function.comp_apply, hft]; rfl) rfl hdp)
  obtain ⟨tz, tm⟩ := typed_fieldLists A fs.toList
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

/-- **`array.new_default` (`Step_read` rule 72), forward, for an unpacked element type.** -/
theorem sread_arrayNewDefault (R : RTyping (simEnv B)) (A : AggTypes (simEnv B)) {s : Store H}
    {f : Frame} {x : TypeIdx} {n : BitVec 32} {d : DefType} {m : Mutability} {t : CValType}
    {v : Val} (hd : f.type? x = some d) (he : Expand d (.array (.field m (.val t))))
    (hv : defaultVal? t = some v) (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [constI32 n, .plain (.arrayNewDefault x)]⟩)
      (adminsToV (vals (List.replicate n.toNat v) ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("val", valV v), ("mut?", mutV m),
    ("zt", tyV (Ty.val t : CStorageType))]
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
      (.tuple [CT.defType d, tyV ((Ty.field m (Ty.val t)).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  have key := dderives_of_ruleAt (O := otherwise (simEnv B))
    ((Aggregates.rd B).arrayNewDefault) σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (Typing.typedV_val v _ hρ)
      (QuantsOk.cons rfl (A.mut_ m _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
        QuantsOk.nil))))))
    (evalExp_tup2 (by eval_tac) (evalExp_cat hrep (by eval_tac)))
    (prems_two (.rulePr evalArgs_nil hex (A.expand _ _ he))
      (.ifPr (evalExp_defaultUnpack hρ rfl rfl hv)))
  have e₁ : adminsToV (vals (List.replicate n.toNat v) ++
      [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]) =
      List.replicate n.toNat (valV v) ++
        [.case "ARRAY.NEW_FIXED" (.tuple [Encode.toValue x, .case "%" (.tuple [.num (.natN n.toNat)])])] := by
    rw [Sim.adminsToV_append, Sim.adminsToV_vals, List.map_replicate]
    rfl
  rw [e₁]
  exact key

/-! ## As forward obligations -/

/-- `struct.new_default`, as a forward obligation. -/
theorem fwd_structNewDefault (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (A : AggTypes (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {vs : List Val} (hu : Aggregates.Unpacked f)
    (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hdef : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some vs) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.structNewDefault x)]⟩
      ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩ :=
  RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
    sread_structNewDefault R A hd he (hu x d _ hd he) hdef hz

/-- `array.new_default`, as a forward obligation. -/
theorem fwd_arrayNewDefault (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (A : AggTypes (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx} {n : BitVec 32}
    {d : DefType} {ft : CFieldType} {v : Val} (hu : Aggregates.Unpacked f)
    (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hv : defaultVal? (fieldStorage ft).unpack = some v) :
    FwdP (simEnv B) hn ⟨s, f, [constI32 n, .plain (.arrayNewDefault x)]⟩
      ⟨s, f, vals (List.replicate n.toNat v) ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩ := by
  obtain ⟨m, t, rfl⟩ := hu.array hd he
  exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
    sread_arrayNewDefault R A hd he hv hz

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
