module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Struct
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecPureArrayNew

/-!
# Aggregates: allocation (`array.new`, `array.new_fixed`, `struct.new`), forward

`Step_pure` rule 41 (`array.new`) replicates its operand (`spure_arrayNew`, no premise; the
`val^n` iteration has no domain). `Step` rule 32 allocates an array: `$add_arrayinst(z, [ai])` with
`ai = {TYPE $type(z, x), FIELDS $packfield_(zt, val)^n}` at the address `|$arrayinst(z)|`.
`evalExp_addArray` evaluates the allocation by its clause; `fwd_arrayNewFixedVal` proves the rule
forward for an unpacked element type, and `fwd_structNewVal` (`Step` rule 29) for a structure type
with unpacked fields (two-domain `^n` iterations, `evalExp_iterNMap2`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

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

variable {env : Env} {H : Type} {hn : H → String}

/-- A two-field record. -/
theorem evalExpFields_two' {ρ : VarEnv} {a₁ a₂ : AtomS} {e₁ e₂ : Exp}
    {v₁ v₂ : Value} (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExpFields env ρ [.mk a₁ e₁, .mk a₂ e₂] [(a₁, v₁), (a₂, v₂)] := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  refine ⟨max n₁ n₂ + 1, ?_⟩
  have e₁ := evalExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have e₂ := evalExp_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  simp [evalExpFields, e₁, e₂]

/-- `$add_arrayinst(z, [ai])` appends `ai` to the store's arrays. -/
theorem evalExp_addArray (D : AggDefs env) (SD : State.StateDefs env) {ρ : VarEnv}
    (hρ : ρ.findDef? "add_arrayinst" = none) {ez el : Exp} {s : Store H} {f : Frame}
    {ai : ArrayInst} (hz : EvalExp env ρ ez (stateV hn s f))
    (hl : EvalExp env ρ el (.list [arrayInstV ai])) :
    EvalExp env ρ (.callE "add_arrayinst" [.expA ez, .expA el]) (stateV hn (s.addArray ai) f) := by
  refine State.evalExp_call1 D.addArray hρ (evalArgs_cons hz (evalArgs_cons hl evalArgs_nil))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (State.matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil)) ?_
  refine evalExp_case (evalExp_tup2 ?_ (State.evalExp_fof SD rfl (evalExp_var rfl)))
  have hS : (storeV hn s).field? "ARRAYS" = some (.list (s.arrays.map arrayInstV)) := rfl
  refine evalExp_extE_iff.2 ⟨storeV hn s, .list [arrayInstV ai], .list (s.arrays.map arrayInstV),
    .list (s.arrays.map arrayInstV ++ [arrayInstV ai]), State.evalExp_sof SD rfl (evalExp_var rfl),
    evalExp_iterPat (by decide) rfl, State.pathGet_dot State.pathGet_root hS, rfl, ?_⟩
  exact State.pathSet_dot State.pathGet_root (by simp [storeV, Store.addArray])
    State.pathSet_root

/-- **`array.new_fixed` (`Step` rule 32), forward, for an unpacked element type.** -/
theorem fwd_arrayNewFixedVal (h₀ : HasRuleAt env "Step" "%~>%" 32 arrayNewFixedRule)
    (T : TypingFacts env hn) (R : RTyping env) (D : AggDefs env) (SD : State.StateDefs env)
    (A : AggTypes env) (P : PackDef env) {s : Store H} {f : Frame} {x : TypeIdx}
    {n : Fin (2 ^ 32)} {d : DefType} {m : Mutability} {t : CValType} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array (.field m (.val t))))
    (hvn : vs.length = n.val) :
    FwdP env hn ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩
      ⟨s.addArray ⟨d, vs.map (packField (.val t))⟩, f, [arrRef s.arrays.length]⟩ := by
  intro hc hc'
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  obtain ⟨hz', -⟩ := (T.config _).1 hc'
  obtain ⟨hst', -⟩ := (T.state _ _).1 hz'
  have hcode' : TypedV env instrsT (.list (adminsToV (vals vs))) :=
    ((T.append _ _).1 (by rw [← Sim.adminsToV_append]; exact hcode)).1
  have hvals : TypedV env valsT (.list (vs.map valV)) := by
    simpa [Sim.adminsToV_vals] using T.vals vs hcode'
  let ai : ArrayInst := ⟨d, vs.map (packField (.val t))⟩
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN n.val)),
    ("val*", .list (vs.map valV)), ("x", Encode.toValue x), ("ai", arrayInstV ai),
    ("a", .num (.natN s.arrays.length)), ("mut?", mutV m), ("zt", tyV (Ty.val t : CStorageType))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hlen : (vs.map valV).length = n.val := by simp [hvn]
  have hiter : ∀ (b : Exp) (g : Value → Value),
      (∀ w ∈ vs.map valV, EvalExp env ((VarEnv.empty.bindVals σ).bindVals [("val", w)]) b (g w)) →
      EvalExp env (VarEnv.empty.bindVals σ)
        (.iterE b (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
        (.list ((vs.map valV).map g)) := fun b g hb =>
    Sim.evalExp_iterNMap (by rw [hlen]; rfl) rfl hb
  have hlhs := hiter (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) id
    (fun w _ => evalExp_sub_of (evalExp_var rfl))
  have hflds := hiter (.callE "packfield_" [.expA (.varE "zt"), .expA (.varE "val")]) id
    (fun w _ => evalExp_packfield P (findDef_none ⟨rfl, rfl, rfl⟩ _) (evalExp_var rfl)
      (evalExp_var rfl))
  have hty := evalExp_type D SD (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x")
    (by eval_tac) (by eval_tac)
  have hex : EvalExp env (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m (Ty.val t)).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  have hai : arrayInstV ai = .struct [("TYPE", CT.defType d), ("FIELDS", .list (vs.map valV))] := by
    simp [ai, arrayInstV, packField, fieldValV, Function.comp_def]
  have hif : EvalExp env (VarEnv.empty.bindVals σ)
      (.binE .andOp .boolT
        (.cmpE .eqOp .boolT (.varE "a") (.lenE (.callE "arrayinst" [.expA (.varE "z")])))
        (.cmpE .eqOp .boolT (.varE "ai") (.strE [.mk "TYPE" (.callE "type" [.expA (.varE "z"),
          .expA (.varE "x")]), .mk "FIELDS" (.iterE (.callE "packfield_" [.expA (.varE "zt"),
            .expA (.varE "val")]) (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))])))
      (.bool true) := by
    refine RefsGC.evalExp_and_true (RefsGC.evalExp_eq_true (by eval_tac) ?_)
      (RefsGC.evalExp_eq_true (by eval_tac) ?_)
    · have := evalExp_len (evalExp_arrayinst D (findDef_none hρ _) (e := .varE "z") (s := s) (f := f)
        (hn := hn) (by eval_tac))
      simpa using this
    · rw [hai]
      exact evalExp_strE_iff.2 ⟨_, evalExpFields_two' hty (by simpa using hflds), rfl⟩
  have hadd := evalExp_addArray D SD (findDef_none hρ _) (ez := .varE "z")
    (el := .listE [.varE "ai"]) (ai := ai) (by eval_tac) (by eval_tac)
  have key := dderives_of_ruleAt (O := otherwise env) h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (hvals _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (A.arrayOfStore hn _ ai hst' (by simp [Store.addArray, ai]) _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
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

/-- **`array.new` (`Step_pure` rule 41), forward.** -/
theorem spure_arrayNew (h₀ : HasRuleAt env "Step_pure" "%~>%" 41
      Equiv.ExecPureArrayNew.arrayNewRule)
    (T : TypingFacts env hn) (R : RTyping env) {x : TypeIdx} (v : Val) (n : BitVec 32)
    (hc : TypedV env instrsT (.list (adminsToV [v.toAdmin, constI32 n, .plain (.arrayNew x)]))) :
    SPure env (adminsToV [v.toAdmin, constI32 n, .plain (.arrayNew x)])
      (adminsToV (vals (List.replicate n.toNat v) ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])) := by
  let σ : List (IL.Id × Value) := [("val", adminToV v.toAdmin), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV env valT (adminToV v.toAdmin) := typed_toAdmin R v (typed_head T hc)
  have hrep := Vec.evalExp_iterListN_nodom (env := env) (ρ := VarEnv.empty.bindVals σ)
    (b := .subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (eₙ := .varE "n")
    (k := n.toNat) (by eval_tac) (evalExp_sub_of (evalExp_var rfl))
  have e₁ : adminsToV (vals (List.replicate n.toNat v) ++
      [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]) =
      List.replicate n.toNat (adminToV v.toAdmin) ++
        [.case "ARRAY.NEW_FIXED" (.tuple [Encode.toValue x, .case "%" (.tuple [.num (.natN n.toNat)])])] := by
    rw [Sim.adminsToV_append, Sim.adminsToV_vals, List.map_replicate, adminToV_toAdmin]
    rfl
  rw [e₁]
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hv _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) QuantsOk.nil)))
    (evalExp_tup2 (by eval_tac) (evalExp_cat hrep (by eval_tac))) (fun _ hp => nomatch hp)

/-- `array.new` at `simEnv B`, as a forward obligation. -/
theorem fwd_arrayNew {B : Builtins} (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    {s : Store H} {f : Frame} {x : TypeIdx} (v : Val) (n : BitVec 32) :
    FwdP (simEnv B) hn ⟨s, f, [v.toAdmin, constI32 n, .plain (.arrayNew x)]⟩
      ⟨s, f, vals (List.replicate n.toNat v) ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩ :=
  RefsGC.fwd_of_spure T (hasStepRules_simEnv B).pure fun hc =>
    spure_arrayNew (hasRuleAt_simEnv B Equiv.ExecPureArrayNew.hasArrayNew_wasm30) T R v n hc

/-- Three premises. -/
theorem prems_three {O : ElseI} {els : Prop} {ρ : VarEnv} {pr₁ pr₂ pr₃ : Prem}
    (h₁ : DPrem env O els ρ pr₁) (h₂ : DPrem env O els ρ pr₂) (h₃ : DPrem env O els ρ pr₃) :
    ∀ p ∈ [pr₁, pr₂, pr₃], DPrem env O els ρ p := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h₁
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h₂
  rcases List.mem_singleton.1 hp with rfl
  exact h₃

/-- `$add_structinst(z, [si])` appends `si` to the store's structs. -/
theorem evalExp_addStruct (D : AggDefs env) (SD : State.StateDefs env) {ρ : VarEnv}
    (hρ : ρ.findDef? "add_structinst" = none) {ez el : Exp} {s : Store H} {f : Frame}
    {si : StructInst} (hz : EvalExp env ρ ez (stateV hn s f))
    (hl : EvalExp env ρ el (.list [structInstV si])) :
    EvalExp env ρ (.callE "add_structinst" [.expA ez, .expA el])
      (stateV hn (s.addStruct si) f) := by
  refine State.evalExp_call1 D.addStruct hρ (evalArgs_cons hz (evalArgs_cons hl evalArgs_nil))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (State.matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil)) ?_
  refine evalExp_case (evalExp_tup2 ?_ (State.evalExp_fof SD rfl (evalExp_var rfl)))
  have hS : (storeV hn s).field? "STRUCTS" = some (.list (s.structs.map structInstV)) := rfl
  refine evalExp_extE_iff.2 ⟨storeV hn s, .list [structInstV si], .list (s.structs.map structInstV),
    .list (s.structs.map structInstV ++ [structInstV si]), State.evalExp_sof SD rfl (evalExp_var rfl),
    evalExp_iterPat (by decide) rfl, State.pathGet_dot State.pathGet_root hS, rfl, ?_⟩
  exact State.pathSet_dot State.pathGet_root (by simp [storeV, Store.addStruct])
    State.pathSet_root

/-- Packing values into unpacked fields keeps them. -/
theorem packFields_val :
    ∀ (l : List CFieldType) (vs : List Val), l.length = vs.length →
      (∀ ft ∈ l, ∃ m t, ft = .field m (.val t)) →
      ((l.zip vs).map fun p => packField (fieldStorage p.1) p.2).map fieldValV = vs.map valV
  | [], [], _, _ => rfl
  | ft :: l, v :: vs, hl, hu => by
      obtain ⟨m, t, rfl⟩ := hu ft (List.mem_cons_self ..)
      have ih := packFields_val l vs (by simpa using hl) fun g hg => hu g (List.mem_cons_of_mem _ hg)
      simpa [packField, fieldStorage, fieldValV] using ih
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- The `%% mut? zt` body of the struct `Expand` premise, at one field. -/
theorem evalExp_fieldBody {ρ : VarEnv} (ft : CFieldType) :
    EvalExp env (ρ.bindVals [("mut?", (mutV ∘ fieldMut) ft), ("zt", (tyV ∘ fieldStorage) ft)])
      (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]), .varE "zt"]))
      (tyV ft) := by
  rw [tyV_field]
  cases ft with
  | field m zt => cases m <;> (simp only [Function.comp, fieldMut, fieldStorage, mutV]; eval_tac)

/-- **`struct.new` (`Step` rule 29), forward, for a structure type with unpacked fields.** -/
theorem fwd_structNewVal (h₀ : HasRuleAt env "Step" "%~>%" 29 structNewRule)
    (T : TypingFacts env hn) (R : RTyping env) (D : AggDefs env) (SD : State.StateDefs env)
    (A : AggTypes env) (P : PackDef env) {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {vs : List Val} (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hvn : vs.length = fs.length)
    (hall : ∀ ft ∈ fs.toList, ∃ m t, ft = .field m (.val t)) :
    FwdP env hn ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩
      ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩, f,
        [.ref (.struct s.structs.length)]⟩ := by
  intro hc hc'
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  obtain ⟨hz', -⟩ := (T.config _).1 hc'
  obtain ⟨hst', -⟩ := (T.state _ _).1 hz'
  have hcode' : TypedV env instrsT (.list (adminsToV (vals vs))) :=
    ((T.append _ _).1 (by rw [← Sim.adminsToV_append]; exact hcode)).1
  have hvals : TypedV env valsT (.list (vs.map valV)) := by
    simpa [Sim.adminsToV_vals] using T.vals vs hcode'
  have hfl : fs.toList.length = vs.length := by rw [hvn]; rfl
  let si : StructInst := ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN vs.length)),
    ("val*", .list (vs.map valV)), ("x", Encode.toValue x), ("si", structInstV si),
    ("a", .num (.natN s.structs.length)), ("mut?*", .list (fs.toList.map (mutV ∘ fieldMut))),
    ("zt*", .list (fs.toList.map (tyV ∘ fieldStorage)))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hlhs : EvalExp env (VarEnv.empty.bindVals σ)
      (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
        (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")])) (.list (vs.map valV)) := by
    have := Sim.evalExp_iterNMap (env := env) (ρ := VarEnv.empty.bindVals σ) (x := "val")
      (b := .subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (g := id) (c := "n")
      (y := "val*") (ws := vs.map valV) (by rw [List.length_map]; rfl) rfl (fun w _ => evalExp_sub_of (evalExp_var rfl))
    simpa using this
  have hty := evalExp_type D SD (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x")
    (by eval_tac) (by eval_tac)
  have hexp : EvalExp env (VarEnv.empty.bindVals σ)
      (.iterE (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
        .varE "zt"])) (.mk (.listN (.varE "n") none) [.mk "mut?" (.varE "mut?*"),
          .mk "zt" (.varE "zt*")])) (.list (fs.toList.map tyV)) :=
    evalExp_iterNMap2 (ps := fs.toList) (g₁ := mutV ∘ fieldMut) (g₂ := tyV ∘ fieldStorage)
      (by rw [hfl]; rfl) rfl rfl fun ft _ => evalExp_fieldBody ft
  have hst : tyV (Ty.struct fs : CCompType) =
      .case "STRUCT" (.case "%" (.tuple [.list (fs.toList.map tyV)])) := by
    simp only [tyV, tyV_list]
    rfl
  have hex : EvalExp env (VarEnv.empty.bindVals σ)
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
  have hflds : EvalExp env (VarEnv.empty.bindVals σ)
      (.iterE (.callE "packfield_" [.expA (.varE "zt"), .expA (.varE "val")])
        (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*"), .mk "zt" (.varE "zt*")]))
      (.list (vs.map valV)) := by
    have := evalExp_iterNMap2 (env := env) (ρ := VarEnv.empty.bindVals σ) (ps := ps)
      (x₁ := "val") (x₂ := "zt") (y₁ := "val*") (y₂ := "zt*") (c := "n")
      (g₁ := fun p => valV p.2) (g₂ := fun p => tyV (fieldStorage p.1)) (g := fun p => valV p.2)
      (b := .callE "packfield_" [.expA (.varE "zt"), .expA (.varE "val")])
      (by simp [ps, hfl]; rfl) (by rw [hp₁]; rfl) (by rw [hp₂]; rfl)
      (fun p hp => by
        obtain ⟨m, t, ht⟩ := hall p.1 (List.of_mem_zip hp).1
        have hs : fieldStorage p.1 = Ty.val t := by rw [ht]; rfl
        exact evalExp_packfield P (findDef_none ⟨rfl, rfl, rfl⟩ _) (t := t)
          (by rw [← hs]; exact evalExp_var rfl) (evalExp_var rfl))
    rwa [hp₁] at this
  have hsi : structInstV si = .struct [("TYPE", CT.defType d), ("FIELDS", .list (vs.map valV))] := by
    simp only [si, structInstV]
    rw [packFields_val fs.toList vs hfl hall]
  have hif₂ : EvalExp env (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "si") (.strE [.mk "TYPE" (.callE "type" [.expA (.varE "z"),
        .expA (.varE "x")]), .mk "FIELDS" (.iterE (.callE "packfield_" [.expA (.varE "zt"),
          .expA (.varE "val")]) (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*"),
            .mk "zt" (.varE "zt*")]))])) (.bool true) := by
    refine RefsGC.evalExp_eq_true (by eval_tac) ?_
    rw [hsi]
    exact evalExp_strE_iff.2 ⟨_, evalExpFields_two' hty hflds, rfl⟩
  have hif₁ : EvalExp env (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "a") (.lenE (.callE "structinst" [.expA (.varE "z")])))
      (.bool true) := by
    refine RefsGC.evalExp_eq_true (by eval_tac) ?_
    have := evalExp_len (evalExp_structinst D (findDef_none hρ _) (e := .varE "z") (s := s) (f := f)
      (hn := hn) (by eval_tac))
    simpa using this
  have hadd := evalExp_addStruct D SD (findDef_none hρ _) (ez := .varE "z")
    (el := .listE [.varE "si"]) (si := si) (by eval_tac) (by eval_tac)
  obtain ⟨tz, tm⟩ := typed_fieldLists A fs.toList
  have key := dderives_of_ruleAt (O := otherwise env) h₀ σ
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

end Silmaril.Wasm.SpecTec.Sim.Aggregates
