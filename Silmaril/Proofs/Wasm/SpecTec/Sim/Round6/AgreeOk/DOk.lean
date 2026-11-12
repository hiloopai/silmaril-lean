module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeSub.Main
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Struct
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Insts

/-!
# Round 6: the validation rules under `DDerivesB`, in any typed context

Iteration premises over one or two list domains (`dpremB_iter1`, `dpremB_iter2`), the typing of
the leaf types' images, and one lemma per rule of the validation group not covered by tracks
refokbb and reading: `Heaptype_ok/bot`, `Valtype_ok/num`, `vec`, `bot` (with `Numtype_ok`,
`Vectype_ok`), `Storagetype_ok/pack` (with `Packtype_ok`), `Resulttype_ok`, and
`Comptype_ok/struct` (any number of fields), `array`, `func`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV numtypeV vectypeV packtypeV)
open Silmaril.Wasm
open Round6.Reading
open Round6.AgreeSub (CtxT HeapT listIterE evalExp_atomE)

variable {B : Builtins}

/-! ## Iterated premises -/

/-- The rows of a one-domain iteration. -/
theorem iterRows_one (x : IL.Id) (ws : List Value) :
    iterRows [(x, ws)] none ws.length = ws.map fun w => [(x, w)] := by
  apply List.ext_getElem
  · simp [iterRows]
  · intro i h₁ h₂
    have hi : i < ws.length := by simpa [iterRows] using h₁
    simp [iterRows, iterRow, hi]

/-- **A premise iterated over one list domain** holds when it holds at every element. -/
theorem dpremB_iter1 {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem} {x y : IL.Id}
    {ws : List Value} (hy : ρ.findVal? y = some (.list ws))
    (h : ∀ w ∈ ws, DPremB env O els (ρ.bindVals [(x, w)]) pr) :
    DPremB env O els ρ (.iterPr pr (.mk .list [.mk x (.varE y)])) := by
  refine .iterList (k := ws.length) (xvs := [(x, .list ws)]) (dls := [(x, ws)]) (.inl rfl)
    ⟨2, by simp [evalDoms, domVar, domSrc, evalExp, hy, Res.ofOption]⟩ (by simp)
    (by simp [domLists, Value.asList?]) (by simp) ?_
  rw [iterRows_one]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact h w hw

/-- **A premise iterated over two parallel list domains** holds when it holds at every pair. -/
theorem dpremB_iter2 {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {x₁ x₂ y₁ y₂ : IL.Id} {ps : List (Value × Value)}
    (hy₁ : ρ.findVal? y₁ = some (.list (ps.map Prod.fst)))
    (hy₂ : ρ.findVal? y₂ = some (.list (ps.map Prod.snd)))
    (h : ∀ p ∈ ps, DPremB env O els (ρ.bindVals [(x₁, p.1), (x₂, p.2)]) pr) :
    DPremB env O els ρ (.iterPr pr (.mk .list [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)])) := by
  refine .iterList (k := ps.length) (xvs := [(x₁, .list (ps.map Prod.fst)),
    (x₂, .list (ps.map Prod.snd))]) (dls := [(x₁, ps.map Prod.fst), (x₂, ps.map Prod.snd)])
    (.inl rfl) ⟨2, by simp [evalDoms, domVar, domSrc, evalExp, hy₁, hy₂, Res.ofOption]⟩
    (by simp) (by simp [domLists, Value.asList?]) (by simp) ?_
  rw [Aggregates.iterRows_pair]
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  exact h p hp

/-- Two lists related pointwise are the two projections of one list of pairs. -/
theorem forall2_zip {α : Type} {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, List.Forall₂ R l₁ l₂ →
      ∃ ps : List (α × α), l₁ = ps.map Prod.fst ∧ l₂ = ps.map Prod.snd ∧ ∀ p ∈ ps, R p.1 p.2
  | [], [], _ => ⟨[], rfl, rfl, by simp⟩
  | _ :: _, _ :: _, .cons h hs => by
    obtain ⟨ps, rfl, rfl, hps⟩ := forall2_zip hs
    exact ⟨(_, _) :: ps, rfl, rfl, by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h
      · exact hps p hp⟩

/-- A list variable `x*` iterated pointwise evaluates to its list. -/
theorem evalExp_listIterV {env : Env} {ρ : VarEnv} {x : IL.Id} {ws : List Value}
    (hy : ρ.findVal? (x ++ "*") = some (.list ws))
    (hx : ∀ w, (ρ.bindVals [(x, w)]).findVal? x = some w) :
    EvalExp env ρ (listIterE x) (.list ws) := by
  have h := evalExp_iterMap (env := env) (b := .varE x) (x := x) (y := x ++ "*") (ws := ws)
    (g := fun w => w) hy (fun w _ => evalExp_var (hx w))
  rwa [List.map_id'] at h

/-- `%(x*)` evaluates to `%(ws)`. -/
theorem evalExp_resE {env : Env} {ρ : VarEnv} {x : IL.Id} {ws : List Value}
    (hy : ρ.findVal? (x ++ "*") = some (.list ws))
    (hx : ∀ w, (ρ.bindVals [(x, w)]).findVal? x = some w) :
    EvalExp env ρ (resE x) (.case "%" (.tuple [.list ws])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_listIterV hy hx) evalExps_nil, rfl⟩)

/-! ## Typing the leaf types -/

/-- Every number type is a `numtype`. -/
theorem typedV_numtypeV (t : NumType) : TypedV (simEnv B) (.varT "numtype" []) (numtypeV t) := by
  rcases t with t | t <;> cases t <;> exact Typing.typedV_closedCase IntNumeric.findTyp_numtype rfl
    hasTyp_tupT_nil

/-- Every vector type is a `vectype`. -/
theorem typedV_vectypeV (t : VecType) : TypedV (simEnv B) (.varT "vectype" []) (vectypeV t) := by
  cases t
  exact Typing.typedV_closedCase Typing.findTyp_vectype rfl hasTyp_tupT_nil

/-- Every packed type is a `packtype`. -/
theorem typedV_packtypeV (p : PackType) : TypedV (simEnv B) (.varT "packtype" []) (packtypeV p) := by
  cases p <;> exact Typing.typedV_closedCase Round5.Pos.findTyp_packtype rfl hasTyp_tupT_nil

/-! ## Leaf rules -/

/-- **`Heaptype_ok/bot`.** -/
theorem dd_heaptypeOkBot (O : ElseI) {c : Value} (hc : CtxT B c) :
    DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, .case "BOT" (.tuple [])]) :=
  dderivesB_of_ruleAt ruleAt_heaptypeOkBot (self_mem_conclAlts _) [("C", c)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup2 (evalExp_var rfl) (evalExp_atomE "BOT")) premsB_nil

/-- **`Valtype_ok/bot`.** -/
theorem dd_valtypeOkBot (O : ElseI) {c : Value} (hc : CtxT B c) :
    DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, .case "BOT" (.tuple [])]) :=
  dderivesB_of_ruleAt ruleAt_valtypeOkBot (self_mem_conclAlts _) [("C", c)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup2 (evalExp_var rfl) (evalExp_atomE "BOT")) premsB_nil

/-- `x` in the scope `C, x`. -/
theorem findVal_two_snd {c v : Value} {x : IL.Id} (hx₁ : x ≠ "_") :
    (VarEnv.empty.bindVals [("C", c), (x, v)]).findVal? x = some v := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx₁]

/-- `C` in the scope `C, x`. -/
theorem findVal_two_fst {c v : Value} {x : IL.Id} (hx₁ : x ≠ "_") (hx₂ : x ≠ "C") :
    (VarEnv.empty.bindVals [("C", c), (x, v)]).findVal? "C" = some c := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx₁]
  exact fun h => absurd h hx₂

/-- A leaf rule `C ⊢ x : OK` with no premises. -/
theorem dd_leafOk (O : ElseI) {c v : Value} (hc : CtxT B c) {r x : IL.Id}
    (hr : HasRuleAt (simEnv B) r "%|-%:OK" 0
      (.ruleD "" [Round6.AgreeSub.ctxP, varP x x] "%|-%:OK" (.tupE [.varE "C", .varE x]) []))
    (hv : TypedV (simEnv B) (.varT x []) v) (hx₁ : x ≠ "_" := by decide)
    (hx₂ : x ≠ "C" := by decide) :
    DDerivesB (simEnv B) O r "%|-%:OK" [] (.tuple [c, v]) :=
  dderivesB_of_ruleAt hr (self_mem_conclAlts _) [("C", c), (x, v)]
    (QuantsOk.cons (findVal_two_fst hx₁ hx₂) (hc _ (valsOnly_bind _))
      (QuantsOk.cons (findVal_two_snd hx₁)
      (hv _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_tup2 (evalExp_var (findVal_two_fst hx₁ hx₂)) (evalExp_var (findVal_two_snd hx₁)))
    premsB_nil

/-- A subsumption rule `C ⊢ x : OK` (at a larger sort) from `C ⊢ x : OK` (at `x`'s sort). -/
theorem dd_subsumeOk (O : ElseI) {c v : Value} (hc : CtxT B c) {r r' x s nm : IL.Id} {k : Nat}
    (hr : HasRuleAt (simEnv B) r "%|-%:OK" k
      (.ruleD nm [Round6.AgreeSub.ctxP, varP x x] "%|-%:OK" (.tupE [.varE "C", subVarE x x s])
        [relPrem r' "%|-%:OK" [.varE x]]))
    (hv : TypedV (simEnv B) (.varT x []) v)
    (hd : DDerivesB (simEnv B) O r' "%|-%:OK" [] (.tuple [c, v])) (hx₁ : x ≠ "_" := by decide)
    (hx₂ : x ≠ "C" := by decide) :
    DDerivesB (simEnv B) O r "%|-%:OK" [] (.tuple [c, v]) :=
  have hx := findVal_two_snd (c := c) (v := v) hx₁
  have hC := findVal_two_fst (c := c) (v := v) hx₁ hx₂
  dderivesB_of_ruleAt hr (self_mem_conclAlts _) [("C", c), (x, v)]
    (QuantsOk.cons hC (hc _ (valsOnly_bind _)) (QuantsOk.cons hx (hv _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_var hC) (RefsGC.evalExp_sub_of (evalExp_var hx)))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var hC) (evalExp_var hx)) hd))

/-- **`Valtype_ok/num`**, with `Numtype_ok`. -/
theorem dd_valtypeOkNum (O : ElseI) {c : Value} (hc : CtxT B c) (t : NumType) :
    DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, numtypeV t]) :=
  dd_subsumeOk O hc ruleAt_valtypeOkNum (typedV_numtypeV t)
    (dd_leafOk O hc ruleAt_numtypeOk (typedV_numtypeV t))

/-- **`Valtype_ok/vec`**, with `Vectype_ok`. -/
theorem dd_valtypeOkVec (O : ElseI) {c : Value} (hc : CtxT B c) (t : VecType) :
    DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, vectypeV t]) :=
  dd_subsumeOk O hc ruleAt_valtypeOkVec (typedV_vectypeV t)
    (dd_leafOk O hc ruleAt_vectypeOk (typedV_vectypeV t))

/-- **`Storagetype_ok/pack`**, with `Packtype_ok`. -/
theorem dd_storagetypeOkPack (O : ElseI) {c : Value} (hc : CtxT B c) (p : PackType) :
    DDerivesB (simEnv B) O "Storagetype_ok" "%|-%:OK" [] (.tuple [c, packtypeV p]) :=
  dd_subsumeOk O hc ruleAt_storagetypeOkPack (typedV_packtypeV p)
    (dd_leafOk O hc ruleAt_packtypeOk (typedV_packtypeV p))

/-! ## Sequences and composite types -/

/-- The scope of a rule with `C` and one list variable. -/
def listσ (c : Value) (y : IL.Id) (ws : List Value) : List (IL.Id × Value) :=
  [("C", c), (y, .list ws)]

/-- **`Resulttype_ok`**, from `Valtype_ok` at every element. -/
theorem dd_resulttypeOk (O : ElseI) {c : Value} (hc : CtxT B c) {ts : List Value}
    (hT : ∀ t ∈ ts, TypedV (simEnv B) (.varT "valtype" []) t)
    (h : ∀ t ∈ ts, DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, t])) :
    DDerivesB (simEnv B) O "Resulttype_ok" "%|-%:OK" []
      (.tuple [c, .case "%" (.tuple [.list ts])]) :=
  dderivesB_of_ruleAt ruleAt_resulttypeOk (self_mem_conclAlts _) (listσ c "t*" ts)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hT _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_resE rfl fun _ => rfl))
    (premsB_one (dpremB_iter1 rfl fun w hw => .rulePr (evalArgs_nil _ _)
      (evalExp_tup2 (evalExp_var (by simp [listσ, VarEnv.findVal?, VarEnv.bindVals, Map.binds,
        Map.bind])) (evalExp_var rfl)) (h w hw)))

/-- **`Comptype_ok/struct`**, from `Fieldtype_ok` at every field. -/
theorem dd_comptypeOkStruct (O : ElseI) {c : Value} (hc : CtxT B c) {fs : List Value}
    (hT : ∀ f ∈ fs, TypedV (simEnv B) (.varT "fieldtype" []) f)
    (h : ∀ f ∈ fs, DDerivesB (simEnv B) O "Fieldtype_ok" "%|-%:OK" [] (.tuple [c, f])) :
    DDerivesB (simEnv B) O "Comptype_ok" "%|-%:OK" []
      (.tuple [c, .case "STRUCT" (.case "%" (.tuple [.list fs]))]) :=
  dderivesB_of_ruleAt RefOkB.ruleAt_comptypeOkStruct (self_mem_conclAlts _)
    (listσ c "fieldtype*" fs)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hT _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_resE (x := "fieldtype") rfl
      fun _ => rfl)))
    (premsB_one (dpremB_iter1 rfl fun w hw => .rulePr (evalArgs_nil _ _)
      (evalExp_tup2 (evalExp_var (by simp [listσ, VarEnv.findVal?, VarEnv.bindVals, Map.binds,
        Map.bind])) (evalExp_var rfl)) (h w hw)))

/-- **`Comptype_ok/array`.** -/
theorem dd_comptypeOkArray (O : ElseI) {c f : Value} (hc : CtxT B c)
    (hT : TypedV (simEnv B) (.varT "fieldtype" []) f)
    (h : DDerivesB (simEnv B) O "Fieldtype_ok" "%|-%:OK" [] (.tuple [c, f])) :
    DDerivesB (simEnv B) O "Comptype_ok" "%|-%:OK" [] (.tuple [c, .case "ARRAY" f]) :=
  dderivesB_of_ruleAt ruleAt_comptypeOkArray (self_mem_conclAlts _) [("C", c), ("fieldtype", f)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hT _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_var rfl)))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) h))

/-- The scope of `Comptype_ok/func`. -/
def funcσ (c : Value) (ps rs : List Value) : List (IL.Id × Value) :=
  [("C", c), ("t_1*", .list ps), ("t_2*", .list rs)]

/-- **`Comptype_ok/func`**, from two `Resulttype_ok`. -/
theorem dd_comptypeOkFunc (O : ElseI) {c : Value} (hc : CtxT B c) {ps rs : List Value}
    (hp : ∀ t ∈ ps, TypedV (simEnv B) (.varT "valtype" []) t)
    (hr : ∀ t ∈ rs, TypedV (simEnv B) (.varT "valtype" []) t)
    (dp : DDerivesB (simEnv B) O "Resulttype_ok" "%|-%:OK" []
      (.tuple [c, .case "%" (.tuple [.list ps])]))
    (dr : DDerivesB (simEnv B) O "Resulttype_ok" "%|-%:OK" []
      (.tuple [c, .case "%" (.tuple [.list rs])])) :
    DDerivesB (simEnv B) O "Comptype_ok" "%|-%:OK" []
      (.tuple [c, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list ps]),
        .case "%" (.tuple [.list rs])])]) :=
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals (funcσ c ps rs)) (resE "t_1")
      (.case "%" (.tuple [.list ps])) := evalExp_resE rfl fun _ => rfl
  have e₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals (funcσ c ps rs)) (resE "t_2")
      (.case "%" (.tuple [.list rs])) := evalExp_resE rfl fun _ => rfl
  dderivesB_of_ruleAt ruleAt_comptypeOkFunc (self_mem_conclAlts _) (funcσ c ps rs)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hp _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (typedV_list_iff.2 hr _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_tup2 e₁ e₂)))
    (premsB_two (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) e₁) dp)
      (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) e₂) dr))

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
