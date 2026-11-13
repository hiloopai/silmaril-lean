module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XLocal

/-!
# Instruction typing of the wasm-3.0 script, extended: `local.get` is exact

* `localGet_head`: the head `LOCAL.GET` occurs only in rule 52 of `Instr_ok` (`decide` on the rule
  list of `simEnv B`);
* `localGet_inv`: under `DDerivesB`, an `Instr_ok` fact at `LOCAL.GET (idxV n)` in `ctxL ls` has a
  type `[] -> [u]` with `ls[n] = %%(SET, u)`;
* `localGet_sat_iff`: so, in a bounded context `{locals := L}`, the satisfaction condition at
  `local.get x` is exact, at every instruction type: `stepModel BI` has the `Instr_ok` fact exactly
  when Core validates the typing.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV idxV instrtypeV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV ruleHead headsOk instrOk_heads head_of_headsOk
  mem_conclAlts_head instrHead_some eval_head instrOk_params)

variable {B : Builtins}

/-- The head `o` occurs at rule `k` only. -/
def headAt (o : MixopS) (k : Nat) (rules : List Rule) : Bool :=
  rules.zipIdx.all fun (r, j) => ruleHead r != some o || j == k

set_option maxRecDepth 100000 in
/-- **`LOCAL.GET` is typed by rule 52 only.** -/
theorem localGet_head : ∃ ps t rules,
    (simEnv B).findRel? "Instr_ok" = some (ps, "%|-%:%", t, rules) ∧
      headAt "LOCAL.GET" 52 rules = true :=
  ⟨_, _, _, rfl, by decide⟩

/-- A rule at index `j` with head `o`, in a list passing `headAt o k`, is rule `k`. -/
theorem eq_of_headAt {o : MixopS} {k : Nat} {rules : List Rule} (h : headAt o k rules = true)
    {j : Nat} {r : Rule} (hj : rules[j]? = some r) (ho : ruleHead r = some o) : j = k := by
  have hm : (r, j) ∈ rules.zipIdx := List.mem_zipIdx_iff_getElem?.2 hj
  have hr := List.all_eq_true.1 h _ hm
  simpa [ho] using hr

/-- The conclusion of a rule passing `headsOk`, evaluated at `(c, OP w, it)`, has head `OP`. -/
theorem ruleHead_of_eval {rules : List Rule} (hh : headsOk rules = true) {j : Nat} {nm : IL.Id}
    {qs : List Param} {e e' : Exp} {prems : List Prem}
    (hj : rules[j]? = some (.ruleD nm qs "%|-%:%" e prems)) (halt : e' ∈ conclAlts e) {ρ : VarEnv}
    {c w it : Value} {op : MixopS} (he : EvalExp (simEnv B) ρ e' (.tuple [c, .case op w, it])) :
    ruleHead (.ruleD nm qs "%|-%:%" e prems) = some op := by
  obtain ⟨o, hho, -⟩ := head_of_headsOk hh hj
  obtain ⟨a, b, c', rfl⟩ := instrHead_some hho
  obtain ⟨a', b', c'', rfl⟩ := mem_conclAlts_head halt
  rw [hho, eval_head he]

/-- `Instr_ok/local.get`, as a rule. -/
def localGetRule : Rule :=
  .ruleD "local.get" [Round6.AgreeSub.ctxP, .expP "x" (.varT "idx" []), .expP "t" (.varT "valtype" [])]
    "%|-%:%" (.tupE [.varE "C", .caseE "LOCAL.GET" (.varE "x"), itLXE [] [] [.varE "t"]])
    [.ifPr (.cmpE .eqOp .boolT localsAtE (.caseE "%%" (.tupE [.caseE "SET" (.tupE []), .varE "t"])))]

/-- Two lookups of one relation agree. -/
theorem findRel_inj {env : Env} {x : IL.Id} {a b : List Param × MixopS × Typ × List Rule}
    (h₁ : env.findRel? x = some a) (h₂ : env.findRel? x = some b) : a = b :=
  Option.some.inj (h₁.symm.trans h₂)

/-- Rule 52 of `Instr_ok` is `localGetRule`, and `Instr_ok` has no parameters. -/
theorem instrOk_rule52 {ps : List Param} {t : Typ} {rules : List Rule} {r : Rule}
    (hrel : (simEnv B).findRel? "Instr_ok" = some (ps, "%|-%:%", t, rules))
    (hrule : rules[52]? = some r) : r = localGetRule ∧ ps = [] := by
  obtain ⟨_, _, _, hrel', -, hk⟩ := ruleAt_localGet (B := B)
  have e : rules = _ := congrArg (·.2.2.2) (findRel_inj hrel hrel')
  subst e
  exact ⟨Option.some.inj (hrule.symm.trans hk), instrOk_params hrel⟩

/-- **The rule behind an `Instr_ok` fact at `LOCAL.GET`** is rule 52, read under some scope. -/
theorem localGet_rule {O : ElseI} {c w it : Value}
    (h : DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, .case "LOCAL.GET" w, it])) :
    ∃ σ : List (IL.Id × Value),
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.tupE [.varE "C", .caseE "LOCAL.GET" (.varE "x"), itLXE [] [] [.varE "t"]])
        (.tuple [c, .case "LOCAL.GET" w, it]) ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT localsAtE
        (.caseE "%%" (.tupE [.caseE "SET" (.tupE []), .varE "t"]))) (.bool true) := by
  cases h with
  | rule hrel hrule halt hps _ he hp =>
    obtain ⟨ps₀, t₀, rules₀, hrel₀, hh⟩ := instrOk_heads (B := B)
    obtain ⟨ps₁, t₁, rules₁, hrel₁, ha⟩ := localGet_head (B := B)
    have e₀ := congrArg (·.2.2.2) (findRel_inj hrel₀ hrel)
    have e₁ := congrArg (·.2.2.2) (findRel_inj hrel₁ hrel)
    dsimp only at e₀ e₁
    have hj := eq_of_headAt (e₁ ▸ ha) hrule (ruleHead_of_eval (e₀ ▸ hh) hrule halt he)
    obtain ⟨hr, rfl⟩ := instrOk_rule52 hrel (hj ▸ hrule)
    obtain ⟨-, -, -, rfl, rfl⟩ := Rule.ruleD.inj hr
    have hρ : _ = VarEnv.empty := Option.some.inj hps.symm
    have he' : _ = _ := List.mem_singleton.1 halt
    subst hρ he'
    have hif := hp _ (List.mem_singleton_self _)
    cases hif with
    | ifPr h => exact ⟨_, he, h⟩

/-- `%%(SET, u)`, read back from an equation that holds. -/
theorem eqTrue_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp}
    (h : EvalExp env ρ (.cmpE .eqOp .boolT e₁ e₂) (.bool true)) :
    ∃ v, EvalExp env ρ e₁ v ∧ EvalExp env ρ e₂ v := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  obtain rfl := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hc
  exact ⟨v₁, h₁, h₂⟩

/-- `C.LOCALS[x.0]`, read back in `C = ctxL ls`, `x = idxV n`. -/
theorem localsAt_inv {env : Env} {ρ : VarEnv} {ls : List Value} {n : Nat} {u : Value}
    (hC : ρ.findVal? "C" = some (ctxL ls)) (hx : ρ.findVal? "x" = some (idxV n))
    (h : EvalExp env ρ localsAtE u) : ls[n]? = some u := by
  obtain ⟨lv, i, hl, hi, hidx⟩ := evalExp_idxE_iff.1 h
  obtain ⟨cv, hc, hf⟩ := evalExp_dotE_iff.1 hl
  obtain rfl : cv = ctxL ls := Option.some.inj ((evalExp_varE_iff.1 hc).symm.trans hC)
  obtain rfl : lv = .list ls := (Option.some.inj hf).symm
  obtain ⟨vs, hvs, -, hvi⟩ := evalExp_projE_iff.1 hi
  have hxv := evalExp_varE_iff.1 (evalExp_uncaseE_iff.1 hvs)
  rw [hx] at hxv
  obtain rfl : vs = [Equiv.Validation.natV n] := by
    simp only [idxV, Option.some.injEq] at hxv
    cases hxv
    rfl
  obtain rfl : i = n := by
    simpa [Equiv.Validation.natV] using hvi.symm
  simpa [Value.idx?] using hidx

/-- A pair expression, inverted. -/
theorem evalExp_tup2_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) :
    ∃ a b, v = .tuple [a, b] ∧ EvalExp env ρ e₁ a ∧ EvalExp env ρ e₂ b := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨a, ws, rfl, ha, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨b, ws', rfl, hb, hws'⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hws'
  exact ⟨a, b, rfl, ha, hb⟩

/-- The type of `local.get`, in a scope binding `t` to `u`. -/
theorem evalExp_itLocalGet {env : Env} {ρ : VarEnv} {u : Value} (hu : ρ.findVal? "t" = some u) :
    EvalExp env ρ (itLXE [] [] [.varE "t"]) (itV [] [] [u]) :=
  evalExp_case (evalExp_tup3 Instr30.evalExp_resNil Instr30.evalExp_nil
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_list1 (Sim.evalExp_var hu))
      evalExps_nil, rfl⟩)))

/-- **Inversion at `local.get`**: an `Instr_ok` fact at `LOCAL.GET (idxV n)` in `ctxL ls` has a
type `[] -> [u]` with `ls[n] = %%(SET, u)`. -/
theorem localGet_inv {O : ElseI} {ls : List Value} {n : Nat} {it : Value}
    (h : DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxL ls, .case "LOCAL.GET" (idxV n), it])) :
    ∃ u, it = itV [] [] [u] ∧ ls[n]? = some (.case "%%" (.tuple [.case "SET" (.tuple []), u])) := by
  obtain ⟨σ, he, hp⟩ := localGet_rule h
  obtain ⟨_, _, _, heq, h1, h2, h3⟩ := Round6.RefOkV.evalExp_tup3_ex he
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  obtain ⟨xv, hxv, hxe⟩ := evalExp_caseE_iff.1 h2
  obtain rfl := (Value.case.inj hxe).2
  obtain ⟨v, hl, hr⟩ := eqTrue_inv hp
  have hls := localsAt_inv (evalExp_varE_iff.1 h1) (evalExp_varE_iff.1 hxv) hl
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 hr
  obtain ⟨a, u, rfl, ha, hu⟩ := evalExp_tup2_inv hw
  obtain rfl := ha.unique (Round6.AgreeSub.evalExp_atomE "SET")
  exact ⟨u, h3.unique (evalExp_itLocalGet (evalExp_varE_iff.1 hu)), hls⟩

/-! ## Exactness at `local.get` -/

/-- An instruction type whose image is `[] -> [u]` is `[] -> [t]` with `tyV t = u`. -/
theorem instrtypeV_res1 {it : InstrType} {u : Value} (h : instrtypeV it = itV [] [] [u]) :
    ∃ t, it = .plain [] [t] ∧ tyV t = u := by
  obtain ⟨ps, xs, rs⟩ := it
  simp only [Instr30.instrtypeV_eq, itV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
    Value.list.injEq, List.map_eq_nil_iff, List.map_eq_singleton_iff, true_and, and_true] at h
  obtain ⟨rfl, rfl, t, rfl, rfl⟩ := h
  exact ⟨t, rfl, rfl⟩

/-- A local type whose image is `%%(SET, u)` is set, at a type with image `u`. -/
theorem localV_set {lt : LocalType} {u : Value}
    (h : localV lt = .case "%%" (.tuple [.case "SET" (.tuple []), u])) :
    lt.init = .set ∧ tyV lt.type = u := by
  obtain ⟨i, t⟩ := lt
  cases i <;> simp_all [localV, initV]

/-- **The satisfaction condition at `local.get` is exact**, in every evaluator `simEnv B`, under
every reading of `otherwise`, in a bounded context `{locals := L}`, at every instruction type. -/
theorem localGet_sat_iff (O : ElseI) {L : List LocalType} (hL : ∀ lt ∈ L, LocalBnd lt)
    (x : LocalIdx) {it : InstrType} :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
        (.tuple [ctxL (L.map localV), instrToV (.localGet x), instrtypeV it]) ↔
      InstrOk (ctxLoc L) (.localGet x) it := by
  refine ⟨fun h => ?_, local_preserves O hL (.inl ⟨x, rfl⟩)⟩
  obtain ⟨u, hit, hls⟩ := localGet_inv h
  rw [List.getElem?_map] at hls
  obtain ⟨lt, hlt, hv⟩ := Option.map_eq_some_iff.1 hls
  obtain ⟨hi, rfl⟩ := localV_set hv
  obtain ⟨t, rfl, ht⟩ := instrtypeV_res1 hit
  obtain rfl := Equiv.Validation.tyV_inj _ _ ht
  obtain ⟨i, t'⟩ := lt
  obtain rfl : i = .set := hi
  exact .variable (.localGet hlt)

end Silmaril.Wasm.SpecTec.Institution.Instr30X
