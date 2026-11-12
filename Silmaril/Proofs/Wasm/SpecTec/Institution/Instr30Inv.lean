module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30Heads
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30Derive

/-!
# Instruction typing of the wasm-3.0 script: inverting `Instr_ok` at `nop` and `drop`

Under `DDerivesB`, in any evaluator `simEnv B` and any reading `O` of `otherwise`:

* `nop_inv`: an `Instr_ok` fact at `NOP` has the type `[] -> []`;
* `drop_inv`: an `Instr_ok` fact at `DROP` has a type `[u] -> []` with `Valtype_ok` at `u`, in the
  same context.

Both rest on `instrOk_heads` (only rule 0 types `NOP`, only rule 2 types `DROP`) and on
`mem_conclAlts_head` (the reading of conclusions keeps the head).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading

variable {B : Builtins}

/-- A conclusion with a head is a triple whose middle is a case with that head. -/
theorem instrHead_some {e : Exp} {o : MixopS} (h : instrHead e = some o) :
    ∃ a b c, e = .tupE [a, .caseE o b, c] := by
  unfold instrHead at h
  split at h
  · cases h
    exact ⟨_, _, _, rfl⟩
  · cases h

/-- A triple `(a, OP b, c)` evaluates to a triple whose middle has head `OP`. -/
theorem eval_head {env : Env} {ρ : VarEnv} {a b c : Exp} {o op : MixopS} {x w y : Value}
    (h : EvalExp env ρ (.tupE [a, .caseE o b, c]) (.tuple [x, .case op w, y])) : o = op := by
  obtain ⟨_, _, _, he, -, hb, -⟩ := Round6.RefOkV.evalExp_tup3_ex h
  obtain ⟨_, -, hw⟩ := evalExp_caseE_iff.1 hb
  simp only [Value.tuple.injEq, List.cons.injEq] at he
  rw [← he.2.1] at hw
  exact (Value.case.inj hw).1.symm

/-- `Instr_ok` has no parameters. -/
theorem instrOk_params {ps : List Param} {t : Typ} {rules : List Rule}
    (h : (simEnv B).findRel? "Instr_ok" = some (ps, "%|-%:%", t, rules)) : ps = [] := by
  obtain ⟨ps₁, t₁, rules₁, hrel₁, hps₁, -⟩ := ruleAt_nop (B := B)
  have hd : (ps₁, "%|-%:%", t₁, rules₁) = (ps, "%|-%:%", t, rules) :=
    Option.some.inj (hrel₁.symm.trans h)
  exact (Prod.mk.inj hd).1 ▸ hps₁

/-- What `instrOk_rule` concludes: rule `j` of `Instr_ok`, read at `e'` under `σ`. -/
def RuleBehind (O : ElseI) (c w it : Value) (op : MixopS) : Prop :=
  ∃ (rules : List Rule) (ps : List Param) (t : Typ) (j : Nat) (nm : IL.Id) (qs : List Param)
    (e : Exp) (prems : List Prem) (e' : Exp) (σ : List (IL.Id × Value)),
    (simEnv B).findRel? "Instr_ok" = some (ps, "%|-%:%", t, rules) ∧
    rules[j]? = some (.ruleD nm qs "%|-%:%" e prems) ∧ e' ∈ conclAlts e ∧
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ) e' (.tuple [c, .case op w, it]) ∧
    (∀ pr ∈ prems, DPremB (simEnv B) O (O "Instr_ok" [] j (.tuple [c, .case op w, it]))
      (VarEnv.empty.bindVals σ) pr) ∧
    (op = "NOP" → j = 0) ∧ (op = "DROP" → j = 2)

/-- The components of a `DDerivesB` derivation of `Instr_ok` at a head give `RuleBehind`. -/
theorem ruleBehind_of {O : ElseI} {c w it : Value} {op : MixopS} {ps : List Param} {t : Typ}
    {rules : List Rule} {j : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp}
    {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
    (hrel : (simEnv B).findRel? "Instr_ok" = some (ps, "%|-%:%", t, rules))
    (hrule : rules[j]? = some (.ruleD nm qs "%|-%:%" e prems)) (halt : e' ∈ conclAlts e)
    (hps : bindParams VarEnv.empty ps [] = some ρ₀)
    (he : EvalExp (simEnv B) (ρ₀.bindVals σ) e' (.tuple [c, .case op w, it]))
    (hp : ∀ pr ∈ prems, DPremB (simEnv B) O (O "Instr_ok" [] j (.tuple [c, .case op w, it]))
      (ρ₀.bindVals σ) pr) : RuleBehind (B := B) O c w it op := by
  obtain ⟨ps₀, t₀, rules₀, hrel₀, hok⟩ := instrOk_heads (B := B)
  have hd : (ps₀, "%|-%:%", t₀, rules₀) = (ps, "%|-%:%", t, rules) :=
    Option.some.inj (hrel₀.symm.trans hrel)
  have hrs : rules₀ = rules := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hd).2).2).2
  have hρ : ρ₀ = VarEnv.empty := by
    simpa only [instrOk_params hrel, bindParams, Option.some.injEq] using hps.symm
  have hrule₀ : rules₀[j]? = some (.ruleD nm qs "%|-%:%" e prems) := hrs ▸ hrule
  obtain ⟨o, hho, h0, -, h2⟩ : ∃ o, ruleHead (.ruleD nm qs "%|-%:%" e prems) = some o ∧
      (o = "NOP" → j = 0) ∧ (o = "UNREACHABLE" → j = 1) ∧ (o = "DROP" → j = 2) :=
    head_of_headsOk hok hrule₀
  obtain ⟨a, b, c', he₀⟩ : ∃ a b c, e = .tupE [a, .caseE o b, c] := instrHead_some hho
  have halt' : e' ∈ conclAlts (.tupE [a, .caseE o b, c']) := he₀ ▸ halt
  obtain ⟨a', b', c'', he'⟩ : ∃ a' b' c'', e' = .tupE [a', .caseE o b', c''] :=
    mem_conclAlts_head halt'
  have hev : EvalExp (simEnv B) (ρ₀.bindVals σ) (.tupE [a', .caseE o b', c''])
      (.tuple [c, .case op w, it]) := he' ▸ he
  have hoe : o = op := eval_head hev
  exact ⟨rules, ps, t, j, nm, qs, e, prems, e', σ, hrel, hrule, halt, hρ ▸ he, hρ ▸ hp,
    fun h => h0 (hoe.trans h), fun h => h2 (hoe.trans h)⟩

/-- **The rule behind an `Instr_ok` fact at a given head**: its index `j` in the rule list of
`simEnv B`, with the head's index constraints of `head_of_headsOk`. -/
theorem instrOk_rule {O : ElseI} {c w it : Value} {op : MixopS}
    (h : DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, .case op w, it])) :
    RuleBehind (B := B) O c w it op := by
  cases h with
  | rule hrel hrule halt hps _ he hp => exact ruleBehind_of hrel hrule halt hps he hp

/-- `Instr_ok/nop`'s conclusion has no optional atoms, so it is its only reading. -/
theorem conclAlts_nop :
    conclAlts (.tupE [.varE "C", .caseE "NOP" (.tupE []), itNilE]) =
      [.tupE [.varE "C", .caseE "NOP" (.tupE []), itNilE]] := rfl

/-- **Inversion at `nop`**: an `Instr_ok` fact at `NOP` has the type `[] -> []`. -/
theorem nop_inv {O : ElseI} {c it : Value}
    (h : DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, .case "NOP" (.tuple []), it])) :
    it = itV [] [] [] := by
  obtain ⟨rules, ps, t, j, nm, qs, e, prems, e', σ, hrel, hrule, halt, he, -, h0, -⟩ :=
    instrOk_rule h
  obtain rfl := h0 rfl
  obtain ⟨_, _, _, hrel', -, hk⟩ := ruleAt_nop (B := B)
  rw [hrel] at hrel'
  obtain rfl := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Option.some.inj hrel')).2).2).2
  rw [hrule] at hk
  obtain ⟨-, -, -, rfl, -⟩ := Rule.ruleD.inj (Option.some.inj hk)
  rw [conclAlts_nop, List.mem_singleton] at halt
  subst halt
  obtain ⟨_, _, _, heq, -, -, h3⟩ := Round6.RefOkV.evalExp_tup3_ex he
  simp only [Value.tuple.injEq, List.cons.injEq] at heq
  rw [heq.2.2.1]
  exact h3.unique evalExp_itNil

/-- A relational premise `r(C, t)`, inverted. -/
theorem prem_rule_ct {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {r : IL.Id} {op : MixopS}
    {c u : Value} (hc : ρ.findVal? "C" = some c) (hu : ρ.findVal? "t" = some u)
    (h : DPremB env O els ρ (.rulePr r [] op (.tupE [.varE "C", .varE "t"]))) :
    DDerivesB env O r op [] (.tuple [c, u]) := by
  cases h with
  | rulePr ha he hd =>
    obtain rfl := Silmaril.SpecTec.Equiv.Validation.evalArgs_nil_iff.1 ha
    rwa [he.unique (evalExp_tup2 (Sim.evalExp_var hc) (Sim.evalExp_var hu))] at hd

/-- `Instr_ok/drop`'s conclusion has no optional atoms, so it is its only reading. -/
theorem conclAlts_drop :
    conclAlts (.tupE [.varE "C", .caseE "DROP" (.tupE []), itDropE]) =
      [.tupE [.varE "C", .caseE "DROP" (.tupE []), itDropE]] := rfl

/-- The type of `drop` evaluates to `[u] -> []`, where `u` is the value of `t`. -/
theorem itDrop_inv {env : Env} {ρ : VarEnv} {it : Value} (h : EvalExp env ρ itDropE it) :
    ∃ u, ρ.findVal? "t" = some u ∧ it = itV [u] [] [] := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨p, l, r, rfl, hp, hl, hr⟩ := Round6.RefOkV.evalExp_tup3_ex hw
  obtain ⟨p', hp', rfl⟩ := evalExp_caseE_iff.1 hp
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hp'
  obtain ⟨a, ws, rfl, ha, hws⟩ := Silmaril.SpecTec.Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain rfl := Silmaril.SpecTec.Equiv.Validation.evalExps_nil_iff.1 hws
  obtain ⟨us, hus, rfl⟩ := evalExp_listE_iff.1 ha
  obtain ⟨u, us', rfl, hu, hus'⟩ := Silmaril.SpecTec.Equiv.Validation.evalExps_cons_iff.1 hus
  obtain rfl := Silmaril.SpecTec.Equiv.Validation.evalExps_nil_iff.1 hus'
  obtain rfl := hl.unique evalExp_nil
  obtain rfl := hr.unique evalExp_resNil
  exact ⟨u, evalExp_varE_iff.1 hu, rfl⟩

/-- **Inversion at `drop`**: an `Instr_ok` fact at `DROP` has a type `[u] -> []`, and `u` is a
`Valtype_ok` fact in the same context. -/
theorem drop_inv {O : ElseI} {c it : Value}
    (h : DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, .case "DROP" (.tuple []), it])) :
    ∃ u, it = itV [u] [] [] ∧ DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, u]) := by
  obtain ⟨rules, ps, t, j, nm, qs, e, prems, e', σ, hrel, hrule, halt, he, hp, -, h2⟩ :=
    instrOk_rule h
  obtain rfl := h2 rfl
  obtain ⟨_, _, _, hrel', -, hk⟩ := ruleAt_drop (B := B)
  rw [hrel] at hrel'
  obtain rfl := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Option.some.inj hrel')).2).2).2
  rw [hrule] at hk
  obtain ⟨-, -, -, rfl, rfl⟩ := Rule.ruleD.inj (Option.some.inj hk)
  rw [conclAlts_drop, List.mem_singleton] at halt
  subst halt
  obtain ⟨_, _, _, heq, h1, -, h3⟩ := Round6.RefOkV.evalExp_tup3_ex he
  simp only [Value.tuple.injEq, List.cons.injEq] at heq
  obtain ⟨rfl, -, rfl, -⟩ := heq
  obtain ⟨u, hu, rfl⟩ := itDrop_inv h3
  exact ⟨u, rfl, prem_rule_ct (evalExp_varE_iff.1 h1) hu (hp _ (List.mem_singleton_self _))⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30
