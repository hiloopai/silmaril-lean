module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Basic
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Numerics

/-!
# Their `Step_exp` read by `DDerives`: rule lookup, heads, typing of encodings

* `rulesOf`, `findRel_stepF`, `findRel_reduceF` (and `…O` for the original script): the relations
  `Step_exp` and `Reduce_exp` as the environments hold them; the literal rules of `Rules` are at
  the stated indices (`rfl`).
* `lhsHead`: the constructor on the left of a rule's conclusion `S |- C … ~> …`. A derivation
  whose left-hand side is `con c _` comes from a rule with head `c` (`head_of_body`), and the
  rules with each head the fragment uses are listed by computation (`headsF_*`).
* Typing: every encoding the rules quantify over has the IL type the rule declares (`typedV_enc`,
  `typedV_encNum`, the operator lemmas, `typedV_emptyS`); an expression typed `val` is a literal
  (`lit_of_typedV_val`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (DDerives DPrem QuantsOk TypedV ValsOnly otherwise)

set_option maxRecDepth 100000

/-! ## Relations and rules -/

/-- The rules of relation `x` in `env` (empty if there is none). -/
noncomputable def rulesOf (env : Env) (x : IL.Id) : List Rule :=
  match env.findRel? x with
  | some (_, _, _, rs) => rs
  | none => []

/-- The type `S × exp × exp` of `Step_exp` and `Reduce_exp`. -/
def sxxT : Typ := .tupT [.mk "_" (.varT "S" []), .mk "_" (.varT "exp" []), .mk "_" (.varT "exp" [])]

theorem findRel_stepF :
    envF.findRel? "Step_exp" = some ([], "%|-%~>%", sxxT, rulesOf envF "Step_exp") := rfl

theorem findRel_reduceF :
    envF.findRel? "Reduce_exp" = some ([], "%|-%~>*%", sxxT, rulesOf envF "Reduce_exp") := rfl

theorem findRel_stepO :
    envO.findRel? "Step_exp" = some ([], "%|-%~>%", sxxT, rulesOf envO "Step_exp") := rfl

theorem findRel_reduceO :
    envO.findRel? "Reduce_exp" = some ([], "%|-%~>*%", sxxT, rulesOf envO "Reduce_exp") := rfl

theorem reduceF_rules : rulesOf envF "Reduce_exp" = [Rules.F.redNormal, Rules.F.redStep] := rfl
theorem reduceO_rules : rulesOf envO "Reduce_exp" = [Rules.O.redNormal, Rules.O.redStep] := rfl

theorem stepF_0 : (rulesOf envF "Step_exp")[0]? = some Rules.F.unCtx := rfl
theorem stepF_1 : (rulesOf envF "Step_exp")[1]? = some Rules.F.unBool := rfl
theorem stepF_2 : (rulesOf envF "Step_exp")[2]? = some Rules.F.unNum := rfl
theorem stepF_3 : (rulesOf envF "Step_exp")[3]? = some Rules.F.binCtx1 := rfl
theorem stepF_4 : (rulesOf envF "Step_exp")[4]? = some Rules.F.binCtx2 := rfl
theorem stepF_5 : (rulesOf envF "Step_exp")[5]? = some Rules.F.binBool := rfl
theorem stepF_6 : (rulesOf envF "Step_exp")[6]? = some Rules.F.binNum := rfl
theorem stepF_7 : (rulesOf envF "Step_exp")[7]? = some Rules.F.cmpCtx1 := rfl
theorem stepF_8 : (rulesOf envF "Step_exp")[8]? = some Rules.F.cmpCtx2 := rfl
theorem stepF_9 : (rulesOf envF "Step_exp")[9]? = some Rules.F.cmpEqTrue := rfl
theorem stepF_10 : (rulesOf envF "Step_exp")[10]? = some Rules.F.cmpEqFalse := rfl
theorem stepF_11 : (rulesOf envF "Step_exp")[11]? = some Rules.F.cmpNeFalse := rfl
theorem stepF_12 : (rulesOf envF "Step_exp")[12]? = some Rules.F.cmpNeTrue := rfl
theorem stepF_13 : (rulesOf envF "Step_exp")[13]? = some Rules.F.cmpNum := rfl

theorem stepO_0 : (rulesOf envO "Step_exp")[0]? = some Rules.O.unCtx := rfl
theorem stepO_1 : (rulesOf envO "Step_exp")[1]? = some Rules.O.unBool := rfl
theorem stepO_2 : (rulesOf envO "Step_exp")[2]? = some Rules.O.unNum := rfl
theorem stepO_3 : (rulesOf envO "Step_exp")[3]? = some Rules.O.binCtx1 := rfl
theorem stepO_4 : (rulesOf envO "Step_exp")[4]? = some Rules.O.binCtx2 := rfl
theorem stepO_5 : (rulesOf envO "Step_exp")[5]? = some Rules.O.binBool := rfl
theorem stepO_6 : (rulesOf envO "Step_exp")[6]? = some Rules.O.binNum := rfl
theorem stepO_7 : (rulesOf envO "Step_exp")[7]? = some Rules.O.cmpCtx1 := rfl
theorem stepO_8 : (rulesOf envO "Step_exp")[8]? = some Rules.O.cmpCtx2 := rfl
theorem stepO_9 : (rulesOf envO "Step_exp")[9]? = some Rules.O.cmpEqTrue := rfl
theorem stepO_10 : (rulesOf envO "Step_exp")[10]? = some Rules.O.cmpNeFalse := rfl
theorem stepO_11 : (rulesOf envO "Step_exp")[11]? = some Rules.O.cmpNum := rfl

/-! ## Heads -/

/-- The constructor of a `CaseE`. -/
def headOfCase : Exp → Option MixopS
  | .caseE c _ => some c
  | _ => none

/-- The constructor in the middle of a conclusion `(S, C …, …)`. -/
def headOfConcl : Exp → Option MixopS
  | .tupE [_, e, _] => headOfCase e
  | _ => none

/-- The constructor on the left of a conclusion `S |- C … ~> …`. -/
def lhsHead : Rule → Option MixopS
  | .ruleD _ _ _ e _ => headOfConcl e

theorem headOfCase_spec {e : Exp} {c : MixopS} (h : headOfCase e = some c) :
    ∃ e₀, e = .caseE c e₀ := by
  cases e <;> simp_all [headOfCase]

theorem headOfConcl_spec {e : Exp} {c : MixopS} (h : headOfConcl e = some c) :
    ∃ e₁ e₂ e₃, e = .tupE [e₁, e₂, e₃] ∧ headOfCase e₂ = some c := by
  unfold headOfConcl at h
  split at h
  · exact ⟨_, _, _, rfl, h⟩
  · cases h

/-- The indices of the rules with head `c`. -/
def headIdx (rs : List Rule) (c : MixopS) : List Nat :=
  (List.range rs.length).filter fun i => (rs[i]?.bind lhsHead) == some c

theorem mem_headIdx {rs : List Rule} {i : Nat} {r : Rule} {c : MixopS} (h : rs[i]? = some r)
    (hc : lhsHead r = some c) : i ∈ headIdx rs c := by
  obtain ⟨hi, hr⟩ := List.getElem?_eq_some_iff.1 h
  simp [headIdx, hi, hr, hc]

theorem headsF_un : headIdx (rulesOf envF "Step_exp") "UN" = [0, 1, 2] := by decide
theorem headsF_bin : headIdx (rulesOf envF "Step_exp") "BIN" = [3, 4, 5, 6] := by decide
theorem headsF_cmp :
    headIdx (rulesOf envF "Step_exp") "CMP" = [7, 8, 9, 10, 11, 12, 13] := by decide
theorem headsF_bool : headIdx (rulesOf envF "Step_exp") "BOOL" = [] := by decide
theorem headsF_nat : headIdx (rulesOf envF "Step_exp") "NAT" = [] := by decide
theorem headsF_int : headIdx (rulesOf envF "Step_exp") "INT" = [] := by decide

/-- A rule body whose left-hand side is `case c w` comes from a rule with head `c`. -/
theorem head_of_body {env : Env} {D : Sim.Interp} {els : Prop} {op : MixopS} {r : Rule}
    {S w x : Value} {c c' : MixopS}
    (hb : Sim.RuleBody env D els [] [] op r (.tuple [S, .case c w, x]))
    (hh : lhsHead r = some c') : c' = c := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := hb
  obtain ⟨e₁, e₂, e₃, rfl, h₂⟩ := headOfConcl_spec hh
  obtain ⟨e₀, rfl⟩ := headOfCase_spec h₂
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 he
  obtain ⟨w₁, ws₁, -, hws₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws₂, hw₂, -, rfl⟩ := evalExps_cons_iff.1 hws₁
  obtain ⟨u, -, hu⟩ := evalExp_caseE_iff.1 hw₂
  have hv' : S = w₁ ∧ Value.case c w = w₂ ∧ [x] = ws₂ := by simpa using hv
  have hw : Value.case c w = w₂ := hv'.2.1
  rw [hu] at hw
  exact (Value.case.inj hw).1.symm

/-- Every rule of `Step_exp` has a head. -/
theorem headsF_all : ∀ (i : Nat) (r : Rule), (rulesOf envF "Step_exp")[i]? = some r →
    (lhsHead r).isSome := by
  intro i r h
  have hi : i < (rulesOf envF "Step_exp").length := (List.getElem?_eq_some_iff.1 h).1
  have hall : ∀ j < (rulesOf envF "Step_exp").length,
      (((rulesOf envF "Step_exp")[j]?).bind lhsHead).isSome := by decide
  have := hall i hi
  rwa [h] at this

theorem evalArgs_nil_eq {env : Env} {ρ : VarEnv} {ws : List ArgV} (h : EvalArgs env ρ [] ws) :
    ws = [] := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [evalArgs] at h
  | succ n =>
      simp only [evalArgs, List.mapM_nil] at h
      exact (Except.ok.inj h).symm

theorem evalExp_tuple' {env : Env} {ρ : VarEnv} {x₁ x₂ x₃ : IL.Id} {v₁ v₂ v₃ : Value}
    (h₁ : ρ.findVal? x₁ = some v₁) (h₂ : ρ.findVal? x₂ = some v₂) (h₃ : ρ.findVal? x₃ = some v₃) :
    EvalExp env ρ (.tupE [.varE x₁, .varE x₂, .varE x₃]) (.tuple [v₁, v₂, v₃]) :=
  evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var h₁) (evalExps_cons (evalExp_var h₂)
    (evalExps_cons (evalExp_var h₃) evalExps_nil)), rfl⟩

/-! ## Reading `Reduce_exp` as the reflexive-transitive closure of `Step_exp` -/

/-- A tuple of three variables evaluates to their values. -/
theorem evalExp_tup3_vars {env : Env} {ρ : VarEnv} {x₁ x₂ x₃ : IL.Id} {w : Value}
    (h : EvalExp env ρ (.tupE [.varE x₁, .varE x₂, .varE x₃]) w) :
    ∃ v₁ v₂ v₃, w = .tuple [v₁, v₂, v₃] ∧ ρ.findVal? x₁ = some v₁ ∧ ρ.findVal? x₂ = some v₂ ∧
      ρ.findVal? x₃ = some v₃ := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, ws₁, h₁, hws₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws₂, h₂, hws₂, rfl⟩ := evalExps_cons_iff.1 hws₁
  obtain ⟨w₃, ws₃, h₃, hws₃, rfl⟩ := evalExps_cons_iff.1 hws₂
  obtain rfl := evalExps_nil_iff.1 hws₃
  exact ⟨w₁, w₂, w₃, rfl, evalExp_varE_iff.1 h₁, evalExp_varE_iff.1 h₂, evalExp_varE_iff.1 h₃⟩

theorem evalExp_tup3_vars_eq {env : Env} {ρ : VarEnv} {x₁ x₂ x₃ : IL.Id} {v₁ v₂ v₃ : Value}
    (h : EvalExp env ρ (.tupE [.varE x₁, .varE x₂, .varE x₃]) (.tuple [v₁, v₂, v₃])) :
    ρ.findVal? x₁ = some v₁ ∧ ρ.findVal? x₂ = some v₂ ∧ ρ.findVal? x₃ = some v₃ := by
  obtain ⟨u₁, u₂, u₃, hu, h₁, h₂, h₃⟩ := evalExp_tup3_vars h
  have e : v₁ = u₁ ∧ v₂ = u₂ ∧ v₃ = u₃ := by simpa using hu
  obtain ⟨rfl, rfl, rfl⟩ := e
  exact ⟨h₁, h₂, h₃⟩

/-- The `step` rule's first premise, `Step_exp (S, e, e')`, as a step from the value of `e`. -/
theorem reduce_step_prem {env : Env} {O : Sim.ElseI} {els : Prop} {ρ : VarEnv} {S a : Value}
    (hS : ρ.findVal? "S" = some S) (ha : ρ.findVal? "e" = some a)
    (h : DPrem env O els ρ (.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE "S", .varE "e",
      .varE "e'"]))) :
    ∃ b, ρ.findVal? "e'" = some b ∧ DDerives env O "Step_exp" "%|-%~>%" [] (.tuple [S, a, b]) := by
  cases h with
  | rulePr hargs he hd =>
    obtain ⟨v₁, v₂, b, rfl, h₁, h₂, h₃⟩ := evalExp_tup3_vars he
    rw [hS] at h₁
    rw [ha] at h₂
    obtain rfl := Option.some.inj h₁
    obtain rfl := Option.some.inj h₂
    rw [evalArgs_nil_eq hargs] at hd
    exact ⟨b, h₃, hd⟩

/-- `normal`'s conclusion `(S, e, e)` has equal sides. -/
theorem reduce_normal_eq {env : Env} {ρ : VarEnv} {S a c : Value}
    (h : EvalExp env ρ (.tupE [.varE "S", .varE "e", .varE "e"]) (.tuple [S, a, c])) : a = c := by
  obtain ⟨-, h₂, h₃⟩ := evalExp_tup3_vars_eq h
  rw [h₂] at h₃
  exact Option.some.inj h₃

/-- The relation lookup of a `DDerives.rule` of `Reduce_exp`. -/
theorem reduce_lookup {env : Env} {nrm stp : Rule} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {ρ₀ : VarEnv}
    (hfind : env.findRel? "Reduce_exp" = some ([], "%|-%~>*%", sxxT, [nrm, stp]))
    (hrel : env.findRel? "Reduce_exp" = some (ps, op, t, rules))
    (hps : bindParams VarEnv.empty ps [] = some ρ₀) :
    rules = [nrm, stp] ∧ ρ₀ = VarEnv.empty := by
  rw [hfind] at hrel
  have e : [] = ps ∧ "%|-%~>*%" = op ∧ sxxT = t ∧ [nrm, stp] = rules := by simpa using hrel
  obtain ⟨rfl, -, -, rfl⟩ := e
  exact ⟨rfl, by simpa [bindParams] using hps.symm⟩

/-- The premises of a non-`Reduce_exp` premise satisfy the `reduce_rec` motive vacuously. -/
theorem reduce_motive_rulePr {env : Env} {P : Value → Value → Value → Prop}
    {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp} {avs : List ArgV}
    {w : Value} (ha : EvalArgs env ρ args avs) (he : EvalExp env ρ e w)
    (ih : x = "Reduce_exp" → avs = [] → ∀ S a c, w = .tuple [S, a, c] → P S a c) :
    ∀ e', Prem.rulePr x args op e = .rulePr "Reduce_exp" [] "%|-%~>*%" e' →
      ∀ w', EvalExp env ρ e' w' → ∀ S a c, w' = .tuple [S, a, c] → P S a c := by
  intro e' heq w' he' S a c hw
  obtain ⟨rfl, rfl, -, rfl⟩ := Prem.rulePr.inj heq
  rw [he'.unique he] at hw
  exact ih rfl (evalArgs_nil_eq ha) S a c hw

/-- The motive `reduce_rec` gives a premise: a `Reduce_exp` premise satisfies `P`. -/
def ReduceMotive (env : Env) (P : Value → Value → Value → Prop) (ρ : VarEnv) (pr : Prem) : Prop :=
  ∀ e, pr = .rulePr "Reduce_exp" [] "%|-%~>*%" e →
    ∀ w, EvalExp env ρ e w → ∀ S a c, w = .tuple [S, a, c] → P S a c

/-- The rule case of `reduce_rec`: `normal` gives `P` by reflexivity, `step` by prefixing. -/
theorem reduce_rule_case {env : Env} {O : Sim.ElseI} {nrm stp : Rule}
    (hfind : env.findRel? "Reduce_exp" = some ([], "%|-%~>*%", sxxT, [nrm, stp]))
    (hnrm : nrm = .ruleD "normal" [.expP "S" (.varT "S" []), .expP "e" (.varT "exp" [])]
      "%|-%~>*%" (.tupE [.varE "S", .varE "e", .varE "e"]) [])
    (hstp : stp = .ruleD "step" [.expP "S" (.varT "S" []), .expP "e" (.varT "exp" []),
        .expP "e''" (.varT "exp" []), .expP "e'" (.varT "exp" [])] "%|-%~>*%"
      (.tupE [.varE "S", .varE "e", .varE "e''"])
      [.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE "S", .varE "e", .varE "e'"]),
        .rulePr "Reduce_exp" [] "%|-%~>*%" (.tupE [.varE "S", .varE "e'", .varE "e''"])])
    (P : Value → Value → Value → Prop) (hrefl : ∀ S a, P S a a)
    (hstep : ∀ S a b c, DDerives env O "Step_exp" "%|-%~>%" [] (.tuple [S, a, b]) →
      P S b c → P S a c) {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem} {ρ₀ : VarEnv}
    {σ : List (IL.Id × Value)} {els : Prop} {S a c : Value}
    (hrel : env.findRel? "Reduce_exp" = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems))
    (hps : bindParams VarEnv.empty ps [] = some ρ₀)
    (he : EvalExp env (ρ₀.bindVals σ) e (.tuple [S, a, c]))
    (hp : ∀ pr ∈ prems, DPrem env O els (ρ₀.bindVals σ) pr)
    (ih : ∀ pr ∈ prems, ReduceMotive env P (ρ₀.bindVals σ) pr) : P S a c := by
  obtain ⟨rfl, rfl⟩ := reduce_lookup hfind hrel hps
  match i, hrule with
  | 0, hrule =>
    obtain ⟨-, -, -, rfl, rfl⟩ := Rule.ruleD.inj (Option.some.inj (hnrm ▸ hrule).symm)
    exact reduce_normal_eq he ▸ hrefl _ _
  | 1, hrule =>
    obtain ⟨-, -, -, rfl, rfl⟩ := Rule.ruleD.inj (Option.some.inj (hstp ▸ hrule).symm)
    obtain ⟨hS, ha, hc⟩ := evalExp_tup3_vars_eq he
    obtain ⟨b, hb, hd⟩ := reduce_step_prem hS ha (hp _ (List.mem_cons_self ..))
    exact hstep _ _ _ _ hd (ih _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl _
      (evalExp_tuple' hS hb hc) _ _ _ rfl)

/-- A `Reduce_exp` derivation is a chain of `Step_exp` steps: any property closed under prefixing
a step and holding reflexively holds of it. The proof is the recursor of the mutual
`DDerives`/`DPrem`, with `DPrem`'s motive saying that a `Reduce_exp` premise satisfies it. -/
theorem reduce_rec {env : Env} {O : Sim.ElseI} {nrm stp : Rule}
    (hfind : env.findRel? "Reduce_exp" = some ([], "%|-%~>*%", sxxT, [nrm, stp]))
    (hnrm : nrm = .ruleD "normal" [.expP "S" (.varT "S" []), .expP "e" (.varT "exp" [])]
      "%|-%~>*%" (.tupE [.varE "S", .varE "e", .varE "e"]) [])
    (hstp : stp = .ruleD "step" [.expP "S" (.varT "S" []), .expP "e" (.varT "exp" []),
        .expP "e''" (.varT "exp" []), .expP "e'" (.varT "exp" [])] "%|-%~>*%"
      (.tupE [.varE "S", .varE "e", .varE "e''"])
      [.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE "S", .varE "e", .varE "e'"]),
        .rulePr "Reduce_exp" [] "%|-%~>*%" (.tupE [.varE "S", .varE "e'", .varE "e''"])])
    (P : Value → Value → Value → Prop) (hrefl : ∀ S a, P S a a)
    (hstep : ∀ S a b c, DDerives env O "Step_exp" "%|-%~>%" [] (.tuple [S, a, b]) →
      P S b c → P S a c) :
    ∀ {S a c : Value}, DDerives env O "Reduce_exp" "%|-%~>*%" [] (.tuple [S, a, c]) →
      P S a c := by
  intro S a c h
  refine Sim.DDerives.rec
    (motive_1 := fun x _ args v _ => x = "Reduce_exp" → args = [] →
      ∀ S a c, v = .tuple [S, a, c] → P S a c)
    (motive_2 := fun _ ρ pr _ => ReduceMotive env P ρ pr)
    ?_ (by intros; simp_all [ReduceMotive]) (by intros; simp_all [ReduceMotive])
    (by intros; simp_all [ReduceMotive]) (fun ha he _ ih => reduce_motive_rulePr ha he ih)
    (by intros; simp_all [ReduceMotive]) (by intros; simp_all [ReduceMotive])
    (by intros; simp_all [ReduceMotive]) (by intros; simp_all [ReduceMotive]) h rfl rfl S a c rfl
  intro x op args v ps t rules i nm qs e prems ρ₀ σ hrel hrule hps _ he hp ih hx hargs S a c hv
  subst hx hargs hv
  exact reduce_rule_case hfind hnrm hstp P hrefl hstep hrel hrule hps he hp ih

end Silmaril.Wasm.SpecTec.Meta
