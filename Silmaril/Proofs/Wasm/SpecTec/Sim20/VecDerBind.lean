module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerCensus

/-!
# Derivations that avoid the six rules bind harmlessly

`quantsV_of_rule` gives `QuantsV` at one rule instance whose value is `VOk`. To have it at every
instance of a derivation, the premise derivations must be at `VOk` values too. Their values are
the premise expressions, evaluated in the rule's scope.

* `bldB n ec e`: `e` is built by variables at pattern positions of `ec`, subtype coercions,
  tuples, lists, concatenations, iterations that read their variable back, and constructors other
  than `VUNOP`, `VBINOP`, `VRELOP`. **`vOk_of_bldB`**: if `ec` evaluates to a `VOk` value, so does
  `e`.
* `premOkB ec pr`: a premise that consults a relation is a top-level `rulePr` of `Step`,
  `Step_pure` or `Step_read` without arguments whose expression passes `bldB` at `ec`; every other
  premise consults no relation. `censusP` checks it on the three relations (kernel,
  `premCensus_step`, `premCensus_pure`, `premCensus_read`).
* `sideN`: the relation is one of the three and the rule is outside `patExcl`.
* **`toSideV`**: a `DDerivesBS sideN` derivation of `simEnv20T B` at a `VOk` value is a
  `DDerivesBS sideV` derivation, so (`VecDerTask.dderivesBS_toV'`) a derivation of
  `simEnv20V B`: **`dderivesBN_toV`**, `sstepBN_toV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (ElseI)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB conclAlts SStepB otherwiseB)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (relFreeB evalExps_mem)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (VOk fams opOf)

/-! ## Built values -/

/-- The three operator constructors. -/
def famOps : List String := ["VUNOP", "VBINOP", "VRELOP"]

/-- **`e` is built from variables at pattern positions of `ec`** (fuel `n`). -/
def bldB : Nat → Exp → Exp → Bool
  | 0, _, _ => false
  | _ + 1, ec, .varE x => patB 64 ec x
  | n + 1, ec, .subE e _ _ => bldB n ec e
  | n + 1, ec, .caseE op e => !famOps.contains op && bldB n ec e
  | n + 1, ec, .tupE es => es.all fun e => bldB n ec e
  | n + 1, ec, .listE es => es.all fun e => bldB n ec e
  | n + 1, ec, .catE a b => bldB n ec a && bldB n ec b
  | _ + 1, ec, .iterE b (.mk it [.mk x (.varE z)]) =>
      iterX it && bodyX x b && x != "_" && patB 64 ec z
  | _ + 1, _, _ => false

/-- A constructor outside `famOps` carries no family payload. -/
theorem payOk_of_not_fam {op : MixopS} (h : famOps.contains op = false) (w : Value) :
    ∀ f ∈ fams, op = opOf f → VecAgree.PayOk f w := by
  intro f hf hop
  simp only [fams, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> simp [opOf] at hop <;> subst hop <;> simp [famOps] at h

/-- The statement of `vOk_of_bldB` at fuel `n`, against the conclusion `ec` at `ρ`. -/
def BldIH (env : Env) (ρ : VarEnv) (ec : Exp) (n : Nat) : Prop :=
  ∀ {e : Exp} {w : Value}, bldB n ec e = true → EvalExp env ρ e w → VOk w

section Cases

variable {env : Env} {ρ : VarEnv} {ec : Exp} {vc : Value} {n : Nat} {w : Value}

theorem bld_var (hc : EvalExp env ρ ec vc) (hvc : VOk vc) {x : IL.Id}
    (hb : bldB (n + 1) ec (.varE x) = true) (he : EvalExp env ρ (.varE x) w) : VOk w := by
  have hp : patB 64 ec x = true := by simpa [bldB] using hb
  exact vOk_of_patB 64 hp hc hvc (evalExp_varE_iff.1 he)

theorem bld_case (ih : BldIH env ρ ec n) {op : MixopS} {e : Exp}
    (hb : bldB (n + 1) ec (.caseE op e) = true) (he : EvalExp env ρ (.caseE op e) w) : VOk w := by
  have hb' : famOps.contains op = false ∧ bldB n ec e = true := by simpa [bldB] using hb
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 he
  exact .case op (ih hb'.2 hu) (payOk_of_not_fam hb'.1 u)

theorem bld_tup (ih : BldIH env ρ ec n) {es : List Exp}
    (hb : bldB (n + 1) ec (.tupE es) = true) (he : EvalExp env ρ (.tupE es) w) : VOk w := by
  have hb' : ∀ e ∈ es, bldB n ec e = true := by simpa [bldB] using hb
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 he
  refine .tuple fun u hu => ?_
  obtain ⟨e, hm, heu⟩ := evalExps_mem hvs u hu
  exact ih (hb' e hm) heu

theorem bld_list (ih : BldIH env ρ ec n) {es : List Exp}
    (hb : bldB (n + 1) ec (.listE es) = true) (he : EvalExp env ρ (.listE es) w) : VOk w := by
  have hb' : ∀ e ∈ es, bldB n ec e = true := by simpa [bldB] using hb
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 he
  refine .list fun u hu => ?_
  obtain ⟨e, hm, heu⟩ := evalExps_mem hvs u hu
  exact ih (hb' e hm) heu

/-- A concatenation of `VOk` values is `VOk`. -/
theorem vOk_cat {v₁ v₂ v : Value} (hc : Value.cat? v₁ v₂ = some v) (hv₁ : VOk v₁)
    (hv₂ : VOk v₂) : VOk v := by
  unfold Value.cat? at hc
  split at hc
  · obtain rfl := (Option.some.inj hc).symm
    refine .list fun u hu => ?_
    rcases List.mem_append.1 hu with hu | hu
    · exact VecAgree.vOk_list hv₁ u hu
    · exact VecAgree.vOk_list hv₂ u hu
  · obtain rfl := (Option.some.inj hc).symm; exact hv₂
  · obtain rfl := (Option.some.inj hc).symm; exact hv₁
  · cases hc

theorem bld_cat (ih : BldIH env ρ ec n) {a b : Exp}
    (hb : bldB (n + 1) ec (.catE a b) = true) (he : EvalExp env ρ (.catE a b) w) : VOk w := by
  have hb' : bldB n ec a = true ∧ bldB n ec b = true := by simpa [bldB] using hb
  obtain ⟨v₁, v₂, h₁, h₂, hcat⟩ := evalExp_catE_iff.1 he
  exact vOk_cat hcat (ih hb'.1 h₁) (ih hb'.2 h₂)

theorem bld_iter (hc : EvalExp env ρ ec vc) (hvc : VOk vc) {b : Exp} {ie : IterExp}
    (hb : bldB (n + 1) ec (.iterE b ie) = true) (he : EvalExp env ρ (.iterE b ie) w) : VOk w := by
  rcases ie with ⟨it, ds⟩
  rcases ds with _ | ⟨⟨x, ze⟩, _ | ⟨d, ds⟩⟩
  · simp [bldB] at hb
  · by_cases hz : ∃ z, ze = .varE z
    · obtain ⟨z, rfl⟩ := hz
      have hb' : ((iterX it = true ∧ bodyX x b = true) ∧ x ≠ "_") ∧ patB 64 ec z = true := by
        simpa [bldB] using hb
      obtain ⟨⟨⟨hit, hbx⟩, hx⟩, hp⟩ := hb'
      exact vOk_of_patB 64 hp hc hvc (evalExp_iterX_inv hit hbx hx he)
    · cases ze <;> simp_all [bldB]
  · simp [bldB] at hb

end Cases

/-- `vOk_of_bldB`, at every fuel. -/
theorem bldIH {env : Env} {ρ : VarEnv} {ec : Exp} {vc : Value} (hc : EvalExp env ρ ec vc)
    (hvc : VOk vc) : ∀ n, BldIH env ρ ec n
  | 0 => by
    intro hb
    simp [bldB] at hb
  | n + 1 => by
    intro hb he
    rename_i e w
    have ih : BldIH env ρ ec n := bldIH hc hvc n
    cases e with
    | varE x => exact bld_var hc hvc hb he
    | subE e t₁ t₂ => exact ih (by simpa [bldB] using hb) (evalExp_subE_iff.1 he)
    | caseE op e => exact bld_case ih hb he
    | tupE es => exact bld_tup ih hb he
    | listE es => exact bld_list ih hb he
    | catE a b => exact bld_cat ih hb he
    | iterE b ie => exact bld_iter hc hvc hb he
    | _ => simp [bldB] at hb

/-- **A value built from `VOk` pattern variables is `VOk`.** -/
theorem vOk_of_bldB {env : Env} {ρ : VarEnv} {ec : Exp} {vc : Value} (hc : EvalExp env ρ ec vc)
    (hvc : VOk vc) (n : Nat) {e : Exp} {w : Value} (hb : bldB n ec e = true)
    (he : EvalExp env ρ e w) : VOk w :=
  bldIH hc hvc n hb he

/-! ## The premise check -/

/-- One of the three reduction relations. -/
def stepRelB (y : IL.Id) : Bool := y == "Step" || y == "Step_pure" || y == "Step_read"

/-- **A premise whose derivation stays at `VOk` values**, against the conclusion `ec`. -/
def premOkB (ec : Exp) : Prem → Bool
  | .rulePr y args _ ep => stepRelB y && args.isEmpty && bldB 64 ec ep
  | pr => relFreeB pr

/-- Every rule of `x` outside `patExcl` passes `premOkB` at every conclusion alternative. -/
def censusP (x : String) (rules : List Rule) : Bool :=
  (List.range rules.length).all fun i => patExcl.contains (x, i) || match rules[i]? with
    | some (.ruleD _ _ _ e prems) => (conclAlts e).all fun ec => prems.all (premOkB ec)
    | none => true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem premCensus_step (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step" = some ([], "%~>%", t, rules) ∧ censusP "Step" rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem premCensus_pure (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
      censusP "Step_pure" rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem premCensus_read (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
      censusP "Step_read" rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

end Silmaril.Wasm.SpecTec.Sim20.VecDer
