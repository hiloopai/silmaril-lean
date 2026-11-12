module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecRef
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The default-matching principle, and the three rules it unblocks

Phase 4, continued.  `Equiv/ExecRef.lean` left `ref.i31` and `i31.get-num`
uncharacterised, with an informal reason: their *conclusions* contain a
`CallE`, and `matchExp` has no syntactic case for one, so it falls through to
`matchDefault`, which **evaluates** the pattern and compares it to the value
(`Sem/Eval.lean:1238-1242`; `eval.ml`'s `match_exp'` default).  Settling them
needs an inversion principle for that fall-through, which did not exist.

`Step_pure/br_table-lt` needs the same thing for a different former: its
conclusion is `(BR l*[i!%.0])`, an `IdxE`.

So this file builds the principle once —

* `matchDefault_iff` — a default match is exactly "the pattern evaluates to
  the value, and nothing is bound";
* `matchExp_callE_iff`, `matchExp_idxE_iff` — `matchExp` at the two formers
  that reach it here;

— and then uses it three times.

It belongs in `Sem/Eval.lean` beside the other `matchExp_*` inversions; it is
here because this is where it is first needed.

## What is proved

**`br_table`, both rules, characterised exactly.**  `br_table-ge` branches to
the default label; `br_table-lt` branches to `l*[i]`, and its conclusion is
matched by *evaluating* the index.

**`ref.i31` and `i31.get-num` fire at nothing, at the pin** — now as theorems
rather than as a remark.  `$wrap__` and `$extend__` are `hint(builtin)` with
no clause (`Equiv/Numerics.lean`), so the conclusion has no value.  With an
interpretation installed they would fire; `wasmIntBuiltins` does not interpret
them, and the file says so rather than quietly extending it.

Core 3.0's reduction relation stands at **44 / 218** characterised after this
file, with two more rules proved unfireable at the pin.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecDefault

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution
open Silmaril.SpecTec.Equiv.ExecRef (matchExp_numE_iff)

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## The default-matching principle -/

/-- A *default* match evaluates the pattern and compares (`eval.ml`'s
`match_exp'` fall-through).  It binds nothing. -/
theorem matchDefault_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value} :
    (∃ n, matchDefault n env ρ e v = .ok ρ') ↔ EvalExp env ρ e v ∧ ρ' = ρ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchDefault] at hn
    | succ m =>
        simp only [matchDefault, Res.bind_eq_ok, Res.assert_eq_ok] at hn
        obtain ⟨w, hw, hwv, hr⟩ := hn
        subst hwv
        exact ⟨⟨m, hw⟩, (Validation.okInj hr).symm⟩
  · rintro ⟨⟨n, hn⟩, rfl⟩
    exact ⟨n + 1, by
      simp only [matchDefault, hn, Bind.bind, Except.bind, Res.assert, reduceIte]⟩

/-- `matchExp` at a `CallE` is the default match. -/
theorem matchExp_callE_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {args : List Arg}
    {v : Value} :
    MatchExp env ρ (.callE x args) v ρ' ↔ CallDef env ρ x args v ∧ ρ' = ρ := by
  rw [show MatchExp env ρ (.callE x args) v ρ'
        ↔ ∃ n, matchDefault n env ρ (.callE x args) v = .ok ρ' from ?_,
    matchDefault_iff, evalExp_callE_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ m => exact ⟨m, by simpa only [matchExp] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [matchExp] using hn⟩

/-- `matchExp` at an `IdxE` is the default match. -/
theorem matchExp_idxE_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {v : Value} :
    MatchExp env ρ (.idxE e₁ e₂) v ρ' ↔ EvalExp env ρ (.idxE e₁ e₂) v ∧ ρ' = ρ := by
  rw [show MatchExp env ρ (.idxE e₁ e₂) v ρ'
        ↔ ∃ n, matchDefault n env ρ (.idxE e₁ e₂) v = .ok ρ' from ?_, matchDefault_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ m => exact ⟨m, by simpa only [matchExp] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [matchExp] using hn⟩

/-- `Step_pure/br_table-lt`, rule 13 of the pinned stream. -/
def brTableLtRule : Rule :=
  (.ruleD "br_table-lt" [(.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "l*" (.iterT (.varT "labelidx" []) .list)), (.expP "l'" (.varT "labelidx" []))]
   "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i")])), (.caseE "BR_TABLE" (.tupE [(.iterE (.varE "l") (.mk .list [(.mk "l" (.varE
   "l*"))])), (.varE "l'")]))]), (.listE [(.caseE "BR" (.idxE (.iterE (.varE "l") (.mk .list
   [(.mk "l" (.varE "l*"))])) (.projE (.uncaseE (.varE "i") "%") (0))))])]) [(.ifPr (.cmpE
   .ltOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.lenE (.iterE (.varE "l")
   (.mk .list [(.mk "l" (.varE "l*"))])))))])

/-- `Step_pure/br_table-ge`, rule 14 of the pinned stream. -/
def brTableGeRule : Rule :=
  (.ruleD "br_table-ge" [(.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "l*" (.iterT (.varT "labelidx" []) .list)), (.expP "l'" (.varT "labelidx" []))]
   "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i")])), (.caseE "BR_TABLE" (.tupE [(.iterE (.varE "l") (.mk .list [(.mk "l" (.varE
   "l*"))])), (.varE "l'")]))]), (.listE [(.caseE "BR" (.varE "l'"))])]) [(.ifPr (.cmpE
   .geOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.lenE (.iterE (.varE "l")
   (.mk .list [(.mk "l" (.varE "l*"))])))))])


/-- The pinned wasm-3.0 specification has the two `br_table` rules at those
indices inside `Step_pure`. -/
structure HasBrTableRules (env : Env) : Prop where
  /-- `Step_pure/br_table-lt`, rule 13. -/
  brTableLt : HasRuleAt env "Step_pure" "%~>%" 13 brTableLtRule
  /-- `Step_pure/br_table-ge`, rule 14. -/
  brTableGe : HasRuleAt env "Step_pure" "%~>%" 14 brTableGeRule

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- Discharged by `rfl` against the pinned stream. -/
theorem hasBrTableRules_wasm30 : HasBrTableRules (envOfScript Specs.wasm30) :=
  ⟨⟨_, _, _, rfl, rfl, rfl⟩, ⟨_, _, _, rfl, rfl, rfl⟩⟩

/-! ## `ref.i31` and `i31.get-num` fire at nothing, at the pin

Both put a call in the **conclusion**.  `matchExp_callE_iff` turns that into a
`CallDef`, and `$wrap__`/`$extend__` are `hint(builtin)` with no clause, so
there is nothing for the conclusion to be.  `Equiv/ExecRef.lean` stated this as
a remark; here it is a theorem. -/

set_option maxRecDepth 4000000 in
/-- **`ref.i31` fires at nothing, at the pin**: its conclusion names
`$wrap__`, which the pinned script leaves uninterpreted. -/
theorem not_ruleFires_refI31_pinned {v : Value} :
    ¬ RuleFires (envOfScript Specs.wasm30) "%~>%" [] [] v ExecRef.refI31Rule := by
  unfold ExecRef.refI31Rule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
  obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
  obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
  obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
  obtain ⟨tv, iv, κ, rfl, htv, hiv⟩ := matchExps_two_iff.1 hpvs
  rw [matchExp_caseNil_iff] at htv
  obtain ⟨rfl, rfl⟩ := htv
  rw [matchExp_freshVar_iff (by simp)] at hiv
  subst hiv
  rw [matchExp_caseNil_iff] at h2
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
  obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
  obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
  obtain ⟨hcall, -⟩ := matchExp_callE_iff.1 hrvv
  exact ExecBuiltins.not_callDef_of_nil (x := "wrap__") rfl rfl
    (fun _ => by simp [Builtins.none]) hcall

set_option maxRecDepth 4000000 in
/-- **`i31.get-num` fires at nothing, at the pin**, for the same reason:
`$extend__`. -/
theorem not_ruleFires_i31GetNum_pinned {v : Value} :
    ¬ RuleFires (envOfScript Specs.wasm30) "%~>%" [] [] v ExecRef.i31GetNumRule := by
  unfold ExecRef.i31GetNumRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
  obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
  obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
  rw [matchExp_freshVar_iff (by simp)] at hpv
  subst hpv
  obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
  rw [matchExp_freshVar_iff (by simp)] at hqv
  subst hqv
  obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
  obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
  obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
  obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
  obtain ⟨tv, cv, υ, rfl, htv2, hcv⟩ := matchExps_two_iff.1 hrvs
  rw [matchExp_caseNil_iff] at htv2
  obtain ⟨rfl, rfl⟩ := htv2
  obtain ⟨hcall, -⟩ := matchExp_callE_iff.1 hcv
  exact ExecBuiltins.not_callDef_of_nil (x := "extend__") rfl rfl
    (fun _ => by simp [Builtins.none]) hcall

/-! ## `br_table`

The last two `Step_pure` rules outside the vector block.  Both match the
label vector with a `*` iteration whose body is the domain variable, which
`matchExp_iterE_list_iff` handles; `br_table-lt`'s conclusion additionally
indexes it, which is where `matchExp_idxE_iff` is needed. -/

/-- `(BR_TABLE l* l')`. -/
def brTableV (ls : List Value) (l' : Value) : Value :=
  .case "BR_TABLE" (.tuple [.list ls, l'])

/-- The shared left-hand side: `(CONST I32 i) (BR_TABLE l* l')`. -/
theorem matchExp_brTableLhs_iff {env : Env} {ρ' : VarEnv} {vs : List Value} :
    MatchExps env VarEnv.empty
      [.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]),
       .caseE "BR_TABLE" (.tupE [.iterE (.varE "l") (.mk .list [.mk "l" (.varE "l*")]),
         .varE "l'"])] vs ρ' ↔
      ∃ iv ls l', vs = [Execution.constV Execution.i32V iv, brTableV ls l'] ∧
        ρ' = ((VarEnv.empty.bindVal "i" iv).bindVal "l*" (.list ls)).bindVal "l'" l' := by
  constructor
  · rintro h
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 h
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨tv, iv, κ, rfl, htv, hiv⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff (by simp)] at hiv
    subst hiv
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨lsv, l'v, μ, rfl, hls, hl'⟩ := matchExps_two_iff.1 hqvs
    rw [matchExp_iterE_list_iff (bindsVar_varE "l") (by simp) (by simp)] at hls
    obtain ⟨ls, rfl, hls'⟩ := hls
    rw [matchExp_freshVar_iff (by simp)] at hls'
    subst hls'
    rw [matchExp_freshVar_iff (by simp)] at hl'
    subst hl'
    exact ⟨iv, ls, l'v, rfl, rfl⟩
  · rintro ⟨iv, ls, l', rfl, rfl⟩
    exact matchExps_two_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_iterE_list_iff (bindsVar_varE "l") (by simp) (by simp)).2
              ⟨ls, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- `Step_pure/br_table-ge` (`4.3:127`): an index past the end takes the
default label. -/
theorem ruleFires_brTableGe_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brTableGeRule ↔
      ∃ k us ls l', v = Execution.stepV
          [Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN k) :: us))),
           brTableV ls l'] [Execution.brV l'] ∧ ls.length ≤ k := by
  unfold brTableGeRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨iv, ls, l', rfl, rfl⟩ := matchExp_brTableLhs_iff.1 has
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    rw [matchExp_boundVar_iff (w := l') (by simp)] at hrvv
    obtain ⟨rfl, rfl⟩ := hrvv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_imm_iff (x := "i") (c := iv) (by simp)] at hu₁
    obtain ⟨us, hus⟩ := hu₁
    obtain ⟨lvs, hlvs, rfl⟩ := evalExp_lenE_iff.1 hu₂
    have hiter : EvalExp env
        (((VarEnv.empty.bindVal "i" iv).bindVal "l*" (.list ls)).bindVal "l'" rv)
        (.iterE (.varE "l") (.mk .list [.mk "l" (.varE "l*")])) (.list ls) :=
      evalExp_iterBody_var (b := .varE "l") (d := 0)
        (fun σ w hw => by simpa [evalExp] using hw) (by simp) (y := "l*") (by simp)
    obtain rfl : ls = lvs := (Value.list.inj (EvalExp.unique hlvs hiter)).symm
    cases u₁ with
    | num m =>
        cases m with
        | natN k =>
            subst hus
            refine ⟨k, us, ls, rv, rfl, ?_⟩
            simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some,
              Except.ok.injEq, Value.bool.injEq, decide_eq_true_eq] at hcmp
            omega
        | _ => simp [cmpValues, Num.cmp] at hcmp
    | _ => simp [cmpValues] at hcmp
  · rintro ⟨k, us, ls, l', rfl, hk⟩
    refine ⟨((VarEnv.empty.bindVal "i" (.case "%" (.tuple (.num (.natN k) :: us)))).bindVal
        "l*" (.list ls)).bindVal "l'" l',
      ((VarEnv.empty.bindVal "i" (.case "%" (.tuple (.num (.natN k) :: us)))).bindVal
        "l*" (.list ls)).bindVal "l'" l',
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExp_brTableLhs_iff.2 ⟨_, ls, l', rfl, rfl⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_boundVar_iff (w := l') (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.num (.natN k), .num (.natN ls.length), ?_, ?_, ?_⟩
    · exact (evalExp_imm_iff (by simp)).2 ⟨us, rfl⟩
    · exact evalExp_lenE_iff.2 ⟨ls, evalExp_iterBody_var (b := .varE "l") (d := 0)
        (fun σ w hw => by simpa [evalExp] using hw) (by simp) (by simp), rfl⟩
    · simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
        Value.bool.injEq, decide_eq_true_eq]
      omega

/-- `Step_pure/br_table-lt` (`4.3:122`): an in-range index selects from the
table.  The conclusion `(BR l*[i!%.0])` is an `IdxE` *pattern*, so it is
matched by evaluating it — `matchExp_idxE_iff` — which is the whole reason
this file exists. -/
theorem ruleFires_brTableLt_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brTableLtRule ↔
      ∃ k us ls l' lk, v = Execution.stepV
          [Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN k) :: us))),
           brTableV ls l'] [Execution.brV lk] ∧ ls[k]? = some lk := by
  unfold brTableLtRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨iv, ls, l', rfl, rfl⟩ := matchExp_brTableLhs_iff.1 has
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨hidx, rfl⟩ := matchExp_idxE_iff.1 hrvv
    obtain ⟨w, k, hw, hk, hsel⟩ := evalExp_idxE_iff.1 hidx
    have hiter : EvalExp env
        (((VarEnv.empty.bindVal "i" iv).bindVal "l*" (.list ls)).bindVal "l'" l')
        (.iterE (.varE "l") (.mk .list [.mk "l" (.varE "l*")])) (.list ls) :=
      evalExp_iterBody_var (b := .varE "l") (d := 0)
        (fun σ w hw => by simpa [evalExp] using hw) (by simp) (y := "l*") (by simp)
    obtain rfl : w = .list ls := EvalExp.unique hw hiter
    rw [evalExp_imm_iff (x := "i") (c := iv) (by simp)] at hk
    obtain ⟨us, rfl⟩ := hk
    exact ⟨k, us, ls, l', rv, rfl, by simpa [Value.idx?] using hsel⟩
  · rintro ⟨k, us, ls, l', lk, rfl, hsel⟩
    have hlt : k < ls.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hsel
      exact absurd hsel (by simp)
    refine ⟨((VarEnv.empty.bindVal "i" (.case "%" (.tuple (.num (.natN k) :: us)))).bindVal
        "l*" (.list ls)).bindVal "l'" l',
      ((VarEnv.empty.bindVal "i" (.case "%" (.tuple (.num (.natN k) :: us)))).bindVal
        "l*" (.list ls)).bindVal "l'" l',
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExp_brTableLhs_iff.2 ⟨_, ls, l', rfl, rfl⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            matchExp_idxE_iff.2 ⟨evalExp_idxE_iff.2 ⟨.list ls, k, ?_, ?_,
              by simpa [Value.idx?] using hsel⟩, rfl⟩⟩⟩⟩⟩, ?_⟩
    · exact evalExp_iterBody_var (b := .varE "l") (d := 0)
        (fun σ w hw => by simpa [evalExp] using hw) (by simp) (y := "l*") (by simp)
    · exact (evalExp_imm_iff (by simp)).2 ⟨us, rfl⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_cmpE_iff.2 ⟨.num (.natN k), .num (.natN ls.length), ?_, ?_, ?_⟩
      · exact (evalExp_imm_iff (by simp)).2 ⟨us, rfl⟩
      · exact evalExp_lenE_iff.2 ⟨ls, evalExp_iterBody_var (b := .varE "l") (d := 0)
          (fun σ w hw => by simpa [evalExp] using hw) (by simp) (by simp), rfl⟩
      · simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
          Value.bool.injEq, decide_eq_true_eq]
        omega

end Silmaril.SpecTec.Equiv.ExecDefault
