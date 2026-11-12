module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecStepRules
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `Step_pure/array.new`, the last rule of the 218 to be transcribed

`array.new` was the one rule of the reduction relation left untranscribed,
and the reason is in its right-hand side: it *replicates* one value `n`
times, and the IL spells that as an iteration whose **domain list is empty**

    (iter (sub (var "val") …) (listn (var "n")) )          -- no `dom`

rather than an iteration over a bound sequence.  Every other `listN`
iteration in the relation carries exactly one domain; this is the only
`ds = []`.  With no domain there is nothing to bind per round, so the body
is matched against each of the `n` elements in the *same* scope — which is
precisely what "the same value, `n` times" means, and why the rule needs no
premise to say the elements agree.

Transcribing it makes **all 218 rules of the reduction relation** carry
provenance by `rfl` against the pinned stream.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecPureArrayNew

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-- `Step_pure/array.new`, rule 41 of the pinned stream. -/
def arrayNewRule : Rule :=
    (.ruleD "array.new" [(.expP "val" (.varT "val" [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.listE [(.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.NEW" (.varE "x"))]), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [])) (.listE [(.caseE "ARRAY.NEW_FIXED" (.tupE [(.varE "x"), (.caseE "%" (.tupE [(.varE "n")]))]))]))]) [])

set_option maxRecDepth 8000000 in
/-- Discharged by `rfl` against the pinned stream.  With this, all 218 rules
of `Step_pure`, `Step` and `Step_read` are transcribed with provenance. -/
theorem hasArrayNew_wasm30 :
    HasRuleAt (envOfScript Specs.wasm30) "Step_pure" "%~>%" 41 arrayNewRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## What a domain-free iteration means

`matchIterList` with `ds = []` runs `matchRounds`, which matches the body
against each element **in the same scope** and keeps only `findVals? []`,
i.e. nothing; then `matchExps … [] (iterCols rows 0)`, i.e. nothing again.  So
the iteration binds nothing and demands only that every element match the
body.  Here the body is `val` with `val` already bound, so every element must
*equal* it — the replicate. -/

/-- Matching a bound variable against every element of a list, round by
round, succeeds exactly when every element is that variable's value.  The
round index is irrelevant: with no `ListN` counter variable there is nothing
for it to bind. -/
theorem matchRounds_boundVar_iff {env : Env} {ρ : VarEnv} {x : IL.Id} {w : Value}
    {t₁ t₂ : Typ} : ∀ {vs : List Value} {i : Nat}, ρ.findVal? x = some w →
    ((∃ n rows, matchRounds n env ρ (.subE (.varE x) t₁ t₂) [] none i vs = .ok rows) ↔
      ∀ u ∈ vs, u = w)
  | [], _, _ => ⟨fun _ u hu => absurd hu (by simp),
      fun _ => ⟨1, [], by simp [matchRounds]⟩⟩
  | u :: vs, i, hx => by
    constructor
    · rintro ⟨n, rows, hn⟩
      cases n with
      | zero => simp [matchRounds] at hn
      | succ n =>
        rw [matchRounds] at hn
        simp only [Res.bind_eq_ok] at hn
        obtain ⟨σ, hσ, -, -, rest, hrest, -⟩ := hn
        obtain rfl : u = w := by
          have h : MatchExp env ρ (.subE (.varE x) t₁ t₂) u σ := ⟨n, hσ⟩
          rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hx] at h
          exact h.1
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · rfl
        · exact ((matchRounds_boundVar_iff (vs := vs) (i := i + 1) hx).1
            ⟨n, rest, hrest⟩) v hv
    · intro hall
      have hu : u = w := hall u (by simp)
      obtain ⟨n, rows, hn⟩ :=
        (matchRounds_boundVar_iff (vs := vs) (i := i + 1) hx).2
          (fun v hv => hall v (by simp [hv]))
      obtain ⟨m, hm⟩ : MatchExp env ρ (.subE (.varE x) t₁ t₂) u ρ :=
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hx).2 ⟨hu, rfl⟩)
      refine ⟨max n m + 1, [] :: rows, ?_⟩
      rw [matchRounds]
      have hm' : matchExp (max n m) env ρ (.subE (.varE x) t₁ t₂) u = .ok ρ :=
        Sem.matchExp_ok_of_le (Nat.le_max_right n m) hm
      have hn' : matchRounds (max n m) env ρ (.subE (.varE x) t₁ t₂) [] none (i + 1) vs
          = .ok rows := Execution.matchRounds_ok_of_le (Nat.le_max_left n m) hn
      simp [hm', hn', VarEnv.findVals?, Res.ofOption]

/-- **The replicate pattern, inverted.**  `val^n` with `val` and `n` both
already bound matches exactly the list of `n` copies of `val` — and only when
`n`'s value is a `nat` numeral, since `matchIterE`'s `ListN` case matches the
counter against `|vs|`. -/
theorem matchExp_replicateN_iff {env : Env} {ρ ρ' : VarEnv} {x cnt : IL.Id}
    {w nv : Value} {t₁ t₂ : Typ} {v : Value}
    (hx : ρ.findVal? x = some w) (hc : ρ.findVal? cnt = some nv) :
    MatchExp env ρ
      (.iterE (.subE (.varE x) t₁ t₂) (.mk (.listN (.varE cnt) none) [])) v ρ' ↔
      ∃ k, nv = .num (.natN k) ∧ v = .list (List.replicate k w) ∧ ρ' = ρ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [Sem.matchExp] at hn
    | succ n =>
      simp only [Sem.matchExp] at hn
      cases n with
      | zero => simp [Sem.matchIterE] at hn
      | succ n =>
        simp only [Sem.matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok,
          Value.asList?_eq_some] at hn
        obtain ⟨vs, rfl, ρ₀, hρ₀, hlist⟩ := hn
        obtain ⟨rfl, rfl⟩ :=
          (matchExp_boundVar_iff hc).1 (⟨n, hρ₀⟩ : MatchExp env ρ (.varE cnt) _ ρ₀)
        cases n with
        | zero => simp [Sem.matchIterList] at hlist
        | succ n =>
          simp only [Sem.matchIterList, Res.bind_eq_ok] at hlist
          obtain ⟨rows, hrows, hcols⟩ := hlist
          have hall : ∀ u ∈ vs, u = w :=
            (matchRounds_boundVar_iff hx).1 ⟨n, rows, hrows⟩
          obtain ⟨-, rfl⟩ := Validation.matchExps_nil_iff.1
            (⟨n, hcols⟩ : MatchExps env ρ₀ [] _ ρ')
          have hrep : vs = List.replicate vs.length w := by
            rw [List.eq_replicate_iff]; exact ⟨rfl, hall⟩
          exact ⟨vs.length, rfl, by rw [← hrep], rfl⟩
  · rintro ⟨k, rfl, rfl, rfl⟩
    obtain ⟨n, rows, hn⟩ :=
      (matchRounds_boundVar_iff (t₁ := t₁) (t₂ := t₂) (env := env)
        (vs := List.replicate k w) (i := 0) hx).2
        (by intro u hu; exact List.eq_of_mem_replicate hu)
    obtain ⟨m, hm⟩ : MatchExp env ρ' (.varE cnt) (.num (.natN k)) ρ' :=
      (matchExp_boundVar_iff hc).2 ⟨by simp, rfl⟩
    refine ⟨max n m + 4, ?_⟩
    simp only [Sem.matchExp, Sem.matchIterE, Value.asList?_list, Res.ofOption,
      Res.bind_eq_ok, Sem.matchIterList, Sem.iterCols, List.map_nil]
    exact ⟨List.replicate k w, by simp,
      ρ', by simp [hc], rows, Execution.matchRounds_ok_of_le (by omega) hn,
      by simp [Sem.matchExps]⟩

/-- `patLen` of the replicate pattern: the counter's value, read off directly.
This is what makes the right-hand side's concatenation split deterministically
rather than by search. -/
theorem patLen_replicateN {env : Env} {ρ : VarEnv} {e : Exp} {z : IL.Id} {j : Nat}
    (hz : ρ.findVal? z = some (.num (.natN j))) :
    Sem.patLen 2 env ρ (.iterE e (.mk (.listN (.varE z) none) [])) = .ok j := by
  simp [Sem.patLen, Sem.evalExp, hz, Res.ofOption, Bind.bind, Except.bind]

/-- The length side condition of `matchExp_catE_leftLen_iff` is not an extra
assumption either. -/
theorem le_of_matchExp_catE_leftLen {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp}
    {us : List Value} {k m : Nat} (hk : Sem.patLen m env ρ e₁ = .ok k)
    (h : MatchExp env ρ (.catE e₁ e₂) (.list us) ρ') : k ≤ us.length := by
  by_contra hlt
  exact ExecStepRules.not_matchExp_of_matchFails h
    (Execution.matchFails_catE_ofLeft hk (Or.inl (by omega)))

/-- **`Step_pure/array.new`, characterised exactly** — the 218th rule.

`array.new` takes a value and a count and produces that many copies, then
defers to `array.new_fixed`.  Two things the conclusion alone forces, and that
the written rule does not say out loud: the count must be a **`nat` numeral**,
because `matchIterE`'s `ListN` case matches the counter against `|vs|`; and
the output really is `List.replicate`, because the replicate iteration binds
nothing and so compares every element against the *same* `val`. -/
theorem ruleFires_arrayNew_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayNewRule ↔
      ∃ val k x,
        v = .tuple
          [.list [val, Execution.constV Execution.i32V (.case "%" (.tuple [.num (.natN k)])),
                  .case "ARRAY.NEW" x],
           .list (List.replicate k val ++
             [.case "ARRAY.NEW_FIXED"
               (.tuple [x, .case "%" (.tuple [.num (.natN k)])])])] := by
  unfold arrayNewRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    -- the left-hand side
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨val, c, an, τ₁, τ₂, rfl, hval, hc, han⟩ := matchExps_three_iff.1 hivs
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hval
    subst hval
    obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
    obtain ⟨nt, pc, τ₃, rfl, hnt, hpc⟩ := matchExps_two_iff.1 hcws
    rw [Execution.matchExp_caseNil_iff] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    obtain ⟨pw, rfl, hpw⟩ := Validation.matchExp_case_iff.1 hpc
    obtain ⟨pws, rfl, hpws⟩ := Validation.matchExp_tup_iff.1 hpw
    obtain ⟨nv, rfl, hnv⟩ := matchExps_one_iff.1 hpws
    rw [matchExp_freshVar_iff (by simp)] at hnv
    subst hnv
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 han
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    -- the right-hand side: a concatenation whose left operand has a length
    obtain ⟨us, rfl⟩ := ExecStepRules.matchExp_catE_isList hr
    obtain ⟨k, rfl⟩ : ∃ k : Nat, nv = .num (.natN k) := by
      obtain ⟨vs, kk, υ, hvs, ha, -⟩ := ExecReadControl.matchExp_catE_dest hr
      obtain ⟨cnt, hcnt, -, -⟩ := (matchExp_replicateN_iff (env := env)
        (ρ := (((VarEnv.empty.bindVal "val" val).bindVal "n" nv).bindVal "x" x))
        (x := "val") (cnt := "n") (w := val) (nv := nv)
        (by simp) (by simp)).1 ha
      exact ⟨cnt, hcnt⟩
    have hpl := patLen_replicateN (env := env)
      (ρ := ((((VarEnv.empty.bindVal "val" val).bindVal "n"
        (Value.num (Num.natN k))).bindVal "x" x)))
      (e := .subE (.varE "val") (.varT "val" []) (.varT "instr" []))
      (z := "n") (j := k) (by simp)
    rw [ExecStepRules.matchExp_catE_leftLen_iff hpl
      (le_of_matchExp_catE_leftLen hpl hr)] at hr
    obtain ⟨υ, ha, hb⟩ := hr
    obtain ⟨k', hk', hrep, rfl⟩ := (matchExp_replicateN_iff
      (x := "val") (cnt := "n") (w := val) (nv := Value.num (Num.natN k))
      (by simp) (by simp)).1 ha
    obtain rfl : k = k' := by simpa using hk'
    obtain ⟨bvs, hbvs, hbs⟩ := Validation.matchExp_list_iff.1 hb
    obtain ⟨f, rfl, hf⟩ := matchExps_one_iff.1 hbs
    obtain ⟨fw, rfl, hfw⟩ := Validation.matchExp_case_iff.1 hf
    obtain ⟨fws, rfl, hfws⟩ := Validation.matchExp_tup_iff.1 hfw
    obtain ⟨x', pn, τ₄, rfl, hx', hpn⟩ := matchExps_two_iff.1 hfws
    rw [matchExp_boundVar_iff (w := x) (by simp)] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    obtain ⟨pw', rfl, hpw'⟩ := Validation.matchExp_case_iff.1 hpn
    obtain ⟨pws', rfl, hpws'⟩ := Validation.matchExp_tup_iff.1 hpw'
    obtain ⟨nv', rfl, hnv'⟩ := matchExps_one_iff.1 hpws'
    rw [matchExp_boundVar_iff (w := Value.num (Num.natN k)) (by simp)] at hnv'
    obtain ⟨rfl, rfl⟩ := hnv'
    refine ⟨val, k, x', ?_⟩
    have h1 : us.take k = List.replicate k val := by injection hrep
    have h2 : us.drop k = [Value.case "ARRAY.NEW_FIXED"
        (.tuple [x', .case "%" (.tuple [.num (.natN k)])])] := by injection hbvs
    have hus : us = us.take k ++ us.drop k := (List.take_append_drop _ _).symm
    rw [h1, h2] at hus
    rw [hus]
    rfl
  · rintro ⟨val, k, x, rfl⟩
    refine ⟨(((VarEnv.empty.bindVal "val" val).bindVal "n"
        (Value.num (Num.natN k))).bindVal "x" x), (((VarEnv.empty.bindVal "val" val).bindVal "n"
        (Value.num (Num.natN k))).bindVal "x" x), matchExp_concl_iff.2 ⟨_, _,
      (((VarEnv.empty.bindVal "val" val).bindVal "n"
        (Value.num (Num.natN k))).bindVal "x" x), rfl, ?_, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _,
          (VarEnv.empty.bindVal "val" val),
          ((VarEnv.empty.bindVal "val" val).bindVal "n" (Value.num (Num.natN k))),
          rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_one_iff.2 ⟨_, rfl,
                      (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · refine Execution.matchExp_catE_ofLeft (j := k) (m := 2)
        (σ := (((VarEnv.empty.bindVal "val" val).bindVal "n"
          (Value.num (Num.natN k))).bindVal "x" x))
        (patLen_replicateN (z := "n") (j := k) (by simp)) (by simp) ?_ ?_
      · refine (matchExp_replicateN_iff (x := "val") (cnt := "n") (w := val)
          (nv := Value.num (Num.natN k)) (by simp) (by simp)).2 ⟨k, rfl, ?_, rfl⟩
        simp
      · have hd : (List.replicate k val ++
            [Value.case "ARRAY.NEW_FIXED"
              (.tuple [x, .case "%" (.tuple [.num (.natN k)])])]).drop k
            = [Value.case "ARRAY.NEW_FIXED"
              (.tuple [x, .case "%" (.tuple [.num (.natN k)])])] := by simp
        rw [hd]
        exact Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_two_iff.2 ⟨_, _, _, rfl,
                    (matchExp_boundVar_iff (w := x) (by simp)).2 ⟨rfl, rfl⟩,
                    Validation.matchExp_case_iff.2 ⟨_, rfl,
                      Validation.matchExp_tup_iff.2 ⟨_, rfl,
                        matchExps_one_iff.2 ⟨_, rfl,
                          (matchExp_boundVar_iff
                            (w := Value.num (Num.natN k)) (by simp)).2
                            ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩

end Silmaril.SpecTec.Equiv.ExecPureArrayNew
