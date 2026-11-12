module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecRead
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The table block of `Step_read`, characterised

Thirteen rules — `table.get` (two), `table.size`, `table.fill` (three),
`table.copy` (four) and `table.init` (three) — transcribed in
`Equiv/ExecRead.lean` as rules 25-37 of the pinned stream.

Every one of them reads the store only through `$table(z, x)` and
`$elem(z, y)`, and only through those accessors' `REFS` field.  So, exactly as
`ruleFires_refTestTrue_iff` keeps `$inst_reftype` abstract, the
characterisations below keep `$table` and `$elem` abstract: `RefsOf` says
"the accessor *denotes* a structure whose `REFS` field is this list", stated
with `ExecNumeric.Applies`, and never says what the accessor computes.  The
runtime bridge in `Equiv/RuntimeBridge/` is what will connect the other end.

## What is proved

Twelve exact `RuleFires` characterisations —

| rule | theorem |
| --- | --- |
| `table.get-oob` | `ruleFires_tableGetOob_iff` |
| `table.get-val` | `ruleFires_tableGetVal_iff` |
| `table.fill-oob` | `ruleFires_tableFillOob_iff` |
| `table.fill-zero` | `ruleFires_tableFillZero_iff` |
| `table.fill-succ` | `ruleFires_tableFillSucc_iff` |
| `table.copy-oob` | `ruleFires_tableCopyOob_iff` |
| `table.copy-zero` | `ruleFires_tableCopyZero_iff` |
| `table.copy-le` | `ruleFires_tableCopyLe_iff` |
| `table.copy-gt` | `ruleFires_tableCopyGt_iff` |
| `table.init-oob` | `ruleFires_tableInitOob_iff` |
| `table.init-zero` | `ruleFires_tableInitZero_iff` |
| `table.init-succ` | `ruleFires_tableInitSucc_iff` |

— and one rule that fires at nothing, `not_ruleFires_tableSize`.

## Findings

**`table.size` cannot fire.**  Its second premise is
`if $table(z, x).TYPE = at lim rt`, and `lim`/`rt` occur nowhere in the
conclusion.  SpecTec's source writes that as a destructuring equation, but the
elaborated IL keeps it an `IfPr`, and `Sem/Eval.lean` *evaluates* an `IfPr`
rather than solving it, so the premise has no value.  This is the only rule in
the thirteen that our premise semantics narrows away; it is a narrowing worth
recording, because the same shape (`if $mem(z, x).TYPE = at lim`) occurs in
`memory.size` and in several `memory.*` rules.

**The `else` premises are vacuous, so the `-zero` / `-succ` and `-le` / `-gt`
rules overlap.**  `table.fill-zero` fires at *any* index, including one
`table.fill-oob` traps at — nothing in it inspects `i`.  `table.copy-gt` is
not guarded by `i_1 > i_2` at all; the only thing separating it from
`table.copy-le` is which arithmetic its right-hand side writes.

**The bounds check short-circuits.**  `table.copy-oob` and `table.init-oob`
test `i_1 + n > |…|` *or* `i_2 + n > |…|` with `BinE .orOp`, and
`Sem/Eval.lean` tries `boolShort` before evaluating the right operand.  So
when the first test traps, `$table(z, x_2)` — respectively `$elem(z, y)` — is
never consulted, and need not denote at all.  `OobAt`/`InBoundsAt` and the
disjunction's shape in the two statements are exactly that asymmetry.

**`$(n - 1 : nat)` in an output is matched, not computed.**  The residual
count of every `-succ`/`-le`/`-gt` rule sits in a conclusion, where
`matchExp`'s `CvtE` clause inverts the coercion with `Num.cvt` — which accepts
an `int` numeral or a denominator-one `rat` as well as a `nat`.  So
`table.fill-succ` still fires when `n = 0`, with `-1` written as an `int`; the
`n ≠ 0` guard the rule appears to carry is not there.  `PredPair` and
`PredSum` state precisely what is left of it.

**`n` need not be a `nat` numeral.**  In `table.fill-succ` and
`table.init-succ`, `n` is read only through `$(n : int)`, so an `int` or a
`rat` count is accepted.  In `table.copy-gt` it is read through
`$(i!%.0 + n)`, which forces it only to have the *same* numeral kind as the
index payload.  Only the `-oob` rules, whose premise compares against a list
length, force a `nat`.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecReadTable

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution
open Silmaril.SpecTec.Equiv.ExecRead

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## Pattern shapes the family shares -/

/-- The configuration pattern `(z; instr*)` with a *literal* instruction list.
`z` is fresh, so it binds; the instruction patterns are then matched in order
from the extended scope. -/
theorem matchExp_readConfig_iff {env : Env} {ρ' : VarEnv} {es : List Exp} {v : Value} :
    MatchExp env VarEnv.empty (.caseE "%;%" (.tupE [.varE "z", .listE es])) v ρ' ↔
      ∃ z is, v = ExecStep.configV z is ∧
        MatchExps env (VarEnv.empty.bindVal "z" z) es is ρ' := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨z, body, σ, rfl, hz, hbody⟩ := matchExps_two_iff.1 hws
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨is, rfl, his⟩ := Validation.matchExp_list_iff.1 hbody
    exact ⟨z, is, rfl, his⟩
  · rintro ⟨z, is, rfl, his⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, (matchExp_freshVar_iff (by simp)).2 rfl,
        Validation.matchExp_list_iff.2 ⟨_, rfl, his⟩⟩⟩⟩

/-- `(CONST nt c)` as a two-component pattern. -/
theorem matchExp_const_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {v : Value} :
    MatchExp env ρ (.caseE "CONST" (.tupE [e₁, e₂])) v ρ' ↔
      ∃ a b σ, v = Execution.constV a b ∧
        MatchExp env ρ e₁ a σ ∧ MatchExp env σ e₂ b ρ' := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨a, b, σ, rfl, ha, hb⟩ := matchExps_two_iff.1 hws
    exact ⟨a, b, σ, rfl, ha, hb⟩
  · rintro ⟨a, b, σ, rfl, ha, hb⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨a, b, σ, rfl, ha, hb⟩⟩⟩

/-- `%(e)`, the one-case injection every `nat`-like index sits in. -/
theorem matchExp_pct_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value} :
    MatchExp env ρ (.caseE "%" (.tupE [e])) v ρ' ↔
      ∃ w, v = .case "%" (.tuple [w]) ∧ MatchExp env ρ e w ρ' := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨a, rfl, ha⟩ := matchExps_one_iff.1 hws
    exact ⟨a, rfl, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_one_iff.2 ⟨a, rfl, ha⟩⟩⟩

/-- A two-index instruction pattern, `(OP x y)`, over two *fresh* variables. -/
theorem matchExp_twoIdx_iff {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {x y : IL.Id}
    {v : Value} (hx : ρ.findVal? x = none) (hy : ∀ a, (ρ.bindVal x a).findVal? y = none) :
    MatchExp env ρ (.caseE op (.tupE [.varE x, .varE y])) v ρ' ↔
      ∃ a b, v = .case op (.tuple [a, b]) ∧ ρ' = (ρ.bindVal x a).bindVal y b := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨a, b, σ, rfl, ha, hb⟩ := matchExps_two_iff.1 hws
    rw [matchExp_freshVar_iff hx] at ha
    subst ha
    rw [matchExp_freshVar_iff (hy a)] at hb
    exact ⟨a, b, rfl, hb⟩
  · rintro ⟨a, b, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨a, b, _, rfl, (matchExp_freshVar_iff hx).2 rfl,
        (matchExp_freshVar_iff (hy a)).2 rfl⟩⟩⟩

/-- A two-index instruction pattern over two *bound* variables: it tests. -/
theorem matchExp_twoIdxBound_iff {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {x y : IL.Id}
    {a b v : Value} (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b) :
    MatchExp env ρ (.caseE op (.tupE [.varE x, .varE y])) v ρ' ↔
      v = .case op (.tuple [a, b]) ∧ ρ' = ρ := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨c, d, σ, rfl, hc, hd⟩ := matchExps_two_iff.1 hws
    rw [matchExp_boundVar_iff hx] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [matchExp_boundVar_iff hy] at hd
    obtain ⟨rfl, rfl⟩ := hd
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, ρ', rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩,
        (matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩⟩⟩⟩

/-! ## The store accessors, kept abstract

`$table(z, x)` and `$elem(z, y)` are ordinary `DecD` calls.  `RefsOf` is the
only thing any of the thirteen rules asks of them. -/

/-- `$f(a, b)` denotes a structure whose `REFS` field is the list `refs`. -/
def RefsOf (env : Env) (f : IL.Id) (a b : Value) (refs : List Value) : Prop :=
  ∃ w, ExecNumeric.Applies env f [.val a, .val b] w ∧ w.field? "REFS" = some (.list refs)

/-- `$f(x, y).REFS`, evaluated. -/
theorem evalExp_dotRefs_iff {env : Env} {ρ : VarEnv} {f x y : IL.Id} {a b v : Value}
    (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b)
    (hd : ρ.findDef? f = none) :
    EvalExp env ρ (.dotE (.callE f [.expA (.varE x), .expA (.varE y)]) "REFS") v ↔
      ∃ w, ExecNumeric.Applies env f [.val a, .val b] w ∧ w.field? "REFS" = some v := by
  have hargs : EvalArgs env ρ [Arg.expA (.varE x), Arg.expA (.varE y)] [.val a, .val b] :=
    evalArgs_cons (evalExp_varE_iff.2 hx) (evalArgs_cons (evalExp_varE_iff.2 hy) evalArgs_nil)
  rw [evalExp_dotE_iff]
  constructor
  · rintro ⟨w, hw, hf⟩
    exact ⟨w, (ExecNumeric.applies_iff_callDef hd hargs).2 (evalExp_callE_iff.1 hw), hf⟩
  · rintro ⟨w, happ, hf⟩
    exact ⟨w, evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef hd hargs).1 happ), hf⟩

/-- `|$f(x, y).REFS|`, evaluated. -/
theorem evalExp_refsLen_iff {env : Env} {ρ : VarEnv} {f x y : IL.Id} {a b v : Value}
    (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b)
    (hd : ρ.findDef? f = none) :
    EvalExp env ρ (.lenE (.dotE (.callE f [.expA (.varE x), .expA (.varE y)]) "REFS")) v ↔
      ∃ refs, RefsOf env f a b refs ∧ v = .num (.natN refs.length) := by
  rw [evalExp_lenE_iff]
  constructor
  · rintro ⟨refs, hrefs, rfl⟩
    exact ⟨refs, (evalExp_dotRefs_iff hx hy hd).1 hrefs, rfl⟩
  · rintro ⟨refs, hrefs, rfl⟩
    exact ⟨refs, (evalExp_dotRefs_iff hx hy hd).2 hrefs, rfl⟩

/-! ## Nat comparisons

Each side condition in the family is a `nat`-typed order comparison.
`Num.cmp` is defined only on two numerals with the *same* constructor
(`Sem/Value.lean`), so a successful comparison against a `nat` length already
forces the index payload to be a `nat` numeral — nothing else in the rule
does. -/

/-- A successful `≥` against a `nat` numeral. -/
theorem cmpValues_ge_natR {v : Value} {q : Nat}
    (h : cmpValues .geOp v (.num (.natN q)) = .ok (.bool true)) :
    ∃ p : Nat, v = .num (.natN p) ∧ q ≤ p := by
  cases v with
  | num m =>
      cases m with
      | natN p =>
          refine ⟨p, rfl, ?_⟩
          simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
            Value.bool.injEq, decide_eq_true_eq] at h
          omega
      | _ => simp [cmpValues, Num.cmp, Res.ofOption] at h
  | _ => simp [cmpValues] at h

/-- A `>` against a `nat` numeral, whichever way it goes: the comparison has
to *denote*, which already forces the left operand to be a `nat` numeral. -/
theorem cmpValues_gt_natR {v : Value} {q : Nat} {b : Bool}
    (h : cmpValues .gtOp v (.num (.natN q)) = .ok (.bool b)) :
    ∃ p : Nat, v = .num (.natN p) ∧ b = decide (q < p) := by
  cases v with
  | num m =>
      cases m with
      | natN p =>
          refine ⟨p, rfl, ?_⟩
          simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
            Value.bool.injEq] at h
          exact h.symm
      | _ => simp [cmpValues, Num.cmp, Res.ofOption] at h
  | _ => simp [cmpValues] at h

/-- `+` never short-circuits. -/
theorem boolShort_addOp {v : Value} : boolShort .addOp v = none := by
  cases v <;> rfl

/-- An addition that denotes a `nat` numeral had two `nat` numerals. -/
theorem binValues_add_eq_natN {v₁ v₂ : Value} {s : Nat}
    (h : binValues .addOp v₁ v₂ = .ok (.num (.natN s))) :
    ∃ p q : Nat, v₁ = .num (.natN p) ∧ v₂ = .num (.natN q) ∧ s = p + q := by
  cases v₁ with
  | num m₁ =>
      cases v₂ with
      | num m₂ =>
          cases m₁ with
          | natN p =>
              cases m₂ with
              | natN q =>
                  refine ⟨p, q, rfl, rfl, ?_⟩
                  simp only [binValues, Num.bin, Res.ofOption, Option.map_some,
                    Except.ok.injEq, Value.num.injEq, Num.natN.injEq] at h
                  omega
              | _ => simp [binValues, Num.bin, Res.ofOption] at h
          | _ => cases m₂ <;> simp [binValues, Num.bin, Res.ofOption] at h
      | _ => simp [binValues] at h
  | _ => cases v₂ <;> simp [binValues, boolBin, Res.ofOption] at h

/-- `∨` short-circuits on `true`, and on nothing else. -/
theorem boolShort_orOp_iff {v w : Value} :
    boolShort .orOp v = some w ↔ v = .bool true ∧ w = .bool true := by
  cases v with
  | bool b => cases b <;> simp [boolShort, eq_comm]
  | _ => simp [boolShort]

/-- A disjunction that denotes `true` without short-circuiting. -/
theorem binValues_or_eq_true {v₁ v₂ : Value}
    (h : binValues .orOp v₁ v₂ = .ok (.bool true)) :
    ∃ b₁ b₂ : Bool, v₁ = .bool b₁ ∧ v₂ = .bool b₂ ∧ (b₁ || b₂) = true := by
  cases v₁ with
  | bool b₁ =>
      cases v₂ with
      | bool b₂ =>
          exact ⟨b₁, b₂, rfl, rfl, by simpa [binValues, boolBin, Res.ofOption] using h⟩
      | _ => simp [binValues] at h
  | num m₁ => cases v₂ <;> simp [binValues, Num.bin, Res.ofOption] at h
  | _ => simp [binValues] at h

/-- An addition whose *right* operand is a `nat` numeral. -/
theorem binValues_add_natR {v₁ v : Value} {q : Nat}
    (h : binValues .addOp v₁ (.num (.natN q)) = .ok v) :
    ∃ p : Nat, v₁ = .num (.natN p) ∧ v = .num (.natN (p + q)) := by
  cases v₁ with
  | num m₁ =>
      cases m₁ with
      | natN p =>
          refine ⟨p, rfl, ?_⟩
          simpa only [binValues, Num.bin, Res.ofOption, Option.map_some,
            Except.ok.injEq, eq_comm] using h
      | _ => simp [binValues, Num.bin, Res.ofOption] at h
  | _ => simp [binValues] at h

/-- A successful `≤` out of a `nat` numeral. -/
theorem cmpValues_le_natL {v : Value} {p : Nat}
    (h : cmpValues .leOp (.num (.natN p)) v = .ok (.bool true)) :
    ∃ q : Nat, v = .num (.natN q) ∧ p ≤ q := by
  cases v with
  | num m =>
      cases m with
      | natN q =>
          refine ⟨q, rfl, ?_⟩
          simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
            Value.bool.injEq, decide_eq_true_eq] at h
          omega
      | _ => simp [cmpValues, Num.cmp, Res.ofOption] at h
  | _ => simp [cmpValues] at h

/-! ## The bounds check, once

`table.fill`, `table.copy` and `table.init` all guard on
`$(i!%.0 + n) > |$f(z, x).REFS|`, with `$f` either `$table` or `$elem`.  Both
answers matter — `table.copy`'s and `table.init`'s premise is a *disjunction*,
whose right branch is reached only when the left test denotes `false`. -/

/-- The bounds check holding: the index payload is a `nat` numeral `k`, the
accessor denotes a `REFS` list, and `k + n` runs past it. -/
def OobAt (env : Env) (f : IL.Id) (z x i : Value) (n : Nat) : Prop :=
  ∃ k us refs, i = .case "%" (.tuple (.num (.natN k) :: us)) ∧
    RefsOf env f z x refs ∧ refs.length < k + n

/-- The bounds check failing.  Note that it is *not* the negation of `OobAt`:
the check still has to denote, so the index payload is still a `nat` numeral
and the accessor still has to denote a `REFS` list. -/
def InBoundsAt (env : Env) (f : IL.Id) (z x i : Value) (n : Nat) : Prop :=
  ∃ k us refs, i = .case "%" (.tuple (.num (.natN k) :: us)) ∧
    RefsOf env f z x refs ∧ k + n ≤ refs.length

/-- The bounds check, evaluated, both ways. -/
theorem evalExp_oobCmp_iff {env : Env} {ρ : VarEnv} {f zi xi ii ni : IL.Id}
    {z x i nv : Value} {b : Bool}
    (hz : ρ.findVal? zi = some z) (hx : ρ.findVal? xi = some x)
    (hi : ρ.findVal? ii = some i) (hn : ρ.findVal? ni = some nv)
    (hd : ρ.findDef? f = none) :
    EvalExp env ρ
      (.cmpE .gtOp (.numT .natT)
        (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE ii) "%") 0) (.varE ni))
        (.lenE (.dotE (.callE f [.expA (.varE zi), .expA (.varE xi)]) "REFS")))
      (.bool b) ↔
      ∃ n : Nat, nv = .num (.natN n) ∧
        ((b = true ∧ OobAt env f z x i n) ∨ (b = false ∧ InBoundsAt env f z x i n)) := by
  constructor
  · intro h
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 h
    rw [evalExp_refsLen_iff hz hx hd] at hu₂
    obtain ⟨refs, hrefs, rfl⟩ := hu₂
    obtain ⟨s, rfl, hb⟩ := cmpValues_gt_natR hcmp
    obtain ⟨w₁, hw₁, hor⟩ := evalExp_binE_iff.1 hu₁
    simp only [boolShort_addOp, reduceCtorEq, false_or, true_and] at hor
    obtain ⟨w₂, hw₂, hbin⟩ := hor
    rw [evalExp_varE_iff, hn, Option.some.injEq] at hw₂
    subst hw₂
    obtain ⟨p, q, rfl, rfl, rfl⟩ := binValues_add_eq_natN hbin
    rw [evalExp_imm_iff hi] at hw₁
    obtain ⟨us, rfl⟩ := hw₁
    refine ⟨q, rfl, ?_⟩
    by_cases hlt : refs.length < p + q
    · exact Or.inl ⟨by simp [hb, hlt], p, us, refs, rfl, hrefs, hlt⟩
    · exact Or.inr ⟨by simp [hb, hlt], p, us, refs, rfl, hrefs, by omega⟩
  · rintro ⟨n, rfl, hcase⟩
    obtain ⟨rfl, k, us, refs, rfl, hrefs, hcmp⟩ | ⟨rfl, k, us, refs, rfl, hrefs, hcmp⟩ := hcase
    · refine evalExp_cmpE_iff.2 ⟨.num (.natN (k + n)), .num (.natN refs.length), ?_,
        (evalExp_refsLen_iff hz hx hd).2 ⟨refs, hrefs, rfl⟩, ?_⟩
      · exact evalExp_binE_iff.2 ⟨.num (.natN k), (evalExp_imm_iff hi).2 ⟨us, rfl⟩,
          Or.inr ⟨boolShort_addOp, .num (.natN n), evalExp_varE_iff.2 hn, rfl⟩⟩
      · simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
          Value.bool.injEq, decide_eq_true_eq]
        omega
    · refine evalExp_cmpE_iff.2 ⟨.num (.natN (k + n)), .num (.natN refs.length), ?_,
        (evalExp_refsLen_iff hz hx hd).2 ⟨refs, hrefs, rfl⟩, ?_⟩
      · exact evalExp_binE_iff.2 ⟨.num (.natN k), (evalExp_imm_iff hi).2 ⟨us, rfl⟩,
          Or.inr ⟨boolShort_addOp, .num (.natN n), evalExp_varE_iff.2 hn, rfl⟩⟩
      · simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
          Value.bool.injEq, decide_eq_false_iff_not, Nat.not_lt]
        omega

/-! ## The scopes the conclusions build

A rule's premises are evaluated in the scope its conclusion built, and every
backward direction below has to name that scope three times.  Each family gets
one abbreviation. -/

/-- `table.get`'s scope: `z`, `at`, `i`, `x`. -/
def getScope (z nt i x : Value) : VarEnv :=
  (((VarEnv.empty.bindVal "z" z).bindVal "at" nt).bindVal "i" i).bindVal "x" x

/-- `table.copy`'s scope, before the two table indices: `z`, `at_1`, `i_1`,
`at_2`, `i_2`, `at'`, `n`. -/
def copyPre (z nt₁ i₁ nt₂ i₂ nt' n : Value) : VarEnv :=
  ((((((VarEnv.empty.bindVal "z" z).bindVal "at_1" nt₁).bindVal "i_1" i₁).bindVal
    "at_2" nt₂).bindVal "i_2" i₂).bindVal "at'" nt').bindVal "n" n

/-- `table.init`'s scope: `z`, `at`, `i`, `j`, `n`, `x`, `y`. -/
def initScope (z nt i j n x y : Value) : VarEnv :=
  ((((((VarEnv.empty.bindVal "z" z).bindVal "at" nt).bindVal "i" i).bindVal
    "j" j).bindVal "n" n).bindVal "x" x).bindVal "y" y

/-- `table.fill`'s scope: `z`, `at`, `i`, `val`, `n`, `x`. -/
def fillScope (z nt i val n x : Value) : VarEnv :=
  (((((VarEnv.empty.bindVal "z" z).bindVal "at" nt).bindVal "i" i).bindVal
    "val" val).bindVal "n" n).bindVal "x" x

/-! ## `table.get`

Two rules, the standard trap/value split.  Both read `$table(z, x).REFS` and
nothing else of the state. -/

/-- **`Step_read/table.get-oob`, characterised exactly.** -/
theorem ruleFires_tableGetOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableGetOobRule ↔
      ∃ z nt k us x refs,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt (.case "%" (.tuple (.num (.natN k) :: us))),
              .case "TABLE.GET" x],
           .list [Execution.trapV]] ∧
        RefsOf env "table" z x refs ∧ refs.length ≤ k := by
  unfold tableGetOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    obtain ⟨c₁, c₂, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 his
    obtain ⟨nt, i, υ, rfl, hnt, hi⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 h2
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_imm_iff (x := "i") (c := i) (by simp)] at hu₁
    obtain ⟨us, rfl⟩ := hu₁
    rw [evalExp_refsLen_iff (a := z) (b := x) (by simp) (by simp) rfl] at hu₂
    obtain ⟨refs, hrefs, rfl⟩ := hu₂
    obtain ⟨p, rfl, hle⟩ := cmpValues_ge_natR hcmp
    exact ⟨z, nt, p, us, x, refs, rfl, hrefs, hle⟩
  · rintro ⟨z, nt, k, us, x, refs, rfl, hrefs, hle⟩
    refine ⟨getScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) x,
      getScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) x,
      matchExp_concl_iff.2 ⟨_, _,
        getScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) x, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
        matchExp_const_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          (matchExp_freshVar_iff (by simp)).2 rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_cmpE_iff.2 ⟨.num (.natN k), .num (.natN refs.length), ?_, ?_, ?_⟩
      · exact (evalExp_imm_iff (by simp [getScope])).2 ⟨us, rfl⟩
      · exact (evalExp_refsLen_iff (by simp [getScope]) (by simp [getScope]) rfl).2
          ⟨refs, hrefs, rfl⟩
      · simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
          Value.bool.injEq, decide_eq_true_eq]
        omega

/-- **`Step_read/table.get-val`, characterised exactly.**  The right-hand side
is `$table(z, x).REFS[i]`, an `IdxE` *pattern*, so it is matched by being
evaluated (`ExecDefault.matchExp_idxE_iff`); the `if` premise's bound check is
then exactly the one `List.getElem?` already carries, so it adds nothing. -/
theorem ruleFires_tableGetVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableGetValRule ↔
      ∃ z nt k us x refs r,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt (.case "%" (.tuple (.num (.natN k) :: us))),
              .case "TABLE.GET" x],
           .list [r]] ∧
        RefsOf env "table" z x refs ∧ refs[k]? = some r := by
  unfold tableGetValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    obtain ⟨c₁, c₂, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 his
    obtain ⟨nt, i, υ, rfl, hnt, hi⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 h2
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [Validation.matchExp_sub_iff] at hrv
    obtain ⟨hidx, rfl⟩ := ExecDefault.matchExp_idxE_iff.1 hrv
    obtain ⟨w, j, hw, hj, hsel⟩ := evalExp_idxE_iff.1 hidx
    rw [evalExp_imm_iff (x := "i") (c := i) (by simp)] at hj
    obtain ⟨us, rfl⟩ := hj
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨refs, hdot, rfl⟩ := evalExp_lenE_iff.1 hu₂
    obtain rfl : w = .list refs := EvalExp.unique hw hdot
    refine ⟨z, nt, j, us, x, refs, r, rfl,
      (evalExp_dotRefs_iff (a := z) (b := x) (by simp) (by simp) rfl).1 hdot, ?_⟩
    simpa [Value.idx?] using hsel
  · rintro ⟨z, nt, k, us, x, refs, r, rfl, hrefs, hsel⟩
    have hlt : k < refs.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hsel
      exact absurd hsel (by simp)
    refine ⟨getScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) x,
      getScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) x,
      matchExp_concl_iff.2 ⟨_, _,
        getScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) x, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
        matchExp_const_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          (matchExp_freshVar_iff (by simp)).2 rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · refine Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, Validation.matchExp_sub_iff.2
          (ExecDefault.matchExp_idxE_iff.2 ⟨evalExp_idxE_iff.2 ⟨.list refs, k, ?_, ?_,
            by simpa [Value.idx?] using hsel⟩, rfl⟩)⟩⟩
      · exact (evalExp_dotRefs_iff (a := z) (b := x) (by simp [getScope])
          (by simp [getScope]) rfl).2 hrefs
      · exact (evalExp_imm_iff (by simp [getScope])).2 ⟨us, rfl⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_cmpE_iff.2 ⟨.num (.natN k), .num (.natN refs.length), ?_, ?_, ?_⟩
      · exact (evalExp_imm_iff (by simp [getScope])).2 ⟨us, rfl⟩
      · exact evalExp_lenE_iff.2 ⟨refs,
          (evalExp_dotRefs_iff (a := z) (b := x) (by simp [getScope])
            (by simp [getScope]) rfl).2 hrefs, rfl⟩
      · simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
          Value.bool.injEq, decide_eq_true_eq]
        omega

/-! ## `table.size` fires at nothing

`table.size` is the one rule of the family whose second `if` premise names
variables the conclusion never binds: `lim` and `rt`, which occur *only* in

```
if $table(z, x).TYPE = at lim rt
```

The source writes that as a destructuring equation, but the elaborated IL
keeps it an `IfPr`, and `Sem/Eval.lean` evaluates an `IfPr` — it does not
solve it.  `lim` and `rt` therefore have no value in the scope the
conclusion built, the premise has no value, and the rule cannot fire.  This is
a *narrowing* of the pinned stream by our premise semantics, and it is the
only one in the thirteen. -/

/-- **`Step_read/table.size` fires at nothing**, because its second premise
reads `lim` and `rt`, which the conclusion does not bind. -/
theorem not_ruleFires_tableSize {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v tableSizeRule := by
  unfold tableSizeRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
  obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 his
  obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hc
  rw [matchExp_freshVar_iff (by simp)] at hx
  subst hx
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
  obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
  obtain ⟨nt, nv, τ, rfl, hnt, hnv⟩ := matchExp_const_iff.1 hrv
  rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hnt
  subst hnt
  obtain ⟨nval, rfl, hn⟩ := matchExp_pct_iff.1 hnv
  rw [matchExp_freshVar_iff (by simp)] at hn
  subst hn
  obtain ⟨κ, hpr1, hrest⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨rfl, -⟩ := Validation.premHolds_if_iff.1 hpr1
  obtain ⟨μ, hpr2, -⟩ := Validation.premsHold_cons_iff.1 hrest
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr2
  obtain ⟨v₁, v₂, -, hv₂, -⟩ := evalExp_cmpE_iff.1 hev
  obtain ⟨w, hw, -⟩ := evalExp_caseE_iff.1 hv₂
  obtain ⟨ws, hws, -⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨p, ps, -, -, hq⟩ := Validation.evalExps_cons_iff.1 hws
  obtain ⟨q, qs, -, hlim, -⟩ := Validation.evalExps_cons_iff.1 hq
  rw [evalExp_varE_iff] at hlim
  simp at hlim

/-! ## `table.fill`

The three rules share a left-hand side,
`(CONST at i) val (CONST at %(n)) (TABLE.FILL x)`, in which the *second*
`CONST`'s address type is the already-bound `at`: the two constants must carry
the same numeric type, which is a constraint the rule imposes and the
characterisation records by using one `nt` twice. -/

/-- The left-hand side of all three `table.fill` rules. -/
theorem matchExps_fillLhs_iff {env : Env} {ρ' : VarEnv} {ta tb tc td : Typ}
    {z : Value} {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") ta tb, .varE "i"]),
       .subE (.varE "val") tc td,
       .caseE "CONST" (.tupE [.subE (.varE "at") ta tb, .caseE "%" (.tupE [.varE "n"])]),
       .caseE "TABLE.FILL" (.varE "x")] vs ρ' ↔
      ∃ nt i val n x,
        vs = [Execution.constV nt i, val, Execution.constV nt (.case "%" (.tuple [n])),
              .case "TABLE.FILL" x] ∧
        ρ' = fillScope z nt i val n x := by
  constructor
  · intro h
    obtain ⟨a, b, c, d, σ, τ, υ, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 h
    obtain ⟨nt, i, κ, rfl, hnt, hi⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h2
    subst h2
    obtain ⟨nt', nval, μ, rfl, hnt', hnv⟩ := matchExp_const_iff.1 h3
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := nt) (by simp)] at hnt'
    obtain ⟨rfl, rfl⟩ := hnt'
    obtain ⟨nn, rfl, hn⟩ := matchExp_pct_iff.1 hnv
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 h4
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    exact ⟨nt', i, b, nn, x, rfl, rfl⟩
  · rintro ⟨nt, i, val, n, x, rfl, rfl⟩
    exact matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
      matchExp_const_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        (matchExp_freshVar_iff (by simp)).2 rfl⟩,
      Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
      matchExp_const_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩),
        matchExp_pct_iff.2 ⟨_, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩

/-- **`Step_read/table.fill-oob`, characterised exactly.** -/
theorem ruleFires_tableFillOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableFillOobRule ↔
      ∃ z nt i val n x,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt i, val, Execution.constV nt (Execution.pctV n),
              .case "TABLE.FILL" x],
           .list [Execution.trapV]] ∧
        OobAt env "table" z x i n := by
  unfold tableFillOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    obtain ⟨nt, i, val, nval, x, rfl, rfl⟩ := matchExps_fillLhs_iff.1 his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_oobCmp_iff (z := z) (x := x) (i := i) (nv := nval)
      (by simp [fillScope]) (by simp [fillScope]) (by simp [fillScope])
      (by simp [fillScope]) rfl] at hev
    obtain ⟨n, rfl, hcase⟩ := hev
    rcases hcase with ⟨-, hoob⟩ | ⟨hfalse, -⟩
    · exact ⟨z, nt, i, val, n, x, rfl, hoob⟩
    · exact absurd hfalse (by simp)
  · rintro ⟨z, nt, i, val, n, x, rfl, hoob⟩
    refine ⟨fillScope z nt i val (.num (.natN n)) x, fillScope z nt i val (.num (.natN n)) x,
      matchExp_concl_iff.2 ⟨_, _, fillScope z nt i val (.num (.natN n)) x, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        matchExps_fillLhs_iff.2 ⟨nt, i, val, .num (.natN n), x, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      exact (evalExp_oobCmp_iff (z := z) (x := x) (i := i) (nv := .num (.natN n))
        (by simp [fillScope]) (by simp [fillScope]) (by simp [fillScope])
        (by simp [fillScope]) rfl).2 ⟨n, rfl, Or.inl ⟨rfl, hoob⟩⟩

/-- **`Step_read/table.fill-zero`, characterised exactly.**  Note that the
index `i` is *never inspected*: its only occurrence is the pattern variable,
and the premise constrains `n` alone.  A zero-length fill therefore succeeds at
any index — including one `table.fill-oob` also traps at, since `i + 0 > |refs|`
is satisfiable.  The two rules genuinely overlap. -/
theorem ruleFires_tableFillZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableFillZeroRule ↔
      ∃ z nt i val x,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt i, val, Execution.constV nt (Execution.pctV 0),
              .case "TABLE.FILL" x],
           .list []] := by
  unfold tableFillZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    obtain ⟨nt, i, val, nval, x, rfl, rfl⟩ := matchExps_fillLhs_iff.1 his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 hbvs
    obtain ⟨-, hev⟩ := ExecRef.premsHold_elseIf_iff.1 hp
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hu₁
    rw [evalExp_numE_iff] at hu₂
    subst hu₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    have hnv : nval = .num (.natN 0) := by simpa [fillScope] using hu₁
    subst hnv
    exact ⟨z, nt, i, val, x, rfl⟩
  · rintro ⟨z, nt, i, val, x, rfl⟩
    refine ⟨fillScope z nt i val (.num (.natN 0)) x, fillScope z nt i val (.num (.natN 0)) x,
      matchExp_concl_iff.2 ⟨_, _, fillScope z nt i val (.num (.natN 0)) x, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        matchExps_fillLhs_iff.2 ⟨nt, i, val, .num (.natN 0), x, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩
    · refine ExecRef.premsHold_elseIf_iff.2 ⟨rfl, evalExp_cmpE_iff.2
        ⟨.num (.natN 0), .num (.natN 0), evalExp_varE_iff.2 (by simp [fillScope]),
          evalExp_numE_iff.2 rfl, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩

/-! ## `table.copy`

Four rules, one left-hand side.  `table.copy-oob` names its two table indices
`x_1`/`x_2` and the other three name them `x`/`y`, so the shared lemma is
parametric in the pair of identifiers. -/

/-- The left-hand side of all four `table.copy` rules. -/
theorem matchExps_copyLhs_iff {env : Env} {ρ' : VarEnv} {x₁ x₂ : IL.Id}
    {ta tb tc td te tf : Typ} {z : Value} {vs : List Value}
    (hx₁ : ∀ nt₁ i₁ nt₂ i₂ nt' n : Value, (copyPre z nt₁ i₁ nt₂ i₂ nt' n).findVal? x₁ = none)
    (hx₂ : ∀ nt₁ i₁ nt₂ i₂ nt' n a : Value,
      ((copyPre z nt₁ i₁ nt₂ i₂ nt' n).bindVal x₁ a).findVal? x₂ = none) :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at_1") ta tb, .varE "i_1"]),
       .caseE "CONST" (.tupE [.subE (.varE "at_2") tc td, .varE "i_2"]),
       .caseE "CONST" (.tupE [.subE (.varE "at'") te tf, .caseE "%" (.tupE [.varE "n"])]),
       .caseE "TABLE.COPY" (.tupE [.varE x₁, .varE x₂])] vs ρ' ↔
      ∃ nt₁ i₁ nt₂ i₂ nt' n a b,
        vs = [Execution.constV nt₁ i₁, Execution.constV nt₂ i₂,
              Execution.constV nt' (.case "%" (.tuple [n])),
              .case "TABLE.COPY" (.tuple [a, b])] ∧
        ρ' = ((copyPre z nt₁ i₁ nt₂ i₂ nt' n).bindVal x₁ a).bindVal x₂ b := by
  constructor
  · intro h
    obtain ⟨c₁, c₂, c₃, c₄, σ, τ, υ, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 h
    obtain ⟨nt₁, i₁, κ₁, rfl, hnt₁, hi₁⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hnt₁
    subst hnt₁
    rw [matchExp_freshVar_iff (by simp)] at hi₁
    subst hi₁
    obtain ⟨nt₂, i₂, κ₂, rfl, hnt₂, hi₂⟩ := matchExp_const_iff.1 h2
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hnt₂
    subst hnt₂
    rw [matchExp_freshVar_iff (by simp)] at hi₂
    subst hi₂
    obtain ⟨nt', nv, κ₃, rfl, hnt', hnv⟩ := matchExp_const_iff.1 h3
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hnt'
    subst hnt'
    obtain ⟨nn, rfl, hn⟩ := matchExp_pct_iff.1 hnv
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    obtain ⟨a, b, rfl, rfl⟩ :=
      (matchExp_twoIdx_iff (ρ := copyPre z nt₁ i₁ nt₂ i₂ nt' nn)
        (hx₁ _ _ _ _ _ _) (fun a => hx₂ _ _ _ _ _ _ a)).1 h4
    exact ⟨nt₁, i₁, nt₂, i₂, nt', nn, a, b, rfl, rfl⟩
  · rintro ⟨nt₁, i₁, nt₂, i₂, nt', n, a, b, rfl, rfl⟩
    exact matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
      matchExp_const_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        (matchExp_freshVar_iff (by simp)).2 rfl⟩,
      matchExp_const_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        (matchExp_freshVar_iff (by simp)).2 rfl⟩,
      matchExp_const_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        matchExp_pct_iff.2 ⟨_, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩,
      (matchExp_twoIdx_iff (hx₁ nt₁ i₁ nt₂ i₂ nt' n)
        (fun c => hx₂ nt₁ i₁ nt₂ i₂ nt' n c)).2 ⟨a, b, rfl, rfl⟩⟩

/-- **`Step_read/table.copy-oob`, characterised exactly.**  The premise is a
*short-circuiting* disjunction: `Sem/Eval.lean`'s `BinE` clause tries
`boolShort` first, so when the source table's check already says "out of
bounds" the destination table's check — and therefore `$table(z, x_2)` — is
never evaluated at all.  That is why the right branch, and only the right
branch, carries `InBoundsAt` for the source. -/
theorem ruleFires_tableCopyOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableCopyOobRule ↔
      ∃ z nt₁ i₁ nt₂ i₂ nt' n x y,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt₁ i₁, Execution.constV nt₂ i₂,
              Execution.constV nt' (Execution.pctV n),
              .case "TABLE.COPY" (.tuple [x, y])],
           .list [Execution.trapV]] ∧
        (OobAt env "table" z x i₁ n ∨
          (InBoundsAt env "table" z x i₁ n ∧ OobAt env "table" z y i₂ n)) := by
  unfold tableCopyOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    rw [matchExps_copyLhs_iff (x₁ := "x_1") (x₂ := "x_2")
      (by intros; simp [copyPre]) (by intros; simp [copyPre])] at his
    obtain ⟨nt₁, i₁, nt₂, i₂, nt', nv, x, y, rfl, rfl⟩ := his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨w₁, hw₁, hor⟩ := evalExp_binE_iff.1 hev
    rcases hor with hs | ⟨hs, w₂, hw₂, hbin⟩
    · obtain ⟨rfl, -⟩ := boolShort_orOp_iff.1 hs
      rw [evalExp_oobCmp_iff (z := z) (x := x) (i := i₁) (nv := nv)
        (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
        (by simp [copyPre]) rfl] at hw₁
      obtain ⟨n, rfl, hcase⟩ := hw₁
      rcases hcase with ⟨-, hoob⟩ | ⟨hf, -⟩
      · exact ⟨z, nt₁, i₁, nt₂, i₂, nt', n, x, y, rfl, Or.inl hoob⟩
      · exact absurd hf (by simp)
    · obtain ⟨b₁, b₂, rfl, rfl, hbb⟩ := binValues_or_eq_true hbin
      have hb₁ : b₁ = false := by cases b₁ <;> simp [boolShort] at hs ⊢
      subst hb₁
      have hb₂ : b₂ = true := by simpa using hbb
      subst hb₂
      rw [evalExp_oobCmp_iff (z := z) (x := x) (i := i₁) (nv := nv)
        (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
        (by simp [copyPre]) rfl] at hw₁
      obtain ⟨n, rfl, hcase₁⟩ := hw₁
      rw [evalExp_oobCmp_iff (z := z) (x := y) (i := i₂) (nv := .num (.natN n))
        (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
        (by simp [copyPre]) rfl] at hw₂
      obtain ⟨n', hn', hcase₂⟩ := hw₂
      simp only [Value.num.injEq, Num.natN.injEq] at hn'
      subst hn'
      rcases hcase₁ with ⟨hf, -⟩ | ⟨-, hin⟩
      · exact absurd hf (by simp)
      rcases hcase₂ with ⟨-, hoob⟩ | ⟨hf, -⟩
      · exact ⟨z, nt₁, i₁, nt₂, i₂, nt', n, x, y, rfl, Or.inr ⟨hin, hoob⟩⟩
      · exact absurd hf (by simp)
  · rintro ⟨z, nt₁, i₁, nt₂, i₂, nt', n, x, y, rfl, hcase⟩
    refine ⟨((copyPre z nt₁ i₁ nt₂ i₂ nt' (.num (.natN n))).bindVal "x_1" x).bindVal "x_2" y,
      ((copyPre z nt₁ i₁ nt₂ i₂ nt' (.num (.natN n))).bindVal "x_1" x).bindVal "x_2" y,
      matchExp_concl_iff.2 ⟨_, _,
        ((copyPre z nt₁ i₁ nt₂ i₂ nt' (.num (.natN n))).bindVal "x_1" x).bindVal "x_2" y,
        rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        (matchExps_copyLhs_iff (x₁ := "x_1") (x₂ := "x_2")
          (by intros; simp [copyPre]) (by intros; simp [copyPre])).2
        ⟨nt₁, i₁, nt₂, i₂, nt', .num (.natN n), x, y, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      rcases hcase with hoob | ⟨hin, hoob⟩
      · exact evalExp_binE_iff.2 ⟨.bool true,
          (evalExp_oobCmp_iff (z := z) (x := x) (i := i₁) (nv := .num (.natN n))
            (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
            (by simp [copyPre]) rfl).2 ⟨n, rfl, Or.inl ⟨rfl, hoob⟩⟩, Or.inl rfl⟩
      · exact evalExp_binE_iff.2 ⟨.bool false,
          (evalExp_oobCmp_iff (z := z) (x := x) (i := i₁) (nv := .num (.natN n))
            (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
            (by simp [copyPre]) rfl).2 ⟨n, rfl, Or.inr ⟨rfl, hin⟩⟩,
          Or.inr ⟨rfl, .bool true,
            (evalExp_oobCmp_iff (z := z) (x := y) (i := i₂) (nv := .num (.natN n))
              (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
              (by simp [copyPre]) rfl).2 ⟨n, rfl, Or.inl ⟨rfl, hoob⟩⟩, rfl⟩⟩

/-- **`Step_read/table.copy-zero`, characterised exactly.**  Like
`table.fill-zero`, neither index is inspected. -/
theorem ruleFires_tableCopyZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableCopyZeroRule ↔
      ∃ z nt₁ i₁ nt₂ i₂ nt' x y,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt₁ i₁, Execution.constV nt₂ i₂,
              Execution.constV nt' (Execution.pctV 0),
              .case "TABLE.COPY" (.tuple [x, y])],
           .list []] := by
  unfold tableCopyZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    rw [matchExps_copyLhs_iff (x₁ := "x") (x₂ := "y")
      (by intros; simp [copyPre]) (by intros; simp [copyPre])] at his
    obtain ⟨nt₁, i₁, nt₂, i₂, nt', nv, x, y, rfl, rfl⟩ := his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 hbvs
    obtain ⟨-, hev⟩ := ExecRef.premsHold_elseIf_iff.1 hp
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hu₁
    rw [evalExp_numE_iff] at hu₂
    subst hu₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    have hnv : nv = .num (.natN 0) := by simpa [copyPre] using hu₁
    subst hnv
    exact ⟨z, nt₁, i₁, nt₂, i₂, nt', x, y, rfl⟩
  · rintro ⟨z, nt₁, i₁, nt₂, i₂, nt', x, y, rfl⟩
    refine ⟨((copyPre z nt₁ i₁ nt₂ i₂ nt' (.num (.natN 0))).bindVal "x" x).bindVal "y" y,
      ((copyPre z nt₁ i₁ nt₂ i₂ nt' (.num (.natN 0))).bindVal "x" x).bindVal "y" y,
      matchExp_concl_iff.2 ⟨_, _,
        ((copyPre z nt₁ i₁ nt₂ i₂ nt' (.num (.natN 0))).bindVal "x" x).bindVal "y" y,
        rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        (matchExps_copyLhs_iff (x₁ := "x") (x₂ := "y")
          (by intros; simp [copyPre]) (by intros; simp [copyPre])).2
        ⟨nt₁, i₁, nt₂, i₂, nt', .num (.natN 0), x, y, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩
    · exact ExecRef.premsHold_elseIf_iff.2 ⟨rfl, evalExp_cmpE_iff.2
        ⟨.num (.natN 0), .num (.natN 0), evalExp_varE_iff.2 (by simp [copyPre]),
          evalExp_numE_iff.2 rfl, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩

/-! ## `table.init`

Same shape as `table.copy`, except that the element-segment index `j` and the
count are fixed to `I32` by the rule rather than carried in an `addrtype`
variable, and the second bounds check reads `$elem(z, y)` instead of
`$table`. -/

/-- The left-hand side of all three `table.init` rules. -/
theorem matchExps_initLhs_iff {env : Env} {ρ' : VarEnv} {ta tb : Typ}
    {z : Value} {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") ta tb, .varE "i"]),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"]),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
       .caseE "TABLE.INIT" (.tupE [.varE "x", .varE "y"])] vs ρ' ↔
      ∃ nt i j n x y,
        vs = [Execution.constV nt i, Execution.constV Execution.i32V j,
              Execution.constV Execution.i32V (.case "%" (.tuple [n])),
              .case "TABLE.INIT" (.tuple [x, y])] ∧
        ρ' = initScope z nt i j n x y := by
  constructor
  · intro h
    obtain ⟨c₁, c₂, c₃, c₄, σ, τ, υ, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 h
    obtain ⟨nt, i, κ₁, rfl, hnt, hi⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨t₂, j, κ₂, rfl, ht₂, hj⟩ := matchExp_const_iff.1 h2
    rw [matchExp_caseNil_iff] at ht₂
    obtain ⟨rfl, rfl⟩ := ht₂
    rw [matchExp_freshVar_iff (by simp)] at hj
    subst hj
    obtain ⟨t₃, nv, κ₃, rfl, ht₃, hnv⟩ := matchExp_const_iff.1 h3
    rw [matchExp_caseNil_iff] at ht₃
    obtain ⟨rfl, rfl⟩ := ht₃
    obtain ⟨nn, rfl, hn⟩ := matchExp_pct_iff.1 hnv
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_twoIdx_iff (by simp) (fun a => by simp)] at h4
    obtain ⟨x, y, rfl, rfl⟩ := h4
    exact ⟨nt, i, j, nn, x, y, rfl, rfl⟩
  · rintro ⟨nt, i, j, n, x, y, rfl, rfl⟩
    exact matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
      matchExp_const_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        (matchExp_freshVar_iff (by simp)).2 rfl⟩,
      matchExp_const_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_freshVar_iff (by simp)).2 rfl⟩,
      matchExp_const_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        matchExp_pct_iff.2 ⟨_, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩,
      (matchExp_twoIdx_iff (by simp) (fun a => by simp)).2 ⟨x, y, rfl, rfl⟩⟩

/-- **`Step_read/table.init-oob`, characterised exactly.**  The same
short-circuit as `table.copy-oob`: when the table check traps, `$elem(z, y)`
is never consulted. -/
theorem ruleFires_tableInitOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableInitOobRule ↔
      ∃ z nt i j n x y,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt i, Execution.constV Execution.i32V j,
              Execution.constV Execution.i32V (Execution.pctV n),
              .case "TABLE.INIT" (.tuple [x, y])],
           .list [Execution.trapV]] ∧
        (OobAt env "table" z x i n ∨
          (InBoundsAt env "table" z x i n ∧ OobAt env "elem" z y j n)) := by
  unfold tableInitOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    obtain ⟨nt, i, j, nv, x, y, rfl, rfl⟩ := matchExps_initLhs_iff.1 his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨w₁, hw₁, hor⟩ := evalExp_binE_iff.1 hev
    rcases hor with hs | ⟨hs, w₂, hw₂, hbin⟩
    · obtain ⟨rfl, -⟩ := boolShort_orOp_iff.1 hs
      rw [evalExp_oobCmp_iff (z := z) (x := x) (i := i) (nv := nv)
        (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
        (by simp [initScope]) rfl] at hw₁
      obtain ⟨n, rfl, hcase⟩ := hw₁
      rcases hcase with ⟨-, hoob⟩ | ⟨hf, -⟩
      · exact ⟨z, nt, i, j, n, x, y, rfl, Or.inl hoob⟩
      · exact absurd hf (by simp)
    · obtain ⟨b₁, b₂, rfl, rfl, hbb⟩ := binValues_or_eq_true hbin
      have hb₁ : b₁ = false := by cases b₁ <;> simp [boolShort] at hs ⊢
      subst hb₁
      have hb₂ : b₂ = true := by simpa using hbb
      subst hb₂
      rw [evalExp_oobCmp_iff (z := z) (x := x) (i := i) (nv := nv)
        (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
        (by simp [initScope]) rfl] at hw₁
      obtain ⟨n, rfl, hcase₁⟩ := hw₁
      rw [evalExp_oobCmp_iff (f := "elem") (z := z) (x := y) (i := j) (nv := .num (.natN n))
        (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
        (by simp [initScope]) rfl] at hw₂
      obtain ⟨n', hn', hcase₂⟩ := hw₂
      simp only [Value.num.injEq, Num.natN.injEq] at hn'
      subst hn'
      rcases hcase₁ with ⟨hf, -⟩ | ⟨-, hin⟩
      · exact absurd hf (by simp)
      rcases hcase₂ with ⟨-, hoob⟩ | ⟨hf, -⟩
      · exact ⟨z, nt, i, j, n, x, y, rfl, Or.inr ⟨hin, hoob⟩⟩
      · exact absurd hf (by simp)
  · rintro ⟨z, nt, i, j, n, x, y, rfl, hcase⟩
    refine ⟨initScope z nt i j (.num (.natN n)) x y, initScope z nt i j (.num (.natN n)) x y,
      matchExp_concl_iff.2 ⟨_, _, initScope z nt i j (.num (.natN n)) x y, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        matchExps_initLhs_iff.2 ⟨nt, i, j, .num (.natN n), x, y, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      rcases hcase with hoob | ⟨hin, hoob⟩
      · exact evalExp_binE_iff.2 ⟨.bool true,
          (evalExp_oobCmp_iff (z := z) (x := x) (i := i) (nv := .num (.natN n))
            (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
            (by simp [initScope]) rfl).2 ⟨n, rfl, Or.inl ⟨rfl, hoob⟩⟩, Or.inl rfl⟩
      · exact evalExp_binE_iff.2 ⟨.bool false,
          (evalExp_oobCmp_iff (z := z) (x := x) (i := i) (nv := .num (.natN n))
            (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
            (by simp [initScope]) rfl).2 ⟨n, rfl, Or.inr ⟨rfl, hin⟩⟩,
          Or.inr ⟨rfl, .bool true,
            (evalExp_oobCmp_iff (f := "elem") (z := z) (x := y) (i := j)
              (nv := .num (.natN n))
              (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
              (by simp [initScope]) rfl).2 ⟨n, rfl, Or.inl ⟨rfl, hoob⟩⟩, rfl⟩⟩

/-- **`Step_read/table.init-zero`, characterised exactly.** -/
theorem ruleFires_tableInitZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableInitZeroRule ↔
      ∃ z nt i j x y,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt i, Execution.constV Execution.i32V j,
              Execution.constV Execution.i32V (Execution.pctV 0),
              .case "TABLE.INIT" (.tuple [x, y])],
           .list []] := by
  unfold tableInitZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    obtain ⟨nt, i, j, nv, x, y, rfl, rfl⟩ := matchExps_initLhs_iff.1 his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 hbvs
    obtain ⟨-, hev⟩ := ExecRef.premsHold_elseIf_iff.1 hp
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hu₁
    rw [evalExp_numE_iff] at hu₂
    subst hu₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    have hnv : nv = .num (.natN 0) := by simpa [initScope] using hu₁
    subst hnv
    exact ⟨z, nt, i, j, x, y, rfl⟩
  · rintro ⟨z, nt, i, j, x, y, rfl⟩
    refine ⟨initScope z nt i j (.num (.natN 0)) x y, initScope z nt i j (.num (.natN 0)) x y,
      matchExp_concl_iff.2 ⟨_, _, initScope z nt i j (.num (.natN 0)) x y, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        matchExps_initLhs_iff.2 ⟨nt, i, j, .num (.natN 0), x, y, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩
    · exact ExecRef.premsHold_elseIf_iff.2 ⟨rfl, evalExp_cmpE_iff.2
        ⟨.num (.natN 0), .num (.natN 0), evalExp_varE_iff.2 (by simp [initScope]),
          evalExp_numE_iff.2 rfl, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩

/-! ## Computed right-hand sides

The `-succ`, `-le` and `-gt` rules put arithmetic in their *conclusion*.
`matchExp` has no pattern case for `BinE`, so it falls through to
`matchDefault` and **evaluates**; it does have one for `CvtE`, which undoes the
coercion with `Num.cvt` on the matched numeral.  The two behave very
differently, and both are visible in the characterisations below. -/

/-- `matchExp` at a `BinE` is the default match. -/
theorem matchExp_binE_iff {env : Env} {ρ ρ' : VarEnv} {op : BinOp} {t : OpTyp}
    {e₁ e₂ : Exp} {v : Value} :
    MatchExp env ρ (.binE op t e₁ e₂) v ρ' ↔
      EvalExp env ρ (.binE op t e₁ e₂) v ∧ ρ' = ρ := by
  rw [show MatchExp env ρ (.binE op t e₁ e₂) v ρ'
        ↔ ∃ n, matchDefault n env ρ (.binE op t e₁ e₂) v = .ok ρ' from ?_,
    ExecDefault.matchDefault_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ m => exact ⟨m, by simpa only [matchExp] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [matchExp] using hn⟩

/-- `matchExp` at a `CvtE` *is* a pattern case: the matched value has to be a
numeral, and the **source** type converts it back before the operand is
matched.  So a `nat`-coerced output can be matched by an `int` or a
denominator-one `rat` numeral as well as by a `nat` one. -/
theorem matchExp_cvtE_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {t₁ t₂ : NumTyp}
    {v : Value} :
    MatchExp env ρ (.cvtE e t₁ t₂) v ρ' ↔
      ∃ m m', v = .num m ∧ Num.cvt t₁ m = some m' ∧ MatchExp env ρ e (.num m') ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ k =>
        cases v with
        | num m =>
            simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
            obtain ⟨m', hm', hrest⟩ := hn
            exact ⟨m, m', rfl, hm', ⟨k, hrest⟩⟩
        | _ =>
            exfalso
            obtain ⟨hev, -⟩ := ExecDefault.matchDefault_iff.1
              ⟨k, by simpa only [matchExp] using hn⟩
            obtain ⟨m, m', -, -, hv⟩ := evalExp_cvtE_iff.1 hev
            exact absurd hv (by simp)
  · rintro ⟨m, m', rfl, hm', hm⟩
    exact matchExp_cvtE_num hm' hm

/-- `-` never short-circuits. -/
theorem boolShort_subOp {v : Value} : boolShort .subOp v = none := by
  cases v <;> rfl

/-- A coercion to `int` lands on an `int` numeral. -/
theorem cvt_intT_eq {m m' : Num} (h : Num.cvt .intT m = some m') :
    ∃ a : Int, m' = .intN a := by
  cases m with
  | natN n => refine ⟨n, ?_⟩; simp only [Num.cvt, Option.some.injEq] at h; exact h.symm
  | intN j => refine ⟨j, ?_⟩; simp only [Num.cvt, Option.some.injEq] at h; exact h.symm
  | ratN q =>
      by_cases hq : q.den = 1
      · refine ⟨q.num, ?_⟩
        simp only [Num.cvt, hq, reduceIte, Option.some.injEq] at h
        exact h.symm
      · simp [Num.cvt, hq] at h
  | realN s => simp [Num.cvt] at h

/-- Integer subtraction, on two `int` numerals. -/
theorem binValues_sub_intN {a b : Int} {v : Value}
    (h : binValues .subOp (.num (.intN a)) (.num (.intN b)) = .ok v) :
    v = .num (.intN (a - b)) := by
  simpa only [binValues, Num.bin, Res.ofOption, Option.map_some, Except.ok.injEq,
    eq_comm] using h

/-- `n` and the numeral the `$(n - 1 : nat)` pattern accepts for it: both are
read only through a coercion to `int`. -/
def PredPair (mn m : Num) : Prop :=
  ∃ a : Int, Num.cvt .intT mn = some (.intN a) ∧ Num.cvt .intT m = some (.intN (a - 1))

/-- `%($(i!%.0 + 1))` as a *pattern*: the addition is evaluated, which forces
`i`'s payload to be a `nat` numeral and pins the result exactly. -/
theorem matchExp_succPct_iff {env : Env} {ρ ρ' : VarEnv} {ii : IL.Id} {i w : Value}
    (hi : ρ.findVal? ii = some i) :
    MatchExp env ρ (.caseE "%" (.tupE [.binE .addOp (.numT .natT)
        (.projE (.uncaseE (.varE ii) "%") 0) (.numE (.natN 1))])) w ρ' ↔
      ∃ k us, i = .case "%" (.tuple (.num (.natN k) :: us)) ∧
        w = Execution.pctV (k + 1) ∧ ρ' = ρ := by
  rw [matchExp_pct_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    rw [matchExp_binE_iff] at hu
    obtain ⟨hev, rfl⟩ := hu
    obtain ⟨v₁, hv₁, hor⟩ := evalExp_binE_iff.1 hev
    simp only [boolShort_addOp, reduceCtorEq, false_or, true_and] at hor
    obtain ⟨v₂, hv₂, hbin⟩ := hor
    rw [evalExp_numE_iff] at hv₂
    subst hv₂
    obtain ⟨k, rfl, rfl⟩ := binValues_add_natR hbin
    rw [evalExp_imm_iff hi] at hv₁
    obtain ⟨us, rfl⟩ := hv₁
    exact ⟨k, us, rfl, rfl, rfl⟩
  · rintro ⟨k, us, rfl, rfl, rfl⟩
    exact ⟨_, rfl, matchExp_binE_iff.2 ⟨evalExp_binE_iff.2 ⟨.num (.natN k),
      (evalExp_imm_iff hi).2 ⟨us, rfl⟩,
      Or.inr ⟨boolShort_addOp, .num (.natN 1), evalExp_numE_iff.2 rfl, rfl⟩⟩, rfl⟩⟩

/-- `%($(n - 1 : nat))` as a *pattern*.  Unlike `+ 1`, the outer coercion is a
`CvtE`, which `matchExp` inverts with `Num.cvt`: the matched numeral only has
to *convert* to `n - 1`, so it may be a negative `int` even when `n` is zero.
Nothing here forces `n` itself to be a `nat` numeral either — it is read only
through `$(n : int)`. -/
theorem matchExp_predPct_iff {env : Env} {ρ ρ' : VarEnv} {ni : IL.Id} {nv w : Value}
    (hn : ρ.findVal? ni = some nv) :
    MatchExp env ρ (.caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
        (.cvtE (.varE ni) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
        .intT .natT])) w ρ' ↔
      ∃ mn m, nv = .num mn ∧ w = .case "%" (.tuple [.num m]) ∧ PredPair mn m ∧
        ρ' = ρ := by
  rw [matchExp_pct_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨m, m', rfl, hcvt, hbody⟩ := matchExp_cvtE_iff.1 hu
    rw [matchExp_binE_iff] at hbody
    obtain ⟨hev, rfl⟩ := hbody
    obtain ⟨v₁, hv₁, hor⟩ := evalExp_binE_iff.1 hev
    simp only [boolShort_subOp, reduceCtorEq, false_or, true_and] at hor
    obtain ⟨v₂, hv₂, hbin⟩ := hor
    obtain ⟨mn, mn', hnv, hncvt, rfl⟩ := evalExp_cvtE_iff.1 hv₁
    rw [evalExp_varE_iff, hn, Option.some.injEq] at hnv
    obtain ⟨o, o', ho, hocvt, rfl⟩ := evalExp_cvtE_iff.1 hv₂
    rw [evalExp_numE_iff, Value.num.injEq] at ho
    subst ho
    simp only [Num.cvt, Option.some.injEq] at hocvt
    subst hocvt
    obtain ⟨a, rfl⟩ := cvt_intT_eq hncvt
    have hm' : m' = .intN (a - 1) := by
      have h2 := binValues_sub_intN hbin
      simp only [Value.num.injEq] at h2
      simpa using h2
    subst hm'
    exact ⟨mn, m, hnv, rfl, ⟨a, hncvt, hcvt⟩, rfl⟩
  · rintro ⟨mn, m, rfl, rfl, ⟨a, hncvt, hmcvt⟩, rfl⟩
    refine ⟨_, rfl, matchExp_cvtE_iff.2 ⟨m, .intN (a - 1), rfl, hmcvt, ?_⟩⟩
    refine matchExp_binE_iff.2 ⟨evalExp_binE_iff.2 ⟨.num (.intN a),
      evalExp_cvtE_iff.2 ⟨mn, .intN a, evalExp_varE_iff.2 hn, hncvt, rfl⟩,
      Or.inr ⟨boolShort_subOp, .num (.intN 1),
        evalExp_cvtE_iff.2 ⟨.natN 1, .intN 1, evalExp_numE_iff.2 rfl, rfl, rfl⟩, rfl⟩⟩, rfl⟩

/-- The right-hand side of `table.fill-succ`.  Nothing in it binds, so the
scope comes out unchanged. -/
theorem matchExps_fillSuccRhs_iff {env : Env} {ρ ρ' : VarEnv} {ta tb tc td : Typ}
    {nt i val nv x : Value} {vs : List Value}
    (hnt : ρ.findVal? "at" = some nt) (hi : ρ.findVal? "i" = some i)
    (hval : ρ.findVal? "val" = some val) (hn : ρ.findVal? "n" = some nv)
    (hx : ρ.findVal? "x" = some x) :
    MatchExps env ρ
      [.caseE "CONST" (.tupE [.subE (.varE "at") ta tb, .varE "i"]),
       .subE (.varE "val") tc td,
       .caseE "TABLE.SET" (.varE "x"),
       .caseE "CONST" (.tupE [.subE (.varE "at") ta tb,
         .caseE "%" (.tupE [.binE .addOp (.numT .natT)
           (.projE (.uncaseE (.varE "i") "%") 0) (.numE (.natN 1))])]),
       .subE (.varE "val") tc td,
       .caseE "CONST" (.tupE [.subE (.varE "at") ta tb,
         .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
           (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
           .intT .natT])]),
       .caseE "TABLE.FILL" (.varE "x")] vs ρ' ↔
      ∃ k us mn m,
        i = .case "%" (.tuple (.num (.natN k) :: us)) ∧ nv = .num mn ∧ PredPair mn m ∧
        vs = [Execution.constV nt i, val, .case "TABLE.SET" x,
              Execution.constV nt (Execution.pctV (k + 1)), val,
              Execution.constV nt (.case "%" (.tuple [.num m])),
              .case "TABLE.FILL" x] ∧
        ρ' = ρ := by
  constructor
  · intro h
    obtain ⟨w1, ws1, σ1, rfl, h1, t1⟩ := Validation.matchExps_cons_iff.1 h
    obtain ⟨a1, b1, τ1, rfl, hA1, hB1⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hnt] at hA1
    obtain ⟨rfl, rfl⟩ := hA1
    rw [matchExp_boundVar_iff hi] at hB1
    obtain ⟨rfl, rfl⟩ := hB1
    obtain ⟨w2, ws2, σ2, rfl, h2, t2⟩ := Validation.matchExps_cons_iff.1 t1
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hval] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨w3, ws3, σ3, rfl, h3, t3⟩ := Validation.matchExps_cons_iff.1 t2
    obtain ⟨c3, rfl, hc3⟩ := Validation.matchExp_case_iff.1 h3
    rw [matchExp_boundVar_iff hx] at hc3
    obtain ⟨rfl, rfl⟩ := hc3
    obtain ⟨w4, ws4, σ4, rfl, h4, t4⟩ := Validation.matchExps_cons_iff.1 t3
    obtain ⟨a4, b4, τ4, rfl, hA4, hB4⟩ := matchExp_const_iff.1 h4
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hnt] at hA4
    obtain ⟨rfl, rfl⟩ := hA4
    rw [matchExp_succPct_iff hi] at hB4
    obtain ⟨k, us, hik, rfl, rfl⟩ := hB4
    obtain ⟨w5, ws5, σ5, rfl, h5, t5⟩ := Validation.matchExps_cons_iff.1 t4
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hval] at h5
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨w6, ws6, σ6, rfl, h6, t6⟩ := Validation.matchExps_cons_iff.1 t5
    obtain ⟨a6, b6, τ6, rfl, hA6, hB6⟩ := matchExp_const_iff.1 h6
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hnt] at hA6
    obtain ⟨rfl, rfl⟩ := hA6
    rw [matchExp_predPct_iff hn] at hB6
    obtain ⟨mn, m, hnv, rfl, hpred, rfl⟩ := hB6
    obtain ⟨w7, ws7, σ7, rfl, h7, t7⟩ := Validation.matchExps_cons_iff.1 t6
    obtain ⟨c7, rfl, hc7⟩ := Validation.matchExp_case_iff.1 h7
    rw [matchExp_boundVar_iff hx] at hc7
    obtain ⟨rfl, rfl⟩ := hc7
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 t7
    exact ⟨k, us, mn, m, hik, hnv, hpred, rfl, rfl⟩
  · rintro ⟨k, us, mn, m, hik, hnv, hpred, rfl, rfl⟩
    refine Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
        Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hnt).2 ⟨rfl, rfl⟩),
        (matchExp_boundVar_iff hi).2 ⟨rfl, rfl⟩⟩
    · exact Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hval).2 ⟨rfl, rfl⟩)
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hnt).2 ⟨rfl, rfl⟩),
        (matchExp_succPct_iff hi).2 ⟨k, us, hik, rfl, rfl⟩⟩
    · exact Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hval).2 ⟨rfl, rfl⟩)
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hnt).2 ⟨rfl, rfl⟩),
        (matchExp_predPct_iff hn).2 ⟨mn, m, hnv, rfl, hpred, rfl⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩⟩

/-- **`Step_read/table.fill-succ`, characterised exactly.**

Two things are worth reading off.  First, the only premise is `else`, which
`Sem/Eval.lean` discharges unconditionally — so the `n ≠ 0` guard the rule
appears to have comes *entirely* from its right-hand side.  Second, that guard
is weaker than it looks: `$(n - 1 : nat)` sits in a matched position, and
`matchExp`'s `CvtE` clause only asks that the residual numeral *convert* to
`n - 1` as an `int`.  So `table.fill-succ` still fires at `n = 0`, with `-1`
written as an `int` numeral — and it fires at an `n` that is not a `nat`
numeral at all.  `PredPair` is exactly that condition. -/
theorem ruleFires_tableFillSucc_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableFillSuccRule ↔
      ∃ z nt k us val mn m x,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt (.case "%" (.tuple (.num (.natN k) :: us))), val,
              Execution.constV nt (.case "%" (.tuple [.num mn])), .case "TABLE.FILL" x],
           .list
             [Execution.constV nt (.case "%" (.tuple (.num (.natN k) :: us))), val,
              .case "TABLE.SET" x,
              Execution.constV nt (Execution.pctV (k + 1)), val,
              Execution.constV nt (.case "%" (.tuple [.num m])),
              .case "TABLE.FILL" x]] ∧
        PredPair mn m := by
  unfold tableFillSuccRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    obtain ⟨nt, i, val, nv, x, rfl, rfl⟩ := matchExps_fillLhs_iff.1 his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    rw [matchExps_fillSuccRhs_iff (nt := nt) (i := i) (val := val) (nv := nv) (x := x)
      (by simp [fillScope]) (by simp [fillScope]) (by simp [fillScope])
      (by simp [fillScope]) (by simp [fillScope])] at hbvs
    obtain ⟨k, us, mn, m, rfl, rfl, hpred, rfl, rfl⟩ := hbvs
    exact ⟨z, nt, k, us, val, mn, m, x, rfl, hpred⟩
  · rintro ⟨z, nt, k, us, val, mn, m, x, rfl, hpred⟩
    refine ⟨fillScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) val (.num mn) x,
      fillScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) val (.num mn) x,
      matchExp_concl_iff.2 ⟨_, _,
        fillScope z nt (.case "%" (.tuple (.num (.natN k) :: us))) val (.num mn) x,
        rfl, ?_, ?_⟩, ExecRef.premsHold_else_iff.2 rfl⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        matchExps_fillLhs_iff.2 ⟨nt, _, val, .num mn, x, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        (matchExps_fillSuccRhs_iff (by simp [fillScope]) (by simp [fillScope])
          (by simp [fillScope]) (by simp [fillScope]) (by simp [fillScope])).2
        ⟨k, us, mn, m, rfl, rfl, hpred, rfl, rfl⟩⟩

/-- The right-hand side of `table.copy-le`. -/
theorem matchExps_copyLeRhs_iff {env : Env} {ρ ρ' : VarEnv} {ta tb tc td te tf : Typ}
    {nt₁ i₁ nt₂ i₂ nt' nv x y : Value} {vs : List Value}
    (ha₁ : ρ.findVal? "at_1" = some nt₁) (hi₁ : ρ.findVal? "i_1" = some i₁)
    (ha₂ : ρ.findVal? "at_2" = some nt₂) (hi₂ : ρ.findVal? "i_2" = some i₂)
    (ha' : ρ.findVal? "at'" = some nt') (hn : ρ.findVal? "n" = some nv)
    (hx : ρ.findVal? "x" = some x) (hy : ρ.findVal? "y" = some y) :
    MatchExps env ρ
      [.caseE "CONST" (.tupE [.subE (.varE "at_1") ta tb, .varE "i_1"]),
       .caseE "CONST" (.tupE [.subE (.varE "at_2") tc td, .varE "i_2"]),
       .caseE "TABLE.GET" (.varE "y"),
       .caseE "TABLE.SET" (.varE "x"),
       .caseE "CONST" (.tupE [.subE (.varE "at_1") ta tb,
         .caseE "%" (.tupE [.binE .addOp (.numT .natT)
           (.projE (.uncaseE (.varE "i_1") "%") 0) (.numE (.natN 1))])]),
       .caseE "CONST" (.tupE [.subE (.varE "at_2") tc td,
         .caseE "%" (.tupE [.binE .addOp (.numT .natT)
           (.projE (.uncaseE (.varE "i_2") "%") 0) (.numE (.natN 1))])]),
       .caseE "CONST" (.tupE [.subE (.varE "at'") te tf,
         .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
           (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
           .intT .natT])]),
       .caseE "TABLE.COPY" (.tupE [.varE "x", .varE "y"])] vs ρ' ↔
      ∃ k₁ us₁ k₂ us₂ mn m,
        i₁ = .case "%" (.tuple (.num (.natN k₁) :: us₁)) ∧
        i₂ = .case "%" (.tuple (.num (.natN k₂) :: us₂)) ∧
        nv = .num mn ∧ PredPair mn m ∧
        vs = [Execution.constV nt₁ i₁, Execution.constV nt₂ i₂,
              .case "TABLE.GET" y, .case "TABLE.SET" x,
              Execution.constV nt₁ (Execution.pctV (k₁ + 1)),
              Execution.constV nt₂ (Execution.pctV (k₂ + 1)),
              Execution.constV nt' (.case "%" (.tuple [.num m])),
              .case "TABLE.COPY" (.tuple [x, y])] ∧
        ρ' = ρ := by
  constructor
  · intro h
    obtain ⟨w1, ws1, σ1, rfl, h1, t1⟩ := Validation.matchExps_cons_iff.1 h
    obtain ⟨a1, b1, τ1, rfl, hA1, hB1⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha₁] at hA1
    obtain ⟨rfl, rfl⟩ := hA1
    rw [matchExp_boundVar_iff hi₁] at hB1
    obtain ⟨rfl, rfl⟩ := hB1
    obtain ⟨w2, ws2, σ2, rfl, h2, t2⟩ := Validation.matchExps_cons_iff.1 t1
    obtain ⟨a2, b2, τ2, rfl, hA2, hB2⟩ := matchExp_const_iff.1 h2
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha₂] at hA2
    obtain ⟨rfl, rfl⟩ := hA2
    rw [matchExp_boundVar_iff hi₂] at hB2
    obtain ⟨rfl, rfl⟩ := hB2
    obtain ⟨w3, ws3, σ3, rfl, h3, t3⟩ := Validation.matchExps_cons_iff.1 t2
    obtain ⟨c3, rfl, hc3⟩ := Validation.matchExp_case_iff.1 h3
    rw [matchExp_boundVar_iff hy] at hc3
    obtain ⟨rfl, rfl⟩ := hc3
    obtain ⟨w4, ws4, σ4, rfl, h4, t4⟩ := Validation.matchExps_cons_iff.1 t3
    obtain ⟨c4, rfl, hc4⟩ := Validation.matchExp_case_iff.1 h4
    rw [matchExp_boundVar_iff hx] at hc4
    obtain ⟨rfl, rfl⟩ := hc4
    obtain ⟨w5, ws5, σ5, rfl, h5, t5⟩ := Validation.matchExps_cons_iff.1 t4
    obtain ⟨a5, b5, τ5, rfl, hA5, hB5⟩ := matchExp_const_iff.1 h5
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha₁] at hA5
    obtain ⟨rfl, rfl⟩ := hA5
    rw [matchExp_succPct_iff hi₁] at hB5
    obtain ⟨k₁, us₁, hk₁, rfl, rfl⟩ := hB5
    obtain ⟨w6, ws6, σ6, rfl, h6, t6⟩ := Validation.matchExps_cons_iff.1 t5
    obtain ⟨a6, b6, τ6, rfl, hA6, hB6⟩ := matchExp_const_iff.1 h6
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha₂] at hA6
    obtain ⟨rfl, rfl⟩ := hA6
    rw [matchExp_succPct_iff hi₂] at hB6
    obtain ⟨k₂, us₂, hk₂, rfl, rfl⟩ := hB6
    obtain ⟨w7, ws7, σ7, rfl, h7, t7⟩ := Validation.matchExps_cons_iff.1 t6
    obtain ⟨a7, b7, τ7, rfl, hA7, hB7⟩ := matchExp_const_iff.1 h7
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha'] at hA7
    obtain ⟨rfl, rfl⟩ := hA7
    rw [matchExp_predPct_iff hn] at hB7
    obtain ⟨mn, m, hnv, rfl, hpred, rfl⟩ := hB7
    obtain ⟨w8, ws8, σ8, rfl, h8, t8⟩ := Validation.matchExps_cons_iff.1 t7
    rw [matchExp_twoIdxBound_iff hx hy] at h8
    obtain ⟨rfl, rfl⟩ := h8
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 t8
    exact ⟨k₁, us₁, k₂, us₂, mn, m, hk₁, hk₂, hnv, hpred, rfl, rfl⟩
  · rintro ⟨k₁, us₁, k₂, us₂, mn, m, hk₁, hk₂, hnv, hpred, rfl, rfl⟩
    refine Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
        Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha₁).2 ⟨rfl, rfl⟩),
        (matchExp_boundVar_iff hi₁).2 ⟨rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha₂).2 ⟨rfl, rfl⟩),
        (matchExp_boundVar_iff hi₂).2 ⟨rfl, rfl⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha₁).2 ⟨rfl, rfl⟩),
        (matchExp_succPct_iff hi₁).2 ⟨k₁, us₁, hk₁, rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha₂).2 ⟨rfl, rfl⟩),
        (matchExp_succPct_iff hi₂).2 ⟨k₂, us₂, hk₂, rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha').2 ⟨rfl, rfl⟩),
        (matchExp_predPct_iff hn).2 ⟨mn, m, hnv, rfl, hpred, rfl⟩⟩
    · exact (matchExp_twoIdxBound_iff hx hy).2 ⟨rfl, rfl⟩

/-- **`Step_read/table.copy-le`, characterised exactly.** -/
theorem ruleFires_tableCopyLe_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableCopyLeRule ↔
      ∃ z nt₁ k₁ us₁ nt₂ k₂ us₂ nt' mn m x y,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt₁ (.case "%" (.tuple (.num (.natN k₁) :: us₁))),
              Execution.constV nt₂ (.case "%" (.tuple (.num (.natN k₂) :: us₂))),
              Execution.constV nt' (.case "%" (.tuple [.num mn])),
              .case "TABLE.COPY" (.tuple [x, y])],
           .list
             [Execution.constV nt₁ (.case "%" (.tuple (.num (.natN k₁) :: us₁))),
              Execution.constV nt₂ (.case "%" (.tuple (.num (.natN k₂) :: us₂))),
              .case "TABLE.GET" y, .case "TABLE.SET" x,
              Execution.constV nt₁ (Execution.pctV (k₁ + 1)),
              Execution.constV nt₂ (Execution.pctV (k₂ + 1)),
              Execution.constV nt' (.case "%" (.tuple [.num m])),
              .case "TABLE.COPY" (.tuple [x, y])]] ∧
        k₁ ≤ k₂ ∧ PredPair mn m := by
  unfold tableCopyLeRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    rw [matchExps_copyLhs_iff (x₁ := "x") (x₂ := "y")
      (by intros; simp [copyPre]) (by intros; simp [copyPre])] at his
    obtain ⟨nt₁, i₁, nt₂, i₂, nt', nv, x, y, rfl, rfl⟩ := his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    rw [matchExps_copyLeRhs_iff (nt₁ := nt₁) (i₁ := i₁) (nt₂ := nt₂) (i₂ := i₂)
      (nt' := nt') (nv := nv) (x := x) (y := y)
      (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
      (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
      (by simp [copyPre])] at hbvs
    obtain ⟨k₁, us₁, k₂, us₂, mn, m, rfl, rfl, rfl, hpred, rfl, rfl⟩ := hbvs
    obtain ⟨-, hev⟩ := ExecRef.premsHold_elseIf_iff.1 hp
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_imm_iff (x := "i_1")
      (c := .case "%" (.tuple (.num (.natN k₁) :: us₁))) (by simp [copyPre])] at hu₁
    obtain ⟨vs₁, heq₁⟩ := hu₁
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at heq₁
    obtain ⟨rfl, -⟩ := heq₁
    obtain ⟨p, hp₂, hle⟩ := cmpValues_le_natL hcmp
    rw [evalExp_imm_iff (x := "i_2")
      (c := .case "%" (.tuple (.num (.natN k₂) :: us₂))) (by simp [copyPre])] at hu₂
    obtain ⟨vs₂, heq₂⟩ := hu₂
    rw [hp₂] at heq₂
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
      Num.natN.injEq, true_and] at heq₂
    obtain ⟨rfl, -⟩ := heq₂
    exact ⟨z, nt₁, k₁, us₁, nt₂, k₂, us₂, nt', mn, m, x, y, rfl, hle, hpred⟩
  · rintro ⟨z, nt₁, k₁, us₁, nt₂, k₂, us₂, nt', mn, m, x, y, rfl, hle, hpred⟩
    refine ⟨((copyPre z nt₁ (.case "%" (.tuple (.num (.natN k₁) :: us₁))) nt₂
        (.case "%" (.tuple (.num (.natN k₂) :: us₂))) nt' (.num mn)).bindVal "x" x).bindVal "y" y,
      ((copyPre z nt₁ (.case "%" (.tuple (.num (.natN k₁) :: us₁))) nt₂
        (.case "%" (.tuple (.num (.natN k₂) :: us₂))) nt' (.num mn)).bindVal "x" x).bindVal "y" y,
      matchExp_concl_iff.2 ⟨_, _,
        ((copyPre z nt₁ (.case "%" (.tuple (.num (.natN k₁) :: us₁))) nt₂
          (.case "%" (.tuple (.num (.natN k₂) :: us₂))) nt'
          (.num mn)).bindVal "x" x).bindVal "y" y, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        (matchExps_copyLhs_iff (x₁ := "x") (x₂ := "y")
          (by intros; simp [copyPre]) (by intros; simp [copyPre])).2
        ⟨nt₁, _, nt₂, _, nt', .num mn, x, y, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        (matchExps_copyLeRhs_iff (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
          (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
          (by simp [copyPre])).2 ⟨k₁, us₁, k₂, us₂, mn, m, rfl, rfl, rfl, hpred, rfl, rfl⟩⟩
    · refine ExecRef.premsHold_elseIf_iff.2 ⟨rfl, evalExp_cmpE_iff.2
        ⟨.num (.natN k₁), .num (.natN k₂),
          (evalExp_imm_iff (by simp [copyPre])).2 ⟨us₁, rfl⟩,
          (evalExp_imm_iff (by simp [copyPre])).2 ⟨us₂, rfl⟩, ?_⟩⟩
      simp only [cmpValues, Num.cmp, Res.ofOption, Option.map_some, Except.ok.injEq,
        Value.bool.injEq, decide_eq_true_eq]
      omega

/-- The right-hand side of `table.init-succ`.  Its second instruction is
`$elem(z, y).REFS[j!%.0]`, an `IdxE` pattern, so it is matched by being
evaluated, exactly as in `table.get-val`. -/
theorem matchExps_initSuccRhs_iff {env : Env} {ρ ρ' : VarEnv} {ta tb tc td : Typ}
    {z nt i j nv x y : Value} {vs : List Value}
    (hz : ρ.findVal? "z" = some z) (hnt : ρ.findVal? "at" = some nt)
    (hi : ρ.findVal? "i" = some i) (hj : ρ.findVal? "j" = some j)
    (hn : ρ.findVal? "n" = some nv)
    (hx : ρ.findVal? "x" = some x) (hy : ρ.findVal? "y" = some y)
    (hd : ρ.findDef? "elem" = none) :
    MatchExps env ρ
      [.caseE "CONST" (.tupE [.subE (.varE "at") ta tb, .varE "i"]),
       .subE (.idxE (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE "y")]) "REFS")
         (.projE (.uncaseE (.varE "j") "%") 0)) tc td,
       .caseE "TABLE.SET" (.varE "x"),
       .caseE "CONST" (.tupE [.subE (.varE "at") ta tb,
         .caseE "%" (.tupE [.binE .addOp (.numT .natT)
           (.projE (.uncaseE (.varE "i") "%") 0) (.numE (.natN 1))])]),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
         .caseE "%" (.tupE [.binE .addOp (.numT .natT)
           (.projE (.uncaseE (.varE "j") "%") 0) (.numE (.natN 1))])]),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
         .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
           (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
           .intT .natT])]),
       .caseE "TABLE.INIT" (.tupE [.varE "x", .varE "y"])] vs ρ' ↔
      ∃ k us jk js mn m refs r,
        i = .case "%" (.tuple (.num (.natN k) :: us)) ∧
        j = .case "%" (.tuple (.num (.natN jk) :: js)) ∧
        nv = .num mn ∧ PredPair mn m ∧
        RefsOf env "elem" z y refs ∧ refs[jk]? = some r ∧
        vs = [Execution.constV nt i, r, .case "TABLE.SET" x,
              Execution.constV nt (Execution.pctV (k + 1)),
              Execution.constV Execution.i32V (Execution.pctV (jk + 1)),
              Execution.constV Execution.i32V (.case "%" (.tuple [.num m])),
              .case "TABLE.INIT" (.tuple [x, y])] ∧
        ρ' = ρ := by
  constructor
  · intro h
    obtain ⟨w1, ws1, σ1, rfl, h1, t1⟩ := Validation.matchExps_cons_iff.1 h
    obtain ⟨a1, b1, τ1, rfl, hA1, hB1⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hnt] at hA1
    obtain ⟨rfl, rfl⟩ := hA1
    rw [matchExp_boundVar_iff hi] at hB1
    obtain ⟨rfl, rfl⟩ := hB1
    obtain ⟨w2, ws2, σ2, rfl, h2, t2⟩ := Validation.matchExps_cons_iff.1 t1
    rw [Validation.matchExp_sub_iff] at h2
    obtain ⟨hidx, rfl⟩ := ExecDefault.matchExp_idxE_iff.1 h2
    obtain ⟨wv, jj, hdot, hjv, hsel⟩ := evalExp_idxE_iff.1 hidx
    rw [evalExp_dotRefs_iff (a := z) (b := y) hz hy hd] at hdot
    obtain ⟨sv, happ, hfield⟩ := hdot
    rw [evalExp_imm_iff hj] at hjv
    obtain ⟨us'', hjj⟩ := hjv
    obtain ⟨w3, ws3, σ3, rfl, h3, t3⟩ := Validation.matchExps_cons_iff.1 t2
    obtain ⟨c3, rfl, hc3⟩ := Validation.matchExp_case_iff.1 h3
    rw [matchExp_boundVar_iff hx] at hc3
    obtain ⟨rfl, rfl⟩ := hc3
    obtain ⟨w4, ws4, σ4, rfl, h4, t4⟩ := Validation.matchExps_cons_iff.1 t3
    obtain ⟨a4, b4, τ4, rfl, hA4, hB4⟩ := matchExp_const_iff.1 h4
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hnt] at hA4
    obtain ⟨rfl, rfl⟩ := hA4
    rw [matchExp_succPct_iff hi] at hB4
    obtain ⟨k, us, hik, rfl, rfl⟩ := hB4
    obtain ⟨w5, ws5, σ5, rfl, h5, t5⟩ := Validation.matchExps_cons_iff.1 t4
    obtain ⟨a5, b5, τ5, rfl, hA5, hB5⟩ := matchExp_const_iff.1 h5
    rw [matchExp_caseNil_iff] at hA5
    obtain ⟨rfl, rfl⟩ := hA5
    rw [matchExp_succPct_iff hj] at hB5
    obtain ⟨jk, js, hjk, rfl, rfl⟩ := hB5
    obtain ⟨w6, ws6, σ6, rfl, h6, t6⟩ := Validation.matchExps_cons_iff.1 t5
    obtain ⟨a6, b6, τ6, rfl, hA6, hB6⟩ := matchExp_const_iff.1 h6
    rw [matchExp_caseNil_iff] at hA6
    obtain ⟨rfl, rfl⟩ := hA6
    rw [matchExp_predPct_iff hn] at hB6
    obtain ⟨mn, m, hnv, rfl, hpred, rfl⟩ := hB6
    obtain ⟨w7, ws7, σ7, rfl, h7, t7⟩ := Validation.matchExps_cons_iff.1 t6
    rw [matchExp_twoIdxBound_iff hx hy] at h7
    obtain ⟨rfl, rfl⟩ := h7
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 t7
    rw [hjk] at hjj
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
      Num.natN.injEq, true_and] at hjj
    obtain ⟨rfl, -⟩ := hjj
    cases wv with
    | list refs =>
        exact ⟨k, us, jk, js, mn, m, refs, w2, hik, hjk, hnv, hpred,
          ⟨sv, happ, hfield⟩, by simpa [Value.idx?] using hsel, rfl, rfl⟩
    | _ => simp [Value.idx?] at hsel
  · rintro ⟨k, us, jk, js, mn, m, refs, r, hik, hjk, hnv, hpred, hrefs, hsel, rfl, rfl⟩
    refine Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
        Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hnt).2 ⟨rfl, rfl⟩),
        (matchExp_boundVar_iff hi).2 ⟨rfl, rfl⟩⟩
    · refine Validation.matchExp_sub_iff.2 (ExecDefault.matchExp_idxE_iff.2
        ⟨evalExp_idxE_iff.2 ⟨.list refs, jk, ?_, ?_, by simpa [Value.idx?] using hsel⟩, rfl⟩)
      · exact (evalExp_dotRefs_iff (a := z) (b := y) hz hy hd).2 hrefs
      · exact (evalExp_imm_iff hj).2 ⟨js, hjk⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hnt).2 ⟨rfl, rfl⟩),
        (matchExp_succPct_iff hi).2 ⟨k, us, hik, rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_succPct_iff hj).2 ⟨jk, js, hjk, rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_predPct_iff hn).2 ⟨mn, m, hnv, rfl, hpred, rfl⟩⟩
    · exact (matchExp_twoIdxBound_iff hx hy).2 ⟨rfl, rfl⟩

/-- **`Step_read/table.init-succ`, characterised exactly.** -/
theorem ruleFires_tableInitSucc_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableInitSuccRule ↔
      ∃ z nt k us jk js mn m x y refs r,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt (.case "%" (.tuple (.num (.natN k) :: us))),
              Execution.constV Execution.i32V
                (.case "%" (.tuple (.num (.natN jk) :: js))),
              Execution.constV Execution.i32V (.case "%" (.tuple [.num mn])),
              .case "TABLE.INIT" (.tuple [x, y])],
           .list
             [Execution.constV nt (.case "%" (.tuple (.num (.natN k) :: us))), r,
              .case "TABLE.SET" x,
              Execution.constV nt (Execution.pctV (k + 1)),
              Execution.constV Execution.i32V (Execution.pctV (jk + 1)),
              Execution.constV Execution.i32V (.case "%" (.tuple [.num m])),
              .case "TABLE.INIT" (.tuple [x, y])]] ∧
        RefsOf env "elem" z y refs ∧ refs[jk]? = some r ∧ PredPair mn m := by
  unfold tableInitSuccRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    obtain ⟨nt, i, j, nv, x, y, rfl, rfl⟩ := matchExps_initLhs_iff.1 his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    rw [matchExps_initSuccRhs_iff (z := z) (nt := nt) (i := i) (j := j) (nv := nv)
      (x := x) (y := y)
      (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
      (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
      (by simp [initScope]) rfl] at hbvs
    obtain ⟨k, us, jk, js, mn, m, refs, r, rfl, rfl, rfl, hpred, hrefs, hsel, rfl, rfl⟩ := hbvs
    exact ⟨z, nt, k, us, jk, js, mn, m, x, y, refs, r, rfl, hrefs, hsel, hpred⟩
  · rintro ⟨z, nt, k, us, jk, js, mn, m, x, y, refs, r, rfl, hrefs, hsel, hpred⟩
    refine ⟨initScope z nt (.case "%" (.tuple (.num (.natN k) :: us)))
        (.case "%" (.tuple (.num (.natN jk) :: js))) (.num mn) x y,
      initScope z nt (.case "%" (.tuple (.num (.natN k) :: us)))
        (.case "%" (.tuple (.num (.natN jk) :: js))) (.num mn) x y,
      matchExp_concl_iff.2 ⟨_, _,
        initScope z nt (.case "%" (.tuple (.num (.natN k) :: us)))
          (.case "%" (.tuple (.num (.natN jk) :: js))) (.num mn) x y,
        rfl, ?_, ?_⟩, ExecRef.premsHold_else_iff.2 rfl⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        matchExps_initLhs_iff.2 ⟨nt, _, _, .num mn, x, y, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        (matchExps_initSuccRhs_iff (by simp [initScope]) (by simp [initScope])
          (by simp [initScope]) (by simp [initScope]) (by simp [initScope])
          (by simp [initScope]) (by simp [initScope]) rfl).2
        ⟨k, us, jk, js, mn, m, refs, r, rfl, rfl, rfl, hpred, hrefs, hsel, rfl, rfl⟩⟩

/-- An addition that denotes *some* numeral had two numerals. -/
theorem binValues_add_eq_num {v₁ v₂ : Value} {p : Num}
    (h : binValues .addOp v₁ v₂ = .ok (.num p)) :
    ∃ m₁ m₂, v₁ = .num m₁ ∧ v₂ = .num m₂ ∧ Num.bin .addOp m₁ m₂ = some p := by
  cases v₁ with
  | num m₁ =>
      cases v₂ with
      | num m₂ =>
          refine ⟨m₁, m₂, rfl, rfl, ?_⟩
          simp only [binValues, Res.ofOption_eq_ok, Option.map_eq_some_iff,
            Value.num.injEq] at h
          obtain ⟨q, hq, rfl⟩ := h
          exact hq
      | _ => simp [binValues] at h
  | _ => cases v₂ <;> simp [binValues, boolBin, Res.ofOption] at h

/-- `i`'s payload, `n`, and the numeral `$((i!%.0 + n) - 1 : nat)` accepts.
The addition is *evaluated*, so the two operands are numerals of the same
kind; the outer `nat` coercion is a *pattern*, so the result only has to
convert back. -/
def PredSum (mi mn m : Num) : Prop :=
  ∃ p a, Num.bin .addOp mi mn = some p ∧ Num.cvt .intT p = some (.intN a) ∧
    Num.cvt .intT m = some (.intN (a - 1))

/-- `%($((i!%.0 + n) - 1 : nat))` as a *pattern*. -/
theorem matchExp_predSumPct_iff {env : Env} {ρ ρ' : VarEnv} {ii ni : IL.Id}
    {i nv w : Value} (hi : ρ.findVal? ii = some i) (hn : ρ.findVal? ni = some nv) :
    MatchExp env ρ (.caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
        (.cvtE (.binE .addOp (.numT .natT)
          (.projE (.uncaseE (.varE ii) "%") 0) (.varE ni)) .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT])) w ρ' ↔
      ∃ mi us mn m, i = .case "%" (.tuple (.num mi :: us)) ∧ nv = .num mn ∧
        w = .case "%" (.tuple [.num m]) ∧ PredSum mi mn m ∧ ρ' = ρ := by
  rw [matchExp_pct_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨m, m', rfl, hcvt, hbody⟩ := matchExp_cvtE_iff.1 hu
    rw [matchExp_binE_iff] at hbody
    obtain ⟨hev, rfl⟩ := hbody
    obtain ⟨v₁, hv₁, hor⟩ := evalExp_binE_iff.1 hev
    simp only [boolShort_subOp, reduceCtorEq, false_or, true_and] at hor
    obtain ⟨v₂, hv₂, hbin⟩ := hor
    obtain ⟨p, p', hadd, hpcvt, rfl⟩ := evalExp_cvtE_iff.1 hv₁
    obtain ⟨o, o', ho, hocvt, rfl⟩ := evalExp_cvtE_iff.1 hv₂
    rw [evalExp_numE_iff, Value.num.injEq] at ho
    subst ho
    simp only [Num.cvt, Option.some.injEq] at hocvt
    subst hocvt
    obtain ⟨a, rfl⟩ := cvt_intT_eq hpcvt
    have hm' : m' = .intN (a - 1) := by
      have h2 := binValues_sub_intN hbin
      simp only [Value.num.injEq] at h2
      simpa using h2
    subst hm'
    obtain ⟨u₁, hu₁, hor2⟩ := evalExp_binE_iff.1 hadd
    simp only [boolShort_addOp, reduceCtorEq, false_or, true_and] at hor2
    obtain ⟨u₂, hu₂, hbin2⟩ := hor2
    obtain ⟨mi, mnn, rfl, rfl, hbinnum⟩ := binValues_add_eq_num hbin2
    rw [evalExp_imm_iff hi] at hu₁
    obtain ⟨us, hieq⟩ := hu₁
    rw [evalExp_varE_iff, hn, Option.some.injEq] at hu₂
    exact ⟨mi, us, mnn, m, hieq, hu₂, rfl, ⟨p, a, hbinnum, hpcvt, hcvt⟩, rfl⟩
  · rintro ⟨mi, us, mn, m, hieq, rfl, rfl, ⟨p, a, hbinnum, hpcvt, hmcvt⟩, rfl⟩
    refine ⟨_, rfl, matchExp_cvtE_iff.2 ⟨m, .intN (a - 1), rfl, hmcvt, ?_⟩⟩
    refine matchExp_binE_iff.2 ⟨evalExp_binE_iff.2 ⟨.num (.intN a), ?_,
      Or.inr ⟨boolShort_subOp, .num (.intN 1),
        evalExp_cvtE_iff.2 ⟨.natN 1, .intN 1, evalExp_numE_iff.2 rfl, rfl, rfl⟩, rfl⟩⟩, rfl⟩
    refine evalExp_cvtE_iff.2 ⟨p, .intN a, ?_, hpcvt, rfl⟩
    exact evalExp_binE_iff.2 ⟨.num mi, (evalExp_imm_iff hi).2 ⟨us, hieq⟩,
      Or.inr ⟨boolShort_addOp, .num mn, evalExp_varE_iff.2 hn,
        by simp [binValues, hbinnum, Res.ofOption]⟩⟩

/-- The right-hand side of `table.copy-gt`. -/
theorem matchExps_copyGtRhs_iff {env : Env} {ρ ρ' : VarEnv} {ta tb tc td te tf : Typ}
    {nt₁ i₁ nt₂ i₂ nt' nv x y : Value} {vs : List Value}
    (ha₁ : ρ.findVal? "at_1" = some nt₁) (hi₁ : ρ.findVal? "i_1" = some i₁)
    (ha₂ : ρ.findVal? "at_2" = some nt₂) (hi₂ : ρ.findVal? "i_2" = some i₂)
    (ha' : ρ.findVal? "at'" = some nt') (hn : ρ.findVal? "n" = some nv)
    (hx : ρ.findVal? "x" = some x) (hy : ρ.findVal? "y" = some y) :
    MatchExps env ρ
      [.caseE "CONST" (.tupE [.subE (.varE "at_1") ta tb,
         .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
           (.cvtE (.binE .addOp (.numT .natT)
             (.projE (.uncaseE (.varE "i_1") "%") 0) (.varE "n")) .natT .intT)
           (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT])]),
       .caseE "CONST" (.tupE [.subE (.varE "at_2") tc td,
         .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
           (.cvtE (.binE .addOp (.numT .natT)
             (.projE (.uncaseE (.varE "i_2") "%") 0) (.varE "n")) .natT .intT)
           (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT])]),
       .caseE "TABLE.GET" (.varE "y"),
       .caseE "TABLE.SET" (.varE "x"),
       .caseE "CONST" (.tupE [.subE (.varE "at_1") ta tb, .varE "i_1"]),
       .caseE "CONST" (.tupE [.subE (.varE "at_2") tc td, .varE "i_2"]),
       .caseE "CONST" (.tupE [.subE (.varE "at'") te tf,
         .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
           (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
           .intT .natT])]),
       .caseE "TABLE.COPY" (.tupE [.varE "x", .varE "y"])] vs ρ' ↔
      ∃ mi₁ us₁ mi₂ us₂ mn m₁ m₂ m,
        i₁ = .case "%" (.tuple (.num mi₁ :: us₁)) ∧
        i₂ = .case "%" (.tuple (.num mi₂ :: us₂)) ∧
        nv = .num mn ∧
        PredSum mi₁ mn m₁ ∧ PredSum mi₂ mn m₂ ∧ PredPair mn m ∧
        vs = [Execution.constV nt₁ (.case "%" (.tuple [.num m₁])),
              Execution.constV nt₂ (.case "%" (.tuple [.num m₂])),
              .case "TABLE.GET" y, .case "TABLE.SET" x,
              Execution.constV nt₁ i₁, Execution.constV nt₂ i₂,
              Execution.constV nt' (.case "%" (.tuple [.num m])),
              .case "TABLE.COPY" (.tuple [x, y])] ∧
        ρ' = ρ := by
  constructor
  · intro h
    obtain ⟨w1, ws1, σ1, rfl, h1, t1⟩ := Validation.matchExps_cons_iff.1 h
    obtain ⟨a1, b1, τ1, rfl, hA1, hB1⟩ := matchExp_const_iff.1 h1
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha₁] at hA1
    obtain ⟨rfl, rfl⟩ := hA1
    rw [matchExp_predSumPct_iff hi₁ hn] at hB1
    obtain ⟨mi₁, us₁, mn, m₁, hieq₁, hnv, rfl, hps₁, rfl⟩ := hB1
    obtain ⟨w2, ws2, σ2, rfl, h2, t2⟩ := Validation.matchExps_cons_iff.1 t1
    obtain ⟨a2, b2, τ2, rfl, hA2, hB2⟩ := matchExp_const_iff.1 h2
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha₂] at hA2
    obtain ⟨rfl, rfl⟩ := hA2
    rw [matchExp_predSumPct_iff hi₂ hn] at hB2
    obtain ⟨mi₂, us₂, mn', m₂, hieq₂, hnv', rfl, hps₂, rfl⟩ := hB2
    rw [hnv] at hnv'
    simp only [Value.num.injEq] at hnv'
    subst hnv'
    obtain ⟨w3, ws3, σ3, rfl, h3, t3⟩ := Validation.matchExps_cons_iff.1 t2
    obtain ⟨c3, rfl, hc3⟩ := Validation.matchExp_case_iff.1 h3
    rw [matchExp_boundVar_iff hy] at hc3
    obtain ⟨rfl, rfl⟩ := hc3
    obtain ⟨w4, ws4, σ4, rfl, h4, t4⟩ := Validation.matchExps_cons_iff.1 t3
    obtain ⟨c4, rfl, hc4⟩ := Validation.matchExp_case_iff.1 h4
    rw [matchExp_boundVar_iff hx] at hc4
    obtain ⟨rfl, rfl⟩ := hc4
    obtain ⟨w5, ws5, σ5, rfl, h5, t5⟩ := Validation.matchExps_cons_iff.1 t4
    obtain ⟨a5, b5, τ5, rfl, hA5, hB5⟩ := matchExp_const_iff.1 h5
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha₁] at hA5
    obtain ⟨rfl, rfl⟩ := hA5
    rw [matchExp_boundVar_iff hi₁] at hB5
    obtain ⟨rfl, rfl⟩ := hB5
    obtain ⟨w6, ws6, σ6, rfl, h6, t6⟩ := Validation.matchExps_cons_iff.1 t5
    obtain ⟨a6, b6, τ6, rfl, hA6, hB6⟩ := matchExp_const_iff.1 h6
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha₂] at hA6
    obtain ⟨rfl, rfl⟩ := hA6
    rw [matchExp_boundVar_iff hi₂] at hB6
    obtain ⟨rfl, rfl⟩ := hB6
    obtain ⟨w7, ws7, σ7, rfl, h7, t7⟩ := Validation.matchExps_cons_iff.1 t6
    obtain ⟨a7, b7, τ7, rfl, hA7, hB7⟩ := matchExp_const_iff.1 h7
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff ha'] at hA7
    obtain ⟨rfl, rfl⟩ := hA7
    rw [matchExp_predPct_iff hn] at hB7
    obtain ⟨mn₂, m, hnv₂, rfl, hpred, rfl⟩ := hB7
    rw [hnv] at hnv₂
    simp only [Value.num.injEq] at hnv₂
    subst hnv₂
    obtain ⟨w8, ws8, σ8, rfl, h8, t8⟩ := Validation.matchExps_cons_iff.1 t7
    rw [matchExp_twoIdxBound_iff hx hy] at h8
    obtain ⟨rfl, rfl⟩ := h8
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 t8
    exact ⟨mi₁, us₁, mi₂, us₂, mn, m₁, m₂, m, hieq₁, hieq₂, hnv, hps₁, hps₂, hpred,
      rfl, rfl⟩
  · rintro ⟨mi₁, us₁, mi₂, us₂, mn, m₁, m₂, m, hieq₁, hieq₂, hnv, hps₁, hps₂, hpred,
      rfl, rfl⟩
    refine Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
        Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha₁).2 ⟨rfl, rfl⟩),
        (matchExp_predSumPct_iff hi₁ hn).2 ⟨mi₁, us₁, mn, m₁, hieq₁, hnv, rfl, hps₁, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha₂).2 ⟨rfl, rfl⟩),
        (matchExp_predSumPct_iff hi₂ hn).2 ⟨mi₂, us₂, mn, m₂, hieq₂, hnv, rfl, hps₂, rfl⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha₁).2 ⟨rfl, rfl⟩),
        (matchExp_boundVar_iff hi₁).2 ⟨rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha₂).2 ⟨rfl, rfl⟩),
        (matchExp_boundVar_iff hi₂).2 ⟨rfl, rfl⟩⟩
    · exact matchExp_const_iff.2 ⟨_, _, ρ', rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff ha').2 ⟨rfl, rfl⟩),
        (matchExp_predPct_iff hn).2 ⟨mn, m, hnv, rfl, hpred, rfl⟩⟩
    · exact (matchExp_twoIdxBound_iff hx hy).2 ⟨rfl, rfl⟩

/-- **`Step_read/table.copy-gt`, characterised exactly.**  The only premise is
`else`, and — unlike the `-le` rule — nothing compares the two indices: the
rule fires on *every* pair whose right-hand side is writable.  What constrains
it is arithmetic: the output's first two constants are `$((i + n) - 1 : nat)`,
so `i`'s payload and `n` must be numerals of the same kind that add.  Even
that does not force them to be `nat` numerals, because the outer coercion is
matched by `Num.cvt`, not computed. -/
theorem ruleFires_tableCopyGt_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableCopyGtRule ↔
      ∃ z nt₁ mi₁ us₁ nt₂ mi₂ us₂ nt' mn m₁ m₂ m x y,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV nt₁ (.case "%" (.tuple (.num mi₁ :: us₁))),
              Execution.constV nt₂ (.case "%" (.tuple (.num mi₂ :: us₂))),
              Execution.constV nt' (.case "%" (.tuple [.num mn])),
              .case "TABLE.COPY" (.tuple [x, y])],
           .list
             [Execution.constV nt₁ (.case "%" (.tuple [.num m₁])),
              Execution.constV nt₂ (.case "%" (.tuple [.num m₂])),
              .case "TABLE.GET" y, .case "TABLE.SET" x,
              Execution.constV nt₁ (.case "%" (.tuple (.num mi₁ :: us₁))),
              Execution.constV nt₂ (.case "%" (.tuple (.num mi₂ :: us₂))),
              Execution.constV nt' (.case "%" (.tuple [.num m])),
              .case "TABLE.COPY" (.tuple [x, y])]] ∧
        PredSum mi₁ mn m₁ ∧ PredSum mi₂ mn m₂ ∧ PredPair mn m := by
  unfold tableCopyGtRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, is, rfl, his⟩ := matchExp_readConfig_iff.1 hl
    rw [matchExps_copyLhs_iff (x₁ := "x") (x₂ := "y")
      (by intros; simp [copyPre]) (by intros; simp [copyPre])] at his
    obtain ⟨nt₁, i₁, nt₂, i₂, nt', nv, x, y, rfl, rfl⟩ := his
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    rw [matchExps_copyGtRhs_iff (nt₁ := nt₁) (i₁ := i₁) (nt₂ := nt₂) (i₂ := i₂)
      (nt' := nt') (nv := nv) (x := x) (y := y)
      (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
      (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
      (by simp [copyPre])] at hbvs
    obtain ⟨mi₁, us₁, mi₂, us₂, mn, m₁, m₂, m, rfl, rfl, rfl, hps₁, hps₂, hpred,
      rfl, rfl⟩ := hbvs
    exact ⟨z, nt₁, mi₁, us₁, nt₂, mi₂, us₂, nt', mn, m₁, m₂, m, x, y, rfl,
      hps₁, hps₂, hpred⟩
  · rintro ⟨z, nt₁, mi₁, us₁, nt₂, mi₂, us₂, nt', mn, m₁, m₂, m, x, y, rfl,
      hps₁, hps₂, hpred⟩
    refine ⟨((copyPre z nt₁ (.case "%" (.tuple (.num mi₁ :: us₁))) nt₂
        (.case "%" (.tuple (.num mi₂ :: us₂))) nt' (.num mn)).bindVal "x" x).bindVal "y" y,
      ((copyPre z nt₁ (.case "%" (.tuple (.num mi₁ :: us₁))) nt₂
        (.case "%" (.tuple (.num mi₂ :: us₂))) nt' (.num mn)).bindVal "x" x).bindVal "y" y,
      matchExp_concl_iff.2 ⟨_, _,
        ((copyPre z nt₁ (.case "%" (.tuple (.num mi₁ :: us₁))) nt₂
          (.case "%" (.tuple (.num mi₂ :: us₂))) nt'
          (.num mn)).bindVal "x" x).bindVal "y" y, rfl, ?_, ?_⟩,
      ExecRef.premsHold_else_iff.2 rfl⟩
    · exact matchExp_readConfig_iff.2 ⟨z, _, rfl,
        (matchExps_copyLhs_iff (x₁ := "x") (x₂ := "y")
          (by intros; simp [copyPre]) (by intros; simp [copyPre])).2
        ⟨nt₁, _, nt₂, _, nt', .num mn, x, y, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        (matchExps_copyGtRhs_iff (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
          (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre]) (by simp [copyPre])
          (by simp [copyPre])).2
        ⟨mi₁, us₁, mi₂, us₂, mn, m₁, m₂, m, rfl, rfl, rfl, hps₁, hps₂, hpred, rfl, rfl⟩⟩

end Silmaril.SpecTec.Equiv.ExecReadTable
