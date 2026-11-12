module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Numerics.IntegerN
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Numerics.IntegerN.Agreement
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# SpecTec's integer numerics and Silmaril's agree

The deepest step of `docs/projects/spectec/README.md` applied to one group: the
denotation of the pinned WebAssembly specification's *numerics* — the
`DecD`s of `specification/wasm-3.0/3.1-numerics.scalar.spectec`, read out of
`specs/spectec/wasm-3.0.ast` and interpreted by `Sem/Eval.lean`'s `callDef` —
is exactly what `Silmaril/Wasm/Numerics/IntegerN.lean` computes.

Everything is relative to the pin `608711107b7f1edb13efd57b7d79b49477462d36`.

## The shape of an agreement statement

A SpecTec function is a `DecD`, so its denotation is `CallDef`, and a theorem
reads

```
CallDef env ρ "iadd_" args (bvV (Numerics.iadd_ N i₁ i₂))
```

where `args` is any argument list denoting the bridged inputs.  The bridge is
the "Numeric bridge" section below: it is deliberately *small* — naturals,
integers, rationals, booleans, bit patterns and `sx` — because the numerics
group needs no AST bridge at all.  It is kept in its own section so that it
can be merged with a general `Sem/Bridge.lean` later.

`iN(N)` is `uN(N)` is a one-case variant (`1.1-syntax.values.spectec:10-15`),
so a bit pattern bridges to `%( n )`, i.e. `Value.case "%" (.tuple [.num
(.natN n)])`; that is `bvV`.  `sx` bridges to `U` or `S`, each a nullary
injection; that is `sxV`.

## What is proved

The hypothesis of every theorem is `NumEnv env`, "`env` interprets the
numerics group as the pinned specification does", and `numEnv_wasm30`
discharges it for `envOfScript Specs.wasm30` in a single `rfl` over all 976
top-level definitions.  The `…_wasm30` corollaries are therefore statements
about the pinned bytes, not about a hypothetical environment.

| SpecTec | Silmaril | theorem |
| --- | --- | --- |
| `$bool` | `Numerics.bool_` | `callDef_bool` |
| `$signed_` | `Numerics.signed_` | `callDef_signed` |
| `$inv_signed_` | `Numerics.invSigned_` | `callDef_invSigned` |
| `$sat_u_`, `$sat_s_` | `Numerics.sat_u_`, `sat_s_` | `callDef_satU`, `callDef_satS` |
| `$iadd_`, `$isub_`, `$imul_` | `Numerics.iadd_`, … | `callDef_iadd`, … |
| `$ineg_`, `$iabs_` | `Numerics.ineg_`, `iabs_` | `callDef_ineg`, `callDef_iabs` |
| `$iextend_` | `Numerics.iextend_` | `callDef_iextend` |
| `$imin_`, `$imax_` | `Numerics.imin_`, `imax_` | `callDef_imin`, `callDef_imax` |
| `$iadd_sat_`, `$isub_sat_` | `Numerics.iadd_sat_`, … | `callDef_iaddSat`, … |
| `$ieqz_`, `$inez_`, `$ieq_`, `$ine_` | `Numerics.ieqz_`, … | `callDef_ieqz`, … |
| `$ilt_`, `$igt_`, `$ile_`, `$ige_` | `Numerics.ilt_`, … | `callDef_ilt`, … |
| `$idiv_`, `$irem_` at divisor `0` | `Numerics.idiv_`, `irem_` | `callDef_idiv_zero`, … |

`callDef_iadd_intBinOp` and `callDef_ilt_intRelOp` compose the last link,
`Silmaril/Wasm/Numerics/IntegerN/Agreement.lean`, so that the specification's
`$iadd_` is shown to denote what `Numerics.intBinOp` computes on `i32`/`i64`.

## The side conditions, and why each one is real

* `0 < N` wherever `$signed_`, `$inv_signed_`, `$sat_s_` or `$iextend_` is
  involved.  The elaborated IL computes `2^(N-1)` by subtracting in `int` and
  converting back with `Xl.Num.cvt`, which sends a negative `int` to nothing
  (`spectec/src/xl/num.ml:86`, transcribed as `Sem/Value.lean`'s `Num.cvt`);
  so at `N = 0` **the specification itself is stuck**, while
  `IntegerN.signed_` is total.  This is a genuine difference of
  domain, not of value, and no Wasm width is `0`.
* `i < 2^N` in `callDef_signed`: outside that range *no* clause of `$signed_`
  applies (`3.1-numerics.scalar.spectec:53-54`), so the specification is
  undefined there too.  Every call site supplies `BitVec.isLt`.
* `-2^(N-1) ≤ j < 2^(N-1)` in `callDef_invSigned`, for the same reason
  (`:57-58`); `IntegerN.invSigned_` extends the spec by reduction mod `2^N`,
  as its own docstring says.
* `0 < K ≤ N` in `callDef_iextend`: the signed clause feeds `$signed_(K, …)`
  into `$inv_signed_(N, …)`, which needs the result to fit in width `N`.

## What this file does **not** prove

See the final section, "What is not reached".
-/

@[expose] public section


/-! ## Calling a definition, compositionally

`Silmaril/SpecTec/Sem/Eval.lean` gives the fuel-free relations for expression
evaluation and the `evalExp_*_iff` lemmas that decompose them.  Clause
selection has no such lemmas there, so this section supplies the four it
needs: an introduction rule for `callDef` through `tryClauses`, one for a
clause that fires, one for a clause that is skipped, and the matching and
premise rules those two consume.  Each is the equation lemma of the
corresponding fuel-indexed function, transported to the relation by running
the sub-derivations at a common fuel level. -/

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod
open Res

/-- The argument pattern `a` matches `w`, extending `ρ` to `ρ'`. -/
def MatchArg (env : Env) (ρ : VarEnv) (a : Arg) (w : ArgV) (ρ' : VarEnv) : Prop :=
  ∃ n, matchArg n env ρ a w = .ok ρ'

/-- The pattern `e` *definitely* fails to match `v`: not merely "no scope is
produced at this fuel level", but `.error .undef`, which is what makes
`tryClauses` move on to the next clause. -/
def MatchExpUndef (env : Env) (ρ : VarEnv) (e : Exp) (v : Value) : Prop :=
  ∃ n, matchExp n env ρ e v = .error .undef

/-- The argument patterns `as` definitely fail to match `ws`. -/
def MatchArgsUndef (env : Env) (ρ : VarEnv) (as : List Arg) (ws : List ArgV) : Prop :=
  ∃ n, matchArgs n env ρ as ws = .error .undef

/-- The premises `prs` definitely fail in `ρ`. -/
def PremsUndef (env : Env) (ρ : VarEnv) (prs : List Prem) : Prop :=
  ∃ n, premsHold n env ρ prs = .error .undef

/-- The clause list `cs`, applied to `ws`, yields `v`. -/
def TryClauses (env : Env) (cs : List Clause) (ws : List ArgV) (v : Value) : Prop :=
  ∃ n, tryClauses n env cs ws = .ok v

/-- A definite failure stays a definite failure when the fuel grows: `⊑` can
only move `outOfFuel`. -/
theorem undef_of_le {α : Type} {r₁ r₂ : Res α} (hmono : r₁ ⊑ r₂)
    (hv : r₁ = .error .undef) : r₂ = .error .undef := by
  rw [Res.Le.eq_of_ne_oof hmono (by rw [hv]; simp), hv]

/-- More fuel preserves a scope `matchArg` has committed to. -/
theorem matchArg_ok_of_le {m n : Nat} {env ρ a w ρ'} (h : m ≤ n)
    (hv : matchArg m env ρ a w = .ok ρ') : matchArg n env ρ a w = .ok ρ' :=
  ((monoAt_of_le h).matchArg env ρ a w).ok hv

/-- More fuel preserves a scope `matchArgs` has committed to. -/
theorem matchArgs_ok_of_le {m n : Nat} {env ρ as ws ρ'} (h : m ≤ n)
    (hv : matchArgs m env ρ as ws = .ok ρ') : matchArgs n env ρ as ws = .ok ρ' :=
  ((monoAt_of_le h).matchArgs env ρ as ws).ok hv

/-- More fuel preserves a definite failure of `matchExp`. -/
theorem matchExp_undef_of_le {m n : Nat} {env ρ e v} (h : m ≤ n)
    (hv : matchExp m env ρ e v = .error .undef) : matchExp n env ρ e v = .error .undef :=
  undef_of_le ((monoAt_of_le h).matchExp env ρ e v) hv

/-- More fuel preserves a definite failure of `matchArgs`. -/
theorem matchArgs_undef_of_le {m n : Nat} {env ρ as ws} (h : m ≤ n)
    (hv : matchArgs m env ρ as ws = .error .undef) :
    matchArgs n env ρ as ws = .error .undef :=
  undef_of_le ((monoAt_of_le h).matchArgs env ρ as ws) hv

/-- More fuel preserves a definite failure of `tryClauses`. -/
theorem tryClauses_undef_of_le {m n : Nat} {env cs ws} (h : m ≤ n)
    (hv : tryClauses m env cs ws = .error .undef) :
    tryClauses n env cs ws = .error .undef :=
  undef_of_le ((monoAt_of_le h).tryClauses env cs ws) hv

/-- More fuel preserves a definite failure of `premsHold`. -/
theorem premsHold_undef_of_le {m n : Nat} {env ρ prs} (h : m ≤ n)
    (hv : premsHold m env ρ prs = .error .undef) :
    premsHold n env ρ prs = .error .undef :=
  undef_of_le ((monoAt_of_le h).premsHold env ρ prs) hv

/-- More fuel preserves a value `tryClauses` has committed to. -/
theorem tryClauses_ok_of_le {m n : Nat} {env cs ws v} (h : m ≤ n)
    (hv : tryClauses m env cs ws = .ok v) : tryClauses n env cs ws = .ok v :=
  ((monoAt_of_le h).tryClauses env cs ws).ok hv

/-! ### Matching -/

/-- An unbound variable pattern matches anything and binds it. -/
theorem matchExp_varE {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value}
    (h : ρ.findVal? x = none) : MatchExp env ρ (.varE x) v (ρ.bindVal x v) :=
  ⟨1, by simp only [matchExp, h]⟩

/-- A numeral pattern matches only itself. -/
theorem matchExp_numE {env : Env} {ρ : VarEnv} {m : IL.Num} :
    MatchExp env ρ (.numE m) (.num m) ρ := ⟨1, by simp [matchExp]⟩

/-- A boolean pattern matches only itself. -/
theorem matchExp_boolE {env : Env} {ρ : VarEnv} {b : Bool} :
    MatchExp env ρ (.boolE b) (.bool b) ρ := ⟨1, by simp [matchExp]⟩

/-- An injection pattern matches an injection with the same mixop. -/
theorem matchExp_caseE {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {e : Exp} {w : Value}
    (h : MatchExp env ρ e w ρ') : MatchExp env ρ (.caseE op e) (.case op w) ρ' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp [matchExp, Res.assert, Bind.bind, Except.bind, h]⟩

/-- The empty tuple pattern matches the empty tuple. -/
theorem matchExp_tupE_nil {env : Env} {ρ : VarEnv} :
    MatchExp env ρ (.tupE []) (.tuple []) ρ :=
  ⟨2, by simp [matchExp, matchExps, Bind.bind, Except.bind]⟩

/-- A one-component tuple pattern matches a one-component tuple. -/
theorem matchExp_tupE_one {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h : MatchExp env ρ e v ρ') : MatchExp env ρ (.tupE [e]) (.tuple [v]) ρ' := by
  obtain ⟨n, h⟩ := h
  refine ⟨n + 3, ?_⟩
  simp only [matchExp, Res.ofOption, Value.asTuple?, Bind.bind, Except.bind, matchExps,
    matchExp_ok_of_le (show n ≤ n + 1 by omega) h]

/-- A numeral pattern definitely fails on anything else. -/
theorem matchExp_numE_undef {env : Env} {ρ : VarEnv} {m : IL.Num} {v : Value}
    (h : v ≠ .num m) : MatchExpUndef env ρ (.numE m) v :=
  ⟨1, by simp [matchExp, Res.assert, h]⟩

/-- A boolean pattern definitely fails on anything else. -/
theorem matchExp_boolE_undef {env : Env} {ρ : VarEnv} {b : Bool} {v : Value}
    (h : v ≠ .bool b) : MatchExpUndef env ρ (.boolE b) v :=
  ⟨1, by simp [matchExp, Res.assert, h]⟩

/-- An injection pattern definitely fails on an injection with another mixop. -/
theorem matchExp_caseE_undef {env : Env} {ρ : VarEnv} {op op' : MixopS} {e : Exp}
    {w : Value} (h : op' ≠ op) : MatchExpUndef env ρ (.caseE op e) (.case op' w) :=
  ⟨1, by simp [matchExp, Res.assert, Bind.bind, Except.bind, h]⟩

/-- Failure propagates out of an injection pattern. -/
theorem matchExp_caseE_undef' {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp}
    {w : Value} (h : MatchExpUndef env ρ e w) :
    MatchExpUndef env ρ (.caseE op e) (.case op w) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp [matchExp, Res.assert, Bind.bind, Except.bind, h]⟩

/-- Failure propagates out of a one-component tuple pattern. -/
theorem matchExp_tupE_one_undef {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : MatchExpUndef env ρ e v) : MatchExpUndef env ρ (.tupE [e]) (.tuple [v]) := by
  obtain ⟨n, h⟩ := h
  refine ⟨n + 3, ?_⟩
  simp only [matchExp, Res.ofOption, Value.asTuple?, Bind.bind, Except.bind, matchExps,
    matchExp_undef_of_le (show n ≤ n + 1 by omega) h]

/-- An expression argument matches by matching its expression. -/
theorem matchArg_expA {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h : MatchExp env ρ e v ρ') (hs : argSubOk env ρ e v = true := by rfl) :
    MatchArg env ρ (.expA e) (.val v) ρ' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp only [matchArg, hs, h, ite_true]⟩

/-- An expression argument definitely fails when its expression does. -/
theorem matchArg_expA_undef {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : MatchExpUndef env ρ e v) :
    ∃ n, matchArg n env ρ (.expA e) (.val v) = .error .undef := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp only [matchArg, h]; split <;> rfl⟩

/-- The empty argument list matches the empty value list. -/
theorem matchArgs_nil {env : Env} {ρ : VarEnv} : MatchArgs env ρ [] [] ρ :=
  ⟨1, by simp [matchArgs]⟩

/-- Argument lists match head first, threading the scope. -/
theorem matchArgs_cons {env : Env} {ρ ρ' ρ'' : VarEnv} {a : Arg} {as : List Arg}
    {w : ArgV} {ws : List ArgV} (h₁ : MatchArg env ρ a w ρ')
    (h₂ : MatchArgs env ρ' as ws ρ'') : MatchArgs env ρ (a :: as) (w :: ws) ρ'' := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp only [matchArgs, matchArg_ok_of_le (le_max_left n₁ n₂) h₁, Bind.bind, Except.bind,
    matchArgs_ok_of_le (le_max_right n₁ n₂) h₂]

/-- A head failure fails the whole argument list. -/
theorem matchArgs_cons_undef {env : Env} {ρ : VarEnv} {a : Arg} {as : List Arg}
    {w : ArgV} {ws : List ArgV} (h : ∃ n, matchArg n env ρ a w = .error .undef) :
    MatchArgsUndef env ρ (a :: as) (w :: ws) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp only [matchArgs, h, Bind.bind, Except.bind]⟩

/-- A tail failure fails the whole argument list. -/
theorem matchArgs_cons_undef_tail {env : Env} {ρ ρ' : VarEnv} {a : Arg} {as : List Arg}
    {w : ArgV} {ws : List ArgV} (h₁ : MatchArg env ρ a w ρ')
    (h₂ : MatchArgsUndef env ρ' as ws) : MatchArgsUndef env ρ (a :: as) (w :: ws) := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp only [matchArgs, matchArg_ok_of_le (le_max_left n₁ n₂) h₁, Bind.bind, Except.bind,
    matchArgs_undef_of_le (le_max_right n₁ n₂) h₂]

/-! ### Premises -/

/-- `ElsePr` is the trivially-true premise that marks a fallback clause. -/
theorem premsHold_elsePr {env : Env} {ρ : VarEnv} : PremsHold env ρ [.elsePr] ρ :=
  ⟨2, by simp only [premsHold, List.foldlM_cons, List.foldlM_nil, premHolds,
    Bind.bind, Except.bind]; rfl⟩

/-- A side condition that evaluates to `false` fails definitely, so the clause
it guards is skipped. -/
theorem premsUndef_ifPr {env : Env} {ρ : VarEnv} {e : Exp} {prs : List Prem}
    (h : EvalExp env ρ e (.bool false)) : PremsUndef env ρ (.ifPr e :: prs) := by
  obtain ⟨n, h⟩ := h
  refine ⟨n + 2, ?_⟩
  have e1 : premHolds (n + 1) env ρ (.ifPr e) = .error .undef := by
    simp only [premHolds, h, Bind.bind, Except.bind]
    exact Res.assert_neg (by simp) _
  simp only [premsHold, List.foldlM_cons, e1, Bind.bind, Except.bind]

/-! ### Clause selection -/

/-- A clause fires: its argument patterns match, its premises hold, and its
body is evaluated in the scope they built. -/
theorem tryClauses_hit {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV} {ρ₀ ρ₁ : VarEnv} {v : Value}
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (hp : PremsHold env ρ₀ prems ρ₁)
    (he : EvalExp env ρ₁ e v) : TryClauses env (.defD q pats e prems :: cs) ws v := by
  obtain ⟨n₁, hm⟩ := hm
  obtain ⟨n₂, hp⟩ := hp
  obtain ⟨n₃, he⟩ := he
  refine ⟨max (max n₁ n₂) n₃ + 1, ?_⟩
  have e1 := matchArgs_ok_of_le (m := n₁) (n := max (max n₁ n₂) n₃) (by omega) hm
  have e2 := premsHold_ok_of_le (m := n₂) (n := max (max n₁ n₂) n₃) (by omega) hp
  have e3 := evalExp_ok_of_le (m := n₃) (n := max (max n₁ n₂) n₃) (by omega) he
  simp only [tryClauses, e1, Bind.bind, Except.bind, e2, Res.elimUndef_ok, e3]

/-- A clause is skipped when its argument patterns definitely fail. -/
theorem tryClauses_skip_match {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV} {v : Value}
    (hm : MatchArgsUndef env VarEnv.empty pats ws)
    (hrest : TryClauses env cs ws v) : TryClauses env (.defD q pats e prems :: cs) ws v := by
  obtain ⟨n₁, hm⟩ := hm
  obtain ⟨n₂, hrest⟩ := hrest
  refine ⟨max n₁ n₂ + 1, ?_⟩
  have e1 := matchArgs_undef_of_le (m := n₁) (n := max n₁ n₂) (by omega) hm
  have e2 := tryClauses_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) hrest
  simp only [tryClauses, e1, Bind.bind, Except.bind, Res.elimUndef_undef, e2]

/-- A clause is skipped when its premises definitely fail. -/
theorem tryClauses_skip_prem {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV} {ρ₀ : VarEnv} {v : Value}
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (hp : PremsUndef env ρ₀ prems)
    (hrest : TryClauses env cs ws v) : TryClauses env (.defD q pats e prems :: cs) ws v := by
  obtain ⟨n₁, hm⟩ := hm
  obtain ⟨n₂, hp⟩ := hp
  obtain ⟨n₃, hrest⟩ := hrest
  refine ⟨max (max n₁ n₂) n₃ + 1, ?_⟩
  have e1 := matchArgs_ok_of_le (m := n₁) (n := max (max n₁ n₂) n₃) (by omega) hm
  have e2 := premsHold_undef_of_le (m := n₂) (n := max (max n₁ n₂) n₃) (by omega) hp
  have e3 := tryClauses_ok_of_le (m := n₃) (n := max (max n₁ n₂) n₃) (by omega) hrest
  simp only [tryClauses, e1, Bind.bind, Except.bind, e2, Res.elimUndef_undef, e3]

/-- A call reduces to its definition's clause list. -/
theorem callDef_of_tryClauses {env : Env} {ρ : VarEnv} {x : IL.Id} {ps : List Param}
    {t : Typ} {cs : List Clause} {args : List Arg} {ws : List ArgV} {v : Value}
    (hρ : ρ.findDef? x = none) (hd : env.findDef? x = some (ps, t, cs))
    (ha : EvalArgs env ρ args ws) (hc : TryClauses env cs ws v) :
    CallDef env ρ x args v := by
  obtain ⟨n₁, ha⟩ := ha
  obtain ⟨n₂, hc⟩ := hc
  refine ⟨max n₁ n₂ + 1, ?_⟩
  have e1 := evalArgs_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) ha
  have e2 := tryClauses_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) hc
  simp only [callDef, e1, Bind.bind, Except.bind, hρ, Option.getD_none, Res.ofOption, hd, e2,
    Res.elimUndef_ok]

/-- A function with no clauses has no value anywhere: `eval.ml:364-366` leaves
an uninterpreted function unreduced. -/
theorem not_callDef_of_no_clauses {env : Env} {ρ : VarEnv} {x : IL.Id} {ps : List Param}
    {t : Typ} {args : List Arg} {v : Value} (hρ : ρ.findDef? x = none)
    (hd : env.findDef? x = some (ps, t, []))
    (hb : ∀ ws, env.builtins.call x ws = Option.none) : ¬ CallDef env ρ x args v := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [callDef] at hn
  | succ n =>
      simp only [callDef, Res.bind_eq_ok] at hn
      obtain ⟨ws, _, d, hdd, hc⟩ := hn
      simp only [hρ, Option.getD_none, Res.ofOption_eq_ok, hd, Option.some.injEq] at hdd
      subst hdd
      cases n with
      | zero => simp [tryClauses, Res.elimUndef] at hc
      | succ m =>
          have hnil : tryClauses (m + 1) env [] ws = .error .undef := by simp [tryClauses]
          rw [hnil, Res.elimUndef, hρ, Option.getD_none, hb ws] at hc
          simp at hc

/-! ## Evaluating the shapes the numerics group uses

The `evalExp_*_iff` lemmas of `Silmaril/SpecTec/Sem/Eval.lean` decompose an
evaluation into its subterms.  The numerics clauses use a handful of shapes
over and over, so each gets a one-step introduction rule here. -/

/-- A variable denotes what the scope binds it to. -/
theorem evalExp_var {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value}
    (h : ρ.findVal? x = some v) : EvalExp env ρ (.varE x) v :=
  evalExp_varE_iff.2 h

/-- A numeral denotes itself. -/
theorem evalExp_num {env : Env} {ρ : VarEnv} {m : IL.Num} :
    EvalExp env ρ (.numE m) (.num m) := evalExp_numE_iff.2 rfl

/-- The empty list of expressions denotes the empty list of values. -/
theorem evalExps_nil {env : Env} {ρ : VarEnv} : EvalExps env ρ [] [] :=
  ⟨1, by simp only [evalExps, List.mapM_nil]; rfl⟩

/-- A list of expressions denotes the list of their denotations. -/
theorem evalExps_cons {env : Env} {ρ : VarEnv} {e : Exp} {es : List Exp}
    {v : Value} {vs : List Value} (h : EvalExp env ρ e v) (hs : EvalExps env ρ es vs) :
    EvalExps env ρ (e :: es) (v :: vs) := by
  obtain ⟨n₁, h⟩ := h
  obtain ⟨n₂, hs⟩ := hs
  refine ⟨max n₁ n₂ + 1, ?_⟩
  have e1 := evalExp_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) h
  have e2 : es.mapM (evalExp (max n₁ n₂) env ρ) = .ok vs := by
    have := evalExps_ok_of_le (m := n₂) (n := max n₁ n₂ + 1) (by omega) hs
    simpa only [evalExps] using this
  simp only [evalExps, List.mapM_cons, e1, e2, Bind.bind, Except.bind]
  rfl

/-- A binary operator on two numerals, at any operator type: `binValues`
dispatches on the *values*, not on the annotation. -/
theorem evalExp_binNum {env : Env} {ρ : VarEnv} {op : BinOp} {t : OpTyp} {e₁ e₂ : Exp}
    {m₁ m₂ m : IL.Num} (h₁ : EvalExp env ρ e₁ (.num m₁)) (h₂ : EvalExp env ρ e₂ (.num m₂))
    (hm : Num.bin op m₁ m₂ = some m) : EvalExp env ρ (.binE op t e₁ e₂) (.num m) :=
  evalExp_binE_iff.2 ⟨.num m₁, h₁, Or.inr ⟨by cases op <;> rfl, .num m₂, h₂, by
    simp [binValues, hm]⟩⟩

/-- An order comparison of two numerals. -/
theorem evalExp_cmpNum {env : Env} {ρ : VarEnv} {op : CmpOp} {t : OpTyp} {e₁ e₂ : Exp}
    {m₁ m₂ : IL.Num} {b : Bool} (h₁ : EvalExp env ρ e₁ (.num m₁))
    (h₂ : EvalExp env ρ e₂ (.num m₂)) (hm : Num.cmp op m₁ m₂ = some b) :
    EvalExp env ρ (.cmpE op t e₁ e₂) (.bool b) :=
  evalExp_cmpE_iff.2 ⟨.num m₁, .num m₂, h₁, h₂, by
    cases op <;> simp_all [cmpValues, Num.cmp]⟩

/-- An equality test, which `eval.ml:260-263` settles by structural equality. -/
theorem evalExp_eq {env : Env} {ρ : VarEnv} {t : OpTyp} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.cmpE .eqOp t e₁ e₂) (.bool (v₁ == v₂)) :=
  evalExp_cmpE_iff.2 ⟨v₁, v₂, h₁, h₂, rfl⟩

/-- A disequality test. -/
theorem evalExp_ne {env : Env} {ρ : VarEnv} {t : OpTyp} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.cmpE .neOp t e₁ e₂) (.bool (!(v₁ == v₂))) :=
  evalExp_cmpE_iff.2 ⟨v₁, v₂, h₁, h₂, rfl⟩

/-- A unary operator on a numeral. -/
theorem evalExp_unNum {env : Env} {ρ : VarEnv} {op : UnOp} {t : OpTyp} {e : Exp}
    {m m' : IL.Num} (h : EvalExp env ρ e (.num m)) (hm : Num.un op m = some m') :
    EvalExp env ρ (.unE op t e) (.num m') :=
  evalExp_unE_iff.2 ⟨.num m, h, by simp [unValue, hm]⟩

/-- A numeric conversion, which depends only on its target type. -/
theorem evalExp_cvtNum {env : Env} {ρ : VarEnv} {e : Exp} {t₁ t₂ : NumTyp}
    {m m' : IL.Num} (h : EvalExp env ρ e (.num m)) (hm : Num.cvt t₂ m = some m') :
    EvalExp env ρ (.cvtE e t₁ t₂) (.num m') := evalExp_cvtE_iff.2 ⟨m, m', h, hm, rfl⟩

end Silmaril.SpecTec.Sem

namespace Silmaril.SpecTec.Equiv

open Silmaril.SpecTec.IL Silmaril.SpecTec.Sem

/-! ## The numeric bridge -/

/-- A natural number as an IL value. -/
def natV (n : Nat) : Value := .num (.natN n)

/-- An integer as an IL value. -/
def intV (i : Int) : Value := .num (.intN i)

/-- A rational as an IL value. -/
def ratV (q : Rat) : Value := .num (.ratN q)

/-- A boolean as an IL value. -/
def boolV (b : Bool) : Value := .bool b

/-- A bit pattern as a value of the IL's `uN(N)` — equivalently `iN(N)`. -/
def bvV {N : Nat} (i : BitVec N) : Value := .case "%" (.tuple [natV i.toNat])

/-- A signedness as a value of the IL's `sx`. -/
def sxV : Wasm.Signedness → Value
  | .unsigned => .case "U" (.tuple [])
  | .signed => .case "S" (.tuple [])

/-- An optional bit pattern as a value of the IL's `iN(N)?`. -/
def optUNV {N : Nat} (o : Option (BitVec N)) : Value := .opt (o.map bvV)

/-- A value, as the argument expression denoting it. -/
def litArg (v : Value) : Arg := .expA (lit v)

/-- A list of values, as the argument list denoting them. -/
def litArgs (vs : List Value) : List Arg := vs.map litArg

/-! ## Literal arguments -/

/-- Every argument of `litArgs vs` evaluates to the value it spells, at any
fuel budget large enough for the biggest of them. -/
theorem mapM_litArgs {env : Env} {ρ : VarEnv} (k : Nat) :
    ∀ vs : List Value, (∀ v ∈ vs, 2 * v.size + 1 ≤ k) →
      (vs.map litArg).mapM (evalArg (k + 1) env ρ) = .ok (vs.map ArgV.val)
  | [], _ => rfl
  | v :: vs, h => by
      have hv : evalArg (k + 1) env ρ (litArg v) = .ok (.val v) := by
        simp only [litArg, evalArg, litE env ρ v k (h v (by simp)), Functor.map,
          Except.map]
      have hs := mapM_litArgs (env := env) (ρ := ρ) k vs
        (fun w hw => h w (by simp [hw]))
      simp only [List.map_cons, List.mapM_cons, hv, hs, Bind.bind, Except.bind]
      rfl

/-- A literal argument list denotes exactly the values it spells. -/
theorem evalArgs_litArgs (env : Env) (ρ : VarEnv) (vs : List Value) :
    EvalArgs env ρ (litArgs vs) (vs.map ArgV.val) := by
  refine ⟨2 * Value.sizes vs + 3, ?_⟩
  simp only [evalArgs, litArgs]
  exact mapM_litArgs (env := env) (ρ := ρ) (2 * Value.sizes vs + 1) vs
    (fun v hv => by have := Value.size_le_sizes hv; omega)


/-! ## The numerics group of the pinned specification

Each constant below is the `(params, type, clauses)` triple that
`Silmaril/SpecTec/Sem/Env.lean`'s `envOfScript` builds for one definition of
`specification/wasm-3.0/3.1-numerics.scalar.spectec`, read straight off the
pinned `--ast` stream.  `numEnv_wasm30` checks all of them against
`Silmaril.SpecTec.Specs.wasm30` in a single `rfl`.

The clause lists are the *only* thing the agreement theorems below depend on,
so writing them out is what makes those theorems statements about the
specification rather than about an environment nobody built.
-/

/-- `$bool` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:72-74`), as
`envOfScript` records it. -/
def boolDef : List Param × Typ × List Clause :=
  ([(.expP "bool" .boolT)],
   (.numT .natT),
   [(.defD [] [(.expA (.boolE false))] (.numE (.natN 0)) []), (.defD [] [(.expA (.boolE true))]
     (.numE (.natN 1)) [])])

/-- `$signed_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:52-54`), as
`envOfScript` records it. -/
def signedDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "nat" (.numT .natT))],
   (.numT .intT),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i" (.numT .natT))] [(.expA (.varE "N")), (.expA
     (.varE "i"))] (.cvtE (.varE "i") .natT .intT) [(.ifPr (.cmpE .ltOp (.numT .natT) (.varE "i")
     (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp (.numT .intT) (.cvtE
     (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT))))]), (.defD
     [(.expP "N" (.varT "N" [])), (.expP "i" (.numT .natT))] [(.expA (.varE "N")), (.expA (.varE
     "i"))] (.binE .subOp (.numT .intT) (.cvtE (.varE "i") .natT .intT) (.cvtE (.binE .powOp
     (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)) [(.ifPr (.binE .andOp .boolT
     (.cmpE .leOp (.numT .natT) (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp
     (.numT .intT) (.cvtE (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT
     .natT)) (.varE "i")) (.cmpE .ltOp (.numT .natT) (.varE "i") (.binE .powOp (.numT .natT)
     (.numE (.natN 2)) (.varE "N")))))])])

/-- `$inv_signed_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:56-58`), as
`envOfScript` records it. -/
def invSignedDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "int" (.numT .intT))],
   (.numT .natT),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i" (.numT .intT))] [(.expA (.varE "N")), (.expA
     (.varE "i"))] (.cvtE (.varE "i") .intT .natT) [(.ifPr (.binE .andOp .boolT (.cmpE .leOp
     (.numT .intT) (.cvtE (.numE (.natN 0)) .natT .intT) (.varE "i")) (.cmpE .ltOp (.numT .intT)
     (.varE "i") (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp (.numT
     .intT) (.cvtE (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT))
     .natT .intT))))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i" (.numT .intT))] [(.expA
     (.varE "N")), (.expA (.varE "i"))] (.cvtE (.binE .addOp (.numT .intT) (.varE "i") (.cvtE
     (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)) .intT .natT) [(.ifPr
     (.binE .andOp .boolT (.cmpE .leOp (.numT .intT) (.unE .minusOp (.numT .intT) (.cvtE (.binE
     .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "N")
     .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)) .natT .intT)) (.varE "i"))
     (.cmpE .ltOp (.numT .intT) (.varE "i") (.cvtE (.numE (.natN 0)) .natT .intT))))])])

/-- `$sat_u_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:87-90`), as
`envOfScript` records it. -/
def satUDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "int" (.numT .intT))],
   (.numT .natT),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i" (.numT .intT))] [(.expA (.varE "N")), (.expA
     (.varE "i"))] (.numE (.natN 0)) [(.ifPr (.cmpE .ltOp (.numT .intT) (.varE "i") (.cvtE (.numE
     (.natN 0)) .natT .intT)))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i" (.numT .intT))]
     [(.expA (.varE "N")), (.expA (.varE "i"))] (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.binE
     .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT) (.cvtE (.numE (.natN 1))
     .natT .intT)) .intT .natT) [(.ifPr (.cmpE .gtOp (.numT .intT) (.varE "i") (.binE .subOp
     (.numT .intT) (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
     (.cvtE (.numE (.natN 1)) .natT .intT))))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i"
     (.numT .intT))] [(.expA (.varE "N")), (.expA (.varE "i"))] (.cvtE (.varE "i") .intT .natT)
     [.elsePr])])

/-- `$sat_s_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:92-95`), as
`envOfScript` records it. -/
def satSDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "int" (.numT .intT))],
   (.numT .intT),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i" (.numT .intT))] [(.expA (.varE "N")), (.expA
     (.varE "i"))] (.unE .minusOp (.numT .intT) (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN
     2)) (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "N") .natT .intT) (.cvtE (.numE (.natN
     1)) .natT .intT)) .intT .natT)) .natT .intT)) [(.ifPr (.cmpE .ltOp (.numT .intT) (.varE "i")
     (.unE .minusOp (.numT .intT) (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE
     (.binE .subOp (.numT .intT) (.cvtE (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT
     .intT)) .intT .natT)) .natT .intT))))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i"
     (.numT .intT))] [(.expA (.varE "N")), (.expA (.varE "i"))] (.binE .subOp (.numT .intT) (.cvtE
     (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp (.numT .intT) (.cvtE
     (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)) .natT .intT)
     (.cvtE (.numE (.natN 1)) .natT .intT)) [(.ifPr (.cmpE .gtOp (.numT .intT) (.varE "i") (.binE
     .subOp (.numT .intT) (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE
     .subOp (.numT .intT) (.cvtE (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
     .intT .natT)) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))))]), (.defD [(.expP "N"
     (.varT "N" [])), (.expP "i" (.numT .intT))] [(.expA (.varE "N")), (.expA (.varE "i"))] (.varE
     "i") [.elsePr])])

/-- `$ineg_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:147`), as
`envOfScript` records it. -/
def inegDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.varE "i_1"))] (.caseE "%" (.tupE [(.cvtE (.binE .modOp (.numT .intT)
     (.binE .subOp (.numT .intT) (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N"))
     .natT .intT) (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .intT)) (.cvtE (.binE
     .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)) .intT .natT)])) [])])

/-- `$iabs_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:149-150`), as
`envOfScript` records it. -/
def iabsDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.varE "i_1"))] (.varE "i_1") [(.ifPr (.cmpE .geOp (.numT .intT) (.callE
     "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_1") "%") 0))]) (.cvtE
     (.numE (.natN 0)) .natT .intT)))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT
     "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.varE "i_1"))] (.callE "ineg_"
     [(.expA (.varE "N")), (.expA (.varE "i_1"))]) [.elsePr])])

/-- `$iextend_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:161-162`), as
`envOfScript` records it. -/
def iextendDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "K" (.varT "K" [])), (.expP "sx" (.varT "sx" [])), (.expP
    "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "K" (.varT "K" [])), (.expP "i" (.varT "iN" [(.expA
     (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.varE "K")), (.expA (.caseE "U" (.tupE []))),
     (.expA (.varE "i"))] (.caseE "%" (.tupE [(.binE .modOp (.numT .natT) (.projE (.uncaseE (.varE
     "i") "%") 0) (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "K")))])) []), (.defD
     [(.expP "N" (.varT "N" [])), (.expP "K" (.varT "K" [])), (.expP "i" (.varT "iN" [(.expA
     (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.varE "K")), (.expA (.caseE "S" (.tupE []))),
     (.expA (.varE "i"))] (.caseE "%" (.tupE [(.callE "inv_signed_" [(.expA (.varE "N")), (.expA
     (.callE "signed_" [(.expA (.varE "K")), (.expA (.binE .modOp (.numT .natT) (.projE (.uncaseE
     (.varE "i") "%") 0) (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "K"))))]))])]))
     [])])

/-- `$iadd_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:165`), as
`envOfScript` records it. -/
def iaddDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))])), (.expP "iN"
    (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.varE "i_1")),
     (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.binE .modOp (.numT .natT) (.binE .addOp (.numT
     .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE (.varE "i_2") "%") 0))
     (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")))])) [])])

/-- `$isub_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:167`), as
`envOfScript` records it. -/
def isubDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))])), (.expP "iN"
    (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.varE "i_1")),
     (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.cvtE (.binE .modOp (.numT .intT) (.binE .subOp
     (.numT .intT) (.cvtE (.binE .addOp (.numT .natT) (.binE .powOp (.numT .natT) (.numE (.natN
     2)) (.varE "N")) (.projE (.uncaseE (.varE "i_1") "%") 0)) .natT .intT) (.cvtE (.projE
     (.uncaseE (.varE "i_2") "%") 0) .natT .intT)) (.cvtE (.binE .powOp (.numT .natT) (.numE
     (.natN 2)) (.varE "N")) .natT .intT)) .intT .natT)])) [])])

/-- `$imul_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:169`), as
`envOfScript` records it. -/
def imulDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))])), (.expP "iN"
    (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.varE "i_1")),
     (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.binE .modOp (.numT .natT) (.binE .mulOp (.numT
     .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE (.varE "i_2") "%") 0))
     (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")))])) [])])

/-- `$imin_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:183-186`), as
`envOfScript` records it. -/
def iminDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE
     []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.varE "i_1") [(.ifPr (.cmpE .leOp
     (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE (.varE "i_2") "%")
     0)))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])),
     (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U"
     (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.varE "i_2") [(.ifPr (.cmpE
     .gtOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE (.varE "i_2")
     "%") 0)))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE
     "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA
     (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.varE "i_1") [(.ifPr
     (.cmpE .leOp (.numT .intT) (.callE "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE
     (.varE "i_1") "%") 0))]) (.callE "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE
     (.varE "i_2") "%") 0))])))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN"
     [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE
     "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.varE
     "i_2") [.elsePr])])

/-- `$imax_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:188-191`), as
`envOfScript` records it. -/
def imaxDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE
     []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.varE "i_1") [(.ifPr (.cmpE .geOp
     (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE (.varE "i_2") "%")
     0)))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])),
     (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U"
     (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.varE "i_2") [(.ifPr (.cmpE
     .ltOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE (.varE "i_2")
     "%") 0)))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE
     "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA
     (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.varE "i_1") [(.ifPr
     (.cmpE .geOp (.numT .intT) (.callE "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE
     (.varE "i_1") "%") 0))]) (.callE "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE
     (.varE "i_2") "%") 0))])))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN"
     [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE
     "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.varE
     "i_2") [.elsePr])])

/-- `$iadd_sat_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:193-194`), as
`envOfScript` records it. -/
def iaddSatDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE
     []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "sat_u_"
     [(.expA (.varE "N")), (.expA (.cvtE (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE
     "i_1") "%") 0) (.projE (.uncaseE (.varE "i_2") "%") 0)) .natT .intT))])])) []), (.defD
     [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP "i_2"
     (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "S" (.tupE []))),
     (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "inv_signed_"
     [(.expA (.varE "N")), (.expA (.callE "sat_s_" [(.expA (.varE "N")), (.expA (.binE .addOp
     (.numT .intT) (.callE "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_1")
     "%") 0))]) (.callE "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_2")
     "%") 0))])))]))])])) [])])

/-- `$isub_sat_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:196-197`), as
`envOfScript` records it. -/
def isubSatDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "iN" [(.expA (.varE "N"))]),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE
     []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "sat_u_"
     [(.expA (.varE "N")), (.expA (.binE .subOp (.numT .intT) (.cvtE (.projE (.uncaseE (.varE
     "i_1") "%") 0) .natT .intT) (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT
     .intT)))])])) []), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA
     (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")),
     (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.caseE "%"
     (.tupE [(.callE "inv_signed_" [(.expA (.varE "N")), (.expA (.callE "sat_s_" [(.expA (.varE
     "N")), (.expA (.binE .subOp (.numT .intT) (.callE "signed_" [(.expA (.varE "N")), (.expA
     (.projE (.uncaseE (.varE "i_1") "%") 0))]) (.callE "signed_" [(.expA (.varE "N")), (.expA
     (.projE (.uncaseE (.varE "i_2") "%") 0))])))]))])])) [])])

/-- `$ieqz_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:218`), as
`envOfScript` records it. -/
def ieqzDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "u32" []),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.varE "i_1"))] (.caseE "%" (.tupE [(.callE "bool" [(.expA (.cmpE .eqOp
     .boolT (.projE (.uncaseE (.varE "i_1") "%") 0) (.numE (.natN 0))))])])) [])])

/-- `$inez_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:220`), as
`envOfScript` records it. -/
def inezDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "u32" []),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.varE "i_1"))] (.caseE "%" (.tupE [(.callE "bool" [(.expA (.cmpE .neOp
     .boolT (.projE (.uncaseE (.varE "i_1") "%") 0) (.numE (.natN 0))))])])) [])])

/-- `$ieq_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:223`), as
`envOfScript` records it. -/
def ieqDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))])), (.expP "iN"
    (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "u32" []),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.varE "i_1")),
     (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "bool" [(.expA (.cmpE .eqOp .boolT (.varE
     "i_1") (.varE "i_2")))])])) [])])

/-- `$ine_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:225`), as
`envOfScript` records it. -/
def ineDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))])), (.expP "iN"
    (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "u32" []),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.varE "i_1")),
     (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "bool" [(.expA (.cmpE .neOp .boolT (.varE
     "i_1") (.varE "i_2")))])])) [])])

/-- `$ilt_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:227-228`), as
`envOfScript` records it. -/
def iltDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "u32" []),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE
     []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "bool"
     [(.expA (.cmpE .ltOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE
     (.varE "i_2") "%") 0)))])])) []), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT
     "iN" [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))]
     (.caseE "%" (.tupE [(.callE "bool" [(.expA (.cmpE .ltOp (.numT .intT) (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_1") "%") 0))]) (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_2") "%") 0))])))])])) [])])

/-- `$igt_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:230-231`), as
`envOfScript` records it. -/
def igtDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "u32" []),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE
     []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "bool"
     [(.expA (.cmpE .gtOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE
     (.varE "i_2") "%") 0)))])])) []), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT
     "iN" [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))]
     (.caseE "%" (.tupE [(.callE "bool" [(.expA (.cmpE .gtOp (.numT .intT) (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_1") "%") 0))]) (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_2") "%") 0))])))])])) [])])

/-- `$ile_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:233-234`), as
`envOfScript` records it. -/
def ileDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "u32" []),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE
     []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "bool"
     [(.expA (.cmpE .leOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE
     (.varE "i_2") "%") 0)))])])) []), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT
     "iN" [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))]
     (.caseE "%" (.tupE [(.callE "bool" [(.expA (.cmpE .leOp (.numT .intT) (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_1") "%") 0))]) (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_2") "%") 0))])))])])) [])])

/-- `$ige_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:236-237`), as
`envOfScript` records it. -/
def igeDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.varT "u32" []),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE
     []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.caseE "%" (.tupE [(.callE "bool"
     [(.expA (.cmpE .geOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.projE (.uncaseE
     (.varE "i_2") "%") 0)))])])) []), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT
     "iN" [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))]
     (.caseE "%" (.tupE [(.callE "bool" [(.expA (.cmpE .geOp (.numT .intT) (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_1") "%") 0))]) (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_2") "%") 0))])))])])) [])])

/-- `$idiv_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:171-175`), as
`envOfScript` records it. -/
def idivDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.iterT (.varT "iN" [(.expA (.varE "N"))]) .opt),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.caseE "U" (.tupE []))), (.expA (.varE "i_1")), (.expA (.caseE "%"
     (.tupE [(.numE (.natN 0))])))] (.optE none) []), (.defD [(.expP "N" (.varT "N" [])), (.expP
     "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))]
     [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE
     "i_2"))] (.optE (some (.caseE "%" (.tupE [(.cvtE (.callE "truncz" [(.expA (.binE .divOp
     (.numT .ratT) (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT) (.cvtE (.projE
     (.uncaseE (.varE "i_2") "%") 0) .natT .ratT)))]) .intT .natT)])))) []), (.defD [(.expP "N"
     (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE "N")),
     (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.caseE "%" (.tupE [(.numE
     (.natN 0))])))] (.optE none) []), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT
     "iN" [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))]
     (.optE none) [(.ifPr (.cmpE .eqOp .boolT (.binE .divOp (.numT .ratT) (.cvtE (.callE "signed_"
     [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_1") "%") 0))]) .intT .ratT) (.cvtE
     (.callE "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_2") "%") 0))])
     .intT .ratT)) (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp
     (.numT .intT) (.cvtE (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT
     .natT)) .natT .ratT)))]), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN"
     [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE
     "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.optE
     (some (.caseE "%" (.tupE [(.callE "inv_signed_" [(.expA (.varE "N")), (.expA (.callE "truncz"
     [(.expA (.binE .divOp (.numT .ratT) (.cvtE (.callE "signed_" [(.expA (.varE "N")), (.expA
     (.projE (.uncaseE (.varE "i_1") "%") 0))]) .intT .ratT) (.cvtE (.callE "signed_" [(.expA
     (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_2") "%") 0))]) .intT .ratT)))]))])]))))
     [])])

/-- `$irem_` (`specification/wasm-3.0/3.1-numerics.scalar.spectec:177-181`), as
`envOfScript` records it. -/
def iremDef : List Param × Typ × List Clause :=
  ([(.expP "N" (.varT "N" [])), (.expP "sx" (.varT "sx" [])), (.expP "iN" (.varT "iN" [(.expA
    (.varE "N"))])), (.expP "iN" (.varT "iN" [(.expA (.varE "N"))]))],
   (.iterT (.varT "iN" [(.expA (.varE "N"))]) .opt),
   [(.defD [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA
     (.varE "N")), (.expA (.caseE "U" (.tupE []))), (.expA (.varE "i_1")), (.expA (.caseE "%"
     (.tupE [(.numE (.natN 0))])))] (.optE none) []), (.defD [(.expP "N" (.varT "N" [])), (.expP
     "i_1" (.varT "iN" [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))]))]
     [(.expA (.varE "N")), (.expA (.caseE "U" (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE
     "i_2"))] (.optE (some (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.projE
     (.uncaseE (.varE "i_1") "%") 0) .natT .intT) (.cvtE (.binE .mulOp (.numT .natT) (.projE
     (.uncaseE (.varE "i_2") "%") 0) (.cvtE (.callE "truncz" [(.expA (.binE .divOp (.numT .ratT)
     (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT) (.cvtE (.projE (.uncaseE (.varE
     "i_2") "%") 0) .natT .ratT)))]) .intT .natT)) .natT .intT)) .intT .natT)])))) []), (.defD
     [(.expP "N" (.varT "N" [])), (.expP "i_1" (.varT "iN" [(.expA (.varE "N"))]))] [(.expA (.varE
     "N")), (.expA (.caseE "S" (.tupE []))), (.expA (.varE "i_1")), (.expA (.caseE "%" (.tupE
     [(.numE (.natN 0))])))] (.optE none) []), (.defD [(.expP "N" (.varT "N" [])), (.expP "i_1"
     (.varT "iN" [(.expA (.varE "N"))])), (.expP "i_2" (.varT "iN" [(.expA (.varE "N"))])), (.expP
     "j_1" (.numT .intT)), (.expP "j_2" (.numT .intT))] [(.expA (.varE "N")), (.expA (.caseE "S"
     (.tupE []))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.optE (some (.caseE "%" (.tupE
     [(.callE "inv_signed_" [(.expA (.varE "N")), (.expA (.binE .subOp (.numT .intT) (.varE "j_1")
     (.binE .mulOp (.numT .intT) (.varE "j_2") (.callE "truncz" [(.expA (.binE .divOp (.numT
     .ratT) (.cvtE (.varE "j_1") .intT .ratT) (.cvtE (.varE "j_2") .intT .ratT)))]))))])]))))
     [(.ifPr (.binE .andOp .boolT (.cmpE .eqOp .boolT (.varE "j_1") (.callE "signed_" [(.expA
     (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_1") "%") 0))])) (.cmpE .eqOp .boolT (.varE
     "j_2") (.callE "signed_" [(.expA (.varE "N")), (.expA (.projE (.uncaseE (.varE "i_2") "%")
     0))]))))])])

/-- An environment that interprets the wasm-3.0 numerics group exactly as the
pinned specification does. -/
structure NumEnv (env : Env) : Prop where
  /-- `$bool`. -/
  boolD : env.findDef? "bool" = some boolDef
  /-- `$signed_`. -/
  signedD : env.findDef? "signed_" = some signedDef
  /-- `$inv_signed_`. -/
  invSignedD : env.findDef? "inv_signed_" = some invSignedDef
  /-- `$sat_u_`. -/
  satUD : env.findDef? "sat_u_" = some satUDef
  /-- `$sat_s_`. -/
  satSD : env.findDef? "sat_s_" = some satSDef
  /-- `$ineg_`. -/
  inegD : env.findDef? "ineg_" = some inegDef
  /-- `$iabs_`. -/
  iabsD : env.findDef? "iabs_" = some iabsDef
  /-- `$iextend_`. -/
  iextendD : env.findDef? "iextend_" = some iextendDef
  /-- `$iadd_`. -/
  iaddD : env.findDef? "iadd_" = some iaddDef
  /-- `$isub_`. -/
  isubD : env.findDef? "isub_" = some isubDef
  /-- `$imul_`. -/
  imulD : env.findDef? "imul_" = some imulDef
  /-- `$imin_`. -/
  iminD : env.findDef? "imin_" = some iminDef
  /-- `$imax_`. -/
  imaxD : env.findDef? "imax_" = some imaxDef
  /-- `$iadd_sat_`. -/
  iaddSatD : env.findDef? "iadd_sat_" = some iaddSatDef
  /-- `$isub_sat_`. -/
  isubSatD : env.findDef? "isub_sat_" = some isubSatDef
  /-- `$ieqz_`. -/
  ieqzD : env.findDef? "ieqz_" = some ieqzDef
  /-- `$inez_`. -/
  inezD : env.findDef? "inez_" = some inezDef
  /-- `$ieq_`. -/
  ieqD : env.findDef? "ieq_" = some ieqDef
  /-- `$ine_`. -/
  ineD : env.findDef? "ine_" = some ineDef
  /-- `$ilt_`. -/
  iltD : env.findDef? "ilt_" = some iltDef
  /-- `$igt_`. -/
  igtD : env.findDef? "igt_" = some igtDef
  /-- `$ile_`. -/
  ileD : env.findDef? "ile_" = some ileDef
  /-- `$ige_`. -/
  igeD : env.findDef? "ige_" = some igeDef
  /-- `$idiv_`. -/
  idivD : env.findDef? "idiv_" = some idivDef
  /-- `$irem_`. -/
  iremD : env.findDef? "irem_" = some iremDef

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 2000000 in
/-- The pinned wasm-3.0 specification is such an environment.

This is the one statement in this file the kernel has to *compute*: it unfolds
all 976 top-level definitions of `Specs.wasm30` into the four declaration maps
of `envOfScript` and looks each of the 25 names up. -/
theorem numEnv_wasm30 : NumEnv (envOfScript Specs.wasm30) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Evaluating the shapes the numerics clauses use -/

/-- Reading the payload out of a `uN(N)` value held in a variable: the IL
spells it `i!%.0`. -/
theorem evalExp_uNV_payload {env : Env} {ρ : VarEnv} {x : IL.Id} {N : Nat} {i : BitVec N}
    (h : ρ.findVal? x = some (bvV i)) :
    EvalExp env ρ (.projE (.uncaseE (.varE x) "%") 0) (natV i.toNat) :=
  evalExp_projE_iff.2 ⟨[natV i.toNat], evalExp_uncaseE_iff.2 (evalExp_var h),
    Int.le_refl 0, rfl⟩

/-- Building a one-component injection, which is how every `uN(N)` result is
written. -/
theorem evalExp_case_tup_one {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {v : Value}
    (h : EvalExp env ρ e v) : EvalExp env ρ (.caseE op (.tupE [e])) (.case op (.tuple [v])) :=
  evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[v], evalExps_cons h evalExps_nil, rfl⟩, rfl⟩

/-- `cvt nat int`, which is total. -/
theorem evalExp_toInt {env : Env} {ρ : VarEnv} {e : Exp} {n : Nat}
    (h : EvalExp env ρ e (natV n)) : EvalExp env ρ (.cvtE e .natT .intT) (intV (n : Int)) :=
  evalExp_cvtNum h rfl

/-- `cvt int nat`, which `Xl.Num.cvt` defines only on a non-negative integer. -/
theorem evalExp_toNat {env : Env} {ρ : VarEnv} {e : Exp} {j : Int} (hj : 0 ≤ j)
    (h : EvalExp env ρ e (intV j)) : EvalExp env ρ (.cvtE e .intT .natT) (natV j.toNat) :=
  evalExp_cvtNum h (by simp [Num.cvt, hj])

/-- A natural literal, bridged. -/
theorem evalExp_natLit {env : Env} {ρ : VarEnv} (n : Nat) :
    EvalExp env ρ (.numE (.natN n)) (natV n) := evalExp_num

/-- The literal `1`, coerced into `int`. -/
theorem evalExp_oneInt {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.cvtE (.numE (.natN 1)) .natT .intT) (intV 1) := evalExp_toInt evalExp_num

/-- The literal `0`, coerced into `int`. -/
theorem evalExp_zeroInt {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.cvtE (.numE (.natN 0)) .natT .intT) (intV 0) := evalExp_toInt evalExp_num

/-- The IL's `2 ^ N`. -/
theorem evalExp_twoPow {env : Env} {ρ : VarEnv} {x : IL.Id} {N : Nat}
    (h : ρ.findVal? x = some (natV N)) :
    EvalExp env ρ (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE x)) (natV (2 ^ N)) :=
  evalExp_binNum evalExp_num (evalExp_var h) rfl

/-- The IL's `2 ^ (N - 1)`.  The elaborated form subtracts in `int` and
converts the result back to `nat`, so it is *stuck* at `N = 0`: `Xl.Num.cvt`
sends `-1` to nothing.  Hence the `0 < N` hypothesis that every theorem below
mentioning `signed_` carries. -/
theorem evalExp_twoPowPred {env : Env} {ρ : VarEnv} {x : IL.Id} {N : Nat} (hN : 0 < N)
    (h : ρ.findVal? x = some (natV N)) :
    EvalExp env ρ (.binE .powOp (.numT .natT) (.numE (.natN 2))
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE x) .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)) (natV (2 ^ (N - 1))) := by
  have hsub : EvalExp env ρ (.binE .subOp (.numT .intT) (.cvtE (.varE x) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (intV ((N : Int) - 1)) :=
    evalExp_binNum (evalExp_toInt (evalExp_var h)) evalExp_oneInt rfl
  have hnat := evalExp_toNat (show (0 : Int) ≤ (N : Int) - 1 by omega) hsub
  rw [show ((N : Int) - 1).toNat = N - 1 by omega] at hnat
  exact evalExp_binNum evalExp_num hnat rfl

/-- The empty argument list. -/
theorem evalArgs_nil {env : Env} {ρ : VarEnv} : EvalArgs env ρ [] [] :=
  ⟨1, by simp only [evalArgs, List.mapM_nil]; rfl⟩

/-- An expression argument, evaluated. -/
theorem evalArgs_cons {env : Env} {ρ : VarEnv} {e : Exp} {as : List Arg} {v : Value}
    {ws : List ArgV} (h : EvalExp env ρ e v) (hs : EvalArgs env ρ as ws) :
    EvalArgs env ρ (.expA e :: as) (.val v :: ws) := by
  obtain ⟨n₁, h⟩ := h
  obtain ⟨n₂, hs⟩ := hs
  refine ⟨max n₁ n₂ + 2, ?_⟩
  have e1 : evalArg (max n₁ n₂ + 1) env ρ (.expA e) = .ok (.val v) := by
    simp only [evalArg, evalExp_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) h,
      Functor.map, Except.map]
  have e2 : as.mapM (evalArg (max n₁ n₂ + 1) env ρ) = .ok ws := by
    have := evalArgs_ok_of_le (m := n₂) (n := max n₁ n₂ + 2) (by omega) hs
    simpa only [evalArgs] using this
  simp only [evalArgs, List.mapM_cons, e1, e2, Bind.bind, Except.bind]
  rfl

/-- The `u32` truth value a test or comparison returns. -/
theorem uNV_u32OfBool (b : Bool) :
    bvV (Wasm.Numerics.u32OfBool b) = .case "%" (.tuple [natV (Wasm.Numerics.bool_ b)]) := by
  cases b <;> rfl

/-- A local scope binds no `DefP` parameters, so a call inside a clause body
resolves to the global definition. -/
theorem findDef?_empty {x : IL.Id} : VarEnv.empty.findDef? x = none := rfl

/-! ## Agreement: the helper functions -/

/-- `Xl.Num`'s truncating `\` on two non-negative integers is `Nat`'s `%`
(`spectec/src/xl/num.ml:160-161`). -/
theorem tmod_natCast (a b : Nat) : (a : Int).tmod (b : Int) = ((a % b : Nat) : Int) := rfl

/-- **`$bool`** agrees with `Numerics.bool_`. -/
theorem callDef_bool {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "bool" = none) {args : List Arg} {b : Bool}
    (ha : EvalArgs env ρ args [.val (.bool b)]) :
    CallDef env ρ "bool" args (natV (Wasm.Numerics.bool_ b)) := by
  refine callDef_of_tryClauses hρ h.boolD ha ?_
  have hit : ∀ c : Bool, TryClauses env [.defD [] [.expA (.boolE c)]
      (.numE (.natN (Wasm.Numerics.bool_ c))) []] [.val (.bool c)]
      (natV (Wasm.Numerics.bool_ c)) := fun c =>
    tryClauses_hit (matchArgs_cons (matchArg_expA matchExp_boolE) matchArgs_nil)
      premsHold_nil evalExp_num
  cases b
  · exact tryClauses_hit (matchArgs_cons (matchArg_expA matchExp_boolE) matchArgs_nil)
      premsHold_nil evalExp_num
  · exact tryClauses_skip_match
      (matchArgs_cons_undef (matchArg_expA_undef
        (matchExp_boolE_undef (b := false) (v := .bool true) (by simp))))
      (hit true)

/-- `$bool` applied to a comparison, the shape every test and relation uses. -/
theorem evalExp_boolCall {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "bool" = none) {e : Exp} {b : Bool} (he : EvalExp env ρ e (.bool b)) :
    EvalExp env ρ (.callE "bool" [.expA e]) (natV (Wasm.Numerics.bool_ b)) :=
  evalExp_callE_iff.2 (callDef_bool h hρ (evalArgs_cons he evalArgs_nil))

/-- **`$signed_`** agrees with `Numerics.signed_` on the whole domain the IL
definition covers: `0 < N` (below which `2^(N-1)` is stuck) and `i < 2^N`
(outside which no clause applies). -/
theorem callDef_signed {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "signed_" = none) {args : List Arg} {N i : Nat}
    (ha : EvalArgs env ρ args [.val (natV N), .val (natV i)]) (hN : 0 < N)
    (hi : i < 2 ^ N) : CallDef env ρ "signed_" args (intV (Wasm.Numerics.signed_ N i)) := by
  refine callDef_of_tryClauses hρ h.signedD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (natV i) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (natV i) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (natV i)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hpow := evalExp_twoPowPred (env := env) hN hNv
  by_cases hlt : i < 2 ^ (N - 1)
  · refine tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .natT) (evalExp_var hiv) hpow (by simp [Num.cmp, hlt]))) ?_
    have := evalExp_toInt (env := env) (evalExp_var hiv)
    simpa [Wasm.Numerics.signed_, hlt] using this
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .natT) (evalExp_var hiv) hpow (by simp [Num.cmp, hlt]))) ?_
    refine tryClauses_hit hmatch (premsHold_ifPr ?_) ?_
    · exact evalExp_and (b₁ := true) (b₂ := true)
        (evalExp_cmpNum (op := .leOp) (t := .numT .natT) hpow (evalExp_var hiv)
          (by simp [Num.cmp]; omega))
        (evalExp_cmpNum (op := .ltOp) (t := .numT .natT) (evalExp_var hiv)
          (evalExp_twoPow hNv) (by simp [Num.cmp, hi]))
    · have := evalExp_binNum (env := env) (op := .subOp) (t := .numT .intT)
        (evalExp_toInt (evalExp_var hiv)) (evalExp_toInt (evalExp_twoPow hNv)) rfl
      simpa [Wasm.Numerics.signed_, hlt, intV] using this

/-- **`$inv_signed_`** agrees with `Numerics.invSigned_` on the IL definition's
domain, `-2^(N-1) ≤ j < 2^(N-1)`. -/
theorem callDef_invSigned {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "inv_signed_" = none) {args : List Arg} {N : Nat} {j : Int}
    (ha : EvalArgs env ρ args [.val (natV N), .val (intV j)]) (hN : 0 < N)
    (h₁ : -2 ^ (N - 1) ≤ j) (h₂ : j < 2 ^ (N - 1)) :
    CallDef env ρ "inv_signed_" args (natV (Wasm.Numerics.invSigned_ N j)) := by
  refine callDef_of_tryClauses hρ h.invSignedD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (intV j) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (intV j) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (intV j)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hpow : EvalExp env σ _ (intV ((2 ^ (N - 1) : Nat) : Int)) :=
    evalExp_toInt (evalExp_twoPowPred hN hNv)
  have hcast : (((2 ^ (N - 1) : Nat)) : Int) = 2 ^ (N - 1) := by push_cast; rfl
  have hpp : (2 : Int) ^ (N - 1) ≤ 2 ^ N := by
    have : (2 : Nat) ^ (N - 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast this
  rw [hcast] at hpow
  by_cases hneg : 0 ≤ j
  · refine tryClauses_hit hmatch (premsHold_ifPr ?_) ?_
    · exact evalExp_and (b₁ := true) (b₂ := true)
        (evalExp_cmpNum (op := .leOp) (t := .numT .intT) evalExp_zeroInt
          (evalExp_var hiv) (by simp [Num.cmp]; omega))
        (evalExp_cmpNum (op := .ltOp) (t := .numT .intT) (evalExp_var hiv) hpow
          (by simp [Num.cmp, h₂]))
    · have := evalExp_toNat (env := env) hneg (evalExp_var hiv)
      rwa [Wasm.Numerics.invSigned_of_nonneg hneg h₂]
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr ?_) ?_
    · exact evalExp_and (b₁ := false) (b₂ := true)
        (evalExp_cmpNum (op := .leOp) (t := .numT .intT) evalExp_zeroInt
          (evalExp_var hiv) (by simp [Num.cmp]; omega))
        (evalExp_cmpNum (op := .ltOp) (t := .numT .intT) (evalExp_var hiv) hpow
          (by simp [Num.cmp, h₂]))
    refine tryClauses_hit hmatch (premsHold_ifPr ?_) ?_
    · refine evalExp_and (b₁ := true) (b₂ := true) ?_
        (evalExp_cmpNum (op := .ltOp) (t := .numT .intT) (evalExp_var hiv)
          evalExp_zeroInt (by simp [Num.cmp]; omega))
      exact evalExp_cmpNum (op := .leOp) (t := .numT .intT)
        (evalExp_unNum hpow rfl) (evalExp_var hiv) (by simp [Num.cmp]; omega)
    · have hsum := evalExp_binNum (env := env) (op := .addOp) (t := .numT .intT)
        (evalExp_var hiv) (evalExp_toInt (evalExp_twoPow hNv)) rfl
      have hnn : (0 : Int) ≤ j + ((2 ^ N : Nat) : Int) := by push_cast; omega
      have := evalExp_toNat (env := env) hnn hsum
      rw [Wasm.Numerics.invSigned_of_neg (by omega) (by omega)]
      convert this using 3
      push_cast
      rfl

/-! ## Agreement: the integer arithmetic of `$iadd_` … `$iabs_`

Each theorem says: calling the pinned IL definition on the bridged arguments
denotes the bridge of what `Silmaril/Wasm/Numerics/IntegerN.lean` computes.
`IntegerN.Agreement` then carries that across to `BitVec` and to
`Numerics.intBinOp`. -/

/-- `uN(N)` of a wrapped natural. -/
theorem uNV_ofNat (N k : Nat) :
    bvV (BitVec.ofNat N k) = .case "%" (.tuple [natV (k % 2 ^ N)]) := by
  simp [bvV, natV]

/-- The IL's `\` at type `nat`. -/
theorem evalExp_wrapNat {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : EvalExp env ρ e₁ (natV a)) (h₂ : EvalExp env ρ e₂ (natV b)) (hb : b ≠ 0) :
    EvalExp env ρ (.binE .modOp (.numT .natT) e₁ e₂) (natV (a % b)) :=
  evalExp_binNum h₁ h₂ (by simp [Num.bin, hb])

/-- The IL's `\` at type `int`, on two operands that came from `nat`.  `Z.rem`
truncates towards zero (`spectec/src/xl/num.ml:160-161`), which on
non-negative operands is `Nat`'s `%`. -/
theorem evalExp_wrapInt {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : EvalExp env ρ e₁ (intV (a : Int))) (h₂ : EvalExp env ρ e₂ (intV (b : Int)))
    (hb : b ≠ 0) :
    EvalExp env ρ (.cvtE (.binE .modOp (.numT .intT) e₁ e₂) .intT .natT)
      (natV (a % b)) := by
  have hm : EvalExp env ρ (.binE .modOp (.numT .intT) e₁ e₂) (intV ((a % b : Nat) : Int)) :=
    evalExp_binNum h₁ h₂ (by
      simp only [Num.bin, tmod_natCast]
      simp [hb])
  have h0 := evalExp_toNat
    (show (0 : Int) ≤ ((a % b : Nat) : Int) from Int.natCast_nonneg _) hm
  rwa [Int.toNat_natCast] at h0

/-- **`$iadd_`** agrees with `Numerics.iadd_`. -/
theorem callDef_iadd {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "iadd_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "iadd_" args (bvV (Wasm.Numerics.iadd_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.iaddD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hadd := evalExp_binNum (env := env) (op := .addOp) (t := .numT .natT)
      (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl
    have hc := evalExp_case_tup_one (op := "%")
      (evalExp_wrapNat hadd (evalExp_twoPow hNv) (Nat.two_pow_pos N).ne')
    simpa [bvV, natV, Wasm.Numerics.iadd_, Nat.mod_mod_of_dvd] using hc

/-- **`$imul_`** agrees with `Numerics.imul_`. -/
theorem callDef_imul {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "imul_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "imul_" args (bvV (Wasm.Numerics.imul_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.imulD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hmul := evalExp_binNum (env := env) (op := .mulOp) (t := .numT .natT)
      (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl
    have hc := evalExp_case_tup_one (op := "%")
      (evalExp_wrapNat hmul (evalExp_twoPow hNv) (Nat.two_pow_pos N).ne')
    simpa [bvV, natV, Wasm.Numerics.imul_, Nat.mod_mod_of_dvd] using hc

/-- **`$isub_`** agrees with `Numerics.isub_`.  The IL adds `2^N` before
subtracting, in `int`, and converts back; the Lean transcription subtracts in
`Nat`, where the same bias keeps the result non-negative. -/
theorem callDef_isub {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "isub_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "isub_" args (bvV (Wasm.Numerics.isub_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.isubD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hlt := i₂.isLt
    have hbias := evalExp_binNum (env := env) (op := .addOp) (t := .numT .natT)
      (evalExp_twoPow hNv) (evalExp_uNV_payload h1) rfl
    have hdiff := evalExp_binNum (env := env) (op := .subOp) (t := .numT .intT)
      (evalExp_toInt hbias) (evalExp_toInt (evalExp_uNV_payload h2)) rfl
    rw [show ((2 ^ N + i₁.toNat : Nat) : Int) - ((i₂.toNat : Nat) : Int)
        = ((2 ^ N + i₁.toNat - i₂.toNat : Nat) : Int) by omega] at hdiff
    have hc := evalExp_case_tup_one (op := "%")
      (evalExp_wrapInt hdiff (evalExp_toInt (evalExp_twoPow hNv))
        (Nat.two_pow_pos N).ne')
    simpa [bvV, natV, Wasm.Numerics.isub_, Nat.mod_mod_of_dvd] using hc

/-- **`$ineg_`** agrees with `Numerics.ineg_`. -/
theorem callDef_ineg {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "ineg_" = none) {args : List Arg} {N : Nat} {i : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i)]) :
    CallDef env ρ "ineg_" args (bvV (Wasm.Numerics.ineg_ N i)) := by
  refine callDef_of_tryClauses hρ h.inegD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i) := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  · have hlt := i.isLt
    have hdiff := evalExp_binNum (env := env) (op := .subOp) (t := .numT .intT)
      (evalExp_toInt (evalExp_twoPow hNv)) (evalExp_toInt (evalExp_uNV_payload h1)) rfl
    rw [show ((2 ^ N : Nat) : Int) - ((i.toNat : Nat) : Int)
        = ((2 ^ N - i.toNat : Nat) : Int) by omega] at hdiff
    have hc := evalExp_case_tup_one (op := "%")
      (evalExp_wrapInt hdiff (evalExp_toInt (evalExp_twoPow hNv))
        (Nat.two_pow_pos N).ne')
    simpa [bvV, natV, Wasm.Numerics.ineg_, Nat.mod_mod_of_dvd] using hc

/-- **`$iabs_`** agrees with `Numerics.iabs_`. -/
theorem callDef_iabs {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "iabs_" = none) {args : List Arg} {N : Nat} {i : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i)]) (hN : 0 < N) :
    CallDef env ρ "iabs_" args (bvV (Wasm.Numerics.iabs_ N i)) := by
  refine callDef_of_tryClauses hρ h.iabsD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i) := by rw [hσ]; rfl
  have hdefs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hdefn : σ.findDef? "ineg_" = none := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i_1")] [.val (natV N), .val (bvV i)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hsig : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
      .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
      (intV (Wasm.Numerics.signed_ N i.toNat)) :=
    evalExp_callE_iff.2 (callDef_signed h hdefs
      (evalArgs_cons (evalExp_var hNv)
        (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i.isLt)
  by_cases hge : Wasm.Numerics.signed_ N i.toNat ≥ 0
  · refine tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .geOp)
      (t := .numT .intT) hsig evalExp_zeroInt (by simp [Num.cmp]; omega))) ?_
    have := evalExp_var (env := env) h1
    simpa [Wasm.Numerics.iabs_, hge] using this
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .geOp)
      (t := .numT .intT) hsig evalExp_zeroInt (by simp [Num.cmp]; omega))) ?_
    refine tryClauses_hit hmatch premsHold_elsePr ?_
    have := evalExp_callE_iff.2 (callDef_ineg (env := env) (ρ := σ) h hdefn
      (evalArgs_cons (evalExp_var hNv) (evalArgs_cons (evalExp_var h1) evalArgs_nil)))
    simpa [Wasm.Numerics.iabs_, hge] using this

/-! ## Agreement: the tests and relations

`$ieqz_` … `$ige_` all have the shape `%( $bool(c) )`, so they bridge to
`Numerics.u32OfBool` of the same condition.  The signed cases call `$signed_`,
and inherit its `0 < N` hypothesis. -/

/-- Equality of bridged naturals is equality of the naturals. -/
theorem natV_beq (a b : Nat) : (natV a == natV b) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab; simp
  · simp only [natV, hab, decide_false]
    exact beq_eq_false_iff_ne.2 (by simp [hab])

/-- Equality of bridged `uN(N)` values is equality of the bit patterns. -/
theorem uNV_beq {N : Nat} (i₁ i₂ : BitVec N) : (bvV i₁ == bvV i₂) = decide (i₁ = i₂) := by
  by_cases hab : i₁ = i₂
  · subst hab; simp
  · simp only [hab, decide_false]
    refine beq_eq_false_iff_ne.2 ?_
    simp only [bvV, natV, ne_eq, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.num.injEq, Num.natN.injEq, and_true, true_and]
    intro hc
    exact absurd (BitVec.eq_of_toNat_eq hc) hab

/-- The body shape `%( $bool(c) )` that every test and relation returns. -/
theorem evalExp_boolResult {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "bool" = none) {e : Exp} {b : Bool} (he : EvalExp env ρ e (.bool b)) :
    EvalExp env ρ (.caseE "%" (.tupE [.callE "bool" [.expA e]]))
      (bvV (Wasm.Numerics.u32OfBool b)) := by
  rw [uNV_u32OfBool]
  exact evalExp_case_tup_one (evalExp_boolCall h hρ he)

/-- **`$ieqz_`** agrees with `Numerics.ieqz_`. -/
theorem callDef_ieqz {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "ieqz_" = none) {args : List Arg} {N : Nat} {i : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i)]) :
    CallDef env ρ "ieqz_" args (bvV (Wasm.Numerics.ieqz_ N i)) := by
  refine callDef_of_tryClauses hρ h.ieqzD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i) with hσ
  have h1 : σ.findVal? "i_1" = some (bvV i) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  · have hc := evalExp_eq (env := env) (t := .boolT) (evalExp_uNV_payload h1)
      (evalExp_natLit 0)
    rw [show (natV i.toNat == natV 0) = decide (i.toNat = 0) from natV_beq _ _] at hc
    exact evalExp_boolResult h hb hc

/-- **`$inez_`** agrees with `Numerics.inez_`. -/
theorem callDef_inez {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "inez_" = none) {args : List Arg} {N : Nat} {i : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i)]) :
    CallDef env ρ "inez_" args (bvV (Wasm.Numerics.inez_ N i)) := by
  refine callDef_of_tryClauses hρ h.inezD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i) with hσ
  have h1 : σ.findVal? "i_1" = some (bvV i) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  · have hc := evalExp_ne (env := env) (t := .boolT) (evalExp_uNV_payload h1)
      (evalExp_natLit 0)
    rw [show (!(natV i.toNat == natV 0)) = decide (i.toNat ≠ 0) by
      rw [natV_beq]; simp] at hc
    exact evalExp_boolResult h hb hc

/-- **`$ieq_`** agrees with `Numerics.ieq_`. -/
theorem callDef_ieq {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "ieq_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "ieq_" args (bvV (Wasm.Numerics.ieq_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.ieqD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hc := evalExp_eq (env := env) (t := .boolT) (evalExp_var h1) (evalExp_var h2)
    rw [show (bvV i₁ == bvV i₂) = decide (i₁ = i₂) from uNV_beq _ _] at hc
    exact evalExp_boolResult h hb hc

/-- **`$ine_`** agrees with `Numerics.ine_`. -/
theorem callDef_ine {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "ine_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "ine_" args (bvV (Wasm.Numerics.ine_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.ineD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hc := evalExp_ne (env := env) (t := .boolT) (evalExp_var h1) (evalExp_var h2)
    rw [show (!(bvV i₁ == bvV i₂)) = decide (i₁ ≠ i₂) by rw [uNV_beq]; simp] at hc
    exact evalExp_boolResult h hb hc

/-! ## Agreement: the ordered relations -/


/-- **`$ilt_`** agrees with `Numerics.ilt_`.  The `0 < N` hypothesis is
needed only by the signed clause, which calls `$signed_`. -/
theorem callDef_ilt {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "ilt_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "ilt_" args (bvV (Wasm.Numerics.ilt_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.iltD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      exact tryClauses_hit (hmatch "U") premsHold_nil
        (evalExp_boolResult h hb (evalExp_cmpNum (op := .ltOp) (t := .numT .natT)
          (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl))
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons_undef (matchArg_expA_undef
          (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      exact evalExp_boolResult h hb (evalExp_cmpNum (op := .ltOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl)


/-- **`$igt_`** agrees with `Numerics.igt_`.  The `0 < N` hypothesis is
needed only by the signed clause, which calls `$signed_`. -/
theorem callDef_igt {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "igt_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "igt_" args (bvV (Wasm.Numerics.igt_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.igtD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      exact tryClauses_hit (hmatch "U") premsHold_nil
        (evalExp_boolResult h hb (evalExp_cmpNum (op := .gtOp) (t := .numT .natT)
          (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl))
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons_undef (matchArg_expA_undef
          (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      exact evalExp_boolResult h hb (evalExp_cmpNum (op := .gtOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl)


/-- **`$ile_`** agrees with `Numerics.ile_`.  The `0 < N` hypothesis is
needed only by the signed clause, which calls `$signed_`. -/
theorem callDef_ile {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "ile_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "ile_" args (bvV (Wasm.Numerics.ile_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.ileD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      exact tryClauses_hit (hmatch "U") premsHold_nil
        (evalExp_boolResult h hb (evalExp_cmpNum (op := .leOp) (t := .numT .natT)
          (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl))
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons_undef (matchArg_expA_undef
          (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      exact evalExp_boolResult h hb (evalExp_cmpNum (op := .leOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl)


/-- **`$ige_`** agrees with `Numerics.ige_`.  The `0 < N` hypothesis is
needed only by the signed clause, which calls `$signed_`. -/
theorem callDef_ige {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "ige_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "ige_" args (bvV (Wasm.Numerics.ige_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.igeD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      exact tryClauses_hit (hmatch "U") premsHold_nil
        (evalExp_boolResult h hb (evalExp_cmpNum (op := .geOp) (t := .numT .natT)
          (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl))
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons_undef (matchArg_expA_undef
          (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      exact evalExp_boolResult h hb (evalExp_cmpNum (op := .geOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl)

/-! ## Agreement: the minima and maxima -/


/-- **`$imin_`** agrees with `Numerics.imin_`.  The `0 < N` hypothesis is
needed only by the signed clauses, which call `$signed_`. -/
theorem callDef_imin {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "imin_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "imin_" args (bvV (Wasm.Numerics.imin_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.iminD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  have hskip : ∀ a b : MixopS, a ≠ b → MatchArgsUndef env VarEnv.empty
        [Arg.expA (.varE "N"), .expA (.caseE b (.tupE [])), .expA (.varE "i_1"),
          .expA (.varE "i_2")]
        [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] := by
    intro a b hab
    exact matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hab)))
  cases sx with
  | unsigned =>
      by_cases hle : i₁.toNat ≤ i₂.toNat
      · exact tryClauses_hit (hmatch "U")
          (premsHold_ifPr (evalExp_cmpNum (op := .leOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) (by simp [Num.cmp, hle])))
          (by simpa [Wasm.Numerics.imin_, hle] using evalExp_var (env := env) h1)
      · refine tryClauses_skip_prem (hmatch "U")
          (premsUndef_ifPr (evalExp_cmpNum (op := .leOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2)
            (by simp [Num.cmp, hle]))) ?_
        exact tryClauses_hit (hmatch "U")
          (premsHold_ifPr (evalExp_cmpNum (op := .gtOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2)
            (by simp [Num.cmp]; omega)))
          (by simpa [Wasm.Numerics.imin_, hle] using evalExp_var (env := env) h2)
  | signed =>
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      refine tryClauses_skip_match (hskip "S" "U" (by decide)) ?_
      refine tryClauses_skip_match (hskip "S" "U" (by decide)) ?_
      by_cases hle : Wasm.Numerics.signed_ N i₁.toNat ≤ Wasm.Numerics.signed_ N i₂.toNat
      · exact tryClauses_hit (hmatch "S")
          (premsHold_ifPr (evalExp_cmpNum (op := .leOp) (t := .numT .intT)
            hsig₁ hsig₂ (by simp [Num.cmp]; omega)))
          (by simpa [Wasm.Numerics.imin_, hle] using evalExp_var (env := env) h1)
      · refine tryClauses_skip_prem (hmatch "S")
          (premsUndef_ifPr (evalExp_cmpNum (op := .leOp) (t := .numT .intT)
            hsig₁ hsig₂ (by simp [Num.cmp]; omega))) ?_
        exact tryClauses_hit (hmatch "S") premsHold_elsePr
          (by simpa [Wasm.Numerics.imin_, hle] using evalExp_var (env := env) h2)


/-- **`$imax_`** agrees with `Numerics.imax_`.  The `0 < N` hypothesis is
needed only by the signed clauses, which call `$signed_`. -/
theorem callDef_imax {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "imax_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "imax_" args (bvV (Wasm.Numerics.imax_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.imaxD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  have hskip : ∀ a b : MixopS, a ≠ b → MatchArgsUndef env VarEnv.empty
        [Arg.expA (.varE "N"), .expA (.caseE b (.tupE [])), .expA (.varE "i_1"),
          .expA (.varE "i_2")]
        [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] := by
    intro a b hab
    exact matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hab)))
  cases sx with
  | unsigned =>
      by_cases hle : i₁.toNat ≥ i₂.toNat
      · exact tryClauses_hit (hmatch "U")
          (premsHold_ifPr (evalExp_cmpNum (op := .geOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) (by simp [Num.cmp, hle])))
          (by simpa [Wasm.Numerics.imax_, hle] using evalExp_var (env := env) h1)
      · refine tryClauses_skip_prem (hmatch "U")
          (premsUndef_ifPr (evalExp_cmpNum (op := .geOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2)
            (by simp [Num.cmp, hle]))) ?_
        exact tryClauses_hit (hmatch "U")
          (premsHold_ifPr (evalExp_cmpNum (op := .ltOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2)
            (by simp [Num.cmp]; omega)))
          (by simpa [Wasm.Numerics.imax_, hle] using evalExp_var (env := env) h2)
  | signed =>
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      refine tryClauses_skip_match (hskip "S" "U" (by decide)) ?_
      refine tryClauses_skip_match (hskip "S" "U" (by decide)) ?_
      by_cases hle : Wasm.Numerics.signed_ N i₁.toNat ≥ Wasm.Numerics.signed_ N i₂.toNat
      · exact tryClauses_hit (hmatch "S")
          (premsHold_ifPr (evalExp_cmpNum (op := .geOp) (t := .numT .intT)
            hsig₁ hsig₂ (by simp [Num.cmp]; omega)))
          (by simpa [Wasm.Numerics.imax_, hle] using evalExp_var (env := env) h1)
      · refine tryClauses_skip_prem (hmatch "S")
          (premsUndef_ifPr (evalExp_cmpNum (op := .geOp) (t := .numT .intT)
            hsig₁ hsig₂ (by simp [Num.cmp]; omega))) ?_
        exact tryClauses_hit (hmatch "S") premsHold_elsePr
          (by simpa [Wasm.Numerics.imax_, hle] using evalExp_var (env := env) h2)

/-! ## Agreement: sign extension within a width -/

/-- `$signed_` lands in the two's-complement range of its own width. -/
theorem signed_bounds {K m : Nat} (hK : 0 < K) (hm : m < 2 ^ K) :
    -2 ^ (K - 1) ≤ Wasm.Numerics.signed_ K m ∧ Wasm.Numerics.signed_ K m < 2 ^ (K - 1) := by
  have hs : (2 : Nat) ^ K = 2 ^ (K - 1) * 2 := by
    conv_lhs => rw [show K = (K - 1) + 1 from (Nat.succ_pred_eq_of_pos hK).symm]
    exact Nat.pow_succ 2 (K - 1)
  have hsI : (2 : Int) ^ K = 2 ^ (K - 1) * 2 := by exact_mod_cast hs
  have hmI : (m : Int) < 2 ^ K := by exact_mod_cast hm
  unfold Wasm.Numerics.signed_
  split <;> rename_i hc
  · have : (m : Int) < 2 ^ (K - 1) := by exact_mod_cast hc
    omega
  · have : ¬ (m : Int) < 2 ^ (K - 1) := by
      intro hlt; exact hc (by exact_mod_cast hlt)
    omega

/-- `$inv_signed_` lands in `uN(N)`. -/
theorem invSigned_lt (N : Nat) (j : Int) : Wasm.Numerics.invSigned_ N j < 2 ^ N := by
  have hpos : (0 : Int) < ((2 ^ N : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos N
  have h1 := Int.emod_lt_of_pos j hpos
  have h2 := Int.emod_nonneg j (ne_of_gt hpos)
  simp only [Wasm.Numerics.invSigned_]
  omega

/-- **`$iextend_`** agrees with `Numerics.iextend_` for `0 < K ≤ N`, the shape
every `extendK_s` instruction uses. -/
theorem callDef_iextend {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "iextend_" = none) {args : List Arg} {N K : Nat}
    {sx : Wasm.Signedness} {i : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (natV K), .val (sxV sx), .val (bvV i)])
    (hK : 0 < K) (hKN : K ≤ N) :
    CallDef env ρ "iextend_" args (bvV (Wasm.Numerics.iextend_ N K sx i)) := by
  refine callDef_of_tryClauses hρ h.iextendD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "K" (natV K)).bindVal
      "i" (bvV i) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hKv : σ.findVal? "K" = some (natV K) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (bvV i) := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hv : σ.findDef? "inv_signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "K"), .expA (.caseE a (.tupE [])),
        .expA (.varE "i")]
      [.val (natV N), .val (natV K), .val (.case a (.tuple [])), .val (bvV i)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  have hmod : EvalExp env σ (.binE .modOp (.numT .natT)
      (.projE (.uncaseE (.varE "i") "%") 0)
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "K"))) (natV (i.toNat % 2 ^ K)) :=
    evalExp_wrapNat (evalExp_uNV_payload hiv) (evalExp_twoPow hKv) (Nat.two_pow_pos K).ne'
  have hlt : i.toNat % 2 ^ K < 2 ^ K := Nat.mod_lt _ (Nat.two_pow_pos K)
  have hltN : i.toNat % 2 ^ K < 2 ^ N :=
    Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hKN)
  cases sx with
  | unsigned =>
      refine tryClauses_hit (hmatch "U") premsHold_nil ?_
      have hc := evalExp_case_tup_one (op := "%") hmod
      simpa [bvV, natV, Wasm.Numerics.iextend_, Nat.mod_eq_of_lt hltN] using hc
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef_tail
          (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
            (matchArg_expA_undef (matchExp_caseE_undef (by decide)))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig : EvalExp env σ (.callE "signed_" [.expA (.varE "K"),
          .expA (.binE .modOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
            (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "K")))])
          (intV (Wasm.Numerics.signed_ K (i.toNat % 2 ^ K))) :=
        evalExp_callE_iff.2 (callDef_signed h hs
          (evalArgs_cons (evalExp_var hKv) (evalArgs_cons hmod evalArgs_nil)) hK hlt)
      obtain ⟨hb₁, hb₂⟩ := signed_bounds hK hlt
      have hmono : (2 : Int) ^ (K - 1) ≤ 2 ^ (N - 1) := by
        have : (2 : Nat) ^ (K - 1) ≤ 2 ^ (N - 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        exact_mod_cast this
      have hinv := evalExp_callE_iff.2 (callDef_invSigned (env := env) (ρ := σ) h hv
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hsig evalArgs_nil))
        (by omega) (by omega) (by omega))
      have hc := evalExp_case_tup_one (op := "%") hinv
      have hlt2 := invSigned_lt N (Wasm.Numerics.signed_ K (i.toNat % 2 ^ K))
      simpa [bvV, natV, Wasm.Numerics.iextend_, Nat.mod_eq_of_lt hlt2] using hc

/-! ## Agreement: saturation -/

/-- `$sat_u_` lands in `uN(N)`. -/
theorem sat_u_lt (N : Nat) (j : Int) : Wasm.Numerics.sat_u_ N j < 2 ^ N := by
  have hp : 0 < 2 ^ N := Nat.two_pow_pos N
  have hpI : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by push_cast; rfl
  simp only [Wasm.Numerics.sat_u_]
  split
  · omega
  · split <;> omega

/-- `$sat_s_` lands in the two's-complement range of width `N`. -/
theorem sat_s_bounds (N : Nat) (j : Int) :
    -2 ^ (N - 1) ≤ Wasm.Numerics.sat_s_ N j ∧ Wasm.Numerics.sat_s_ N j < 2 ^ (N - 1) := by
  have hpn := Nat.two_pow_pos (N - 1)
  have hc : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by push_cast; rfl
  have hp : (0 : Int) < 2 ^ (N - 1) := by omega
  simp only [Wasm.Numerics.sat_s_]
  split
  · omega
  · split <;> omega

/-- **`$sat_u_`** agrees with `Numerics.sat_u_`. -/
theorem callDef_satU {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "sat_u_" = none) {args : List Arg} {N : Nat} {j : Int}
    (ha : EvalArgs env ρ args [.val (natV N), .val (intV j)]) :
    CallDef env ρ "sat_u_" args (natV (Wasm.Numerics.sat_u_ N j)) := by
  refine callDef_of_tryClauses hρ h.satUD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (intV j) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (intV j) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (intV j)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hmax : EvalExp env σ (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (intV (((2 ^ N : Nat) : Int) - 1)) :=
    evalExp_binNum (evalExp_toInt (evalExp_twoPow hNv)) evalExp_oneInt rfl
  have hpn := Nat.two_pow_pos N
  have hcastN : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by push_cast; rfl
  by_cases hneg : j < 0
  · refine tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .intT) (evalExp_var hiv) evalExp_zeroInt
      (by simp [Num.cmp]; omega))) ?_
    have hz := evalExp_natLit (env := env) (ρ := σ) 0
    simpa [Wasm.Numerics.sat_u_, hneg, natV] using hz
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .intT) (evalExp_var hiv) evalExp_zeroInt
      (by simp [Num.cmp]; omega))) ?_
    by_cases hbig : (2 : Int) ^ N - 1 < j
    · refine tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .gtOp)
        (t := .numT .intT) (evalExp_var hiv) hmax (by simp [Num.cmp]; omega))) ?_
      have hc := evalExp_toNat (env := env) (by omega) hmax
      rw [show (((2 ^ N : Nat) : Int) - 1).toNat = 2 ^ N - 1 by omega] at hc
      simpa [Wasm.Numerics.sat_u_, hneg, hbig, natV] using hc
    · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .gtOp)
        (t := .numT .intT) (evalExp_var hiv) hmax (by simp [Num.cmp]; omega))) ?_
      refine tryClauses_hit hmatch premsHold_elsePr ?_
      have hc := evalExp_toNat (env := env) (show (0 : Int) ≤ j by omega) (evalExp_var hiv)
      simpa [Wasm.Numerics.sat_u_, hneg, hbig, natV] using hc

/-- **`$sat_s_`** agrees with `Numerics.sat_s_` for `0 < N`. -/
theorem callDef_satS {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "sat_s_" = none) {args : List Arg} {N : Nat} {j : Int}
    (ha : EvalArgs env ρ args [.val (natV N), .val (intV j)]) (hN : 0 < N) :
    CallDef env ρ "sat_s_" args (intV (Wasm.Numerics.sat_s_ N j)) := by
  refine callDef_of_tryClauses hρ h.satSD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (intV j) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (intV j) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (intV j)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hcast : (((2 ^ (N - 1) : Nat)) : Int) = 2 ^ (N - 1) := by push_cast; rfl
  have hpow : EvalExp env σ _ (intV ((2 ^ (N - 1) : Nat) : Int)) :=
    evalExp_toInt (evalExp_twoPowPred hN hNv)
  rw [hcast] at hpow
  have hlow : EvalExp env σ _ (intV (-2 ^ (N - 1))) :=
    evalExp_unNum (op := .minusOp) (t := .numT .intT) hpow rfl
  have hmax : EvalExp env σ _ (intV (2 ^ (N - 1) - 1)) :=
    evalExp_binNum (op := .subOp) (t := .numT .intT) hpow evalExp_oneInt rfl
  by_cases hlo : j < -2 ^ (N - 1)
  · exact tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .intT) (evalExp_var hiv) hlow (by simp [Num.cmp]; omega)))
      (by simpa [Wasm.Numerics.sat_s_, hlo] using hlow)
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .intT) (evalExp_var hiv) hlow (by simp [Num.cmp]; omega))) ?_
    by_cases hhi : 2 ^ (N - 1) - 1 < j
    · exact tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .gtOp)
        (t := .numT .intT) (evalExp_var hiv) hmax (by simp [Num.cmp]; omega)))
        (by simpa [Wasm.Numerics.sat_s_, hlo, hhi] using hmax)
    · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .gtOp)
        (t := .numT .intT) (evalExp_var hiv) hmax (by simp [Num.cmp]; omega))) ?_
      exact tryClauses_hit hmatch premsHold_elsePr
        (by simpa [Wasm.Numerics.sat_s_, hlo, hhi] using evalExp_var (env := env) hiv)

/-! ## Agreement: saturating addition and subtraction -/


/-- **`$iadd_sat_`** agrees with `Numerics.iadd_sat_`.  The `0 < N` hypothesis is needed
only by the signed clause, which calls `$signed_` and `$inv_signed_`. -/
theorem callDef_iaddSat {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "iadd_sat_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "iadd_sat_" args (bvV (Wasm.Numerics.iadd_sat_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.iaddSatD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hv : σ.findDef? "inv_signed_" = none := by rw [hσ]; rfl
  have hu : σ.findDef? "sat_u_" = none := by rw [hσ]; rfl
  have hw : σ.findDef? "sat_s_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      refine tryClauses_hit (hmatch "U") premsHold_nil ?_
      have harg : EvalExp env σ (.cvtE (.binE .addOp (.numT .natT)
            (.projE (.uncaseE (.varE "i_1") "%") 0)
            (.projE (.uncaseE (.varE "i_2") "%") 0)) .natT .intT)
          (intV ((i₁.toNat : Int) + i₂.toNat)) := by
        have := evalExp_toInt (env := env) (evalExp_binNum (op := .addOp)
          (t := .numT .natT) (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl)
        rw [show ((i₁.toNat + i₂.toNat : Nat) : Int) = (i₁.toNat : Int) + i₂.toNat by
          push_cast; rfl] at this
        exact this
      have hsat := evalExp_callE_iff.2 (callDef_satU (env := env) (ρ := σ) h hu
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons harg evalArgs_nil)))
      have hc := evalExp_case_tup_one (op := "%") hsat
      have hlt := sat_u_lt N ((i₁.toNat : Int) + i₂.toNat)
      simpa [bvV, natV, Wasm.Numerics.iadd_sat_, Nat.mod_eq_of_lt hlt] using hc
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      have hcomb := evalExp_binNum (env := env) (op := .addOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl
      have hsat := evalExp_callE_iff.2 (callDef_satS (env := env) (ρ := σ) h hw
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hcomb evalArgs_nil)) hN)
      obtain ⟨hb₁, hb₂⟩ := sat_s_bounds N
        (Wasm.Numerics.signed_ N i₁.toNat + Wasm.Numerics.signed_ N i₂.toNat)
      have hinv := evalExp_callE_iff.2 (callDef_invSigned (env := env) (ρ := σ) h hv
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hsat evalArgs_nil)) hN hb₁ hb₂)
      have hc := evalExp_case_tup_one (op := "%") hinv
      have hlt := invSigned_lt N (Wasm.Numerics.sat_s_ N
        (Wasm.Numerics.signed_ N i₁.toNat + Wasm.Numerics.signed_ N i₂.toNat))
      simpa [bvV, natV, Wasm.Numerics.iadd_sat_, Nat.mod_eq_of_lt hlt] using hc


/-- **`$isub_sat_`** agrees with `Numerics.isub_sat_`.  The `0 < N` hypothesis is needed
only by the signed clause, which calls `$signed_` and `$inv_signed_`. -/
theorem callDef_isubSat {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "isub_sat_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "isub_sat_" args (bvV (Wasm.Numerics.isub_sat_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.isubSatD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hv : σ.findDef? "inv_signed_" = none := by rw [hσ]; rfl
  have hu : σ.findDef? "sat_u_" = none := by rw [hσ]; rfl
  have hw : σ.findDef? "sat_s_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      refine tryClauses_hit (hmatch "U") premsHold_nil ?_
      have harg : EvalExp env σ (.binE .subOp (.numT .intT)
            (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .intT)
            (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .intT))
          (intV ((i₁.toNat : Int) - i₂.toNat)) := evalExp_binNum (op := .subOp) (t := .numT .intT)
        (evalExp_toInt (evalExp_uNV_payload h1)) (evalExp_toInt (evalExp_uNV_payload h2)) rfl
      have hsat := evalExp_callE_iff.2 (callDef_satU (env := env) (ρ := σ) h hu
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons harg evalArgs_nil)))
      have hc := evalExp_case_tup_one (op := "%") hsat
      have hlt := sat_u_lt N ((i₁.toNat : Int) - i₂.toNat)
      simpa [bvV, natV, Wasm.Numerics.isub_sat_, Nat.mod_eq_of_lt hlt] using hc
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      have hcomb := evalExp_binNum (env := env) (op := .subOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl
      have hsat := evalExp_callE_iff.2 (callDef_satS (env := env) (ρ := σ) h hw
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hcomb evalArgs_nil)) hN)
      obtain ⟨hb₁, hb₂⟩ := sat_s_bounds N
        (Wasm.Numerics.signed_ N i₁.toNat - Wasm.Numerics.signed_ N i₂.toNat)
      have hinv := evalExp_callE_iff.2 (callDef_invSigned (env := env) (ρ := σ) h hv
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hsat evalArgs_nil)) hN hb₁ hb₂)
      have hc := evalExp_case_tup_one (op := "%") hinv
      have hlt := invSigned_lt N (Wasm.Numerics.sat_s_ N
        (Wasm.Numerics.signed_ N i₁.toNat - Wasm.Numerics.signed_ N i₂.toNat))
      simpa [bvV, natV, Wasm.Numerics.isub_sat_, Nat.mod_eq_of_lt hlt] using hc

/-! ## Agreement: the zero-divisor clauses of `$idiv_` and `$irem_` -/

/-- **`$idiv_`** at divisor `0` agrees with `Numerics.idiv_`: both are
undefined, which the IL writes as the empty option `eps`. -/
theorem callDef_idiv_zero {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "idiv_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV (0 : BitVec N))]) :
    CallDef env ρ "idiv_" args (optUNV (Wasm.Numerics.idiv_ N sx i₁ 0)) := by
  refine callDef_of_tryClauses hρ h.idivD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁) with hσ
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁),
        .val (.case "%" (.tuple [natV 0]))] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_caseE
            (matchExp_tupE_one matchExp_numE))) matchArgs_nil)))
  rw [show bvV (0 : BitVec N) = .case "%" (.tuple [natV 0]) by simp [bvV, natV],
    show Wasm.Numerics.idiv_ N sx i₁ 0 = none by cases sx <;> simp [Wasm.Numerics.idiv_]]
  have hbody : EvalExp env σ (Exp.optE none) (optUNV (N := N) none) :=
    evalExp_optE_none_iff.2 rfl
  cases sx with
  | unsigned => exact tryClauses_hit (hmatch "U") premsHold_nil hbody
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      exact tryClauses_hit (hmatch "S") premsHold_nil hbody

/-- **`$irem_`** at divisor `0` agrees with `Numerics.irem_`. -/
theorem callDef_irem_zero {env : Env} {ρ : VarEnv} (h : NumEnv env)
    (hρ : ρ.findDef? "irem_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV (0 : BitVec N))]) :
    CallDef env ρ "irem_" args (optUNV (Wasm.Numerics.irem_ N sx i₁ 0)) := by
  refine callDef_of_tryClauses hρ h.iremD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁) with hσ
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁),
        .val (.case "%" (.tuple [natV 0]))] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_caseE
            (matchExp_tupE_one matchExp_numE))) matchArgs_nil)))
  rw [show bvV (0 : BitVec N) = .case "%" (.tuple [natV 0]) by simp [bvV, natV],
    show Wasm.Numerics.irem_ N sx i₁ 0 = none by cases sx <;> simp [Wasm.Numerics.irem_]]
  have hbody : EvalExp env σ (Exp.optE none) (optUNV (N := N) none) :=
    evalExp_optE_none_iff.2 rfl
  cases sx with
  | unsigned => exact tryClauses_hit (hmatch "U") premsHold_nil hbody
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      exact tryClauses_hit (hmatch "S") premsHold_nil hbody

/-! ## What the pinned specification leaves uninterpreted

`3.1-numerics.scalar.spectec` marks a large part of the numerics group
`hint(builtin)` and gives it no defining clause: the shift and bitwise
operations, `$iclz_`/`$ictz_`/`$ipopcnt_`, *every* conversion between widths,
*every* floating-point operation, and the two rational rounding functions
`$truncz` and `$ceilz` that `$idiv_` and `$irem_` are written in terms of.
`spectec --ast` prints such a declaration as a `def` node with an empty clause
list, and `eval.ml:364-366` leaves a call to it unreduced.

So their denotation is **empty**: there is no value `v` at all with
`CallDef env ρ x args v`.  That is a fact about the specification, not a gap
in this file, and it is what `not_callDef_uninterpreted` records. -/

/-- `x` is declared by `env` with no clauses, decidably. -/
def uninterpretedIn (env : Env) (x : IL.Id) : Bool :=
  match env.findDef? x with
  | some d => d.2.2.isEmpty
  | none => false

/-- `x` is declared by `env` with no clauses: an *uninterpreted* function. -/
def Uninterpreted (env : Env) (x : IL.Id) : Prop :=
  ∃ ps t, env.findDef? x = some (ps, t, [])

/-- `uninterpretedIn` witnesses `Uninterpreted`. -/
theorem uninterpreted_of_uninterpretedIn {env : Env} {x : IL.Id}
    (h : uninterpretedIn env x = true) : Uninterpreted env x := by
  unfold uninterpretedIn at h
  cases hd : env.findDef? x with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some d =>
      rw [hd] at h
      obtain ⟨ps, t, cs⟩ := d
      cases cs with
      | nil => exact ⟨ps, t, hd⟩
      | cons c cs => exact absurd h (by simp [List.isEmpty])

/-- **An uninterpreted function has no value at all.**  This is the formal
content of `hint(builtin)`. -/
theorem not_callDef_uninterpreted {env : Env} {ρ : VarEnv} {x : IL.Id}
    {args : List Arg} {v : Value} (hx : uninterpretedIn env x = true)
    (hρ : ρ.findDef? x = none)
    (hb : ∀ ws, env.builtins.call x ws = Option.none) : ¬ CallDef env ρ x args v := by
  obtain ⟨ps, t, hd⟩ := uninterpreted_of_uninterpretedIn hx
  exact not_callDef_of_no_clauses hρ hd hb

/-- Every scalar-numerics name that `3.1-numerics.scalar.spectec` declares
with `hint(builtin)`: eighteen integer operations, the two rational rounding
functions, the ten conversions, the twenty-six floating-point operations, and
the sixteen bit/byte representation functions — seventy-two in all.

The list below is grouped in *that* order, which is **not** the order the file
declares them in: the file's order is bit/byte representation
(`3.1-numerics.scalar.spectec:31-47`), rounding (`:77`, `:81`), integer
(`:152-215`), floating-point (`:275-303`), conversions (`:323-333`).  Only the
*set* matters to `uninterpretedIn_wasm30`, which quantifies over the list. -/
def uninterpretedNumerics : List IL.Id :=
  ["iclz_", "ictz_", "ipopcnt_", "iq15mulr_sat_", "irelaxed_q15mulr_", "iavgr_",
   "inot_", "irev_", "iand_", "iandnot_", "ior_", "ixor_", "ishl_", "ishr_",
   "irotl_", "irotr_", "ibitselect_", "irelaxed_laneselect_",
   "truncz", "ceilz",
   "wrap__", "extend__", "trunc__", "trunc_sat__", "relaxed_trunc__", "demote__",
   "promote__", "convert__", "narrow__", "reinterpret__",
   "fabs_", "fneg_", "fsqrt_", "fceil_", "ffloor_", "ftrunc_", "fnearest_",
   "fadd_", "fsub_", "fmul_", "fdiv_", "fmin_", "fmax_", "fpmin_", "fpmax_",
   "frelaxed_min_", "frelaxed_max_", "fcopysign_",
   "feq_", "fne_", "flt_", "fgt_", "fle_", "fge_",
   "frelaxed_madd_", "frelaxed_nmadd_",
   "ibits_", "fbits_", "ibytes_", "fbytes_", "nbytes_", "vbytes_", "zbytes_",
   "cbytes_", "inv_ibits_", "inv_fbits_", "inv_ibytes_", "inv_fbytes_",
   "inv_nbytes_", "inv_vbytes_", "inv_zbytes_", "inv_cbytes_"]

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 2000000 in
/-- **Every one of them is uninterpreted in the pinned wasm-3.0
specification.**  Seventy-two names, checked in one `rfl`. -/
theorem uninterpretedIn_wasm30 :
    uninterpretedNumerics.all (uninterpretedIn (envOfScript Specs.wasm30)) = true := by rfl

/-- The pinned specification gives no meaning to any of them. -/
theorem not_callDef_wasm30 {ρ : VarEnv} {x : IL.Id} (hx : x ∈ uninterpretedNumerics)
    {args : List Arg} {v : Value} (hρ : ρ.findDef? x = none) :
    ¬ CallDef (envOfScript Specs.wasm30) ρ x args v :=
  not_callDef_uninterpreted (List.all_eq_true.1 uninterpretedIn_wasm30 x hx) hρ
    (fun _ => by simp [Builtins.none])

/-- `$iand_`, for instance, denotes nothing: the bitwise operations are not
defined by the specification at all. -/
theorem not_callDef_iand_wasm30 {args : List Arg} {v : Value} :
    ¬ CallDef (envOfScript Specs.wasm30) VarEnv.empty "iand_" args v :=
  not_callDef_wasm30 (by decide) rfl

/-- Nor `$ishl_`, where a divergence over the shift amount's modulus would
show up if there were anything to compare. -/
theorem not_callDef_ishl_wasm30 {args : List Arg} {v : Value} :
    ¬ CallDef (envOfScript Specs.wasm30) VarEnv.empty "ishl_" args v :=
  not_callDef_wasm30 (by decide) rfl

/-- Nor `$wrap__` and `$extend__`, the two conversions between widths. -/
theorem not_callDef_wrap_wasm30 {args : List Arg} {v : Value} :
    ¬ CallDef (envOfScript Specs.wasm30) VarEnv.empty "wrap__" args v :=
  not_callDef_wasm30 (by decide) rfl

/-- `$extend__`, likewise. -/
theorem not_callDef_extend_wasm30 {args : List Arg} {v : Value} :
    ¬ CallDef (envOfScript Specs.wasm30) VarEnv.empty "extend__" args v :=
  not_callDef_wasm30 (by decide) rfl

/-- Nor `$truncz`, which is why `$idiv_` and `$irem_` have a denotation only
at divisor `0`. -/
theorem not_callDef_truncz_wasm30 {args : List Arg} {v : Value} :
    ¬ CallDef (envOfScript Specs.wasm30) VarEnv.empty "truncz" args v :=
  not_callDef_wasm30 (by decide) rfl

/-- Nor any floating-point operation; `$fadd_` stands for all twenty-six. -/
theorem not_callDef_fadd_wasm30 {args : List Arg} {v : Value} :
    ¬ CallDef (envOfScript Specs.wasm30) VarEnv.empty "fadd_" args v :=
  not_callDef_wasm30 (by decide) rfl

/-! ## The agreement, at the pinned specification itself

Each corollary is the corresponding theorem above instantiated at
`numEnv_wasm30` and at literal arguments, so that nothing is left hypothetical:
these are statements about `specs/spectec/wasm-3.0.ast`.

The errata of `docs/projects/spectec-divergences.md` do not touch this group — the thirteen
wasm-3.0 patches correct `Bi32`, `Bi64`, `cont`, `utf8` and nine §6.x text
grammars — so the same statements hold of the corrected script; see "What this
file does not prove" below for the precise status of that claim. -/

/-- `$signed_` at the pinned specification. -/
theorem callDef_signed_wasm30 {N i : Nat} (hN : 0 < N) (hi : i < 2 ^ N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "signed_" (litArgs [natV N, natV i])
      (intV (Wasm.Numerics.signed_ N i)) :=
  callDef_signed numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN hi

/-- `$inv_signed_` at the pinned specification. -/
theorem callDef_invSigned_wasm30 {N : Nat} {j : Int} (hN : 0 < N)
    (h₁ : -2 ^ (N - 1) ≤ j) (h₂ : j < 2 ^ (N - 1)) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "inv_signed_"
      (litArgs [natV N, intV j]) (natV (Wasm.Numerics.invSigned_ N j)) :=
  callDef_invSigned numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN h₁ h₂

/-- `$bool` at the pinned specification. -/
theorem callDef_bool_wasm30 (b : Bool) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "bool" (litArgs [boolV b])
      (natV (Wasm.Numerics.bool_ b)) :=
  callDef_bool numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$sat_u_` at the pinned specification. -/
theorem callDef_satU_wasm30 {N : Nat} {j : Int} :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "sat_u_" (litArgs [natV N, intV j])
      (natV (Wasm.Numerics.sat_u_ N j)) :=
  callDef_satU numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$sat_s_` at the pinned specification. -/
theorem callDef_satS_wasm30 {N : Nat} {j : Int} (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "sat_s_" (litArgs [natV N, intV j])
      (intV (Wasm.Numerics.sat_s_ N j)) :=
  callDef_satS numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$iadd_` at the pinned specification. -/
theorem callDef_iadd_wasm30 {N : Nat} (i₁ i₂ : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "iadd_"
      (litArgs [natV N, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.iadd_ N i₁ i₂)) :=
  callDef_iadd numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$isub_` at the pinned specification. -/
theorem callDef_isub_wasm30 {N : Nat} (i₁ i₂ : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "isub_"
      (litArgs [natV N, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.isub_ N i₁ i₂)) :=
  callDef_isub numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$imul_` at the pinned specification. -/
theorem callDef_imul_wasm30 {N : Nat} (i₁ i₂ : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "imul_"
      (litArgs [natV N, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.imul_ N i₁ i₂)) :=
  callDef_imul numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$ineg_` at the pinned specification. -/
theorem callDef_ineg_wasm30 {N : Nat} (i : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "ineg_" (litArgs [natV N, bvV i])
      (bvV (Wasm.Numerics.ineg_ N i)) :=
  callDef_ineg numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$iabs_` at the pinned specification. -/
theorem callDef_iabs_wasm30 {N : Nat} (i : BitVec N) (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "iabs_" (litArgs [natV N, bvV i])
      (bvV (Wasm.Numerics.iabs_ N i)) :=
  callDef_iabs numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$iextend_` at the pinned specification. -/
theorem callDef_iextend_wasm30 {N K : Nat} {sx : Wasm.Signedness} (i : BitVec N)
    (hK : 0 < K) (hKN : K ≤ N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "iextend_"
      (litArgs [natV N, natV K, sxV sx, bvV i])
      (bvV (Wasm.Numerics.iextend_ N K sx i)) :=
  callDef_iextend numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hK hKN

/-- `$imin_` at the pinned specification. -/
theorem callDef_imin_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ i₂ : BitVec N)
    (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "imin_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.imin_ N sx i₁ i₂)) :=
  callDef_imin numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$imax_` at the pinned specification. -/
theorem callDef_imax_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ i₂ : BitVec N)
    (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "imax_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.imax_ N sx i₁ i₂)) :=
  callDef_imax numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$iadd_sat_` at the pinned specification. -/
theorem callDef_iaddSat_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ i₂ : BitVec N)
    (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "iadd_sat_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV i₂])
      (bvV (Wasm.Numerics.iadd_sat_ N sx i₁ i₂)) :=
  callDef_iaddSat numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$isub_sat_` at the pinned specification. -/
theorem callDef_isubSat_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ i₂ : BitVec N)
    (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "isub_sat_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV i₂])
      (bvV (Wasm.Numerics.isub_sat_ N sx i₁ i₂)) :=
  callDef_isubSat numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$ieqz_` at the pinned specification. -/
theorem callDef_ieqz_wasm30 {N : Nat} (i : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "ieqz_" (litArgs [natV N, bvV i])
      (bvV (Wasm.Numerics.ieqz_ N i)) :=
  callDef_ieqz numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$inez_` at the pinned specification. -/
theorem callDef_inez_wasm30 {N : Nat} (i : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "inez_" (litArgs [natV N, bvV i])
      (bvV (Wasm.Numerics.inez_ N i)) :=
  callDef_inez numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$ieq_` at the pinned specification. -/
theorem callDef_ieq_wasm30 {N : Nat} (i₁ i₂ : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "ieq_"
      (litArgs [natV N, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.ieq_ N i₁ i₂)) :=
  callDef_ieq numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$ine_` at the pinned specification. -/
theorem callDef_ine_wasm30 {N : Nat} (i₁ i₂ : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "ine_"
      (litArgs [natV N, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.ine_ N i₁ i₂)) :=
  callDef_ine numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$ilt_` at the pinned specification. -/
theorem callDef_ilt_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ i₂ : BitVec N)
    (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "ilt_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.ilt_ N sx i₁ i₂)) :=
  callDef_ilt numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$igt_` at the pinned specification. -/
theorem callDef_igt_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ i₂ : BitVec N)
    (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "igt_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.igt_ N sx i₁ i₂)) :=
  callDef_igt numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$ile_` at the pinned specification. -/
theorem callDef_ile_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ i₂ : BitVec N)
    (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "ile_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.ile_ N sx i₁ i₂)) :=
  callDef_ile numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$ige_` at the pinned specification. -/
theorem callDef_ige_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ i₂ : BitVec N)
    (hN : 0 < N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "ige_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.ige_ N sx i₁ i₂)) :=
  callDef_ige numEnv_wasm30 rfl (evalArgs_litArgs _ _ _) hN

/-- `$idiv_` at divisor `0`, at the pinned specification. -/
theorem callDef_idiv_zero_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "idiv_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV (0 : BitVec N)])
      (optUNV (Wasm.Numerics.idiv_ N sx i₁ 0)) :=
  callDef_idiv_zero numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-- `$irem_` at divisor `0`, at the pinned specification. -/
theorem callDef_irem_zero_wasm30 {N : Nat} {sx : Wasm.Signedness} (i₁ : BitVec N) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "irem_"
      (litArgs [natV N, sxV sx, bvV i₁, bvV (0 : BitVec N)])
      (optUNV (Wasm.Numerics.irem_ N sx i₁ 0)) :=
  callDef_irem_zero numEnv_wasm30 rfl (evalArgs_litArgs _ _ _)

/-! ## Reaching Silmaril's 32- and 64-bit operations

`Silmaril/Wasm/Numerics/IntegerN/Agreement.lean` proves that the
width-parametric transcription above *is* the `BitVec` operation and *is*
`Numerics.intBinOp`/`intRelOp` at `t.width`.  Composing, the pinned
specification's `$iadd_` denotes exactly what `Silmaril.Wasm.Numerics.intBinOp`
computes. -/

/-- `$iadd_` at an `i32`/`i64` type denotes `intBinOp t .add`. -/
theorem callDef_iadd_intBinOp (t : Wasm.IntType) (x y : Wasm.Numerics.IntValue t) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "iadd_"
      (litArgs [natV t.width, bvV x, bvV y])
      (bvV ((Wasm.Numerics.intBinOp t .add x y).toOption.getD 0)) := by
  have := callDef_iadd_wasm30 (N := t.width) x y
  rwa [show Wasm.Numerics.iadd_ t.width x y
      = (Wasm.Numerics.intBinOp t .add x y).toOption.getD 0 by
    have h := Wasm.Numerics.ibinop_agree t .add x y
    simp only [Wasm.Numerics.ibinop_] at h
    rw [← h]
    rfl] at this

/-- `$ilt_` at an `i32`/`i64` type denotes `intRelOp t (.lt sx)`. -/
theorem callDef_ilt_intRelOp (t : Wasm.IntType) (sx : Wasm.Signedness)
    (x y : Wasm.Numerics.IntValue t) (hN : 0 < t.width) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "ilt_"
      (litArgs [natV t.width, sxV sx, bvV x, bvV y])
      (bvV (Wasm.Numerics.intRelOp t (.lt sx) x y)) := by
  have := callDef_ilt_wasm30 (N := t.width) (sx := sx) x y hN
  rwa [show Wasm.Numerics.ilt_ t.width sx x y = Wasm.Numerics.intRelOp t (.lt sx) x y by
    have h := Wasm.Numerics.irelop_agree t (.lt sx) x y
    simpa only [Wasm.Numerics.irelop_] using h] at this

/-- Evaluation is deterministic (`Sem/Eval.lean`'s `CallDef.unique`), so
`callDef_iadd_wasm30` pins `$iadd_` down completely: no other value is
denoted.  The same argument applies to every theorem in this section. -/
theorem callDef_iadd_wasm30_unique {N : Nat} (i₁ i₂ : BitVec N) (v : Value)
    (hv : CallDef (envOfScript Specs.wasm30) VarEnv.empty "iadd_"
      (litArgs [natV N, bvV i₁, bvV i₂]) v) :
    v = bvV (Wasm.Numerics.iadd_ N i₁ i₂) :=
  hv.unique (callDef_iadd_wasm30 i₁ i₂)

/-! ## Sanity checks

Concrete instances of the bridge and of the Silmaril side, decided in the
kernel on small widths.  The SpecTec side is never *evaluated* here: every
statement above is proved by unfolding the clauses with the compositionality
lemmas, so there is nothing to run. -/

/-- The bridge on a concrete bit pattern. -/
example : bvV (3#8) = .case "%" (.tuple [natV 3]) := rfl

/-- Two's complement at width 8. -/
example : Wasm.Numerics.signed_ 8 200 = -56 := by decide

/-- Its inverse. -/
example : Wasm.Numerics.invSigned_ 8 (-56) = 200 := by decide

/-- Wrapping addition. -/
example : Wasm.Numerics.iadd_ 8 255#8 1#8 = 0#8 := by decide

/-- Wrapping subtraction, where the IL's `2^N +` bias matters. -/
example : Wasm.Numerics.isub_ 8 0#8 1#8 = 255#8 := by decide

/-- Signed comparison disagrees with unsigned, as it must. -/
example : Wasm.Numerics.ilt_ 8 .signed 255#8 0#8 = 1#32 := by decide

/-- …and unsigned does not. -/
example : Wasm.Numerics.ilt_ 8 .unsigned 255#8 0#8 = 0#32 := by decide

/-- `extend8_s` at width 32. -/
example : Wasm.Numerics.iextend_ 32 8 .signed 255#32 = 0xFFFFFFFF#32 := by decide

/-! ## What is not reached

Three things in `3.1-numerics.scalar.spectec` are **not** covered above, and
in each case the reason is a property of the specification, not a gap in the
proof.  They are stated here precisely.

### 1. The bitwise, shift, rotate and bit-counting operations are undefined

`$iclz_`, `$ictz_`, `$ipopcnt_`, `$inot_`, `$irev_`, `$iand_`, `$iandnot_`,
`$ior_`, `$ixor_`, `$ishl_`, `$ishr_`, `$irotl_`, `$irotr_`, `$ibitselect_`,
`$irelaxed_laneselect_`, `$iavgr_`, `$iq15mulr_sat_` and `$irelaxed_q15mulr_`
— all eighteen — are declared `hint(builtin)`
(`3.1-numerics.scalar.spectec:152-215`) and have **no clause**.  There is
therefore nothing to compare: `not_callDef_iand_wasm30` and
`not_callDef_ishl_wasm30` prove that the pinned specification assigns them no
value at all.  In particular the classic divergence — whether a shift amount
is reduced modulo `N` — cannot be checked against SpecTec, because SpecTec at
this pin does not say.  `IntegerN.ishl_` documents the modulus as coming from
the *prose* specification, not from the SpecTec source.

### 2. The conversions between widths are undefined, too

`$wrap__`, `$extend__`, `$trunc__`, `$trunc_sat__`, `$relaxed_trunc__`,
`$demote__`, `$promote__`, `$convert__`, `$narrow__` and `$reinterpret__` are
all `hint(builtin)` (`3.1-numerics.scalar.spectec:323-333`) with no clause, so
priority (2) of this task — "the conversions between widths" — is empty on the
SpecTec side.  `not_callDef_wrap_wasm30` and `not_callDef_extend_wasm30`
record that.  What *is* available is `$iextend_`
(`3.1-numerics.scalar.spectec:161-162`), the within-width sign extension that
`extendK_s` uses, and that is proved: `callDef_iextend`.

### 3. `$idiv_` and `$irem_` are undefined except at divisor `0`

Both are written in terms of `$truncz` (`:172,175,178,180`), which is itself
`hint(builtin)` with no clause (`:76-78`; the intended definition is present
only as a comment).  `not_callDef_truncz_wasm30` proves `$truncz` denotes
nothing, so the three non-zero clauses of `$idiv_` and the two of `$irem_`
have no value.  The zero clauses do, and they agree: `callDef_idiv_zero` and
`callDef_irem_zero`.

The signed clause of `$irem_` has a second, independent obstruction.  Its
`--ast` form is

```
(clause … (exp "j_1" int) (exp "j_2" int) … (if (bin and bool
  (cmp eq bool (var "j_1") (call "signed_" …)) (cmp eq bool (var "j_2") …))))
```

— `j_1` and `j_2` occur free in both the premise and the body, and the
premise is an `IfPr`, not a `LetPr`.  `eval.ml:688-693` *evaluates* an `IfPr`
and demands a `BoolE`; a free variable makes it `Ok None`, which
`eval.ml:655-660` turns into "this call does not reduce".  So the surface
syntax `-- if j_1 = $signed_(N, i_1)` (`:181`), which reads as a binding,
elaborates to a test that the IL evaluator cannot perform.  The same holds of
our transcription, where the clause is simply skipped.  This is reported as
part of the errata work, not fixed here.

### 4. Floating point

`fN(N)` is a *structured* type at this pin
(`1.1-syntax.values.spectec:46-55`): `POS`/`NEG` of `NORM m exp`, `SUBNORM m`,
`INF` or `NAN (m)`.  It is **not** `Xl.Num`'s `real`, so the rendering caveat
of `docs/projects/spectec/README.md` does not apply to it, and `Sem.Value` can hold a float
exactly.  What is missing is the *operations*: all twenty-six of `$fabs_` …
`$frelaxed_nmadd_` are `hint(builtin)` with no clause
(`3.1-numerics.scalar.spectec:275-303`).  `not_callDef_fadd_wasm30` records
one of them; `uninterpretedIn_wasm30` records all of them at once.  So the
only honest statement about floating-point agreement at this pin is the
negative one, and it is proved.

### 5. The corrected specifications

The theorems above are stated for an arbitrary `NumEnv env` and instantiated
at `envOfScript Specs.wasm30`.  The thirteen verified wasm-3.0 errata of
`docs/projects/spectec-divergences.md` patch `Bi32`, `Bi64`, `cont`, `utf8` and nine §6.x
text-format grammars — none of them a member of the numerics group — so the
same instantiation should hold of `IL.Binary51.wasm30binary51` and
`IL.Text6x.wasm30text6x`.  That is **not proved here**: `envOfScript` of a
patched script re-runs `replaceDefs` over all 976 definitions, and the general
lemma "`replaceDefs` preserves `envOfScript … |>.findDef?` away from the
patch's target" is not in `Silmaril/SpecTec/Errata.lean` yet.  Adding it is the
right fix and belongs in that file, not this one.

### 6. The vector numerics

`3.2-numerics.vector.spectec` is untouched.  Its lane-wise operations are
built from the scalar ones proved here, so it is the natural next step. -/

end Silmaril.SpecTec.Equiv
