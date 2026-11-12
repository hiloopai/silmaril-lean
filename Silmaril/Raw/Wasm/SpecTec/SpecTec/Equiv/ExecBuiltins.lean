module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecNumeric
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Numerics.IntegerN
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# When a definition denotes nothing, and what to do about it

Phase 4, continued.  `Equiv/ExecNumeric.lean` characterises the eight scalar
numeric rules of `Step_pure` and observes that an opcode whose scalar function
the pin leaves `hint(builtin)` is *stuck* — but only conditionally, because
"`$binop_` denotes nothing at `AND`" was not proved.  This file supplies the
missing half.

## Why it cannot be computed

`tryClauses`, `matchExp` and `evalExp` are all defined by well-founded
recursion on their fuel (`termination_by n => n`), so none of them reduces
under `rfl`: a goal

```
tryClauses 200 (envOfScript Specs.wasm30) … = .error .undef
```

is not closed by `decide` or `rfl`, however much `maxRecDepth` it is given.
(`hasNumericRules_wasm30` *is* an `rfl`, but it only looks a relation up in a
`Map`; it never runs the evaluator.)  The argument has to be structural, which
is what the rest of this section builds.

## The match-failure principle

`tryClauses` moves to the next clause exactly when the current clause's
argument patterns or premises **definitely** fail — `.error .undef`, not merely
"no scope at this fuel" (`Res.elimUndef`, `eval.ml:655,665`).
`Equiv/Numerics.lean` has the three positive lemmas (`tryClauses_hit`,
`tryClauses_skip_match`, `tryClauses_skip_prem`); proving that a call denotes
*nothing* needs their converses, and a reason for a pattern to fail in the
first place.

* `matchExp_caseE_undef_of_ne` — a `CaseE` pattern against a different
  injection fails definitely.  This is the reason every dispatcher clause for a
  different opcode is skipped.
* `matchArg_expA_undef`, and `matchArgs_cons_undef` from `Equiv/Numerics.lean`,
  lift that to an argument list.
* `not_tryClauses_nil`, `tryClauses_cons_iff_of_skip`,
  `not_tryClauses_of_bodyUndef` — the negative side of `tryClauses`.
* `not_callDef_of_notTryClauses` — and hence of `CallDef`, and hence of
  `Applies`.

## The design move: a builtin interpretation

Stopping at "the pinned IL is stuck at `i32.and`" would make the whole
builtin-dependent part of §4.3 unreachable, which is most of the numeric and
vector block.  It is also the wrong conclusion to stop at: the pinned
specification's *equations* are right, and only its *primitives* are missing.

So `Env` carries an interpretation of the primitives, and `callDef` consults it
exactly where the script supplies nothing:

```
Res.elimUndef (tryClauses n env d.2.2 argVs) .ok
  (fun _ => Res.ofOption (env.builtins.call x' argVs))
```

With `Builtins.none` this is the old behaviour on the nose, so every existing
theorem about the pinned specification stands unchanged and means what it
said.  With `Builtins.ofProfile` — Silmaril's own numerics — the equivalence
statement becomes

> our Core 3.0 ≡ SpecTec IL[builtins := our numerics]

which is the same shape as running WasmCert with our floats.  The two readings
are kept apart by name, never conflated: `Specs.wasm30` is the pinned script
and denotes nothing at `$iand_`; `envWithBuiltins` is the instantiated one.

Note that the fallback triggers on *any* definite failure, not only on an
empty clause list.  That is deliberate and slightly stronger than
"`hint(builtin)`": `$idiv_` has clauses but they are written in terms of
`$truncz`, which is itself builtin, so interpreting `$truncz` repairs `$idiv_`
*through its own equations* rather than overriding them.  The cost is that a
builtin entry for a name whose clauses genuinely fail would shadow that
failure; `builtinsAgree` below is the hypothesis that rules this out where it
matters.

## What is proved here

See the sections below, and "What is not reached" at the end.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecBuiltins

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (RuleFires HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric

-- The local simp set `Equiv/Execution.lean` uses for "this pattern variable is
-- (not) already bound" side conditions.
attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## A pattern that definitely fails -/

/-- A `CaseE` pattern against a *different* injection fails definitely.  This
is `Res.assert (op' = op) …` with the assertion false (`eval.ml`'s
`match_exp`), and it is why a dispatcher skips the clauses for other opcodes. -/
theorem matchExp_caseE_undef_of_ne {env : Env} {ρ : VarEnv} {op op' : MixopS} {e : Exp}
    {w : Value} (h : ¬ (op' = op)) : MatchExpUndef env ρ (.caseE op e) (.case op' w) :=
  ⟨1, by simp only [matchExp, Value.asCase?, Res.ofOption_some, Bind.bind, Except.bind,
    Res.assert, h, reduceIte]⟩

/-- A `CaseE` pattern against a value that is not an injection at all fails
definitely too. -/
theorem matchExp_caseE_undef_of_notCase {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp}
    {v : Value} (h : v.asCase? = none) : MatchExpUndef env ρ (.caseE op e) v :=
  ⟨1, by simp only [matchExp, h, Res.ofOption_none, Bind.bind, Except.bind]⟩

/-- A definite failure of an expression pattern is one of an `ExpA` argument. -/
theorem matchArg_expA_undef {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : MatchExpUndef env ρ e v) : ∃ n, matchArg n env ρ (.expA e) (.val v) = .error .undef := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp only [matchArg, h]; split <;> rfl⟩

/-! ## The negative side of `tryClauses` -/

/-- An empty clause list denotes nothing.  This is a `hint(builtin)` function
in the pinned script. -/
theorem not_tryClauses_nil {env : Env} {ws : List ArgV} {v : Value} :
    ¬ TryClauses env [] ws v := by
  rintro ⟨n, h⟩
  cases n with
  | zero => simp [tryClauses] at h
  | succ n => simp [tryClauses] at h

/-- A clause whose patterns definitely fail contributes nothing: the call
denotes `v` with the clause exactly when it does without it. -/
theorem tryClauses_cons_iff_of_skip {env : Env} {q : List Param} {pats : List Arg}
    {e : Exp} {prems : List Prem} {cs : List Clause} {ws : List ArgV} {v : Value}
    (hm : MatchArgsUndef env VarEnv.empty pats ws) :
    TryClauses env (.defD q pats e prems :: cs) ws v ↔ TryClauses env cs ws v := by
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨m, hm⟩ := hm
    have h' : tryClauses (max m n + 1) env (.defD q pats e prems :: cs) ws = .ok v :=
      tryClauses_ok_of_le (by omega) h
    have e1 : matchArgs (max m n) env VarEnv.empty pats ws = .error .undef :=
      matchArgs_undef_of_le (by omega) hm
    simp only [tryClauses, e1, Bind.bind, Except.bind, Res.elimUndef] at h'
    exact ⟨max m n, h'⟩
  · intro h
    exact tryClauses_skip_match hm h

/-- A clause that fires but whose *body* is undefined makes the whole call
undefined: `Res.elimUndef` catches a failure of the match or the premises, but
not of the body. -/
theorem not_tryClauses_of_bodyUndef {env : Env} {q : List Param} {pats : List Arg}
    {e : Exp} {prems : List Prem} {cs : List Clause} {ws : List ArgV} {ρ₀ ρ₁ : VarEnv}
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (hp : PremsHold env ρ₀ prems ρ₁)
    (hb : ∀ u, ¬ EvalExp env ρ₁ e u) {v : Value} :
    ¬ TryClauses env (.defD q pats e prems :: cs) ws v := by
  rintro ⟨n, h⟩
  obtain ⟨n₁, hm⟩ := hm
  obtain ⟨n₂, hp⟩ := hp
  cases n with
  | zero => simp [tryClauses] at h
  | succ n =>
      set N := max (max n₁ n₂) n with hN
      have e1 : matchArgs N env VarEnv.empty pats ws = .ok ρ₀ :=
        matchArgs_ok_of_le (by omega) hm
      have e2 : premsHold N env ρ₀ prems = .ok ρ₁ := premsHold_ok_of_le (by omega) hp
      have h' : tryClauses (N + 1) env (.defD q pats e prems :: cs) ws = .ok v :=
        tryClauses_ok_of_le (by omega) h
      simp only [tryClauses, e1, Bind.bind, Except.bind, e2, Res.elimUndef_ok] at h'
      exact hb v ⟨N, h'⟩

/-! ## Lifting to a call -/

/-- If the clauses of `x` denote nothing at `ws`, neither does `Applies`. -/
theorem not_applies_of_notTryClauses {env : Env} {x : IL.Id} {ps : List Param} {t : Typ}
    {cs : List Clause} {ws : List ArgV} (hd : env.findDef? x = some (ps, t, cs))
    (hb : env.builtins.call x ws = Option.none)
    (h : ∀ u, ¬ TryClauses env cs ws u) : ∀ u, ¬ Applies env x ws u := by
  rintro u ⟨ps', t', cs', hd', hc⟩
  rw [hd] at hd'
  have hcs : cs = cs' := congrArg (fun p => p.2.2) (Option.some.inj hd')
  subst hcs
  rcases hc with hc | ⟨-, hbv⟩
  · exact h u hc
  · rw [hb] at hbv; exact absurd hbv (by simp)

/-! ## The pinned reading is unchanged

`Builtins.none` makes the fallback `Res.ofOption none = .error .undef`, which
`Res.elimUndef` already returns in that position.  So `callDef` at a
`Builtins.none` environment is the old `callDef` **on the nose**, and every
theorem about `Specs.wasm30` proved before the parameterisation means exactly
what it said.  `envOfScript` builds a `Builtins.none` environment, so this is
not a side condition anyone has to carry. -/

/-- With no interpretation installed, the fallback is invisible. -/
theorem elimUndef_ofOption_none {α : Type} (r : Res α) :
    Res.elimUndef r .ok (fun _ => Res.ofOption Option.none) = r := by
  cases r with
  | ok a => rfl
  | error e => cases e <;> rfl

/-! ## A `hint(builtin)` function, with and without an interpretation -/

/-- **The finding, as a lemma** (#881 and
`Equiv/Numerics.lean`'s negative results, stated once and generically).  A
function the pinned script declares with **no clauses** denotes nothing, at
every argument list, as long as no interpretation is installed for it. -/
theorem not_callDef_of_nil {env : Env} {ρ : VarEnv} {x : IL.Id} {ps : List Param}
    {t : Typ} {args : List Arg} {v : Value}
    (hρ : ρ.findDef? x = none) (hd : env.findDef? x = some (ps, t, []))
    (hb : ∀ ws, env.builtins.call x ws = Option.none) :
    ¬ CallDef env ρ x args v := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [callDef] at hn
  | succ n =>
      rw [callDef] at hn
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hρ, Option.getD_none, hd] at hn
      obtain ⟨ws, -, d, hdd, hc⟩ := hn
      obtain rfl := (Option.some.inj hdd).symm
      cases n with
      | zero => simp [tryClauses, Res.elimUndef] at hc
      | succ m =>
          have hnil : tryClauses (m + 1) env [] ws = .error .undef := by simp [tryClauses]
          rw [hnil, Res.elimUndef, hb ws] at hc
          simp at hc

/-- …and with an interpretation it denotes what the interpretation says.  This
is the half that unblocks every builtin-dependent rule at once: the
specification's *equations* are used as written, and only its *primitives*
come from outside. -/
theorem callDef_of_builtin_nil {env : Env} {ρ : VarEnv} {x : IL.Id} {ps : List Param}
    {t : Typ} {args : List Arg} {ws : List ArgV} {v : Value}
    (hρ : ρ.findDef? x = none) (hd : env.findDef? x = some (ps, t, []))
    (ha : EvalArgs env ρ args ws) (hb : env.builtins.call x ws = some v) :
    CallDef env ρ x args v := by
  obtain ⟨n, ha⟩ := ha
  refine ⟨n + 2, ?_⟩
  have e1 : evalArgs (n + 1) env ρ args = .ok ws := evalArgs_ok_of_le (by omega) ha
  have hnil : tryClauses (n + 1) env [] ws = .error .undef := by simp [tryClauses]
  simp only [callDef, e1, Bind.bind, Except.bind, hρ, Option.getD_none, hd,
    Res.ofOption_some, hnil, Res.elimUndef, hb, Res.ofOption_some]

/-! ## An interpretation: Silmaril's own numerics

`Silmaril/Wasm/Numerics/IntegerN.lean` defines the integer primitives the
pinned script declares and does not define.  `wasmIntBuiltins` is that
assignment, read through `Equiv/Numerics.lean`'s value bridge: `iN(N)` is the
one-case variant `%( n )`, so a bit pattern is `bvV`.

This is the instantiation the equivalence theorem is stated at.  It is kept
strictly separate from the pinned reading: `Specs.wasm30` denotes nothing at
`$iand_` (`not_callDef_iand_wasm30`, still true), and `wasm30WithWasmNumerics`
denotes `Numerics.iand_` there (`callDef_iand_wasmBuiltins`).  The two are
never conflated — which of the two a theorem is about is visible in its
statement. -/

/-- Read a bit pattern of width `N` out of the IL's `iN(N)`, which is the
one-case variant `%( n )` (`1.1-syntax.values.spectec:10-15`). -/
def asBits? (N : Nat) : Value → Option (BitVec N)
  | .case "%" (.tuple [.num (.natN n)]) => some (BitVec.ofNat N n)
  | _ => none

@[simp] theorem asBits?_bvV {N : Nat} (i : BitVec N) : asBits? N (bvV i) = some i := by
  simp [asBits?, bvV, natV]

/-- A binary integer primitive, read through the value bridge. -/
def binBits (N : Nat) (f : BitVec N → BitVec N → BitVec N) (a b : Value) : Option Value :=
  match asBits? N a, asBits? N b with
  | some x, some y => some (bvV (f x y))
  | _, _ => Option.none

/-- A unary integer primitive, read through the value bridge. -/
def unBits (N : Nat) (f : BitVec N → BitVec N) (a : Value) : Option Value :=
  match asBits? N a with
  | some x => some (bvV (f x))
  | Option.none => Option.none

@[simp] theorem binBits_bvV {N : Nat} (f : BitVec N → BitVec N → BitVec N) (i₁ i₂ : BitVec N) :
    binBits N f (bvV i₁) (bvV i₂) = some (bvV (f i₁ i₂)) := by simp [binBits]

@[simp] theorem unBits_bvV {N : Nat} (f : BitVec N → BitVec N) (i : BitVec N) :
    unBits N f (bvV i) = some (bvV (f i)) := by simp [unBits]

/-- Silmaril's integer primitives, as an interpretation of the `hint(builtin)`
names of `3.1-numerics.scalar.spectec:152-215`.  Each entry matches the
argument shape the pinned declaration gives the function, so a call with the
wrong shape is still uninterpreted. -/
noncomputable def wasmIntBuiltins : Builtins where
  call x ws :=
    match x, ws with
    | "iand_", [.val (.num (.natN N)), .val a, .val b] =>
        binBits N (Wasm.Numerics.iand_ N) a b
    | "ior_", [.val (.num (.natN N)), .val a, .val b] =>
        binBits N (Wasm.Numerics.ior_ N) a b
    | "ixor_", [.val (.num (.natN N)), .val a, .val b] =>
        binBits N (Wasm.Numerics.ixor_ N) a b
    | "iandnot_", [.val (.num (.natN N)), .val a, .val b] =>
        binBits N (Wasm.Numerics.iandnot_ N) a b
    | "inot_", [.val (.num (.natN N)), .val a] => unBits N (Wasm.Numerics.inot_ N) a
    | "iclz_", [.val (.num (.natN N)), .val a] => unBits N (Wasm.Numerics.iclz_ N) a
    | "ictz_", [.val (.num (.natN N)), .val a] => unBits N (Wasm.Numerics.ictz_ N) a
    | "ipopcnt_", [.val (.num (.natN N)), .val a] => unBits N (Wasm.Numerics.ipopcnt_ N) a
    | _, _ => Option.none

/-- The pinned wasm-3.0 script, read with Silmaril's integer primitives
installed.  Every `findDef?`/`findRel?` fact about `envOfScript Specs.wasm30`
holds of it unchanged (`Env.findDef?_withBuiltins`), so every provenance
`rfl` in `Equiv/Execution.lean` and `Equiv/ExecNumeric.lean` transfers. -/
noncomputable def wasm30WithWasmNumerics : Env :=
  (envOfScript Specs.wasm30).withBuiltins wasmIntBuiltins

set_option maxRecDepth 4000000 in
/-- Looking a definition up is unaffected by installing an interpretation, and
this `rfl` is cheap: neither side has to unfold `envOfScript`. -/
@[simp] theorem findDef?_wasm30WithWasmNumerics (x : IL.Id) :
    wasm30WithWasmNumerics.findDef? x = (envOfScript Specs.wasm30).findDef? x := by
  rw [wasm30WithWasmNumerics, Env.findDef?_withBuiltins]

set_option maxRecDepth 4000000 in
/-- **The unblocking theorem.**  `$iand_` is `hint(builtin)` with no clause, so
the pinned script gives it nothing; with Silmaril's numerics installed it
denotes exactly `Numerics.iand_`. -/
theorem callDef_iand_wasmBuiltins {N : Nat} (i₁ i₂ : BitVec N) :
    CallDef wasm30WithWasmNumerics VarEnv.empty "iand_"
      (litArgs [natV N, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.iand_ N i₁ i₂)) :=
  callDef_of_builtin_nil rfl
    (by rw [findDef?_wasm30WithWasmNumerics]; rfl) (evalArgs_litArgs _ _ _)
    (by simp [wasm30WithWasmNumerics, Env.withBuiltins, wasmIntBuiltins, natV])

set_option maxRecDepth 4000000 in
/-- The same for `$ishl_`'s companion `$ior_`, to show the pattern is not
special to one name. -/
theorem callDef_ior_wasmBuiltins {N : Nat} (i₁ i₂ : BitVec N) :
    CallDef wasm30WithWasmNumerics VarEnv.empty "ior_"
      (litArgs [natV N, bvV i₁, bvV i₂]) (bvV (Wasm.Numerics.ior_ N i₁ i₂)) :=
  callDef_of_builtin_nil rfl
    (by rw [findDef?_wasm30WithWasmNumerics]; rfl) (evalArgs_litArgs _ _ _)
    (by simp [wasm30WithWasmNumerics, Env.withBuiltins, wasmIntBuiltins, natV])

set_option maxRecDepth 4000000 in
/-- **The contrast, kept explicit.**  At the pinned script — no interpretation
installed — the very same call denotes nothing.  This is the
#881 finding, and it is still true; the parameterisation does not erase it, it
gives it a name. -/
theorem not_callDef_iand_pinned {args : List Arg} {v : Value} :
    ¬ CallDef (envOfScript Specs.wasm30) VarEnv.empty "iand_" args v :=
  not_callDef_of_nil rfl rfl (fun _ => by simp [Builtins.none])

/-! ## `$binop_`'s dispatch, walked

`Equiv/ExecNumeric.lean` left one thing conditional: that `$binop_` denotes
nothing at `AND`.  That is a statement about the *pinned clause list*, so the
clause list has to be in Lean.  `AND` is clause 5, so reaching it means
skipping `ADD`, `SUB`, `MUL`, `DIV` and `REM` — each of which fails on the
opcode pattern, a `CaseE` against a different injection
(`matchExp_caseE_undef_of_ne`).

The six clauses below were generated from the `--ast` s-expressions by the
converter that produced `Equiv/ExecNumeric.lean`'s rule terms, and
`binopDef_wasm30` discharges the provenance by `rfl` against the pinned
stream, as everywhere else in this development.

One transcription trap, since it cost a false start: the `--ast` printer emits
a `SubE` as `(sub e t_2 t_1)` — the **target** type first, then the source —
which is the opposite of `IL.Exp.subE`'s argument order.  `local.tee`
(`Equiv/Execution.lean`) is the witness: its `(sub (var "val") (var "instr")
(var "val"))` is `.subE (.varE "val") (.varT "val" []) (.varT "instr" [])`. -/

/-- `$binop_` clause 0, the `ADD` case. -/
def binopClauseADD : Clause :=
  (.defD [(.expP "Inn" (.varT "Inn" [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE
   "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expP "i_2" (.varT "num_" [(.expA
   (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))]))] [(.expA (.subE (.varE
   "Inn") (.varT "Inn" []) (.varT "numtype" []))), (.expA (.caseE "ADD" (.tupE []))), (.expA
   (.varE "i_1")), (.expA (.varE "i_2"))] (.listE [(.callE "iadd_" [(.expA (.callE "sizenn"
   [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expA (.varE
   "i_1")), (.expA (.varE "i_2"))])]) [])

/-- `$binop_` clause 1, the `SUB` case. -/
def binopClauseSUB : Clause :=
  (.defD [(.expP "Inn" (.varT "Inn" [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE
   "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expP "i_2" (.varT "num_" [(.expA
   (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))]))] [(.expA (.subE (.varE
   "Inn") (.varT "Inn" []) (.varT "numtype" []))), (.expA (.caseE "SUB" (.tupE []))), (.expA
   (.varE "i_1")), (.expA (.varE "i_2"))] (.listE [(.callE "isub_" [(.expA (.callE "sizenn"
   [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expA (.varE
   "i_1")), (.expA (.varE "i_2"))])]) [])

/-- `$binop_` clause 2, the `MUL` case. -/
def binopClauseMUL : Clause :=
  (.defD [(.expP "Inn" (.varT "Inn" [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE
   "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expP "i_2" (.varT "num_" [(.expA
   (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))]))] [(.expA (.subE (.varE
   "Inn") (.varT "Inn" []) (.varT "numtype" []))), (.expA (.caseE "MUL" (.tupE []))), (.expA
   (.varE "i_1")), (.expA (.varE "i_2"))] (.listE [(.callE "imul_" [(.expA (.callE "sizenn"
   [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expA (.varE
   "i_1")), (.expA (.varE "i_2"))])]) [])

/-- `$binop_` clause 3, the `DIV` case. -/
def binopClauseDIV : Clause :=
  (.defD [(.expP "Inn" (.varT "Inn" [])), (.expP "sx" (.varT "sx" [])), (.expP "i_1" (.varT
   "num_" [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expP
   "i_2" (.varT "num_" [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype"
   [])))]))] [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))), (.expA
   (.caseE "DIV" (.varE "sx"))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.liftE
   (.callE "idiv_" [(.expA (.callE "sizenn" [(.expA (.subE (.varE "Inn") (.varT "Inn" [])
   (.varT "numtype" [])))])), (.expA (.varE "sx")), (.expA (.varE "i_1")), (.expA (.varE
   "i_2"))])) [])

/-- `$binop_` clause 4, the `REM` case. -/
def binopClauseREM : Clause :=
  (.defD [(.expP "Inn" (.varT "Inn" [])), (.expP "sx" (.varT "sx" [])), (.expP "i_1" (.varT
   "num_" [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expP
   "i_2" (.varT "num_" [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype"
   [])))]))] [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))), (.expA
   (.caseE "REM" (.varE "sx"))), (.expA (.varE "i_1")), (.expA (.varE "i_2"))] (.liftE
   (.callE "irem_" [(.expA (.callE "sizenn" [(.expA (.subE (.varE "Inn") (.varT "Inn" [])
   (.varT "numtype" [])))])), (.expA (.varE "sx")), (.expA (.varE "i_1")), (.expA (.varE
   "i_2"))])) [])

/-- `$binop_` clause 5, the `AND` case. -/
def binopClauseAND : Clause :=
  (.defD [(.expP "Inn" (.varT "Inn" [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE
   "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expP "i_2" (.varT "num_" [(.expA
   (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))]))] [(.expA (.subE (.varE
   "Inn") (.varT "Inn" []) (.varT "numtype" []))), (.expA (.caseE "AND" (.tupE []))), (.expA
   (.varE "i_1")), (.expA (.varE "i_2"))] (.listE [(.callE "iand_" [(.expA (.callE "sizenn"
   [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expA (.varE
   "i_1")), (.expA (.varE "i_2"))])]) [])

/-- `$binop_`'s parameters, as pinned. -/
def binopParams : List Param :=
  [(.expP "numtype" (.varT "numtype" [])),
   (.expP "binop_" (.varT "binop_" [(.expA (.varE "numtype"))])),
   (.expP "num_" (.varT "num_" [(.expA (.varE "numtype"))])),
   (.expP "num_" (.varT "num_" [(.expA (.varE "numtype"))]))]

/-- `$binop_`'s result type: a *list*, which is the option-as-list that makes
the `-val`/`-trap` pair of rules a partition. -/
def binopTyp : Typ := .iterT (.varT "num_" [(.expA (.varE "numtype"))]) .list

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1000000 in
/-- **Provenance.**  The pinned `$binop_` begins with those six clauses, in
that order; `rest` is the thirteen the walk never reaches. -/
theorem binopDef_wasm30 :
    ∃ rest, (envOfScript Specs.wasm30).findDef? "binop_" =
      some (binopParams, binopTyp,
        binopClauseADD :: binopClauseSUB :: binopClauseMUL ::
        binopClauseDIV :: binopClauseREM :: binopClauseAND :: rest) :=
  ⟨_, rfl⟩

/-- The `AND` opcode, as a value. -/
def andV : Value := Execution.caseNilV "AND"

/-- The argument values a call `$binop_(I32, AND, c_1, c_2)` evaluates to. -/
def andArgs (nt c₁ c₂ : Value) : List ArgV :=
  [.val nt, .val andV, .val c₁, .val c₂]

/-- The type pattern of every `$binop_` clause is a `SubE` of a fresh variable,
so it matches any value in the subtype (`argSubOk`) and binds `Inn` to it. -/
theorem matchArg_InnPat {env : Env} {ρ : VarEnv} {t₁ t₂ : Typ} {v : Value}
    (hx : ρ.findVal? "Inn" = none) (hs : argSubOk env ρ (.subE (.varE "Inn") t₁ t₂) v = true) :
    MatchArg env ρ (.expA (.subE (.varE "Inn") t₁ t₂)) (.val v) (ρ.bindVal "Inn" v) :=
  matchArg_expA (Validation.matchExp_sub_iff.2
    ((Execution.matchExp_freshVar_iff hx).2 rfl)) hs

/-- An argument whose subtype test fails definitely does not match. -/
theorem matchArg_expA_undef_of_sub {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (hs : argSubOk env ρ e v = false) :
    ∃ n, matchArg n env ρ (.expA e) (.val v) = .error .undef :=
  ⟨1, by simp [matchArg, hs]⟩

/-- A clause whose opcode is not `AND` is skipped at `$binop_(I32, AND, …)`. -/
theorem binopSkip {env : Env} {t₁ t₂ : Typ} {op : MixopS} {inner : Exp}
    {pats : List Arg} {nt c₁ c₂ : Value}
    (hop : ¬ (("AND" : MixopS) = op))
    (hpats : pats = [.expA (.subE (.varE "Inn") t₁ t₂), .expA (.caseE op inner),
      .expA (.varE "i_1"), .expA (.varE "i_2")]) :
    MatchArgsUndef env VarEnv.empty pats (andArgs nt c₁ c₂) := by
  subst hpats
  cases hs : argSubOk env VarEnv.empty (.subE (.varE "Inn") t₁ t₂) nt with
  | false => exact matchArgs_cons_undef (matchArg_expA_undef_of_sub hs)
  | true =>
      exact matchArgs_cons_undef_tail (matchArg_InnPat (by simp) hs)
        (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef_of_ne hop)))

/-- The `Inn` argument pattern of `$binop_`'s integer clauses. -/
abbrev innPatE : Exp := .subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])

set_option maxRecDepth 4000000 in
/-- **`i32.and` is stuck at the pin.**  `$binop_` dispatches past `ADD`, `SUB`,
`MUL`, `DIV` and `REM` — each fails on the opcode — and reaches the `AND`
clause, whose patterns *do* match.  Its body is `$iand_(…)`, which the pinned
script leaves `hint(builtin)` with no clause, so the body is undefined; and
`tryClauses` does not fall through when a clause's **body** fails.  Hence the
call denotes nothing, at any argument whose type passes the `Inn` pattern's
subtype test (`argSubOk`; `I32` and `I64` do). -/
theorem not_applies_binop_and_pinned (nt c₁ c₂ : Value)
    (hnt : argSubOk (envOfScript Specs.wasm30) VarEnv.empty innPatE nt = true) :
    ∀ u, ¬ Applies (envOfScript Specs.wasm30) "binop_" (andArgs nt c₁ c₂) u := by
  obtain ⟨rest, hd⟩ := binopDef_wasm30
  refine not_applies_of_notTryClauses hd (by simp [Builtins.none]) ?_
  intro u
  unfold binopClauseADD binopClauseSUB binopClauseMUL binopClauseDIV binopClauseREM
    binopClauseAND
  rw [tryClauses_cons_iff_of_skip (binopSkip (by decide) rfl),
    tryClauses_cons_iff_of_skip (binopSkip (by decide) rfl),
    tryClauses_cons_iff_of_skip (binopSkip (by decide) rfl),
    tryClauses_cons_iff_of_skip (binopSkip (by decide) rfl),
    tryClauses_cons_iff_of_skip (binopSkip (by decide) rfl)]
  refine not_tryClauses_of_bodyUndef (ρ₀ := ((VarEnv.empty.bindVal "Inn"
      nt).bindVal "i_1" c₁).bindVal "i_2" c₂) ?_ premsHold_nil ?_
  · exact matchArgs_cons (matchArg_InnPat (by simp) hnt)
      (matchArgs_cons (matchArg_expA ((Execution.matchExp_caseNil_iff).2 ⟨rfl, rfl⟩))
        (matchArgs_cons (matchArg_expA ((Execution.matchExp_freshVar_iff (by simp)).2 rfl))
          (matchArgs_cons (matchArg_expA ((Execution.matchExp_freshVar_iff (by simp)).2 rfl))
            matchArgs_nil)))
  · intro w hw
    obtain ⟨vs, hvs, -⟩ := evalExp_listE_iff.1 hw
    obtain ⟨y, ys, -, hy, -⟩ := Validation.evalExps_cons_iff.1 hvs
    exact not_callDef_of_nil (x := "iand_") rfl rfl (fun _ => by simp [Builtins.none])
      (evalExp_callE_iff.1 hy)

/-! ## The other side: with an interpretation, `i32.and` steps

The same walk, at `wasm30WithWasmNumerics`.  The five skips are unchanged —
they are statements about the opcode patterns, not about the environment — and
the `AND` clause's patterns match exactly as before.  What changes is its
*body*: `$iand_(sizenn(Inn), i_1, i_2)` now denotes something, because
`wasmIntBuiltins` interprets `$iand_`.

`$sizenn` and `$size` are ordinary defined functions and are evaluated as
written: `$sizenn(I32) = $size(I32) = 32`.  Nothing is special-cased. -/

/-- `$size`'s `I32` clause, which is its first. -/
def sizeClauseI32 : Clause :=
  .defD [] [(.expA (.caseE "I32" (.tupE [])))] (.numE (.natN 32)) []

/-- `$sizenn`'s only clause: it defers to `$size`. -/
def sizennClause : Clause :=
  .defD [(.expP "nt" (.varT "numtype" []))] [(.expA (.varE "nt"))]
    (.callE "size" [(.expA (.varE "nt"))]) []

set_option maxRecDepth 4000000 in
/-- **Provenance** for `$size`: its first clause is the `I32` one. -/
theorem sizeDef_wasm30 :
    ∃ ps t rest, (envOfScript Specs.wasm30).findDef? "size"
      = some (ps, t, sizeClauseI32 :: rest) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 4000000 in
/-- **Provenance** for `$sizenn`. -/
theorem sizennDef_wasm30 :
    ∃ ps t, (envOfScript Specs.wasm30).findDef? "sizenn" = some (ps, t, [sizennClause]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1000000 in
/-- `$size(I32)` is `32`. -/
theorem callDef_size_i32 {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "size" = none)
    (ha : EvalArgs wasm30WithWasmNumerics ρ args [.val Execution.i32V]) :
    CallDef wasm30WithWasmNumerics ρ "size" args (natV 32) := by
  obtain ⟨ps, t, rest, hd⟩ := sizeDef_wasm30
  refine callDef_of_tryClauses hρ (by rw [findDef?_wasm30WithWasmNumerics]; exact hd) ha ?_
  exact tryClauses_hit (ρ₀ := VarEnv.empty)
    (matchArgs_cons (matchArg_expA ((Execution.matchExp_caseNil_iff).2 ⟨rfl, rfl⟩))
      matchArgs_nil)
    premsHold_nil (evalExp_num)

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1000000 in
/-- `$sizenn(I32)` is `32`, through `$size`. -/
theorem callDef_sizenn_i32 {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "sizenn" = none)
    (ha : EvalArgs wasm30WithWasmNumerics ρ args [.val Execution.i32V]) :
    CallDef wasm30WithWasmNumerics ρ "sizenn" args (natV 32) := by
  obtain ⟨ps, t, hd⟩ := sizennDef_wasm30
  refine callDef_of_tryClauses hρ (by rw [findDef?_wasm30WithWasmNumerics]; exact hd) ha ?_
  refine tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "nt" Execution.i32V)
    (matchArgs_cons (matchArg_expA ((Execution.matchExp_freshVar_iff (by simp)).2 rfl))
      matchArgs_nil)
    premsHold_nil ?_
  exact evalExp_callE_iff.2 (callDef_size_i32 rfl
    (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- **`i32.and` steps, with Silmaril's numerics installed.**  The dispatch is
the specification's own — `ADD`, `SUB`, `MUL`, `DIV`, `REM` are skipped on the
opcode and the `AND` clause fires — and only the primitive `$iand_` comes from
outside.  Compare `not_applies_binop_and_pinned`: the same call, at the same
script, denotes nothing when no interpretation is installed. -/
theorem applies_binop_and_wasmBuiltins (i₁ i₂ : BitVec 32) :
    Applies wasm30WithWasmNumerics "binop_"
      (andArgs Execution.i32V (bvV i₁) (bvV i₂))
      (.list [bvV (Wasm.Numerics.iand_ 32 i₁ i₂)]) := by
  obtain ⟨rest, hd⟩ := binopDef_wasm30
  refine ⟨binopParams, binopTyp, _, by rw [findDef?_wasm30WithWasmNumerics]; exact hd, Or.inl ?_⟩
  unfold binopClauseADD binopClauseSUB binopClauseMUL binopClauseDIV binopClauseREM
    binopClauseAND
  refine tryClauses_skip_match (binopSkip (by decide) rfl)
    (tryClauses_skip_match (binopSkip (by decide) rfl)
      (tryClauses_skip_match (binopSkip (by decide) rfl)
        (tryClauses_skip_match (binopSkip (by decide) rfl)
          (tryClauses_skip_match (binopSkip (by decide) rfl) ?_))))
  refine tryClauses_hit (ρ₀ := ((VarEnv.empty.bindVal "Inn" Execution.i32V).bindVal "i_1"
      (bvV i₁)).bindVal "i_2" (bvV i₂))
    (matchArgs_cons (matchArg_InnPat (by simp) (by decide))
      (matchArgs_cons (matchArg_expA ((Execution.matchExp_caseNil_iff).2 ⟨rfl, rfl⟩))
        (matchArgs_cons (matchArg_expA ((Execution.matchExp_freshVar_iff (by simp)).2 rfl))
          (matchArgs_cons (matchArg_expA ((Execution.matchExp_freshVar_iff (by simp)).2 rfl))
            matchArgs_nil))))
    premsHold_nil ?_
  refine evalExp_listE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, [], rfl, ?_,
    Validation.evalExps_nil_iff.2 rfl⟩, rfl⟩
  refine evalExp_callE_iff.2 (callDef_of_builtin_nil (x := "iand_")
    (ws := [.val (natV 32), .val (bvV i₁), .val (bvV i₂)]) rfl
    (by rw [findDef?_wasm30WithWasmNumerics]; rfl) ?_ ?_)
  · refine evalArgs_cons ?_ (evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))
    exact evalExp_callE_iff.2 (callDef_sizenn_i32 rfl
      (evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp))) evalArgs_nil))
  · simp [wasm30WithWasmNumerics, Env.withBuiltins, wasmIntBuiltins, natV]

/-! ## The payoff, at the rule

`Equiv/ExecNumeric.lean` characterised `binop-val` exactly, in terms of
`Applies`.  The two results above are the two things `Applies` can do at
`$binop_(I32, AND, …)`, so the rule-level statements follow immediately —
and they are opposite. -/

set_option maxRecDepth 4000000 in
/-- The provenance of the eight numeric rules transfers to the instantiated
environment: installing an interpretation does not touch `findRel?`. -/
theorem hasNumericRules_wasmBuiltins : HasNumericRules wasm30WithWasmNumerics :=
  ⟨⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩⟩

/-- **`i32.and` reduces.**  With Silmaril's numerics installed, `Step_pure`
derives `(CONST I32 i_1) (CONST I32 i_2) (BINOP I32 AND) ~> (CONST I32 c)` with
`c` the bitwise and.  The dispatch is the specification's own; only `$iand_`
comes from outside. -/
theorem derives_binopAnd_wasmBuiltins (i₁ i₂ : BitVec 32) :
    Derives wasm30WithWasmNumerics "Step_pure" "%~>%" []
      (Execution.stepV
        [Execution.constV Execution.i32V (bvV i₁),
         Execution.constV Execution.i32V (bvV i₂),
         binopV Execution.i32V andV]
        [Execution.constV Execution.i32V (bvV (Wasm.Numerics.iand_ 32 i₁ i₂))]) :=
  Validation.derives_of_ruleAt hasNumericRules_wasmBuiltins.binopVal
    (ruleFires_binopVal_iff.2
      ⟨_, _, _, _, _, _, rfl, applies_binop_and_wasmBuiltins i₁ i₂, by simp [memValue]⟩)

/-- **…and at the pin it does not.**  `binop-val` cannot fire on any
configuration whose operator is `AND`: the first thing it wants is a value in
`$binop_`'s result, and the pinned script gives that call no result at all.
With `binop-trap` — which wants the result to be `eps` — ruled out the same
way, `i32.and` is a *stuck* configuration of the specification as published:
not a value, not a trap. -/
theorem not_ruleFires_binopAnd_pinned {nt c₁ c₂ : Value} {js : List Value}
    (hnt : argSubOk (envOfScript Specs.wasm30) VarEnv.empty innPatE nt = true) :
    ¬ RuleFires (envOfScript Specs.wasm30) "%~>%" [] []
        (Execution.stepV [Execution.constV nt c₁, Execution.constV nt c₂, binopV nt andV] js)
        binopValRule := by
  refine not_ruleFires_binopVal_of_undefined
    (P := fun ws => ∃ d₁ d₂, ws = andArgs nt d₁ d₂) ?_
    (fun ws hws w => by
      obtain ⟨d₁, d₂, rfl⟩ := hws; exact not_applies_binop_and_pinned _ _ _ hnt w)
  rintro mt op d₁ d₂ c heq
  refine ⟨d₁, d₂, ?_⟩
  simp only [Execution.stepV, Execution.constV, binopV, Value.tuple.injEq, Value.list.injEq,
    List.cons.injEq, Value.case.injEq, and_true, true_and] at heq
  obtain ⟨⟨⟨hmt, -⟩, ⟨-, -⟩, -, hop⟩, -⟩ := heq
  simp only [andArgs, hop, hmt]

end Silmaril.SpecTec.Equiv.ExecBuiltins
