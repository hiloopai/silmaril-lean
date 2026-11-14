module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Typing

/-!
# Their primitives, evaluated by ours

The rules `UN-*`, `BIN-*`, `CMP-NUM` of `Step_exp` compute with `$boolun`, `$boolbin`, `$numun`,
`$numbin` and `$numcmp` (`3-primitives.spectec`). Read by our evaluator, in `fixed`, each of them is
the corresponding operation of `Xl.Num`/`Xl.Bool` as our `Sem` transcribes it, on `nat` and `int`
operands: `boolun_spec`, `boolbin_spec`, `numun_spec`, `numbin_spec`, `numcmp_spec`.

Most cases are closed computations with symbolic payloads (`with_unfolding_all rfl`); the guarded
clauses of `$numbin` (`SUB`, `DIV` on `nat`, `DIV` on `int`) are walked clause by clause.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-! ## Clause lists, deterministically -/

/-- The clauses definitely fail. -/
def TryUndef (env : Env) (cs : List Clause) (ws : List ArgV) : Prop :=
  ∃ n, tryClauses n env cs ws = .error .undef

theorem TryClauses.unique {env : Env} {cs : List Clause} {ws : List ArgV} {v w : Value}
    (h₁ : TryClauses env cs ws v) (h₂ : TryClauses env cs ws w) : v = w := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e₁ := tryClauses_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have e₂ := tryClauses_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  rw [e₁] at e₂
  exact Except.ok.inj e₂

theorem TryUndef.not {env : Env} {cs : List Clause} {ws : List ArgV} {v : Value}
    (h₁ : TryUndef env cs ws) : ¬ TryClauses env cs ws v := by
  rintro ⟨n₂, h₂⟩
  obtain ⟨n₁, h₁⟩ := h₁
  have e₁ := tryClauses_undef_of_le (Nat.le_max_left n₁ n₂) h₁
  have e₂ := tryClauses_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  rw [e₁] at e₂
  cases e₂

/-- The specification of a primitive: its clauses give `f a` when it is defined and fail
definitely when it is not. -/
def Spec (env : Env) (cs : List Clause) (ws : List ArgV) : Option Value → Prop
  | some v => TryClauses env cs ws v
  | none => TryUndef env cs ws

theorem Spec.iff {env : Env} {cs : List Clause} {ws : List ArgV} {o : Option Value}
    (h : Spec env cs ws o) {w : Value} : TryClauses env cs ws w ↔ o = some w := by
  cases o with
  | none => exact ⟨fun hw => absurd hw (TryUndef.not h), fun h' => by cases h'⟩
  | some v =>
      exact ⟨fun hw => congrArg some (TryClauses.unique h hw), fun h' => by cases h'; exact h⟩

theorem tryUndef_skip_match {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV}
    (hm : MatchArgsUndef env VarEnv.empty pats ws) (hrest : TryUndef env cs ws) :
    TryUndef env (.defD q pats e prems :: cs) ws := by
  obtain ⟨n₁, hm⟩ := hm
  obtain ⟨n₂, hrest⟩ := hrest
  refine ⟨max n₁ n₂ + 1, ?_⟩
  have e1 := matchArgs_undef_of_le (m := n₁) (n := max n₁ n₂) (by omega) hm
  have e2 := tryClauses_undef_of_le (m := n₂) (n := max n₁ n₂) (by omega) hrest
  simp only [tryClauses, e1, Bind.bind, Except.bind, Res.elimUndef_undef, e2]

theorem tryUndef_skip_prem {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV} {ρ₀ : VarEnv}
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (hp : PremsUndef env ρ₀ prems)
    (hrest : TryUndef env cs ws) : TryUndef env (.defD q pats e prems :: cs) ws := by
  obtain ⟨n₁, hm⟩ := hm
  obtain ⟨n₂, hp⟩ := hp
  obtain ⟨n₃, hrest⟩ := hrest
  refine ⟨max (max n₁ n₂) n₃ + 1, ?_⟩
  have e1 := matchArgs_ok_of_le (m := n₁) (n := max (max n₁ n₂) n₃) (by omega) hm
  have e2 := premsHold_undef_of_le (m := n₂) (n := max (max n₁ n₂) n₃) (by omega) hp
  have e3 := tryClauses_undef_of_le (m := n₃) (n := max (max n₁ n₂) n₃) (by omega) hrest
  simp only [tryClauses, e1, Bind.bind, Except.bind, e2, Res.elimUndef_undef, e3]

/-! ## Arguments -/

/-- `nat` or `int`. -/
def NatInt : Num → Prop
  | .natN _ => True
  | .intN _ => True
  | _ => False

/-- The arguments of a binary primitive. -/
def args3 (o a b : Value) : List ArgV := [.val o, .val a, .val b]

/-- The arguments of a unary primitive. -/
def args2 (o a : Value) : List ArgV := [.val o, .val a]

/-! ## Skipping clauses whose patterns fail -/

/-- Clause `c` definitely does not match `ws`. -/
def Miss (env : Env) (ws : List ArgV) (c : Clause) : Prop :=
  match c with
  | .defD _ pats _ _ => MatchArgsUndef env VarEnv.empty pats ws

/-- Every clause of `cs` misses `ws`. -/
inductive AllMiss (env : Env) (ws : List ArgV) : List Clause → Prop where
  | nil : AllMiss env ws []
  | cons {c : Clause} {cs : List Clause} : Miss env ws c → AllMiss env ws cs →
      AllMiss env ws (c :: cs)

theorem tryClauses_append_miss {env : Env} {ws : List ArgV} {v : Value} {rest : List Clause} :
    ∀ {pre : List Clause}, AllMiss env ws pre → TryClauses env rest ws v →
      TryClauses env (pre ++ rest) ws v
  | [], _, h => h
  | .defD _ _ _ _ :: _, .cons hm hms, h => tryClauses_skip_match hm (tryClauses_append_miss hms h)

theorem tryUndef_append_miss {env : Env} {ws : List ArgV} {rest : List Clause} :
    ∀ {pre : List Clause}, AllMiss env ws pre → TryUndef env rest ws →
      TryUndef env (pre ++ rest) ws
  | [], _, h => h
  | .defD _ _ _ _ :: _, .cons hm hms, h => tryUndef_skip_match hm (tryUndef_append_miss hms h)

/-- Every clause of a concrete list misses: one closed computation per clause. -/
macro "miss_all" : tactic => `(tactic| repeat (first
  | exact AllMiss.nil
  | refine AllMiss.cons (Exists.intro 10 (by with_unfolding_all rfl)) ?_))

/-! ## `$numbin` -/

/-- The arguments of `$numbin(op, a, b)`. -/
abbrev nbArgs (op : BinOp) (a b : Num) : List ArgV := args3 (encBinOp op) (encNum a) (encNum b)

/-- `$numbin(op, a, b)` is `Num.bin op a b` (encoded), or fails definitely when that is
undefined. -/
abbrev NB (op : BinOp) (a b : Num) : Prop :=
  Spec envF Rules.F.numbinF (nbArgs op a b) ((Num.bin op a b).map encNum)

/-- The scope a clause `(op, C x₁, C' x₂)` of `$numbin` builds. -/
abbrev nbScope (x₁ : IL.Id) (a : Num) (x₂ : IL.Id) (b : Num) : VarEnv :=
  (VarEnv.empty.bindVal x₁ (.num a)).bindVal x₂ (.num b)

/-- A guard `x =/= z` on a numeral other than `z`. -/
theorem evalExp_ne_num {ρ : VarEnv} {x : IL.Id} {m z : Num} {ez : Exp}
    (hx : ρ.findVal? x = some (.num m)) (hz : EvalExp envF ρ ez (.num z)) (h : m ≠ z) :
    EvalExp envF ρ (.cmpE .neOp .boolT (.varE x) ez) (.bool true) := by
  have e := evalExp_ne (t := .boolT) (evalExp_var hx) hz
  have hb : (Value.num m == Value.num z) = false := by simpa using h
  simpa [hb] using e

/-- A guard `x =/= z` on the numeral `z` itself. -/
theorem evalExp_ne_num_self {ρ : VarEnv} {x : IL.Id} {z : Num} {ez : Exp}
    (hx : ρ.findVal? x = some (.num z)) (hz : EvalExp envF ρ ez (.num z)) :
    EvalExp envF ρ (.cmpE .neOp .boolT (.varE x) ez) (.bool false) := by
  simpa using evalExp_ne (t := .boolT) (evalExp_var hx) hz

end Silmaril.Wasm.SpecTec.Meta
