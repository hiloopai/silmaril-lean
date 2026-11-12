module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Backward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Table
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Backward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Tags
public import Silmaril.Wasm.SpecTec.Sim.BwdRead.Defs

/-!
# Inverting the state accessors

The backward lemmas for `Step_read` 23–102 read a premise such as `$local(z, x) = ?(val)` back
into Core's side condition. Evaluation is a function (`EvalExp.unique`), so a premise that
*holds* pins down the value of each accessor; what is needed is the converse of the forward
evaluation lemmas of family M (`State.evalExp_local`, `evalExp_table`, …): if the accessor
evaluates at all, it evaluates to the entry the forward lemma names, and that entry exists.

* `evalExp_call1_inv`: a call of a single-clause, premise-free definition that `B` does not
  interpret evaluates to what its body does, in the scope of its argument patterns.
* `evalExp_local_inv`, `evalExp_storeAcc_inv`: the accessors `$local` and `$global`/`$table`/
  `$mem`/`$elem`/`$data`, inverted on an encoded state.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff evalArgs_unique)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open State (HasClause1 StateDefs zxPat idxPayload storeAccBody accScope idxV)

/-- Matching is a function of its fuel. -/
theorem matchArgs_unique {env : Env} {ρ ρ₁ ρ₂ : VarEnv} {pats : List Arg} {ws : List ArgV}
    (h₁ : MatchArgs env ρ pats ws ρ₁) (h₂ : MatchArgs env ρ pats ws ρ₂) : ρ₁ = ρ₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e₁ := matchArgs_ok_of_le (le_max_left n₁ n₂) h₁
  have e₂ := matchArgs_ok_of_le (le_max_right n₁ n₂) h₂
  rw [e₁] at e₂
  exact Except.ok.inj e₂

/-- **A one-clause, premise-free clause list, inverted**: its value is the body's, in the scope
the patterns bind. -/
theorem tryClauses_one_inv {env : Env} {q : List Param} {pats : List Arg} {body : Exp}
    {ws : List ArgV} {v : Value} (h : TryClauses env [.defD q pats body []] ws v) :
    ∃ ρ₀, MatchArgs env VarEnv.empty pats ws ρ₀ ∧ EvalExp env ρ₀ body v := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [tryClauses] at hn
  | succ m =>
    cases m with
    | zero => simp [tryClauses, matchArgs, Res.elimUndef, Bind.bind, Except.bind] at hn
    | succ k =>
      rw [tryClauses] at hn
      cases hA : matchArgs (k + 1) env VarEnv.empty pats ws with
      | ok ρ₀ =>
        have hb : evalExp (k + 1) env ρ₀ body = .ok v := by
          simpa [hA, Bind.bind, Except.bind, premsHold_nil_eq] using hn
        exact ⟨ρ₀, ⟨k + 1, hA⟩, ⟨k + 1, hb⟩⟩
      | error e =>
        cases e <;> simp [hA, Bind.bind, Except.bind, Res.elimUndef, tryClauses] at hn

/-- **A call of a single-clause, premise-free definition, inverted**, when `B` has no entry for
it at the argument values. -/
theorem evalExp_call1_inv {env : Env} {ρ : VarEnv} {x : IL.Id} {pats args : List Arg}
    {ws : List ArgV} {body : Exp} {v : Value} (hd : HasClause1 env x pats body)
    (hρ : ρ.findDef? x = none) (hb : env.builtins.call x ws = none)
    (ha : EvalArgs env ρ args ws) (h : EvalExp env ρ (.callE x args) v) :
    ∃ ρ₀, MatchArgs env VarEnv.empty pats ws ρ₀ ∧ EvalExp env ρ₀ body v := by
  obtain ⟨ps, t, q, hf⟩ := hd
  obtain ⟨ws', ps', t', cs, ha', hf', hc⟩ := callDef_iff.1 (evalExp_callE_iff.1 h)
  have hws : ws' = ws := evalArgs_unique ha' ha
  have hx : (ρ.findDef? x).getD x = x := by rw [hρ]; rfl
  have hcs : cs = [.defD q pats body []] := by
    rw [hx, hf] at hf'
    exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hf')).2).2.symm
  rw [hcs, hws, hx] at hc
  rcases hc with hc | ⟨-, hc⟩
  · exact tryClauses_one_inv hc
  · exact absurd (hb.symm.trans hc) (by simp)

/-! ## The accessors, inverted -/

section Accessors

variable {env : Env} (D : StateDefs env) {ρ : VarEnv} {ez ex : Exp} {S F : Value} {n : Nat}
include D

omit D in
/-- The arguments `z, x` of an accessor, evaluated, and its clause's scope. -/
theorem accScope_of {acc : IL.Id} {body : Exp} {r : Value} (hd : HasClause1 env acc zxPat body)
    (hρ : ρ.findDef? acc = none)
    (hb : env.builtins.call acc [.val (stV S F), .val (idxV n)] = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (idxV n))
    (h : EvalExp env ρ (.callE acc [.expA ez, .expA ex]) r) :
    EvalExp env (accScope (stV S F) (idxV n)) body r := by
  obtain ⟨ρ₀, hm, he⟩ := evalExp_call1_inv hd hρ hb
    (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil)) h
  have e : ρ₀ = accScope (stV S F) (idxV n) := matchArgs_unique hm State.matchArgs_zxPat
  exact e ▸ he

omit D in
/-- `x!%.0` in an accessor's scope. -/
theorem idxPayload_inv {Z : Value} {i : Nat}
    (h : EvalExp env (accScope Z (idxV n)) idxPayload (.num (.natN i))) : i = n := by
  have e := EvalExp.unique h (State.evalExp_idxPayload rfl)
  simpa using e

/-- **`$local(z, x)`, inverted.** -/
theorem evalExp_local_inv {r : Value} (hρ : ρ.findDef? "local" = none)
    (hb : env.builtins.call "local" [.val (stV S F), .val (idxV n)] = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (idxV n))
    (h : EvalExp env ρ (.callE "local" [.expA ez, .expA ex]) r) :
    ∃ L, F.field? "LOCALS" = some L ∧ L.idx? n = some r := by
  obtain ⟨L, i, hL, hi, hr⟩ := evalExp_idxE_iff.1 (accScope_of D.local_ hρ hb hz hx h)
  obtain ⟨F', hF', hfl⟩ := evalExp_dotE_iff.1 hL
  have eF : F' = F := EvalExp.unique hF' (State.evalExp_fof D rfl (evalExp_var rfl))
  have ei : i = n := idxPayload_inv hi
  exact ⟨L, eF ▸ hfl, ei ▸ hr⟩

/-- **A store accessor (`$global`, `$table`, `$mem`, `$elem`, `$data`), inverted**: the frame's
module lists an address `a` at index `n` of field `Fl`, and the store's `Fl` entry `a` is the
result. -/
theorem evalExp_storeAcc_inv {acc : IL.Id} {Fl : AtomS} {r : Value}
    (hd : HasClause1 env acc zxPat (storeAccBody Fl)) (hρ : ρ.findDef? acc = none)
    (hb : env.builtins.call acc [.val (stV S F), .val (idxV n)] = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (idxV n))
    (h : EvalExp env ρ (.callE acc [.expA ez, .expA ex]) r) :
    ∃ Ls M As a, S.field? Fl = some Ls ∧ F.field? "MODULE" = some M ∧ M.field? Fl = some As ∧
      As.idx? n = some (.num (.natN a)) ∧ Ls.idx? a = some r := by
  obtain ⟨Ls, a, hLs, ha, hr⟩ := evalExp_idxE_iff.1 (accScope_of hd hρ hb hz hx h)
  obtain ⟨S', hS', hfS⟩ := evalExp_dotE_iff.1 hLs
  have eS : S' = S := EvalExp.unique hS' (State.evalExp_sof D rfl (evalExp_var rfl))
  obtain ⟨As, i, hAs, hi, hai⟩ := evalExp_idxE_iff.1 ha
  obtain ⟨M, hM, hfM⟩ := evalExp_dotE_iff.1 hAs
  obtain ⟨F', hF', hfF⟩ := evalExp_dotE_iff.1 hM
  have eF : F' = F := EvalExp.unique hF' (State.evalExp_fof D rfl (evalExp_var rfl))
  have ei : i = n := idxPayload_inv hi
  exact ⟨Ls, M, As, a, eS ▸ hfS, eF ▸ hfF, hfM, ei ▸ hai, hr⟩

end Accessors

/-- Reading an address list and an encoded instance list back. -/
theorem idx_idx_map_inv {α : Type} {l₁ : List Nat} {l₂ : List α} {enc : α → Value} {n a : Nat}
    {r : Value} (h₁ : (Value.list (l₁.map fun a => .num (.natN a))).idx? n = some (.num (.natN a)))
    (h₂ : (Value.list (l₂.map enc)).idx? a = some r) :
    ∃ t, l₁[n]? = some a ∧ l₂[a]? = some t ∧ r = enc t := by
  have e₁ : (l₁[n]?).map (fun a => Value.num (.natN a)) = some (.num (.natN a)) := by
    simpa [Value.idx?] using h₁
  have e₂ : (l₂[a]?).map enc = some r := by simpa [Value.idx?] using h₂
  obtain ⟨a', ha', ea⟩ := Option.map_eq_some_iff.1 e₁
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 e₂
  have : a' = a := by simpa using ea
  exact ⟨t, this ▸ ha', ht, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.BwdRead
