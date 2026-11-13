module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.Utf8Mono.Typ
public import Silmaril.Wasm.SpecTec.Sim20.StoreBulk.Thms

/-!
# `$utf8` in the 2.0 script is below the erratum's primitive

The one non-congruence case of environment monotonicity from the 2.0 script to its `$utf8`
erratum is a call of `$utf8` (`EnvExt.at0`). In the script its five clauses are tried; under the
erratum there are none and the primitive `utf8Call` answers. This file proves, in any environment
whose `$utf8` has the 2.0 clauses (`utf8Clauses20`) and whose `$concat_` has its first clause, that
at every fuel and on every argument list the first answer is below the second in `Res.Le`
(`utf8_le20`):

* on `[[ch]]`, an earlier argument: the clauses are out of fuel at every fuel
  (`tryClauses_utf8_single`, an earlier `tryClauses_utf8_20` for any such environment);
* on any other list, the four one-character clauses do not match (`matchArgs_ch_ne`), so they
  are peeled off (`tryClauses_peelCh`), and the last clause is round 7's first 3.0 clause
  `utf8Clause1`: on `[]` it answers `[]` once it has fuel (`tryClauses_last_nil`); on a list of
  two or more characters its body calls `$utf8` on a singleton, which never returns
  (`body_oofE`, `tryClauses_last_cons`);
* on any other argument list no clause pattern matches, and both
  sides are a definite failure.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Mono

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (utf8Clause1 chsDom utf8Body)
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res concatClause1 clausePats BadArgs OofOrUndef
  matchArgs_clause1 iterRows_cons tryClauses_bad utf8Call_bad)
open Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd (utf8Call)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Clauses20 utf8Clauses20_split tryClauses_badL
  utf8Clauses20_badShape utf8_small20 utf8_step20)

set_option maxRecDepth 100000

variable {env : Env}

/-! ## One character -/

/-- **`$utf8` on a one-element list never returns**, in every environment with the 2.0 clauses
(an earlier `tryClauses_utf8_20`, for any such environment). -/
theorem tryClauses_utf8_single (hd : env.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses20))
    (u : Value) : ∀ n, tryClauses n env utf8Clauses20 [.val (.list [u])] = .error .outOfFuel := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [utf8Clauses20_split]
    rcases tryClauses_badL (env := env) u [utf8Clause1] _ utf8Clauses20_badShape n
      with h | ⟨m, hm, h⟩
    · exact h
    · rw [h]
      have hl : (utf8Clauses20.take 4).length = 4 := rfl
      by_cases hs : m < 12
      · exact utf8_small20 m hs u [] hd
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 12 := ⟨m - 12, by omega⟩
        exact utf8_step20 j u [] hd (ih (j + 1) (by omega))

/-! ## Peeling the one-character clauses on other lists -/

/-- Lists of different lengths do not match. -/
theorem matchExps_len (ρ : VarEnv) : ∀ (n : Nat) (es : List Exp) (vs : List Value),
    es.length ≠ vs.length → OofOrUndef (matchExps n env ρ es vs)
  | 0, _, _, _ => Or.inl (by simp [matchExps])
  | _ + 1, [], [], h => absurd rfl h
  | _ + 1, [], _ :: _, _ => Or.inr (by simp [matchExps])
  | _ + 1, _ :: _, [], _ => Or.inr (by simp [matchExps])
  | n + 1, e :: es, v :: vs, h => by
    simp only [matchExps]
    cases hm : matchExp n env ρ e v with
    | error err => cases err <;> simp [OofOrUndef]
    | ok ρ' =>
      exact matchExps_len ρ' n es vs (by simpa using h)

/-- The pattern `[ch]` does not match a list of any other length. -/
theorem matchArgs_ch_ne (L : List Value) (hL : L.length ≠ 1) :
    ∀ n, OofOrUndef (matchArgs n env VarEnv.empty [.expA (.listE [.varE "ch"])] [.val (.list L)]) := by
  intro n
  rcases n with _ | _ | _ | n
  · simp [OofOrUndef, matchArgs]
  · simp [OofOrUndef, matchArgs, matchArg]
  · simp [OofOrUndef, matchArgs, matchArg, argSubOk, matchExp]
  · have h := matchExps_len (env := env) VarEnv.empty n [.varE "ch"] L (by simpa using hL.symm)
    simp only [matchArgs, matchArg, argSubOk, matchExp, Value.asList?, Res.ofOption, bind_ok]
    rcases h with h | h <;> simp [h, OofOrUndef]

/-- A clause whose pattern is `[ch]`. -/
def ChPat (c : Clause) : Prop := clausePats c = [.expA (.listE [.varE "ch"])]

/-- **Peeling the one-character clauses** on a list of another length: out of fuel, or the rest
at the remaining fuel. -/
theorem tryClauses_peelCh (L : List Value) (hL : L.length ≠ 1) (rest : List Clause) :
    ∀ (cs : List Clause), (∀ c ∈ cs, ChPat c) → ∀ k,
      tryClauses k env (cs ++ rest) [.val (.list L)] = .error .outOfFuel ∨
        ∃ m, m + cs.length = k ∧
          tryClauses k env (cs ++ rest) [.val (.list L)] = tryClauses m env rest [.val (.list L)]
  | [], _, k => Or.inr ⟨k, rfl, rfl⟩
  | c :: cs, hcs, 0 => Or.inl (by simp [tryClauses])
  | c :: cs, hcs, k + 1 => by
    have ih := tryClauses_peelCh L hL rest cs (fun c' h' => hcs c' (List.mem_cons_of_mem _ h')) k
    obtain ⟨q, pats, body, prems⟩ := c
    have hp : pats = [.expA (.listE [.varE "ch"])] := hcs _ List.mem_cons_self
    subst hp
    simp only [List.cons_append, tryClauses]
    rcases matchArgs_ch_ne (env := env) L hL k with h | h
    · exact Or.inl (by simp [h, Res.elimUndef])
    · simp only [h, Res.elimUndef]
      rcases ih with h' | ⟨m, hm, h'⟩
      · exact Or.inl (by simpa using h')
      · exact Or.inr ⟨m, by simp at hm ⊢; omega, by simpa using h'⟩

theorem chPat_take4 : ∀ c ∈ utf8Clauses20.take 4, ChPat c := by
  have h : (utf8Clauses20.take 4).map clausePats =
      List.replicate 4 [.expA (.listE [.varE "ch"])] := rfl
  intro c hc
  exact List.eq_of_mem_replicate (h ▸ List.mem_map_of_mem hc)

/-! ## The last clause -/

theorem utf8_nilE (hc : ∃ ps t rest, env.findDef? "concat_" = some (ps, t, concatClause1 :: rest))
    (hX : env.memTyp "X" = false) :
    tryClauses 12 env [utf8Clause1] [.val (.list [])] = .ok (.list []) := by
  obtain ⟨ps, t, crest, hc⟩ := hc
  simp [tryClauses, utf8Clause1, matchArgs, matchArg, argSubOk, matchExp, chsDom,
    matchIterE, matchIterList, matchRounds, matchExps, premsHold, utf8Body, evalExp, callDef,
    evalArgs, evalArg, evalIterE, evalDoms, evalIterList, evalRounds, Res.ofOption, domVar, domSrc,
    iterCols, iterRows, Res.assert, hc, VarEnv.findDef?, VarEnv.bindVal, VarEnv.bindVals,
    VarEnv.empty, Map.bind, Map.find?, iterCol, VarEnv.findVal?,
    Map.empty, Res.elimUndef, concatClause1, matchTypV, Map.binds, resolveTyp,
    VarEnv.findTyp?, VarEnv.bindTyp, hX, evalExps]
  rfl

/-- On `[[]]` the last clause answers `[]` or is out of fuel. -/
theorem tryClauses_last_nil
    (hc : ∃ ps t rest, env.findDef? "concat_" = some (ps, t, concatClause1 :: rest))
    (hX : env.memTyp "X" = false) (n : Nat) :
    tryClauses n env [utf8Clause1] [.val (.list [])] = .error .outOfFuel ∨
      tryClauses n env [utf8Clause1] [.val (.list [])] = .ok (.list []) := by
  have h12 := utf8_nilE hc hX
  rcases Nat.le_total n 12 with h | h
  · rcases (monoAt_of_le h).tryClauses env [utf8Clause1] [.val (.list [])] with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h'.symm.trans h12)
  · rcases (monoAt_of_le h).tryClauses env [utf8Clause1] [.val (.list [])] with h' | h'
    · exact absurd (h12.symm.trans h') (by simp)
    · exact Or.inr (h12 ▸ h')

/-- The body of the last clause on a non-empty list is out of fuel, when `$utf8` never returns on
its first character. -/
theorem body_oofE {ps : List Param} {t : Typ} {cls : List Clause} (u : Value) (us : List Value)
    (hd : env.findDef? "utf8" = some (ps, t, cls))
    (hT : ∀ m, tryClauses m env cls [.val (.list [u])] = .error .outOfFuel) :
    ∀ m, evalExp m env (VarEnv.empty.bindVal "ch*" (.list (u :: us))) utf8Body =
      .error .outOfFuel := by
  obtain ⟨t', hR⟩ := iterRows_cons u us
  intro m
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;>
  simp [utf8Body, evalExp, callDef, evalArgs, evalArg, evalIterE, evalDoms, chsDom,
    evalIterList, evalRounds, Res.ofOption, domVar, domSrc, Res.assert, hd, VarEnv.findDef?,
    VarEnv.bindVal, VarEnv.bindVals, VarEnv.empty, Map.bind, Map.find?, VarEnv.findVal?,
    Map.empty, Res.elimUndef, hT, Map.binds, hR, evalExps, List.mapM_cons]

/-- On a non-empty list the last clause is out of fuel at every fuel. -/
theorem tryClauses_last_cons {ps : List Param} {t : Typ} {cls : List Clause} (u : Value)
    (us : List Value) (hd : env.findDef? "utf8" = some (ps, t, cls))
    (hT : ∀ m, tryClauses m env cls [.val (.list [u])] = .error .outOfFuel) :
    ∀ n, tryClauses n env [utf8Clause1] [.val (.list (u :: us))] = .error .outOfFuel
  | 0 => by simp [tryClauses]
  | n + 1 => by
      have hb := body_oofE u us hd hT n
      rcases matchArgs_clause1 env (u :: us) n with h | h
      · simp [tryClauses, utf8Clause1, h, Res.elimUndef]
      · rcases n with _ | n
        · simp [tryClauses, utf8Clause1, h, Res.elimUndef, premsHold]
        · simp [tryClauses, utf8Clause1, h, Res.elimUndef, premsHold, hb]

/-! ## `$utf8` below the primitive -/

/-- An environment with the 2.0 `$utf8` and the first clause of `$concat_`. -/
structure Utf8Script20 (env : Env) : Prop where
  utf8 : env.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses20)
  concat : ∃ ps t rest, env.findDef? "concat_" = some (ps, t, concatClause1 :: rest)
  memX : env.memTyp "X" = false
  call : ∀ ws, env.builtins.call "utf8" ws = none

/-- On `[[]]` the 2.0 clauses answer `[]` or are out of fuel. -/
theorem tryClauses_utf8_nil20 (h : Utf8Script20 env) (n : Nat) :
    tryClauses n env utf8Clauses20 [.val (.list [])] = .error .outOfFuel ∨
      tryClauses n env utf8Clauses20 [.val (.list [])] = .ok (.list []) := by
  rw [utf8Clauses20_split]
  rcases tryClauses_peelCh (env := env) [] (by simp) [utf8Clause1] _ chPat_take4 n
    with h' | ⟨m, -, h'⟩
  · exact Or.inl h'
  · rw [h']
    exact tryClauses_last_nil h.concat h.memX m

/-- On a list of two or more characters the 2.0 clauses are out of fuel. -/
theorem tryClauses_utf8_long20
    (hd : env.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses20))
    (u u' : Value) (us : List Value) (n : Nat) :
    tryClauses n env utf8Clauses20 [.val (.list (u :: u' :: us))] = .error .outOfFuel := by
  rw [utf8Clauses20_split]
  rcases tryClauses_peelCh (env := env) (u :: u' :: us) (by simp) [utf8Clause1] _ chPat_take4 n
    with h' | ⟨m, -, h'⟩
  · exact h'
  · rw [h']
    exact tryClauses_last_cons u (u' :: us) hd (tryClauses_utf8_single hd u) m

theorem utf8Clauses20_pats : ∀ c ∈ utf8Clauses20, clausePats c = [.expA (.iterE (.varE "ch") chsDom)] ∨
    clausePats c = [.expA (.listE [.varE "ch"])] := by
  intro c hc
  rw [utf8Clauses20_split] at hc
  rcases List.mem_append.1 hc with hc | hc
  · exact Or.inr (chPat_take4 c hc)
  · obtain rfl := List.mem_singleton.1 hc
    exact Or.inl rfl

/-- **`$utf8` in the 2.0 script is below the erratum's primitive**, at every fuel and on every
argument list. -/
theorem utf8_le20 {env₂ : Env} (h : Utf8Script20 env)
    (h₂ : env₂.findDef? "utf8" = some (utf8Params, utf8Res, []))
    (hc₂ : ∀ ws, env₂.builtins.call "utf8" ws = utf8Call ws) (n : Nat) (ws : List ArgV) :
    callAt n env "utf8" ws ⊑ callAt n env₂ "utf8" ws := by
  simp only [callAt, h.utf8, h₂, hc₂, h.call, Res.ofOption, bind_ok]
  rcases n with _ | n
  · simp only [tryClauses, Res.elimUndef]; exact Res.oof_le _
  rw [show tryClauses (n + 1) env₂ [] ws = .error .undef by simp [tryClauses]]
  simp only [Res.elimUndef]
  by_cases hw : ∃ L, ws = [.val (.list L)]
  · obtain ⟨L, rfl⟩ := hw
    rcases L with _ | ⟨u, _ | ⟨u', us⟩⟩
    · rcases tryClauses_utf8_nil20 h (n + 1) with h' | h' <;> simp only [h']
      · exact Res.oof_le _
      · exact Res.Le.refl _
    · simp only [tryClauses_utf8_single h.utf8 u]; exact Res.oof_le _
    · simp only [tryClauses_utf8_long20 h.utf8]; exact Res.oof_le _
  · have hb : BadArgs ws := fun L h' => hw ⟨L, h'⟩
    rcases tryClauses_bad env ws hb _ utf8Clauses20_pats (n + 1) with h' | h' <;>
      simp only [h', utf8Call_bad hb]
    · exact Res.oof_le _
    · exact Res.Le.refl _

end Silmaril.Wasm.SpecTec.Sim20.Utf8Mono
