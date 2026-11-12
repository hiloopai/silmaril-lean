module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef.Host

/-!
# Round 5, pass 2, track fwdref: `$concatn_` over equal-length chunks

```
def $concatn_(syntax X, eps, n) = eps
def $concatn_(syntax X, (w^n) (w'^n)*, n) = w^n $concatn_(X, (w'^n)*, n)
```

The second clause's list pattern `[w^n] ++ (w'^n)*` splits off one element (`patLen` of a
one-element list is `1`); `w^n` binds `n` to that element's length (the counter of a `^n`
pattern is itself a pattern, matched against the length), and each `w'^n` then *tests* its
element's length against the bound `n`. So on a list of chunks of one length `k`, with `k` as
the third argument, the clauses compute the concatenation (`tryClauses_concatn`, by induction on
the chunks), in every environment that has the script's definition and no global type named `X`
(`ConcatnDefs`, `concatnDefs_simEnv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.Execution (MatchIterList MatchRounds matchExp_freshVar_iff
  matchExp_boundVar_iff matchIterList_single_iff bindsVar_varE iterCols_single
  findVals?_bindVal_single matchRounds_ok_of_le matchExp_iterE_listN_iff matchExp_catE_ofLeft
  patLen_listE matchExps_one_iff)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-- Binding a type leaves the value bindings alone. -/
@[simp] theorem findVal?_bindTyp (ρ : VarEnv) (x y : IL.Id) (T : Typ) :
    (ρ.bindTyp x T).findVal? y = ρ.findVal? y := rfl

/-! ## The definition -/

/-- `w^n` over `w*`. -/
abbrev wNE : Exp := .iterE (.varE "w") (.mk (.listN (.varE "n") none) [.mk "w" (.varE "w*")])
/-- `w'^n` over `w'*`. -/
abbrev w'NE : Exp := .iterE (.varE "w'") (.mk (.listN (.varE "n") none) [.mk "w'" (.varE "w'*")])
/-- `(w'^n)*` over `w'**`. -/
abbrev w'NStarE : Exp := .iterE w'NE (.mk .list [.mk "w'*" (.varE "w'**")])

/-- The argument patterns of the first clause. -/
abbrev concatnPats₁ : List Arg := [.typA (.varT "X" []), .expA (.listE []), .expA (.varE "n")]
/-- The argument patterns of the second clause. -/
abbrev concatnPats₂ : List Arg :=
  [.typA (.varT "X" []), .expA (.catE (.listE [wNE]) w'NStarE), .expA (.varE "n")]
/-- The body of the second clause. -/
abbrev concatnBody₂ : Exp :=
  .catE wNE (.callE "concatn_" [.typA (.varT "X" []), .expA w'NStarE, .expA (.varE "n")])

/-- What the evaluation of `$concatn_` needs of an environment. -/
structure ConcatnDefs (env : Env) : Prop where
  /-- The two clauses, as the script has them (quantifiers left open). -/
  defn : ∃ ps t q₁ q₂, env.findDef? "concatn_" = some (ps, t,
    [.defD q₁ concatnPats₁ (.listE []) [], .defD q₂ concatnPats₂ concatnBody₂ []])
  /-- `X` is a pattern variable, not a global type. -/
  noX : env.memTyp "X" = false

set_option maxRecDepth 100000 in
/-- **`simEnv B` has them.** -/
theorem concatnDefs_simEnv (B : Builtins) : ConcatnDefs (simEnv B) :=
  ⟨⟨_, _, _, _, rfl⟩, rfl⟩

/-! ## Matching -/

/-- A type-variable pattern that is neither bound nor global binds. -/
theorem matchArg_typVar {env : Env} {ρ : VarEnv} {x : IL.Id} {T : Typ}
    (hx : ρ.findTyp? x = none) (hg : env.memTyp x = false) :
    MatchArg env ρ (.typA (.varT x [])) (.typ T) (ρ.bindTyp x T) :=
  ⟨1, by simp [matchArg, matchTypV, hx, hg]⟩

/-- **A one-domain list iteration whose body binds its variable at every element** matches the
list by binding the domain. The forward half of `matchIterList_single_iff`, for a body that binds
only on the values matched. -/
theorem matchRounds_on {env : Env} {ρ : VarEnv} {e : Exp} {x : IL.Id} (hx' : x ≠ "_") :
    ∀ (i : Nat) (vs : List Value), (∀ v ∈ vs, MatchExp env ρ e v (ρ.bindVal x v)) →
      MatchRounds env ρ e [x] none i vs (vs.map fun v => [v])
  | _, [], _ => ⟨1, by simp only [matchRounds, List.map_nil]⟩
  | i, v :: vs, hb => by
    obtain ⟨n₁, h₁⟩ := hb v (List.mem_cons_self ..)
    obtain ⟨n₂, h₂⟩ := matchRounds_on hx' (i + 1) vs fun w hw => hb w (List.mem_cons_of_mem _ hw)
    refine ⟨max n₁ n₂ + 1, ?_⟩
    have e1 := Silmaril.SpecTec.Equiv.Validation.matchExp_ok_mono (m := n₁) (n := max n₁ n₂)
      (by omega) h₁
    have e2 := matchRounds_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) h₂
    simp only [matchRounds, e1, Bind.bind, Except.bind, findVals?_bindVal_single hx',
      Res.ofOption, e2, List.map_cons]

/-- The list iteration itself (`matchExp` on `e*`). -/
theorem matchExp_iterList_on {env : Env} {ρ ρ' : VarEnv} {e : Exp} {x y : IL.Id} {vs : List Value}
    (hx' : x ≠ "_") (hb : ∀ v ∈ vs, MatchExp env ρ e v (ρ.bindVal x v))
    (hy : MatchExp env ρ (.varE y) (.list vs) ρ') :
    MatchExp env ρ (.iterE e (.mk .list [.mk x (.varE y)])) (.list vs) ρ' := by
  obtain ⟨n₁, h₁⟩ := matchRounds_on hx' 0 vs hb
  obtain ⟨n₂, h₂⟩ := Silmaril.SpecTec.Equiv.Validation.matchExps_cons_iff.2
    ⟨Value.list vs, [], ρ', rfl, hy, Silmaril.SpecTec.Equiv.Validation.matchExps_nil_iff.2
      ⟨rfl, rfl⟩⟩
  have e1 := matchRounds_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) h₁
  have e2 := Silmaril.SpecTec.Equiv.Validation.matchExps_ok_of_le (m := n₂) (n := max n₁ n₂)
    (by omega) h₂
  refine ⟨max n₁ n₂ + 3, ?_⟩
  simp only [matchExp, matchIterE, Value.asList?_list, Res.ofOption, Bind.bind, Except.bind,
    matchIterList, List.map_cons, List.map_nil, domVar, domSrc, List.length_cons,
    List.length_nil, Nat.zero_add, e1, iterCols_single, e2]

/-- `w'^n` matches a chunk of length `n`, binding `w'*`. -/
theorem matchExp_w'N {env : Env} {ρ : VarEnv} {d : List Value}
    (hn : ρ.findVal? "n" = some (.num (.natN d.length))) (hw : ρ.findVal? "w'" = none)
    (hws : ρ.findVal? "w'*" = none) :
    MatchExp env ρ w'NE (.list d) (ρ.bindVal "w'*" (.list d)) :=
  matchExp_iterE_listN_iff.2 ⟨d, ρ, rfl, (matchExp_boundVar_iff hn).2 ⟨rfl, rfl⟩,
    (matchIterList_single_iff (bindsVar_varE _) hw (by decide)).2
      ((matchExp_freshVar_iff hws).2 rfl)⟩

/-- `(w'^n)*` matches chunks of length `n`, binding `w'**`. -/
theorem matchExp_w'NStar {env : Env} {ρ : VarEnv} {k : Nat} {ds : List (List Value)}
    (hk : ∀ d ∈ ds, d.length = k) (hn : ρ.findVal? "n" = some (.num (.natN k)))
    (hw : ρ.findVal? "w'" = none) (hws : ρ.findVal? "w'*" = none)
    (hwss : ρ.findVal? "w'**" = none) :
    MatchExp env ρ w'NStarE (.list (ds.map .list)) (ρ.bindVal "w'**" (.list (ds.map .list))) := by
  refine matchExp_iterList_on (by decide) ?_ ((matchExp_freshVar_iff hwss).2 rfl)
  intro v hv
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
  exact matchExp_w'N (by rw [hn, hk d hd]) hw hws

/-- The clause-2 scope. -/
abbrev concatnScope (T : Typ) (k : Nat) (c : List Value) (ds : List (List Value)) : VarEnv :=
  (((VarEnv.empty.bindTyp "X" T).bindVal "n" (.num (.natN k))).bindVal "w*" (.list c)).bindVal
    "w'**" (.list (ds.map .list))

/-- The second clause's patterns, on a non-empty list of chunks of length `k`. -/
theorem matchArgs_concatn₂ {env : Env} (D : ConcatnDefs env) (T : Typ) {k : Nat}
    {c : List Value} {ds : List (List Value)} (hc : c.length = k)
    (hk : ∀ d ∈ ds, d.length = k) :
    MatchArgs env VarEnv.empty concatnPats₂ [.typ T, .val (.list (.list c :: ds.map .list)),
      .val (.num (.natN k))] (concatnScope T k c ds) := by
  refine matchArgs_cons (matchArg_typVar rfl D.noX) (matchArgs_cons (matchArg_expA ?_)
    (matchArgs_cons (matchArg_expA ((matchExp_boundVar_iff (by simp)).2 ⟨rfl, rfl⟩))
      matchArgs_nil))
  refine matchExp_catE_ofLeft (j := 1) (m := 1)
    (σ := ((VarEnv.empty.bindTyp "X" T).bindVal "n" (.num (.natN k))).bindVal "w*" (.list c))
    patLen_listE (by simp) ?_ ?_
  · refine Silmaril.SpecTec.Equiv.Validation.matchExp_list_iff.2 ⟨[.list c], by simp,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_iterE_listN_iff.2 ⟨c, _, rfl,
        (matchExp_freshVar_iff (by simp)).2 rfl, ?_⟩⟩⟩
    rw [hc]
    exact (matchIterList_single_iff (bindsVar_varE _) (by simp) (by decide)).2
      ((matchExp_freshVar_iff (by simp)).2 rfl)
  · simpa using matchExp_w'NStar hk (by simp) (by simp) (by simp) (by simp)

/-- The first clause's patterns fail definitely on a non-empty list. -/
theorem matchArgs_concatn₁_undef {env : Env} (D : ConcatnDefs env) (T : Typ) {a : Value}
    {al : List Value} {w : ArgV} :
    MatchArgsUndef env VarEnv.empty concatnPats₁ [.typ T, .val (.list (a :: al)), w] :=
  matchArgs_cons_undef_tail (matchArg_typVar rfl D.noX)
    (matchArgs_cons_undef ⟨3, by simp [matchArg, argSubOk, matchExp, matchExps, Value.asList?,
      Bind.bind, Except.bind]⟩)

/-! ## Evaluation -/

/-- `x^n` with a plain variable body, the counter bound to the domain's length. -/
theorem evalExp_varN {env : Env} {ρ : VarEnv} {x y : IL.Id} (hx : x ≠ "_") {vs : List Value}
    (h : ρ.findVal? y = some (.list vs)) (hm : ρ.findVal? "n" = some (.num (.natN vs.length))) :
    EvalExp env ρ (.iterE (.varE x) (.mk (.listN (.varE "n") none) [.mk x (.varE y)]))
      (.list vs) :=
  Exn.evalExp_iterN_var (d := 1) (fun σ w hw => by simp [evalExp, hw, Res.ofOption]) hx h hm

/-- `(w'^n)*` rebuilds the chunks bound to `w'**`. -/
theorem evalExp_w'NStar {env : Env} {ρ : VarEnv} {k : Nat} {ds : List (List Value)}
    (hk : ∀ d ∈ ds, d.length = k) (hn : ρ.findVal? "n" = some (.num (.natN k)))
    (hwss : ρ.findVal? "w'**" = some (.list (ds.map .list))) :
    EvalExp env ρ w'NStarE (.list (ds.map .list)) := by
  have h := evalExp_iterMap (env := env) (b := w'NE) (x := "w'*") (g := id) hwss (by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
    exact evalExp_varN (by decide) (by simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind])
      (by simpa [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, Map.find?, hk d hd]
        using hn))
  simpa using h

/-- A type argument resolves through the scope. -/
theorem evalArgs_typA {env : Env} {ρ : VarEnv} {t : Typ} {args : List Arg} {ws : List ArgV}
    (hs : EvalArgs env ρ args ws) : EvalArgs env ρ (.typA t :: args) (.typ (resolveTyp ρ t) :: ws) := by
  obtain ⟨n, hs⟩ := hs
  have e2 : args.mapM (evalArg (n + 1) env ρ) = .ok ws := by
    have := evalArgs_ok_of_le (m := n) (n := n + 2) (by omega) hs
    simpa only [evalArgs] using this
  refine ⟨n + 2, ?_⟩
  simp only [evalArgs, List.mapM_cons, evalArg, e2, Bind.bind, Except.bind]
  rfl

/-- **`$concatn_` concatenates chunks of the length it is given.** -/
theorem tryClauses_concatn {env : Env} (D : ConcatnDefs env) (T : Typ) (k : Nat) :
    ∀ ds : List (List Value), (∀ d ∈ ds, d.length = k) →
      ∃ cs, (∃ ps t, env.findDef? "concatn_" = some (ps, t, cs)) ∧
        TryClauses env cs [.typ T, .val (.list (ds.map .list)), .val (.num (.natN k))]
          (.list ds.flatten) := by
  obtain ⟨ps, t, q₁, q₂, hd⟩ := D.defn
  intro ds
  induction ds with
  | nil =>
    intro _
    refine ⟨_, ⟨ps, t, hd⟩, tryClauses_hit (matchArgs_cons (matchArg_typVar rfl D.noX)
      (matchArgs_cons (matchArg_expA (Silmaril.SpecTec.Equiv.Validation.matchExp_list_iff.2
        ⟨[], rfl, Silmaril.SpecTec.Equiv.Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩))
        (matchArgs_cons (matchArg_expA ((matchExp_freshVar_iff (by simp)).2 rfl))
          matchArgs_nil))) premsHold_nil ?_⟩
    exact ⟨3, by simp [evalExp, evalExps]; rfl⟩
  | cons c ds ih =>
    show (∀ d ∈ c :: ds, d.length = k) → ∃ cs, (∃ ps t, env.findDef? "concatn_" = some (ps, t, cs)) ∧
      TryClauses env cs [.typ T, .val (.list ((c :: ds).map .list)), .val (.num (.natN k))]
        (.list (c :: ds).flatten)
    intro hk
    have hc : c.length = k := hk c (List.mem_cons_self ..)
    have hk' : ∀ d ∈ ds, d.length = k := fun d hd => hk d (List.mem_cons_of_mem _ hd)
    obtain ⟨cs, ⟨ps', t', hd'⟩, hrec⟩ := ih hk'
    rw [hd] at hd'
    obtain rfl : _ = cs := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hd')).2).2
    refine ⟨_, ⟨ps, t, hd⟩, tryClauses_skip_match (matchArgs_concatn₁_undef D T)
      (tryClauses_hit (matchArgs_concatn₂ D T hc hk') premsHold_nil ?_)⟩
    have hw : EvalExp env (concatnScope T k c ds) wNE (.list c) :=
      evalExp_varN (by decide) (by simp) (by simp [hc])
    have hargs : EvalArgs env (concatnScope T k c ds)
        [.typA (.varT "X" []), .expA w'NStarE, .expA (.varE "n")]
        [.typ T, .val (.list (ds.map .list)), .val (.num (.natN k))] := by
      have h := evalArgs_typA (env := env) (t := .varT "X" []) (evalArgs_cons (evalExp_w'NStar (ρ := concatnScope T k c ds)
        hk' (by simp) (by simp)) (evalArgs_cons (evalExp_var (ρ := concatnScope T k c ds)
          (x := "n") (v := .num (.natN k)) (by simp)) evalArgs_nil))
      simpa [resolveTyp, VarEnv.findTyp?, VarEnv.bindTyp, VarEnv.bindVal, Map.bind, Map.find?]
        using h
    have hcall : EvalExp env (concatnScope T k c ds)
        (.callE "concatn_" [.typA (.varT "X" []), .expA w'NStarE, .expA (.varE "n")])
        (.list ds.flatten) :=
      evalExp_callE_iff.2 (callDef_of_tryClauses rfl hd hargs hrec)
    exact evalExp_catE_iff.2 ⟨_, _, hw, hcall, by simp [Value.cat?]⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef
