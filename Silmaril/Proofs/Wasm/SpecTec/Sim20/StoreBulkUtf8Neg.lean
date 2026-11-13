module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkUtf8

/-!
# Without the erratum: `$utf8` never returns on a one-character name in the 2.0 script

The 2.0 script's `$utf8` (`utf8Clauses20`) has five clauses. The first four match a
one-character list `[ch]` and bind a byte variable (`b`, `b_1`, …) only in their `if` premise,
`ch < … ∧ … = b`. The evaluator does not solve premises: the right conjunct needs the byte
variable, which is unbound, so these clauses never apply (`bad_never_ok`, through a strictness
check `strictB` and `not_evalExp_strict`). The fifth is round 5's `utf8Clause1`,
`$utf8(ch*) = $concat_(byte, $utf8([ch])*)`, which calls `$utf8([ch])` again eleven fuel levels
lower. So on `[u]` the clauses are out of fuel at every fuel (**`tryClauses_utf8_20`**), and
`outOfFuel` never falls back to the primitives.

Consequences, in every `simEnv20 B`:

* **`not_hasTyp_name_single20`**: a one-character name is not a `name`;
* **`not_typedV_moduleInst20_single`**: no module instance exporting a one-character name is a
  `moduleinst`;
* **`not_invokeTy_single`**, **`not_good20B_single`**: `InvokeTy` fails at such a frame, and no
  configuration whose frame's module exports a one-character name is `Good20B`.

So the forward invariant of rounds 5–6 covers only modules whose export names are typed in
`simEnv20` (the empty name is, `typedV_name_nil20`); the erratum `utf8Env20` types every name
within SpecTec's bound (`StoreBulkUtf8`). This is round 5's 3.0 result (`Round5.Pos.tryClauses_utf8`)
for the 2.0 script, whose looping clause comes last rather than first.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT)
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res)
open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (utf8Clause1 chsDom utf8Body ok_bind' err_bind' namePremLhs
  namePrem charDom)

set_option maxRecDepth 100000

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## Strictness: an expression that needs an unbound variable has no value -/

/-- **`e` needs `x`**: evaluating `e` evaluates `x` (the right operand of a short-circuiting
operator excepted). -/
def strictB (x : IL.Id) : Exp → Bool
  | .varE y => y == x
  | .cmpE _ _ a b => strictB x a || strictB x b
  | .binE op _ a b => strictB x a || (!(op == .andOp || op == .orOp || op == .implOp) && strictB x b)
  | .cvtE a _ _ => strictB x a
  | .projE a _ => strictB x a
  | .uncaseE a _ => strictB x a
  | _ => false

/-- **A clause that never applies to `[u]`**: pattern `[ch]`, one premise `l ∧ r`, and `r` needs a
byte variable the pattern does not bind. -/
def badClause : Clause → Bool
  | .defD _ [.expA (.listE [.varE "ch"])] _ [.ifPr (.binE .andOp _ _ r)] =>
      ["b", "b_1", "b_2", "b_3", "b_4"].any (strictB · r)
  | _ => false

/-- The clauses of `$utf8` in the 2.0 script. -/
noncomputable def utf8Clauses20 : List Clause :=
  ((baseEnv20.findDef? "utf8").map (·.2.2)).getD []

theorem findDef_utf8_20 (B : Builtins) : (E20 B).findDef? "utf8" =
    some (utf8Params, utf8Res,
      utf8Clauses20) := rfl

/-- The last clause is round 5's `utf8Clause1`. -/
theorem utf8Clauses20_split : utf8Clauses20 = utf8Clauses20.take 4 ++ [utf8Clause1] := rfl

/-- The first four never apply (checked by evaluation of `badClause`). -/
theorem utf8Clauses20_bad : (utf8Clauses20.take 4).all badClause = true := rfl

/-- The pattern `[ch]` on `[[u]]` binds `ch` or runs out of fuel. -/
theorem matchArgs_ch20 (env : Env) (u : Value) (n : Nat) :
    matchArgs n env VarEnv.empty [.expA (.listE [.varE "ch"])] [.val (.list [u])] =
      .ok (VarEnv.empty.bindVal "ch" u) ∨
    matchArgs n env VarEnv.empty [.expA (.listE [.varE "ch"])] [.val (.list [u])] = .error .outOfFuel := by
  rcases n with _ | _ | _ | _ | _ | n <;>
    simp [matchArgs, matchArg, argSubOk, matchExp, matchExps, Res.ofOption, VarEnv.findVal?, VarEnv.empty, Map.find?, Map.empty]

theorem boolShort_none {op : BinOp} (h : (!(op == .andOp || op == .orOp || op == .implOp)) = true)
    (w : Value) : boolShort op w = none := by
  cases op <;> simp_all [boolShort]

/-- The right operand of a non-short-circuiting operator is evaluated. -/
theorem evalExp_binE_right {env : Env} {ρ : VarEnv} {op : BinOp} {t : OpTyp} {a b : Exp}
    {v : Value} (hop : (!(op == .andOp || op == .orOp || op == .implOp)) = true)
    (he : EvalExp env ρ (.binE op t a b) v) : ∃ v₂, EvalExp env ρ b v₂ := by
  obtain ⟨v₁, -, hs⟩ := evalExp_binE_iff.1 he
  rcases hs with hs | ⟨-, v₂, h₂, -⟩
  · exact absurd hs (by rw [boolShort_none hop]; simp)
  · exact ⟨v₂, h₂⟩

theorem strictB_binE {x : IL.Id} {op : BinOp} {t : OpTyp} {a b : Exp}
    (h : strictB x (.binE op t a b) = true) : strictB x a = true ∨
      ((!(op == .andOp || op == .orOp || op == .implOp)) = true ∧ strictB x b = true) := by
  simpa [strictB] using h

/-- **An expression that needs an unbound variable has no value.** -/
theorem not_evalExp_strict {env : Env} {ρ : VarEnv} {x : IL.Id} (hx : ρ.findVal? x = none) :
    ∀ (e : Exp) (v : Value), strictB x e = true → ¬ EvalExp env ρ e v
  | .varE y, v, h, he => by
    have hy : y = x := by simpa [strictB] using h
    have hv : ρ.findVal? x = some v := hy ▸ evalExp_varE_iff.1 he
    exact absurd (hx.symm.trans hv) (by simp)
  | .cmpE op t a b, v, h, he => by
    obtain ⟨v₁, v₂, h₁, h₂, -⟩ := evalExp_cmpE_iff.1 he
    rcases Bool.or_eq_true_iff.1 (by simpa [strictB] using h) with ha | hb
    · exact not_evalExp_strict hx a v₁ ha h₁
    · exact not_evalExp_strict hx b v₂ hb h₂
  | .binE op t a b, v, h, he => by
    obtain ⟨v₁, h₁, -⟩ := evalExp_binE_iff.1 he
    rcases strictB_binE h with ha | ⟨hop, hb⟩
    · exact not_evalExp_strict hx a v₁ ha h₁
    · obtain ⟨v₂, h₂⟩ := evalExp_binE_right hop he
      exact not_evalExp_strict hx b v₂ hb h₂
  | .cvtE a t₁ t₂, v, h, he => by
    obtain ⟨m, m', h₁, -⟩ := evalExp_cvtE_iff.1 he
    exact not_evalExp_strict hx a _ (by simpa [strictB] using h) h₁
  | .projE a i, v, h, he => by
    obtain ⟨vs, h₁, -⟩ := evalExp_projE_iff.1 he
    exact not_evalExp_strict hx a _ (by simpa [strictB] using h) h₁
  | .uncaseE a op, v, h, he => by
    exact not_evalExp_strict hx a _ (by simpa [strictB] using h) (evalExp_uncaseE_iff.1 he)
  | .boolE _, _, h, _ | .numE _, _, h, _ | .textE _, _, h, _ => absurd h (by simp [strictB])
  | .unE .., _, h, _ => absurd h (by simp [strictB])
  | .tupE .., _, h, _ => absurd h (by simp [strictB])
  | .caseE .., _, h, _ => absurd h (by simp [strictB])
  | .optE .., _, h, _ => absurd h (by simp [strictB])
  | .theE .., _, h, _ => absurd h (by simp [strictB])
  | .strE .., _, h, _ => absurd h (by simp [strictB])
  | .dotE .., _, h, _ => absurd h (by simp [strictB])
  | .compE .., _, h, _ => absurd h (by simp [strictB])
  | .listE .., _, h, _ => absurd h (by simp [strictB])
  | .liftE .., _, h, _ => absurd h (by simp [strictB])
  | .memE .., _, h, _ => absurd h (by simp [strictB])
  | .lenE .., _, h, _ => absurd h (by simp [strictB])
  | .catE .., _, h, _ => absurd h (by simp [strictB])
  | .idxE .., _, h, _ => absurd h (by simp [strictB])
  | .sliceE .., _, h, _ => absurd h (by simp [strictB])
  | .updE .., _, h, _ => absurd h (by simp [strictB])
  | .extE .., _, h, _ => absurd h (by simp [strictB])
  | .callE .., _, h, _ => absurd h (by simp [strictB])
  | .iterE .., _, h, _ => absurd h (by simp [strictB])
  | .subE .., _, h, _ => absurd h (by simp [strictB])

/-- The shape of the four one-character clauses. -/
def BadShape (c : Clause) : Prop :=
  ∃ qs body t l r, c = .defD qs [.expA (.listE [.varE "ch"])] body [.ifPr (.binE .andOp t l r)] ∧
    ∃ y, y ≠ "ch" ∧ strictB y r = true

theorem badClause_spec (c : Clause) (h : badClause c = true) : BadShape c := by
  unfold badClause at h
  split at h
  · rename_i qs body t l r
    obtain ⟨y, hy, hs⟩ := List.any_eq_true.1 h
    refine ⟨qs, body, t, l, r, rfl, y, ?_, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp at h

theorem evalExp_of_premsHold {env : Env} {ρ ρ' : VarEnv} {e : Exp} {n : Nat}
    (h : premsHold n env ρ [.ifPr e] = .ok ρ') : EvalExp env ρ e (.bool true) := by
  rcases n with _ | _ | n
  · simp [premsHold] at h
  · simp [premsHold, premHolds] at h
  · simp only [premsHold, List.foldlM, premHolds] at h
    cases he : evalExp n env ρ e with
    | error err => simp [he] at h
    | ok v =>
      simp only [he] at h
      by_cases hv : v = .bool true
      · exact ⟨n, hv ▸ he⟩
      · simp [Res.assert, hv] at h

theorem evalExp_and_right {env : Env} {ρ : VarEnv} {t : OpTyp} {l r : Exp}
    (h : EvalExp env ρ (.binE .andOp t l r) (.bool true)) : ∃ v, EvalExp env ρ r v := by
  obtain ⟨v₁, -, hs⟩ := evalExp_binE_iff.1 h
  rcases hs with hs | ⟨-, v₂, h₂, -⟩
  · cases v₁ <;> simp [boolShort] at hs
    rename_i b; cases b <;> simp_all
  · exact ⟨v₂, h₂⟩

/-- **A one-character clause never applies**: matching and its premise are out of fuel or a
definite failure. -/
theorem bad_never_ok {env : Env} {q : List Param} {pats : List Arg} {body : Exp}
    {prems : List Prem} (hc : BadShape (.defD q pats body prems)) (n : Nat) (u : Value)
    (ρ₁ : VarEnv) :
    (do let ρ₀ ← matchArgs n env VarEnv.empty pats [.val (.list [u])]
        premsHold n env ρ₀ prems : Res VarEnv) ≠ .ok ρ₁ := by
  obtain ⟨qs, body', t, l, r, hc', y, hy, hs⟩ := hc
  cases hc'
  intro h
  rcases matchArgs_ch20 env u n with hm | hm <;> simp only [hm] at h
  · have he := evalExp_and_right (evalExp_of_premsHold h)
    obtain ⟨v, hv⟩ := he
    refine not_evalExp_strict (x := y) ?_ r v hs hv
    simp [VarEnv.bindVal, VarEnv.findVal?, VarEnv.empty, Map.bind, Map.find?, Map.empty, Ne.symm hy]
  · cases h


/-- Peeling the one-character clauses: out of fuel, or the rest at the remaining fuel. -/
theorem tryClauses_badL {env : Env} (u : Value) (rest : List Clause) :
    ∀ (cs : List Clause), (∀ c ∈ cs, BadShape c) → ∀ k,
      tryClauses k env (cs ++ rest) [.val (.list [u])] = .error .outOfFuel ∨
        ∃ m, m + cs.length = k ∧
          tryClauses k env (cs ++ rest) [.val (.list [u])] = tryClauses m env rest [.val (.list [u])]
  | [], _, k => Or.inr ⟨k, rfl, rfl⟩
  | c :: cs, hcs, 0 => Or.inl (by simp [tryClauses])
  | c :: cs, hcs, k + 1 => by
    have ih := tryClauses_badL (env := env) u rest cs (fun c' h' => hcs c' (List.mem_cons_of_mem _ h')) k
    obtain ⟨q, pats, body, prems⟩ := c
    have hb := bad_never_ok (env := env) (hcs _ List.mem_cons_self) k u
    simp only [List.cons_append, tryClauses]
    cases hX : matchArgs k env VarEnv.empty pats [.val (.list [u])] >>= fun ρ₀ =>
        premsHold k env ρ₀ prems with
    | ok ρ₁ => exact absurd hX (hb ρ₁)
    | error e =>
      cases e with
      | outOfFuel => exact Or.inl (by simp [Res.elimUndef])
      | undef =>
        simp only [Res.elimUndef]
        rcases ih with h | ⟨m, hm, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨m, by simp at hm ⊢; omega, h⟩

/-- `[ch]` evaluates to `[u]` once there is fuel. -/
theorem evalArg_ch20 (env : Env) (m : Nat) (u : Value) (ρ : VarEnv)
    (hρ : ρ.findVal? "ch" = some u) :
    evalArg m env ρ (.expA (.listE [.varE "ch"])) = .ok (.val (.list [u])) ∨
      evalArg m env ρ (.expA (.listE [.varE "ch"])) = .error .outOfFuel := by
  rcases m with _ | _ | _ | _ | m
  · simp [evalArg]
  · simp [evalArg, evalExp]
  · simp [evalArg, evalExp, evalExps]
  · simp [evalArg, evalExp, evalExps]
  · simp [evalArg, evalExp, evalExps, hρ, Res.ofOption]

/-- **The fuel shift**, in any environment: if `$utf8`'s clauses are out of fuel on `[u]` at
`n + 1`, the last clause is at `n + 12`. -/
theorem utf8_step20 {env : Env} (n : Nat) (u : Value) {ps : List Param} {t : Typ}
    {cls : List Clause} (rest : List Clause) (hd : env.findDef? "utf8" = some (ps, t, cls))
    (hT : tryClauses (n + 1) env cls [.val (.list [u])] = .error .outOfFuel) :
    tryClauses (n + 12) env (utf8Clause1 :: rest) [.val (.list [u])] = .error .outOfFuel := by
  simp only [tryClauses, utf8Clause1]
  rcases evalArg_ch20 env n u
    { vals := [("ch", u), ("ch*", Value.list [u])], typs := [], defs := [], grams := [] } rfl
    with he | he <;>
  simp [matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, matchIterList, matchRounds,
    matchExps, premsHold, utf8Body, evalExp, callDef, evalArgs, evalArg, evalIterE, evalDoms,
    evalIterList, evalRounds, Res.ofOption, domVar, domSrc, iterCols, iterRows, Res.assert, hd,
    VarEnv.findDef?, VarEnv.bindVal, VarEnv.bindVals, VarEnv.empty, Map.bind, Map.find?, iterCol,
    VarEnv.findVal?, VarEnv.findVals?, Map.empty, he, hT, Res.elimUndef, iterRow, Map.binds]

/-- Below fuel `12` the last clause runs out of fuel outright. -/
theorem utf8_small20 {env : Env} (k : Nat) (hk : k < 12) (u : Value) {ps : List Param} {t : Typ}
    {cls : List Clause} (rest : List Clause) (hd : env.findDef? "utf8" = some (ps, t, cls)) :
    tryClauses k env (utf8Clause1 :: rest) [.val (.list [u])] = .error .outOfFuel := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
  all_goals simp [tryClauses, utf8Clause1, matchArgs, matchArg, argSubOk, matchExp, chsDom,
    matchIterE, matchIterList, matchRounds, matchExps, premsHold, utf8Body, evalExp, callDef,
    evalArgs, evalArg, evalIterE, evalDoms, evalIterList, evalRounds, Res.ofOption, domVar, domSrc,
    iterCols, iterRows, Res.assert, hd, VarEnv.findDef?, VarEnv.bindVal, VarEnv.bindVals,
    VarEnv.empty, Map.bind, Map.find?, iterCol, VarEnv.findVal?, VarEnv.findVals?,
    Map.empty, premHolds, Res.elimUndef]

theorem utf8Clauses20_badShape : ∀ c ∈ utf8Clauses20.take 4, BadShape c := fun c hc =>
  badClause_spec c (List.all_eq_true.1 utf8Clauses20_bad c hc)

/-- **`$utf8` on a one-element list never returns in the 2.0 script**: its clauses are out of
fuel at every fuel, in every `simEnv20 B`. -/
theorem tryClauses_utf8_20 (B : Builtins) (u : Value) :
    ∀ n, tryClauses n (E20 B) utf8Clauses20 [.val (.list [u])] =
      .error .outOfFuel := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [utf8Clauses20_split]
    rcases tryClauses_badL (env := E20 B) u [utf8Clause1] _ utf8Clauses20_badShape n
      with h | ⟨m, hm, h⟩
    · exact h
    · rw [h]
      have hl : (utf8Clauses20.take 4).length = 4 := rfl
      by_cases hs : m < 12
      · exact utf8_small20 m hs u [] (findDef_utf8_20 B)
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 12 := ⟨m - 12, by omega⟩
        exact utf8_step20 j u [] (findDef_utf8_20 B) (ih (j + 1) (by omega))


/-- `|$utf8([u])|` has no value in `simEnv20 B`, at any fuel. -/
theorem evalExp_namePremLhs20 (B : Builtins) (u : Value) (n : Nat) (v : Value) :
    evalExp n (E20 B) (VarEnv.empty.bindVal "char*" (.list [u]))
      namePremLhs ≠ .ok v := by
  have hd := findDef_utf8_20 B
  have hT := tryClauses_utf8_20 B u
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
  simp [namePremLhs, charDom, evalExp, callDef, evalArgs, evalArg, evalIterE, evalDoms,
    evalIterList, evalRounds, Res.ofOption, domVar, domSrc, Res.assert, hd, VarEnv.findDef?,
    VarEnv.bindVal, VarEnv.bindVals, VarEnv.empty, Map.bind, Map.find?, iterRow, iterRows,
    VarEnv.findVal?, Map.empty, Res.elimUndef, hT, Map.binds]

/-- `name`'s premise fails on a one-character list in `simEnv20 B`. -/
theorem not_evalExp_namePrem20 (B : Builtins) (u : Value) (v : Value) :
    ¬ EvalExp (E20 B) (VarEnv.empty.bindVal "char*" (.list [u]))
      namePrem v := by
  rintro ⟨n, hn⟩
  rcases n with _ | n
  · simp [evalExp] at hn
  · simp only [namePrem, evalExp] at hn
    cases he : evalExp n (E20 B)
        (VarEnv.empty.bindVal "char*" (.list [u])) namePremLhs with
    | ok w => exact evalExp_namePremLhs20 B u n w he
    | error e => rw [he] at hn; cases hn

/-- **A one-character name is not a `name` of `simEnv20 B`**, in any term-only scope. -/
theorem not_hasTyp_name_single20 (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) (u : Value) :
    ¬ HasTyp (E20 B) ρ (.varT "name" []) (.case "%" (.tuple [.list [u]])) := by
  intro h
  have hl : localTyp? ρ "name" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_name20] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := Sim.IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    cases he
    obtain ⟨-, hp⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    exact not_evalExp_namePrem20 B u _ (Sim.ConfigOk.evalExp_of_premsOk_if hp)
  · exact absurd hrest not_hasTypInsts_nil

/-! ## Consequences -/

/-- **A one-character name is not a `name` of `simEnv20 B`.** -/
theorem not_typedV_name_single20 (B : Builtins) (c : Char) :
    ¬ TypedV (E20 B) (.varT "name" []) (nameV (String.singleton c)) := fun h =>
  not_hasTyp_name_single20 B (ρ := VarEnv.empty) ⟨rfl, rfl, rfl⟩ _
    (by simpa [nameV] using h VarEnv.empty ⟨rfl, rfl, rfl⟩)

/-- **No module instance exporting a one-character name is a `moduleinst` of `simEnv20 B`.** -/
theorem not_typedV_moduleInst20_single (B : Builtins) {m : ModuleInst} {x : ExportInst}
    (hx : x ∈ m.exports) {c : Char} (hc : x.name = String.singleton c) :
    ¬ TypedV (E20 B) (.varT "moduleinst" []) (moduleInstV m) := by
  intro h
  have hF := Whole.hasTypFields_of_closed findTyp_moduleinst20 h
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨hE, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  have hx' : TypedV (E20 B) (.varT "exportinst" [])
      (.struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)]) :=
    Whole.typedV_of_empty20 (Sim.typedV_list_iff.1 (Whole.typedV_list_of_empty20 hE) _
      (List.mem_map_of_mem (f := fun x : ExportInst =>
        Value.struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)]) hx) _ ⟨rfl, rfl, rfl⟩)
  have hX := Whole.hasTypFields_of_closed findTyp_exportinst20 hx'
  obtain ⟨hN, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hX
  rw [hc] at hN
  exact not_typedV_name_single20 B c (Whole.typedV_of_empty20 hN)

/-- **`InvokeTy` fails at a frame whose module exports a one-character name.** -/
theorem not_invokeTy_single {H : Type} (B : Builtins) {s : Store H} {f : Frame} {x : ExportInst}
    (hx : x ∈ f.module.exports) {c : Char} (hc : x.name = String.singleton c) :
    ¬ InvokeTy B s f := fun h =>
  not_typedV_moduleInst20_single B hx hc h.frame

/-- **No configuration whose frame's module exports a one-character name is `Good20B`**, at any
profile and host naming. -/
theorem not_good20B_single {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
    {cfg : Config H} {x : ExportInst} (hx : x ∈ cfg.frame.module.exports) {c : Char}
    (hc : x.name = String.singleton c) : ¬ Good20B hn P cfg := by
  intro hg
  obtain ⟨-, hfr⟩ := Whole.typedV_stateV_iff.1 hg.typ.state
  have hF := Whole.hasTypFields_of_closed Whole.findTyp_frame20 hfr
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨hM, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  exact not_typedV_moduleInst20_single _ hx hc (Whole.typedV_of_empty20 hM)

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
