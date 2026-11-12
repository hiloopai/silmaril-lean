module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.BfuncBound
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.SegmentsV1
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Execution
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecNumeric
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10

/-!
# #688 in the byte grammar institution: the pinned `Bfunc` derives `2^32` locals

Discharges `Task.bfunc688PinnedLarge` (`BfuncBound`). The pinned `Bfunc`
(`A-binary.spectec:505-506`) is `local**:Blist(Blocals) expr:Bexpr => ($concat_(local, local**),
expr)` with no premise, and `Blocals` is `n:Bu32 t:Bvaltype => (LOCAL t)^n`. The bytes
`02 (FF FF FF FF 0F 7F) (01 7F) 0B` are two runs, of `2^32 - 1` and `1` `i32` locals, and the empty
expression; their value has `2^32` locals.

Nothing is evaluated on a list of that length: every lemma is proved for symbolic lists and
run lengths and only instantiated at the end (`bfunc_runs`, then `bfunc688PinnedLarge`).

* `hasV1Types_original`, `blocals_shape`, `blist_shape`, `bexpr_shape`, `concat_shape`,
  `bfunc_shape`: the pinned wasm-1.0 environment, by `rfl`.
* `evalExp_iterListN_nodom`: `e^n` with no domain is `n` copies of `e`'s value.
* `matchExp_nested`, `evalExp_nested`: the nested iteration `((x)*)*`, matched against and
  evaluated to a list of lists, at explicit fuel.
* `concat_try`: the two clauses of `$concat_` flatten any list of lists, by induction.
* `blocals_derives`, `blist_two`, `bfunc_two`: the derivations.
* `bfunc_runs`, **`bfunc688PinnedLarge`**, **`bfunc688_separates`**.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts
open Silmaril.Wasm.Binary (U32 UN)
open Silmaril.SpecTec.Equiv (blistParams blistProds)
open Silmaril.SpecTec.Equiv.BinaryModule (Rounds symDerives_iterG blistScope blistScope_n
  blistScope_els evalArgs_typA_gramA_iff evalExp_blistResult matchExp_iterList_var
  evalExp_iterList_var)
open Silmaril.SpecTec.Equiv.V1Binary (HasV1Types symDerives_bu32_v1 symDerives_bvaltype_v1)

namespace Bfunc688

/-! ## The pinned wasm-1.0 environment -/

set_option maxRecDepth 100000 in
theorem hasV1Types_original : HasV1Types Wasm10.envOriginal :=
  ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl,
    by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- `Blocals`'s body, `n:Bu32 t:Bvaltype`. -/
def blocalsBody : IL.Sym :=
  .seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
    .seqG [.attrG (.varE "t") (.varG "Bvaltype" [])]]

/-- `Blocals`'s value, `(LOCAL t)^n`. -/
def blocalsValue : Exp :=
  .iterE (.caseE "LOCAL" (.varE "t")) (.mk (.listN (.varE "n") none) [])

set_option maxRecDepth 100000 in
theorem blocals_shape : ∃ q t, Wasm10.envOriginal.findGram? "Blocals" =
    some ([], t, [.prodD q blocalsBody blocalsValue []]) :=
  ⟨_, _, by rfl⟩

set_option maxRecDepth 100000 in
theorem blist_shape : Wasm10.envOriginal.findGram? "Blist" =
    some (blistParams, .iterT (.varT "el" []) .list, blistProds) := by rfl

set_option maxRecDepth 100000 in
theorem bexpr_shape : ∃ q t, Wasm10.envOriginal.findGram? "Bexpr" =
    some ([], t, [.prodD q bexprBody bexprValue []]) := ⟨_, _, by rfl⟩

/-! ## `(LOCAL t)^n` -/

/-- `iterRows` with no domain: `k` empty rows. -/
theorem iterRows_nil (k : Nat) : iterRows [] none k = List.replicate k [] := by
  simp only [iterRows]
  rw [show iterRow [] none = fun _ => [] from funext fun _ => rfl, List.map_const',
    List.length_range]

/-- A `mapM` of a constant success over `k` copies. -/
theorem mapM_replicate_ok {α β : Type} (f : α → Res β) (a : α) (b : β) (h : f a = .ok b) :
    ∀ k, (List.replicate k a).mapM f = .ok (List.replicate k b)
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, List.mapM_cons, h, mapM_replicate_ok f a b h k]
    rfl

/-- **A domain-free `ListN` iteration repeats its body**: `e^n` with `n ↦ m` is `m` copies of
`e`'s value. -/
theorem evalExp_iterListN_nodom {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} {m : Nat}
    (hn : ρ.findVal? "n" = some (.num (.natN m))) (he : EvalExp env ρ e v) :
    EvalExp env ρ (.iterE e (.mk (.listN (.varE "n") none) [])) (.list (List.replicate m v)) := by
  obtain ⟨k, hk⟩ := he
  refine evalExp_iterE_iff.mpr ⟨k + 4, ?_⟩
  have hcount : evalExp (k + 3) env ρ (.varE "n") = .ok (.num (.natN m)) := by
    simp [evalExp, hn]
  rw [evalIterE]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hcount]
  refine ⟨[], by simp [evalDoms]; rfl, _, rfl, m, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok]
  refine ⟨[], rfl, by simp, List.replicate m v, ?_, rfl⟩
  rw [iterRows_nil, evalRounds]
  have hb : ρ.bindVals [] = ρ := by cases ρ; rfl
  have hk' : evalExp (k + 1) env ρ e = .ok v := evalExp_ok_of_le (Nat.le_succ k) hk
  refine mapM_replicate_ok _ _ _ ?_ m
  rw [hb]
  exact hk'

/-! ## Nested list iterations `(x*)*` -/

/-- The pattern and expression `((x)*)*` with domains `x ← xs`, `xs ← xss`. -/
def nestP (x xs xss : IL.Id) : Exp :=
  .iterE (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) (.mk .list [.mk xs (.varE xss)])

/-- `matchExp_iterList_var` at an explicit fuel. -/
theorem matchExp_iterList_var_fuel {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hx : x ≠ "_")
    (hfx : ρ.findVal? x = none) (hfxs : ρ.findVal? xs = none) (vs : List Value) (k : Nat) :
    matchExp (vs.length + k + 6) env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)]))
      (.list vs) = .ok (ρ.bindVal xs (.list vs)) := by
  rw [show vs.length + k + 6 = (vs.length + k + 5) + 1 by omega, matchExp,
    show vs.length + k + 5 = (vs.length + k + 4) + 1 by omega, matchIterE]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?]
  refine ⟨vs, rfl, ?_⟩
  rw [show vs.length + k + 4 = (vs.length + (k + 1) + 2) + 1 by omega, matchIterList]
  simp only [Res.bind_eq_ok]
  refine ⟨vs.map (fun v => [v]), ?_, ?_⟩
  · exact Silmaril.SpecTec.Equiv.BinaryModule.matchRounds_var hx hfx vs 0 (k + 1)
  · have hcols : iterCols (vs.map (fun v => [v])) [Dom.mk x (Exp.varE xs)].length
        = [Value.list vs] := by
      simp [iterCols, Silmaril.SpecTec.Equiv.BinaryModule.iterCol_singletons]
    rw [hcols, show List.map domSrc [Dom.mk x (Exp.varE xs)] = [Exp.varE xs] from rfl]
    rw [show vs.length + (k + 1) + 2 = (vs.length + (k + 1) + 1) + 1 by omega, matchExps]
    simp only [Res.bind_eq_ok]
    refine ⟨ρ.bindVal xs (.list vs), ?_, ?_⟩
    · rw [show vs.length + (k + 1) + 1 = (vs.length + (k + 1)) + 1 by omega, matchExp, hfxs]
    · rw [show vs.length + (k + 1) + 1 = (vs.length + (k + 1)) + 1 by omega, matchExps]

/-- The rounds of matching `((x)*)*` against a list of lists. -/
theorem matchRounds_nested {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hx : x ≠ "_")
    (hxs : xs ≠ "_") (hfx : ρ.findVal? x = none) (hfxs : ρ.findVal? xs = none) :
    ∀ (Ls : List (List Value)) (i N : Nat), (∀ L ∈ Ls, L.length + 6 ≤ N) →
      matchRounds (N + Ls.length + 1) env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)]))
        [xs] none i (Ls.map Value.list) = .ok ((Ls.map Value.list).map fun v => [v])
  | [], _, _, _ => by simp [matchRounds]
  | L :: Ls, i, N, hN => by
    have hfuel : N + (L :: Ls).length + 1 = (N + Ls.length + 1) + 1 := by
      simp only [List.length_cons]; omega
    rw [List.map_cons, hfuel, matchRounds]
    have hk' : matchExp (N + Ls.length + 1) env ρ
        (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) (.list L) =
          .ok (ρ.bindVal xs (.list L)) := by
      have := hN L (by simp)
      have e := matchExp_iterList_var_fuel (env := env) hx hfx hfxs L (N + Ls.length + 1 - 6 - L.length)
      rwa [show L.length + (N + Ls.length + 1 - 6 - L.length) + 6 = N + Ls.length + 1 by omega] at e
    have hrow : (ρ.bindVal xs (.list L)).findVals? [xs] = some [.list L] := by
      simp [VarEnv.findVals?, VarEnv.findVal?, VarEnv.bindVal, hxs]
    simp [hk', hrow, matchRounds_nested hx hxs hfx hfxs Ls (i + 1) N
      (fun L' hL' => hN L' (by simp [hL']))]

/-- **Matching `((x)*)*` against a list of lists** binds `xss` to it. -/
theorem matchExp_nested {env : Env} {ρ : VarEnv} {x xs xss : IL.Id} (hx : x ≠ "_")
    (hxs : xs ≠ "_") (hfx : ρ.findVal? x = none) (hfxs : ρ.findVal? xs = none)
    (hfxss : ρ.findVal? xss = none) (Ls : List (List Value)) (N : Nat) (h1 : 1 ≤ N)
    (hN : ∀ L ∈ Ls, L.length + 6 ≤ N) :
    MatchExp env ρ (nestP x xs xss) (.list (Ls.map Value.list))
      (ρ.bindVal xss (.list (Ls.map Value.list))) := by
  refine ⟨N + Ls.length + 4, ?_⟩
  rw [nestP, show N + Ls.length + 4 = (N + Ls.length + 3) + 1 by omega, matchExp,
    show N + Ls.length + 3 = (N + Ls.length + 2) + 1 by omega, matchIterE]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?]
  refine ⟨_, rfl, ?_⟩
  rw [show N + Ls.length + 2 = (N + Ls.length + 1) + 1 by omega, matchIterList]
  simp only [Res.bind_eq_ok]
  refine ⟨(Ls.map Value.list).map (fun v => [v]), ?_, ?_⟩
  · exact matchRounds_nested hx hxs hfx hfxs Ls 0 N hN
  · show matchExps (N + Ls.length + 1) env ρ ([Dom.mk xs (Exp.varE xss)].map domSrc)
        (iterCols ((Ls.map Value.list).map (fun v => [v])) [Dom.mk xs (Exp.varE xss)].length) =
          .ok (ρ.bindVal xss (.list (Ls.map Value.list)))
    have hcols : iterCols ((Ls.map Value.list).map (fun v => [v]))
        [Dom.mk xs (Exp.varE xss)].length = [Value.list (Ls.map Value.list)] := by
      simp only [iterCols, List.length_singleton, List.range_one, List.map_cons, List.map_nil,
        Silmaril.SpecTec.Equiv.BinaryModule.iterCol_singletons]
    rw [hcols, show List.map domSrc [Dom.mk xs (Exp.varE xss)] = [Exp.varE xss] from rfl]
    rw [show N + Ls.length + 1 = (N + Ls.length) + 1 by omega, matchExps]
    simp only [Res.bind_eq_ok]
    refine ⟨ρ.bindVal xss (.list (Ls.map Value.list)), ?_, ?_⟩
    · cases h : N + Ls.length with
      | zero => omega
      | succ n => rw [matchExp, hfxss]
    · cases h : N + Ls.length with
      | zero => omega
      | succ n => rw [matchExps]

/-- `evalExp_iterList_var` at an explicit fuel. -/
theorem evalExp_iterList_var_fuel {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? xs = some (.list vs)) :
    evalExp 5 env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) = .ok (.list vs) := by
  have hdoms : evalDoms 3 env ρ [.mk x (.varE xs)] = .ok [(x, Value.list vs)] := by
    simp [evalDoms, domVar, domSrc, evalExp, h]
  rw [evalExp, evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, Value.asList?,
    List.isEmpty_cons]
  refine ⟨[(x, Value.list vs)], rfl, trivial, vs.length, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_cons,
    List.mapM_nil]
  refine ⟨[(x, vs)], by simp [Value.asList?], by simp, vs, ?_, rfl⟩
  rw [Silmaril.SpecTec.Equiv.BinaryModule.iterRows_single]
  exact Silmaril.SpecTec.Equiv.BinaryModule.evalRounds_single env ρ x hx vs 0

/-- The rounds of evaluating `((x)*)*`. -/
theorem mapM_nested {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hx : x ≠ "_") (hxs : xs ≠ "_") :
    ∀ Ls : List (List Value), ((Ls.map Value.list).map (fun w => [(xs, w)])).mapM
      (fun r => evalExp 6 env (ρ.bindVals r) (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])))
        = .ok (Ls.map Value.list)
  | [] => rfl
  | L :: Ls => by
    have hv : evalExp 6 env (ρ.bindVals [(xs, Value.list L)])
        (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) = .ok (.list L) :=
      evalExp_ok_of_le (by omega) (evalExp_iterList_var_fuel hx (by
        simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, hxs]))
    simp only [List.map_cons, List.mapM_cons, hv, mapM_nested hx hxs Ls]
    rfl

/-- **Evaluating `((x)*)*`** with `xss` bound to a list of lists gives it back. -/
theorem evalExp_nested {env : Env} {ρ : VarEnv} {x xs xss : IL.Id} (hx : x ≠ "_")
    (hxs : xs ≠ "_") {Ls : List (List Value)}
    (h : ρ.findVal? xss = some (.list (Ls.map Value.list))) :
    evalExp 10 env ρ (nestP x xs xss) = .ok (.list (Ls.map Value.list)) := by
  have hdoms : evalDoms 8 env ρ [.mk xs (.varE xss)] =
      .ok [(xs, Value.list (Ls.map Value.list))] := by
    simp [evalDoms, domVar, domSrc, evalExp, h]
  rw [nestP, evalExp, evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, Value.asList?,
    List.isEmpty_cons]
  refine ⟨[(xs, Value.list (Ls.map Value.list))], rfl, trivial, _, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_cons,
    List.mapM_nil]
  refine ⟨[(xs, Ls.map Value.list)], by simp [Value.asList?], by simp, Ls.map Value.list, ?_,
    rfl⟩
  rw [Silmaril.SpecTec.Equiv.BinaryModule.iterRows_single, evalRounds]
  exact mapM_nested hx hxs Ls

/-! ## `$concat_` -/

/-- The first clause of `$concat_`, `$concat_(X, []) = []`. -/
def concatC1 : Clause :=
  .defD [.typP "X"] [.typA (.varT "X" []), .expA (.listE [])] (.listE []) []

/-- `(w)*`. -/
def iterW : Exp := .iterE (.varE "w") (.mk .list [.mk "w" (.varE "w*")])

/-- The second clause of `$concat_`, `$concat_(X, w* w'**) = w* ++ $concat_(X, w'**)`. -/
def concatC2 (q : List Param) : Clause :=
  .defD q [.typA (.varT "X" []), .expA (.catE (.listE [iterW]) (nestP "w'" "w'*" "w'**"))]
    (.catE iterW (.callE "concat_" [.typA (.varT "X" []), .expA (nestP "w'" "w'*" "w'**")])) []

set_option maxRecDepth 100000 in
theorem concat_shape : ∃ ps t q, Wasm10.envOriginal.findDef? "concat_" =
    some (ps, t, [concatC1, concatC2 q]) := ⟨_, _, _, by rfl⟩

set_option maxRecDepth 100000 in
theorem memTyp_X : Wasm10.envOriginal.memTyp "X" = false := by rfl

/-- The type parameter `X` matches any type, from the empty scope. -/
theorem matchArg_X (τ : Typ) :
    MatchArg Wasm10.envOriginal VarEnv.empty (.typA (.varT "X" [])) (.typ τ)
      (VarEnv.empty.bindTyp "X" τ) :=
  ⟨1, by simp [matchArg, matchTypV, memTyp_X]; rfl⟩

/-- A length bound for every member of a list of lists. -/
theorem length_le_sum : ∀ (Ls : List (List Value)), ∀ L ∈ Ls,
    L.length + 6 ≤ (Ls.map List.length).sum + 6
  | [], _, h => absurd h (by simp)
  | L' :: Ls, L, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := length_le_sum Ls L h
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **`$concat_` flattens**, at any type argument. -/
theorem concat_try :
    ∀ (Ls : List (List Value)) (q : List Param) (τ : Typ), TryClauses Wasm10.envOriginal [concatC1, concatC2 q]
      [.typ τ, .val (.list (Ls.map Value.list))] (.list Ls.flatten)
  | [], q, τ => by
    refine tryClauses_hit (matchArgs_cons (matchArg_X τ)
      (matchArgs_cons (matchArg_expA ⟨2, by simp [matchExp, matchExps]; rfl⟩) matchArgs_nil))
      (premsHold_nil_iff.mpr rfl) ?_
    exact ⟨2, by simp [evalExp, evalExps]; rfl⟩
  | L :: Ls, q, τ => by
    refine tryClauses_skip_match (matchArgs_cons_undef_tail (matchArg_X τ)
      (matchArgs_cons_undef (matchArg_expA_undef ⟨2, by
        simp only [matchExp, Value.asList?, Res.ofOption, Bind.bind, Except.bind]
        rw [matchExps] <;> simp⟩))) ?_
    let ρX : VarEnv := VarEnv.empty.bindTyp "X" τ
    let σ : VarEnv := ρX.bindVal "w*" (.list L)
    let ρ' : VarEnv := σ.bindVal "w'**" (.list (Ls.map Value.list))
    have h₁ : MatchExp Wasm10.envOriginal ρX (.listE [iterW]) (.list [.list L]) σ := by
      refine ⟨L.length + 8, ?_⟩
      have e := matchExp_iterList_var_fuel (env := Wasm10.envOriginal) (ρ := ρX)
        (x := "w") (xs := "w*") (by decide) rfl rfl L 0
      rw [show L.length + 8 = (L.length + 7) + 1 by omega, matchExp]
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?]
      refine ⟨_, rfl, ?_⟩
      rw [show L.length + 7 = (L.length + 6) + 1 by omega, matchExps]
      simp only [Res.bind_eq_ok]
      refine ⟨_, by rw [iterW]; simpa using e, ?_⟩
      rw [show L.length + 6 = (L.length + 5) + 1 by omega, matchExps]
    have h₂ : MatchExp Wasm10.envOriginal σ (nestP "w'" "w'*" "w'**") (.list (Ls.map Value.list))
        ρ' :=
      matchExp_nested (by decide) (by decide) rfl rfl rfl Ls _ (by omega) (length_le_sum Ls)
    have hcat : MatchExp Wasm10.envOriginal ρX (.catE (.listE [iterW]) (nestP "w'" "w'*" "w'**"))
        (.list ((L :: Ls).map Value.list)) ρ' :=
      Silmaril.SpecTec.Equiv.Execution.matchExp_catE_ofLeft
        Silmaril.SpecTec.Equiv.Execution.patLen_listE (by simp) h₁ h₂
    obtain ⟨ps, t, q', hd⟩ := concat_shape
    have hargs : EvalArgs Wasm10.envOriginal ρ'
        [.typA (.varT "X" []), .expA (nestP "w'" "w'*" "w'**")]
        [.typ (resolveTyp ρ' (.varT "X" [])), .val (.list (Ls.map Value.list))] := by
      have e := evalExp_nested (env := Wasm10.envOriginal) (ρ := ρ') (x := "w'") (xs := "w'*")
        (xss := "w'**") (Ls := Ls) (by decide) (by decide) rfl
      exact ⟨12, by simp [evalArgs, evalArg, List.mapM_cons, e]⟩
    have hcall : EvalExp Wasm10.envOriginal ρ'
        (.callE "concat_" [.typA (.varT "X" []), .expA (nestP "w'" "w'*" "w'**")])
        (.list Ls.flatten) := by
      refine evalExp_callE_iff.mpr (Silmaril.SpecTec.Equiv.ExecNumeric.callDef_iff.mpr
        ⟨_, ps, t, [concatC1, concatC2 q'], hargs, ?_, Or.inl (concat_try Ls q' _)⟩)
      rw [show ρ'.findDef? "concat_" = none from rfl]
      exact hd
    refine tryClauses_hit (matchArgs_cons (matchArg_X τ)
      (matchArgs_cons (matchArg_expA hcat) matchArgs_nil)) (premsHold_nil_iff.mpr rfl) ?_
    exact evalExp_catE_iff.mpr ⟨_, _, evalExp_iterList_var (by decide) rfl, hcall, rfl⟩

/-! ## `Blocals` -/

/-- `Bvaltype` reads `7F` (`i32`). -/
theorem bvaltype_7F : ∃ tv : Value, ∀ σ, SymDerives Wasm10.envOriginal σ (.varG "Bvaltype" [])
    [0x7F] [tv] σ :=
  ⟨_, fun _ => (symDerives_bvaltype_v1 hasV1Types_original).mpr ⟨rfl, _, .i32, rfl⟩⟩

/-- **`Blocals` reads `n t` as `(LOCAL t)^n`.** -/
theorem blocals_derives {tv : Value}
    (htv : ∀ σ, SymDerives Wasm10.envOriginal σ (.varG "Bvaltype" []) [0x7F] [tv] σ)
    {bs : Grammar.Bytes} {m : Nat} (hm : U32 bs m) (ρ : VarEnv) :
    SymDerives Wasm10.envOriginal ρ (.varG "Blocals" []) (bs ++ [0x7F])
      [.list (List.replicate m (.case "LOCAL" tv))] ρ := by
  obtain ⟨q, t, hg⟩ := blocals_shape
  let σ₁ : VarEnv := VarEnv.empty.bindVal "n" (.num (.natN m))
  let σ₂ : VarEnv := σ₁.bindVal "t" tv
  have hu : SymDerives Wasm10.envOriginal VarEnv.empty (.varG "Bu32" []) bs [numCase m]
      VarEnv.empty :=
    (symDerives_bu32_v1 hasV1Types_original hasLeb_wasm10_original).mpr ⟨rfl, m, hm, rfl⟩
  have h₁ : SymDerives Wasm10.envOriginal VarEnv.empty
      (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])) bs [numCase m] σ₁ :=
    symDerives_attrG.mpr ⟨_, _, hu, rfl, matchExp_case_var rfl⟩
  have h₂ : SymDerives Wasm10.envOriginal σ₁ (.attrG (.varE "t") (.varG "Bvaltype" [])) [0x7F]
      [tv] σ₂ := symDerives_attrVar rfl (htv σ₁)
  have hbody : SymDerives Wasm10.envOriginal VarEnv.empty blocalsBody (bs ++ [0x7F])
      [numCase m, tv] σ₂ :=
    symDerives_seqG_cons.mpr ⟨bs, [numCase m], σ₁, [0x7F], [tv], symDerives_seqG_single h₁,
      symDerives_seqG_single (symDerives_seqG_single h₂), rfl, rfl⟩
  have hval : EvalExp Wasm10.envOriginal σ₂ blocalsValue
      (.list (List.replicate m (.case "LOCAL" tv))) :=
    evalExp_iterListN_nodom rfl (evalExp_caseE_iff.mpr ⟨tv, evalExp_varE_iff.mpr rfl, rfl⟩)
  have hp : ProdDerives Wasm10.envOriginal ρ [] [] (.prodD q blocalsBody blocalsValue [])
      (bs ++ [0x7F]) [.list (List.replicate m (.case "LOCAL" tv))] :=
    ⟨[], VarEnv.empty, _, σ₂, σ₂, _, evalArgs_nil _ ρ, rfl, hbody, premsHold_nil_iff.mpr rfl,
      hval, rfl⟩
  exact (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩

/-! ## `Blist(Blocals)` with two runs -/

/-- **`Blist(Y)` reads `02 b₁ b₂`** as the list of the two values `Y` reads. -/
theorem blist_two {y : IL.Id} {b₁ b₂ : Grammar.Bytes} {v₁ v₂ : Value}
    (h₁ : ∀ σ, SymDerives Wasm10.envOriginal σ (.varG y []) b₁ [v₁] σ)
    (h₂ : ∀ σ, SymDerives Wasm10.envOriginal σ (.varG y []) b₂ [v₂] σ) (t : Typ) (ρ : VarEnv) :
    SymDerives Wasm10.envOriginal ρ (.varG "Blist" [.typA t, .gramA (.varG y [])])
      ([0x02] ++ (b₁ ++ (b₂ ++ []))) [.list [v₁, v₂]] ρ := by
  let σ := blistScope ρ t y
  let σ₁ : VarEnv := σ.bindVal "n" (.num (.natN 2))
  let σ₂ : VarEnv := σ₁.bindVal "el*" (.list [v₁, v₂])
  have hn₁ : σ₁.findVal? "n" = some (.num (.natN 2)) := by
    simp [σ₁, VarEnv.findVal?, VarEnv.bindVal, Map.bind]
  have hel₁ : σ₁.findVal? "el" = none := by
    simpa [σ₁, VarEnv.findVal?, VarEnv.bindVal, Map.bind, Map.find?] using Silmaril.SpecTec.Equiv.BinaryModule.blistScope_el ρ t y
  have hels₁ : σ₁.findVal? "el*" = none := by
    simpa [σ₁, VarEnv.findVal?, VarEnv.bindVal, Map.bind, Map.find?] using blistScope_els ρ t y
  have hu : SymDerives Wasm10.envOriginal σ (.varG "Bu32" []) [0x02] [numCase 2] σ :=
    (symDerives_bu32_v1 hasV1Types_original hasLeb_wasm10_original).mpr
      ⟨rfl, 2, .byte 0x02 (by decide) (by decide), rfl⟩
  have hA : SymDerives Wasm10.envOriginal σ (.attrG (.caseE "%" (.tupE [.varE "n"]))
      (.varG "Bu32" [])) [0x02] [numCase 2] σ₁ :=
    symDerives_attrG.mpr ⟨_, _, hu, rfl, matchExp_case_var (blistScope_n ρ t y)⟩
  have hr : Rounds Wasm10.envOriginal σ₁ (.attrG (.varE "el") (.varG y []))
      [.mk "el" (.varE "el*")] (b₁ ++ (b₂ ++ [])) [(v₁, [v₁]), (v₂, [v₂])] :=
    .cons (symDerives_attrVar hel₁ (h₁ σ₁))
      (by simp [domVar, VarEnv.findVal?, VarEnv.bindVal, Map.bind])
      (.cons (symDerives_attrVar hel₁ (h₂ σ₁))
        (by simp [domVar, VarEnv.findVal?, VarEnv.bindVal, Map.bind]) .nil)
  have hc : IterCount Wasm10.envOriginal σ₁ (.listN (.varE "n") none)
      [(v₁, [v₁]), (v₂, [v₂])].length :=
    ⟨rfl, _, evalExp_varE_iff.mpr hn₁, rfl⟩
  have hI : SymDerives Wasm10.envOriginal σ₁ (.iterG (.attrG (.varE "el") (.varG y []))
      (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])) (b₁ ++ (b₂ ++ []))
      [.list [v₁, v₂]] σ₂ :=
    symDerives_iterG.mpr ⟨_, hr, hc, rfl, ⟨_, matchExp_varE_of_none hels₁, rfl⟩⟩
  have hbody : SymDerives Wasm10.envOriginal σ (blistBodyOf y) ([0x02] ++ (b₁ ++ (b₂ ++ [])))
      [numCase 2, .list [v₁, v₂]] σ₂ :=
    symDerives_seqG_cons.mpr ⟨[0x02], [numCase 2], σ₁, _, [.list [v₁, v₂]],
      symDerives_seqG_single hA, symDerives_seqG_single (symDerives_seqG_single hI), rfl, rfl⟩
  have hn : σ₂.findVal? "n" = some (.num (.natN 2)) := by
    simp [σ₂, σ₁, VarEnv.findVal?, VarEnv.bindVal, Map.bind]
  have hel : σ₂.findVal? "el*" = some (.list [v₁, v₂]) := by
    simp [σ₂, VarEnv.findVal?, VarEnv.bindVal, Map.bind]
  have hp : ProdDerives Wasm10.envOriginal ρ blistParams [.typA t, .gramA (.varG y [])]
      (.prodD [.expP "n" (.varT "n" []), .expP "el*" (.iterT (.varT "el" []) .list)]
        (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
          .seqG [.iterG (.attrG (.varE "el") (.varG "BX" []))
            (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])]])
        (.iterE (.varE "el") (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])) [])
      ([0x02] ++ (b₁ ++ (b₂ ++ []))) [.list [v₁, v₂]] :=
    ⟨_, σ, _, σ₂, σ₂, _, evalArgs_typA_gramA_iff.mpr rfl, rfl, hbody, premsHold_nil_iff.mpr rfl,
      evalExp_blistResult hn hel rfl, rfl⟩
  exact (symDerives_varG blist_shape).mpr ⟨rfl, _, by simp [blistProds], hp⟩

/-! ## `Bfunc` -/

/-- The pinned `Bfunc`'s body, `local**:Blist(Blocals) expr:Bexpr`. -/
def bfuncBody : IL.Sym :=
  .seqG [.seqG [.attrG (nestP "local" "local*" "local**")
      (.varG "Blist" [.typA (.iterT (.varT "local" []) .list), .gramA (.varG "Blocals" [])])],
    .seqG [.attrG (.varE "expr") (.varG "Bexpr" [])]]

/-- The pinned `Bfunc`'s value, `($concat_(local, local**), expr)`. -/
def bfuncValue : Exp :=
  .tupE [.callE "concat_" [.typA (.varT "local" []), .expA (nestP "local" "local*" "local**")],
    .varE "expr"]

set_option maxRecDepth 100000 in
theorem bfunc_shape : ∃ q t, Wasm10.envOriginal.findGram? "Bfunc" =
    some ([], t, [.prodD q bfuncBody bfuncValue []]) := ⟨_, _, by rfl⟩

/-- **The pinned `Bfunc` reads two runs of locals and an empty body** as the concatenation of
the runs, with no bound on its length. -/
theorem bfunc_two {b₁ b₂ : Grammar.Bytes} {A B : List Value}
    (h₁ : ∀ σ, SymDerives Wasm10.envOriginal σ (.varG "Blocals" []) b₁ [.list A] σ)
    (h₂ : ∀ σ, SymDerives Wasm10.envOriginal σ (.varG "Blocals" []) b₂ [.list B] σ)
    (ρ : VarEnv) :
    gramRelSup Wasm10.envOriginal ρ (.varG "Bfunc" [])
      (([0x02] ++ (b₁ ++ (b₂ ++ []))) ++ [0x0B]) (.tuple [.list [A, B].flatten, .list []]) := by
  obtain ⟨q, t, hg⟩ := bfunc_shape
  obtain ⟨qe, te, hbe⟩ := bexpr_shape
  obtain ⟨ps, tc, qc, hd⟩ := concat_shape
  let σ₁ : VarEnv := VarEnv.empty.bindVal "local**" (.list ([A, B].map Value.list))
  let σ₂ : VarEnv := σ₁.bindVal "expr" (.list [])
  have f₁ : SymDerives Wasm10.envOriginal VarEnv.empty (.attrG (nestP "local" "local*" "local**")
      (.varG "Blist" [.typA (.iterT (.varT "local" []) .list), .gramA (.varG "Blocals" [])]))
      ([0x02] ++ (b₁ ++ (b₂ ++ []))) [.list ([A, B].map Value.list)] σ₁ :=
    symDerives_attrG.mpr ⟨_, _, blist_two h₁ h₂ _ _, rfl,
      matchExp_nested (by decide) (by decide) rfl rfl rfl [A, B] _ (by omega)
        (length_le_sum [A, B])⟩
  have f₂ : SymDerives Wasm10.envOriginal σ₁ (.attrG (.varE "expr") (.varG "Bexpr" [])) [0x0B]
      [.list []] σ₂ := symDerives_attrVar rfl (bexpr_end hbe σ₁)
  have hbody : SymDerives Wasm10.envOriginal VarEnv.empty bfuncBody
      (([0x02] ++ (b₁ ++ (b₂ ++ []))) ++ [0x0B]) [.list ([A, B].map Value.list), .list []] σ₂ :=
    symDerives_seqG_cons.mpr ⟨_, _, σ₁, [0x0B], [.list []], symDerives_seqG_single f₁,
      symDerives_seqG_single (symDerives_seqG_single f₂), rfl, rfl⟩
  have hargs : EvalArgs Wasm10.envOriginal σ₂
      [.typA (.varT "local" []), .expA (nestP "local" "local*" "local**")]
      [.typ (resolveTyp σ₂ (.varT "local" [])), .val (.list ([A, B].map Value.list))] := by
    have e := evalExp_nested (env := Wasm10.envOriginal) (ρ := σ₂) (x := "local")
      (xs := "local*") (xss := "local**") (Ls := [A, B]) (by decide) (by decide) rfl
    exact ⟨12, by simp [evalArgs, evalArg, List.mapM_cons, e]⟩
  have hcall : EvalExp Wasm10.envOriginal σ₂
      (.callE "concat_" [.typA (.varT "local" []), .expA (nestP "local" "local*" "local**")])
      (.list [A, B].flatten) := by
    refine evalExp_callE_iff.mpr (Silmaril.SpecTec.Equiv.ExecNumeric.callDef_iff.mpr
      ⟨_, ps, tc, [concatC1, concatC2 qc], hargs, ?_, Or.inl (concat_try [A, B] qc _)⟩)
    rw [show σ₂.findDef? "concat_" = none from rfl]
    exact hd
  have hval : EvalExp Wasm10.envOriginal σ₂ bfuncValue (.tuple [.list [A, B].flatten, .list []]) :=
    evalExp_tupE_iff.mpr ⟨_, evalExps_cons_iff.mpr ⟨_, _, hcall, evalExps_cons_iff.mpr
      ⟨_, _, evalExp_varE_iff.mpr rfl, evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩
  have hp : ProdDerives Wasm10.envOriginal ρ [] [] (.prodD q bfuncBody bfuncValue [])
      (([0x02] ++ (b₁ ++ (b₂ ++ []))) ++ [0x0B]) [.tuple [.list [A, B].flatten, .list []]] :=
    ⟨[], VarEnv.empty, _, σ₂, σ₂, _, evalArgs_nil _ ρ, rfl, hbody, premsHold_nil_iff.mpr rfl,
      hval, rfl⟩
  exact gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩⟩

/-! ## `2^32` locals -/

/-- `FF FF FF FF 0F` is the LEB128 `u32` encoding of `2^32 - 1`. -/
theorem u32_max : U32 [0xFF, 0xFF, 0xFF, 0xFF, 0x0F] (2 ^ 32 - 1) := by
  have h : U32 [0xFF, 0xFF, 0xFF, 0xFF, 0x0F]
      (2 ^ 7 * (2 ^ 7 * (2 ^ 7 * (2 ^ 7 * (0x0F : UInt8).toNat + ((0xFF : UInt8).toNat - 2 ^ 7)) +
        ((0xFF : UInt8).toNat - 2 ^ 7)) + ((0xFF : UInt8).toNat - 2 ^ 7)) +
        ((0xFF : UInt8).toNat - 2 ^ 7)) :=
    .cont 0xFF (by decide) (by decide) (.cont 0xFF (by decide) (by decide)
      (.cont 0xFF (by decide) (by decide) (.cont 0xFF (by decide) (by decide)
        (.byte 0x0F (by decide) (by decide)))))
  simpa using h

/-- `01` is the LEB128 `u32` encoding of `1`. -/
theorem u32_one : U32 [0x01] 1 := .byte 0x01 (by decide) (by decide)

end Bfunc688


open Bfunc688 in
/-- **Two runs of `m₁` and `m₂` locals**: the pinned theory entails a `Bfunc` sentence with
`m₁ + m₂` locals, for any `u32` encodings of the run lengths. -/
theorem bfunc_runs {bs₁ bs₂ : Grammar.Bytes} {m₁ m₂ : Nat} (h₁ : U32 bs₁ m₁) (h₂ : U32 bs₂ m₂) :
    ∃ (bs : Grammar.Bytes) (L : List Value) (e : Value), L.length = m₁ + m₂ ∧
      Entails (scriptAxioms Wasm10.envOriginal)
        (derivesNT "Bfunc" [] VarEnv.empty bs (.tuple [.list L, e])) := by
  obtain ⟨tv, htv⟩ := bvaltype_7F
  refine ⟨_, _, _, ?_, (gramRelSup_varG_iff_entails ..).mp
    (bfunc_two (blocals_derives htv h₁) (blocals_derives htv h₂) VarEnv.empty)⟩
  simp

open Bfunc688 in
/-- **`Task.bfunc688PinnedLarge` holds**: the pinned wasm-1.0 theory entails a `Bfunc` sentence
with `2^32` locals, read from `02 (FF FF FF FF 0F 7F) (01 7F) 0B`: two runs of `i32` locals,
`2^32 - 1` and `1`, and an empty body. -/
theorem bfunc688PinnedLarge : Task.bfunc688PinnedLarge := by
  obtain ⟨bs, L, e, hL, h⟩ := bfunc_runs u32_max u32_one
  exact ⟨bs, L, e, by rw [hL]; omega, h⟩

/-- **#688 separates**: the corrected wasm-1.0 theory does not entail all of the pinned one. -/
theorem bfunc688_separates :
    ¬ ∀ ψ ∈ scriptAxioms Wasm10.envOriginal, Entails (scriptAxioms Wasm10.envFixed) ψ :=
  bfunc688_separates_of_task bfunc688PinnedLarge

end Silmaril.Wasm.SpecTec.GrammarInst
