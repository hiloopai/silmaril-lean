module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval

/-!
# Matching a pattern never touches the definition namespace

A `VarEnv` (`Silmaril/SpecTec/Sem/Eval.lean`) has four namespaces, mirroring
`spectec/src/il/subst.ml:9`: `vals` for term variables, `typs` for type
variables, `defs` for `DefP` parameters — each bound to the *name* of a global
definition — and `grams` for grammar variables.  `Silmaril/SpecTec/Sem/Eval.lean`
already proves that a successful match only ever *extends* a scope
(`matchExp_extends`, via `GrowsAt`/`growsAt_succ`).  This file proves the
sharper statement for one of the four namespaces:

> **`matchExp` leaves `defs` alone.**  If `matchExp n env ρ e v = .ok σ` then
> `σ.defs = ρ.defs`, hence `σ.findDef? x = ρ.findDef? x` for every `x`.

The payoff is that a `CallE` resolved through the scope — `callDef` reads
`(ρ.findDef? x).getD x` (`eval.ml:361-372`) — means the same thing before and
after a pattern match: matching cannot capture or redirect a function name.
This is strictly stronger than `Extends`, which only says the old `defs` list
is a suffix of the new one, and so permits new entries that would *shadow* an
old binding, since `Map.find?` searches from the front.

## Which functions this holds of, and which it does not

The proof is by mutual induction on the fuel over the whole sub-family that
`matchExp` can reach, exactly as `GrowsAt` does for the extension property.
The sub-family that is closed under the recursion, and for which `defs` is
genuinely unchanged, is

  `matchExp`, `matchDefault`, `matchExps`, `matchExpFields`, `matchIterE`,
  `matchIterList`.

That these six are closed is a fact about the definitions, checked clause by
clause:

* `matchExp` recurses into itself and calls `matchDefault`, `matchExps`,
  `matchExpFields` and `matchIterE`, plus `patLen` in the `CatE` clause —
  and `patLen` returns a `Res Nat`, not a scope.
* `matchDefault` calls only `evalExp`, which returns a `Res Value` and
  produces no scope at all.
* `matchExps` and `matchExpFields` thread `matchExp` pointwise.
* `matchIterE` calls `matchExp`, `matchExps` and `matchIterList`.
* `matchIterList` calls `matchRounds` — which returns
  `Res (List (List Value))`, again no scope — and then `matchExps`.

Nothing in that list reaches `matchArg`, `matchArgs`, `premHolds`,
`premsHold`, `premIter` or `premRounds`, which is essential, because:

* **`matchArg` binds a def.**  Its `DefA` clause is
  `| _+1, _, ρ, .defA y, .defName x => .ok (ρ.bindDef y x)` — the one place in
  the evaluator where `defs` grows — so the property proved here is simply
  false for it, and `matchArgs`, which threads `matchArg`, inherits the
  failure.
* **`premHolds` can invoke a rule** (`RulePr`), and its `LetPr` match runs in
  a scope that the surrounding `tryClauses`/`matchArgs` may already have given
  def bindings.  `premHolds` is reached only from `tryClauses`, never from
  `matchExp`, so it stays outside the induction.

Those exclusions are not an artefact of the proof: `matchArg` really does
change `defs`.  The six functions above are therefore the largest sub-family
closed under the recursion for which the statement is true.

The two headline results are `matchExp_defs` (fuelled form) and
`MatchExp.findDef?` (relational form, for
`MatchExp env ρ e v σ := ∃ n, matchExp n env ρ e v = .ok σ`); the remaining
five members of the family get the same statement at the end of the file.
-/

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod

@[expose] public section

/-! ## `defs` is untouched by the binders `matchExp` can perform -/

namespace VarEnv

@[simp] theorem defs_bindVal (ρ : VarEnv) (x : IL.Id) (v : Value) :
    (ρ.bindVal x v).defs = ρ.defs := rfl

@[simp] theorem defs_bindTyp (ρ : VarEnv) (x : IL.Id) (t : Typ) :
    (ρ.bindTyp x t).defs = ρ.defs := rfl

@[simp] theorem defs_bindGram (ρ : VarEnv) (x : IL.Id) (g : Sym) :
    (ρ.bindGram x g).defs = ρ.defs := rfl

@[simp] theorem defs_bindVals (ρ : VarEnv) (xs : List (IL.Id × Value)) :
    (ρ.bindVals xs).defs = ρ.defs := rfl

end VarEnv

/-! ## The `Grows`-style combinator algebra, for `defs` -/

/-- `DefsFixed ρ r`: whatever scope `r` produces has exactly `ρ`'s definition
namespace.  Failure is vacuous, which is what makes the combinators below
total — the same shape as `Grows` in `Silmaril/SpecTec/Sem/Eval.lean`. -/
def DefsFixed (ρ : VarEnv) (r : Res VarEnv) : Prop :=
  ∀ σ, r = .ok σ → σ.defs = ρ.defs

theorem defsFixed_ok (ρ : VarEnv) : DefsFixed ρ (.ok ρ) := by
  rintro σ h; cases h; rfl

theorem defsFixed_ok_of {ρ σ : VarEnv} (h : σ.defs = ρ.defs) : DefsFixed ρ (.ok σ) := by
  rintro τ hτ; cases hτ; exact h

theorem defsFixed_error (ρ : VarEnv) (e : Stuck) : DefsFixed ρ (.error e) := by
  rintro σ h; exact absurd h (by simp)

theorem defsFixed_bind {α : Type} {ρ : VarEnv} {r : Res α} {f : α → Res VarEnv}
    (hf : ∀ a, DefsFixed ρ (f a)) : DefsFixed ρ (r >>= f) := by
  rintro σ h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨a, _, ha⟩ := h
  exact hf a σ ha

theorem defsFixed_bind_env {ρ : VarEnv} {r : Res VarEnv} {f : VarEnv → Res VarEnv}
    (hr : DefsFixed ρ r) (hf : ∀ σ, DefsFixed σ (f σ)) : DefsFixed ρ (r >>= f) := by
  rintro τ h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨σ, hσ, hτ⟩ := h
  exact (hf σ τ hτ).trans (hr σ hσ)

theorem defsFixed_assert {ρ : VarEnv} {c : Prop} [Decidable c] {r : Res VarEnv}
    (h : DefsFixed ρ r) : DefsFixed ρ (Res.assert c r) := by
  by_cases hc : c
  · simpa [Res.assert, hc] using h
  · simp only [Res.assert, hc, ite_false]; exact defsFixed_error _ _

theorem defsFixed_elimUndef {α : Type} {ρ : VarEnv} {r : Res α} {f : α → Res VarEnv}
    {g : Unit → Res VarEnv} (hf : ∀ a, DefsFixed ρ (f a)) (hg : ∀ u, DefsFixed ρ (g u)) :
    DefsFixed ρ (Res.elimUndef r f g) := by
  cases r with
  | ok a => exact hf a
  | error e => cases e with
    | undef => exact hg ()
    | outOfFuel => exact defsFixed_error _ _

/-- `Res.scan` keeps `defs` fixed: the answer is one of the alternatives'
(`Res.scan_eq_ok`). -/
theorem defsFixed_scan {ρ : VarEnv} {f : Nat → Res VarEnv} (hf : ∀ j, DefsFixed ρ (f j))
    (k i : Nat) : DefsFixed ρ (Res.scan f i k) := by
  intro σ h
  obtain ⟨j, -, -, hj⟩ := Res.scan_eq_ok k i h
  exact hf j σ hj

/-! ## The mutual induction on the fuel -/

/-- Every member of the `matchExp` sub-family leaves `defs` alone, at a fixed
fuel level.  Note which functions are *absent* with respect to `GrowsAt`:
`matchArg`, `matchArgs`, `premHolds`, `premsHold`, `premIter` and
`premRounds` cannot appear here, because `matchArg`'s `DefA` clause binds a
def.  None of them is reachable from `matchExp`. -/
structure DefsFixedAt (n : Nat) : Prop where
  /-- `matchExp` keeps `defs`. -/
  matchExp : ∀ env ρ e v, DefsFixed ρ (matchExp n env ρ e v)
  /-- `matchDefault` keeps `defs`. -/
  matchDefault : ∀ env ρ e v, DefsFixed ρ (matchDefault n env ρ e v)
  /-- `matchExps` keeps `defs`. -/
  matchExps : ∀ env ρ es vs, DefsFixed ρ (matchExps n env ρ es vs)
  /-- `matchExpFields` keeps `defs`. -/
  matchExpFields : ∀ env ρ fs gs, DefsFixed ρ (matchExpFields n env ρ fs gs)
  /-- `matchIterE` keeps `defs`. -/
  matchIterE : ∀ env ρ e it ds v, DefsFixed ρ (matchIterE n env ρ e it ds v)
  /-- `matchIterList` keeps `defs`. -/
  matchIterList : ∀ env ρ e ds ido vs, DefsFixed ρ (matchIterList n env ρ e ds ido vs)

/-- Base case: with no fuel nothing succeeds. -/
theorem defsFixedAt_zero : DefsFixedAt 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
      | (simp only [matchExp]; exact defsFixed_error _ _)
      | (simp only [matchDefault]; exact defsFixed_error _ _)
      | (simp only [matchExps]; exact defsFixed_error _ _)
      | (simp only [matchExpFields]; exact defsFixed_error _ _)
      | (simp only [matchIterE]; exact defsFixed_error _ _)
      | (simp only [matchIterList]; exact defsFixed_error _ _)

/-- The inductive step, by structural recursion on the fuel. -/
theorem defsFixedAt_succ : ∀ n, DefsFixedAt n
  | 0 => defsFixedAt_zero
  | n + 1 => by
      have ih := defsFixedAt_succ n
      have hm := ih.matchExp
      have hmd := ih.matchDefault
      have hms := ih.matchExps
      have hmf := ih.matchExpFields
      have hmi := ih.matchIterE
      have hmil := ih.matchIterList
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      -- `matchExp`
      · intro env ρ e v
        cases e
        case varE x =>
          simp only [matchExp]
          split
          · split
            · exact defsFixed_ok ρ
            · exact defsFixed_error _ _
          · exact defsFixed_ok_of (VarEnv.defs_bindVal _ _ _)
        case unE op t e =>
          cases op <;> cases v <;> simp only [matchExp] <;>
            first
              | exact hmd _ _ _ _
              | exact defsFixed_assert (hm _ _ _ _)
              | exact defsFixed_assert (defsFixed_bind fun _ => hm _ _ _ _)
        case tupE es =>
          simp only [matchExp]; exact defsFixed_bind fun _ => hms _ _ _ _
        case projE e i =>
          simp only [matchExp]
          split
          · exact hm _ _ _ _
          · exact hmd _ _ _ _
        case caseE op e =>
          simp only [matchExp]
          exact defsFixed_bind fun _ => defsFixed_assert (hm _ _ _ _)
        case uncaseE e op => simp only [matchExp]; exact hm _ _ _ _
        case optE eo =>
          cases eo <;> simp only [matchExp] <;>
            first
              | exact defsFixed_assert (defsFixed_ok ρ)
              | exact defsFixed_bind fun _ => defsFixed_bind fun _ => hm _ _ _ _
        case strE fs =>
          simp only [matchExp]; exact defsFixed_bind fun _ => hmf _ _ _ _
        case listE es =>
          simp only [matchExp]; exact defsFixed_bind fun _ => hms _ _ _ _
        case catE e₁ e₂ =>
          simp only [matchExp]
          refine defsFixed_bind fun vs => defsFixed_elimUndef (fun k => ?_) (fun _ => ?_)
          · exact defsFixed_assert
              (defsFixed_bind_env (hm _ _ _ _) fun σ => hm _ _ _ _)
          · refine defsFixed_elimUndef (fun k => ?_) (fun _ => ?_)
            · exact defsFixed_assert
                (defsFixed_bind_env (hm _ _ _ _) fun σ => hm _ _ _ _)
            · exact defsFixed_scan
                (fun _ => defsFixed_bind_env (hm _ _ _ _) fun σ => hm _ _ _ _) _ _
        case iterE e₀ it =>
          cases it with
          | mk i ds => simp only [matchExp]; exact hmi _ _ _ _ _ _
        case cvtE e t₁ t₂ =>
          cases v <;> simp only [matchExp] <;>
            first
              | exact hmd _ _ _ _
              | exact defsFixed_bind fun _ => hm _ _ _ _
        case subE e t₁ t₂ => simp only [matchExp]; exact hm _ _ _ _
        case boolE b => simp only [matchExp]; exact defsFixed_assert (defsFixed_ok ρ)
        case numE m => simp only [matchExp]; exact defsFixed_assert (defsFixed_ok ρ)
        case textE t => simp only [matchExp]; exact defsFixed_assert (defsFixed_ok ρ)
        all_goals (simp only [matchExp]; exact hmd _ _ _ _)
      -- `matchDefault`: only `evalExp`, which produces no scope.
      · intro env ρ e v
        simp only [matchDefault]
        exact defsFixed_bind fun _ => defsFixed_assert (defsFixed_ok ρ)
      -- `matchExps`
      · intro env ρ es vs
        cases es with
        | nil =>
            cases vs <;> simp only [matchExps] <;>
              first | exact defsFixed_ok ρ | exact defsFixed_error _ _
        | cons e es =>
            cases vs with
            | nil => simp only [matchExps]; exact defsFixed_error _ _
            | cons v vs =>
                simp only [matchExps]
                exact defsFixed_bind_env (hm _ _ _ _) fun σ => hms _ _ _ _
      -- `matchExpFields`
      · intro env ρ fs gs
        cases fs with
        | nil =>
            cases gs <;> simp only [matchExpFields] <;>
              first | exact defsFixed_ok ρ | exact defsFixed_error _ _
        | cons f fs =>
            cases f with
            | mk a e =>
                cases gs with
                | nil => simp only [matchExpFields]; exact defsFixed_error _ _
                | cons g gs =>
                    simp only [matchExpFields]
                    exact defsFixed_assert
                      (defsFixed_bind_env (hm _ _ _ _) fun σ => hmf _ _ _ _)
      -- `matchIterE`
      · intro env ρ e it ds v
        cases it with
        | opt =>
            simp only [matchIterE]
            refine defsFixed_bind fun o => ?_
            cases o with
            | none => exact hms _ _ _ _
            | some w =>
                exact defsFixed_bind fun _ => defsFixed_bind fun _ => hms _ _ _ _
        | list =>
            simp only [matchIterE]; exact defsFixed_bind fun _ => hmil _ _ _ _ _ _
        | list1 =>
            simp only [matchIterE]
            exact defsFixed_bind fun _ => defsFixed_assert (hmil _ _ _ _ _ _)
        | listN eₙ x =>
            simp only [matchIterE]
            exact defsFixed_bind fun _ =>
              defsFixed_bind_env (hm _ _ _ _) fun σ => hmil _ _ _ _ _ _
      -- `matchIterList`: `matchRounds` returns rows of values, not a scope.
      · intro env ρ e ds ido vs
        simp only [matchIterList]
        exact defsFixed_bind fun _ => hms _ _ _ _

/-! ## The results -/

/-- **A successful match leaves the definition namespace alone.**  Unlike
`matchExp_extends`, which only puts `ρ.defs` as a suffix of `σ.defs`, this
says the two lists are *equal*: a pattern match cannot even shadow a `DefP`
binding, let alone drop one. -/
theorem matchExp_defs {n : Nat} {env : Env} {ρ σ : VarEnv} {e : Exp} {v : Value}
    (h : matchExp n env ρ e v = .ok σ) : σ.defs = ρ.defs :=
  (defsFixedAt_succ n).matchExp env ρ e v σ h

/-- The relational form: `findDef?` is preserved, pointwise. -/
theorem MatchExp.findDef? {env : Env} {ρ σ : VarEnv} {e : Exp} {v : Value}
    (h : MatchExp env ρ e v σ) (x : IL.Id) : σ.findDef? x = ρ.findDef? x := by
  obtain ⟨n, h⟩ := h
  simp only [VarEnv.findDef?, matchExp_defs h]

/-! ### The same statement for the rest of the sub-family -/

/-- `matchDefault` evaluates and compares; it binds nothing at all. -/
theorem matchDefault_defs {n : Nat} {env : Env} {ρ σ : VarEnv} {e : Exp} {v : Value}
    (h : matchDefault n env ρ e v = .ok σ) : σ.defs = ρ.defs :=
  (defsFixedAt_succ n).matchDefault env ρ e v σ h

/-- Matching a list of patterns pointwise leaves `defs` alone. -/
theorem matchExps_defs {n : Nat} {env : Env} {ρ σ : VarEnv} {es : List Exp}
    {vs : List Value} (h : matchExps n env ρ es vs = .ok σ) : σ.defs = ρ.defs :=
  (defsFixedAt_succ n).matchExps env ρ es vs σ h

/-- Matching a record pattern leaves `defs` alone. -/
theorem matchExpFields_defs {n : Nat} {env : Env} {ρ σ : VarEnv} {fs : List ExpField}
    {gs : List (AtomS × Value)} (h : matchExpFields n env ρ fs gs = .ok σ) :
    σ.defs = ρ.defs :=
  (defsFixedAt_succ n).matchExpFields env ρ fs gs σ h

/-- Matching an iteration pattern leaves `defs` alone. -/
theorem matchIterE_defs {n : Nat} {env : Env} {ρ σ : VarEnv} {e : Exp} {it : Iter}
    {ds : List Dom} {v : Value} (h : matchIterE n env ρ e it ds v = .ok σ) :
    σ.defs = ρ.defs :=
  (defsFixedAt_succ n).matchIterE env ρ e it ds v σ h

/-- The list case of `matchIterE` leaves `defs` alone. -/
theorem matchIterList_defs {n : Nat} {env : Env} {ρ σ : VarEnv} {e : Exp}
    {ds : List Dom} {ido : Option IL.Id} {vs : List Value}
    (h : matchIterList n env ρ e ds ido vs = .ok σ) : σ.defs = ρ.defs :=
  (defsFixedAt_succ n).matchIterList env ρ e ds ido vs σ h

/-! ### The corollary that matters in practice -/

/-- `evalExp` and `callDef` resolve a function name through
`(ρ.findDef? x).getD x` (`eval.ml:361-372`).  Since a successful match leaves
`defs` alone, that resolution is unaffected by any pattern matching done on
the way: a `findDef?` computed in the *initial* environment still governs. -/
theorem MatchExp.resolve {env : Env} {ρ σ : VarEnv} {e : Exp} {v : Value}
    (h : MatchExp env ρ e v σ) (x : IL.Id) :
    (σ.findDef? x).getD x = (ρ.findDef? x).getD x := by
  rw [h.findDef? x]

/-- Specialised to the case that actually arises.  `DefP` patterns occur only
in `matchArg`, so inside a rule's conclusion `findDef?` is uniformly `none`,
and name resolution is the identity however deep the match went. -/
theorem MatchExp.resolve_none {env : Env} {ρ σ : VarEnv} {e : Exp} {v : Value}
    (h : MatchExp env ρ e v σ) {x : IL.Id} (hx : ρ.findDef? x = none) :
    (σ.findDef? x).getD x = x := by
  rw [h.findDef? x, hx, Option.getD_none]

end

end Silmaril.SpecTec.Sem
