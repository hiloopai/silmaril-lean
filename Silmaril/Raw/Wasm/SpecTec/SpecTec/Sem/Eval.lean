module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Value
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Env
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.DecodeSound
public import Silmaril.Encoding.Relation

/-!
# A denotational semantics for SpecTec's internal language

Step 3 of `docs/projects/spectec/README.md`: the fuel-indexed evaluator, its
metatheory, and the relations it induces.  Everything is relative to the pin
`608711107b7f1edb13efd57b7d79b49477462d36`, whose evaluator is
`spectec/src/il/eval.ml` (1359 lines).

## What this is a semantics *of*

`eval.ml` is a **reduction on expressions**: `reduce_exp` (`eval.ml:220`)
rewrites an `Il.Ast.exp` towards a normal form, and an "IL value" there is an
expression that happens to be in normal form (`is_value_exp`, `eval.ml:211`).
Here an expression is instead *interpreted* into the separate domain
`Silmaril.SpecTec.Sem.Value`, so a value is a value and carries no syntax.
Every clause below names the `eval.ml` clause it comes from, and every place
where the value-directed reading forces a different answer is called out.

## Why fuel, and why three outcomes rather than two

Function clauses are tried in order and the first one that matches wins
(`reduce_exp_call`, `eval.ml:640-671`), and `ElsePr` is the trivially true
premise that marks the fallback clause (`eval.ml:694`).  "No earlier clause
applies" is a *negative* condition, so evaluation is not the least fixpoint of
a positive rule set and cannot be an ordinary Lean inductive predicate.  The
semantics is therefore a family of total functions indexed by a fuel budget,
with the relations recovered as `∃ n, … = .ok v` (`EvalExp` and friends
below).

A two-valued `Option Value` would not do.  Running out of fuel must *not* be
confused with a definite failure, because `callDef` falls through to the next
clause exactly when the current one definitely fails: if exhaustion also
counted as failure, a call could answer `v₂` at fuel `m` (clause 1 starved,
clause 2 fires) and `v₁ ≠ v₂` at fuel `n > m` (clause 1 fires), and
monotonicity in fuel would be false.  So the result type is

```
inductive Stuck where | undef | outOfFuel
abbrev Res (α) := Except Stuck α
```

which is exactly the trichotomy `eval.ml` itself works with: its `'a result`
is `('a, 'a) Result.t` (`eval.ml:18`) and its matching functions return
`subst option result`, so a step is either a definite answer (`Ok (Some _)`),
a definite failure (`Error _`), or "cannot tell" (`Ok None`).  `Res.ok`,
`Res.error .undef` and `Res.error .outOfFuel` line up with those three.

On "cannot tell" `eval.ml` consults the flag `assume_coherent_matches`
(`eval.ml:16`): when it is set — the default — a later clause's definite
answer is accepted anyway (`eval.ml:656-661,666-671`), on the assumption that
the clauses do not overlap.  We take the other branch of that flag, the one
`eval.ml:657,667` spells `if not !assume_coherent_matches then Ok None`, and
propagate `outOfFuel` outwards.  That choice is what makes monotonicity in
fuel (`monoAt_of_le`, `evalExp_ok_of_le`) true.

## In what sense this is conservative, and against which flag value

The claim is about the flag **alone**, with every other deviation held fixed:
`tryClauses` answers no more often, and never differently, than
`reduce_exp_call` run at the flag's **default** `true`.  Under the reading
`.ok` ↔ `Ok (Some _)`, `.error .undef` ↔ `Error _` and
`.error .outOfFuel` ↔ `Ok None`, the two searches agree clause by clause
except where we report `outOfFuel` and stop while the `true` branch moves on;
a "cannot tell" that we turn into a skip is also a skip there, since the
`true` branch takes a later clause's answer too (`eval.ml:658-661,668-670`).
This says nothing about the *other* deviations listed under "Scope" below —
`RulePr`, `DefA`, the one-sided short circuits and the comparison of types in
place of unification each change answers on their own.

Against the `false` branch — the branch this file otherwise transcribes —
not even that much holds, and it is worth being precise about why.  A value
domain has no stuck expressions, so wherever `eval.ml` can keep a partially
reduced expression and say "cannot tell", we must decide; four such `Ok None`
outcomes become `.error .undef` here, and a definite failure is precisely what
makes `tryClauses` *skip* a clause that `eval.ml` with the flag off would stop
the whole call on:

| situation | `eval.ml` | here |
| --- | --- | --- |
| `IfPr e` with `e` not a `BoolE` | `Ok None` (`eval.ml:692`) | `premHolds`: `undef` |
| `match_typ` structural mismatch | `Ok None` (`eval.ml:850`) | `matchTypV`: `undef` |
| `match_sym` structural mismatch | `Ok None` (`eval.ml:1118`) | `matchSymV`: `undef` |
| `Num.cmp` undefined on its pair | stuck `CmpE` (`eval.ml:267`) | `cmpValues`: `undef` |

`match_typ` reaches `Ok None` from three more places that `matchTypV` also
collapses — `eval.ml:834,839,843`, where a type application fails to reduce
any further.  The first and the last rows are the same phenomenon seen twice:
`eval.ml:267` returns the unreduced `CmpE` as a perfectly good `Ok`, and it is
the `IfPr` consuming it that reports `Ok None` at `eval.ml:692`.

## Fuel accounting

Every recursive call in the mutual block below is at fuel `n` when the caller
is at `n + 1`, *including* the steps of a list traversal.  That is not the
tightest accounting — a 1000-element list needs 1000 units of fuel to copy —
but it makes the whole block one recursion on `Nat`, and it makes
monotonicity one induction.  Since fuel is existentially quantified in every
statement of interest, nothing is lost.

## Coverage of the pinned corpus

The constructor counts quoted throughout this file were measured on the three
pinned streams in `specs/spectec/` together (`wasm-1.0`, `wasm-2.0`,
`wasm-3.0`; 315 + 467 + 976 top-level definitions) by walking the decoded
S-expressions with the `param`/`arg` disambiguation of
`Silmaril/SpecTec/IL/Decode.lean`.  The headline numbers are: 10639 `ExpA`,
316 `TypA`, 69 `DefA` and 119 `GramA` arguments, so all four argument forms
occur and all four are handled; 3676 `IterE` and 150 `IterPr`; 126 `ElsePr`;
and **zero** `TextE`, **zero** `TheE` and **zero** `LetPr`, which are
implemented all the same.
-/

@[expose] public section

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod

/-! ## Results

`eval.ml`'s `'a result = ('a, 'a) Result.t` (`eval.ml:18`) pairs a value with
a flag saying whether the computation got stuck; its matching functions add an
`option` on top, giving the three outcomes `Ok (Some _)`, `Ok None` and
`Error _`.  `Res` keeps the three outcomes and drops the partially reduced
expression, which has no counterpart in a value domain. -/

/-- The two ways a fuel-indexed evaluation can fail to produce a value. -/
inductive Stuck where
  /-- The expression has no value: an unbound variable, a type error, an
  out-of-range index, a division by zero.  This is `eval.ml`'s `Error _`,
  and also its `Ok e'` when `e'` is a stuck redex that no amount of further
  work can reduce. -/
  | undef
  /-- The fuel budget ran out.  This is the one outcome that more fuel can
  change, and the one that `evalExp_mono` is allowed to say nothing about. -/
  | outOfFuel
  deriving DecidableEq, Repr, Inhabited

/-- The result of a fuel-indexed evaluation step.  `Except` is used rather
than a bespoke inductive so that `do` notation, `>>=` and the `Monad`
simp set are available. -/
abbrev Res (α : Type) : Type := Except Stuck α

namespace Res

variable {α β : Type}

/-- Read a partial operation on values — `Value.cat?`, `Value.idx?`,
`Env.findDef?`, … — as a result whose failure is *definite*.  None of those
operations consumes fuel, so `none` can only mean `undef`. -/
def ofOption : Option α → Res α
  | none => .error .undef
  | some a => .ok a

@[simp] theorem ofOption_none : (ofOption none : Res α) = .error .undef := rfl

@[simp] theorem ofOption_some (a : α) : ofOption (some a) = .ok a := rfl

@[simp] theorem ofOption_eq_ok {o : Option α} {a : α} : ofOption o = .ok a ↔ o = some a := by
  cases o <;> simp [ofOption]

/-- `>>=` produces a definite answer exactly when both stages do. -/
@[simp] theorem bind_eq_ok {r : Res α} {f : α → Res β} {b : β} :
    (r >>= f) = .ok b ↔ ∃ a, r = .ok a ∧ f a = .ok b := by
  cases r <;> simp [Bind.bind, Except.bind]

/-- `Functor.map` produces a definite answer exactly when its argument does. -/
@[simp] theorem map_eq_ok {r : Res α} {f : α → β} {b : β} :
    (f <$> r) = .ok b ↔ ∃ a, r = .ok a ∧ f a = b := by
  cases r <;> simp [Functor.map, Except.map, eq_comm]

/-- Run `r` only if a decidable side condition holds, and fail definitely
otherwise.  This is the value-level reading of `eval.ml`'s `when` guards,
whose failure branch is always an `Error` or a non-matching clause. -/
def assert (c : Prop) [Decidable c] (r : Res α) : Res α :=
  if c then r else .error .undef

@[simp] theorem assert_pos {c : Prop} [Decidable c] (h : c) (r : Res α) :
    assert c r = r := by simp [assert, h]

@[simp] theorem assert_neg {c : Prop} [Decidable c] (h : ¬ c) (r : Res α) :
    assert c r = .error .undef := by simp [assert, h]

@[simp] theorem assert_eq_ok {c : Prop} [Decidable c] {r : Res α} {a : α} :
    assert c r = .ok a ↔ c ∧ r = .ok a := by
  by_cases h : c <;> simp [assert, h]

/-- Case analysis that distinguishes a *definite* failure from fuel
exhaustion: `f` consumes a definite answer, `g` is the fallback taken only on
`undef`, and `outOfFuel` propagates.

This is the single place where the three-valued result earns its keep.  It is
`eval.ml`'s dispatch on `subst option result` with `assume_coherent_matches`
turned *off* (`eval.ml:655-657,665-667`): a definite match failure moves on to
the next alternative, while "cannot tell" stops the search.  Propagating
rather than continuing is exactly what makes the evaluator monotone in its
fuel. -/
def elimUndef (r : Res α) (f : α → Res β) (g : Unit → Res β) : Res β :=
  match r with
  | .ok a => f a
  | .error .outOfFuel => .error .outOfFuel
  | .error .undef => g ()

@[simp] theorem elimUndef_ok (a : α) (f : α → Res β) (g : Unit → Res β) :
    elimUndef (.ok a) f g = f a := rfl

@[simp] theorem elimUndef_undef (f : α → Res β) (g : Unit → Res β) :
    elimUndef (.error .undef) f g = g () := rfl

@[simp] theorem elimUndef_oof (f : α → Res β) (g : Unit → Res β) :
    elimUndef (.error .outOfFuel) f g = .error .outOfFuel := rfl

/-- Try the `k + 1` alternatives `f i, f (i+1), …, f (i+k)` in order and take
the first *definite* answer.

This is `elimUndef` iterated, and it exists for exactly one caller: the
`CatE` clause of `matchExp` when neither operand's length is known, where the
alternatives are the splits of the matched list.  Stopping on `outOfFuel`
rather than moving on is the whole point — an alternative that merely ran out
of fuel must not be mistaken for one that definitely fails, or more fuel
would change the answer and `monoAt_succ` would be false. -/
def scan (f : Nat → Res α) (i : Nat) : Nat → Res α
  | 0 => f i
  | k+1 => elimUndef (f i) (fun a => .ok a) (fun _ => scan f (i+1) k)

@[simp] theorem scan_zero (f : Nat → Res α) (i : Nat) : scan f i 0 = f i := rfl

/-- One step of the search, as `elimUndef`. -/
theorem scan_succ (f : Nat → Res α) (i k : Nat) :
    scan f i (k+1) = elimUndef (f i) (fun a => .ok a) (fun _ => scan f (i+1) k) := rfl

/-- The first alternative answered, so the search answered. -/
theorem scan_succ_ok {f : Nat → Res α} {i k : Nat} {a : α} (h : f i = .ok a) :
    scan f i (k+1) = .ok a := by rw [scan_succ, h, elimUndef_ok]

/-- The first alternative failed definitely, so the search moves on. -/
theorem scan_succ_undef {f : Nat → Res α} {i k : Nat} (h : f i = .error .undef) :
    scan f i (k+1) = scan f (i+1) k := by rw [scan_succ, h, elimUndef_undef]

/-- The first alternative ran out of fuel, so the search stops. -/
theorem scan_succ_oof {f : Nat → Res α} {i k : Nat} (h : f i = .error .outOfFuel) :
    scan f i (k+1) = .error .outOfFuel := by rw [scan_succ, h, elimUndef_oof]

/-- **Soundness of the search**: whatever it answers, one of its
alternatives answered it. -/
theorem scan_eq_ok {f : Nat → Res α} {a : α} :
    ∀ (k i : Nat), scan f i k = .ok a → ∃ j, i ≤ j ∧ j ≤ i + k ∧ f j = .ok a
  | 0, i, h => ⟨i, Nat.le_refl _, Nat.le_add_right _ _, h⟩
  | k+1, i, h => by
      cases hf : f i with
      | ok b =>
          rw [scan_succ_ok hf] at h
          exact ⟨i, Nat.le_refl _, by omega, by rw [hf]; exact h⟩
      | error s =>
          cases s with
          | undef =>
              rw [scan_succ_undef hf] at h
              obtain ⟨j, hj₁, hj₂, hj₃⟩ := scan_eq_ok k (i+1) h
              exact ⟨j, by omega, by omega, hj₃⟩
          | outOfFuel => rw [scan_succ_oof hf] at h; exact absurd h (by simp)

/-- **Completeness of the search**: the first alternative that answers is the
one it takes. -/
theorem scan_eq_of_lt {f : Nat → Res α} {a : α} :
    ∀ (k i m : Nat), i ≤ m → m ≤ i + k → f m = .ok a →
      (∀ j, i ≤ j → j < m → f j = .error .undef) → scan f i k = .ok a
  | 0, i, m, h₁, h₂, hm, _ => by
      have : m = i := by omega
      subst this; exact hm
  | k+1, i, m, h₁, h₂, hm, hlt => by
      rcases Nat.eq_or_lt_of_le h₁ with rfl | hi
      · exact scan_succ_ok hm
      · rw [scan_succ_undef (hlt i (Nat.le_refl _) hi)]
        exact scan_eq_of_lt k (i+1) m hi (by omega) hm fun j hj hjm => hlt j (by omega) hjm

/-! ### The monotonicity order

`r₁ ⊑ r₂` says that `r₂` refines `r₁`: either `r₁` was only ever "out of
fuel", or the two agree.  This is the relation in which the whole evaluator
is monotone in its fuel. -/

/-- `r₁ ⊑ r₂`: `r₂` answers whatever `r₁` answered, unless `r₁` ran out of
fuel. -/
def Le (r₁ r₂ : Res α) : Prop := r₁ = .error .outOfFuel ∨ r₂ = r₁

@[inherit_doc] scoped infix:50 " ⊑ " => Res.Le

@[refl] theorem Le.refl (r : Res α) : r ⊑ r := Or.inr rfl

theorem Le.trans {r₁ r₂ r₃ : Res α} (h₁ : r₁ ⊑ r₂) (h₂ : r₂ ⊑ r₃) : r₁ ⊑ r₃ := by
  rcases h₁ with h₁ | h₁
  · exact Or.inl h₁
  · subst h₁; exact h₂

/-- Out of fuel is below everything. -/
theorem oof_le (r : Res α) : (.error .outOfFuel : Res α) ⊑ r := Or.inl rfl

/-- A definite answer is only below itself. -/
theorem Le.eq_of_ne_oof {r₁ r₂ : Res α} (h : r₁ ⊑ r₂)
    (hne : r₁ ≠ .error .outOfFuel) : r₂ = r₁ := by
  rcases h with h | h
  · exact absurd h hne
  · exact h

/-- The form the monotonicity theorems are used in. -/
theorem Le.ok {r₁ r₂ : Res α} {a : α} (h : r₁ ⊑ r₂) (ha : r₁ = .ok a) :
    r₂ = .ok a := by
  rcases h with h | h
  · exact absurd (ha ▸ h) (by simp)
  · exact h.trans ha

/-- `>>=` is monotone in both arguments. -/
theorem bind_le {r₁ r₂ : Res α} {f₁ f₂ : α → Res β} (hr : r₁ ⊑ r₂)
    (hf : ∀ a, f₁ a ⊑ f₂ a) : (r₁ >>= f₁) ⊑ (r₂ >>= f₂) := by
  rcases hr with hr | hr
  · subst hr; exact Or.inl rfl
  · subst hr
    cases r₂ with
    | error e => exact Or.inr rfl
    | ok a => exact hf a

/-- The special case where only the scrutinee moves. -/
theorem bind_le_left {r₁ r₂ : Res α} (f : α → Res β) (hr : r₁ ⊑ r₂) :
    (r₁ >>= f) ⊑ (r₂ >>= f) := bind_le hr (fun _ => Le.refl _)

/-- `Functor.map` is monotone. -/
theorem map_le {r₁ r₂ : Res α} (f : α → β) (hr : r₁ ⊑ r₂) :
    (f <$> r₁) ⊑ (f <$> r₂) := by
  rcases hr with hr | hr
  · subst hr; exact Or.inl rfl
  · subst hr; exact Or.inr rfl

/-- `List.mapM` is monotone pointwise. -/
theorem mapM_le {f₁ f₂ : α → Res β} (hf : ∀ a, f₁ a ⊑ f₂ a) :
    ∀ xs : List α, xs.mapM f₁ ⊑ xs.mapM f₂
  | [] => Le.refl _
  | x :: xs => by
      simp only [List.mapM_cons]
      exact bind_le (hf x) fun _ => bind_le (mapM_le hf xs) fun _ => Le.refl _

/-- `List.foldlM` is monotone in the step function. -/
theorem foldlM_le {f₁ f₂ : β → α → Res β} (hf : ∀ b a, f₁ b a ⊑ f₂ b a) :
    ∀ (xs : List α) (b : β), xs.foldlM f₁ b ⊑ xs.foldlM f₂ b
  | [], _ => Le.refl _
  | x :: xs, b => by
      simp only [List.foldlM_cons]
      exact bind_le (hf b x) fun b' => foldlM_le hf xs b'

/-- `assert` is monotone. -/
theorem assert_le {c : Prop} [Decidable c] {r₁ r₂ : Res α} (h : r₁ ⊑ r₂) :
    assert c r₁ ⊑ assert c r₂ := by
  by_cases hc : c
  · simpa [assert, hc] using h
  · simp only [assert, hc, ite_false]
    exact Le.refl _

/-- `Except.isOk` is monotone: a definite answer stays. -/
theorem isOk_le {r₁ r₂ : Res α} (h : r₁ ⊑ r₂) (h₁ : r₁.isOk = true) : r₂.isOk = true := by
  rcases h with h | h
  · rw [h] at h₁; exact absurd h₁ (by simp [Except.isOk, Except.toBool])
  · rw [h]; exact h₁

/-- `elimUndef` is monotone.  This is the step where the design pays off: the
fallback `g` is taken on *both* sides or on neither, because a definite
failure stays a definite failure when the fuel grows. -/
theorem elimUndef_le {r₁ r₂ : Res α} {f₁ f₂ : α → Res β} {g₁ g₂ : Unit → Res β}
    (hr : r₁ ⊑ r₂) (hf : ∀ a, f₁ a ⊑ f₂ a) (hg : ∀ u, g₁ u ⊑ g₂ u) :
    elimUndef r₁ f₁ g₁ ⊑ elimUndef r₂ f₂ g₂ := by
  rcases hr with hr | hr
  · subst hr; exact Or.inl rfl
  · subst hr
    cases r₂ with
    | ok a => exact hf a
    | error e => cases e with
      | undef => exact hg ()
      | outOfFuel => exact Or.inl rfl

/-- `scan` is monotone: each alternative moves up, and because `elimUndef`
takes its fallback on both sides or on neither, the search visits the same
alternatives on both sides. -/
theorem scan_le {f₁ f₂ : Nat → Res α} (hf : ∀ j, f₁ j ⊑ f₂ j) :
    ∀ (k i : Nat), scan f₁ i k ⊑ scan f₂ i k
  | 0, i => hf i
  | k+1, i => by
      rw [scan_succ, scan_succ]
      exact elimUndef_le (hf i) (fun _ => Le.refl _) fun _ => scan_le hf k (i+1)

end Res


/-! ## Syntactic equality on types and grammar symbols

`match_typ` (`eval.ml:815`) and `match_sym` (`eval.ml:1102`) fall back on
structural comparison once neither side is a pattern variable.  `IL.Typ` and
`IL.Sym` sit in a nested, mutually recursive group, so Lean's `deriving`
handler cannot give them `DecidableEq`, and `Silmaril/SpecTec/IL/Ast.lean`
derives only `Repr` and `Inhabited`.  Rather than transcribe a
twenty-constructor `decEq` by hand, equality is decided *through the printer*:
`Silmaril/SpecTec/IL/Print.lean` sends each syntactic class to an `SExp`,
`SExp` does have `DecidableEq`, and `Silmaril/SpecTec/IL/DecodeSound.lean`
proves the printer injective by exhibiting a left inverse.  The two
`*_iff` lemmas below are the whole interface. -/

/-- Structural equality of types, decided through `IL.typS`. -/
def typEq (t₁ t₂ : Typ) : Bool := typS t₁ == typS t₂

/-- `typEq` decides equality of types: `decodeTyp?` is a left inverse of
`typS` (`decodeTyp?_typS`), so `typS` is injective. -/
@[simp] theorem typEq_iff {t₁ t₂ : Typ} : typEq t₁ t₂ = true ↔ t₁ = t₂ := by
  constructor
  · intro h
    have h' : typS t₁ = typS t₂ := by simpa [typEq] using h
    have := decodeTyp?_typS t₁
    rw [h', decodeTyp?_typS t₂] at this
    exact (Option.some_inj.mp this).symm
  · rintro rfl; simp [typEq]

/-- Structural equality of grammar symbols, decided through `IL.symS`. -/
def symEq (g₁ g₂ : Sym) : Bool := symS g₁ == symS g₂

/-- `symEq` decides equality of grammar symbols (`decodeSym?_symS`). -/
@[simp] theorem symEq_iff {g₁ g₂ : Sym} : symEq g₁ g₂ = true ↔ g₁ = g₂ := by
  constructor
  · intro h
    have h' : symS g₁ = symS g₂ := by simpa [symEq] using h
    have := decodeSym?_symS g₁
    rw [h', decodeSym?_symS g₂] at this
    exact (Option.some_inj.mp this).symm
  · rintro rfl; simp [symEq]

/-! ## Two numeric predicates `Sem/Value.lean` does not need

`match_exp'` inverts a unary sign (`eval.ml:900-904`), which needs
`Xl.Num.is_neg` (`spectec/src/xl/num.ml:191-195`) and `Xl.Num.abs`
(`num.ml:115-120`).  No other part of the evaluator uses them, so they live
here rather than in `Silmaril/SpecTec/Sem/Value.lean`. -/

namespace Num

/-- `Xl.Num.is_neg` (`spectec/src/xl/num.ml:191-195`).  A `` `Real `` stores
only its rendering (`Silmaril/SpecTec/IL/Ast.lean`), so `r < 0.0`
(`num.ml:195`) is not computable and the answer is `false`; the only caller
goes on to ask for `absN`, which is `none` on a `realN` anyway. -/
def isNeg : Num → Bool
  | .natN _ => false
  | .intN i => i < 0
  | .ratN q => q < 0
  | .realN _ => false

/-- `Xl.Num.abs` (`spectec/src/xl/num.ml:115-120`).  `num.ml:120` takes
`Float.abs` of a float, which a stored rendering cannot support, so that
clause is `none`. -/
def absN : Num → Option Num
  | .natN n => some (.natN n)
  | .intN i => some (.intN (i.natAbs : Int))
  | .ratN q => some (.ratN (if q < 0 then -q else q))
  | .realN _ => none

end Num

/-! ## Evaluated arguments, and the variable environment -/

/-- The environment an expression is evaluated in: one map per namespace a
*parameter* or a *binder* can live in.

This is the value-level counterpart of `Il.Subst.subst`
(`spectec/src/il/subst.ml:9-10`), which has exactly these four maps.
`eval.ml` applies a substitution to the syntax and then reduces; we carry the
environment instead, which is the same thing for a closed value semantics and
avoids having to transcribe `subst.ml`.

`VarEnv` is deliberately separate from `Sem.Env` (`spectec/src/il/env.ml`):
`Env` holds the *script* — the type, relation, function and grammar
definitions — and never changes during evaluation, while `VarEnv` is the
local scope and changes constantly. -/
structure VarEnv where
  /-- Term variables: `ExpP` parameters, and the binders of a clause, a rule
  or an iteration (`subst.ml:9`, `varid`). -/
  vals : Map Value
  /-- Type variables: `TypP` parameters (`subst.ml:9`, `typid`). -/
  typs : Map Typ
  /-- Definition variables: `DefP` parameters, each bound to the name of a
  global definition (`subst.ml:9`, `defid`). -/
  defs : Map IL.Id
  /-- Grammar variables: `GramP` parameters (`subst.ml:9`, `gramid`). -/
  grams : Map Sym
  deriving Repr, Inhabited

namespace VarEnv

/-- The empty scope (`Subst.empty`, `spectec/src/il/subst.ml:13-18`). -/
def empty : VarEnv := ⟨Map.empty, Map.empty, Map.empty, Map.empty⟩

/-- `Subst.find_varid` (`spectec/src/il/subst.ml:25`). -/
def findVal? (ρ : VarEnv) (x : IL.Id) : Option Value := ρ.vals.find? x

/-- `Subst.find_typid` (`spectec/src/il/subst.ml:26`). -/
def findTyp? (ρ : VarEnv) (x : IL.Id) : Option Typ := ρ.typs.find? x

/-- `Subst.find_defid` (`spectec/src/il/subst.ml:27`). -/
def findDef? (ρ : VarEnv) (x : IL.Id) : Option IL.Id := ρ.defs.find? x

/-- `Subst.find_gramid` (`spectec/src/il/subst.ml:28`). -/
def findGram? (ρ : VarEnv) (x : IL.Id) : Option Sym := ρ.grams.find? x

/-- `Subst.add_varid` (`spectec/src/il/subst.ml:30`); `Map.bind` already drops
the wildcard `"_"`. -/
def bindVal (ρ : VarEnv) (x : IL.Id) (v : Value) : VarEnv :=
  { ρ with vals := ρ.vals.bind x v }

/-- `Subst.add_typid` (`spectec/src/il/subst.ml:31`). -/
def bindTyp (ρ : VarEnv) (x : IL.Id) (t : Typ) : VarEnv :=
  { ρ with typs := ρ.typs.bind x t }

/-- `Subst.add_defid` (`spectec/src/il/subst.ml:32`), *with the two arguments
in the order the name suggests*: the pattern's identifier is bound to the
actual one.  See `matchArg` for why `eval.ml:1131` has them the other way
round. -/
def bindDef (ρ : VarEnv) (x y : IL.Id) : VarEnv :=
  { ρ with defs := ρ.defs.bind x y }

/-- `Subst.add_gramid` (`spectec/src/il/subst.ml:33`). -/
def bindGram (ρ : VarEnv) (x : IL.Id) (g : Sym) : VarEnv :=
  { ρ with grams := ρ.grams.bind x g }

/-- Bind a list of term variables left to right, so later entries shadow
earlier ones.  This is how one round of an iteration enters scope. -/
def bindVals (ρ : VarEnv) (xs : List (IL.Id × Value)) : VarEnv :=
  { ρ with vals := ρ.vals.binds xs }

/-- Look every identifier up in the term namespace, failing if any is
unbound.  Used to read an iteration's bindings back out after the body has
been matched (`eval.ml:1021-1027`). -/
def findVals? (ρ : VarEnv) (xs : List IL.Id) : Option (List Value) :=
  xs.mapM ρ.findVal?

@[simp] theorem bindVals_nil (ρ : VarEnv) : ρ.bindVals [] = ρ := rfl

@[simp] theorem findVals?_nil (ρ : VarEnv) : ρ.findVals? [] = some [] := rfl

end VarEnv

/-! ## Transposing an iteration

An `iterexp` is an `Iter` together with a list of domains `(x, e)`
(`spectec/src/il/ast.ml:95`): each `x` ranges over the successive elements of
the list — or the contents of the option — that `e` denotes, and the body runs
once per index.  `eval.ml` implements that by substitution
(`eval.ml:406-415`): it projects the `i`-th element out of every domain list,
builds a substitution from it, and reduces the body under it.  The two
helpers below are the same projection, as data. -/

/-- The bindings in force during round `i` of an iteration: the `i`-th element
of every domain, plus the iteration counter if the `ListN` names one
(`eval.ml:407-413`). -/
def iterRow (ds : List (IL.Id × List Value)) (ido : Option IL.Id) (i : Nat) :
    List (IL.Id × Value) :=
  ds.filterMap (fun d => (d.2[i]?).map fun v => (d.1, v)) ++
    (ido.map fun y => (y, Value.num (.natN i))).toList

/-- `iterRow` for every round, in order; `k` is the number of rounds
(`eval.ml:406`, `List.init n`). -/
def iterRows (ds : List (IL.Id × List Value)) (ido : Option IL.Id) (k : Nat) :
    List (List (IL.Id × Value)) :=
  (List.range k).map (iterRow ds ido)

/-- The `j`-th component of every row: used in the *pattern* direction, where
each round of a matched iteration contributes one value per domain variable
and the columns are what the domain expressions are matched against
(`eval.ml:1021-1027`). -/
def iterCol (rows : List (List Value)) (j : Nat) : List Value :=
  rows.filterMap fun r => r[j]?

/-- Every column of `rows`, as a list value apiece; `k` is the number of
domains. -/
def iterCols (rows : List (List Value)) (k : Nat) : List Value :=
  (List.range k).map fun j => Value.list (iterCol rows j)


/-! ## Pure auxiliaries of the evaluator

Everything in this section is fuel-free: it either inspects syntax or
combines values that have already been computed. -/

/-- The variable an iteration domain binds (`spectec/src/il/ast.ml:95`). -/
def domVar : Dom → IL.Id
  | .mk x _ => x

/-- The expression an iteration domain ranges over
(`spectec/src/il/ast.ml:95`). -/
def domSrc : Dom → Exp
  | .mk _ e => e

/-- `Xl.Bool.bin` (`spectec/src/xl/bool.ml:29-34`), as a partial operation on
the IL's `binop`: the four numeric operators are not `Xl.Bool.binop`
(`bool.ml:4`) and are `none` here. -/
def boolBin : BinOp → Bool → Bool → Option Bool
  | .andOp, b₁, b₂ => some (b₁ && b₂)
  | .orOp, b₁, b₂ => some (b₁ || b₂)
  | .implOp, b₁, b₂ => some (!b₁ || b₂)
  | .equivOp, b₁, b₂ => some (b₁ == b₂)
  | _, _, _ => none

/-- The short-circuiting half of `Xl.Bool.bin_partial`
(`spectec/src/xl/bool.ml:36-47`): the cases in which the *left* operand alone
settles the answer.

`bool.ml:40,42,44-46` is the symmetric half: it also settles `_ ∧ false`,
`_ ∨ true` and `_ ⇒ true` from the right operand when the left one is stuck.  That half is
deliberately dropped, and dropping it is forced: an `undef` left operand with
a right operand that only becomes `false` once there is enough fuel would make
the whole conjunction `undef` at small fuel and `false` at large fuel, so
`evalExp_mono` would be false.  We are strictly less defined than `eval.ml`
here, never differently defined. -/
def boolShort : BinOp → Value → Option Value
  | .andOp, .bool false => some (.bool false)
  | .orOp, .bool true => some (.bool true)
  | .implOp, .bool false => some (.bool true)
  | _, _ => none

/-- A binary operator applied to two values.

`eval.ml:240-255` dispatches on the operator: a `Xl.Bool.binop` goes to
`Bool.bin_partial` and a `Xl.Num.binop` to `Num.bin_partial`
(`spectec/src/xl/num.ml:232-275`).  Once *both* operands are values, both of
those reduce to `Xl.Bool.bin` (`bool.ml:29`) and `Xl.Num.bin` (`num.ml:134`)
respectively (`bool.ml:38`, `num.ml:234-238`), which is what this is.

`Num.bin_partial`'s remaining clauses (`num.ml:256-274`) — `0 + e`, `e * 0`,
`e ^ 0`, `0 / e`, … — fire only when the *other* operand is stuck, and are
dropped for the same reason as the right-biased boolean short circuits: at
small fuel `0 * e` would be `0` and at large fuel, if `e` turns out to be a
`rat`, `Num.bin` rejects the mixed pair (`num.ml:174`) and the answer would
change.  `Silmaril/SpecTec/Sem/Value.lean` has `Num.bin` itself. -/
def binValues : BinOp → Value → Value → Res Value
  | op, .bool b₁, .bool b₂ => Res.ofOption ((boolBin op b₁ b₂).map Value.bool)
  | op, .num m₁, .num m₂ => Res.ofOption ((Num.bin op m₁ m₂).map Value.num)
  | _, _, _ => .error .undef

/-- A comparison applied to two values (`eval.ml:256-270`).

`eqOp` and `neOp` are settled by structural equality of the reduced operands
(`eval.ml:260-263`, `Eq.eq_exp`), which on the value domain is
`Value`'s `DecidableEq`; the four order comparisons are `Xl.Num.cmp`
(`num.ml:277-303`), which is defined only on two numerals of the same
constructor.  `eval.ml:267` leaves a failed `Num.cmp` as a stuck `CmpE`
rather than an error; both are "no value" here. -/
def cmpValues : CmpOp → Value → Value → Res Value
  | .eqOp, v₁, v₂ => .ok (.bool (v₁ == v₂))
  | .neOp, v₁, v₂ => .ok (.bool (!(v₁ == v₂)))
  | op, .num m₁, .num m₂ => Res.ofOption ((Num.cmp op m₁ m₂).map Value.bool)
  | _, _, _ => .error .undef

/-- A unary operator applied to a value (`eval.ml:227-238`): `NotOp` is
`Xl.Bool.un` (`spectec/src/xl/bool.ml:25-27`) and the two signs are
`Xl.Num.un` (`num.ml:122-132`).  `eval.ml:236-237` additionally cancels a
double negation, which is a syntactic rewrite with nothing to do on values. -/
def unValue : UnOp → Value → Res Value
  | .notOp, .bool b => .ok (.bool (!b))
  | op, .num m => Res.ofOption ((Num.un op m).map Value.num)
  | _, _ => .error .undef

/-- `MemE` applied to two values (`eval.ml:339-350`): membership in an option
is equality with its contents (`eval.ml:343-344`) and membership in a list is
`List.exists` (`eval.ml:346-348`), both decided by `Value`'s `DecidableEq`
where `eval.ml` uses `Eq.eq_exp` on reduced expressions. -/
def memValue : Value → Value → Res Value
  | _, .opt none => .ok (.bool false)
  | v, .opt (some w) => .ok (.bool (v == w))
  | v, .list ws => .ok (.bool (ws.contains v))
  | _, _ => .error .undef

/-- Shallow resolution of a `TypA` argument through the scope.

`eval.ml:636` does not reduce a type argument at all ("types are reduced on
demand"), and `Subst.subst_typ` (`spectec/src/il/subst.ml`) would substitute
everywhere.  We substitute only at the head, which is all `matchTypV` can
observe; a full `subst.ml` is not part of an untyped value semantics and is
not transcribed. -/
def resolveTyp (ρ : VarEnv) : Typ → Typ
  | .varT x [] => (ρ.findTyp? x).getD (.varT x [])
  | t => t

/-- Shallow resolution of a `GramA` argument through the scope; see
`resolveTyp`. -/
def resolveSym (ρ : VarEnv) : Sym → Sym
  | .varG x [] => (ρ.findGram? x).getD (.varG x [])
  | g => g

/-- Match a type *pattern* against a type argument (`match_typ`,
`eval.ml:815-850`), restricted to the part an untyped semantics can use.

Three clauses survive.  A pattern `VarT (x, [])` with `x` already in the
scope is non-linear and must agree (`eval.ml:821-822`); one whose `x` is not
a *global* type name is a fresh pattern variable and binds (`eval.ml:823-825`,
"an unbound type is treated as a pattern variable"); anything else is matched
structurally.  `eval.ml:826-850` additionally reduces type applications and
descends into `TupT`/`IterT` to unify sub-patterns; that is type-level
computation (`reduce_typ`, `eval.ml:107`), which belongs to `Sem/Type.lean`,
so here a non-variable pattern is only compared, never decomposed. -/
def matchTypV (env : Env) (ρ : VarEnv) (pat t : Typ) : Res VarEnv :=
  match pat with
  | .varT x [] =>
      match ρ.findTyp? x with
      | some t' => if typEq t' t then .ok ρ else .error .undef
      | none =>
          if env.memTyp x then
            (if typEq (.varT x []) t then .ok ρ else .error .undef)
          else .ok (ρ.bindTyp x t)
  | _ => if typEq pat t then .ok ρ else .error .undef

/-- Match a grammar-symbol *pattern* against a grammar argument
(`match_sym`, `eval.ml:1102-1119`), with the same three clauses as
`matchTypV`: non-linear re-use (`eval.ml:1108-1109`), a fresh pattern
variable when the name is not a global grammar (`eval.ml:1110-1112`), and
structural comparison otherwise.  `eval.ml:1113-1117` decomposes `VarG` and
`IterG`; decomposition needs grammar-level reduction and is left to
`Sem/Grammar.lean`. -/
def matchSymV (env : Env) (ρ : VarEnv) (pat g : Sym) : Res VarEnv :=
  match pat with
  | .varG x [] =>
      match ρ.findGram? x with
      | some g' => if symEq g' g then .ok ρ else .error .undef
      | none =>
          if env.memGram x then
            (if symEq (.varG x []) g then .ok ρ else .error .undef)
          else .ok (ρ.bindGram x g)
  | _ => if symEq pat g then .ok ρ else .error .undef

/-- Bind a parameter list to an argument list positionally.

This is *not* how a function call binds its arguments: a `DecD` clause carries
its own argument *patterns* (`DefD (_, args, _, _)`,
`spectec/src/il/ast.ml:149`) and `reduce_exp_call` matches against those
(`eval.ml:654`).  A `RelD` rule does not (`RuleD` has no `arg list`,
`ast.ml:145`), so the relation's parameters are bound positionally instead;
that is what `derives` uses this for. -/
def bindParams (ρ : VarEnv) : List Param → List ArgV → Option VarEnv
  | [], [] => some ρ
  | .expP x _ :: ps, .val v :: as => bindParams (ρ.bindVal x v) ps as
  | .typP x :: ps, .typ t :: as => bindParams (ρ.bindTyp x t) ps as
  | .defP x _ _ :: ps, .defName y :: as => bindParams (ρ.bindDef x y) ps as
  | .gramP x _ _ :: ps, .gram g :: as => bindParams (ρ.bindGram x g) ps as
  | _, _ => none


/-- Does `v` lie in the subtype `t` of a `SubE` argument pattern, as far as the
value can show it?  (Silmaril change, see `docs/projects/spectec/README.md`.)

`eval.ml`'s matcher tests the subtype of a `SubE` pattern before descending
(`eval.ml:1035-1068`, `sub_typ` on the value's type).  Values here carry no
type, so the test is the one a value can answer: when `t` is a parameterless
global type whose single instance is a `VariantT` (`Inn`, `Fnn`, `numtype`,
`packtype`, …) and `v` is a `case`, the case's operator must be one of `t`'s.
Every other shape passes (a local type variable, a type family, a non-case
value): the test only ever rejects a value that is definitely outside `t`.

Without it, the first clause or instance whose argument is `(Inn <: numtype)`
captures `F32`/`F64` as well: `num_(F32)` is read as `iN(32)` and
`$binop_(F32, ADD, …)` as `$iadd_`. -/
def subCaseOk (env : Env) (ρ : VarEnv) : Typ → Value → Bool
  | .varT x [], .case op _ =>
      match ρ.findTyp? x with
      | some _ => true
      | none =>
          match env.findTyp? x with
          | some (_, [.instD [] [] (.variantT cs)]) =>
              cs.any fun | .mk op' _ _ _ => decide (op' = op)
          | _ => true
  | _, _ => true

/-- The subtype test of a top-level `SubE` argument pattern (`subCaseOk`); every
other pattern passes. -/
def argSubOk (env : Env) (ρ : VarEnv) : Exp → Value → Bool
  | .subE _ t _, v => subCaseOk env ρ t v
  | _, _ => true


/-! ## The evaluator

One mutual block, every member indexed by fuel, every recursive call at `n`
when the caller is at `n + 1`.  Which forms of expression are *patterns* and
which are only *evaluated* is decided in `matchExp`; see its docstring. -/

mutual

/-- Evaluate an expression (`reduce_exp`, `eval.ml:220-537`).

`eval.ml` rewrites an expression towards a normal form and reads the value
off it; here the expression is interpreted directly into `Value`.  The clause
for each constructor cites the `eval.ml` clause it comes from.  Two whole
families of `eval.ml` clauses have no counterpart because they are *syntactic*
rewrites on partially reduced terms rather than facts about values: the
cancellations `~~e ↝ e` and `--e ↝ e` (`eval.ml:236-237`), and the
type-directed re-coercions `SubE` performs on a tuple, a record or a case
(`eval.ml:502-533`). -/
def evalExp : Nat → Env → VarEnv → Exp → Res Value
  | 0, _, _, _ => .error .outOfFuel
  -- `VarE` (`eval.ml:226`).  `eval.ml` has already substituted, so a variable
  -- is irreducible there; here it is looked up, and an unbound one has no
  -- value.
  | _+1, _, ρ, .varE x => Res.ofOption (ρ.findVal? x)
  | _+1, _, _, .boolE b => .ok (.bool b)
  | _+1, _, _, .numE n => .ok (.num n)
  -- `TextE` (`eval.ml:226`); zero occurrences in the pinned corpus.
  | _+1, _, _, .textE t => .ok (.text t)
  | n+1, env, ρ, .unE op _ e => do
      let v ← evalExp n env ρ e
      unValue op v
  -- `BinE` (`eval.ml:240-255`), left-biased short circuit; see `boolShort`.
  | n+1, env, ρ, .binE op _ e₁ e₂ => do
      let v₁ ← evalExp n env ρ e₁
      match boolShort op v₁ with
      | some v => .ok v
      | none => do
          let v₂ ← evalExp n env ρ e₂
          binValues op v₁ v₂
  | n+1, env, ρ, .cmpE op _ e₁ e₂ => do
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      cmpValues op v₁ v₂
  -- `TupE` (`eval.ml:358-360`).
  | n+1, env, ρ, .tupE es => Value.tuple <$> evalExps n env ρ es
  -- `ProjE` (`eval.ml:421-426`).  The index is an `Int` because
  -- `print.ml:119` renders it with `string_of_int`; a negative one indexes
  -- nothing.
  | n+1, env, ρ, .projE e i => do
      let v ← evalExp n env ρ e
      let vs ← Res.ofOption v.asTuple?
      Res.ofOption (if 0 ≤ i then vs[i.toNat]? else none)
  -- `CaseE` (`eval.ml:469-483`); the `check` flag the two clauses differ in
  -- is not part of `IL.Exp` (`Silmaril/SpecTec/IL/Ast.lean`).
  | n+1, env, ρ, .caseE op e => Value.case op <$> evalExp n env ρ e
  -- `UncaseE` (`eval.ml:427-434`): a different mixop is an error
  -- (`eval.ml:430-431`).
  | n+1, env, ρ, .uncaseE e op => do
      let v ← evalExp n env ρ e
      let (op', w) ← Res.ofOption v.asCase?
      Res.assert (op' = op) (.ok w)
  | _+1, _, _, .optE none => .ok (.opt none)
  | n+1, env, ρ, .optE (some e) => (fun v => Value.opt (some v)) <$> evalExp n env ρ e
  -- `TheE` (`eval.ml:442-448`); zero occurrences in the pinned corpus.
  | n+1, env, ρ, .theE e => do
      let v ← evalExp n env ρ e
      let o ← Res.ofOption v.asOpt?
      Res.ofOption o
  -- `StrE` (`eval.ml:306-311`).
  | n+1, env, ρ, .strE fs => Value.struct <$> evalExpFields n env ρ fs
  -- `DotE` (`eval.ml:312-318`), `Value.field?`.
  | n+1, env, ρ, .dotE e a => do
      let v ← evalExp n env ρ e
      Res.ofOption (v.field? a)
  -- `CompE` (`eval.ml:319-338`), `Value.comp?`.
  | n+1, env, ρ, .compE e₁ e₂ => do
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      Res.ofOption (Value.comp? v₁ v₂)
  -- `ListE` (`eval.ml:449-451`).
  | n+1, env, ρ, .listE es => Value.list <$> evalExps n env ρ es
  -- `LiftE` (`eval.ml:452-458`).
  | n+1, env, ρ, .liftE e => do
      let v ← evalExp n env ρ e
      let o ← Res.ofOption v.asOpt?
      .ok (.list o.toList)
  -- `MemE` (`eval.ml:339-350`).
  | n+1, env, ρ, .memE e₁ e₂ => do
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      memValue v₁ v₂
  -- `LenE` (`eval.ml:351-357`), `Value.len?`.
  | n+1, env, ρ, .lenE e => do
      let v ← evalExp n env ρ e
      Res.ofOption (v.len?.map fun k => Value.num (.natN k))
  -- `CatE` (`eval.ml:459-467`), `Value.cat?`.
  | n+1, env, ρ, .catE e₁ e₂ => do
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      Res.ofOption (Value.cat? v₁ v₂)
  -- `IdxE` (`eval.ml:271-278`), `Value.idx?`.
  | n+1, env, ρ, .idxE e₁ e₂ => do
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      let i ← Res.ofOption v₂.asNat?
      Res.ofOption (v₁.idx? i)
  -- `SliceE` (`eval.ml:279-287`), `Value.slice?`.
  | n+1, env, ρ, .sliceE e₁ e₂ e₃ => do
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      let v₃ ← evalExp n env ρ e₃
      let i ← Res.ofOption v₂.asNat?
      let k ← Res.ofOption v₃.asNat?
      Res.ofOption (v₁.slice? i k)
  -- `UpdE` (`eval.ml:288-296`): write `v₂` at `p`.
  | n+1, env, ρ, .updE e₁ p e₂ => do
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      pathSet n env ρ v₁ p v₂
  -- `ExtE` (`eval.ml:297-305`): `CatE` the old contents of `p` with `v₂` and
  -- write the result back (`eval.ml:302-303`).
  | n+1, env, ρ, .extE e₁ p e₂ => do
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      let u ← pathGet n env ρ v₁ p
      let u' ← Res.ofOption (Value.cat? u v₂)
      pathSet n env ρ v₁ p u'
  -- `CallE` (`eval.ml:361-372`).
  | n+1, env, ρ, .callE x args => callDef n env ρ x args
  -- `IterE` (`eval.ml:373-420`); 3676 occurrences.
  | n+1, env, ρ, .iterE e (.mk it ds) => evalIterE n env ρ e it ds
  -- `CvtE` (`eval.ml:484-493`): only the *target* type matters
  -- (`eval.ml:488`), so this is first-order and needs no type environment.
  | n+1, env, ρ, .cvtE e _ t₂ => do
      let v ← evalExp n env ρ e
      let m ← Res.ofOption v.asNum?
      Res.ofOption ((Num.cvt t₂ m).map Value.num)
  -- `SubE` (`eval.ml:494-536`).  On a value every branch of that clause is
  -- the identity: `eval.ml:498` returns `e1'` when the two types are
  -- equivalent, `eval.ml:534-535` returns it unchanged when it is head
  -- normal, and the `TupE`/`StrE`/`CaseE` branches
  -- (`eval.ml:502-533`) only push `SubE` inwards, which by the same argument
  -- is again the identity.  So an untyped value semantics ignores the types.
  | n+1, env, ρ, .subE e _ _ => evalExp n env ρ e
termination_by n => n

/-- `map_results (reduce_exp …)` (`eval.ml:39-41`, used at `eval.ml:359`),
which fails as soon as one element does. -/
def evalExps : Nat → Env → VarEnv → List Exp → Res (List Value)
  | 0, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, es => es.mapM (evalExp n env ρ)
termination_by n => n

/-- `reduce_expfield` (`eval.ml:551-566`), minus the `check` bookkeeping the
`--ast` stream drops. -/
def evalExpFields : Nat → Env → VarEnv → List ExpField → Res (List (AtomS × Value))
  | 0, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, fs =>
      fs.mapM fun f => match f with
        | .mk a e => (fun v => (a, v)) <$> evalExp n env ρ e
termination_by n => n

/-- `reduce_arg` (`eval.ml:629-638`).  Only `ExpA` is evaluated
(`eval.ml:635`); the other three are carried as syntax, with a `DefA` resolved
through the scope so that a `DefP`-bound name reaches the global definition it
stands for.  See `ArgV`. -/
def evalArg : Nat → Env → VarEnv → Arg → Res ArgV
  | 0, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, .expA e => ArgV.val <$> evalExp n env ρ e
  | _+1, _, ρ, .typA t => .ok (.typ (resolveTyp ρ t))
  | _+1, _, ρ, .defA x => .ok (.defName ((ρ.findDef? x).getD x))
  | _+1, _, ρ, .gramA g => .ok (.gram (resolveSym ρ g))
termination_by n => n

/-- `map_results (reduce_arg …)` (`eval.ml:363`). -/
def evalArgs : Nat → Env → VarEnv → List Arg → Res (List ArgV)
  | 0, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, args => args.mapM (evalArg n env ρ)
termination_by n => n

/-- The domain expressions of an `iterexp`, evaluated
(`reduce_iterexp`, `eval.ml:546-549`). -/
def evalDoms : Nat → Env → VarEnv → List Dom → Res (List (IL.Id × Value))
  | 0, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, ds =>
      ds.mapM fun d => (fun v => (domVar d, v)) <$> evalExp n env ρ (domSrc d)
termination_by n => n

/-- `IterE` (`eval.ml:373-420`), the intricate clause.

An `iterexp` is an `Iter` plus a list of domains `(x, e)`
(`spectec/src/il/ast.ml:95`): `x` runs over the elements of `e`'s value and
the body is evaluated once per index.  `eval.ml` reduces the body *first*
(`eval.ml:374`) and then substitutes; we cannot, because the body mentions
the `x`s and would be undefined, so the body is evaluated once per round
*after* the bindings are in scope (`evalRounds`).  That is the one structural
difference, and it is forced by working with values rather than with
partially reduced expressions.

The four iterators:

* `Opt` (`eval.ml:384-393`) — all domains `none` gives `none`
  (`eval.ml:387`), all `some` runs the body once (`eval.ml:388-391`), a mix
  is inconsistent (`eval.ml:392-393`).
* `List` (`eval.ml:394-400`) — the length is read off the first domain
  (`eval.ml:395`) and the iteration restarts as a `ListN`.
* `List1` — as `List`, but an empty list is an error (`eval.ml:396,400`).
* `ListN e x?` (`eval.ml:401-417`) — `e` fixes the length, every domain must
  have exactly that length (`eval.ml:405`), and the optional `x` is bound to
  the round number (`eval.ml:409-413`).

`eval.ml:377-379` leaves `Opt`, `List` and `List1` stuck when there are *no*
domains, because the number of rounds is then unknown ("lists with no
iteration vars are invalid except as patterns"); `ListN` with no domains is
fine and repeats the body `n` times.  `Opt` ≤ `List1` in the constructor
order `ast.ml:16-20` declares, which is what `iter' <= List1` at
`eval.ml:377` tests. -/
def evalIterE : Nat → Env → VarEnv → Exp → Iter → List Dom → Res Value
  | 0, _, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, e, .opt, ds => do
      let xvs ← evalDoms n env ρ ds
      Res.assert (ds.isEmpty = false) do
        let os ← Res.ofOption (xvs.mapM fun p => p.2.asOpt?.map fun o => (p.1, o))
        if os.all fun p => p.2.isNone then .ok (.opt none)
        else if os.all fun p => p.2.isSome then do
          let row := os.filterMap fun p => p.2.map fun w => (p.1, w)
          let v ← evalExp n env (ρ.bindVals row) e
          .ok (.opt (some v))
        else .error .undef
  | n+1, env, ρ, e, .list, ds => do
      let xvs ← evalDoms n env ρ ds
      Res.assert (ds.isEmpty = false) do
        let k ← Res.ofOption (xvs.head?.bind fun p => p.2.asList?.map List.length)
        evalIterList n env ρ e xvs none k
  | n+1, env, ρ, e, .list1, ds => do
      let xvs ← evalDoms n env ρ ds
      Res.assert (ds.isEmpty = false) do
        let k ← Res.ofOption (xvs.head?.bind fun p => p.2.asList?.map List.length)
        Res.assert (1 ≤ k) (evalIterList n env ρ e xvs none k)
  | n+1, env, ρ, e, .listN eₙ ido, ds => do
      let xvs ← evalDoms n env ρ ds
      let kv ← evalExp n env ρ eₙ
      let k ← Res.ofOption kv.asNat?
      evalIterList n env ρ e xvs ido k
termination_by n => n

/-- The `ListN` body of `evalIterE` (`eval.ml:401-417`): every domain must be
a list of exactly `k` elements, and the body runs once per index. -/
def evalIterList : Nat → Env → VarEnv → Exp → List (IL.Id × Value) → Option IL.Id → Nat
    → Res Value
  | 0, _, _, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, e, xvs, ido, k => do
      let ds ← Res.ofOption (xvs.mapM fun p => p.2.asList?.map fun l => (p.1, l))
      Res.assert (ds.all fun p => p.2.length == k) do
        let vs ← evalRounds n env ρ e (iterRows ds ido k)
        .ok (.list vs)
termination_by n => n

/-- Evaluate the body of an iteration once per round, under that round's
bindings (`eval.ml:406-415`, `List.init n`). -/
def evalRounds : Nat → Env → VarEnv → Exp → List (List (IL.Id × Value)) → Res (List Value)
  | 0, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, e, rows => rows.mapM fun r => evalExp n env (ρ.bindVals r) e
termination_by n => n

/-- Read the sub-value a path selects (`reduce_path`, `eval.ml:568-627`).

`reduce_path` is written in continuation-passing style: it walks the path from
the root outwards and hands the continuation the selected sub-expression
together with the *residual* path (`eval.ml:570`).  `pathGet`/`pathSet` is
the same walk split into a read and a write, which is possible because the
only two continuations `eval.ml` ever passes are "replace" (`eval.ml:293-295`)
and "concatenate" (`eval.ml:302-304`). -/
def pathGet : Nat → Env → VarEnv → Value → Path → Res Value
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, _, v, .rootP => .ok v
  | n+1, env, ρ, v, .idxP p e => do
      let u ← pathGet n env ρ v p
      let iv ← evalExp n env ρ e
      let i ← Res.ofOption iv.asNat?
      Res.ofOption (u.idx? i)
  | n+1, env, ρ, v, .sliceP p e₁ e₂ => do
      let u ← pathGet n env ρ v p
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      let i ← Res.ofOption v₁.asNat?
      let k ← Res.ofOption v₂.asNat?
      Res.ofOption (u.slice? i k)
  | n+1, env, ρ, v, .dotP p a => do
      let u ← pathGet n env ρ v p
      Res.ofOption (u.field? a)
termination_by n => n

/-- Write a sub-value through a path: `IdxP` is `Value.setIdx`
(`eval.ml:571-588`), `SliceP` is `Value.setSlice` (`eval.ml:590-606`) and
`DotP` is `Value.setField` (`eval.ml:608-625`). -/
def pathSet : Nat → Env → VarEnv → Value → Path → Value → Res Value
  | 0, _, _, _, _, _ => .error .outOfFuel
  | _+1, _, _, _, .rootP, w => .ok w
  | n+1, env, ρ, v, .idxP p e, w => do
      let u ← pathGet n env ρ v p
      let iv ← evalExp n env ρ e
      let i ← Res.ofOption iv.asNat?
      let u' ← Res.ofOption (u.setIdx i w)
      pathSet n env ρ v p u'
  | n+1, env, ρ, v, .sliceP p e₁ e₂, w => do
      let u ← pathGet n env ρ v p
      let v₁ ← evalExp n env ρ e₁
      let v₂ ← evalExp n env ρ e₂
      let i ← Res.ofOption v₁.asNat?
      let k ← Res.ofOption v₂.asNat?
      let u' ← Res.ofOption (u.setSlice i k w)
      pathSet n env ρ v p u'
  | n+1, env, ρ, v, .dotP p a, w => do
      let u ← pathGet n env ρ v p
      let u' ← Res.ofOption (u.setField a w)
      pathSet n env ρ v p u'
termination_by n => n

/-- How many list elements a pattern consumes, when that is determined.

`eval.ml:923-932` splits a `CatE` pattern only when one side is a literal
`ListE`, whose length is syntactically evident.  This is the same idea with
two more sources of a length: a `ListN` iteration states its own length, and
a `CatE` is the sum of its parts.  The default is to evaluate the pattern and
take `Value.len?`, which succeeds for an already-bound variable. -/
def patLen : Nat → Env → VarEnv → Exp → Res Nat
  | 0, _, _, _ => .error .outOfFuel
  | _+1, _, _, .listE es => .ok es.length
  | n+1, env, ρ, .catE e₁ e₂ => do
      let a ← patLen n env ρ e₁
      let b ← patLen n env ρ e₂
      .ok (a + b)
  | n+1, env, ρ, .iterE _ (.mk (.listN eₙ _) _) => do
      let v ← evalExp n env ρ eₙ
      Res.ofOption v.asNat?
  | n+1, env, ρ, e => do
      let v ← evalExp n env ρ e
      Res.ofOption v.len?
termination_by n => n

/-- Match an expression *pattern* against a value, extending the scope
(`match_exp'`, `eval.ml:877-1070`).

`eval.ml`'s matcher compares two expressions and is full of cases that only
make sense between partially reduced terms; ours is value-directed, and
therefore simpler.  The forms that act as **patterns**, i.e. that are
decomposed rather than evaluated, are exactly:

| form | value | `eval.ml` |
| --- | --- | --- |
| `VarE x` | anything (binds, or checks if `x` is already bound) | 887-895 |
| `BoolE`, `NumE`, `TextE` | the same literal | 897-899 |
| `TupE es` | `tuple vs`, pointwise | 919 |
| `ListE es` | `list vs`, pointwise | 918 |
| `CatE e₁ e₂` | `list vs`, split (see below) | 923-932 |
| `CaseE op e` | `case op v` | 955-957 |
| `OptE eo` | `opt o` | 435-441, 983-995 |
| `StrE fs` | `struct gs`, field by field | 948-949 |
| `IterE e it` | `list`/`opt`, round by round | 983-1028 |
| `UncaseE e op` | `v`, matched against `case op v` | 968-971 |
| `ProjE e 0` | `v`, matched against `tuple [v]` | 972-973 |
| `SubE e _ _` | `v` (types are invisible to values) | 1035-1068 |
| `UnE ±` | a numeral of the matching sign | 900-904 |
| `CvtE e t₁ _` | a numeral, converted *back* along `t₁` | 905-909 |

Every other form — `BinE`, `CmpE`, `TheE`, `DotE`, `CompE`, `LiftE`, `MemE`,
`LenE`, `IdxE`, `SliceE`, `UpdE`, `ExtE`, `CallE` — is **only evaluated**, and
matched by comparing the resulting value (`matchDefault`).  That covers
`eval.ml:885`'s equality shortcut and its `is_head_normal_exp` fallthrough
(`eval.ml:1069`).

### How a `CatE` pattern is split

`eval.ml:923-932` splits a concatenation only when one operand is a literal
`ListE`, whose length is syntactically evident.  `patLen` generalises that to
three sources of a length, and if either operand has one the list is split
there — the left operand's length is preferred, exactly as `eval.ml:923`
tries its `ListE`-on-the-left clause first.

When *neither* operand has a length the clause does not give up: it searches,
trying the `vs.length + 1` splits in increasing order and taking the first
that matches (`Res.scan`).  This is a deliberate strengthening of `eval.ml`,
which SpecTec itself never executes through — the frontend reduces a rule via
`il2al`, whose `translate.ml` gives `CatE` its own treatment — and it is what
makes the concatenation patterns of the reduction relation match at all: a
rule such as `Step_pure/br-handler` concatenates two `*` iterations over
domains the pattern is itself about to bind, so neither has a length.  The
search is first-match, hence still a *function* of its inputs, so
determinism (`MatchExp.unique`) is untouched; and each alternative is
consumed with `Res.elimUndef`, so an alternative that merely ran out of fuel
stops the search rather than being skipped, which is what keeps `matchExp`
monotone in its fuel.

Two `eval.ml` clauses are deliberately not transcribed, both because they need
the type annotation that a `--ast` stream drops
(`Silmaril/SpecTec/IL/Ast.lean`): the eta-expansion of a non-tuple against a
`TupE` pattern (`eval.ml:920-922`, `eta_tup_exp`), and the beta-expansion of
an irrefutable one-case variant pattern (`eval.ml:959-963`).  A value here
must already be a `tuple` or a `case` for those patterns to apply. -/
def matchExp : Nat → Env → VarEnv → Exp → Value → Res VarEnv
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, ρ, .varE x, v =>
      match ρ.findVal? x with
      | some w => if w = v then .ok ρ else .error .undef
      | none => .ok (ρ.bindVal x v)
  | _+1, _, ρ, .boolE b, v => Res.assert (v = .bool b) (.ok ρ)
  | _+1, _, ρ, .numE m, v => Res.assert (v = .num m) (.ok ρ)
  | _+1, _, ρ, .textE t, v => Res.assert (v = .text t) (.ok ρ)
  | n+1, env, ρ, .unE op t e, v =>
      match op, v with
      | .plusOp, .num m =>
          Res.assert (Num.isNeg m = false) (matchExp n env ρ e (.num m))
      | .minusOp, .num m =>
          Res.assert (Num.isNeg m = true) do
            let m' ← Res.ofOption (Num.absN m)
            matchExp n env ρ e (.num m')
      | _, _ => matchDefault n env ρ (.unE op t e) v
  | n+1, env, ρ, .tupE es, v => do
      let vs ← Res.ofOption v.asTuple?
      matchExps n env ρ es vs
  | n+1, env, ρ, .projE e i, v =>
      if i = 0 then matchExp n env ρ e (.tuple [v])
      else matchDefault n env ρ (.projE e i) v
  | n+1, env, ρ, .caseE op e, v => do
      let (op', w) ← Res.ofOption v.asCase?
      Res.assert (op' = op) (matchExp n env ρ e w)
  | n+1, env, ρ, .uncaseE e op, v => matchExp n env ρ e (.case op v)
  | _+1, _, ρ, .optE none, v => Res.assert (v = .opt none) (.ok ρ)
  | n+1, env, ρ, .optE (some e), v => do
      let o ← Res.ofOption v.asOpt?
      let w ← Res.ofOption o
      matchExp n env ρ e w
  | n+1, env, ρ, .strE fs, v => do
      let gs ← Res.ofOption v.asStruct?
      matchExpFields n env ρ fs gs
  | n+1, env, ρ, .listE es, v => do
      let vs ← Res.ofOption v.asList?
      matchExps n env ρ es vs
  | n+1, env, ρ, .catE e₁ e₂, v => do
      let vs ← Res.ofOption v.asList?
      Res.elimUndef (patLen n env ρ e₁)
        (fun k =>
          Res.assert (k ≤ vs.length) do
            let ρ' ← matchExp n env ρ e₁ (.list (vs.take k))
            matchExp n env ρ' e₂ (.list (vs.drop k)))
        (fun _ =>
          Res.elimUndef (patLen n env ρ e₂)
            (fun k =>
              Res.assert (k ≤ vs.length) do
                let ρ' ← matchExp n env ρ e₁ (.list (vs.take (vs.length - k)))
                matchExp n env ρ' e₂ (.list (vs.drop (vs.length - k))))
            (fun _ =>
              Res.scan
                (fun k => do
                  let ρ' ← matchExp n env ρ e₁ (.list (vs.take k))
                  matchExp n env ρ' e₂ (.list (vs.drop k)))
                0 vs.length))
  | n+1, env, ρ, .iterE e (.mk it ds), v => matchIterE n env ρ e it ds v
  | n+1, env, ρ, .cvtE e t₁ t₂, v =>
      match v with
      | .num m => do
          let m' ← Res.ofOption (Num.cvt t₁ m)
          matchExp n env ρ e (.num m')
      | _ => matchDefault n env ρ (.cvtE e t₁ t₂) v
  | n+1, env, ρ, .subE e _ _, v => matchExp n env ρ e v
  | n+1, env, ρ, e@(.binE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.cmpE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.theE _), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.dotE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.compE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.liftE _), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.memE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.lenE _), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.idxE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.sliceE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.updE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.extE ..), v => matchDefault n env ρ e v
  | n+1, env, ρ, e@(.callE ..), v => matchDefault n env ρ e v
termination_by n => n

/-- The non-pattern case of `matchExp`: evaluate and compare
(`eval.ml:885`, and the `is_head_normal_exp` fallthrough at
`eval.ml:1069`). -/
def matchDefault : Nat → Env → VarEnv → Exp → Value → Res VarEnv
  | 0, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, e, v => do
      let w ← evalExp n env ρ e
      Res.assert (w = v) (.ok ρ)
termination_by n => n

/-- `match_list (match_exp' …)` (`eval.ml:93-99`): pointwise, threading the
scope, with mismatched lengths a definite failure (`eval.ml:99`). -/
def matchExps : Nat → Env → VarEnv → List Exp → List Value → Res VarEnv
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, ρ, [], [] => .ok ρ
  | n+1, env, ρ, e :: es, v :: vs => do
      let ρ' ← matchExp n env ρ e v
      matchExps n env ρ' es vs
  | _+1, _, _, _, _ => .error .undef
termination_by n => n

/-- `match_expfield` (`eval.ml:1072-1074`), whose `assert` that the two atoms
agree becomes a failure here. -/
def matchExpFields : Nat → Env → VarEnv → List ExpField → List (AtomS × Value)
    → Res VarEnv
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, ρ, [], [] => .ok ρ
  | n+1, env, ρ, .mk a e :: fs, g :: gs =>
      Res.assert (a = g.1) do
        let ρ' ← matchExp n env ρ e g.2
        matchExpFields n env ρ' fs gs
  | _+1, _, _, _, _ => .error .undef
termination_by n => n

/-- Match an `IterE` pattern against a value (`eval.ml:983-1028`).

The direction is reversed with respect to `evalIterE`: the *value* supplies
the rounds, each round's element is matched against the body, and the values
the body binds to the domain variables are collected into a list (or an
option) and matched against the domain *expressions*, which are themselves
patterns.  `eval.ml:1006` drops the domain variables from the substitution
before matching the body and re-adds the outer bindings afterwards
(`eval.ml:1028`); `matchRounds` does the same by starting every round from the
incoming scope and reading only the domain variables back out.

A consequence worth stating: a variable the *body* binds and that is not a
domain variable does not escape, exactly as `eval.ml:1021-1027` projects only
`List.map fst xes`. -/
def matchIterE : Nat → Env → VarEnv → Exp → Iter → List Dom → Value → Res VarEnv
  | 0, _, _, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, e, .opt, ds, v => do
      let o ← Res.ofOption v.asOpt?
      match o with
      | none => matchExps n env ρ (ds.map domSrc) (ds.map fun _ => Value.opt none)
      | some w => do
          let ρ' ← matchExp n env ρ e w
          let ws ← Res.ofOption (ρ'.findVals? (ds.map domVar))
          matchExps n env ρ (ds.map domSrc) (ws.map fun u => Value.opt (some u))
  | n+1, env, ρ, e, .list, ds, v => do
      let vs ← Res.ofOption v.asList?
      matchIterList n env ρ e ds none vs
  | n+1, env, ρ, e, .list1, ds, v => do
      let vs ← Res.ofOption v.asList?
      Res.assert (vs.isEmpty = false) (matchIterList n env ρ e ds none vs)
  | n+1, env, ρ, e, .listN eₙ ido, ds, v => do
      let vs ← Res.ofOption v.asList?
      let ρ₀ ← matchExp n env ρ eₙ (.num (.natN vs.length))
      matchIterList n env ρ₀ e ds ido vs
termination_by n => n

/-- The list case of `matchIterE` (`eval.ml:1003-1028`): match every element,
then match each column of collected bindings against its domain. -/
def matchIterList : Nat → Env → VarEnv → Exp → List Dom → Option IL.Id → List Value
    → Res VarEnv
  | 0, _, _, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, e, ds, ido, vs => do
      let rows ← matchRounds n env ρ e (ds.map domVar) ido 0 vs
      matchExps n env ρ (ds.map domSrc) (iterCols rows ds.length)
termination_by n => n

/-- One round per element of the matched list (`eval.ml:1008-1017`).  `i` is
the round number, bound to the `ListN` counter variable when there is one
(`eval.ml:1011-1015`). -/
def matchRounds : Nat → Env → VarEnv → Exp → List IL.Id → Option IL.Id → Nat
    → List Value → Res (List (List Value))
  | 0, _, _, _, _, _, _, _ => .error .outOfFuel
  | _+1, _, _, _, _, _, _, [] => .ok []
  | n+1, env, ρ, e, xs, ido, i, v :: vs => do
      let ρ₁ := match ido with
        | some y => ρ.bindVal y (.num (.natN i))
        | none => ρ
      let ρ' ← matchExp n env ρ₁ e v
      let row ← Res.ofOption (ρ'.findVals? xs)
      let rest ← matchRounds n env ρ e xs ido (i + 1) vs
      .ok (row :: rest)
termination_by n => n

/-- Match an argument *pattern* against an evaluated argument (`match_arg`,
`eval.ml:1123-1134`).

`DefA` deserves a note.  `eval.ml:1131` is
`Ok (Some (Subst.add_defid s id1 id2))`, where `id1` comes from the *actual*
argument and `id2` from the *pattern*; every other clause binds the pattern's
identifier to the actual one, and the substitution is afterwards applied to
the clause body, which mentions the pattern's name.  Taking `eval.ml:1131`
literally would therefore bind the wrong direction and leave the body's call
unresolved.  We bind pattern ↦ actual, like the other three clauses.  This is
observable in the pinned corpus: `$ivunop_` (`specs/spectec/wasm-3.0.ast`)
declares a `DefP` parameter `f_`, its single clause has the argument pattern
`(def "f_")` and its body calls `$f_`, while callers such as `$vunop_` pass
`(def "fabs_")`. -/
def matchArg : Nat → Env → VarEnv → Arg → ArgV → Res VarEnv
  | 0, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, .expA e, .val v =>
      if argSubOk env ρ e v then matchExp n env ρ e v else .error .undef
  | _+1, env, ρ, .typA t', .typ t => matchTypV env ρ t' t
  | _+1, _, ρ, .defA y, .defName x => .ok (ρ.bindDef y x)
  | _+1, env, ρ, .gramA g', .gram g => matchSymV env ρ g' g
  | _+1, _, _, _, _ => .error .undef
termination_by n => n

/-- `match_list (match_arg …)` (`eval.ml:654`). -/
def matchArgs : Nat → Env → VarEnv → List Arg → List ArgV → Res VarEnv
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, ρ, [], [] => .ok ρ
  | n+1, env, ρ, a :: as, w :: ws => do
      let ρ' ← matchArg n env ρ a w
      matchArgs n env ρ' as ws
  | _+1, _, _, _, _ => .error .undef
termination_by n => n

/-- Call a definition (`CallE`, `eval.ml:361-372`, and `reduce_exp_call`,
`eval.ml:640-671`).

The name is first resolved through the scope, so that a `DefP` parameter
reaches the global definition it was instantiated with; then the arguments are
evaluated (`eval.ml:363`) and the clauses are tried in order.  An
*uninterpreted* function — one with no clauses — is left unreduced by
`eval.ml:364-366`; here it simply has no value. -/
def callDef : Nat → Env → VarEnv → IL.Id → List Arg → Res Value
  | 0, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, x, args => do
      let argVs ← evalArgs n env ρ args
      let x' := (ρ.findDef? x).getD x
      let d ← Res.ofOption (env.findDef? x')
      Res.elimUndef (tryClauses n env d.2.2 argVs) .ok
        (fun _ => Res.ofOption (env.builtins.call x' argVs))
termination_by n => n

/-- First match wins (`reduce_exp_call`, `eval.ml:640-671`).

A clause applies when its argument patterns match (`eval.ml:654`) *and* its
premises hold (`eval.ml:663`); a definite failure of either moves on to the
next clause (`eval.ml:655,665`) and running out of clauses is a definite
failure (`eval.ml:647`).  Once a clause applies, its body is evaluated and the
search stops: the body failing does **not** fall through, which is
`eval.ml:664` returning `Ok (Some …)` unconditionally.

The clause's own quantifiers (`DefD (quants, …)`,
`spectec/src/il/ast.ml:149`) are ignored: they declare the types of the
pattern variables, which `spectec/src/il/valid.ml` checks and evaluation does
not need.  The body is evaluated in a scope containing *only* the clause's
bindings, mirroring `Subst.subst_exp s e` at `eval.ml:664` with `s` built from
`Subst.empty`. -/
def tryClauses : Nat → Env → List Clause → List ArgV → Res Value
  | 0, _, _, _ => .error .outOfFuel
  | _+1, _, [], _ => .error .undef
  | n+1, env, .defD _ pats e prems :: cs, argVs =>
      Res.elimUndef
        (do let ρ₀ ← matchArgs n env VarEnv.empty pats argVs
            premsHold n env ρ₀ prems)
        (fun ρ₁ => evalExp n env ρ₁ e)
        (fun _ => tryClauses n env cs argVs)
termination_by n => n

/-- Check a premise, returning the extended scope (`reduce_prem`,
`eval.ml:685-795`).

* `IfPr` (`eval.ml:688-693`) is a side condition: `true` holds and binds
  nothing, `false` fails.
* `ElsePr` (`eval.ml:694`) always holds; it is what marks a fallback clause,
  and it occurs 126 times in the pinned corpus.
* `LetPr` (`eval.ml:695-698`) evaluates the right-hand side and matches it
  against the left-hand side, which is therefore a *pattern* and the one
  premise that binds.  Note the argument order: `LetPr (e₁, e₂)` matches
  `e₂`'s value against the pattern `e₁` (`eval.ml:698`,
  `match_exp … e2' e1'`).  Zero occurrences in the pinned corpus — the
  quantifiers `print.ml:165` drops would have been needed to know which of its
  variables flow outwards, and no stream contains one.
* `RulePr` (`eval.ml:687`) is `Ok None` in `eval.ml` — its evaluator never
  decides a relational premise.  Here it is decided, by evaluating the
  asserted instance and asking `derives`.  A `derives` that comes back `false`
  is reported as `outOfFuel`, not as a failure: `derives` is a step-indexed
  *least* fixpoint, so `false` at one fuel level says nothing.  In particular
  a `RulePr` can never cause `tryClauses` to skip a clause, which is exactly
  the effect `eval.ml:687` has.  It binds nothing; see the module-level note
  on scope.
* `IterPr` (`eval.ml:699-795`) is `premIter`; 150 occurrences. -/
def premHolds : Nat → Env → VarEnv → Prem → Res VarEnv
  | 0, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, .ifPr e => do
      let v ← evalExp n env ρ e
      Res.assert (v = .bool true) (.ok ρ)
  | _+1, _, ρ, .elsePr => .ok ρ
  | n+1, env, ρ, .letPr e₁ e₂ => do
      let v ← evalExp n env ρ e₂
      matchExp n env ρ e₁ v
  | n+1, env, ρ, .rulePr x args op e => do
      let argVs ← evalArgs n env ρ args
      let v ← evalExp n env ρ e
      if derives n env x op argVs v then .ok ρ else .error .outOfFuel
  | n+1, env, ρ, .iterPr pr (.mk it ds) => premIter n env ρ pr it ds
termination_by n => n

/-- `reduce_prems` (`eval.ml:672-684`): left to right, each premise seeing the
scope the previous ones extended. -/
def premsHold : Nat → Env → VarEnv → List Prem → Res VarEnv
  | 0, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, prems => prems.foldlM (fun ρ' pr => premHolds n env ρ' pr) ρ
termination_by n => n

/-- An iterated premise (`eval.ml:699-795`).

The iterator is read exactly as in `evalIterE`: `Opt` (`eval.ml:719-741`),
`List`/`List1` (`eval.ml:742-751`) and `ListN` (`eval.ml:752-794`), with the
domain lists required to have the stated length (`eval.ml:757`).

`eval.ml` additionally partitions the domains into those that flow *outwards*
and those that flow *inwards* (`is_let_bound`, `eval.ml:703-710`) and
reverse-matches the outward ones after the body has held
(`eval.ml:733-738,779-790`).  A domain is outward exactly when the iterated
premise is — or iterates — a `LetPr` whose quantifiers bind it
(`eval.ml:705`).  No pinned stream contains a `LetPr`, so `is_let_bound` is
identically false on the corpus and `xes_out` is always empty: this
transcribes precisely the branch the corpus takes.  Binding outwards from an
iterated premise is **not** implemented; `premIter` returns the scope it was
given.  See the module-level note on scope. -/
def premIter : Nat → Env → VarEnv → Prem → Iter → List Dom → Res VarEnv
  | 0, _, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, pr, .opt, ds => do
      let xvs ← evalDoms n env ρ ds
      Res.assert (ds.isEmpty = false) do
        let os ← Res.ofOption (xvs.mapM fun p => p.2.asOpt?.map fun o => (p.1, o))
        if os.all fun p => p.2.isNone then .ok ρ
        else if os.all fun p => p.2.isSome then do
          let row := os.filterMap fun p => p.2.map fun w => (p.1, w)
          let _ ← premHolds n env (ρ.bindVals row) pr
          .ok ρ
        else .error .undef
  | n+1, env, ρ, pr, .list, ds => do
      let xvs ← evalDoms n env ρ ds
      Res.assert (ds.isEmpty = false) do
        let k ← Res.ofOption (xvs.head?.bind fun p => p.2.asList?.map List.length)
        premRounds n env ρ pr xvs none k
  | n+1, env, ρ, pr, .list1, ds => do
      let xvs ← evalDoms n env ρ ds
      Res.assert (ds.isEmpty = false) do
        let k ← Res.ofOption (xvs.head?.bind fun p => p.2.asList?.map List.length)
        Res.assert (1 ≤ k) (premRounds n env ρ pr xvs none k)
  | n+1, env, ρ, pr, .listN eₙ ido, ds => do
      let xvs ← evalDoms n env ρ ds
      let kv ← evalExp n env ρ eₙ
      let k ← Res.ofOption kv.asNat?
      premRounds n env ρ pr xvs ido k
termination_by n => n

/-- The `ListN` body of `premIter` (`eval.ml:752-775`): the premise must hold
in every round. -/
def premRounds : Nat → Env → VarEnv → Prem → List (IL.Id × Value) → Option IL.Id → Nat
    → Res VarEnv
  | 0, _, _, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, pr, xvs, ido, k => do
      let ds ← Res.ofOption (xvs.mapM fun p => p.2.asList?.map fun l => (p.1, l))
      Res.assert (ds.all fun p => p.2.length == k) do
        let _ ← (iterRows ds ido k).mapM fun r => premHolds n env (ρ.bindVals r) pr
        .ok ρ
termination_by n => n

/-- The step-indexed least fixpoint of a relation's rules.

A `RelD` (`spectec/src/il/ast.ml:134`) is genuinely inductive, so unlike the
rest of this block `derives` is not a transcription of anything in `eval.ml`,
which refuses to decide a relational premise at all (`eval.ml:687`).
`derives (n + 1) env x op args v` holds when some rule of `x` has a conclusion
matching `v` and premises that all hold at `n`; `derives 0` is empty, and the
relation "`v` is derivable" is `∃ n, derives n … = true` (`Derives` below).
Fuel is only the ladder up to the least fixpoint, so `false` at a given level
carries no information — which is why `premHolds` reports it as
`outOfFuel`. -/
def derives : Nat → Env → IL.Id → MixopS → List ArgV → Value → Bool
  | 0, _, _, _, _, _ => false
  | n+1, env, x, op, args, v =>
      match env.findRel? x with
      | none => false
      | some (ps, op', _, rules) => op' == op && anyRule n env op ps args v rules
termination_by n => n

/-- Does any rule of a relation fire?  A `RuleD` (`ast.ml:145`) carries no
argument list, so the relation's parameters are bound positionally from the
call's arguments (`bindParams`) and only the conclusion `e` is matched. -/
def anyRule : Nat → Env → MixopS → List Param → List ArgV → Value → List Rule → Bool
  | 0, _, _, _, _, _, _ => false
  | _+1, _, _, _, _, _, [] => false
  | n+1, env, op, ps, args, v, .ruleD _ _ op' e prems :: rs =>
      (op' == op &&
        (do
          let ρ₀ ← Res.ofOption (bindParams VarEnv.empty ps args)
          let ρ₁ ← matchExp n env ρ₀ e v
          premsHold n env ρ₁ prems).isOk) ||
      anyRule n env op ps args v rs
termination_by n => n

end


/-! ## Metatheory

### Monotonicity in fuel

The three properties `docs/projects/spectec/README.md` asks for all rest on this one:
more fuel never changes an answer the evaluator has already committed to.  The
statement has to be about `Res.Le` rather than about equality, because fuel
exhaustion is exactly the outcome that more fuel is allowed to change. -/

open Res

/-- Monotonicity in fuel, for every member of the mutual block at once:
`MonoAt m n` says that going from fuel `m` to fuel `n` refines every answer in
the sense of `Res.Le`, i.e. changes nothing except possibly replacing
`outOfFuel` by a definite result.

A structure rather than a 29-fold conjunction, so that the induction can name
the hypothesis it needs. -/
structure MonoAt (m n : Nat) : Prop where
  /-- Monotonicity of `evalExp`. -/
  exp : ∀ env ρ e, evalExp m env ρ e ⊑ evalExp n env ρ e
  /-- Monotonicity of `evalExps`. -/
  exps : ∀ env ρ es, evalExps m env ρ es ⊑ evalExps n env ρ es
  /-- Monotonicity of `evalExpFields`. -/
  expFields : ∀ env ρ fs, evalExpFields m env ρ fs ⊑ evalExpFields n env ρ fs
  /-- Monotonicity of `evalArg`. -/
  arg : ∀ env ρ a, evalArg m env ρ a ⊑ evalArg n env ρ a
  /-- Monotonicity of `evalArgs`. -/
  args : ∀ env ρ as, evalArgs m env ρ as ⊑ evalArgs n env ρ as
  /-- Monotonicity of `evalDoms`. -/
  doms : ∀ env ρ ds, evalDoms m env ρ ds ⊑ evalDoms n env ρ ds
  /-- Monotonicity of `evalIterE`. -/
  iterE : ∀ env ρ e it ds, evalIterE m env ρ e it ds ⊑ evalIterE n env ρ e it ds
  /-- Monotonicity of `evalIterList`. -/
  iterList : ∀ env ρ e xvs ido k,
    evalIterList m env ρ e xvs ido k ⊑ evalIterList n env ρ e xvs ido k
  /-- Monotonicity of `evalRounds`. -/
  rounds : ∀ env ρ e rs, evalRounds m env ρ e rs ⊑ evalRounds n env ρ e rs
  /-- Monotonicity of `pathGet`. -/
  pathGet : ∀ env ρ v p, pathGet m env ρ v p ⊑ pathGet n env ρ v p
  /-- Monotonicity of `pathSet`. -/
  pathSet : ∀ env ρ v p w, pathSet m env ρ v p w ⊑ pathSet n env ρ v p w
  /-- Monotonicity of `patLen`. -/
  patLen : ∀ env ρ e, patLen m env ρ e ⊑ patLen n env ρ e
  /-- Monotonicity of `matchExp`. -/
  matchExp : ∀ env ρ e v, matchExp m env ρ e v ⊑ matchExp n env ρ e v
  /-- Monotonicity of `matchDefault`. -/
  matchDefault : ∀ env ρ e v, matchDefault m env ρ e v ⊑ matchDefault n env ρ e v
  /-- Monotonicity of `matchExps`. -/
  matchExps : ∀ env ρ es vs, matchExps m env ρ es vs ⊑ matchExps n env ρ es vs
  /-- Monotonicity of `matchExpFields`. -/
  matchExpFields : ∀ env ρ fs gs,
    matchExpFields m env ρ fs gs ⊑ matchExpFields n env ρ fs gs
  /-- Monotonicity of `matchIterE`. -/
  matchIterE : ∀ env ρ e it ds v,
    matchIterE m env ρ e it ds v ⊑ matchIterE n env ρ e it ds v
  /-- Monotonicity of `matchIterList`. -/
  matchIterList : ∀ env ρ e ds ido vs,
    matchIterList m env ρ e ds ido vs ⊑ matchIterList n env ρ e ds ido vs
  /-- Monotonicity of `matchRounds`. -/
  matchRounds : ∀ env ρ e xs ido i vs,
    matchRounds m env ρ e xs ido i vs ⊑ matchRounds n env ρ e xs ido i vs
  /-- Monotonicity of `matchArg`. -/
  matchArg : ∀ env ρ a w, matchArg m env ρ a w ⊑ matchArg n env ρ a w
  /-- Monotonicity of `matchArgs`. -/
  matchArgs : ∀ env ρ as ws, matchArgs m env ρ as ws ⊑ matchArgs n env ρ as ws
  /-- Monotonicity of `callDef`. -/
  callDef : ∀ env ρ x as, callDef m env ρ x as ⊑ callDef n env ρ x as
  /-- Monotonicity of `tryClauses`. -/
  tryClauses : ∀ env cs ws, tryClauses m env cs ws ⊑ tryClauses n env cs ws
  /-- Monotonicity of `premHolds`. -/
  premHolds : ∀ env ρ pr, premHolds m env ρ pr ⊑ premHolds n env ρ pr
  /-- Monotonicity of `premsHold`. -/
  premsHold : ∀ env ρ prs, premsHold m env ρ prs ⊑ premsHold n env ρ prs
  /-- Monotonicity of `premIter`. -/
  premIter : ∀ env ρ pr it ds, premIter m env ρ pr it ds ⊑ premIter n env ρ pr it ds
  /-- Monotonicity of `premRounds`. -/
  premRounds : ∀ env ρ pr xvs ido k,
    premRounds m env ρ pr xvs ido k ⊑ premRounds n env ρ pr xvs ido k
  /-- Monotonicity of `derives`: a derivation found at `m` survives at `n`. -/
  derives : ∀ env x op as v, derives m env x op as v = true → derives n env x op as v = true
  /-- Monotonicity of `anyRule`: a derivation found at `m` survives at `n`. -/
  anyRule : ∀ env op ps as v rs,
    anyRule m env op ps as v rs = true → anyRule n env op ps as v rs = true

/-- Base case: with no fuel every member answers `outOfFuel` (or, for the two
`Bool`-valued members, `false`), which is below everything. -/
theorem monoAt_zero (n : Nat) : MonoAt 0 n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; simp only [evalExp]; exact Res.oof_le _
  · intros; simp only [evalExps]; exact Res.oof_le _
  · intros; simp only [evalExpFields]; exact Res.oof_le _
  · intros; simp only [evalArg]; exact Res.oof_le _
  · intros; simp only [evalArgs]; exact Res.oof_le _
  · intros; simp only [evalDoms]; exact Res.oof_le _
  · intros; simp only [evalIterE]; exact Res.oof_le _
  · intros; simp only [evalIterList]; exact Res.oof_le _
  · intros; simp only [evalRounds]; exact Res.oof_le _
  · intros; simp only [pathGet]; exact Res.oof_le _
  · intros; simp only [pathSet]; exact Res.oof_le _
  · intros; simp only [patLen]; exact Res.oof_le _
  · intros; simp only [matchExp]; exact Res.oof_le _
  · intros; simp only [matchDefault]; exact Res.oof_le _
  · intros; simp only [matchExps]; exact Res.oof_le _
  · intros; simp only [matchExpFields]; exact Res.oof_le _
  · intros; simp only [matchIterE]; exact Res.oof_le _
  · intros; simp only [matchIterList]; exact Res.oof_le _
  · intros; simp only [matchRounds]; exact Res.oof_le _
  · intros; simp only [matchArg]; exact Res.oof_le _
  · intros; simp only [matchArgs]; exact Res.oof_le _
  · intros; simp only [callDef]; exact Res.oof_le _
  · intros; simp only [tryClauses]; exact Res.oof_le _
  · intros; simp only [premHolds]; exact Res.oof_le _
  · intros; simp only [premsHold]; exact Res.oof_le _
  · intros; simp only [premIter]; exact Res.oof_le _
  · intros; simp only [premRounds]; exact Res.oof_le _
  · intros _ _ _ _ _ h; simp [derives] at h
  · intros _ _ _ _ _ _ h; simp [anyRule] at h

/-- The inductive step, and the heart of the monotonicity proof: one unit of
fuel at a time, by structural recursion on the fuel.  Every member of the
mutual block is unfolded once and recombined with `Res.bind_le`,
`Res.map_le`, `Res.mapM_le`, `Res.foldlM_le`, `Res.assert_le` and
`Res.elimUndef_le`; the only clauses that need more than that are the
short-circuiting `BinE`, where the branch taken is settled by the *left*
operand alone, and `RulePr`, where a `derives` that was `false` is reported
as `outOfFuel` and so constrains nothing. -/
theorem monoAt_succ : ∀ m, MonoAt m (m + 1)
  | 0 => monoAt_zero 1
  | m + 1 => by
      have ih := monoAt_succ m
      have hexp := ih.exp
      have hexps := ih.exps
      have hefs := ih.expFields
      have harg := ih.arg
      have hargs := ih.args
      have hdoms := ih.doms
      have hit := ih.iterE
      have hitl := ih.iterList
      have hrnd := ih.rounds
      have hpg := ih.pathGet
      have hps := ih.pathSet
      have hpl := ih.patLen
      have hm := ih.matchExp
      have hmd := ih.matchDefault
      have hms := ih.matchExps
      have hmf := ih.matchExpFields
      have hmi := ih.matchIterE
      have hmil := ih.matchIterList
      have hmr := ih.matchRounds
      have hma := ih.matchArg
      have hmas := ih.matchArgs
      have hcd := ih.callDef
      have htc := ih.tryClauses
      have hph := ih.premHolds
      have hphs := ih.premsHold
      have hpi := ih.premIter
      have hpr := ih.premRounds
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- `evalExp`
      · intro env ρ e
        cases e with
        | varE x => simp only [evalExp]; exact Res.Le.refl _
        | boolE b => simp only [evalExp]; exact Res.Le.refl _
        | numE n => simp only [evalExp]; exact Res.Le.refl _
        | textE t => simp only [evalExp]; exact Res.Le.refl _
        | unE op t e =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | binE op t e₁ e₂ =>
            simp only [evalExp]
            refine Res.bind_le (hexp _ _ _) fun v₁ => ?_
            cases boolShort op v₁ with
            | none => exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
            | some v => exact Res.Le.refl _
        | cmpE op t e₁ e₂ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | tupE es => simp only [evalExp]; exact Res.map_le _ (hexps _ _ _)
        | projE e i =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | caseE op e => simp only [evalExp]; exact Res.map_le _ (hexp _ _ _)
        | uncaseE e op =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | optE eo =>
            cases eo <;> simp only [evalExp] <;>
              first
                | exact Res.Le.refl _
                | exact Res.map_le _ (hexp _ _ _)
        | theE e =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | strE fs => simp only [evalExp]; exact Res.map_le _ (hefs _ _ _)
        | dotE e a =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | compE e₁ e₂ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | listE es => simp only [evalExp]; exact Res.map_le _ (hexps _ _ _)
        | liftE e =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | memE e₁ e₂ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | lenE e =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | catE e₁ e₂ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | idxE e₁ e₂ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | sliceE e₁ e₂ e₃ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ =>
                Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | updE e₁ p e₂ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ => hps _ _ _ _ _
        | extE e₁ p e₂ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ =>
                Res.bind_le (hpg _ _ _ _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ _
        | callE x as => simp only [evalExp]; exact hcd _ _ _ _
        | iterE e₀ it =>
            cases it with
            | mk i ds => simp only [evalExp]; exact hit _ _ _ _ _
        | cvtE e t₁ t₂ =>
            simp only [evalExp]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | subE e t₁ t₂ => simp only [evalExp]; exact hexp _ _ _
      -- `evalExps`
      · intro env ρ es
        simp only [evalExps]
        exact Res.mapM_le (fun _ => hexp _ _ _) es
      -- `evalExpFields`
      · intro env ρ fs
        simp only [evalExpFields]
        refine Res.mapM_le (fun f => ?_) fs
        cases f with
        | mk a e => exact Res.map_le _ (hexp _ _ _)
      -- `evalArg`
      · intro env ρ a
        cases a <;> simp only [evalArg] <;>
          first
            | exact Res.map_le _ (hexp _ _ _)
            | exact Res.Le.refl _
      -- `evalArgs`
      · intro env ρ as
        simp only [evalArgs]
        exact Res.mapM_le (fun _ => harg _ _ _) as
      -- `evalDoms`
      · intro env ρ ds
        simp only [evalDoms]
        exact Res.mapM_le (fun _ => Res.map_le _ (hexp _ _ _)) ds
      -- `evalIterE`
      · intro env ρ e it ds
        cases it with
        | opt =>
            simp only [evalIterE]
            refine Res.bind_le (hdoms _ _ _) fun xvs => Res.assert_le ?_
            refine Res.bind_le (Res.Le.refl _) fun os => ?_
            split
            · exact Res.Le.refl _
            · split
              · exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
              · exact Res.Le.refl _
        | list =>
            simp only [evalIterE]
            exact Res.bind_le (hdoms _ _ _) fun _ =>
              Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hitl _ _ _ _ _ _)
        | list1 =>
            simp only [evalIterE]
            exact Res.bind_le (hdoms _ _ _) fun _ =>
              Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ =>
                Res.assert_le (hitl _ _ _ _ _ _))
        | listN eₙ x =>
            simp only [evalIterE]
            exact Res.bind_le (hdoms _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ =>
                Res.bind_le (Res.Le.refl _) fun _ => hitl _ _ _ _ _ _
      -- `evalIterList`
      · intro env ρ e xvs ido k
        simp only [evalIterList]
        exact Res.bind_le (Res.Le.refl _) fun _ =>
          Res.assert_le (Res.bind_le (hrnd _ _ _ _) fun _ => Res.Le.refl _)
      -- `evalRounds`
      · intro env ρ e rs
        simp only [evalRounds]
        exact Res.mapM_le (fun _ => hexp _ _ _) rs
      -- `pathGet`
      · intro env ρ v p
        cases p with
        | rootP => simp only [pathGet]; exact Res.Le.refl _
        | idxP p e =>
            simp only [pathGet]
            exact Res.bind_le (hpg _ _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | sliceP p e₁ e₂ =>
            simp only [pathGet]
            exact Res.bind_le (hpg _ _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ =>
                Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | dotP p a =>
            simp only [pathGet]
            exact Res.bind_le (hpg _ _ _ _) fun _ => Res.Le.refl _
      -- `pathSet`
      · intro env ρ v p w
        cases p with
        | rootP => simp only [pathSet]; exact Res.Le.refl _
        | idxP p e =>
            simp only [pathSet]
            exact Res.bind_le (hpg _ _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ =>
                Res.bind_le (Res.Le.refl _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ _
        | sliceP p e₁ e₂ =>
            simp only [pathSet]
            exact Res.bind_le (hpg _ _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ =>
                Res.bind_le (hexp _ _ _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ =>
                    Res.bind_le (Res.Le.refl _) fun _ =>
                      Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ _
        | dotP p a =>
            simp only [pathSet]
            exact Res.bind_le (hpg _ _ _ _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ _
      -- `patLen`
      · intro env ρ e
        cases e
        case listE es => simp only [patLen]; exact Res.Le.refl _
        case catE e₁ e₂ =>
          simp only [patLen]
          exact Res.bind_le (hpl _ _ _) fun _ =>
            Res.bind_le (hpl _ _ _) fun _ => Res.Le.refl _
        case iterE e₀ it =>
          cases it with
          | mk i ds =>
              cases i <;> simp only [patLen] <;>
                exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        case optE eo =>
          cases eo <;> simp only [patLen] <;>
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        all_goals
          simp only [patLen]
          exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
      -- `matchExp`
      · intro env ρ e v
        cases e
        case varE x => simp only [matchExp]; exact Res.Le.refl _
        case boolE b => simp only [matchExp]; exact Res.Le.refl _
        case numE n => simp only [matchExp]; exact Res.Le.refl _
        case textE t => simp only [matchExp]; exact Res.Le.refl _
        case unE op t e =>
          cases op <;> cases v <;> simp only [matchExp] <;>
            first
              | exact hmd _ _ _ _
              | exact Res.assert_le (hm _ _ _ _)
              | exact Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _ _)
        case tupE es =>
          simp only [matchExp]
          exact Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _ _
        case projE e i =>
          simp only [matchExp]
          split
          · exact hm _ _ _ _
          · exact hmd _ _ _ _
        case caseE op e =>
          simp only [matchExp]
          exact Res.bind_le (Res.Le.refl _) fun _ => Res.assert_le (hm _ _ _ _)
        case uncaseE e op => simp only [matchExp]; exact hm _ _ _ _
        case optE eo =>
          cases eo <;> simp only [matchExp] <;>
            first
              | exact Res.Le.refl _
              | exact Res.bind_le (Res.Le.refl _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _ _
        case strE fs =>
          simp only [matchExp]
          exact Res.bind_le (Res.Le.refl _) fun _ => hmf _ _ _ _
        case listE es =>
          simp only [matchExp]
          exact Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _ _
        case catE e₁ e₂ =>
          simp only [matchExp]
          refine Res.bind_le (Res.Le.refl _) fun vs => ?_
          refine Res.elimUndef_le (hpl _ _ _) (fun k => ?_) (fun _ => ?_)
          · exact Res.assert_le (Res.bind_le (hm _ _ _ _) fun _ => hm _ _ _ _)
          · refine Res.elimUndef_le (hpl _ _ _) (fun k => ?_) (fun _ => ?_)
            · exact Res.assert_le (Res.bind_le (hm _ _ _ _) fun _ => hm _ _ _ _)
            · exact Res.scan_le (fun _ => Res.bind_le (hm _ _ _ _) fun _ => hm _ _ _ _) _ _
        case iterE e₀ it =>
          cases it with
          | mk i ds => simp only [matchExp]; exact hmi _ _ _ _ _ _
        case cvtE e t₁ t₂ =>
          cases v <;> simp only [matchExp] <;>
            first
              | exact hmd _ _ _ _
              | exact Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _ _
        case subE e t₁ t₂ => simp only [matchExp]; exact hm _ _ _ _
        all_goals (simp only [matchExp]; exact hmd _ _ _ _)
      -- `matchDefault`
      · intro env ρ e v
        simp only [matchDefault]
        exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
      -- `matchExps`
      · intro env ρ es vs
        cases es with
        | nil => cases vs <;> simp only [matchExps] <;> exact Res.Le.refl _
        | cons e es =>
            cases vs with
            | nil => simp only [matchExps]; exact Res.Le.refl _
            | cons v vs =>
                simp only [matchExps]
                exact Res.bind_le (hm _ _ _ _) fun _ => hms _ _ _ _
      -- `matchExpFields`
      · intro env ρ fs gs
        cases fs with
        | nil => cases gs <;> simp only [matchExpFields] <;> exact Res.Le.refl _
        | cons f fs =>
            cases f with
            | mk a e =>
                cases gs with
                | nil => simp only [matchExpFields]; exact Res.Le.refl _
                | cons g gs =>
                    simp only [matchExpFields]
                    exact Res.assert_le (Res.bind_le (hm _ _ _ _) fun _ => hmf _ _ _ _)
      -- `matchIterE`
      · intro env ρ e it ds v
        cases it with
        | opt =>
            simp only [matchIterE]
            refine Res.bind_le (Res.Le.refl _) fun o => ?_
            cases o with
            | none => exact hms _ _ _ _
            | some w =>
                exact Res.bind_le (hm _ _ _ _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _ _
        | list =>
            simp only [matchIterE]
            exact Res.bind_le (Res.Le.refl _) fun _ => hmil _ _ _ _ _ _
        | list1 =>
            simp only [matchIterE]
            exact Res.bind_le (Res.Le.refl _) fun _ =>
              Res.assert_le (hmil _ _ _ _ _ _)
        | listN eₙ x =>
            simp only [matchIterE]
            exact Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (hm _ _ _ _) fun _ => hmil _ _ _ _ _ _
      -- `matchIterList`
      · intro env ρ e ds ido vs
        simp only [matchIterList]
        exact Res.bind_le (hmr _ _ _ _ _ _ _) fun _ => hms _ _ _ _
      -- `matchRounds`
      · intro env ρ e xs ido i vs
        cases vs with
        | nil => simp only [matchRounds]; exact Res.Le.refl _
        | cons v vs =>
            cases ido <;> simp only [matchRounds] <;>
              exact Res.bind_le (hm _ _ _ _) fun _ =>
                Res.bind_le (Res.Le.refl _) fun _ =>
                  Res.bind_le (hmr _ _ _ _ _ _ _) fun _ => Res.Le.refl _
      -- `matchArg`
      · intro env ρ a w
        cases a <;> cases w <;> simp only [matchArg] <;>
          first
            | exact Res.Le.refl _
            | (split
               · exact hm _ _ _ _
               · exact Res.Le.refl _)
      -- `matchArgs`
      · intro env ρ as ws
        cases as with
        | nil => cases ws <;> simp only [matchArgs] <;> exact Res.Le.refl _
        | cons a as =>
            cases ws with
            | nil => simp only [matchArgs]; exact Res.Le.refl _
            | cons w ws =>
                simp only [matchArgs]
                exact Res.bind_le (hma _ _ _ _) fun _ => hmas _ _ _ _
      -- `callDef`
      · intro env ρ x as
        simp only [callDef]
        exact Res.bind_le (hargs _ _ _) fun _ =>
          Res.bind_le (Res.Le.refl _) fun _ =>
            Res.elimUndef_le (htc _ _ _) (fun _ => Res.Le.refl _) (fun _ => Res.Le.refl _)
      -- `tryClauses`
      · intro env cs ws
        cases cs with
        | nil => simp only [tryClauses]; exact Res.Le.refl _
        | cons c cs =>
            cases c with
            | defD q pats e prems =>
                simp only [tryClauses]
                exact Res.elimUndef_le
                  (Res.bind_le (hmas _ _ _ _) fun _ => hphs _ _ _)
                  (fun _ => hexp _ _ _) (fun _ => htc _ _ _)
      -- `premHolds`
      · intro env ρ pr
        cases pr with
        | ifPr e =>
            simp only [premHolds]
            exact Res.bind_le (hexp _ _ _) fun _ => Res.Le.refl _
        | elsePr => simp only [premHolds]; exact Res.Le.refl _
        | letPr e₁ e₂ =>
            simp only [premHolds]
            exact Res.bind_le (hexp _ _ _) fun _ => hm _ _ _ _
        | rulePr x as op e =>
            simp only [premHolds]
            refine Res.bind_le (hargs _ _ _) fun avs =>
              Res.bind_le (hexp _ _ _) fun v => ?_
            cases hd : derives m env x op avs v with
            | true => rw [ih.derives _ _ _ _ _ hd]
            | false => exact Or.inl (by simp)
        | iterPr pr it =>
            cases it with
            | mk i ds => simp only [premHolds]; exact hpi _ _ _ _ _
      -- `premsHold`
      · intro env ρ prs
        simp only [premsHold]
        exact Res.foldlM_le (fun _ _ => hph _ _ _) prs ρ
      -- `premIter`
      · intro env ρ pr it ds
        cases it with
        | opt =>
            simp only [premIter]
            refine Res.bind_le (hdoms _ _ _) fun xvs => Res.assert_le ?_
            refine Res.bind_le (Res.Le.refl _) fun os => ?_
            split
            · exact Res.Le.refl _
            · split
              · exact Res.bind_le (hph _ _ _) fun _ => Res.Le.refl _
              · exact Res.Le.refl _
        | list =>
            simp only [premIter]
            exact Res.bind_le (hdoms _ _ _) fun _ =>
              Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hpr _ _ _ _ _ _)
        | list1 =>
            simp only [premIter]
            exact Res.bind_le (hdoms _ _ _) fun _ =>
              Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ =>
                Res.assert_le (hpr _ _ _ _ _ _))
        | listN eₙ x =>
            simp only [premIter]
            exact Res.bind_le (hdoms _ _ _) fun _ =>
              Res.bind_le (hexp _ _ _) fun _ =>
                Res.bind_le (Res.Le.refl _) fun _ => hpr _ _ _ _ _ _
      -- `premRounds`
      · intro env ρ pr xvs ido k
        simp only [premRounds]
        exact Res.bind_le (Res.Le.refl _) fun _ =>
          Res.assert_le (Res.bind_le (Res.mapM_le (fun _ => hph _ _ _) _) fun _ =>
            Res.Le.refl _)
      -- `derives`
      · intro env x op as v h
        simp only [derives] at h ⊢
        cases hr : env.findRel? x with
        | none => rw [hr] at h; simp at h
        | some d =>
            obtain ⟨ps, op', t, rules⟩ := d
            rw [hr] at h
            simp only [Bool.and_eq_true] at h ⊢
            exact ⟨h.1, ih.anyRule _ _ _ _ _ _ h.2⟩
      -- `anyRule`
      · intro env op ps as v rs h
        cases rs with
        | nil => simp only [anyRule] at h; exact absurd h (by simp)
        | cons r rs =>
            cases r with
            | ruleD y qs op' e prems =>
                simp only [anyRule, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
                rcases h with ⟨hop, hb⟩ | hrest
                · refine Or.inl ⟨hop, ?_⟩
                  refine Res.isOk_le ?_ hb
                  exact Res.bind_le (Res.Le.refl _) fun _ =>
                    Res.bind_le (hm _ _ _ _) fun _ => hphs _ _ _
                · exact Or.inr (ih.anyRule _ _ _ _ _ _ hrest)

/-- `MonoAt` is reflexive. -/
theorem monoAt_refl (m : Nat) : MonoAt m m := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
      | exact Res.Le.refl _
      | assumption

/-- `MonoAt` is transitive, field by field. -/
theorem monoAt_trans {a b c : Nat} (h₁ : MonoAt a b) (h₂ : MonoAt b c) :
    MonoAt a c where
  exp := fun env ρ e => (h₁.exp env ρ e).trans (h₂.exp env ρ e)
  exps := fun env ρ es => (h₁.exps env ρ es).trans (h₂.exps env ρ es)
  expFields := fun env ρ fs => (h₁.expFields env ρ fs).trans (h₂.expFields env ρ fs)
  arg := fun env ρ a => (h₁.arg env ρ a).trans (h₂.arg env ρ a)
  args := fun env ρ as => (h₁.args env ρ as).trans (h₂.args env ρ as)
  doms := fun env ρ ds => (h₁.doms env ρ ds).trans (h₂.doms env ρ ds)
  iterE := fun env ρ e it ds => (h₁.iterE env ρ e it ds).trans (h₂.iterE env ρ e it ds)
  iterList := fun env ρ e xvs ido k =>
    (h₁.iterList env ρ e xvs ido k).trans (h₂.iterList env ρ e xvs ido k)
  rounds := fun env ρ e rs => (h₁.rounds env ρ e rs).trans (h₂.rounds env ρ e rs)
  pathGet := fun env ρ v p => (h₁.pathGet env ρ v p).trans (h₂.pathGet env ρ v p)
  pathSet := fun env ρ v p w => (h₁.pathSet env ρ v p w).trans (h₂.pathSet env ρ v p w)
  patLen := fun env ρ e => (h₁.patLen env ρ e).trans (h₂.patLen env ρ e)
  matchExp := fun env ρ e v => (h₁.matchExp env ρ e v).trans (h₂.matchExp env ρ e v)
  matchDefault := fun env ρ e v => (h₁.matchDefault env ρ e v).trans (h₂.matchDefault env ρ e v)
  matchExps := fun env ρ es vs => (h₁.matchExps env ρ es vs).trans (h₂.matchExps env ρ es vs)
  matchExpFields := fun env ρ fs gs =>
    (h₁.matchExpFields env ρ fs gs).trans (h₂.matchExpFields env ρ fs gs)
  matchIterE := fun env ρ e it ds v =>
    (h₁.matchIterE env ρ e it ds v).trans (h₂.matchIterE env ρ e it ds v)
  matchIterList := fun env ρ e ds ido vs =>
    (h₁.matchIterList env ρ e ds ido vs).trans (h₂.matchIterList env ρ e ds ido vs)
  matchRounds := fun env ρ e xs ido i vs =>
    (h₁.matchRounds env ρ e xs ido i vs).trans (h₂.matchRounds env ρ e xs ido i vs)
  matchArg := fun env ρ a w => (h₁.matchArg env ρ a w).trans (h₂.matchArg env ρ a w)
  matchArgs := fun env ρ as ws => (h₁.matchArgs env ρ as ws).trans (h₂.matchArgs env ρ as ws)
  callDef := fun env ρ x as => (h₁.callDef env ρ x as).trans (h₂.callDef env ρ x as)
  tryClauses := fun env cs ws => (h₁.tryClauses env cs ws).trans (h₂.tryClauses env cs ws)
  premHolds := fun env ρ pr => (h₁.premHolds env ρ pr).trans (h₂.premHolds env ρ pr)
  premsHold := fun env ρ prs => (h₁.premsHold env ρ prs).trans (h₂.premsHold env ρ prs)
  premIter := fun env ρ pr it ds => (h₁.premIter env ρ pr it ds).trans (h₂.premIter env ρ pr it ds)
  premRounds := fun env ρ pr xvs ido k =>
    (h₁.premRounds env ρ pr xvs ido k).trans (h₂.premRounds env ρ pr xvs ido k)
  derives := fun _ _ _ _ _ h => h₂.derives _ _ _ _ _ (h₁.derives _ _ _ _ _ h)
  anyRule := fun _ _ _ _ _ _ h =>
    h₂.anyRule _ _ _ _ _ _ (h₁.anyRule _ _ _ _ _ _ h)

/-- **Monotonicity in fuel**, all members at once: more fuel never changes a
definite answer, and never turns a definite failure into a success. -/
theorem monoAt_of_le {m n : Nat} (h : m ≤ n) : MonoAt m n := by
  induction n, h using Nat.le_induction with
  | base => exact monoAt_refl m
  | succ n hn ihn => exact monoAt_trans ihn (monoAt_succ n)


/-! ### The relations the evaluator induces

Fuel is an artefact of the encoding, so the statements of interest quantify it
away.  `EvalExp env ρ e v` is "`e` denotes `v`", and so on for the other
members; `Derives` is the least fixpoint of a relation's rules. -/

/-- `e` denotes the value `v` in the script `env` and the scope `ρ`. -/
def EvalExp (env : Env) (ρ : VarEnv) (e : Exp) (v : Value) : Prop :=
  ∃ n, evalExp n env ρ e = .ok v

/-- A list of expressions denotes a list of values. -/
def EvalExps (env : Env) (ρ : VarEnv) (es : List Exp) (vs : List Value) : Prop :=
  ∃ n, evalExps n env ρ es = .ok vs

/-- A record expression denotes a list of named values. -/
def EvalExpFields (env : Env) (ρ : VarEnv) (fs : List ExpField)
    (gs : List (AtomS × Value)) : Prop :=
  ∃ n, evalExpFields n env ρ fs = .ok gs

/-- An argument list denotes a list of `ArgV`s. -/
def EvalArgs (env : Env) (ρ : VarEnv) (as : List Arg) (ws : List ArgV) : Prop :=
  ∃ n, evalArgs n env ρ as = .ok ws

/-- An iteration denotes a list or an option (`evalIterE`). -/
def EvalIterE (env : Env) (ρ : VarEnv) (e : Exp) (it : Iter) (ds : List Dom)
    (v : Value) : Prop :=
  ∃ n, evalIterE n env ρ e it ds = .ok v

/-- `p` selects `w` out of `v`. -/
def PathGet (env : Env) (ρ : VarEnv) (v : Value) (p : Path) (w : Value) : Prop :=
  ∃ n, pathGet n env ρ v p = .ok w

/-- Writing `w` through `p` into `v` gives `u`. -/
def PathSet (env : Env) (ρ : VarEnv) (v : Value) (p : Path) (w u : Value) : Prop :=
  ∃ n, pathSet n env ρ v p w = .ok u

/-- Calling `x` on `args` denotes `v`. -/
def CallDef (env : Env) (ρ : VarEnv) (x : IL.Id) (args : List Arg) (v : Value) : Prop :=
  ∃ n, callDef n env ρ x args = .ok v

/-- The pattern `e` matches `v`, extending `ρ` to `ρ'`. -/
def MatchExp (env : Env) (ρ : VarEnv) (e : Exp) (v : Value) (ρ' : VarEnv) : Prop :=
  ∃ n, matchExp n env ρ e v = .ok ρ'

/-- The premise `pr` holds, extending `ρ` to `ρ'`. -/
def PremHolds (env : Env) (ρ : VarEnv) (pr : Prem) (ρ' : VarEnv) : Prop :=
  ∃ n, premHolds n env ρ pr = .ok ρ'

/-- Every premise of `prs` holds, extending `ρ` to `ρ'`. -/
def PremsHold (env : Env) (ρ : VarEnv) (prs : List Prem) (ρ' : VarEnv) : Prop :=
  ∃ n, premsHold n env ρ prs = .ok ρ'

/-- `v` is derivable by the relation `x` at the arguments `args`: the least
fixpoint of `x`'s rules, reached by `derives` at some fuel level. -/
def Derives (env : Env) (x : IL.Id) (op : MixopS) (args : List ArgV) (v : Value) : Prop :=
  ∃ n, derives n env x op args v = true

/-! ### Monotonicity, in the form the relations use -/

/-- More fuel preserves a value `evalExp` has committed to. -/
theorem evalExp_ok_of_le {m n : Nat} {env ρ e v} (h : m ≤ n)
    (hv : evalExp m env ρ e = .ok v) : evalExp n env ρ e = .ok v :=
  ((monoAt_of_le h).exp env ρ e).ok hv

/-- More fuel preserves a value `evalExps` has committed to. -/
theorem evalExps_ok_of_le {m n : Nat} {env ρ es vs} (h : m ≤ n)
    (hv : evalExps m env ρ es = .ok vs) : evalExps n env ρ es = .ok vs :=
  ((monoAt_of_le h).exps env ρ es).ok hv

/-- More fuel preserves a value `evalExpFields` has committed to. -/
theorem evalExpFields_ok_of_le {m n : Nat} {env ρ fs gs} (h : m ≤ n)
    (hv : evalExpFields m env ρ fs = .ok gs) : evalExpFields n env ρ fs = .ok gs :=
  ((monoAt_of_le h).expFields env ρ fs).ok hv

/-- More fuel preserves a value `evalArgs` has committed to. -/
theorem evalArgs_ok_of_le {m n : Nat} {env ρ as ws} (h : m ≤ n)
    (hv : evalArgs m env ρ as = .ok ws) : evalArgs n env ρ as = .ok ws :=
  ((monoAt_of_le h).args env ρ as).ok hv

/-- More fuel preserves a value `evalIterE` has committed to. -/
theorem evalIterE_ok_of_le {m n : Nat} {env ρ e it ds v} (h : m ≤ n)
    (hv : evalIterE m env ρ e it ds = .ok v) : evalIterE n env ρ e it ds = .ok v :=
  ((monoAt_of_le h).iterE env ρ e it ds).ok hv

/-- More fuel preserves a value `pathGet` has committed to. -/
theorem pathGet_ok_of_le {m n : Nat} {env ρ v p w} (h : m ≤ n)
    (hv : pathGet m env ρ v p = .ok w) : pathGet n env ρ v p = .ok w :=
  ((monoAt_of_le h).pathGet env ρ v p).ok hv

/-- More fuel preserves a value `pathSet` has committed to. -/
theorem pathSet_ok_of_le {m n : Nat} {env ρ v p w u} (h : m ≤ n)
    (hv : pathSet m env ρ v p w = .ok u) : pathSet n env ρ v p w = .ok u :=
  ((monoAt_of_le h).pathSet env ρ v p w).ok hv

/-- More fuel preserves a value `callDef` has committed to. -/
theorem callDef_ok_of_le {m n : Nat} {env ρ x as v} (h : m ≤ n)
    (hv : callDef m env ρ x as = .ok v) : callDef n env ρ x as = .ok v :=
  ((monoAt_of_le h).callDef env ρ x as).ok hv

/-- More fuel preserves a scope `matchExp` has committed to. -/
theorem matchExp_ok_of_le {m n : Nat} {env ρ e v ρ'} (h : m ≤ n)
    (hv : matchExp m env ρ e v = .ok ρ') : matchExp n env ρ e v = .ok ρ' :=
  ((monoAt_of_le h).matchExp env ρ e v).ok hv

/-- More fuel preserves a scope `premHolds` has committed to. -/
theorem premHolds_ok_of_le {m n : Nat} {env ρ pr ρ'} (h : m ≤ n)
    (hv : premHolds m env ρ pr = .ok ρ') : premHolds n env ρ pr = .ok ρ' :=
  ((monoAt_of_le h).premHolds env ρ pr).ok hv

/-- More fuel preserves a scope `premsHold` has committed to. -/
theorem premsHold_ok_of_le {m n : Nat} {env ρ prs ρ'} (h : m ≤ n)
    (hv : premsHold m env ρ prs = .ok ρ') : premsHold n env ρ prs = .ok ρ' :=
  ((monoAt_of_le h).premsHold env ρ prs).ok hv

/-- `derives` is monotone in fuel: it climbs towards a least fixpoint. -/
theorem derives_of_le {m n : Nat} {env x op as v} (h : m ≤ n)
    (hv : derives m env x op as v = true) : derives n env x op as v = true :=
  (monoAt_of_le h).derives env x op as v hv

/-! ### Determinism

Each relation is functional, immediately from monotonicity plus the fact that
a function is a function: run both derivations at the larger of their two fuel
levels and compare. -/

/-- Evaluation is deterministic. -/
theorem EvalExp.unique {env ρ e v₁ v₂} (h₁ : EvalExp env ρ e v₁)
    (h₂ : EvalExp env ρ e v₂) : v₁ = v₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have k₁ := evalExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have k₂ := evalExp_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  simpa using k₁.symm.trans k₂

/-- Matching is deterministic. -/
theorem MatchExp.unique {env ρ e v ρ₁ ρ₂} (h₁ : MatchExp env ρ e v ρ₁)
    (h₂ : MatchExp env ρ e v ρ₂) : ρ₁ = ρ₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have k₁ := matchExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have k₂ := matchExp_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  simpa using k₁.symm.trans k₂

/-- Calling a definition is deterministic. -/
theorem CallDef.unique {env ρ x as v₁ v₂} (h₁ : CallDef env ρ x as v₁)
    (h₂ : CallDef env ρ x as v₂) : v₁ = v₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have k₁ := callDef_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have k₂ := callDef_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  simpa using k₁.symm.trans k₂

/-- A premise determines the scope it extends to. -/
theorem PremHolds.unique {env ρ pr ρ₁ ρ₂} (h₁ : PremHolds env ρ pr ρ₁)
    (h₂ : PremHolds env ρ pr ρ₂) : ρ₁ = ρ₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have k₁ := premHolds_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have k₂ := premHolds_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  simpa using k₁.symm.trans k₂

/-! ### Literals

Every value is already an expression: `lit` sends each `Value` constructor to
the `Exp` constructor that `evalExp` interprets back into it.  This is what
makes `evalRel` surjective, and it is the only part of the `EncRel` reading of
`evalExp` that needs a construction rather than a projection. -/

mutual

/-- The literal expression denoting a value.  `boolE`, `numE`, `textE`,
`tupE`, `caseE`, `strE`, `listE` and `optE` mirror `Value`'s constructors one
for one; `evalExp` sends each back to the value it came from (`litE`). -/
def lit : Value → Exp
  | .bool b => .boolE b
  | .num n => .numE n
  | .text t => .textE t
  | .tuple vs => .tupE (litList vs)
  | .case op v => .caseE op (lit v)
  | .struct fs => .strE (litFields fs)
  | .list vs => .listE (litList vs)
  | .opt none => .optE none
  | .opt (some v) => .optE (some (lit v))

/-- `lit` on a list of values, for `tupE` and `listE`. -/
def litList : List Value → List Exp
  | [] => []
  | v :: vs => lit v :: litList vs

/-- `lit` on a record's fields, for `strE`. -/
def litFields : List (AtomS × Value) → List ExpField
  | [] => []
  | f :: fs => .mk f.1 (lit f.2) :: litFields fs

end

/-- Correctness of `lit`, at every fuel level, for the three mutually
recursive forms at once.

The budgets differ by one because `evalExps` and `evalExpFields` spend a unit
of fuel on the traversal itself before reaching the elements: a value of size
`k` needs `2 * k + 1`, a list of total size `k` needs `2 * k + 2`.  The
induction is on the fuel, not on the value — one step of `lit` costs one step
of `evalExp`, and the three statements feed each other across that step. -/
theorem litAt (env : Env) (ρ : VarEnv) : ∀ n : Nat,
    (∀ v : Value, 2 * v.size + 1 ≤ n → evalExp n env ρ (lit v) = .ok v) ∧
    (∀ vs : List Value, 2 * Value.sizes vs + 2 ≤ n →
      evalExps n env ρ (litList vs) = .ok vs) ∧
    (∀ fs : List (AtomS × Value), 2 * Value.sizesFields fs + 2 ≤ n →
      evalExpFields n env ρ (litFields fs) = .ok fs) := by
  intro n
  induction n with
  | zero =>
      exact ⟨fun _ hv => absurd hv (by omega), fun _ hv => absurd hv (by omega),
        fun _ hv => absurd hv (by omega)⟩
  | succ m ih =>
      obtain ⟨ihE, ihL, ihF⟩ := ih
      refine ⟨fun v hv => ?_, fun vs hvs => ?_, fun fs hfs => ?_⟩
      · cases v with
        | bool b => simp [lit, evalExp]
        | num k => simp [lit, evalExp]
        | text t => simp [lit, evalExp]
        | tuple vs =>
            simp only [Value.size_tuple] at hv
            simp only [lit, evalExp, ihL vs (by omega)]
            rfl
        | case op v =>
            simp only [Value.size_case] at hv
            simp only [lit, evalExp, ihE v (by omega)]
            rfl
        | struct fs =>
            simp only [Value.size_struct] at hv
            simp only [lit, evalExp, ihF fs (by omega)]
            rfl
        | list vs =>
            simp only [Value.size_list] at hv
            simp only [lit, evalExp, ihL vs (by omega)]
            rfl
        | opt o =>
            cases o with
            | none => simp [lit, evalExp]
            | some v =>
                simp only [Value.size_opt_some] at hv
                simp only [lit, evalExp, ihE v (by omega)]
                rfl
      · have key : ∀ l : List Value, 2 * Value.sizes l + 1 ≤ m →
            (litList l).mapM (evalExp m env ρ) = .ok l := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons v l ih₂ =>
              intro hl
              simp only [Value.sizes_cons] at hl
              simp only [litList, List.mapM_cons, ihE v (by omega), ih₂ (by omega)]
              rfl
        simp only [evalExps]
        exact key vs (by omega)
      · have key : ∀ l : List (AtomS × Value), 2 * Value.sizesFields l + 1 ≤ m →
            (litFields l).mapM (fun f => match f with
              | .mk a e => (fun v => (a, v)) <$> evalExp m env ρ e) = .ok l := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons f l ih₂ =>
              intro hl
              simp only [Value.sizesFields_cons] at hl
              simp only [litFields, List.mapM_cons, ihE f.2 (by omega), ih₂ (by omega)]
              rfl
        simp only [evalExpFields]
        exact key fs (by omega)

/-- `lit v` evaluates to `v` at any fuel budget of `2 * v.size + 1` or more. -/
theorem litE (env : Env) (ρ : VarEnv) (v : Value) (n : Nat)
    (h : 2 * v.size + 1 ≤ n) : evalExp n env ρ (lit v) = .ok v :=
  (litAt env ρ n).1 v h

/-- The relational form: every value is denoted by its own literal. -/
theorem evalExp_lit (env : Env) (ρ : VarEnv) (v : Value) : EvalExp env ρ (lit v) v :=
  ⟨2 * v.size + 1, litE env ρ v _ (Nat.le_refl _)⟩

/-- `|true|` — the length of a boolean — has no value at any fuel level:
`Value.len?` is defined on `list` only (`eval.ml:351-357`), and `eval.ml:356`
leaves the `LenE` stuck. -/
theorem evalExp_lenE_boolE (n : Nat) (env : Env) (ρ : VarEnv) (b : Bool) (v : Value) :
    evalExp n env ρ (.lenE (.boolE b)) ≠ .ok v := by
  match n with
  | 0 => simp [evalExp]
  | 1 => simp [evalExp]
  | _ + 2 => simp [evalExp, Value.len?]

/-- The denotation of an expression, as a value of
`Silmaril/Encoding/Relation.lean`'s `EncRel`: the carrier is the `Value` and
the "syntax" is the expression, so that `EncRel.Deterministic` — "the syntax
determines the carrier" — is precisely determinism of evaluation.

Reading it the other way round, `EncRel.Functional` would say that a value
determines the expression that computed it, which is false and uninteresting.

The two remaining properties are easy to confuse, so both are recorded as
theorems.  With `σ = Value` and `α = Exp`, `EncRel.Surjective` is "every
*carrier* value has a spelling", i.e. every value is denoted by some
expression — and that is **true**: `evalRel_surjective`, witnessed by `lit`.
It is `EncRel.Total`, "every expression denotes something", that fails, and
`not_evalRel_total` gives a stuck expression as the witness. -/
def evalRel (env : Env) (ρ : VarEnv) : EncRel Value Exp := fun v e => EvalExp env ρ e v

/-- Determinism of evaluation, in `EncRel` vocabulary. -/
theorem evalRel_deterministic (env : Env) (ρ : VarEnv) : (evalRel env ρ).Deterministic :=
  fun _ _ _ h₁ h₂ => h₁.unique h₂

/-- An expression is `EncRel.Encodable` for `evalRel` exactly when it has a
denotation. -/
theorem evalRel_encodable_iff {env : Env} {ρ : VarEnv} {v : Value} :
    (evalRel env ρ).Encodable v ↔ ∃ e, EvalExp env ρ e v := Iff.rfl

/-- `evalRel` is surjective: every *value* is denoted by some expression,
namely its own literal.  This is the property the `EncRel` vocabulary calls
`Surjective` — "every carrier value is a valid spelling of something". -/
theorem evalRel_surjective (env : Env) (ρ : VarEnv) : (evalRel env ρ).Surjective :=
  fun v => ⟨lit v, 2 * v.size + 1, litE env ρ v (2 * v.size + 1) (Nat.le_refl _)⟩

/-- `evalRel` is **not** total: not every expression denotes something.  The
witness is `|true|`, which `evalExp_lenE_boolE` shows is stuck at every fuel
level.  This is the statement the docstring of `evalRel` used to attribute to
`Surjective`. -/
theorem not_evalRel_total (env : Env) (ρ : VarEnv) : ¬ (evalRel env ρ).Total := by
  intro h
  obtain ⟨v, n, hn⟩ := h (.lenE (.boolE true))
  exact evalExp_lenE_boolE n env ρ true v hn


/-! ### Compositionality

One lemma per `Exp` constructor, stating the denotation of the whole in terms
of the denotations of its parts.  These are the equation lemmas of `evalExp`
transported to the fuel-free relation, which is the form they are usable in:
the forward direction strips one unit of fuel, the backward direction runs the
sub-derivations at a common fuel level (`Nat.max`) and adds one.

The simp set `[evalExp, Res.bind_eq_ok, Res.map_eq_ok, Res.ofOption_eq_ok,
Res.assert_eq_ok]` is what does the stripping; everything else is bookkeeping
about the shape of the values involved. -/

section Compositionality

variable {env : Env} {ρ : VarEnv} {v : Value}

/-- A variable denotes what the scope binds it to. -/
theorem evalExp_varE_iff {x : IL.Id} : EvalExp env ρ (.varE x) v ↔ ρ.findVal? x = some v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n => simpa [evalExp] using h
  · intro h; exact ⟨1, by simpa [evalExp] using h⟩

/-- A boolean literal denotes itself. -/
theorem evalExp_boolE_iff {b : Bool} : EvalExp env ρ (.boolE b) v ↔ v = .bool b := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n => simpa [evalExp, eq_comm] using h
  · rintro rfl; exact ⟨1, by simp [evalExp]⟩

/-- A numeral denotes itself. -/
theorem evalExp_numE_iff {m : Num} : EvalExp env ρ (.numE m) v ↔ v = .num m := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n => simpa [evalExp, eq_comm] using h
  · rintro rfl; exact ⟨1, by simp [evalExp]⟩

/-- A text literal denotes itself; zero occurrences in the pinned corpus. -/
theorem evalExp_textE_iff {t : Text} : EvalExp env ρ (.textE t) v ↔ v = .text t := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n => simpa [evalExp, eq_comm] using h
  · rintro rfl; exact ⟨1, by simp [evalExp]⟩

/-- `UnE` applies `unValue` to the denotation of its operand. -/
theorem evalExp_unE_iff {op : UnOp} {t : OpTyp} {e : Exp} :
    EvalExp env ρ (.unE op t e) v ↔ ∃ w, EvalExp env ρ e w ∧ unValue op w = .ok v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok] at h
        obtain ⟨w, hw, hv⟩ := h
        exact ⟨w, ⟨n, hw⟩, hv⟩
  · rintro ⟨w, ⟨n, hw⟩, hv⟩
    exact ⟨n + 1, by simp only [evalExp, Res.bind_eq_ok]; exact ⟨w, hw, hv⟩⟩

/-- `BinE` evaluates its left operand first: either `boolShort` settles the
answer there and the right operand is never consulted, or both are needed. -/
theorem evalExp_binE_iff {op : BinOp} {t : OpTyp} {e₁ e₂ : Exp} :
    EvalExp env ρ (.binE op t e₁ e₂) v ↔
      ∃ v₁, EvalExp env ρ e₁ v₁ ∧
        (boolShort op v₁ = some v ∨
          boolShort op v₁ = none ∧
            ∃ v₂, EvalExp env ρ e₂ v₂ ∧ binValues op v₁ v₂ = .ok v) := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok] at h
        obtain ⟨v₁, h₁, h₂⟩ := h
        refine ⟨v₁, ⟨n, h₁⟩, ?_⟩
        cases hs : boolShort op v₁ with
        | some u => rw [hs] at h₂; exact Or.inl (by simpa using h₂)
        | none =>
            rw [hs] at h₂
            simp only [Res.bind_eq_ok] at h₂
            obtain ⟨v₂, h₃, h₄⟩ := h₂
            exact Or.inr ⟨rfl, v₂, ⟨n, h₃⟩, h₄⟩
  · rintro ⟨v₁, ⟨n₁, h₁⟩, hs | ⟨hs, v₂, ⟨n₂, h₂⟩, h₄⟩⟩
    · exact ⟨n₁ + 1, by simp only [evalExp, Res.bind_eq_ok]; exact ⟨v₁, h₁, by rw [hs]⟩⟩
    · refine ⟨max n₁ n₂ + 1, ?_⟩
      simp only [evalExp, Res.bind_eq_ok]
      refine ⟨v₁, evalExp_ok_of_le (by omega) h₁, ?_⟩
      rw [hs]
      simp only [Res.bind_eq_ok]
      exact ⟨v₂, evalExp_ok_of_le (by omega) h₂, h₄⟩

/-- `CmpE` applies `cmpValues` to the denotations of its two operands. -/
theorem evalExp_cmpE_iff {op : CmpOp} {t : OpTyp} {e₁ e₂ : Exp} :
    EvalExp env ρ (.cmpE op t e₁ e₂) v ↔
      ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ cmpValues op v₁ v₂ = .ok v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok] at h
        obtain ⟨v₁, h₁, v₂, h₂, h₃⟩ := h
        exact ⟨v₁, v₂, ⟨n, h₁⟩, ⟨n, h₂⟩, h₃⟩
  · rintro ⟨v₁, v₂, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, h₃⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok]
    exact ⟨v₁, evalExp_ok_of_le (by omega) h₁, v₂, evalExp_ok_of_le (by omega) h₂, h₃⟩

/-- A tuple denotes the tuple of its components' denotations. -/
theorem evalExp_tupE_iff {es : List Exp} :
    EvalExp env ρ (.tupE es) v ↔ ∃ vs, EvalExps env ρ es vs ∧ v = .tuple vs := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.map_eq_ok] at h
        obtain ⟨vs, hvs, rfl⟩ := h
        exact ⟨vs, ⟨n, hvs⟩, rfl⟩
  · rintro ⟨vs, ⟨n, hvs⟩, rfl⟩
    exact ⟨n + 1, by simp [evalExp, hvs]⟩

/-- A list denotes the list of its components' denotations. -/
theorem evalExp_listE_iff {es : List Exp} :
    EvalExp env ρ (.listE es) v ↔ ∃ vs, EvalExps env ρ es vs ∧ v = .list vs := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.map_eq_ok] at h
        obtain ⟨vs, hvs, rfl⟩ := h
        exact ⟨vs, ⟨n, hvs⟩, rfl⟩
  · rintro ⟨vs, ⟨n, hvs⟩, rfl⟩
    exact ⟨n + 1, by simp [evalExp, hvs]⟩

/-- A record denotes the record of its fields' denotations. -/
theorem evalExp_strE_iff {fs : List ExpField} :
    EvalExp env ρ (.strE fs) v ↔ ∃ gs, EvalExpFields env ρ fs gs ∧ v = .struct gs := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.map_eq_ok] at h
        obtain ⟨gs, hgs, rfl⟩ := h
        exact ⟨gs, ⟨n, hgs⟩, rfl⟩
  · rintro ⟨gs, ⟨n, hgs⟩, rfl⟩
    exact ⟨n + 1, by simp [evalExp, hgs]⟩

/-- A projection picks a component out of a tuple; a negative index picks
nothing (`Exp.projE` keeps OCaml's `int`). -/
theorem evalExp_projE_iff {e : Exp} {i : Int} :
    EvalExp env ρ (.projE e i) v ↔
      ∃ vs, EvalExp env ρ e (.tuple vs) ∧ 0 ≤ i ∧ vs[i.toNat]? = some v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asTuple?_eq_some] at h
        obtain ⟨w, hw, vs, rfl, hidx⟩ := h
        split at hidx
        · rename_i hi; exact ⟨vs, ⟨n, hw⟩, hi, hidx⟩
        · exact absurd hidx (by simp)
  · rintro ⟨vs, ⟨n, hw⟩, hi, hidx⟩
    refine ⟨n + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asTuple?_eq_some]
    exact ⟨.tuple vs, hw, vs, rfl, by simp [hi, hidx]⟩

/-- An injection wraps the denotation of its payload. -/
theorem evalExp_caseE_iff {op : MixopS} {e : Exp} :
    EvalExp env ρ (.caseE op e) v ↔ ∃ w, EvalExp env ρ e w ∧ v = .case op w := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.map_eq_ok] at h
        obtain ⟨w, hw, rfl⟩ := h
        exact ⟨w, ⟨n, hw⟩, rfl⟩
  · rintro ⟨w, ⟨n, hw⟩, rfl⟩
    exact ⟨n + 1, by simp [evalExp, hw]⟩

/-- A projection out of an injection: the operand must denote exactly that
injection. -/
theorem evalExp_uncaseE_iff {e : Exp} {op : MixopS} :
    EvalExp env ρ (.uncaseE e op) v ↔ EvalExp env ρ e (.case op v) := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at h
        obtain ⟨w, hw, p, hp, hop, hv⟩ := h
        obtain ⟨o, u⟩ := p
        simp only [Value.asCase?_eq_some] at hp
        subst hp
        cases hop
        simp only [Except.ok.injEq] at hv
        subst hv
        exact ⟨n, hw⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by simp [evalExp, h]⟩

/-- The empty option denotes itself. -/
theorem evalExp_optE_none_iff : EvalExp env ρ (.optE none) v ↔ v = .opt none := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n => simpa [evalExp, eq_comm] using h
  · rintro rfl; exact ⟨1, by simp [evalExp]⟩

/-- A non-empty option wraps the denotation of its contents. -/
theorem evalExp_optE_some_iff {e : Exp} :
    EvalExp env ρ (.optE (some e)) v ↔ ∃ w, EvalExp env ρ e w ∧ v = .opt (some w) := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.map_eq_ok] at h
        obtain ⟨w, hw, rfl⟩ := h
        exact ⟨w, ⟨n, hw⟩, rfl⟩
  · rintro ⟨w, ⟨n, hw⟩, rfl⟩
    exact ⟨n + 1, by simp [evalExp, hw]⟩

/-- Forcing an option: the operand must denote a non-empty one.  Zero
occurrences in the pinned corpus. -/
theorem evalExp_theE_iff {e : Exp} :
    EvalExp env ρ (.theE e) v ↔ EvalExp env ρ e (.opt (some v)) := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asOpt?_eq_some] at h
        obtain ⟨w, hw, o, rfl, rfl⟩ := h
        exact ⟨n, hw⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by simp [evalExp, h]⟩

/-- Field selection is `Value.field?` of the denotation of the record. -/
theorem evalExp_dotE_iff {e : Exp} {a : AtomS} :
    EvalExp env ρ (.dotE e a) v ↔ ∃ w, EvalExp env ρ e w ∧ w.field? a = some v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨w, hw, hf⟩ := h
        exact ⟨w, ⟨n, hw⟩, hf⟩
  · rintro ⟨w, ⟨n, hw⟩, hf⟩
    exact ⟨n + 1, by simp [evalExp, hw, hf]⟩

/-- Composition is `Value.comp?` of the two denotations. -/
theorem evalExp_compE_iff {e₁ e₂ : Exp} :
    EvalExp env ρ (.compE e₁ e₂) v ↔
      ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ Value.comp? v₁ v₂ = some v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨v₁, h₁, v₂, h₂, h₃⟩ := h
        exact ⟨v₁, v₂, ⟨n, h₁⟩, ⟨n, h₂⟩, h₃⟩
  · rintro ⟨v₁, v₂, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, h₃⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨v₁, evalExp_ok_of_le (by omega) h₁, v₂, evalExp_ok_of_le (by omega) h₂, h₃⟩

/-- Lifting an option to a list. -/
theorem evalExp_liftE_iff {e : Exp} :
    EvalExp env ρ (.liftE e) v ↔ ∃ o, EvalExp env ρ e (.opt o) ∧ v = .list o.toList := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asOpt?_eq_some] at h
        obtain ⟨w, hw, o, rfl, hv⟩ := h
        exact ⟨o, ⟨n, hw⟩, by simpa [eq_comm] using hv⟩
  · rintro ⟨o, ⟨n, hw⟩, rfl⟩
    exact ⟨n + 1, by simp [evalExp, hw]⟩

/-- Membership is `memValue` of the two denotations. -/
theorem evalExp_memE_iff {e₁ e₂ : Exp} :
    EvalExp env ρ (.memE e₁ e₂) v ↔
      ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ memValue v₁ v₂ = .ok v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok] at h
        obtain ⟨v₁, h₁, v₂, h₂, h₃⟩ := h
        exact ⟨v₁, v₂, ⟨n, h₁⟩, ⟨n, h₂⟩, h₃⟩
  · rintro ⟨v₁, v₂, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, h₃⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok]
    exact ⟨v₁, evalExp_ok_of_le (by omega) h₁, v₂, evalExp_ok_of_le (by omega) h₂, h₃⟩

/-- Length is defined on lists only. -/
theorem evalExp_lenE_iff {e : Exp} :
    EvalExp env ρ (.lenE e) v ↔
      ∃ vs, EvalExp env ρ e (.list vs) ∧ v = .num (.natN vs.length) := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
        obtain ⟨w, hw, k, hk, rfl⟩ := h
        rw [Value.len?_eq_some] at hk
        obtain ⟨vs, rfl, rfl⟩ := hk
        exact ⟨vs, ⟨n, hw⟩, rfl⟩
  · rintro ⟨vs, ⟨n, hw⟩, rfl⟩
    exact ⟨n + 1, by simp [evalExp, hw]⟩

/-- Concatenation is `Value.cat?` of the two denotations. -/
theorem evalExp_catE_iff {e₁ e₂ : Exp} :
    EvalExp env ρ (.catE e₁ e₂) v ↔
      ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ Value.cat? v₁ v₂ = some v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨v₁, h₁, v₂, h₂, h₃⟩ := h
        exact ⟨v₁, v₂, ⟨n, h₁⟩, ⟨n, h₂⟩, h₃⟩
  · rintro ⟨v₁, v₂, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, h₃⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨v₁, evalExp_ok_of_le (by omega) h₁, v₂, evalExp_ok_of_le (by omega) h₂, h₃⟩

/-- Indexing: the index must denote a `nat`. -/
theorem evalExp_idxE_iff {e₁ e₂ : Exp} :
    EvalExp env ρ (.idxE e₁ e₂) v ↔
      ∃ w i, EvalExp env ρ e₁ w ∧ EvalExp env ρ e₂ (.num (.natN i)) ∧ w.idx? i = some v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asNat?_eq_some] at h
        obtain ⟨w, hw, u, hu, i, rfl, hi⟩ := h
        exact ⟨w, i, ⟨n, hw⟩, ⟨n, hu⟩, hi⟩
  · rintro ⟨w, i, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, h₃⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨w, evalExp_ok_of_le (by omega) h₁, _, evalExp_ok_of_le (by omega) h₂, _, rfl, h₃⟩

/-- Slicing: both bounds must denote `nat`s, and `Value.slice?` keeps
`eval.ml:284`'s strict bound. -/
theorem evalExp_sliceE_iff {e₁ e₂ e₃ : Exp} :
    EvalExp env ρ (.sliceE e₁ e₂ e₃) v ↔
      ∃ w i k, EvalExp env ρ e₁ w ∧ EvalExp env ρ e₂ (.num (.natN i)) ∧
        EvalExp env ρ e₃ (.num (.natN k)) ∧ w.slice? i k = some v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asNat?_eq_some] at h
        obtain ⟨w, hw, u₂, hu₂, u₃, hu₃, i, rfl, k, rfl, hs⟩ := h
        exact ⟨w, i, k, ⟨n, hw⟩, ⟨n, hu₂⟩, ⟨n, hu₃⟩, hs⟩
  · rintro ⟨w, i, k, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, ⟨n₃, h₃⟩, h₄⟩
    refine ⟨max n₁ (max n₂ n₃) + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨w, evalExp_ok_of_le (by omega) h₁, _, evalExp_ok_of_le (by omega) h₂,
      _, evalExp_ok_of_le (by omega) h₃, _, rfl, _, rfl, h₄⟩

/-- A functional update writes the second denotation through the path. -/
theorem evalExp_updE_iff {e₁ e₂ : Exp} {p : Path} :
    EvalExp env ρ (.updE e₁ p e₂) v ↔
      ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ PathSet env ρ v₁ p v₂ v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok] at h
        obtain ⟨v₁, h₁, v₂, h₂, h₃⟩ := h
        exact ⟨v₁, v₂, ⟨n, h₁⟩, ⟨n, h₂⟩, ⟨n, h₃⟩⟩
  · rintro ⟨v₁, v₂, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, ⟨n₃, h₃⟩⟩
    refine ⟨max n₁ (max n₂ n₃) + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok]
    exact ⟨v₁, evalExp_ok_of_le (by omega) h₁, v₂, evalExp_ok_of_le (by omega) h₂,
      pathSet_ok_of_le (by omega) h₃⟩

/-- An extension reads the path, concatenates, and writes back
(`eval.ml:302-303`). -/
theorem evalExp_extE_iff {e₁ e₂ : Exp} {p : Path} :
    EvalExp env ρ (.extE e₁ p e₂) v ↔
      ∃ v₁ v₂ u u', EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ PathGet env ρ v₁ p u ∧
        Value.cat? u v₂ = some u' ∧ PathSet env ρ v₁ p u' v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨v₁, h₁, v₂, h₂, u, hu, u', hu', h₃⟩ := h
        exact ⟨v₁, v₂, u, u', ⟨n, h₁⟩, ⟨n, h₂⟩, ⟨n, hu⟩, hu', ⟨n, h₃⟩⟩
  · rintro ⟨v₁, v₂, u, u', ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, ⟨n₃, h₃⟩, h₄, ⟨n₄, h₅⟩⟩
    refine ⟨max (max n₁ n₂) (max n₃ n₄) + 1, ?_⟩
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨v₁, evalExp_ok_of_le (by omega) h₁, v₂, evalExp_ok_of_le (by omega) h₂,
      u, pathGet_ok_of_le (by omega) h₃, u', h₄, pathSet_ok_of_le (by omega) h₅⟩

/-- A call delegates to `callDef`. -/
theorem evalExp_callE_iff {x : IL.Id} {as : List Arg} :
    EvalExp env ρ (.callE x as) v ↔ CallDef env ρ x as v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n => exact ⟨n, by simpa [evalExp] using h⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by simpa [evalExp] using h⟩

/-- An iteration delegates to `evalIterE`. -/
theorem evalExp_iterE_iff {e : Exp} {it : Iter} {ds : List Dom} :
    EvalExp env ρ (.iterE e (.mk it ds)) v ↔ EvalIterE env ρ e it ds v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n => exact ⟨n, by simpa [evalExp] using h⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by simpa [evalExp] using h⟩

/-- A numeric conversion depends only on its target type (`eval.ml:488`). -/
theorem evalExp_cvtE_iff {e : Exp} {t₁ t₂ : NumTyp} :
    EvalExp env ρ (.cvtE e t₁ t₂) v ↔
      ∃ m m', EvalExp env ρ e (.num m) ∧ Num.cvt t₂ m = some m' ∧ v = .num m' := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n =>
        simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asNum?_eq_some,
          Option.map_eq_some_iff] at h
        obtain ⟨w, hw, m, rfl, m', hm, rfl⟩ := h
        exact ⟨m, m', ⟨n, hw⟩, hm, rfl⟩
  · rintro ⟨m, m', ⟨n, hw⟩, hm, rfl⟩
    exact ⟨n + 1, by simp [evalExp, hw, hm]⟩

/-- A subtype coercion is the identity on values: see `evalExp`'s `SubE`
clause. -/
theorem evalExp_subE_iff {e : Exp} {t₁ t₂ : Typ} :
    EvalExp env ρ (.subE e t₁ t₂) v ↔ EvalExp env ρ e v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExp] at h
    | succ n => exact ⟨n, by simpa [evalExp] using h⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by simpa [evalExp] using h⟩

end Compositionality


/-! ### Environment weakening

`matchExp` and the premises only ever *extend* the scope they are given: every
binding they make is a `Map.bind`, which prepends (or, for the wildcard `"_"`,
does nothing), so the incoming maps survive as suffixes of the outgoing ones.
That is the precise sense in which a successful match is a weakening. -/

namespace VarEnv

/-- `ρ.Extends σ`: `σ` was obtained from `ρ` by adding bindings in front, in
each of the four namespaces.  `Map` is an association list searched from the
front (`Map.find?`), so a suffix is exactly "nothing was removed". -/
def Extends (ρ σ : VarEnv) : Prop :=
  ρ.vals <:+ σ.vals ∧ ρ.typs <:+ σ.typs ∧ ρ.defs <:+ σ.defs ∧ ρ.grams <:+ σ.grams

@[refl] theorem Extends.refl (ρ : VarEnv) : ρ.Extends ρ :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _⟩

theorem Extends.trans {ρ σ τ : VarEnv} (h₁ : ρ.Extends σ) (h₂ : σ.Extends τ) :
    ρ.Extends τ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.trans h₂.2.2.2⟩

/-- `Map.bind` only ever prepends. -/
theorem suffix_bind {α : Type} (m : Map α) (x : IL.Id) (a : α) : m <:+ m.bind x a := by
  by_cases h : x = "_"
  · simp [Map.bind, h]
  · simp only [Map.bind, h, ite_false]
    exact List.suffix_cons _ _

theorem extends_bindVal (ρ : VarEnv) (x : IL.Id) (w : Value) :
    ρ.Extends (ρ.bindVal x w) :=
  ⟨suffix_bind _ _ _, List.suffix_refl _, List.suffix_refl _, List.suffix_refl _⟩

theorem extends_bindTyp (ρ : VarEnv) (x : IL.Id) (t : Typ) :
    ρ.Extends (ρ.bindTyp x t) :=
  ⟨List.suffix_refl _, suffix_bind _ _ _, List.suffix_refl _, List.suffix_refl _⟩

theorem extends_bindDef (ρ : VarEnv) (x y : IL.Id) : ρ.Extends (ρ.bindDef x y) :=
  ⟨List.suffix_refl _, List.suffix_refl _, suffix_bind _ _ _, List.suffix_refl _⟩

theorem extends_bindGram (ρ : VarEnv) (x : IL.Id) (g : Sym) :
    ρ.Extends (ρ.bindGram x g) :=
  ⟨List.suffix_refl _, List.suffix_refl _, List.suffix_refl _, suffix_bind _ _ _⟩

end VarEnv

/-- `Grows ρ r`: whatever scope `r` produces extends `ρ`.  Failure is vacuous,
which is what makes the combinators below total. -/
def Grows (ρ : VarEnv) (r : Res VarEnv) : Prop := ∀ σ, r = .ok σ → ρ.Extends σ

theorem grows_ok (ρ : VarEnv) : Grows ρ (.ok ρ) := by
  rintro σ h; cases h; rfl

theorem grows_ok_of {ρ σ : VarEnv} (h : ρ.Extends σ) : Grows ρ (.ok σ) := by
  rintro τ hτ; cases hτ; exact h

theorem grows_error (ρ : VarEnv) (e : Stuck) : Grows ρ (.error e) := by
  rintro σ h; exact absurd h (by simp)

theorem grows_bind {α : Type} {ρ : VarEnv} {r : Res α} {f : α → Res VarEnv}
    (hf : ∀ a, Grows ρ (f a)) : Grows ρ (r >>= f) := by
  rintro σ h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨a, _, ha⟩ := h
  exact hf a σ ha

theorem grows_bind_env {ρ : VarEnv} {r : Res VarEnv} {f : VarEnv → Res VarEnv}
    (hr : Grows ρ r) (hf : ∀ σ, Grows σ (f σ)) : Grows ρ (r >>= f) := by
  rintro τ h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨σ, hσ, hτ⟩ := h
  exact (hr σ hσ).trans (hf σ τ hτ)

theorem grows_assert {ρ : VarEnv} {c : Prop} [Decidable c] {r : Res VarEnv}
    (h : Grows ρ r) : Grows ρ (Res.assert c r) := by
  by_cases hc : c
  · simpa [Res.assert, hc] using h
  · simp only [Res.assert, hc, ite_false]; exact grows_error _ _

theorem grows_elimUndef {α : Type} {ρ : VarEnv} {r : Res α} {f : α → Res VarEnv}
    {g : Unit → Res VarEnv} (hf : ∀ a, Grows ρ (f a)) (hg : ∀ u, Grows ρ (g u)) :
    Grows ρ (Res.elimUndef r f g) := by
  cases r with
  | ok a => exact hf a
  | error e => cases e with
    | undef => exact hg ()
    | outOfFuel => exact grows_error _ _

/-- `Res.scan` only extends: the answer is one of the alternatives'
(`Res.scan_eq_ok`). -/
theorem grows_scan {ρ : VarEnv} {f : Nat → Res VarEnv} (hf : ∀ j, Grows ρ (f j))
    (k i : Nat) : Grows ρ (Res.scan f i k) := by
  intro σ h
  obtain ⟨j, -, -, hj⟩ := Res.scan_eq_ok k i h
  exact hf j σ hj

theorem grows_foldlM {α : Type} {f : VarEnv → α → Res VarEnv}
    (hf : ∀ σ a, Grows σ (f σ a)) : ∀ (xs : List α) (ρ : VarEnv), Grows ρ (xs.foldlM f ρ)
  | [], ρ => by
      show Grows ρ (pure ρ)
      exact grows_ok ρ
  | x :: xs, ρ => by
      simp only [List.foldlM_cons]
      exact grows_bind_env (hf ρ x) fun σ => grows_foldlM hf xs σ

theorem grows_matchTypV (env : Env) (ρ : VarEnv) (pat t : Typ) :
    Grows ρ (matchTypV env ρ pat t) := by
  unfold matchTypV
  split
  · split
    · split
      · exact grows_ok ρ
      · exact grows_error _ _
    · split
      · split
        · exact grows_ok ρ
        · exact grows_error _ _
      · exact grows_ok_of (VarEnv.extends_bindTyp _ _ _)
  · split
    · exact grows_ok ρ
    · exact grows_error _ _

theorem grows_matchSymV (env : Env) (ρ : VarEnv) (pat g : Sym) :
    Grows ρ (matchSymV env ρ pat g) := by
  unfold matchSymV
  split
  · split
    · split
      · exact grows_ok ρ
      · exact grows_error _ _
    · split
      · split
        · exact grows_ok ρ
        · exact grows_error _ _
      · exact grows_ok_of (VarEnv.extends_bindGram _ _ _)
  · split
    · exact grows_ok ρ
    · exact grows_error _ _

/-- Every scope-producing member of the mutual block only extends its input
scope, at a fixed fuel level. -/
structure GrowsAt (n : Nat) : Prop where
  /-- `matchExp` only extends. -/
  matchExp : ∀ env ρ e v, Grows ρ (matchExp n env ρ e v)
  /-- `matchDefault` only extends. -/
  matchDefault : ∀ env ρ e v, Grows ρ (matchDefault n env ρ e v)
  /-- `matchExps` only extends. -/
  matchExps : ∀ env ρ es vs, Grows ρ (matchExps n env ρ es vs)
  /-- `matchExpFields` only extends. -/
  matchExpFields : ∀ env ρ fs gs, Grows ρ (matchExpFields n env ρ fs gs)
  /-- `matchIterE` only extends. -/
  matchIterE : ∀ env ρ e it ds v, Grows ρ (matchIterE n env ρ e it ds v)
  /-- `matchIterList` only extends. -/
  matchIterList : ∀ env ρ e ds ido vs, Grows ρ (matchIterList n env ρ e ds ido vs)
  /-- `matchArg` only extends. -/
  matchArg : ∀ env ρ a w, Grows ρ (matchArg n env ρ a w)
  /-- `matchArgs` only extends. -/
  matchArgs : ∀ env ρ as ws, Grows ρ (matchArgs n env ρ as ws)
  /-- `premHolds` only extends. -/
  premHolds : ∀ env ρ pr, Grows ρ (premHolds n env ρ pr)
  /-- `premsHold` only extends. -/
  premsHold : ∀ env ρ prs, Grows ρ (premsHold n env ρ prs)
  /-- `premIter` only extends. -/
  premIter : ∀ env ρ pr it ds, Grows ρ (premIter n env ρ pr it ds)
  /-- `premRounds` only extends. -/
  premRounds : ∀ env ρ pr xvs ido k, Grows ρ (premRounds n env ρ pr xvs ido k)

/-- Base case: with no fuel nothing succeeds. -/
theorem growsAt_zero : GrowsAt 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
      | (simp only [matchExp]; exact grows_error _ _)
      | (simp only [matchDefault]; exact grows_error _ _)
      | (simp only [matchExps]; exact grows_error _ _)
      | (simp only [matchExpFields]; exact grows_error _ _)
      | (simp only [matchIterE]; exact grows_error _ _)
      | (simp only [matchIterList]; exact grows_error _ _)
      | (simp only [matchArg]; exact grows_error _ _)
      | (simp only [matchArgs]; exact grows_error _ _)
      | (simp only [premHolds]; exact grows_error _ _)
      | (simp only [premsHold]; exact grows_error _ _)
      | (simp only [premIter]; exact grows_error _ _)
      | (simp only [premRounds]; exact grows_error _ _)

/-- The inductive step, by structural recursion on the fuel. -/
theorem growsAt_succ : ∀ n, GrowsAt n
  | 0 => growsAt_zero
  | n + 1 => by
      have ih := growsAt_succ n
      have hm := ih.matchExp
      have hmd := ih.matchDefault
      have hms := ih.matchExps
      have hmf := ih.matchExpFields
      have hmi := ih.matchIterE
      have hmil := ih.matchIterList
      have hma := ih.matchArg
      have hmas := ih.matchArgs
      have hph := ih.premHolds
      have hphs := ih.premsHold
      have hpi := ih.premIter
      have hpr := ih.premRounds
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- `matchExp`
      · intro env ρ e v
        cases e
        case varE x =>
          simp only [matchExp]
          split
          · split
            · exact grows_ok ρ
            · exact grows_error _ _
          · exact grows_ok_of (VarEnv.extends_bindVal _ _ _)
        case unE op t e =>
          cases op <;> cases v <;> simp only [matchExp] <;>
            first
              | exact hmd _ _ _ _
              | exact grows_assert (hm _ _ _ _)
              | exact grows_assert (grows_bind fun _ => hm _ _ _ _)
        case tupE es =>
          simp only [matchExp]; exact grows_bind fun _ => hms _ _ _ _
        case projE e i =>
          simp only [matchExp]
          split
          · exact hm _ _ _ _
          · exact hmd _ _ _ _
        case caseE op e =>
          simp only [matchExp]
          exact grows_bind fun _ => grows_assert (hm _ _ _ _)
        case uncaseE e op => simp only [matchExp]; exact hm _ _ _ _
        case optE eo =>
          cases eo <;> simp only [matchExp] <;>
            first
              | exact grows_assert (grows_ok ρ)
              | exact grows_bind fun _ => grows_bind fun _ => hm _ _ _ _
        case strE fs =>
          simp only [matchExp]; exact grows_bind fun _ => hmf _ _ _ _
        case listE es =>
          simp only [matchExp]; exact grows_bind fun _ => hms _ _ _ _
        case catE e₁ e₂ =>
          simp only [matchExp]
          refine grows_bind fun vs => grows_elimUndef (fun k => ?_) (fun _ => ?_)
          · exact grows_assert (grows_bind_env (hm _ _ _ _) fun σ => hm _ _ _ _)
          · refine grows_elimUndef (fun k => ?_) (fun _ => ?_)
            · exact grows_assert (grows_bind_env (hm _ _ _ _) fun σ => hm _ _ _ _)
            · exact grows_scan (fun _ => grows_bind_env (hm _ _ _ _) fun σ => hm _ _ _ _) _ _
        case iterE e₀ it =>
          cases it with
          | mk i ds => simp only [matchExp]; exact hmi _ _ _ _ _ _
        case cvtE e t₁ t₂ =>
          cases v <;> simp only [matchExp] <;>
            first
              | exact hmd _ _ _ _
              | exact grows_bind fun _ => hm _ _ _ _
        case subE e t₁ t₂ => simp only [matchExp]; exact hm _ _ _ _
        case boolE b => simp only [matchExp]; exact grows_assert (grows_ok ρ)
        case numE m => simp only [matchExp]; exact grows_assert (grows_ok ρ)
        case textE t => simp only [matchExp]; exact grows_assert (grows_ok ρ)
        all_goals (simp only [matchExp]; exact hmd _ _ _ _)
      -- `matchDefault`
      · intro env ρ e v
        simp only [matchDefault]
        exact grows_bind fun _ => grows_assert (grows_ok ρ)
      -- `matchExps`
      · intro env ρ es vs
        cases es with
        | nil =>
            cases vs <;> simp only [matchExps] <;>
              first | exact grows_ok ρ | exact grows_error _ _
        | cons e es =>
            cases vs with
            | nil => simp only [matchExps]; exact grows_error _ _
            | cons v vs =>
                simp only [matchExps]
                exact grows_bind_env (hm _ _ _ _) fun σ => hms _ _ _ _
      -- `matchExpFields`
      · intro env ρ fs gs
        cases fs with
        | nil =>
            cases gs <;> simp only [matchExpFields] <;>
              first | exact grows_ok ρ | exact grows_error _ _
        | cons f fs =>
            cases f with
            | mk a e =>
                cases gs with
                | nil => simp only [matchExpFields]; exact grows_error _ _
                | cons g gs =>
                    simp only [matchExpFields]
                    exact grows_assert (grows_bind_env (hm _ _ _ _) fun σ => hmf _ _ _ _)
      -- `matchIterE`
      · intro env ρ e it ds v
        cases it with
        | opt =>
            simp only [matchIterE]
            refine grows_bind fun o => ?_
            cases o with
            | none => exact hms _ _ _ _
            | some w => exact grows_bind fun _ => grows_bind fun _ => hms _ _ _ _
        | list =>
            simp only [matchIterE]; exact grows_bind fun _ => hmil _ _ _ _ _ _
        | list1 =>
            simp only [matchIterE]
            exact grows_bind fun _ => grows_assert (hmil _ _ _ _ _ _)
        | listN eₙ x =>
            simp only [matchIterE]
            exact grows_bind fun _ => grows_bind_env (hm _ _ _ _) fun σ => hmil _ _ _ _ _ _
      -- `matchIterList`
      · intro env ρ e ds ido vs
        simp only [matchIterList]
        exact grows_bind fun _ => hms _ _ _ _
      -- `matchArg`
      · intro env ρ a w
        cases a <;> cases w <;> simp only [matchArg] <;>
          first
            | (split
               · exact hm _ _ _ _
               · exact grows_error _ _)
            | exact grows_matchTypV _ _ _ _
            | exact grows_matchSymV _ _ _ _
            | exact grows_ok_of (VarEnv.extends_bindDef _ _ _)
            | exact grows_error _ _
      -- `matchArgs`
      · intro env ρ as ws
        cases as with
        | nil =>
            cases ws <;> simp only [matchArgs] <;>
              first | exact grows_ok ρ | exact grows_error _ _
        | cons a as =>
            cases ws with
            | nil => simp only [matchArgs]; exact grows_error _ _
            | cons w ws =>
                simp only [matchArgs]
                exact grows_bind_env (hma _ _ _ _) fun σ => hmas _ _ _ _
      -- `premHolds`
      · intro env ρ pr
        cases pr with
        | ifPr e =>
            simp only [premHolds]
            exact grows_bind fun _ => grows_assert (grows_ok ρ)
        | elsePr => simp only [premHolds]; exact grows_ok ρ
        | letPr e₁ e₂ =>
            simp only [premHolds]
            exact grows_bind fun _ => hm _ _ _ _
        | rulePr x as op e =>
            simp only [premHolds]
            refine grows_bind fun _ => grows_bind fun _ => ?_
            split
            · exact grows_ok ρ
            · exact grows_error _ _
        | iterPr pr it =>
            cases it with
            | mk i ds => simp only [premHolds]; exact hpi _ _ _ _ _
      -- `premsHold`
      · intro env ρ prs
        simp only [premsHold]
        exact grows_foldlM (fun σ pr => hph _ σ pr) prs ρ
      -- `premIter`
      · intro env ρ pr it ds
        cases it with
        | opt =>
            simp only [premIter]
            refine grows_bind fun _ => grows_assert (grows_bind fun _ => ?_)
            split
            · exact grows_ok ρ
            · split
              · exact grows_bind fun _ => grows_ok ρ
              · exact grows_error _ _
        | list =>
            simp only [premIter]
            exact grows_bind fun _ =>
              grows_assert (grows_bind fun _ => hpr _ _ _ _ _ _)
        | list1 =>
            simp only [premIter]
            exact grows_bind fun _ =>
              grows_assert (grows_bind fun _ => grows_assert (hpr _ _ _ _ _ _))
        | listN eₙ x =>
            simp only [premIter]
            exact grows_bind fun _ => grows_bind fun _ => grows_bind fun _ => hpr _ _ _ _ _ _
      -- `premRounds`
      · intro env ρ pr xvs ido k
        simp only [premRounds]
        exact grows_bind fun _ => grows_assert (grows_bind fun _ => grows_ok ρ)

/-- **A successful match only extends the scope.**  Together with
`Map.find?`'s search from the front, this says that everything bound before
the match is still visible, with the same value unless the pattern rebound
it. -/
theorem matchExp_extends {n : Nat} {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h : matchExp n env ρ e v = .ok ρ') : ρ.Extends ρ' :=
  (growsAt_succ n).matchExp env ρ e v ρ' h

/-- The relational form of `matchExp_extends`. -/
theorem MatchExp.extends {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h : MatchExp env ρ e v ρ') : ρ.Extends ρ' := by
  obtain ⟨n, h⟩ := h; exact matchExp_extends h

/-- A premise that holds only extends the scope. -/
theorem premHolds_extends {n : Nat} {env : Env} {ρ ρ' : VarEnv} {pr : Prem}
    (h : premHolds n env ρ pr = .ok ρ') : ρ.Extends ρ' :=
  (growsAt_succ n).premHolds env ρ pr ρ' h

/-- The relational form of `premHolds_extends`. -/
theorem PremHolds.extends {env : Env} {ρ ρ' : VarEnv} {pr : Prem}
    (h : PremHolds env ρ pr ρ') : ρ.Extends ρ' := by
  obtain ⟨n, h⟩ := h; exact premHolds_extends h

/-- A list of premises that all hold only extends the scope. -/
theorem premsHold_extends {n : Nat} {env : Env} {ρ ρ' : VarEnv} {prs : List Prem}
    (h : premsHold n env ρ prs = .ok ρ') : ρ.Extends ρ' :=
  (growsAt_succ n).premsHold env ρ prs ρ' h

/-- Matching an argument list only extends the scope. -/
theorem matchArgs_extends {n : Nat} {env : Env} {ρ ρ' : VarEnv} {as : List Arg}
    {ws : List ArgV} (h : matchArgs n env ρ as ws = .ok ρ') : ρ.Extends ρ' :=
  (growsAt_succ n).matchArgs env ρ as ws ρ' h


/-! ## Examples

Small end-to-end checks that the evaluator computes and that the
compositionality lemmas are usable.  `evalExp` is defined by well-founded
recursion on its fuel, so it does not reduce by `rfl`; these go through the
equation lemmas instead, which is also what a proof about a concrete script
would do. -/

namespace Examples

set_option maxRecDepth 10000

/-- `1 + 2` denotes `3`. -/
example : evalExp 3 Env.empty VarEnv.empty
    (.binE .addOp (.numT .natT) (.numE (.natN 1)) (.numE (.natN 2)))
      = .ok (.num (.natN 3)) := by
  simp [evalExp, boolShort, binValues, Num.bin]

/-- An injection, through `evalExp_caseE_iff`. -/
example : EvalExp Env.empty VarEnv.empty (.caseE "X" (.boolE true))
    (.case "X" (.bool true)) := by
  rw [evalExp_caseE_iff]
  exact ⟨.bool true, evalExp_boolE_iff.mpr rfl, rfl⟩

/-- A variable denotes what the scope binds it to. -/
example : EvalExp Env.empty (VarEnv.empty.bindVal "x" (.num (.natN 4)))
    (.varE "x") (.num (.natN 4)) := by
  rw [evalExp_varE_iff]; rfl

/-- `UncaseE` undoes `CaseE` (`eval.ml:430`). -/
example : EvalExp Env.empty VarEnv.empty
    (.uncaseE (.caseE "X" (.boolE true)) "X") (.bool true) := by
  rw [evalExp_uncaseE_iff, evalExp_caseE_iff]
  exact ⟨.bool true, evalExp_boolE_iff.mpr rfl, rfl⟩

/-- Concatenation of two singleton lists. -/
example : EvalExp Env.empty VarEnv.empty
    (.catE (.listE [.numE (.natN 1)]) (.listE [.numE (.natN 2)]))
    (.list [.num (.natN 1), .num (.natN 2)]) := by
  rw [evalExp_catE_iff]
  refine ⟨.list [.num (.natN 1)], .list [.num (.natN 2)], ⟨3, ?_⟩, ⟨3, ?_⟩, rfl⟩
  · simp [evalExp, evalExps]
  · simp [evalExp, evalExps]

/-- A variable pattern binds. -/
example : MatchExp Env.empty VarEnv.empty (.varE "x") (.num (.natN 4))
    (VarEnv.empty.bindVal "x" (.num (.natN 4))) :=
  ⟨1, by simp [matchExp, VarEnv.findVal?, VarEnv.empty, Map.empty, Map.find?]⟩

/-- A one-rule relation: `Zero` relates nothing but the numeral `0`. -/
def exRel : Def := .relD "Zero" [] "|-" .boolT [.ruleD "z" [] "|-" (.numE (.natN 0)) []]

/-- Its only rule fires, so `0` is derivable. -/
example : derives 4 (envOfScript [exRel]) "Zero" "|-" [] (.num (.natN 0)) = true := by
  simp [derives, anyRule, exRel, envOfScript, envOfDefs, envOfDef, Env.bindRel,
    Env.findRel?, Map.find?, Map.bind, Env.empty, Map.empty, matchExp, premsHold,
    bindParams, VarEnv.empty, List.foldlM, Except.isOk, Except.toBool]
  rfl

end Examples

/-! ## Scope: deviations from `eval.ml`, and what is not proved

### Deviations, and why each one is forced

* **Three outcomes, and `assume_coherent_matches = false`.**  `eval.ml:16`
  defaults that flag to `true`, which lets a later clause's definite answer
  override an earlier clause that could not be decided
  (`eval.ml:656-661,666-671`).  We take the other branch (`eval.ml:657,667`),
  so `outOfFuel` propagates.  Without this, monotonicity in fuel is false.
  Holding every other deviation fixed, this choice answers no more often than
  `eval.ml` at the flag's default `true`; against the `false` branch even
  that fails, because four of `eval.ml`'s `Ok None` outcomes are
  `.error .undef` here and therefore let `tryClauses` skip a clause.  The
  module docstring tabulates the four.
* **`DefA` binds pattern ↦ actual.**  `eval.ml:1131` is
  `Subst.add_defid s id1 id2` with the actual argument first, the opposite of
  every other clause of `match_arg`.  `matchArg` documents why that is a bug
  and what the corpus shows; we bind the other way round.
* **Boolean short circuits are left-biased only.**  `Xl.Bool.bin_partial`
  (`spectec/src/xl/bool.ml:36-47`) also settles `_ ∧ false` from the *right*
  operand.  Keeping that half would make `undef ∧ e₂` answer `undef` at small
  fuel and `false` once `e₂` reduces, so monotonicity would fail; see
  `boolShort`.
* **`Num.bin_partial`'s algebraic clauses are dropped** (`num.ml:256-274`),
  for the same reason; see `binValues`.
* **The body of an iteration is evaluated per round, not once up front.**
  `eval.ml:374` reduces the body before binding the iteration variables,
  which it can do because a stuck expression is still an expression.  A value
  semantics cannot; see `evalIterE`.
* **`RulePr` is decided rather than deferred.**  `eval.ml:687` returns
  `Ok None` for every relational premise.  `premHolds` instead evaluates the
  asserted instance and consults `derives`, reporting `false` as `outOfFuel`
  so that the clause is never skipped — which reproduces `eval.ml:687`'s
  effect on clause selection while making relations usable.
* **Types are compared, not unified.**  `matchTypV` and `matchSymV` keep
  `match_typ`'s and `match_sym`'s pattern-variable clauses and replace the
  structural recursion (`eval.ml:826-850`, `eval.ml:1113-1117`) by syntactic
  equality, because decomposing a type needs `reduce_typ` (`eval.ml:107`),
  which belongs to `Sem/Type.lean`.
* **`eta_tup_exp` and the irrefutable one-case pattern are not transcribed**
  (`eval.ml:920-922,959-963`): both read the `typ` note that a `--ast` stream
  drops.

### Deliberately out of scope

* **An iterated premise binds nothing outwards.**  `eval.ml:699-795` splits
  an `IterPr`'s domains into inward- and outward-flowing ones and
  reverse-matches the outward ones (`eval.ml:733-738,779-790`).  A domain is
  outward exactly when the premise is a `LetPr` whose quantifiers bind it
  (`eval.ml:705`), and no pinned stream contains a `LetPr`, so on the corpus
  `is_let_bound` is identically false and `premIter` transcribes the branch
  that is actually taken.  The general case is not implemented.
* **Grammars.**  `GramD`, `Sym` and `ProdD` get an `EncRel (List UInt8) Value`
  denotation in `Sem/Grammar.lean`; this file only carries `GramA` arguments
  and matches them.
* **Types as predicates.**  `HasTyp` and the preservation theorem are
  `Sem/Type.lean` (`docs/projects/spectec/README.md`, step 4).

### The metatheory that is here

1. **Monotonicity in fuel** — `monoAt_of_le`, one structural induction over
   the fuel covering all 29 members of the mutual block, with the per-member
   corollaries `evalExp_ok_of_le` … `derives_of_le`.
2. **Determinism** — `EvalExp.unique`, `MatchExp.unique`, `CallDef.unique`,
   `PremHolds.unique`, and the same statement in `EncRel` vocabulary as
   `evalRel_deterministic : (evalRel env ρ).Deterministic`.  The two
   neighbouring `EncRel` properties are settled too: `evalRel_surjective`
   (every value is denoted by its literal `lit`) holds, and
   `not_evalRel_total` (not every expression denotes) is the one that fails.
3. **Compositionality** — `evalExp_*_iff`, one lemma per `Exp` constructor
   (30, counting `OptE none` and `OptE (some _)` separately), stating the
   denotation of the whole in terms of the denotations of its parts.
4. **Environment weakening** — `matchExp_extends`, `premHolds_extends`,
   `premsHold_extends` and `matchArgs_extends`: a successful match or premise
   only ever prepends bindings, in all four namespaces
   (`VarEnv.Extends`).  This is the first half of item 4 of the plan.

### The metatheory that is *not* here

The **substitution / free-variable lemma** — "`evalExp n env ρ e` depends only
on the restriction of `ρ` to `Silmaril.SpecTec.IL.freeExp e`" — is **not**
proved.  Precisely, the following statement is open in this file:

> for all `n`, `env`, `e` and `ρ₁ ρ₂` such that
> `∀ x ∈ (freeExp e).varid, ρ₁.findVal? x = ρ₂.findVal? x` and likewise for
> `typid`, `defid` and `gramid`, `evalExp n env ρ₁ e = evalExp n env ρ₂ e`.

It needs a third induction over the whole mutual block, with a side condition
per member relating `freeExp`, `freePrem`, `freeArg` and `boundDom` to the
scope each clause builds — in particular an `IterE` extends the scope by its
domain variables, so the invariant has to be stated modulo
`Free.boundDoms`.  `matchExp_extends` above is the part of item 4 that is
proved; nothing weaker is claimed under a stronger name.
-/


/-- A successful argument match, at some fuel level: the relation
`matchArgs` computes (`spectec/src/il/eval.ml:1121-1135`). -/
def MatchArgs (env : Env) (ρ : VarEnv) (pats : List Arg) (ws : List ArgV)
    (ρ' : VarEnv) : Prop :=
  ∃ n, matchArgs n env ρ pats ws = .ok ρ'

/-! ## Shared evaluation lemmas

These were discovered independently in `Sem/Grammar.lean` and
`Equiv/Numerics.lean`; they belong here, where `premsHold` and `evalExp` are
defined. -/

/-- `premsHold` of no premises. -/
theorem premsHold_nil_eq (env : Env) (ρ : VarEnv) (n : Nat) :
    premsHold (n + 1) env ρ [] = .ok ρ := by
  simp only [premsHold, List.foldlM_nil]; rfl

/-- No premises bind nothing. -/
theorem premsHold_nil {env : Env} {ρ : VarEnv} : PremsHold env ρ [] ρ :=
  ⟨1, premsHold_nil_eq env ρ 0⟩

/-- `premsHold` of a single premise. -/
theorem premsHold_singleton_eq (env : Env) (ρ : VarEnv) (n : Nat) (p : Prem) :
    premsHold (n + 1) env ρ [p] = premHolds n env ρ p := by
  simp [premsHold, List.foldlM_cons, List.foldlM_nil]

/-- A single `IfPr` side condition holds when its expression is `true`
(`spectec/src/il/eval.ml:688-693`). -/
theorem premsHold_ifPr {env : Env} {ρ : VarEnv} {e : Exp}
    (h : EvalExp env ρ e (.bool true)) : PremsHold env ρ [.ifPr e] ρ := by
  obtain ⟨n, h⟩ := h
  refine ⟨n + 2, ?_⟩
  rw [premsHold_singleton_eq]
  simp [premHolds, h]

/-- A boolean conjunction, with the left-biased short circuit of
`boolShort` (`spectec/src/il/eval.ml:240-255`). -/
theorem evalExp_and {env : Env} {ρ : VarEnv} {t : OpTyp} {e₁ e₂ : Exp} {b₁ b₂ : Bool}
    (h₁ : EvalExp env ρ e₁ (.bool b₁)) (h₂ : EvalExp env ρ e₂ (.bool b₂)) :
    EvalExp env ρ (.binE .andOp t e₁ e₂) (.bool (b₁ && b₂)) := by
  cases b₁ with
  | false => exact evalExp_binE_iff.2 ⟨.bool false, h₁, Or.inl rfl⟩
  | true => exact evalExp_binE_iff.2 ⟨.bool true, h₁, Or.inr ⟨rfl, .bool b₂, h₂, rfl⟩⟩

/-- A boolean conjunction of two true conditions. -/
theorem evalExp_and_true {env : Env} {ρ : VarEnv} {t : OpTyp} {e₁ e₂ : Exp}
    (h₁ : EvalExp env ρ e₁ (.bool true)) (h₂ : EvalExp env ρ e₂ (.bool true)) :
    EvalExp env ρ (.binE .andOp t e₁ e₂) (.bool true) := by
  simpa using evalExp_and (t := t) h₁ h₂

end Silmaril.SpecTec.Sem
