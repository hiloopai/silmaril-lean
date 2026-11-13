module

public import Silmaril.Compiler.Core.Verified.ReturnLit.Defs
public import Silmaril.Compiler.Core.Source.PureLocal.Defs

/-! # Cerberus's guarded `int` operators

Cerberus elaborates `e₁ + e₂` (and `-`, `*`) on `int` operands to an `unseq` of the operands bound
to a tuple `(a, b)`, followed by the pure guard

```
case (a, b) of
| (Specified(x), Specified(y)) =>
    Specified(catch_exceptional_condition(int, op, conv_int(int, x), conv_int(int, y)))
| _ => undef(UB036_exceptional_condition)
```

`guard file a b p = some op` recognises the guard syntactically. With `int` operands
`Specified n₁`, `Specified n₂` bound to `a` and `b`:

* `guard_eval`: when `n₁ op n₂` is an `int`, the guard evaluates to `Specified (n₁ op n₂)`
  (`PureEval.Eval`, so a Core run by `Eval.sound` and a local run by `PureLocal.Eval.local`);
* `guard_fails`: otherwise its local run reaches the `catch_exceptional_condition` whose request
  is undefined behaviour `UB036_exceptional_condition`.

The Lir side computes `n₁ op n₂` on 64-bit words; the exit status agrees whenever Core does not
reach undefined behaviour.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Guard

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ConvInt (Pure IsInt intTy lookupFun)

/-- The operators of the fragment: those whose guard is `catch_exceptional_condition` alone. -/
def arith : IntOp → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- `conv_int(int, s)`: a call of std.core's `conv_int` (the guard of `*`) or the primitive
(the guards of `+` and `-`). -/
def convOf (file : File Codec.wireModel Unit Unit) (s : Sym) : Pure → Bool
  | .mk _ () (.call (.sym c) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
      .mk _ () (.sym s')]) =>
      decide (s'.key = s.key) &&
      (match lookupFun file c with
       | some d => ConvInt.convInt file d
       | none => false)
  | .mk _ () (.convInt (.signed .int) (.mk _ () (.sym s'))) => decide (s'.key = s.key)
  | _ => false

/-- The guard of a binary `int` operator over the operand tuple `(a, b)`. -/
def guard (file : File Codec.wireModel Unit Unit) (a b : Sym) : Pure → Option IntOp
  | .mk _ () (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym b')]))
      ((.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
          .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]),
        .mk _ () (.ctor .specified [.mk _ () (.catchExceptionalCondition (.signed .int) op p q)]))
        :: _)) =>
      if decide (a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧ y.key ≠ x.key) &&
          convOf file x p && convOf file y q && arith op then some op else none
  | _ => none

/-- The value of an operator of the fragment (`+` for the others, which no guard has). -/
def apply : IntOp → Int → Int → Int
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | _, x, y => x + y

theorem integerOp_arith {op : IntOp} (h : arith op = true) (x y : Int) :
    integerOp op x y = some (apply op x y) := by
  cases op <;> simp [arith] at h <;> rfl

/-! ## Environments -/

theorem lookup_pair_first {a b : Sym} {x y : Val} {env : Env} {s : Sym} (h : s.key = a.key) :
    (extendEnv [(a, x), (b, y)] env).lookup s = some x := by
  have : MapKey.key s = MapKey.key a := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [this, Finmap.lookup_insert]

theorem lookup_pair_second {a b : Sym} {x y : Val} {env : Env} {s : Sym} (h : s.key = b.key)
    (ne : b.key ≠ a.key) : (extendEnv [(a, x), (b, y)] env).lookup s = some y := by
  have hs : MapKey.key s ≠ MapKey.key a := by
    change s.key ≠ a.key
    rw [h]; exact ne
  have : MapKey.key s = MapKey.key b := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [Finmap.lookup_insert_of_ne _ hs, this, Finmap.lookup_insert]

/-! ## Evaluation -/

variable {file : Program} {tags : Mem.Concrete.Tags}

theorem convOf_eval {x : Sym} {p : Pure} (h : convOf file x p = true) {env : Env} {n : Int}
    (hn : IsInt n) (hx : env.lookup x = some (.object (.integer n))) :
    Eval file tags env (.inl p) (.inl (.object (.integer n))) := by
  unfold convOf at h
  split at h
  · rename_i _ c _ ann _ s'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs, hc⟩ := h
    split at hc
    · rename_i d hl
      have hs' : env.lookup s' = some (.object (.integer n)) := by
        rw [ReturnLit.lookup_key hs]; exact hx
      exact ConvInt.convInt_eval (ann := ann) hl hc hn (.cons .val (.cons (.sym hs') .nil))
    · cases hc
  · rename_i _ _ s'
    have hs' : env.lookup s' = some (.object (.integer n)) := by
      rw [ReturnLit.lookup_key (of_decide_eq_true h)]; exact hx
    obtain ⟨lo, hi⟩ := hn
    exact .convInt (.cons (.sym hs') .nil)
      (by simp [primitive, ConvInt.bounds_int, lo, hi, integer]; rfl)
  · cases h

/-- The operand values bound to `a` and `b`. -/
abbrev operands (a b : Sym) (n₁ n₂ : Int) (env : Env) : Env :=
  extendEnv [(a, .loaded (.specified (.integer n₁))), (b, .loaded (.specified (.integer n₂)))] env

theorem catchInt_ok {op : IntOp} (har : arith op = true) {n₁ n₂ : Int}
    (hr : IsInt (apply op n₁ n₂)) (tags : Mem.Concrete.Tags) :
    primitive (.catchInt (.signed .int) op) [.object (.integer n₁), .object (.integer n₂)] tags =
      .ok (.object (.integer (apply op n₁ n₂))) := by
  obtain ⟨lo, hi⟩ := hr
  simp [primitive, ConvInt.bounds_int, integerOp_arith har, lo, hi, integer]
  rfl

theorem catchInt_ub {op : IntOp} (har : arith op = true) {n₁ n₂ : Int}
    (hr : ¬ IsInt (apply op n₁ n₂)) (tags : Mem.Concrete.Tags) :
    primitive (.catchInt (.signed .int) op) [.object (.integer n₁), .object (.integer n₂)] tags =
      .error (.ub .unknown .UB036_exceptional_condition) := by
  simp only [IsInt, not_and_or, not_le] at hr
  simp [primitive, ConvInt.bounds_int, integerOp_arith har]
  rcases hr with hr | hr
  · simp [show ¬ (-2147483648 ≤ apply op n₁ n₂) by omega]; rfl
  · simp [show ¬ (apply op n₁ n₂ ≤ 2147483647) by omega]; rfl

/-- The pieces of a recognised guard. -/
theorem guard_parts {a b : Sym} {p : Pure} {op : IntOp} (h : guard file a b p = some op) :
    ∃ (ann ann₁ pa pb : List Annot) (a' b' : Sym) (bs : List (Pattern Sym × Pure)),
      p = .mk ann () (.case_ (.mk ann₁ () (.ctor .tuple [.mk pa () (.sym a'), .mk pb () (.sym b')]))
        bs) ∧ a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧ arith op = true ∧
      ∀ (env : Env) (n₁ n₂ : Int), IsInt n₁ → IsInt n₂ → ∃ (body : Pure) (q₁ q₂ : List Annot)
        (pp pq : Pure) (x y : Sym),
        selectCase (.tuple [.loaded (.specified (.integer n₁)), .loaded (.specified (.integer n₂))])
          bs = some ([(x, .object (.integer n₁)), (y, .object (.integer n₂))], body) ∧
        body = .mk q₁ () (.ctor .specified [.mk q₂ () (.catchExceptionalCondition (.signed .int) op
          pp pq)]) ∧
        ∀ tags, Eval file tags (extendEnv [(x, .object (.integer n₁)), (y, .object (.integer n₂))]
          env) (.inr [pp, pq]) (.inr [.object (.integer n₁), .object (.integer n₂)]) := by
  unfold guard at h
  split at h
  · rename_i ann ann₁ pa a' pb b' tann tx bs x bx ty sann y cy q₁ q₂ op' pp pq rest
    split at h
    · rename_i cond
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨⟨⟨⟨e1, e2, ne, ne'⟩, cp⟩, cq⟩, har⟩ := cond
      refine ⟨ann, ann₁, pa, pb, a', b', _, rfl, e1, e2, ne, har, ?_⟩
      intro env n₁ n₂ h₁ h₂
      refine ⟨_, q₁, q₂, pp, pq, x, y, by simp [selectCase, matchPattern, matchPatterns], rfl, ?_⟩
      intro tags
      exact .cons (convOf_eval cp h₁ (lookup_pair_first rfl))
        (.cons (convOf_eval cq h₂ (lookup_pair_second rfl ne')) .nil)
    · cases h
  · cases h

/-- **A guard in range** evaluates to `Specified (n₁ op n₂)`. -/
theorem guard_eval {a b : Sym} {p : Pure} {op : IntOp} (h : guard file a b p = some op)
    (env : Env) {n₁ n₂ : Int} (h₁ : IsInt n₁) (h₂ : IsInt n₂) (hr : IsInt (apply op n₁ n₂)) :
    Eval file tags (operands a b n₁ n₂ env) (.inl p)
      (.inl (.loaded (.specified (.integer (apply op n₁ n₂))))) := by
  obtain ⟨ann, ann₁, pa, pb, a', b', bs, rfl, e1, e2, ne, har, rest⟩ := guard_parts h
  obtain ⟨body, q₁, q₂, pp, pq, x, y, hsel, rfl, hargs⟩ := rest (operands a b n₁ n₂ env) n₁ n₂ h₁ h₂
  refine .case_ (.ctor (.cons (.sym (lookup_pair_first e1)) (.cons (.sym (lookup_pair_second e2 ne))
    .nil)) (by simp [primitive]; rfl)) hsel ?_
  exact .ctor (.cons (.catchInt (hargs tags) (catchInt_ok har hr tags)) .nil)
    (by simp [primitive]; rfl)

/-- **A guard out of range** runs, by local steps from any continuation, to the
`catch_exceptional_condition` whose request is undefined behaviour. -/
theorem guard_fails {labels : Labels} {a b : Sym} {p : Pure} {op : IntOp}
    (h : guard file a b p = some op) (env : Env) {n₁ n₂ : Int} (h₁ : IsInt n₁) (h₂ : IsInt n₂)
    (hr : ¬ IsInt (apply op n₁ n₂)) (wc : Bool) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ k', LocalReaches file labels wc ⟨.pureExpr p (operands a b n₁ n₂ env), k, m⟩
        ⟨.apply (.catchInt (.signed .int) op) [.object (.integer n₁), .object (.integer n₂)], k', m⟩ ∧
      requestAux file labels m
        (.apply (.catchInt (.signed .int) op) [.object (.integer n₁), .object (.integer n₂)]) k' wc =
        .end_ (.ub .unknown .UB036_exceptional_condition) := by
  obtain ⟨ann, ann₁, pa, pb, a', b', bs, rfl, e1, e2, ne, har, rest⟩ := guard_parts h
  let env₁ := operands a b n₁ n₂ env
  obtain ⟨body, q₁, q₂, pp, pq, x, y, hsel, rfl, hargs⟩ := rest env₁ n₁ n₂ h₁ h₂
  let env₂ := extendEnv [(x, .object (.integer n₁)), (y, .object (.integer n₂))] env₁
  let k₁ : List Frame := .arguments (.ctor .specified) [] [] env₂ :: k
  have scrut : Eval file (tagsOf file m) env₁
      (.inl (.mk ann₁ () (.ctor .tuple [.mk pa () (.sym a'), .mk pb () (.sym b')])))
      (.inl (.tuple [.loaded (.specified (.integer n₁)), .loaded (.specified (.integer n₂))])) :=
    .ctor (.cons (.sym (lookup_pair_first e1)) (.cons (.sym (lookup_pair_second e2 ne)) .nil))
      (by simp [primitive]; rfl)
  let CATCH : Pure := .mk q₂ () (.catchExceptionalCondition (.signed .int) op pp pq)
  refine ⟨k₁, ?_, ?_⟩
  · refine .head (.next (c' := .pureExpr (.mk ann₁ () (.ctor .tuple [.mk pa () (.sym a'),
        .mk pb () (.sym b')])) env₁) (k' := .pureCase bs env₁ :: k)
      (by simp [requestAux, awaitsScheduling, env₁]) (PureLocal.plain_pureExpr _ _)) ?_
    refine (PureLocal.eval_local file _ scrut _ m rfl).trans ?_
    refine .head (.next (c' := .pureExpr (.mk q₁ () (.ctor .specified [CATCH])) env₂) (k' := k)
      (by simp [requestAux, awaitsScheduling, hsel, CATCH, env₂]) (PureLocal.plain_pureExpr _ _)) ?_
    refine .head (.next (c' := .pureExpr CATCH env₂) (k' := k₁)
      (by simp [requestAux, awaitsScheduling, arguments, k₁]) (PureLocal.plain_pureExpr _ _)) ?_
    refine (PureLocal.arguments_local file (.catchInt (.signed .int) op) [pp, pq] env₂ k₁ m wc
      (by simp [requestAux, awaitsScheduling, CATCH])).trans ?_
    simpa using PureLocal.args_local file _ (hargs (tagsOf file m)) (.catchInt (.signed .int) op)
      [] k₁ m rfl (wc := wc) (labels := labels)
  · rw [PureLocal.requestAux_apply file (op := .catchInt (.signed .int) op) trivial,
      catchInt_ub har hr]

/-! ## Comparisons

Cerberus elaborates `e₁ == e₂` (and `<`, `<=`, `>`, `>=`) on `int` operands to the same
`unseq` of the operands, followed by the pure guard

```
case (a, b) of
| (Specified(x), Specified(y)) =>
    if conv_int(int, x) rel conv_int(int, y) then Specified(c₁) else Specified(c₂)
| _ => Unspecified(int)
```

(`c₁ = 1`, `c₂ = 0`; `!=` swaps them). No arm of a comparison is undefined. -/

/-- The relations of the fragment. -/
def rel : BinOp → Bool
  | .eq | .lt | .le | .gt | .ge => true
  | _ => false

/-- The truth of a relation on integers (equality for the operators that are no relation). -/
def holds : BinOp → Int → Int → Bool
  | .lt, x, y => decide (x < y)
  | .le, x, y => decide (x ≤ y)
  | .gt, x, y => decide (x > y)
  | .ge, x, y => decide (x ≥ y)
  | _, x, y => x == y

theorem integerBin_rel {r : BinOp} (h : rel r = true) (x y : Int) :
    integerBin r x y = some (boolean (holds r x y)) := by
  cases r <;> simp [rel] at h <;> rfl

/-- The guard of a comparison over the operand tuple `(a, b)`: the relation and the two
results. -/
def cmpGuard (file : File Codec.wireModel Unit Unit) (a b : Sym) : Pure → Option (BinOp × Int × Int)
  | .mk _ () (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym b')]))
      ((.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
          .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]),
        .mk _ () (.if_ (.mk _ () (.op r p q))
          (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer c₁)))]))
          (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer c₂)))]))))
        :: _)) =>
      if decide (a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧ y.key ≠ x.key) &&
          convOf file x p && convOf file y q && rel r &&
          decide (-2147483648 ≤ c₁ ∧ c₁ ≤ 2147483647 ∧ -2147483648 ≤ c₂ ∧ c₂ ≤ 2147483647) then
        some (r, c₁, c₂)
      else none
  | _ => none

/-- The value of a comparison. -/
def compare (r : BinOp) (c₁ c₂ : Int) (n₁ n₂ : Int) : Int :=
  if holds r n₁ n₂ then c₁ else c₂

theorem cmpGuard_int {a b : Sym} {p : Pure} {r : BinOp} {c₁ c₂ : Int}
    (h : cmpGuard file a b p = some (r, c₁, c₂)) : IsInt c₁ ∧ IsInt c₂ := by
  unfold cmpGuard at h
  split at h
  · split at h
    · rename_i cond
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨-, h₁, h₂, h₃, h₄⟩ := cond
      exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    · cases h
  · cases h

/-- **A comparison** evaluates to `Specified c₁` when the relation holds, `Specified c₂`
otherwise. -/
theorem cmpGuard_eval {a b : Sym} {p : Pure} {r : BinOp} {c₁ c₂ : Int}
    (h : cmpGuard file a b p = some (r, c₁, c₂))
    (env : Env) {n₁ n₂ : Int} (h₁ : IsInt n₁) (h₂ : IsInt n₂) :
    Eval file tags (operands a b n₁ n₂ env) (.inl p)
      (.inl (.loaded (.specified (.integer (compare r c₁ c₂ n₁ n₂))))) := by
  unfold cmpGuard at h
  split at h
  · split at h
    · rename_i cond
      cases h
      rename_i P0 P1 P2 a' P3 b' Q0 Q1 Q2 x tx Q3 Q4 y ty R0 R1 p q R2 R3 R4 R5 rest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨⟨⟨⟨⟨e1, e2, ne, ne'⟩, cp⟩, cq⟩, hr⟩, -⟩ := cond
      refine .case_ (.ctor (.cons (.sym (lookup_pair_first e1)) (.cons (.sym (lookup_pair_second e2 ne))
        .nil)) (by simp [primitive]; rfl)) (by simp [selectCase, matchPattern, matchPatterns]; exact ⟨rfl, rfl⟩) ?_
      have args : Eval file tags (extendEnv [(x, .object (.integer n₁)), (y, .object (.integer n₂))]
          (operands a b n₁ n₂ env)) (.inr [p, q]) (.inr [.object (.integer n₁), .object (.integer n₂)]) :=
        .cons (convOf_eval cp h₁ (lookup_pair_first rfl))
          (.cons (convOf_eval cq h₂ (lookup_pair_second rfl ne')) .nil)
      unfold compare
      cases hh : holds r n₁ n₂
      · refine .ifFalse (.op args ?_) (.ctor (.cons .val .nil) (by simp [primitive]; rfl))
        simp [primitive, integerBin_rel hr, hh, boolean]; rfl
      · refine .ifTrue (.op args ?_) (.ctor (.cons .val .nil) (by simp [primitive]; rfl))
        simp [primitive, integerBin_rel hr, hh, boolean]; rfl
    · cases h
  · cases h

end Silmaril.Compile.Core.Verified.Guard
