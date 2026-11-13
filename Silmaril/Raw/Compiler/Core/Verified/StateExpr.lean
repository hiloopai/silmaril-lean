module

public import Silmaril.Compiler.Core.Verified.Unary.Defs
public import Silmaril.Compiler.Core.Verified.ClosedEffSound.Defs
public import Silmaril.Compiler.Core.Verified.IntWrap.Defs
public import Silmaril.Compiler.Core.Verified.PtrDeref.Defs

/-! # `int` expressions over several locals

`IntExpr` reads one local; here an expression reads any number of `int` locals, each named by
its symbol's key (`Key`). `term file e = some t` recognises the same elaborations as
`IntExpr.term` (literals, reads `let weak p = pure(x) in load(int, p)`, the guarded `+`, `-`,
`*`, comparisons and the conditional operator), but a read of any symbol `x` is `.var x.key`
(also through the member designators of a struct wrapping one `int`, `IntWrap.desig`: `s.x`
reads the local `s`); it also recognises the unary `-` and `~` (`Unary`), which `close` turns into the subtractions
`0 - e` and `-1 - e`, and the bitwise `&`, `|`, `^` (`Bitwise`, `IntExpr.Term.bit`).
A comparison may also use an effectful two-arm `case` guard (`CmpCont`), as in
`while (ret < 10)`. `t.val σ` is the value with each local `q` holding `σ q`; `t.Ok σ`
says no intermediate value leaves `int`.

The memory fact a read needs is `Loc env m q n`: every symbol with key `q` points, in `env`, to
the slot of an `int` `n`. From a memory with `Loc` for every key `t` reads:

* `term_runs`: if `t.Ok σ`, local steps reach `Specified (t.val σ)` with read accesses only,
  over any continuation;
* `term_fails`: otherwise they reach undefined behaviour `UB036_exceptional_condition`.

`close ds t` replaces each read of `q` by the closed `IntExpr.Term` `ds q` (the expression the
local was last assigned): `(close ds t).val 0 = t.val (fun q => (ds q).val 0)`. The statement
fragment (`Verified/State.lean`) uses it to compile a sequence of assignments to one closed
expression that the existing Lir code (`IntExpr.exprOps`) computes at run time.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns taskFlag unseqTasks)
open Silmaril.Cerberus.Core.ArenaFail (Fails)
open ReturnLit (Eff lookup_key)
open LoadTask (Touched ReadTask)
open Locals (Slot)
open ConvInt (IsInt Pure)
open Cond (OneAnn)
open IntExpr (spec overflow unseq_pair guard_local requestAux_tuple_bind)

/-- The name of a local: its symbol's key. -/
abbrev Key := Digest × Nat

/-- `int` expressions over several locals. -/
inductive Term where
  | lit (n : Int)
  | var (q : Key)
  | bin (op : IntOp) (a b : Term)
  | cmp (r : BinOp) (c₁ c₂ : Int) (a b : Term)
  | cond (c a b : Term)
  /-- `-a` or `~a`. -/
  | un (u : Unary.Unop) (a : Term)
  /-- `a & b`, `a | b`, `a ^ b`. -/
  | bit (o : Bitwise.Op) (a b : Term)
  /-- Signed division/remainder with a positive literal divisor. -/
  | divpos (o : DivRem.Op) (d : DivRem.Divisor) (a : Term)

/-- The locals `t` reads. -/
def Term.vars : Term → List Key
  | .lit _ => []
  | .var q => [q]
  | .bin _ a b => a.vars ++ b.vars
  | .cmp _ _ _ a b => a.vars ++ b.vars
  | .cond c a b => c.vars ++ a.vars ++ b.vars
  | .un _ a => a.vars
  | .bit _ a b => a.vars ++ b.vars
  | .divpos _ _ a => a.vars

/-- The guard of `e₁ != e₂` (and of a negated relation): Cerberus negates the relation,
`if not(conv_int(int, x) rel conv_int(int, y)) then Specified(c₁) else Specified(c₂)`, which
is the comparison with its results swapped: `(rel, c₂, c₁)`. -/
def notGuard (file : File Codec.wireModel Unit Unit) (a b : Sym) : Pure → Option (BinOp × Int × Int)
  | .mk _ () (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym b')]))
      ((.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
          .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]),
        .mk _ () (.if_ (.mk _ () (.not (.mk _ () (.op r p q))))
          (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer c₁)))]))
          (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer c₂)))]))))
        :: _)) =>
      if decide (a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧ y.key ≠ x.key) &&
          Guard.convOf file x p && Guard.convOf file y q && Guard.rel r &&
          decide (-2147483648 ≤ c₁ ∧ c₁ ≤ 2147483647 ∧ -2147483648 ≤ c₂ ∧ c₂ ≤ 2147483647) then
        some (r, c₂, c₁)
      else none
  | _ => none

/-- The comparisons: `Guard.cmpGuard`, or a negated one (`notGuard`). -/
def cmpGuard' (file : File Codec.wireModel Unit Unit) (a b : Sym) (g : Pure) :
    Option (BinOp × Int × Int) :=
  match Guard.cmpGuard file a b g with
  | some x => some x
  | none => notGuard file a b g

theorem notGuard_int {file : File Codec.wireModel Unit Unit} {a b : Sym} {p : Pure} {r : BinOp}
    {c₁ c₂ : Int} (h : notGuard file a b p = some (r, c₁, c₂)) : IsInt c₁ ∧ IsInt c₂ := by
  unfold notGuard at h
  split at h
  · split at h
    · rename_i cond
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨-, h₁, h₂, h₃, h₄⟩ := cond
      exact ⟨⟨h₃, h₄⟩, ⟨h₁, h₂⟩⟩
    · cases h
  · cases h

theorem cmpGuard'_int {file : File Codec.wireModel Unit Unit} {a b : Sym} {p : Pure} {r : BinOp}
    {c₁ c₂ : Int} (h : cmpGuard' file a b p = some (r, c₁, c₂)) : IsInt c₁ ∧ IsInt c₂ := by
  unfold cmpGuard' at h
  split at h
  · rename_i x hx; cases h; exact Guard.cmpGuard_int hx
  · exact notGuard_int h

theorem notGuard_eval {file : Program} {tags : Mem.Concrete.Tags} {a b : Sym} {p : Pure} {r : BinOp}
    {c₁ c₂ : Int} (h : notGuard file a b p = some (r, c₁, c₂))
    (env : Env) {n₁ n₂ : Int} (h₁ : IsInt n₁) (h₂ : IsInt n₂) :
    Eval file tags (Guard.operands a b n₁ n₂ env) (.inl p)
      (.inl (.loaded (.specified (.integer (Guard.compare r c₁ c₂ n₁ n₂))))) := by
  unfold notGuard at h
  split at h
  · split at h
    · rename_i cond
      cases h
      rename_i P0 P1 P2 a' P3 b' Q0 Q1 Q2 x tx Q3 Q4 y ty R0 R1 R1' p q R2 R3 R4 R5 rest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨⟨⟨⟨⟨e1, e2, ne, ne'⟩, cp⟩, cq⟩, hr⟩, -⟩ := cond
      refine .case_ (.ctor (.cons (.sym (Guard.lookup_pair_first e1))
        (.cons (.sym (Guard.lookup_pair_second e2 ne)) .nil)) (by simp [primitive]; rfl))
        (by simp [selectCase, matchPattern, matchPatterns]; exact ⟨rfl, rfl⟩) ?_
      have args : Eval file tags (extendEnv [(x, .object (.integer n₁)), (y, .object (.integer n₂))]
          (Guard.operands a b n₁ n₂ env)) (.inr [p, q]) (.inr [.object (.integer n₁), .object (.integer n₂)]) :=
        .cons (Guard.convOf_eval cp h₁ (Guard.lookup_pair_first rfl))
          (.cons (Guard.convOf_eval cq h₂ (Guard.lookup_pair_second rfl ne')) .nil)
      unfold Guard.compare
      cases hh : Guard.holds r n₁ n₂
      · have hop : Eval file tags (extendEnv [(x, .object (.integer n₁)), (y, .object (.integer n₂))]
            (Guard.operands a b n₁ n₂ env)) (.inl (.mk R1' () (.op r p q))) (.inl .false) :=
          .op args (by simp [primitive, Guard.integerBin_rel hr, hh, boolean]; rfl)
        exact .ifTrue (.not (.cons hop .nil) (by simp [primitive]; rfl))
          (.ctor (.cons .val .nil) (by simp [primitive]; rfl))
      · have hop : Eval file tags (extendEnv [(x, .object (.integer n₁)), (y, .object (.integer n₂))]
            (Guard.operands a b n₁ n₂ env)) (.inl (.mk R1' () (.op r p q))) (.inl .true) :=
          .op args (by simp [primitive, Guard.integerBin_rel hr, hh, boolean]; rfl)
        exact .ifFalse (.not (.cons hop .nil) (by simp [primitive]; rfl))
          (.ctor (.cons .val .nil) (by simp [primitive]; rfl))
    · cases h
  · cases h

theorem cmpGuard'_eval {file : Program} {tags : Mem.Concrete.Tags} {a b : Sym} {p : Pure} {r : BinOp}
    {c₁ c₂ : Int} (h : cmpGuard' file a b p = some (r, c₁, c₂))
    (env : Env) {n₁ n₂ : Int} (h₁ : IsInt n₁) (h₂ : IsInt n₂) :
    Eval file tags (Guard.operands a b n₁ n₂ env) (.inl p)
      (.inl (.loaded (.specified (.integer (Guard.compare r c₁ c₂ n₁ n₂))))) := by
  unfold cmpGuard' at h
  split at h
  · rename_i x hx; cases h; exact Guard.cmpGuard_eval hx env h₁ h₂
  · exact notGuard_eval h env h₁ h₂

/-- What a pointer local holds, as far as the statement machine knows: the null pointer, or the
address of the `int` local of the symbol `x` (named by its key). -/
inductive PtsTo where
  | null
  | addr (x : Sym)

/-- The value of the pointer test `r == NULL` for a pointer local holding the target. -/
def PtsTo.test : PtsTo → Int
  | .null => 1
  | .addr _ => 0

/-- The key a read designator names: a local's own symbol (or a member of a struct wrapping one
`int`, `IntWrap.desig`), or the target `q` of a pointer local `r` dereferenced as `*r` or
`r[0]` (`PtrDeref.derefOf`) when `pts r = some (.addr x)`, `q = x.key`. -/
def readKey (file : File Codec.wireModel Unit Unit) (pts : Key → Option PtsTo) (d : Eff) :
    Option Key :=
  match IntWrap.desig file d with
  | some x => some x.key
  | none => match PtrDeref.derefOf d with
    | some r => match pts r.key with
      | some (.addr x) => some x.key
      | _ => none
    | none => none

theorem readKey_inv {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {d : Eff}
    {q : Key} (h : readKey file pts d = some q) :
    (∃ x, IntWrap.desig file d = some x ∧ x.key = q) ∨
      ∃ r x, PtrDeref.derefOf d = some r ∧ pts r.key = some (.addr x) ∧ x.key = q := by
  unfold readKey at h
  split at h
  · rename_i x hx; cases h; exact .inl ⟨x, hx, rfl⟩
  · split at h
    · rename_i r hr
      split at h
      · rename_i x hq; cases h; exact .inr ⟨r, x, hr, hq, rfl⟩
      · cases h
    · cases h

theorem readKey_noCall {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {d : Eff}
    {q : Key} (h : readKey file pts d = some q) : hasCCall d = false := by
  rcases readKey_inv h with ⟨x, hx, -⟩ | ⟨r, -, hr, -⟩
  · exact IntWrap.desig_noCall hx
  · exact PtrDeref.derefOf_noCall hr

/-- The literal a pointer local used as a test denotes: `r == NULL` is `0` when `r` holds the
address of a local, `1` when it holds the null pointer (`pts`). -/
def nullLit (pts : Key → Option PtsTo) (e : Eff) : Option Int :=
  match PtrDeref.nullTestOf e with
  | some r => (pts r.key).map PtsTo.test
  | none => none

/-- A closed expression that folds to an `int` (`ClosedEff.lit`), or a pointer test (`nullLit`). -/
def litOf (file : File Codec.wireModel Unit Unit) (pts : Key → Option PtsTo) (e : Eff) : Option Int :=
  match ClosedEff.lit file e with
  | some n => some n
  | none => nullLit pts e

theorem litOf_cases {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {c : Int}
    (h : litOf file pts e = some c) :
    ClosedEff.lit file e = some c ∨
      ∃ r t, PtrDeref.nullTestOf e = some r ∧ pts r.key = some t ∧ c = t.test := by
  unfold litOf at h
  split at h
  · rename_i n hn; cases h; exact .inl hn
  · unfold nullLit at h
    split at h
    · rename_i r hr
      cases ht : pts r.key with
      | none => simp [ht] at h
      | some t => simp only [ht, Option.map_some, Option.some.injEq] at h; exact .inr ⟨r, t, hr, ht, h.symm⟩
    · cases h

theorem litOf_none {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff}
    (h : litOf file pts e = none) : ClosedEff.lit file e = none := by
  unfold litOf at h
  split at h
  · cases h
  · assumption

/-- The recogniser, dereferencing the pointer locals `pts`. A closed expression that folds to an `int` (`ClosedEff.lit`: constants
of any integer type, casts, `/`, `%`, shifts, comparisons at wider types) is the literal it
denotes; otherwise the shapes below. -/
def termP (file : File Codec.wireModel Unit Unit) (pts : Key → Option PtsTo) (e : Eff) : Option Term :=
  match litOf file pts e with
  | some n => some (.lit n)
  | none => match e with
  | .mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n)))))) =>
      if -2147483648 ≤ n ∧ n ≤ 2147483647 then some (.lit n) else none
  | .mk _ (.wseq (.mk _ (.base (some p, _))) d
      (.mk _ (.action (.mk .pos (.mk _ _ (.load
        (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
        (.mk _ () (.sym p')) .na)))))) =>
      match readKey file pts d with
      | some q => if p'.key = p.key then some (.var q) else none
      | none => none
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [e₁, e₂])) (.mk _ (.pure g))) =>
      match termP file pts e₁, termP file pts e₂ with
      | some t₁, some t₂ =>
        match Guard.guard file a b g, cmpGuard' file a b g with
        | some op, _ => some (.bin op t₁ t₂)
        | none, some (r, c₁, c₂) => some (.cmp r c₁ c₂ t₁ t₂)
        | none, none => match Bitwise.guard file a b g with
          | some o => some (.bit o t₁ t₂)
          | none => match DivRem.guard file a b g, t₂ with
            | some o, .lit n => match DivRem.divisor? n with
              | some d => some (.divpos o d t₁)
              | none => none
            | _, _ => none
      | _, _ => none
  | .mk _ (.sseq (.mk _ (.base (some c, _))) ec
      (.mk _ (.case_ (.mk _ () (.sym c'))
        [(.mk _ (.ctor .specified [.mk _ (.base (some z, _))]),
          .mk _ (.if_ (.mk _ () (.op .eq (.mk _ () (.sym z')) (.mk _ () (.val (.object (.integer 0))))))
            (.mk _ (.sseq (.mk _ (.base (some u, _))) ea
              (.mk _ (.pure (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _
                (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')]))))))
            (.mk _ (.sseq (.mk _ (.base (some w, _))) eb
              (.mk _ (.pure (.mk _ () (.call (.sym s') [.mk _ () (.val (.ctype (.mk _
                (.basic (.integer (.signed .int)))))), .mk _ () (.sym w')])))))))),
         (.mk _ (.ctor .unspecified _), .mk _ (.pure _))]))) =>
      if c'.key = c.key ∧ z'.key = z.key ∧ u'.key = u.key ∧ w'.key = w.key ∧
          ConvInt.isConvLoadedInt file s = true ∧ ConvInt.isConvLoadedInt file s' = true ∧
          (pts c.key).isNone = true ∧ (pts z.key).isNone = true then
        match termP file pts ec, termP file pts ea, termP file pts eb with
        | some tc, some ta, some tb =>
          if c.key ∉ (tc.vars ++ ta.vars ++ tb.vars) ∧ z.key ∉ (tc.vars ++ ta.vars ++ tb.vars) then
            some (.cond tc ta tb)
          else none
        | _, _, _ => none
      else none
  | .mk _ (.wseq (.mk _ (.base (some a, _))) e₁ (.mk _ (.pure g))) =>
      match termP file pts e₁, Unary.guard file a g with
      | some t, some u => some (.un u t)
      | _, _ => none
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [e₁, e₂])) (.mk _ (.case_ s [(pt, .mk _ (.pure y)), (pu, .mk _ (.pure n))]))) =>
      match termP file pts e₁, termP file pts e₂ with
      | some t₁, some t₂ =>
        match cmpGuard' file a b (.mk [] () (.case_ s [(pt, y), (pu, n)])) with
        | some (r, c₁, c₂) => some (.cmp r c₁ c₂ t₁ t₂)
        | none => none
      | _, _ => none
  | _ => none
termination_by sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The recogniser without pointer locals. -/
def term (file : File Codec.wireModel Unit Unit) (e : Eff) : Option Term :=
  termP file (fun _ => none) e

/-- The value with each local `q` holding `σ q`. -/
def Term.val (σ : Key → Int) : Term → Int
  | .lit c => c
  | .var q => σ q
  | .bin op a b => Guard.apply op (a.val σ) (b.val σ)
  | .cmp r c₁ c₂ a b => Guard.compare r c₁ c₂ (a.val σ) (b.val σ)
  | .cond c a b => if c.val σ = 0 then a.val σ else b.val σ
  | .un u a => u.apply (a.val σ)
  | .bit o a b => o.apply (a.val σ) (b.val σ)
  | .divpos o d a => o.apply (a.val σ) d.val

/-- The locals read hold `int`s, no intermediate value leaves `int`, and the results of
comparisons are `int`s. -/
def Term.Ok (σ : Key → Int) : Term → Prop
  | .lit c => IsInt c
  | .var q => IsInt (σ q)
  | .bin op a b => a.Ok σ ∧ b.Ok σ ∧ IsInt (Guard.apply op (a.val σ) (b.val σ))
  | .cmp _ c₁ c₂ a b => a.Ok σ ∧ b.Ok σ ∧ IsInt c₁ ∧ IsInt c₂
  | .cond c a b => c.Ok σ ∧ if c.val σ = 0 then a.Ok σ else b.Ok σ
  | .un u a => a.Ok σ ∧ IsInt (u.apply (a.val σ))
  | .bit _ a b => a.Ok σ ∧ b.Ok σ
  | .divpos _ _ a => a.Ok σ

/-- The value of an expression in range is an `int`. -/
theorem Term.int_of_ok {σ : Key → Int} : (t : Term) → t.Ok σ → IsInt (t.val σ)
  | .lit _, h => h
  | .var _, h => h
  | .bin _ _ _, h => h.2.2
  | .cmp r c₁ c₂ a b, h => by
    unfold Term.val Guard.compare
    split
    · exact h.2.2.1
    · exact h.2.2.2
  | .cond c a b, h => by
    unfold Term.val
    obtain ⟨-, h⟩ := h
    split
    · rename_i hc; rw [ite_eq_left hc] at h; exact Term.int_of_ok a h
    · rename_i hc; rw [ite_eq_right hc] at h; exact Term.int_of_ok b h
  | .un _ _, h => h.2
  | .bit o a b, h => Bitwise.apply_int o (Term.int_of_ok a h.1) (Term.int_of_ok b h.2)
  | .divpos o d a, h => DivRem.apply_int o (Term.int_of_ok a h) d

/-! ## Closing over the assigned expressions -/

/-- Each read of `q` replaced by the closed expression `ds q`. -/
def close (ds : Key → IntExpr.Term) : Term → IntExpr.Term
  | .lit c => .lit c
  | .var q => ds q
  | .bin op a b => .bin op (close ds a) (close ds b)
  | .cmp r c₁ c₂ a b => .cmp r c₁ c₂ (close ds a) (close ds b)
  | .cond c a b => .cond (close ds c) (close ds a) (close ds b)
  | .un u a => .bin .sub (.lit u.base) (close ds a)
  | .bit o a b => .bit o (close ds a) (close ds b)
  | .divpos o d a => .divpos o d (close ds a)

/-- The values of the closed expressions. -/
def values (ds : Key → IntExpr.Term) : Key → Int := fun q => (ds q).val 0

theorem close_val (ds : Key → IntExpr.Term) : (t : Term) →
    (close ds t).val 0 = t.val (values ds)
  | .lit _ => rfl
  | .var _ => rfl
  | .bin op a b => by simp [close, Term.val, IntExpr.Term.val, close_val ds a, close_val ds b]
  | .cmp r c₁ c₂ a b => by
    simp [close, Term.val, IntExpr.Term.val, close_val ds a, close_val ds b]
  | .cond c a b => by
    simp [close, Term.val, IntExpr.Term.val, close_val ds c, close_val ds a, close_val ds b]
  | .un u a => by
    simp [close, Term.val, IntExpr.Term.val, close_val ds a, Guard.apply, Unary.Unop.apply]
  | .bit o a b => by simp [close, Term.val, IntExpr.Term.val, close_val ds a, close_val ds b]
  | .divpos o d a => by simp [close, Term.val, IntExpr.Term.val, close_val ds a]

theorem close_ok (ds : Key → IntExpr.Term) : (t : Term) →
    (∀ q ∈ t.vars, (ds q).Ok 0) → t.Ok (values ds) → (close ds t).Ok 0
  | .lit _, _, h => h
  | .var q, hd, _ => hd q (by simp [Term.vars])
  | .bin op a b, hd, ⟨ha, hb, hr⟩ => by
    refine ⟨close_ok ds a (fun q hq => hd q (by simp [Term.vars, hq])) ha,
      close_ok ds b (fun q hq => hd q (by simp [Term.vars, hq])) hb, ?_⟩
    rw [close_val, close_val]; exact hr
  | .cmp r c₁ c₂ a b, hd, ⟨ha, hb, h₁, h₂⟩ =>
    ⟨close_ok ds a (fun q hq => hd q (by simp [Term.vars, hq])) ha,
      close_ok ds b (fun q hq => hd q (by simp [Term.vars, hq])) hb, h₁, h₂⟩
  | .cond c a b, hd, ⟨hc, hab⟩ => by
    refine ⟨close_ok ds c (fun q hq => hd q (by simp [Term.vars, hq])) hc, ?_⟩
    rw [close_val]
    split
    · rename_i h0; rw [ite_eq_left h0] at hab
      exact close_ok ds a (fun q hq => hd q (by simp [Term.vars, hq])) hab
    · rename_i h0; rw [ite_eq_right h0] at hab
      exact close_ok ds b (fun q hq => hd q (by simp [Term.vars, hq])) hab
  | .un u a, hd, ⟨ha, hr⟩ => by
    refine ⟨Unary.Unop.base_int u, close_ok ds a (fun q hq => hd q (by simpa [Term.vars] using hq)) ha,
      ?_⟩
    rw [IntExpr.Term.val, close_val]
    simpa [Guard.apply, Unary.Unop.apply] using hr
  | .bit o a b, hd, ⟨ha, hb⟩ =>
    ⟨close_ok ds a (fun q hq => hd q (by simp [Term.vars, hq])) ha,
      close_ok ds b (fun q hq => hd q (by simp [Term.vars, hq])) hb⟩

  | .divpos o d a, hd, ha =>
    close_ok ds a (fun q hq => hd q (by simpa [Term.vars] using hq)) ha

/-- `close ds t` is `Ok` exactly when `t` is, the closed expressions of its reads being `Ok`. -/
theorem ok_of_close (ds : Key → IntExpr.Term) : (t : Term) →
    (∀ q ∈ t.vars, (ds q).Ok 0) → (close ds t).Ok 0 → t.Ok (values ds)
  | .lit _, _, h => h
  | .var q, hd, _ => IntExpr.Term.int_of_ok (ds q) (hd q (by simp [Term.vars]))
  | .bin op a b, hd, ⟨ha, hb, hr⟩ => by
    refine ⟨ok_of_close ds a (fun q hq => hd q (by simp [Term.vars, hq])) ha,
      ok_of_close ds b (fun q hq => hd q (by simp [Term.vars, hq])) hb, ?_⟩
    rw [← close_val, ← close_val]; exact hr
  | .cmp r c₁ c₂ a b, hd, ⟨ha, hb, h₁, h₂⟩ =>
    ⟨ok_of_close ds a (fun q hq => hd q (by simp [Term.vars, hq])) ha,
      ok_of_close ds b (fun q hq => hd q (by simp [Term.vars, hq])) hb, h₁, h₂⟩
  | .cond c a b, hd, ⟨hc, hab⟩ => by
    refine ⟨ok_of_close ds c (fun q hq => hd q (by simp [Term.vars, hq])) hc, ?_⟩
    rw [close_val] at hab
    split
    · rename_i h0; rw [ite_eq_left h0] at hab
      exact ok_of_close ds a (fun q hq => hd q (by simp [Term.vars, hq])) hab
    · rename_i h0; rw [ite_eq_right h0] at hab
      exact ok_of_close ds b (fun q hq => hd q (by simp [Term.vars, hq])) hab
  | .un u a, hd, ⟨_, ha, hr⟩ => by
    refine ⟨ok_of_close ds a (fun q hq => hd q (by simpa [Term.vars] using hq)) ha, ?_⟩
    rw [IntExpr.Term.val, close_val] at hr
    simpa [Guard.apply, Unary.Unop.apply] using hr
  | .bit o a b, hd, ⟨ha, hb⟩ =>
    ⟨ok_of_close ds a (fun q hq => hd q (by simp [Term.vars, hq])) ha,
      ok_of_close ds b (fun q hq => hd q (by simp [Term.vars, hq])) hb⟩

  | .divpos o d a, hd, ha =>
    ok_of_close ds a (fun q hq => hd q (by simpa [Term.vars] using hq)) ha

/-! ## Inversion -/

theorem termP_lit {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {c : Int}
    (h : termP file pts e = some (.lit c)) : litOf file pts e = some c ∧ IsInt c := by
  unfold termP at h
  split at h
  · rename_i n hn
    cases h
    refine ⟨hn, ?_⟩
    rcases litOf_cases hn with hn | ⟨-, t, -, -, rfl⟩
    · exact (ClosedEff.lit_inv file hn).2
    · cases t <;> simp only [PtsTo.test] <;> exact ⟨by omega, by omega⟩
  · rename_i hlit
    have hlit := litOf_none hlit
    split at h
    · split at h
      · rename_i hc
        cases h
        simp [ClosedEff.lit, ClosedEff.value, Fold.eval, Return.fuel, hc] at hlit
      · cases h
    all_goals (repeat' split at h)
    all_goals cases h

theorem termP_var {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {q : Key}
    (h : termP file pts e = some (.var q)) :
    ∃ (a0 pa la a3 c1 a4 : List Annot) (pt : BaseType) (p p' : Sym) (d : Eff) (l : Loc) (u : Unit),
      e = .mk a0 (.wseq (.mk pa (.base (some p, pt))) d (.mk la (.action (.mk .pos (.mk l u
        (.load (Locals.intVal a3 c1) (.mk a4 () (.sym p')) .na)))))) ∧
        readKey file pts d = some q ∧ p'.key = p.key := by
  unfold termP at h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  · split at h
    · rename_i q' hd
      split at h
      · rename_i hc
        cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, hd, hc⟩
      · cases h
    · cases h
  all_goals (repeat' split at h)
  all_goals cases h

theorem termP_bin {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {op : IntOp}
    {t₁ t₂ : Term} (h : termP file pts e = some (.bin op t₁ t₂)) :
    ∃ (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ : Eff) (g : Pure),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g))) ∧
      Guard.guard file a b g = some op ∧ termP file pts e₁ = some t₁ ∧ termP file pts e₂ = some t₂ := by
  unfold termP at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption,
        by assumption⟩)


/-- The guard of a comparison, the continuation of its operand tuple: the pure guard
(`cmpGuard'`), or an effectful `case` whose two arms are pure, read as the pure `case` of
those arms. -/
def CmpCont (file : File Codec.wireModel Unit Unit) (a b : Sym) (K : Eff) (r : BinOp)
    (c₁ c₂ : Int) : Prop :=
  (∃ ag g, K = .mk ag (.pure g) ∧ cmpGuard' file a b g = some (r, c₁, c₂)) ∨
  ∃ (ca : List Annot) (s : Pure) (pt pu : Pattern Sym) (ya na : List Annot) (y n : Pure),
    K = .mk ca (.case_ s [(pt, .mk ya (.pure y)), (pu, .mk na (.pure n))]) ∧
    cmpGuard' file a b (.mk [] () (.case_ s [(pt, y), (pu, n)])) = some (r, c₁, c₂)

theorem CmpCont.int {file : File Codec.wireModel Unit Unit} {a b : Sym} {K : Eff} {r : BinOp}
    {c₁ c₂ : Int} (h : CmpCont file a b K r c₁ c₂) : IsInt c₁ ∧ IsInt c₂ := by
  rcases h with ⟨_, _, _, hg⟩ | ⟨_, _, _, _, _, _, _, _, _, hg⟩ <;> exact cmpGuard'_int hg

theorem CmpCont.calls {file : File Codec.wireModel Unit Unit} {a b : Sym} {K : Eff} {r : BinOp}
    {c₁ c₂ : Int} (h : CmpCont file a b K r c₁ c₂) : hasCCall K = false := by
  rcases h with ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, rfl, _⟩
  · rw [hasCCall.eq_def]
  · rw [hasCCall.eq_def]
    simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_eq_false_iff]
    constructor <;> rw [hasCCall.eq_def]

theorem termP_cmp {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {r : BinOp}
    {c₁ c₂ : Int} {t₁ t₂ : Term} (h : termP file pts e = some (.cmp r c₁ c₂ t₁ t₂)) :
    ∃ (an pp p1 p2 au : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ : Eff) (K : Eff),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) K) ∧
      CmpCont file a b K r c₁ c₂ ∧ termP file pts e₁ = some t₁ ∧ termP file pts e₂ = some t₂ := by
  unfold termP at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl,
        .inl ⟨_, _, rfl, by assumption⟩, by assumption, by assumption⟩)
    | (cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl,
        .inr ⟨_, _, _, _, _, _, _, _, rfl, by assumption⟩, by assumption, by assumption⟩)


theorem termP_bit {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {o : Bitwise.Op}
    {t₁ t₂ : Term} (h : termP file pts e = some (.bit o t₁ t₂)) :
    ∃ (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ : Eff) (g : Pure),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g))) ∧
      Bitwise.guard file a b g = some o ∧ termP file pts e₁ = some t₁ ∧ termP file pts e₂ = some t₂ := by
  unfold termP at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption,
        by assumption⟩)

theorem termP_un {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {u : Unary.Unop} {t : Term}
    (h : termP file pts e = some (.un u t)) :
    ∃ (an pa ag : List Annot) (a : Sym) (ta : BaseType) (e₁ : Eff) (g : Pure),
      e = .mk an (.wseq (.mk pa (.base (some a, ta))) e₁ (.mk ag (.pure g))) ∧
      Unary.guard file a g = some u ∧ termP file pts e₁ = some t := by
  unfold termP at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, _, _, _, _, _, _, rfl, by assumption, by assumption⟩)

theorem termP_divpos {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {o : DivRem.Op}
    {d : DivRem.Divisor} {t : Term} (h : termP file pts e = some (.divpos o d t)) :
    ∃ (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType)
      (e₁ e₂ : Eff) (g : Pure) (n : Int),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g))) ∧
      DivRem.guard file a b g = some o ∧ termP file pts e₁ = some t ∧
      termP file pts e₂ = some (.lit n) ∧ DivRem.divisor? n = some d := by
  unfold termP at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
        by assumption, by assumption, by assumption, by assumption⟩)

/-- The pieces of a run of a conditional (`Cond.CondRuns`), the branch environment agreeing
with the outer one on every symbol whose key is not bound by the conditional (`bk`). -/
def CondRunsK {file : Program} {labels : Labels} (bk : List Key) (e ec ea eb : Eff) : Prop :=
  ∀ (env : Env) (k : List Frame) (m : Mem.Concrete.State), ∃ K : Frame,
    LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.effectExpr ec env, K :: k, m⟩ ∧
    ∀ (cv : Int) (fr : List Frame) (xs : List Access), OneAnn fr xs → ∀ m₁ : Mem.Concrete.State,
      ∃ (env₂ : Env) (KB : Frame) (m₂ : Mem.Concrete.State),
        (∀ y : Sym, y.key ∉ bk → env₂.lookup y = env.lookup y) ∧ Touched m₁ m₂ ∧
        LocalReaches file labels false ⟨.value (spec cv), fr ++ K :: k, m₁⟩
          ⟨.effectExpr (if cv = 0 then ea else eb) env₂, KB :: (fr ++ k), m₂⟩ ∧
        ∀ va : Int, IsInt va → ∀ (fr' : List Frame) (ys : List Access), OneAnn fr' ys →
          ∀ m₃ : Mem.Concrete.State, ∃ m₄, Touched m₃ m₄ ∧
            LocalReaches file labels false ⟨.value (spec va), fr' ++ (KB :: (fr ++ k)), m₃⟩
              ⟨.value (spec va), fr' ++ (fr ++ k), m₄⟩

/-- `Cond.CondRuns` for a fresh symbol of every key outside `[c, z]` gives `CondRunsK`: the
shape lemma `Cond.cond_runs_of_shape` holds for every such symbol, and its branch environment
is the same for all of them. -/
theorem condRunsK_of_shape {file : Program} {labels : Labels} {c c' z z' u u' w w' s s' : Sym}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 d0 d1 d2 d3 d4 d5 : List Annot}
    {t1 t2 t3 t4 : BaseType} {ec ea eb : Eff} {ps : List (Pattern Sym)} {q : PE}
    (hc : c'.key = c.key) (hz : z'.key = z.key) (hu : u'.key = u.key) (hw : w'.key = w.key)
    (hs : ConvInt.isConvLoadedInt file s = true) (hs' : ConvInt.isConvLoadedInt file s' = true) :
    CondRunsK (file := file) (labels := labels) [c.key, z.key]
      (.mk a0 (.sseq (.mk a1 (.base (some c, t1))) ec
        (.mk a2 (.case_ (.mk a3 () (.sym c'))
          [(.mk a4 (.ctor .specified [.mk a5 (.base (some z, t2))]),
            .mk a6 (.if_ (.mk a7 () (.op .eq (.mk a8 () (.sym z')) (.mk a9 () (.val (.object (.integer 0))))))
              (.mk b0 (.sseq (.mk b1 (.base (some u, t3))) ea
                (.mk b2 (.pure (.mk b3 () (.call (.sym s) [.mk b4 () (.val (.ctype (.mk b5
                  (.basic (.integer (.signed .int)))))), .mk b6 () (.sym u')]))))))
              (.mk b7 (.sseq (.mk b8 (.base (some w, t4))) eb
                (.mk b9 (.pure (.mk d0 () (.call (.sym s') [.mk d1 () (.val (.ctype (.mk d2
                  (.basic (.integer (.signed .int)))))), .mk d3 () (.sym w')])))))))),
           (.mk d4 (.ctor .unspecified ps), .mk d5 (.pure q))]))))
      ec ea eb := by
  intro env k m
  let CA : PE := .mk b3 () (.call (.sym s) [.mk b4 () (.val (.ctype (.mk b5
      (.basic (.integer (.signed .int)))))), .mk b6 () (.sym u')])
  let CB : PE := .mk d0 () (.call (.sym s') [.mk d1 () (.val (.ctype (.mk d2
      (.basic (.integer (.signed .int)))))), .mk d3 () (.sym w')])
  let BA : EE := .mk b0 (.sseq (.mk b1 (.base (some u, t3))) ea (.mk b2 (.pure CA)))
  let BB : EE := .mk b7 (.sseq (.mk b8 (.base (some w, t4))) eb (.mk b9 (.pure CB)))
  let IF : EE := .mk a6 (.if_ (.mk a7 () (.op .eq (.mk a8 () (.sym z'))
    (.mk a9 () (.val (.object (.integer 0)))))) BA BB)
  let BS : List (Pattern Sym × EE) := [(.mk a4 (.ctor .specified [.mk a5 (.base (some z, t2))]), IF),
    (.mk d4 (.ctor .unspecified ps), .mk d5 (.pure q))]
  let R : EE := .mk a2 (.case_ (.mk a3 () (.sym c')) BS)
  refine ⟨.strongBind (.mk a1 (.base (some c, t1))) R env,
    .single (.next (Cond.requestAux_sseq m a0 _ ec R env k false) (LoadTask.plain_effectExpr _ _)), ?_⟩
  intro cv fr xs hfr m₁
  let env₁ := extendEnv [(c, spec cv)] env
  let env₂ := extendEnv [(z, .object (.integer cv))] env₁
  have s₁ := Cond.value_strongBind (file := file) (labels := labels) hfr (spec cv) a1 c t1 R env k m₁
  obtain ⟨l, hr⟩ := Cond.requestAux_case (file := file) (labels := labels) m₁ a2 (.mk a3 () (.sym c')) BS
    env₁ (fr ++ k) false
  obtain ⟨l₁, s₂⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr _ env₁) (by simpa using hr)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
  have s₃ : LocalReaches file labels false ⟨.pureExpr (.mk a3 () (.sym c')) env₁, .effectCase BS env₁ :: (fr ++ k), m₂⟩
      ⟨.effectExpr IF env₂, fr ++ k, m₂⟩ :=
    .head (.next (LoadTask.requestAux_sym m₂ a3 c' env₁ (ConvInt.lookup_one hc) _ false)
      (LoadTask.plain_value _))
      (.single (.next (Cond.requestAux_effectCase m₂ _ BS env₁ (fr ++ k) false
        (by simp [BS, selectCase, matchPattern])) (LoadTask.plain_effectExpr _ _)))
  obtain ⟨l', hr'⟩ := Cond.requestAux_if (file := file) (labels := labels) m₂ a6 (.mk a7 () (.op .eq
    (.mk a8 () (.sym z')) (.mk a9 () (.val (.object (.integer 0)))))) BA BB env₂ (fr ++ k) false
  obtain ⟨l₂, s₄⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr _ env₂) (by simpa using hr')
  let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
  have heval : Eval file (tagsOf file m₃) env₂ (.inl (.mk a7 () (.op .eq (.mk a8 () (.sym z'))
      (.mk a9 () (.val (.object (.integer 0))))))) (.inl (boolean (cv == 0))) :=
    .op (.cons (.sym (ConvInt.lookup_one hz)) (.cons .val .nil))
      (by simp [primitive, integerBin, runtimeValue, runtimeObject]; rfl)
  have s₅ := PureLocal.eval_local file (tagsOf file m₃) (wc := false) (labels := labels) heval
    (.effectIf BA BB env₂ :: (fr ++ k)) m₃ rfl
  have hx₂ : ∀ y : Sym, y.key ∉ [c.key, z.key] → env₂.lookup y = env.lookup y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [ConvInt.lookup_one_other hy.2, ConvInt.lookup_one_other hy.1]
  by_cases h0 : cv = 0
  · have hb : (cv == 0) = true := by simp [h0]
    have s₆ : LocalReaches file labels false ⟨.value (boolean (cv == 0)), .effectIf BA BB env₂ :: (fr ++ k), m₃⟩
        ⟨.effectExpr BA env₂, fr ++ k, m₃⟩ :=
      .single (.next (by rw [Cond.requestAux_effectIf]; simp [hb]) (LoadTask.plain_effectExpr _ _))
    refine ⟨env₂, .strongBind (.mk b1 (.base (some u, t3))) (.mk b2 (.pure CA)) env₂, m₃, hx₂,
      ⟨l₂, m₁.lastUsed, rfl⟩, ?_, ?_⟩
    · rw [ite_eq_left h0]
      exact s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.tail
        (.next (Cond.requestAux_sseq m₃ b0 _ ea _ env₂ (fr ++ k) false) (LoadTask.plain_effectExpr _ _)))))))
    · intro va hva fr' ys h' m₄
      simpa using Cond.branch_end (file := file) (labels := labels) hu hs b1 t3 b2 b3 b4 b5 b6 env₂
        (fr ++ k) hva h' m₄
  · have hb : (cv == 0) = false := by simp [h0]
    have s₆ : LocalReaches file labels false ⟨.value (boolean (cv == 0)), .effectIf BA BB env₂ :: (fr ++ k), m₃⟩
        ⟨.effectExpr BB env₂, fr ++ k, m₃⟩ :=
      .single (.next (by rw [Cond.requestAux_effectIf]; simp [hb]) (LoadTask.plain_effectExpr _ _))
    refine ⟨env₂, .strongBind (.mk b8 (.base (some w, t4))) (.mk b9 (.pure CB)) env₂, m₃, hx₂,
      ⟨l₂, m₁.lastUsed, rfl⟩, ?_, ?_⟩
    · rw [ite_eq_right h0]
      exact s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.tail
        (.next (Cond.requestAux_sseq m₃ b7 _ eb _ env₂ (fr ++ k) false) (LoadTask.plain_effectExpr _ _)))))))
    · intro va hva fr' ys h' m₄
      simpa using Cond.branch_end (file := file) (labels := labels) hw hs' b8 t4 b9 d0 d1 d2 d3 env₂
        (fr ++ k) hva h' m₄

theorem termP_cond {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {e : Eff} {tc ta tb : Term}
    (h : termP file pts e = some (.cond tc ta tb)) :
    ∃ (ec ea eb : Eff) (bk : List Key), termP file pts ec = some tc ∧ termP file pts ea = some ta ∧
      termP file pts eb = some tb ∧ (∀ q ∈ bk, q ∉ tc.vars ++ ta.vars ++ tb.vars) ∧
      (∀ q ∈ bk, pts q = none) ∧ (hasCCall ec = false → hasCCall ea = false → hasCCall eb = false → hasCCall e = false) ∧
      ∀ labels, CondRunsK (file := file) (labels := labels) bk e ec ea eb := by
  unfold termP at h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  · repeat' split at h
    all_goals cases h
  · split at h
    · repeat' split at h
      all_goals cases h
    · cases h
  · split at h
    · rename_i cond
      obtain ⟨hc, hz, hu, hw, hs, hs', pc, pz⟩ := cond
      split at h
      · split at h
        · rename_i fresh
          cases h
          refine ⟨_, _, _, _, by assumption, by assumption, by assumption, ?_, ?_, ?_,
            fun labels => condRunsK_of_shape hc hz hu hw hs hs'⟩
          · intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact fresh.1
            · exact fresh.2
          · intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact Option.isNone_iff_eq_none.mp pc
            · exact Option.isNone_iff_eq_none.mp pz
          · intro c₁ c₂ c₃
            simp [hasCCall, c₁, c₂, c₃]
        · cases h
      · cases h
    · cases h
  · split at h <;> cases h
  · (repeat' split at h) <;> cases h
  · cases h

/-- Recognised expressions make no procedure call. -/
theorem termP_calls {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} :
    (t : Term) → {e : Eff} → termP file pts e = some t → hasCCall e = false
  | .lit _, _, h => by
    rcases litOf_cases (termP_lit h).1 with h | ⟨r, -, hr, -⟩
    · exact ClosedEff.lit_noCall _ h
    · exact PtrDeref.nullTestOf_noCall hr
  | .var _, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, hd, _⟩ := termP_var h
    simp [hasCCall, readKey_noCall hd]
  | .bin _ t₁ t₂, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, e₂, _, rfl, _, h₁, h₂⟩ := termP_bin h
    simp [hasCCall, termP_calls t₁ h₁, termP_calls t₂ h₂]
  | .cmp _ _ _ t₁ t₂, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, e₁, e₂, K, rfl, hK, h₁, h₂⟩ := termP_cmp h
    simp [hasCCall, termP_calls t₁ h₁, termP_calls t₂ h₂, hK.calls]
  | .cond tc ta tb, _, h => by
    obtain ⟨_, _, _, _, h₁, h₂, h₃, -, -, hc, -⟩ := termP_cond h
    exact hc (termP_calls tc h₁) (termP_calls ta h₂) (termP_calls tb h₃)
  | .un _ t₁, _, h => by
    obtain ⟨_, _, _, _, _, e₁, _, rfl, _, h₁⟩ := termP_un h
    simp [hasCCall, termP_calls t₁ h₁]
  | .bit _ t₁ t₂, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, e₂, _, rfl, _, h₁, h₂⟩ := termP_bit h
    simp [hasCCall, termP_calls t₁ h₁, termP_calls t₂ h₂]

  | .divpos _ _ t₁, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, e₂, _, n, rfl, _, h₁, h₂, _⟩ := termP_divpos h
    have nc₂ : hasCCall e₂ = false := by
      rcases litOf_cases (termP_lit h₂).1 with h | ⟨r, -, hr, -⟩
      · exact ClosedEff.lit_noCall _ h
      · exact PtrDeref.nullTestOf_noCall hr
    simp [hasCCall, termP_calls t₁ h₁, nc₂]

/-! ## Runs -/

variable {file : Program} {labels : Labels} {pts : Key → Option PtsTo}

/-- Every symbol with key `q` points, in `env`, to the slot of the `int` `n`. -/
def Loc (env : Env) (m : Mem.Concrete.State) (q : Key) (n : Int) : Prop :=
  IsInt n ∧ ∃ id addr, (∀ y : Sym, y.key = q → env.lookup y =
    some (.object (.pointer (.allocated id addr)))) ∧ Slot m id addr n

theorem Loc.touched {env : Env} {m m' : Mem.Concrete.State} {q : Key} {n : Int}
    (h : Loc env m q n) (t : Touched m m') : Loc env m' q n := by
  obtain ⟨hn, id, addr, hx, slot⟩ := h
  exact ⟨hn, id, addr, hx, t.slot slot⟩

theorem Loc.env {env env' : Env} {m : Mem.Concrete.State} {q : Key} {n : Int}
    (h : Loc env m q n) (he : ∀ y : Sym, y.key = q → env'.lookup y = env.lookup y) :
    Loc env' m q n := by
  obtain ⟨hn, id, addr, hx, slot⟩ := h
  exact ⟨hn, id, addr, fun y hy => (he y hy).trans (hx y hy), slot⟩

/-- `Loc` for every local `t` reads. -/
def Locs (env : Env) (m : Mem.Concrete.State) (σ : Key → Int) (t : Term) : Prop :=
  ∀ q ∈ t.vars, Loc env m q (σ q)

theorem Locs.touched {env : Env} {m m' : Mem.Concrete.State} {σ : Key → Int} {t : Term}
    (h : Locs env m σ t) (tch : Touched m m') : Locs env m' σ t :=
  fun q hq => (h q hq).touched tch

theorem Locs.sub {env : Env} {m : Mem.Concrete.State} {σ : Key → Int} {t t' : Term}
    (h : Locs env m σ t) (hs : ∀ q ∈ t'.vars, q ∈ t.vars) : Locs env m σ t' :=
  fun q hq => h q (hs q hq)

theorem Locs.env {env env' : Env} {m : Mem.Concrete.State} {σ : Key → Int} {t : Term}
    {bk : List Key} (h : Locs env m σ t) (fresh : ∀ q ∈ bk, q ∉ t.vars)
    (he : ∀ y : Sym, y.key ∉ bk → env'.lookup y = env.lookup y) : Locs env' m σ t := by
  intro q hq
  refine (h q hq).env fun y hy => he y fun hb => fresh _ hb (hy ▸ hq)

/-- The pointer locals that `t` reads through: each pointer local `r` whose target `x` (by
`pts`) `t` reads is pointed to by every symbol with key `r`, and its object holds the pointer to
`x`'s object (wherever the symbols of `x`'s key point), an address aligned for `int`. -/
def PtsOk (env : Env) (m : Mem.Concrete.State) (pts : Key → Option PtsTo) (t : Term) : Prop :=
  ∀ r x, pts r = some (.addr x) → x.key ∈ t.vars → ∃ pid paddr,
    (∀ y : Sym, y.key = r → env.lookup y = some (.object (.pointer (.allocated pid paddr)))) ∧
    ∀ id addr, (∀ y : Sym, y.key = x.key → env.lookup y = some (.object (.pointer (.allocated id addr)))) →
      StrMem.PtrObj m pid paddr id addr ∧ addr % 4 = 0

theorem PtsOk.none (env : Env) (m : Mem.Concrete.State) (t : Term) :
    PtsOk env m (fun _ => none) t := fun _ _ h _ => by simp at h


/-- What the pointer object `pid` at `paddr` holds for the target `t`: an allocated pointer
(`addr`) or the null pointer (`null`). -/
def PtsTo.Obj (m : Mem.Concrete.State) (pid paddr : Int) : PtsTo → Prop
  | .addr _ => ∃ id addr, StrMem.PtrObj m pid paddr id addr
  | .null => StrMem.PtrNull m pid paddr

theorem PtsTo.Obj.touched {m m' : Mem.Concrete.State} {pid paddr : Int} {t : PtsTo}
    (h : t.Obj m pid paddr) (tch : Touched m m') : t.Obj m' pid paddr := by
  cases t with
  | addr x => obtain ⟨id, addr, obj⟩ := h; exact ⟨id, addr, obj.touched tch⟩
  | null =>
    obtain ⟨l, u, rfl⟩ := tch
    exact ⟨⟨h.slot.alive, h.slot.alloc, h.slot.below, h.slot.above⟩, h.bytes⟩

/-- Each pointer local with a target is pointed to by the symbols of its key and holds an
allocated pointer or the null pointer (`PtsTo.Obj`): what a pointer test needs. -/
def PtsNN (env : Env) (m : Mem.Concrete.State) (pts : Key → Option PtsTo) : Prop :=
  ∀ r t, pts r = some t → ∃ pid paddr,
    (∀ y : Sym, y.key = r → env.lookup y = some (.object (.pointer (.allocated pid paddr)))) ∧
      t.Obj m pid paddr

theorem PtsNN.none (env : Env) (m : Mem.Concrete.State) : PtsNN env m (fun _ => none) :=
  fun _ _ h => by simp at h

/-- `Locs`, `PtsOk` and `PtsNN`: what a read of `t` needs. -/
def LocsP (env : Env) (m : Mem.Concrete.State) (σ : Key → Int) (pts : Key → Option PtsTo)
    (t : Term) : Prop :=
  Locs env m σ t ∧ PtsOk env m pts t ∧ PtsNN env m pts

theorem LocsP.touched {env : Env} {m m' : Mem.Concrete.State} {σ : Key → Int}
    {pts : Key → Option PtsTo} {t : Term} (h : LocsP env m σ pts t) (tch : Touched m m') :
    LocsP env m' σ pts t := by
  refine ⟨h.1.touched tch, fun r q hr hq => ?_, fun r x hr => ?_⟩
  · obtain ⟨pid, paddr, he, hobj⟩ := h.2.1 r q hr hq
    exact ⟨pid, paddr, he, fun id addr hx => ⟨(hobj id addr hx).1.touched tch, (hobj id addr hx).2⟩⟩
  · obtain ⟨pid, paddr, he, obj⟩ := h.2.2 r x hr
    exact ⟨pid, paddr, he, obj.touched tch⟩

theorem LocsP.sub {env : Env} {m : Mem.Concrete.State} {σ : Key → Int}
    {pts : Key → Option PtsTo} {t t' : Term} (h : LocsP env m σ pts t)
    (hs : ∀ q ∈ t'.vars, q ∈ t.vars) : LocsP env m σ pts t' :=
  ⟨h.1.sub hs, fun r q hr hq => h.2.1 r q hr (hs _ hq), h.2.2⟩

theorem LocsP.env {env env' : Env} {m : Mem.Concrete.State} {σ : Key → Int}
    {pts : Key → Option PtsTo} {t : Term} {bk : List Key} (h : LocsP env m σ pts t)
    (fresh : ∀ q ∈ bk, q ∉ t.vars) (hpb : ∀ q ∈ bk, pts q = none)
    (he : ∀ y : Sym, y.key ∉ bk → env'.lookup y = env.lookup y) : LocsP env' m σ pts t := by
  refine ⟨h.1.env fresh he, fun r q hr hq => ?_, fun r x hr => ?_⟩
  · obtain ⟨pid, paddr, hre, hobj⟩ := h.2.1 r q hr hq
    have hrb : r ∉ bk := fun hb => by rw [hpb r hb] at hr; cases hr
    have hqb : q.key ∉ bk := fun hb => fresh _ hb hq
    refine ⟨pid, paddr, fun y hy => (he y (hy ▸ hrb)).trans (hre y hy), fun id addr hx => ?_⟩
    exact hobj id addr fun y hy => (he y (hy ▸ hqb)).symm.trans (hx y hy)
  · obtain ⟨pid, paddr, hre, obj⟩ := h.2.2 r x hr
    have hrb : r ∉ bk := fun hb => by rw [hpb r hb] at hr; cases hr
    exact ⟨pid, paddr, fun y hy => (he y (hy ▸ hrb)).trans (hre y hy), obj⟩

/-- The read-only task of an operand. -/
theorem task_of_runs {env : Env} {σ : Key → Int} (t : Term) {e : Eff}
    (he : termP file pts e = some t) (I : Mem.Concrete.State → Prop)
    (runs : ∀ m, I m → ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
      LocalReaches file labels false ⟨.effectExpr e env, [], m⟩ ⟨.value (spec (t.val σ)), fr ++ [], m'⟩) :
    ReadTask (file := file) (labels := labels) I env e (spec (t.val σ)) := by
  refine ⟨termP_calls t he, fun m hm => ?_⟩
  obtain ⟨xs, m', fr, hfr, rd, tch, run⟩ := runs m hm
  refine ⟨xs, m', rd, tch, fr, by simpa using run, ?_⟩
  rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]

/-- The arm a two-arm `case` selects, with the pure arms wrapped as effects. -/
theorem select_pure {x : Val} {pt pu : Pattern Sym} {ya na : List Annot} {y n : Pure}
    {xs : Bindings} {body : Pure} (h : selectCase x [(pt, y), (pu, n)] = some (xs, body)) :
    ∃ ann, selectCase x [(pt, (.mk ya (.pure y) : Eff)), (pu, .mk na (.pure n))] =
      some (xs, .mk ann (.pure body)) := by
  unfold selectCase at h ⊢
  cases hm : matchPattern pt x with
  | some e =>
    simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ya, rfl⟩
  | none =>
    simp only [hm] at h ⊢
    unfold selectCase at h ⊢
    cases hn : matchPattern pu x with
    | some e =>
      simp only [hn, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨na, rfl⟩
    | none => simp [hn, selectCase] at h

/-- **The guard of a comparison** reaches its value from the operand environment by local
steps, changing only the current location. -/
theorem CmpCont.local {a b : Sym} {K : Eff} {r : BinOp} {c₁ c₂ : Int}
    (h : CmpCont file a b K r c₁ c₂) (env : Env) {n₁ n₂ : Int} (h₁ : IsInt n₁) (h₂ : IsInt n₂)
    (k : List Frame) (m : Mem.Concrete.State) :
    ∃ l, LocalReaches file labels false ⟨.effectExpr K (Guard.operands a b n₁ n₂ env), k, m⟩
      ⟨.value (spec (Guard.compare r c₁ c₂ n₁ n₂)), k, {m with currentLocation := l}⟩ := by
  rcases h with ⟨ag, g, rfl, hg⟩ | ⟨ca, s, pt, pu, ya, na, y, n, rfl, hg⟩
  · obtain ⟨l', s₁⟩ := guard_local (file := file) (labels := labels) ag g
      (Guard.operands a b n₁ n₂ env) k m
    have s₂ := PureLocal.eval_local file (PureEval.tagsOf file m) (wc := false) (labels := labels)
      (cmpGuard'_eval hg env h₁ h₂) (.diagnosticLocation m.currentLocation :: k)
      {m with currentLocation := l'} rfl
    exact ⟨l', s₁.trans (s₂.tail (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)))⟩
  · have ev := cmpGuard'_eval (tags := PureEval.tagsOf file m) hg env h₁ h₂
    cases ev with
    | case_ hs hsel hbody =>
      rename_i x xs body
      let env' := Guard.operands a b n₁ n₂ env
      let BS : List (Pattern Sym × Eff) := [(pt, .mk ya (.pure y)), (pu, .mk na (.pure n))]
      obtain ⟨ann, hsel'⟩ := select_pure (ya := ya) (na := na) hsel
      obtain ⟨l₁, hr⟩ := Cond.requestAux_case (file := file) (labels := labels) m ca s BS env' k false
      obtain ⟨l', s₁⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr s env') (by simpa using hr)
      have s₂ := PureLocal.eval_local file (PureEval.tagsOf file m) (wc := false) (labels := labels)
        hs (.effectCase BS env' :: k) {m with currentLocation := l'} rfl
      have s₃ : LocalReaches file labels false
          ⟨.value x, .effectCase BS env' :: k, {m with currentLocation := l'}⟩
          ⟨.effectExpr (.mk ann (.pure body)) (extendEnv xs env'), k, {m with currentLocation := l'}⟩ :=
        .single (.next (Cond.requestAux_effectCase _ x BS env' k false hsel')
          (LoadTask.plain_effectExpr _ _))
      obtain ⟨l'', s₄⟩ := guard_local (file := file) (labels := labels) ann body
        (extendEnv xs env') k {m with currentLocation := l'}
      have s₅ := PureLocal.eval_local file (PureEval.tagsOf file m) (wc := false) (labels := labels)
        hbody (.diagnosticLocation l' :: k) {m with currentLocation := l''} rfl
      exact ⟨l'', s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail
        (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
          (LoadTask.plain_value _))))))⟩

/-- A literal runs without writing: a closed expression, or a pointer test that `pts` decides. -/
theorem lit_runs {c : Int} {e : Eff} (h : termP file pts e = some (.lit c)) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (nn : PtsNN env m pts) :
    ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧
      Touched m m' ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.value (spec c), fr ++ k, m'⟩ := by
  rcases litOf_cases (termP_lit h).1 with hcl | ⟨r, t, hr, hpr, rfl⟩
  · obtain ⟨l, fr, hfr, run⟩ := ClosedEff.lit_local file labels hcl env k m
    exact ⟨[], _, fr, hfr, by simp, ⟨l, m.lastUsed, rfl⟩, run⟩
  · obtain ⟨pid, paddr, hre, ho⟩ := nn r.key t hpr
    cases t with
    | addr x =>
      obtain ⟨id, addr, obj⟩ := ho
      exact (PtrDeref.nullTest_runs (file := file) (labels := labels) hr
        (fun m' => StrMem.PtrObj m' pid paddr id addr) (hre r rfl) (fun _ h => h)).2 k m obj
    | null =>
      exact (PtrDeref.nullTestNull_runs (file := file) (labels := labels) hr
        (fun m' => StrMem.PtrNull m' pid paddr) (hre r rfl) (fun _ h => h)).2 k m ho


/-- **Value arm.** -/
theorem termP_runs : (t : Term) → {e : Eff} → termP file pts e = some t →
    {env : Env} → {σ : Key → Int} → t.Ok σ → ∀ (k : List Frame) (m : Mem.Concrete.State),
      LocsP env m σ pts t →
      ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧
        Touched m m' ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
          ⟨.value (spec (t.val σ)), fr ++ k, m'⟩
  | .lit c, e, h, env, σ, ok, k, m, locs => lit_runs h env k m locs.2.2
  | .var q, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨a0, pa, la, a3, c1, a4, pt, p, p', d, l, u, rfl, hd, hp'⟩ := termP_var h
    obtain ⟨hn, id, addr, hx, slot⟩ := locs.1 q (by simp [Term.vars])
    rcases readKey_inv hd with ⟨x', hd', hx'⟩ | ⟨r, x, hr, hpr, rfl⟩
    · obtain ⟨a, m', ha, t, run⟩ := IntWrap.load_desig (file := file) (labels := labels) a0 pa la a3
        c1 a4 pt p p' d l u hp' hd' env k m (hx x' hx') ⟨hn.1, hn.2⟩ slot
      exact ⟨[a], m', [.annotations [a]], .inr rfl, by simpa using ha, t, run⟩
    · obtain ⟨pid, paddr, hre, hobj⟩ := locs.2.1 r.key x hpr (by simp [Term.vars])
      obtain ⟨obj, al⟩ := hobj id addr hx
      let I : Mem.Concrete.State → Prop := fun m' =>
        StrMem.PtrObj m' pid paddr id addr ∧ Slot m' id addr (σ x.key)
      have hI : ∀ m₁ m₂, I m₁ → Touched m₁ m₂ → I m₂ := fun _ _ h t => ⟨h.1.touched t, t.slot h.2⟩
      have hdr := PtrDeref.deref_runs (file := file) (labels := labels) hr I hI (hre r rfl)
        (fun _ h => ⟨h.1, h.2.live⟩) al
      exact PtrDeref.read_runs a0 pa la a3 c1 a4 pt p p' d l u hp' I hdr ⟨hn.1, hn.2⟩
        (fun _ h => h.2) k m ⟨obj, slot⟩
  | .bin op t₁ t₂, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := termP_bin h
    obtain ⟨ok₁, ok₂, okr⟩ := ok
    let I : Mem.Concrete.State → Prop := fun m => LocsP env m σ pts (.bin op t₁ t₂)
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.bin op t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.bin op t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT (.mk ag (.pure g)) env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT (.mk ag (.pure g)) env :: k) (annots := au) I hI
      (task_of_runs t₁ h₁ I fun m hm => termP_runs t₁ h₁ ok₁ [] m (hm.sub sub₁))
      (task_of_runs t₂ h₂ I fun m hm => termP_runs t₂ h₂ ok₂ [] m (hm.sub sub₂))
      (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m locs
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val σ), spec (t₂.val σ)]),
          .annotations xs :: .effectBind PAT (.mk ag (.pure g)) env :: k, m₁⟩
        ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b (t₁.val σ) (t₂.val σ) env),
          .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    have i₁ := Term.int_of_ok t₁ ok₁
    have i₂ := Term.int_of_ok t₂ ok₂
    obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag g
      (Guard.operands a b (t₁.val σ) (t₂.val σ) env) (.annotations xs :: k) m₁
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
    have s₅ := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
      (Guard.guard_eval hg env i₁ i₂ okr) (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k)
      m₂ rfl
    refine ⟨xs, m₂, [.annotations xs], .inr rfl, rd, tch.trans ⟨l', m₁.lastUsed, rfl⟩,
      s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
    exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)
  | .cmp rl c₁ c₂ t₁ t₂, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, a, b, ta, tb, e₁, e₂, K, rfl, hK, h₁, h₂⟩ := termP_cmp h
    obtain ⟨ok₁, ok₂, -, -⟩ := ok
    let I : Mem.Concrete.State → Prop := fun m => LocsP env m σ pts (.cmp rl c₁ c₂ t₁ t₂)
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.cmp rl c₁ c₂ t₁ t₂).vars := fun q hq => by
      simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.cmp rl c₁ c₂ t₁ t₂).vars := fun q hq => by
      simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) K)) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT K env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT K env :: k) (annots := au) I hI
      (task_of_runs t₁ h₁ I fun m hm => termP_runs t₁ h₁ ok₁ [] m (hm.sub sub₁))
      (task_of_runs t₂ h₂ I fun m hm => termP_runs t₂ h₂ ok₂ [] m (hm.sub sub₂))
      (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m locs
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val σ), spec (t₂.val σ)]),
          .annotations xs :: .effectBind PAT K env :: k, m₁⟩
        ⟨.effectExpr K (Guard.operands a b (t₁.val σ) (t₂.val σ) env), .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    obtain ⟨l', s₄⟩ := hK.local env (Term.int_of_ok t₁ ok₁) (Term.int_of_ok t₂ ok₂)
      (.annotations xs :: k) m₁
    exact ⟨xs, _, [.annotations xs], .inr rfl, rd, tch.trans ⟨l', m₁.lastUsed, rfl⟩,
      s₁.trans (s₂.trans (s₃.trans s₄))⟩
  | .cond tc ta tb, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨ec, ea, eb, bk, h₁, h₂, h₃, fresh, hpb, -, cr⟩ := termP_cond h
    obtain ⟨okc, okb⟩ := ok
    have subc : ∀ q ∈ tc.vars, q ∈ (Term.cond tc ta tb).vars := fun q hq => by simp [Term.vars, hq]
    have suba : ∀ q ∈ ta.vars, q ∈ (Term.cond tc ta tb).vars := fun q hq => by simp [Term.vars, hq]
    have subb : ∀ q ∈ tb.vars, q ∈ (Term.cond tc ta tb).vars := fun q hq => by simp [Term.vars, hq]
    have fresh' : ∀ q ∈ bk, q ∉ (Term.cond tc ta tb).vars := fun q hq => by
      simpa [Term.vars, List.append_assoc] using fresh q hq
    obtain ⟨K, s₁, rest⟩ := cr labels env k m
    obtain ⟨xs, m₁, fr, hfr, rd, tch, run⟩ := termP_runs tc h₁ okc (K :: k) m (locs.sub subc)
    obtain ⟨env₂, KB, m₂, hx₂, tch₂, s₃, fin⟩ := rest (tc.val σ) fr xs hfr m₁
    have locs₂ : LocsP env₂ m₂ σ pts (.cond tc ta tb) :=
      (locs.touched (tch.trans tch₂)).env fresh' hpb hx₂
    by_cases h0 : tc.val σ = 0
    · rw [ite_eq_left h0] at s₃ okb
      obtain ⟨ys, m₃, fr', hfr', rd', tch', run'⟩ := termP_runs ta h₂ okb (KB :: (fr ++ k)) m₂
        (locs₂.sub suba)
      obtain ⟨m₄, tch₄, s₅⟩ := fin (ta.val σ) (Term.int_of_ok ta okb) fr' ys hfr' m₃
      obtain ⟨zs, fr'', hfr'', hzs, s₆⟩ := Cond.merge (file := file) (labels := labels) hfr hfr'
        (spec (ta.val σ)) k m₄
      have hv : Term.val σ (.cond tc ta tb) = ta.val σ := by simp [Term.val, h0]
      rw [hv]
      exact ⟨zs, m₄, fr'', hfr'', fun a ha => (hzs a ha).elim (rd' a) (rd a),
        tch.trans (tch₂.trans (tch'.trans tch₄)), s₁.trans (run.trans (s₃.trans (run'.trans
          (s₅.trans s₆))))⟩
    · rw [ite_eq_right h0] at s₃ okb
      obtain ⟨ys, m₃, fr', hfr', rd', tch', run'⟩ := termP_runs tb h₃ okb (KB :: (fr ++ k)) m₂
        (locs₂.sub subb)
      obtain ⟨m₄, tch₄, s₅⟩ := fin (tb.val σ) (Term.int_of_ok tb okb) fr' ys hfr' m₃
      obtain ⟨zs, fr'', hfr'', hzs, s₆⟩ := Cond.merge (file := file) (labels := labels) hfr hfr'
        (spec (tb.val σ)) k m₄
      have hv : Term.val σ (.cond tc ta tb) = tb.val σ := by simp [Term.val, h0]
      rw [hv]
      exact ⟨zs, m₄, fr'', hfr'', fun a ha => (hzs a ha).elim (rd' a) (rd a),
        tch.trans (tch₂.trans (tch'.trans tch₄)), s₁.trans (run.trans (s₃.trans (run'.trans
          (s₅.trans s₆))))⟩
  | .un u t₁, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨an, pa, ag, a, ta, e₁, g, rfl, hg, h₁⟩ := termP_un h
    obtain ⟨ok₁, okr⟩ := ok
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.un u t₁).vars := fun q hq => by simpa [Term.vars] using hq
    obtain ⟨xs, m₁, fr, hfr, rd, tch, run⟩ := termP_runs t₁ h₁ ok₁
      (.effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k) m (locs.sub sub₁)
    obtain ⟨m₂, tch₂, run₂⟩ := Unary.runs (an := an) hg (Term.int_of_ok t₁ ok₁) okr hfr run
    exact ⟨xs, m₂, fr, hfr, rd, tch.trans tch₂, run₂⟩

  | .bit o t₁ t₂, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := termP_bit h
    obtain ⟨ok₁, ok₂⟩ := ok
    let I : Mem.Concrete.State → Prop := fun m => LocsP env m σ pts (.bit o t₁ t₂)
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.bit o t₁ t₂).vars := fun q hq => by
      simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.bit o t₁ t₂).vars := fun q hq => by
      simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT (.mk ag (.pure g)) env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT (.mk ag (.pure g)) env :: k) (annots := au) I hI
      (task_of_runs t₁ h₁ I fun m hm => termP_runs t₁ h₁ ok₁ [] m (hm.sub sub₁))
      (task_of_runs t₂ h₂ I fun m hm => termP_runs t₂ h₂ ok₂ [] m (hm.sub sub₂))
      (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m locs
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val σ), spec (t₂.val σ)]),
          .annotations xs :: .effectBind PAT (.mk ag (.pure g)) env :: k, m₁⟩
        ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b (t₁.val σ) (t₂.val σ) env),
          .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    have i₁ := Term.int_of_ok t₁ ok₁
    have i₂ := Term.int_of_ok t₂ ok₂
    obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag g
      (Guard.operands a b (t₁.val σ) (t₂.val σ) env) (.annotations xs :: k) m₁
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
    have s₅ := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
      (Bitwise.guard_eval hg env i₁ i₂) (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k)
      m₂ rfl
    refine ⟨xs, m₂, [.annotations xs], .inr rfl, rd, tch.trans ⟨l', m₁.lastUsed, rfl⟩,
      s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
    exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)
  | .divpos o d t₁, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, n, rfl, hg, h₁, h₂, hd⟩ := termP_divpos h
    rw [← DivRem.divisor?_val hd] at h₂
    let t₂ : Term := .lit d.val
    have ok₁ : t₁.Ok σ := ok
    let I : Mem.Concrete.State → Prop := fun m => LocsP env m σ pts (.divpos o d t₁)
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.divpos o d t₁).vars := fun q hq => by
      simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT (.mk ag (.pure g)) env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT (.mk ag (.pure g)) env :: k) (annots := au) I hI
      (task_of_runs t₁ h₁ I fun m hm => termP_runs t₁ h₁ ok₁ [] m (hm.sub sub₁))
      (task_of_runs t₂ h₂ I fun m hm => lit_runs h₂ env [] m hm.2.2)
      (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m locs
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val σ), spec (t₂.val σ)]),
          .annotations xs :: .effectBind PAT (.mk ag (.pure g)) env :: k, m₁⟩
        ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b (t₁.val σ) (t₂.val σ) env),
          .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    have i₁ := Term.int_of_ok t₁ ok₁
    obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag g
      (Guard.operands a b (t₁.val σ) (t₂.val σ) env) (.annotations xs :: k) m₁
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
    have s₅ := DivRem.guard_local (file := file) (labels := labels) hg env i₁ d false
      (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k) m₂
    refine ⟨xs, m₂, [.annotations xs], .inr rfl, rd, tch.trans ⟨l', m₁.lastUsed, rfl⟩,
      s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
    exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)

/-- A recognised expression in range is a read-only task. -/
theorem termP_task (t : Term) {e : Eff} (h : termP file pts e = some t) {env : Env} {σ : Key → Int}
    (ok : t.Ok σ) (I : Mem.Concrete.State → Prop) (hs : ∀ m, I m → LocsP env m σ pts t) :
    ReadTask (file := file) (labels := labels) I env e (spec (t.val σ)) :=
  task_of_runs t h I fun m hm => termP_runs t h ok [] m (hs m hm)

/-- **Undefined-behaviour arm.** -/
theorem termP_fails : (t : Term) → {e : Eff} → termP file pts e = some t →
    {env : Env} → {σ : Key → Int} → ¬ t.Ok σ → ∀ (k : List Frame) (m : Mem.Concrete.State),
      LocsP env m σ pts t → Fails file labels false ⟨.effectExpr e env, k, m⟩ overflow
  | .lit c, e, h, env, σ, bad, k, m, _ => by
    exact absurd (termP_lit h).2 bad
  | .var q, _, _, _, _, bad, _, _, locs => absurd (locs.1 q (by simp [Term.vars])).1 bad
  | .bin op t₁ t₂, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := termP_bin h
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.bin op t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.bin op t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    let K : List Frame := .effectBind PAT (.mk ag (.pure g)) env :: k
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, K, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    refine ArenaFail.Fails.pre file labels s₁ ?_
    have flag₁ : taskFlag false K [(0, .effectExpr e₁ env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, termP_calls t₁ h₁]
    have flag₀ : taskFlag false K [] = false := by simp [taskFlag]
    by_cases ok₂ : t₂.Ok σ
    · by_cases ok₁ : t₁.Ok σ
      · have okr : ¬ IsInt (Guard.apply op (t₁.val σ) (t₂.val σ)) := fun hr => bad ⟨ok₁, ok₂, hr⟩
        let I : Mem.Concrete.State → Prop := fun m => LocsP env m σ pts (.bin op t₁ t₂)
        have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
        obtain ⟨xs, m₁, -, -, s₂⟩ := unseq_pair (file := file) (labels := labels) (k := K)
          (annots := au) I hI
          (termP_task t₁ h₁ ok₁ I (fun _ hm => hm.sub sub₁))
          (termP_task t₂ h₂ ok₂ I (fun _ hm => hm.sub sub₂))
          (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m locs
        have s₃ : LocalReaches file labels false
            ⟨.value (.tuple [spec (t₁.val σ), spec (t₂.val σ)]), .annotations xs :: K, m₁⟩
            ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b (t₁.val σ) (t₂.val σ) env),
              .annotations xs :: k, m₁⟩ :=
          .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
            (LoadTask.plain_effectExpr _ _))
        obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag g
          (Guard.operands a b (t₁.val σ) (t₂.val σ) env) (.annotations xs :: k) m₁
        obtain ⟨k', s₅, hend⟩ := Guard.guard_fails (labels := labels) hg env (Term.int_of_ok t₁ ok₁)
          (Term.int_of_ok t₂ ok₂) okr false
          (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k)
          {m₁ with currentLocation := l'}
        refine ⟨_, s₂.trans (s₃.trans (s₄.trans s₅)), ?_, Or.inl hend⟩
        intro v h
        cases h
      · obtain ⟨xs, m', fr, hfr, -, tch, run⟩ := termP_runs (file := file) (labels := labels) t₂ h₂
          ok₂ [] m (locs.sub sub₂)
        refine ArenaFail.fail_pair file labels (.inr ⟨spec (t₂.val σ), xs, m', ?_, ?_⟩)
        · rw [flag₁]
          refine ⟨fr, by simpa using run, ?_⟩
          rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
        · rw [flag₀]
          exact termP_fails t₁ h₁ ok₁ [] m' ((locs.sub sub₁).touched tch)
    · refine ArenaFail.fail_pair file labels (.inl ?_)
      rw [flag₁]
      exact termP_fails t₂ h₂ ok₂ [] m (locs.sub sub₂)
  | .cmp rl c₁ c₂ t₁ t₂, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, a, b, ta, tb, e₁, e₂, KC, rfl, hK, h₁, h₂⟩ := termP_cmp h
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.cmp rl c₁ c₂ t₁ t₂).vars := fun q hq => by
      simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.cmp rl c₁ c₂ t₁ t₂).vars := fun q hq => by
      simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    let K : List Frame := .effectBind PAT KC env :: k
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) KC)) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, K, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    refine ArenaFail.Fails.pre file labels s₁ ?_
    have flag₁ : taskFlag false K [(0, .effectExpr e₁ env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, termP_calls t₁ h₁]
    have flag₀ : taskFlag false K [] = false := by simp [taskFlag]
    by_cases ok₂ : t₂.Ok σ
    · by_cases ok₁ : t₁.Ok σ
      · exact absurd ⟨ok₁, ok₂, hK.int⟩ bad
      · obtain ⟨xs, m', fr, hfr, -, tch, run⟩ := termP_runs (file := file) (labels := labels) t₂ h₂
          ok₂ [] m (locs.sub sub₂)
        refine ArenaFail.fail_pair file labels (.inr ⟨spec (t₂.val σ), xs, m', ?_, ?_⟩)
        · rw [flag₁]
          refine ⟨fr, by simpa using run, ?_⟩
          rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
        · rw [flag₀]
          exact termP_fails t₁ h₁ ok₁ [] m' ((locs.sub sub₁).touched tch)
    · refine ArenaFail.fail_pair file labels (.inl ?_)
      rw [flag₁]
      exact termP_fails t₂ h₂ ok₂ [] m (locs.sub sub₂)
  | .cond tc ta tb, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨ec, ea, eb, bk, h₁, h₂, h₃, fresh, hpb, -, cr⟩ := termP_cond h
    have subc : ∀ q ∈ tc.vars, q ∈ (Term.cond tc ta tb).vars := fun q hq => by simp [Term.vars, hq]
    have suba : ∀ q ∈ ta.vars, q ∈ (Term.cond tc ta tb).vars := fun q hq => by simp [Term.vars, hq]
    have subb : ∀ q ∈ tb.vars, q ∈ (Term.cond tc ta tb).vars := fun q hq => by simp [Term.vars, hq]
    have fresh' : ∀ q ∈ bk, q ∉ (Term.cond tc ta tb).vars := fun q hq => by
      simpa [Term.vars, List.append_assoc] using fresh q hq
    obtain ⟨K, s₁, rest⟩ := cr labels env k m
    refine ArenaFail.Fails.pre file labels s₁ ?_
    by_cases okc : tc.Ok σ
    · obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := termP_runs tc h₁ okc (K :: k) m (locs.sub subc)
      obtain ⟨env₂, KB, m₂, hx₂, tch₂, s₃, -⟩ := rest (tc.val σ) fr xs hfr m₁
      refine ArenaFail.Fails.pre file labels (run.trans s₃) ?_
      have locs₂ : LocsP env₂ m₂ σ pts (.cond tc ta tb) :=
        (locs.touched (tch.trans tch₂)).env fresh' hpb hx₂
      by_cases h0 : tc.val σ = 0
      · have okb : ¬ ta.Ok σ := fun o => bad ⟨okc, by rw [ite_eq_left h0]; exact o⟩
        rw [ite_eq_left h0]
        exact termP_fails ta h₂ okb (KB :: (fr ++ k)) m₂ (locs₂.sub suba)
      · have okb : ¬ tb.Ok σ := fun o => bad ⟨okc, by rw [ite_eq_right h0]; exact o⟩
        rw [ite_eq_right h0]
        exact termP_fails tb h₃ okb (KB :: (fr ++ k)) m₂ (locs₂.sub subb)
    · exact termP_fails tc h₁ okc (K :: k) m (locs.sub subc)
  | .un u t₁, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨an, pa, ag, a, ta, e₁, g, rfl, hg, h₁⟩ := termP_un h
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.un u t₁).vars := fun q hq => by simpa [Term.vars] using hq
    by_cases ok₁ : t₁.Ok σ
    · have okr : ¬ IsInt (u.apply (t₁.val σ)) := fun hr => bad ⟨ok₁, hr⟩
      obtain ⟨xs, m₁, fr, hfr, -, -, run⟩ := termP_runs (file := file) (labels := labels) t₁ h₁ ok₁
        (.effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k) m (locs.sub sub₁)
      exact Unary.fails (an := an) hg (Term.int_of_ok t₁ ok₁) okr hfr run
    · refine ArenaFail.Fails.pre file labels
        (.single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false)
          (LoadTask.plain_effectExpr _ _))) ?_
      exact termP_fails t₁ h₁ ok₁ _ m (locs.sub sub₁)

  | .bit o t₁ t₂, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := termP_bit h
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.bit o t₁ t₂).vars := fun q hq => by
      simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.bit o t₁ t₂).vars := fun q hq => by
      simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    let K : List Frame := .effectBind PAT (.mk ag (.pure g)) env :: k
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, K, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    refine ArenaFail.Fails.pre file labels s₁ ?_
    have flag₁ : taskFlag false K [(0, .effectExpr e₁ env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, termP_calls t₁ h₁]
    have flag₀ : taskFlag false K [] = false := by simp [taskFlag]
    by_cases ok₂ : t₂.Ok σ
    · by_cases ok₁ : t₁.Ok σ
      · exact absurd ⟨ok₁, ok₂⟩ bad
      · obtain ⟨xs, m', fr, hfr, -, tch, run⟩ := termP_runs (file := file) (labels := labels) t₂ h₂
          ok₂ [] m (locs.sub sub₂)
        refine ArenaFail.fail_pair file labels (.inr ⟨spec (t₂.val σ), xs, m', ?_, ?_⟩)
        · rw [flag₁]
          refine ⟨fr, by simpa using run, ?_⟩
          rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
        · rw [flag₀]
          exact termP_fails t₁ h₁ ok₁ [] m' ((locs.sub sub₁).touched tch)
    · refine ArenaFail.fail_pair file labels (.inl ?_)
      rw [flag₁]
      exact termP_fails t₂ h₂ ok₂ [] m (locs.sub sub₂)
  | .divpos o d t₁, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, n, rfl, hg, h₁, h₂, hd⟩ := termP_divpos h
    rw [← DivRem.divisor?_val hd] at h₂
    let t₂ : Term := .lit d.val
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    let K : List Frame := .effectBind PAT (.mk ag (.pure g)) env :: k
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, K, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    refine ArenaFail.Fails.pre file labels s₁ ?_
    obtain ⟨xs, m', fr, hfr, -, tch, run⟩ := lit_runs (file := file) (labels := labels) h₂ env [] m
      locs.2.2
    refine ArenaFail.fail_pair file labels (.inr ⟨spec (t₂.val σ), xs, m', ?_, ?_⟩)
    · have flag : taskFlag false K [(0, .effectExpr e₁ env, [])] = false := by
        simp [taskFlag, Interleave.controlHasCCall_effectExpr, termP_calls t₁ h₁]
      rw [flag]
      refine ⟨fr, by simpa [t₂, Term.val] using run, ?_⟩
      rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
    · have flag : taskFlag false K [] = false := by simp [taskFlag]
      rw [flag]
      exact termP_fails t₁ h₁ bad [] m' (locs.touched tch)

/-! ## Without pointer locals -/

theorem term_calls {file : File Codec.wireModel Unit Unit} :
    (t : Term) → {e : Eff} → term file e = some t → hasCCall e = false :=
  fun t _ h => termP_calls t h

theorem term_runs (t : Term) {e : Eff} (h : term file e = some t) {env : Env} {σ : Key → Int}
    (ok : t.Ok σ) (k : List Frame) (m : Mem.Concrete.State) (locs : Locs env m σ t) :
    ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧
      Touched m m' ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.value (spec (t.val σ)), fr ++ k, m'⟩ :=
  termP_runs t h ok k m ⟨locs, PtsOk.none env m t, PtsNN.none env m⟩

theorem term_task (t : Term) {e : Eff} (h : term file e = some t) {env : Env} {σ : Key → Int}
    (ok : t.Ok σ) (I : Mem.Concrete.State → Prop) (hs : ∀ m, I m → Locs env m σ t) :
    ReadTask (file := file) (labels := labels) I env e (spec (t.val σ)) :=
  termP_task t h ok I fun m hm => ⟨hs m hm, PtsOk.none env m t, PtsNN.none env m⟩

theorem term_fails (t : Term) {e : Eff} (h : term file e = some t) {env : Env} {σ : Key → Int}
    (bad : ¬ t.Ok σ) (k : List Frame) (m : Mem.Concrete.State) (locs : Locs env m σ t) :
    Fails file labels false ⟨.effectExpr e env, k, m⟩ overflow :=
  termP_fails t h bad k m ⟨locs, PtsOk.none env m t, PtsNN.none env m⟩

end Silmaril.Compile.Core.Verified.StateExpr
