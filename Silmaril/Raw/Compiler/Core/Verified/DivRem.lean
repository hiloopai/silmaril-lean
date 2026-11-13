module

public import Silmaril.Compiler.Core.Verified.Guard.Defs
public import Silmaril.Compiler.Core.Verified.Arith.Defs
public import Silmaril.Machine.CBackend.Lir.Syntax.Defs

/-! # Signed division and remainder by a positive `int` constant

This first division fragment restricts the divisor to a positive literal. Consequently neither
zero division nor the `INT_MIN / -1` exceptional case can occur. The dividend is computed at
run time, including its sign; both operations truncate toward zero, as Cerberus requires.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.DivRem

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval)
open ConvInt (IsInt Pure)
open Silmaril.Machine

/-- The two operations share the representability check on the quotient. -/
inductive Op where
  | quot
  | rem
  deriving DecidableEq

/-- A positive divisor representable as a C `int`. -/
structure Divisor where
  val : Nat
  positive : 0 < val
  bounded : val ≤ 2147483647

/-- Read a positive C `int` literal as a machine-safe divisor. -/
def divisor? (n : Int) : Option Divisor :=
  if h : 0 < n ∧ n ≤ 2147483647 then
    some ⟨n.toNat, by omega, by omega⟩
  else none

theorem divisor?_val {n : Int} {d : Divisor} (h : divisor? n = some d) : (d.val : Int) = n := by
  unfold divisor? at h
  split at h
  · rename_i hn
    cases h
    simp only [Int.natCast_toNat_eq_self, hn.1.le]
  · cases h

/-- Truncation toward zero, including for a negative dividend. -/
def Op.apply : Op → Int → Int → Int
  | .quot, x, y => x.tdiv y
  | .rem, x, y => x.tmod y

/-- Dividing an `int` by a positive `int` cannot overflow. -/
theorem quotient_int {x : Int} (hx : IsInt x) (d : Divisor) : IsInt (x.tdiv d.val) := by
  have hd : (0 : Int) ≤ d.val := by omega
  by_cases h : 0 ≤ x
  · have lo := Int.tdiv_nonneg h hd
    have hi := Int.tdiv_le_self (d.val : Int) h
    exact ⟨by omega, by obtain ⟨_, hi'⟩ := hx; omega⟩
  · have lo := Int.tdiv_nonneg (a := -x) (by omega) hd
    have hi := Int.tdiv_le_self (d.val : Int) (a := -x) (by omega)
    rw [Int.neg_tdiv] at lo hi
    obtain ⟨hl, hh⟩ := hx
    exact ⟨by omega, by omega⟩

/-- Remainder stays in the range of the dividend, with its sign. -/
theorem remainder_int {x : Int} (_hx : IsInt x) (d : Divisor) : IsInt (x.tmod d.val) := by
  have hd : (0 : Int) < d.val := by have := d.positive; omega
  have bound := d.bounded
  by_cases h : 0 ≤ x
  · have lo := Int.tmod_nonneg (d.val : Int) h
    have hi := Int.tmod_lt_of_pos x hd
    exact ⟨by omega, by omega⟩
  · have lo := Int.tmod_nonneg (d.val : Int) (a := -x) (by omega)
    have hi := Int.tmod_lt_of_pos (-x) hd
    rw [Int.neg_tmod] at lo hi
    exact ⟨by omega, by omega⟩

theorem apply_int (o : Op) {x : Int} (hx : IsInt x) (d : Divisor) : IsInt (o.apply x d.val) := by
  cases o
  · exact quotient_int hx d
  · exact remainder_int hx d

/-- The matching signed Lir instruction. -/
def Op.lir : Op → Lir.Binop
  | .quot => .divs
  | .rem => .rems

/-- Every machine dividend is safe with this positive constant divisor, including words
produced while evaluating a source branch that is not selected. -/
theorem lir_some (o : Op) (x : Lir.Word) (d : Divisor) :
    ∃ z, o.lir.eval x (BitVec.ofNat 64 d.val) = some z := by
  have hdn : d.val < 2 ^ 64 := by have := d.bounded; omega
  have hn : BitVec.ofNat 64 d.val ≠ 0 := by
    intro h
    have hh := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at hh
    have := d.positive
    omega
  have hm : BitVec.ofNat 64 d.val ≠ -1 := by
    intro h
    have hh := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at hh
    have := d.bounded
    omega
  cases o <;>
    simp only [Op.lir, Lir.Binop.eval, Lir.divOp, hn, hm, and_false, ↓reduceIte]
  all_goals exact ⟨_, rfl⟩

/-- The signed instructions compute the Core integer result on representable dividends. -/
theorem lir_eval (o : Op) {x : Int} (hx : IsInt x) (d : Divisor) :
    o.lir.eval (BitVec.ofInt 64 x) (BitVec.ofNat 64 d.val) =
      some (BitVec.ofInt 64 (o.apply x d.val)) := by
  have hd : IsInt (d.val : Int) := ⟨by omega, by have := d.bounded; omega⟩
  have hd0 : d.val ≠ 0 := by have := d.positive; omega
  cases o
  · simpa only [Op.lir, Op.apply, BitVec.ofInt_natCast] using
      (Arith.aop_sound (op := .div) (n := x.tdiv d.val) (pa := (-2147483648, 2147483647))
        (pb := (-2147483648, 2147483647)) (by decide) hx hd
        (by simp [Arith.AOp.eval, hd0]))
  · simpa only [Op.lir, Op.apply, BitVec.ofInt_natCast] using
      (Arith.aop_sound (op := .rem) (n := x.tmod d.val) (pa := (-2147483648, 2147483647))
        (pb := (-2147483648, 2147483647)) (by decide) hx hd
        (by simp [Arith.AOp.eval, hd0]))

/-- The integer operator in the final specified result. -/
def op? : BinOp → Option Op
  | .div => some .quot
  | .remT => some .rem
  | _ => none

/-- The checked standard-library integer representability predicate. -/
def representable (file : File Codec.wireModel Unit Unit) (r : Sym) : Bool :=
  match ConvInt.lookupFun file r with
  | some d => ConvInt.isRepresentable d
  | none => false

/-- The quotient-representability and zero-divisor checks after conversion of the operands.
The undefined arms are unreachable for our positive divisor and `int` dividend. -/
def result (file : File Codec.wireModel Unit Unit) (x y : Sym) : Pure → Option Op
  | .mk _ () (.if_ (.mk _ () (.op .eq (.mk _ () (.sym y₀))
        (.mk _ () (.val (.object (.integer 0)))))) _
      (.mk _ () (.if_ (.mk _ () (.call (.sym r)
        [.mk _ () (.op .div (.mk _ () (.sym x₁)) (.mk _ () (.sym y₁))),
         .mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int))))))]))
        (.mk _ () (.ctor .specified [.mk _ () (.op op (.mk _ () (.sym x₂)) (.mk _ () (.sym y₂)))]))
        _))) =>
      if decide (y₀.key = y.key ∧ x₁.key = x.key ∧ y₁.key = y.key ∧
          x₂.key = x.key ∧ y₂.key = y.key) &&
          representable file r then op? op else none
  | _ => none

theorem op?_primitive {op : BinOp} {o : Op} (h : op? op = some o)
    (x : Int) (d : Divisor) (tags : Mem.Concrete.Tags) :
    primitive (.bin op) [.object (.integer x), .object (.integer d.val)] tags =
      .ok (integer (o.apply x d.val)) := by
  have hd0 : d.val ≠ 0 := by have := d.positive; omega
  cases op <;> simp [op?] at h <;> cases h <;>
    simp [primitive, integerBin, Op.apply, hd0, pure, Except.pure]

/-- The result guard's defined path: the zero test is false and the quotient fits `int`. -/
theorem result_eval {file : Program} {tags : Mem.Concrete.Tags} {x y : Sym} {p : Pure} {o : Op}
    (h : result file x y p = some o) (env : Env) {n : Int} (hn : IsInt n) (d : Divisor)
    (hx : env.lookup x = some (.object (.integer n)))
    (hy : env.lookup y = some (.object (.integer d.val))) :
    Eval file tags env (.inl p) (.inl (.loaded (.specified (.integer (o.apply n d.val))))) := by
  have lx : ∀ {s : Sym}, s.key = x.key → env.lookup s = some (.object (.integer n)) := by
    intro s hs
    rw [ReturnLit.lookup_key hs]
    exact hx
  have ly : ∀ {s : Sym}, s.key = y.key → env.lookup s = some (.object (.integer d.val)) := by
    intro s hs
    rw [ReturnLit.lookup_key hs]
    exact hy
  have hd : d.val ≠ 0 := by have := d.positive; omega
  unfold result at h
  split at h
  · split at h
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨⟨e0, e1, e2, e3, e4⟩, hr⟩ := cond
      unfold representable at hr
      split at hr
      · rename_i df hl
        refine .ifFalse (.op (.cons (.sym (ly e0)) (.cons .val .nil)) ?_) (.ifTrue ?_ ?_)
        · simp [primitive, integerBin, boolean, runtimeValue, runtimeObject, hd, pure, Except.pure]
        · exact ConvInt.isRepresentable_eval hl hr (quotient_int hn d)
            (.cons (.op (.cons (.sym (lx e1)) (.cons (.sym (ly e2)) .nil))
              (by simp [primitive, integerBin, integer, pure, Except.pure])) (.cons .val .nil))
        · exact .ctor (.cons (.op (.cons (.sym (lx e3)) (.cons (.sym (ly e4)) .nil))
            (op?_primitive h n d tags)) .nil) (by simp [primitive, integer]; rfl)
      · cases hr
    · cases h
  · cases h

/-- A pure let of a converted operand, over any continuation. -/
theorem let_local {file : Program} {labels : Labels} {tags : Mem.Concrete.Tags}
    {env : Env} {p body : Pure} {pat : Pattern Sym} {v : Val} {xs : Bindings}
    (hp : Eval file tags env (.inl p) (.inl v)) (hm : matchPattern pat v = some xs)
    (ann : List Annot) (wc : Bool) (k : List Frame) (m : Mem.Concrete.State)
    (ht : PureEval.tagsOf file m = tags) :
    Interleave.LocalReaches file labels wc
      ⟨.pureExpr (.mk ann () (.let_ pat p body)) env, k, m⟩
      ⟨.pureExpr body (extendEnv xs env), k, m⟩ := by
  refine .head (.next (c' := .pureExpr p env) (k' := .pureBind pat body env :: k)
    (by rw [requestAux.eq_def]; simp [awaitsScheduling]) (PureLocal.plain_pureExpr _ _)) ?_
  refine (PureLocal.eval_local file tags hp (.pureBind pat body env :: k) m ht).tail ?_
  exact .next (by rw [requestAux.eq_def]; simp [awaitsScheduling, hm])
    (PureLocal.plain_pureExpr _ _)

/-- Conversion of the two specified operands, then the result guard. -/
def body (file : File Codec.wireModel Unit Unit) (x y : Sym) : Pure → Option Op
  | .mk _ () (.let_ (.mk _ (.base (some u, _))) p
      (.mk _ () (.let_ (.mk _ (.base (some v, _))) q r))) =>
      if decide (u.key ≠ y.key ∧ v.key ≠ u.key) && Guard.convOf file x p &&
          Guard.convOf file y q then result file u v r else none
  | _ => none

/-- Converted operands preserve the C `int` values, then the checked guard computes the result. -/
theorem body_local {file : Program} {labels : Labels} {env : Env} {x y : Sym} {p : Pure} {o : Op}
    (h : body file x y p = some o) {n : Int} (hn : IsInt n) (d : Divisor)
    (hx : env.lookup x = some (.object (.integer n)))
    (hy : env.lookup y = some (.object (.integer d.val)))
    (wc : Bool) (k : List Frame) (m : Mem.Concrete.State) :
    Interleave.LocalReaches file labels wc ⟨.pureExpr p env, k, m⟩
      ⟨.value (.loaded (.specified (.integer (o.apply n d.val)))), k, m⟩ := by
  unfold body at h
  split at h
  · split at h
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨⟨⟨une, vne⟩, cp⟩, cq⟩ := cond
      have hd : IsInt (d.val : Int) := ⟨by omega, by have := d.bounded; omega⟩
      refine (let_local (Guard.convOf_eval cp hn hx) (by simp [matchPattern]; rfl)
        _ wc k m rfl).trans ?_
      refine (let_local (Guard.convOf_eval cq hd ?_) (by simp [matchPattern]; rfl)
        _ wc k m rfl).trans ?_
      · rw [ConvInt.lookup_one_other (Ne.symm une)]
        exact hy
      · refine PureLocal.eval_local file (PureEval.tagsOf file m)
          (result_eval h _ hn d ?_ (ConvInt.lookup_one rfl)) k m rfl
        rw [ConvInt.lookup_one_other (Ne.symm vne)]
        exact ConvInt.lookup_one rfl
    · cases h
  · cases h

/-- The ordinary specified/specified arm after Cerberus's two unspecified-operand arms. -/
def guard (file : File Codec.wireModel Unit Unit) (a b : Sym) : Pure → Option Op
  | .mk _ () (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym b')]))
      ((.mk _ (.ctor .tuple [.mk _ (.ctor .unspecified _), _]), _) ::
       (.mk _ (.ctor .tuple [.mk _ (.base (none, _)), .mk _ (.ctor .unspecified _)]), _) ::
       (.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
         .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]), p) :: _)) =>
      if a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧ y.key ≠ x.key then
        body file x y p else none
  | _ => none

/-- Selecting a pure case follows the Core machine, over any continuation. -/
theorem case_local {file : Program} {labels : Labels} {tags : Mem.Concrete.Tags}
    {env : Env} {p body : Pure} {bs : List (Pattern Sym × Pure)} {v : Val} {xs : Bindings}
    (hp : Eval file tags env (.inl p) (.inl v)) (hm : selectCase v bs = some (xs, body))
    (ann : List Annot) (wc : Bool) (k : List Frame) (m : Mem.Concrete.State)
    (ht : PureEval.tagsOf file m = tags) :
    Interleave.LocalReaches file labels wc
      ⟨.pureExpr (.mk ann () (.case_ p bs)) env, k, m⟩
      ⟨.pureExpr body (extendEnv xs env), k, m⟩ := by
  refine .head (.next (c' := .pureExpr p env) (k' := .pureCase bs env :: k)
    (by rw [requestAux.eq_def]; simp [awaitsScheduling]) (PureLocal.plain_pureExpr _ _)) ?_
  refine (PureLocal.eval_local file tags hp (.pureCase bs env :: k) m ht).tail ?_
  exact .next (by rw [requestAux.eq_def]; simp [awaitsScheduling, hm])
    (PureLocal.plain_pureExpr _ _)

/-- The whole guard computes quotient or remainder for any `int` dividend and positive divisor. -/
theorem guard_local {file : Program} {labels : Labels} {a b : Sym} {p : Pure} {o : Op}
    (h : guard file a b p = some o) (env : Env) {n : Int} (hn : IsInt n) (d : Divisor)
    (wc : Bool) (k : List Frame) (m : Mem.Concrete.State) :
    Interleave.LocalReaches file labels wc
      ⟨.pureExpr p (Guard.operands a b n d.val env), k, m⟩
      ⟨.value (.loaded (.specified (.integer (o.apply n d.val)))), k, m⟩ := by
  unfold guard at h
  split at h
  · split at h
    · rename_i cond
      obtain ⟨e1, e2, ne, ne'⟩ := cond
      refine (case_local (.ctor (.cons (.sym (Guard.lookup_pair_first e1))
        (.cons (.sym (Guard.lookup_pair_second e2 ne)) .nil)) (by simp [primitive]; rfl))
        (by simp [selectCase, matchPattern, matchPatterns]; exact ⟨rfl, rfl⟩)
        _ wc k m rfl).trans ?_
      exact body_local h hn d (Guard.lookup_pair_first rfl) (Guard.lookup_pair_second rfl ne') wc k m
    · cases h
  · cases h

end Silmaril.Compile.Core.Verified.DivRem
