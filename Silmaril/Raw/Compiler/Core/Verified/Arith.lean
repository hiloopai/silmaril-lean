module

public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
public import Silmaril.Cerberus.Mem.Layout.Defs
public import Mathlib.Tactic.NormNum

/-! # Run-time integer arithmetic in Lir, proved against Cerberus's guarded operators

`IExpr` is the integer fragment of Core pure expressions whose operands are run-time values:
registers holding C integers (locals, arguments, loaded values), literals, and Cerberus's
guarded operators `catch_exceptional_condition` (`catchI`, signed arithmetic: overflow is
undefined), `wrapI` (unsigned arithmetic: wrap modulo the type), `conv_int` (`conv`), and the
integer comparisons that elaborated C turns into `0`/`1` (`cmp`). `IExpr.eval` is its value over
the mathematical integers, as the Core dynamics computes it (`Fold.catchInt`, `Fold.wrapInt`,
`Fold.conv` and `Fold.bin`, with the same `wrap`); `none` is undefined behaviour. Division and
remainder (`AOp.div`, `AOp.rem`) are the guarded forms of the elaboration, `if y = 0 then undef
else ...`: a zero divisor is undefined.

A register holds the value `n` as the word `BitVec.ofInt 64 n`, for signed and unsigned types
alike. `gen` compiles an expression to straight-line Lir operations into fresh registers: the
ring operators are 64-bit `add`/`sub`/`mul` (exact modulo `2^64`, which is all `catch` and `wrap`
need), `wrapI` and `conv` then narrow with a sign or zero extension, division, remainder and
comparisons pick the signed or unsigned Lir operator from the operands' static ranges (and refuse
operands that fit neither, and signed dividends that can be `-2^63`).

`gen_sound`: when the expression has a value `v`, the generated operations run (they never get
stuck, never touch memory or the registers below `next`) and leave `ofInt 64 v` in the result
register. Nothing is evaluated at compile time except literals: this is the code that computes
the expression at run time.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Arith

open Silmaril.Machine

/-! ## Integer kinds and wrapping -/

/-- The integer types of LP64 by width and signedness. -/
inductive Kind where
  | s8 | u8 | s16 | u16 | s32 | u32 | s64 | u64
  deriving DecidableEq, Repr

def Kind.lo : Kind → Int
  | .s8 => -128 | .s16 => -32768 | .s32 => -2147483648 | .s64 => -9223372036854775808
  | .u8 | .u16 | .u32 | .u64 => 0

def Kind.hi : Kind → Int
  | .s8 => 127 | .s16 => 32767 | .s32 => 2147483647 | .s64 => 9223372036854775807
  | .u8 => 255 | .u16 => 65535 | .u32 => 4294967295 | .u64 => 18446744073709551615

/-- Reduction into `[lo, hi]` modulo `hi - lo + 1`, as `Fold.wrap` and the dynamics' `wrapI`. -/
def wrap (lo hi n : Int) : Int :=
  let r := n % (hi - lo + 1)
  if r ≤ hi then r else r - (hi - lo + 1)

/-- The Lir operation that narrows a 64-bit word to a kind; none for the 64-bit kinds. -/
def Kind.norm : Kind → Option Lir.Unop
  | .s8 => some .sext8 | .u8 => some .zext8 | .s16 => some .sext16 | .u16 => some .zext16
  | .s32 => some .sext32 | .u32 => some .zext32 | .s64 | .u64 => none

def Kind.normWord (k : Kind) (w : Lir.Word) : Lir.Word :=
  match k.norm with
  | some u => u.eval w
  | none => w

theorem Kind.wrap_mem (k : Kind) (n : Int) : k.lo ≤ wrap k.lo k.hi n ∧ wrap k.lo k.hi n ≤ k.hi := by
  cases k <;> simp only [Kind.lo, Kind.hi, wrap] <;> norm_num <;> split <;> omega

theorem Kind.normWord_ofInt (k : Kind) (n : Int) :
    k.normWord (BitVec.ofInt 64 n) = BitVec.ofInt 64 (wrap k.lo k.hi n) := by
  cases k <;> simp only [Kind.normWord, Kind.norm, Kind.lo, Kind.hi, Lir.Unop.eval, Lir.of32, Lir.lo32]
  all_goals first
    | (apply BitVec.eq_of_toInt_eq
       rw [BitVec.toInt_signExtend, BitVec.toInt_setWidth, BitVec.toNat_ofInt, BitVec.toInt_ofInt]
       rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
       simp only [wrap, Int.bmod_def]
       norm_num
       split <;> split <;> split <;> omega)
    | (apply BitVec.eq_of_toNat_eq
       rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
       simp only [wrap]
       norm_num
       split <;> omega)
    | (apply BitVec.eq_of_toInt_eq
       rw [BitVec.toInt_ofInt, BitVec.toInt_ofInt]
       simp only [wrap, Int.bmod_def]
       norm_num
       split <;> split <;> split <;> omega)

/-- The kind of an LP64 layout (width in bytes, signedness). -/
def Kind.ofLayout : Nat × Bool → Option Kind
  | (1, true) => some .s8 | (1, false) => some .u8
  | (2, true) => some .s16 | (2, false) => some .u16
  | (4, true) => some .s32 | (4, false) => some .u32
  | (8, true) => some .s64 | (8, false) => some .u64
  | _ => none

/-- The kind of a Cerberus integer type. `_Bool` (which converts by comparison with zero),
`wchar_t` and `wint_t` (whose bounds are not those of their layout) and enums have none. -/
def Kind.ofIntegerType (ty : Cerberus.IntegerType) : Option Kind :=
  match ty with
  | .bool | .wchar | .wint | .enum _ => none
  | _ => Cerberus.Mem.Concrete.integerLayout ty >>= Kind.ofLayout

theorem Kind.ofLayout_bounds {w : Nat} {s : Bool} {k : Kind} (h : Kind.ofLayout (w, s) = some k) :
    (if s then (-((256 : Int) ^ w) / 2, (256 : Int) ^ w / 2 - 1) else (0, (256 : Int) ^ w - 1)) =
      (k.lo, k.hi) := by
  unfold Kind.ofLayout at h
  split at h <;> cases h <;>
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [Kind.lo, Kind.hi]

/-- The bounds of a kind are Cerberus's LP64 bounds of its integer type. -/
theorem Kind.ofIntegerType_bounds {ty : Cerberus.IntegerType} {k : Kind}
    (h : Kind.ofIntegerType ty = some k) :
    Cerberus.Mem.Concrete.integerBounds ty = some (k.lo, k.hi) := by
  cases ty <;> simp only [Kind.ofIntegerType, reduceCtorEq] at h <;>
  · obtain ⟨⟨w, s⟩, hl, hk⟩ := Option.bind_eq_some_iff.1 h
    simp only [Cerberus.Mem.Concrete.integerBounds, hl, Option.bind_eq_bind, Option.bind_some,
      ← Kind.ofLayout_bounds hk]
    rfl

/-! ## Expressions -/

/-- The arithmetic operators. `div` and `rem` are truncating and guarded by the elaboration's
zero-divisor test. -/
inductive AOp where
  | add | sub | mul | div | rem
  deriving DecidableEq, Repr

def AOp.eval : AOp → Int → Int → Option Int
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x.tdiv y)
  | .rem, x, y => if y = 0 then none else some (x.tmod y)

/-- The integer comparisons. -/
inductive Rel where
  | eq | lt | le | gt | ge
  deriving DecidableEq, Repr

def Rel.eval : Rel → Int → Int → Bool
  | .eq, x, y => x == y
  | .lt, x, y => decide (x < y)
  | .le, x, y => decide (x ≤ y)
  | .gt, x, y => decide (x > y)
  | .ge, x, y => decide (x ≥ y)

/-- Integer expressions over registers. `var r lo hi` is register `r`, holding a value in
`[lo, hi]`. -/
inductive IExpr where
  | var (r : Nat) (lo hi : Int)
  | lit (n : Int)
  | catchI (k : Kind) (op : AOp) (a b : IExpr)
  | wrapI (k : Kind) (op : AOp) (a b : IExpr)
  | conv (k : Kind) (a : IExpr)
  | cmp (rel : Rel) (a b : IExpr)
  deriving DecidableEq, Repr

namespace IExpr

/-- The value under the register values `ρ`; `none` is undefined behaviour. -/
def eval (ρ : Nat → Int) : IExpr → Option Int
  | .var r _ _ => some (ρ r)
  | .lit n => some n
  | .catchI k op a b => do
      let n ← op.eval (← a.eval ρ) (← b.eval ρ)
      if k.lo ≤ n ∧ n ≤ k.hi then some n else none
  | .wrapI k op a b => do
      let n ← op.eval (← a.eval ρ) (← b.eval ρ)
      some (wrap k.lo k.hi n)
  | .conv k a => do some (wrap k.lo k.hi (← a.eval ρ))
  | .cmp rel a b => do some (if rel.eval (← a.eval ρ) (← b.eval ρ) then 1 else 0)

/-- Static bounds of the value. -/
def range : IExpr → Int × Int
  | .var _ lo hi => (lo, hi)
  | .lit n => (n, n)
  | .catchI k _ _ _ | .wrapI k _ _ _ | .conv k _ => (k.lo, k.hi)
  | .cmp _ _ _ => (0, 1)

/-- The registers of the variables lie below `bound`, hold their values, and the values lie in
the declared ranges. -/
def VarsOk (ρ : Nat → Int) (fr : Lir.Frame Nat) (bound : Nat) : IExpr → Prop
  | .var r lo hi => r < bound ∧ lo ≤ ρ r ∧ ρ r ≤ hi ∧ fr.get r = some (BitVec.ofInt 64 (ρ r))
  | .lit _ => True
  | .catchI _ _ a b | .wrapI _ _ a b | .cmp _ a b => a.VarsOk ρ fr bound ∧ b.VarsOk ρ fr bound
  | .conv _ a => a.VarsOk ρ fr bound

theorem VarsOk.mono {ρ : Nat → Int} {fr fr' : Lir.Frame Nat} {bound bound' : Nat}
    (hle : bound ≤ bound') (hfr : ∀ r, r < bound → fr'.get r = fr.get r) {e : IExpr}
    (h : e.VarsOk ρ fr bound) : e.VarsOk ρ fr' bound' := by
  induction e with
  | var r lo hi =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by omega, h2, h3, by rw [hfr r h1, h4]⟩
  | lit _ => trivial
  | catchI _ _ a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | wrapI _ _ a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | conv _ a iha => exact iha h
  | cmp _ a b iha ihb => exact ⟨iha h.1, ihb h.2⟩

theorem eval_range {ρ : Nat → Int} {fr : Lir.Frame Nat} {bound : Nat} :
    ∀ {e : IExpr} {v : Int}, e.VarsOk ρ fr bound → e.eval ρ = some v →
      e.range.1 ≤ v ∧ v ≤ e.range.2
  | .var r lo hi, v, ⟨_, h2, h3, _⟩, h => by
    simp only [eval, Option.some.injEq] at h; subst h; exact ⟨h2, h3⟩
  | .lit n, v, _, h => by
    simp only [eval, Option.some.injEq] at h; subst h; exact ⟨le_refl _, le_refl _⟩
  | .catchI k op a b, v, _, h => by
    simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, _, y, _, n, _, h⟩ := h
    split at h
    · cases h; simp only [range]; omega
    · cases h
  | .wrapI k op a b, v, _, h => by
    simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, y, _, n, _, h⟩ := h
    subst h; exact k.wrap_mem n
  | .conv k a, v, _, h => by
    simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, h⟩ := h
    subst h; exact k.wrap_mem x
  | .cmp rel a b, v, _, h => by
    simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, y, _, h⟩ := h
    subst h; simp only [range]; split <;> omega

end IExpr

/-! ## Representation of values in words -/

/-- Every value of the range is a signed 64-bit integer. -/
def SFits (p : Int × Int) : Bool := decide (-9223372036854775808 ≤ p.1) && decide (p.2 < 9223372036854775808)

/-- Every value of the range is an unsigned 64-bit integer. -/
def UFits (p : Int × Int) : Bool := decide (0 ≤ p.1) && decide (p.2 < 18446744073709551616)

theorem toInt_ofInt_of_fits {v : Int} (h1 : -9223372036854775808 ≤ v) (h2 : v < 9223372036854775808) :
    (BitVec.ofInt 64 v).toInt = v := by
  rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)

theorem ofInt_eq_ofNat {v : Int} (h1 : 0 ≤ v) : BitVec.ofInt 64 v = BitVec.ofNat 64 v.toNat := by
  rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg h1]

theorem ofBool_eq (b : Bool) : Lir.ofBool b = BitVec.ofInt 64 (if b then 1 else 0) := by
  cases b <;> decide

/-! ## Operator selection and its correctness -/

/-- The Lir operator of an arithmetic operator on operands with ranges `pa`, `pb`. Signed
division needs a dividend above `-2^63` (`-2^63 / -1` is stuck in Lir). -/
def aop (op : AOp) (pa pb : Int × Int) : Option Lir.Binop :=
  match op with
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div =>
    if SFits pa && SFits pb && decide (-9223372036854775808 < pa.1) then some .divs
    else if UFits pa && UFits pb then some .divu else none
  | .rem =>
    if SFits pa && SFits pb && decide (-9223372036854775808 < pa.1) then some .rems
    else if UFits pa && UFits pb then some .remu else none

/-- The Lir condition of a comparison on operands with ranges `pa`, `pb`. -/
def cond (rel : Rel) (pa pb : Int × Int) : Option Lir.Cond :=
  if SFits pa && SFits pb then
    some (match rel with | .eq => .eq | .lt => .lts | .le => .les | .gt => .gts | .ge => .ges)
  else if UFits pa && UFits pb then
    some (match rel with | .eq => .eq | .lt => .ltu | .le => .leu | .gt => .gtu | .ge => .geu)
  else none

theorem mem_of {p : Int × Int} {x : Int} (h : p.1 ≤ x ∧ x ≤ p.2) : p.1 ≤ x ∧ x ≤ p.2 := h

theorem aop_sound {op : AOp} {pa pb : Int × Int} {bo : Lir.Binop} (hbo : aop op pa pb = some bo)
    {x y n : Int} (hx : pa.1 ≤ x ∧ x ≤ pa.2) (hy : pb.1 ≤ y ∧ y ≤ pb.2) (hn : op.eval x y = some n) :
    bo.eval (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = some (BitVec.ofInt 64 n) := by
  cases op with
  | add =>
    simp only [aop, Option.some.injEq] at hbo; subst hbo
    simp only [AOp.eval, Option.some.injEq] at hn; subst hn
    simp [Lir.Binop.eval, BitVec.ofInt_add]
  | sub =>
    simp only [aop, Option.some.injEq] at hbo; subst hbo
    simp only [AOp.eval, Option.some.injEq] at hn; subst hn
    simp [Lir.Binop.eval, sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
  | mul =>
    simp only [aop, Option.some.injEq] at hbo; subst hbo
    simp only [AOp.eval, Option.some.injEq] at hn; subst hn
    simp [Lir.Binop.eval, BitVec.ofInt_mul]
  | div =>
    simp only [AOp.eval] at hn
    split at hn
    · cases hn
    rename_i hy0
    cases hn
    simp only [aop] at hbo
    split at hbo
    · rename_i hs
      cases hbo
      simp only [SFits, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, ha3⟩ := hs
      have ex := toInt_ofInt_of_fits (v := x) (by omega) (by omega)
      have ey := toInt_ofInt_of_fits (v := y) (by omega) (by omega)
      have hz : ¬ BitVec.ofInt 64 y = 0 := fun h => hy0 (by rw [← ey, h]; rfl)
      have hm : ¬ (BitVec.ofInt 64 x = BitVec.intMin 64 ∧ BitVec.ofInt 64 y = -1) := fun h => by
        have := congrArg BitVec.toInt h.1
        rw [ex, BitVec.toInt_intMin] at this
        norm_num at this
        omega
      simp only [Lir.Binop.eval, Lir.divOp, hz, hm, ↓reduceIte, Bool.false_eq_true]
      congr 1
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_sdiv, ex, ey, BitVec.toInt_ofInt]
    · split at hbo
      · rename_i _ hu
        cases hbo
        simp only [UFits, Bool.and_eq_true, decide_eq_true_eq] at hu
        obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hu
        obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : Int) ≤ x)
        obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : Int) ≤ y)
        rw [← Int.ofNat_tdiv]
        have hz : ¬ BitVec.ofNat 64 b = 0 := fun h => hy0 (by
          have := congrArg BitVec.toNat h
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          simp [this])
        simp only [BitVec.ofInt_natCast, Lir.Binop.eval, Lir.divOp, hz, ↓reduceIte, Bool.false_eq_true]
        congr 1
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
          Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self a b) (by omega))]
      · cases hbo
  | rem =>
    simp only [AOp.eval] at hn
    split at hn
    · cases hn
    rename_i hy0
    cases hn
    simp only [aop] at hbo
    split at hbo
    · rename_i hs
      cases hbo
      simp only [SFits, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, ha3⟩ := hs
      have ex := toInt_ofInt_of_fits (v := x) (by omega) (by omega)
      have ey := toInt_ofInt_of_fits (v := y) (by omega) (by omega)
      have hz : ¬ BitVec.ofInt 64 y = 0 := fun h => hy0 (by rw [← ey, h]; rfl)
      have hm : ¬ (BitVec.ofInt 64 x = BitVec.intMin 64 ∧ BitVec.ofInt 64 y = -1) := fun h => by
        have := congrArg BitVec.toInt h.1
        rw [ex, BitVec.toInt_intMin] at this
        norm_num at this
        omega
      simp only [Lir.Binop.eval, Lir.divOp, hz, hm, ↓reduceIte]
      congr 1
      apply BitVec.eq_of_toInt_eq
      have hm : (x.tmod y).natAbs ≤ x.natAbs := by rw [Int.natAbs_tmod]; exact Nat.mod_le _ _
      rw [BitVec.toInt_srem, ex, ey, toInt_ofInt_of_fits (by omega) (by omega)]
    · split at hbo
      · rename_i _ hu
        cases hbo
        simp only [UFits, Bool.and_eq_true, decide_eq_true_eq] at hu
        obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hu
        obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : Int) ≤ x)
        obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : Int) ≤ y)
        rw [← Int.ofNat_tmod]
        have hz : ¬ BitVec.ofNat 64 b = 0 := fun h => hy0 (by
          have := congrArg BitVec.toNat h
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          simp [this])
        simp only [BitVec.ofInt_natCast, Lir.Binop.eval, Lir.divOp, hz, ↓reduceIte, Bool.false_eq_true]
        congr 1
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
          Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le a b) (by omega))]
      · cases hbo

theorem cond_sound {rel : Rel} {pa pb : Int × Int} {c : Lir.Cond} (hc : cond rel pa pb = some c)
    {x y : Int} (hx : pa.1 ≤ x ∧ x ≤ pa.2) (hy : pb.1 ≤ y ∧ y ≤ pb.2) :
    c.eval (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = rel.eval x y := by
  simp only [cond] at hc
  split at hc
  · rename_i hs
    cases hc
    simp only [SFits, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hs
    have ex := toInt_ofInt_of_fits (v := x) (by omega) (by omega)
    have ey := toInt_ofInt_of_fits (v := y) (by omega) (by omega)
    cases rel <;> simp [Lir.Cond.eval, Rel.eval, ex, ey, ← BitVec.toInt_inj]
  · split at hc
    · rename_i _ hu
      cases hc
      simp only [UFits, Bool.and_eq_true, decide_eq_true_eq] at hu
      obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hu
      obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : Int) ≤ x)
      obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : Int) ≤ y)
      cases rel <;> simp [Lir.Cond.eval, Rel.eval, ← BitVec.toNat_inj] <;> omega
    · cases hc

/-! ## Code generation -/

/-- Narrow register `r` in place to kind `k`. -/
def normOps (k : Kind) (r : Nat) : List (Lir.Op Nat) :=
  match k.norm with
  | some u => [.unary u r r]
  | none => []

/-- Compile an expression whose temporaries are `next, next + 1, ...`: the operations, the
register of the result and the next free register. -/
def gen : Nat → IExpr → Option (List (Lir.Op Nat) × Nat × Nat)
  | next, .var r _ _ => some ([], r, next)
  | next, .lit n => some ([.const next (BitVec.ofInt 64 n)], next, next + 1)
  | next, .catchI _ op a b => do
      let (oa, ra, n1) ← gen next a
      let (ob, rb, n2) ← gen n1 b
      let bo ← aop op a.range b.range
      some (oa ++ ob ++ [.binary bo n2 ra rb], n2, n2 + 1)
  | next, .wrapI k op a b => do
      let (oa, ra, n1) ← gen next a
      let (ob, rb, n2) ← gen n1 b
      let bo ← aop op a.range b.range
      some (oa ++ ob ++ [.binary bo n2 ra rb] ++ normOps k n2, n2, n2 + 1)
  | next, .conv k a => do
      let (oa, ra, n1) ← gen next a
      some (oa ++ [.move n1 ra] ++ normOps k n1, n1, n1 + 1)
  | next, .cmp rel a b => do
      let (oa, ra, n1) ← gen next a
      let (ob, rb, n2) ← gen n1 b
      let c ← cond rel a.range b.range
      some (oa ++ ob ++ [.binary (.cmp c) n2 ra rb], n2, n2 + 1)

theorem normOps_exec (k : Kind) (r : Nat) (fr : Lir.Frame Nat) (m : Lir.Memory) (n : Int)
    (h : fr.get r = some (BitVec.ofInt 64 n)) :
    ∃ fr', Lir.execOps (normOps k r) fr m = some (fr', m) ∧
      fr'.get r = some (BitVec.ofInt 64 (wrap k.lo k.hi n)) ∧ ∀ r', r' ≠ r → fr'.get r' = fr.get r' := by
  have hw := k.normWord_ofInt n
  unfold normOps
  unfold Kind.normWord at hw
  split
  · rename_i u hu
    rw [hu] at hw
    refine ⟨fr.set r (u.eval (BitVec.ofInt 64 n)), ?_, ?_, ?_⟩
    · simp [Lir.execOps, Lir.Op.exec, h]
    · simp [hw]
    · intro r' hr'; simp [hr']
  · rename_i hu
    rw [hu] at hw
    simp only at hw
    exact ⟨fr, rfl, by rw [h, hw], fun _ _ => rfl⟩

/-- **The generated code computes the expression.** -/
theorem gen_sound {ρ : Nat → Int} {m : Lir.Memory} :
    ∀ (e : IExpr) {next : Nat} {ops : List (Lir.Op Nat)} {dst next' : Nat},
    gen next e = some (ops, dst, next') →
    ∀ {fr : Lir.Frame Nat}, e.VarsOk ρ fr next → ∀ {v : Int}, e.eval ρ = some v →
    ∃ fr', Lir.execOps ops fr m = some (fr', m) ∧ fr'.get dst = some (BitVec.ofInt 64 v) ∧
      dst < next' ∧ next ≤ next' ∧ ∀ r, r < next → fr'.get r = fr.get r
  | .var r lo hi, next, ops, dst, next', hg, fr, hok, v, hv => by
    simp only [gen, Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl, rfl⟩ := hg
    simp only [IExpr.eval, Option.some.injEq] at hv; subst hv
    obtain ⟨h1, _, _, h4⟩ := hok
    exact ⟨fr, rfl, h4, h1, le_refl _, fun _ _ => rfl⟩
  | .lit n, next, ops, dst, next', hg, fr, _, v, hv => by
    simp only [gen, Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl, rfl⟩ := hg
    simp only [IExpr.eval, Option.some.injEq] at hv; subst hv
    refine ⟨fr.set next (BitVec.ofInt 64 n), rfl, by simp, by omega, by omega, ?_⟩
    intro r hr; simp [show r ≠ next by omega]
  | .catchI k op a b, next, ops, dst, next', hg, fr, hok, v, hv => by
    simp only [gen, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hg
    obtain ⟨⟨oa, ra, n1⟩, hga, ⟨ob, rb, n2⟩, hgb, bo, hbo, rfl, rfl, rfl⟩ := hg
    dsimp only at hgb ⊢
    simp only [IExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hxa, y, hyb, n, hn, hv⟩ := hv
    split at hv
    · simp only [Option.some.injEq] at hv; subst hv
      obtain ⟨hoka, hokb⟩ := hok
      obtain ⟨f1, hx1, hr1, hra, hle1, hp1⟩ := gen_sound a hga hoka hxa
      obtain ⟨f2, hx2, hr2, hrb, hle2, hp2⟩ := gen_sound b hgb (hokb.mono hle1 hp1) hyb
      have hbe := aop_sound hbo (IExpr.eval_range hoka hxa) (IExpr.eval_range hokb hyb) hn
      refine ⟨f2.set n2 (BitVec.ofInt 64 n), ?_, by simp, by omega, by omega, ?_⟩
      · rw [Lir.execOps_append, Lir.execOps_append, hx1, Option.bind_some, hx2, Option.bind_some]
        simp [Lir.execOps, Lir.Op.exec, hr2, hp2 ra hra, hr1, hbe]
      · intro r hr; simp [show r ≠ n2 by omega, hp2 r (by omega), hp1 r hr]
    · cases hv
  | .wrapI k op a b, next, ops, dst, next', hg, fr, hok, v, hv => by
    simp only [gen, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hg
    obtain ⟨⟨oa, ra, n1⟩, hga, ⟨ob, rb, n2⟩, hgb, bo, hbo, rfl, rfl, rfl⟩ := hg
    dsimp only at hgb ⊢
    simp only [IExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨x, hxa, y, hyb, n, hn, rfl⟩ := hv
    obtain ⟨hoka, hokb⟩ := hok
    obtain ⟨f1, hx1, hr1, hra, hle1, hp1⟩ := gen_sound a hga hoka hxa
    obtain ⟨f2, hx2, hr2, hrb, hle2, hp2⟩ := gen_sound b hgb (hokb.mono hle1 hp1) hyb
    have hbe := aop_sound hbo (IExpr.eval_range hoka hxa) (IExpr.eval_range hokb hyb) hn
    obtain ⟨f4, hx4, hr4, hp4⟩ := normOps_exec k n2 (f2.set n2 (BitVec.ofInt 64 n)) m n (by simp)
    refine ⟨f4, ?_, hr4, by omega, by omega, ?_⟩
    · rw [Lir.execOps_append, Lir.execOps_append, Lir.execOps_append, hx1, Option.bind_some, hx2,
        Option.bind_some]
      have h3 : Lir.execOps [Lir.Op.binary bo n2 ra rb] f2 m = some (f2.set n2 (BitVec.ofInt 64 n), m) := by
        simp [Lir.execOps, Lir.Op.exec, hr2, hp2 ra hra, hr1, hbe]
      rw [h3, Option.bind_some, hx4]
    · intro r hr
      rw [hp4 r (by omega)]
      simp [show r ≠ n2 by omega, hp2 r (by omega), hp1 r hr]
  | .conv k a, next, ops, dst, next', hg, fr, hok, v, hv => by
    simp only [gen, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hg
    obtain ⟨⟨oa, ra, n1⟩, hga, rfl, rfl, rfl⟩ := hg
    dsimp only
    simp only [IExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨x, hxa, rfl⟩ := hv
    obtain ⟨f1, hx1, hr1, hra, hle1, hp1⟩ := gen_sound a hga hok hxa
    obtain ⟨f4, hx4, hr4, hp4⟩ := normOps_exec k n1 (f1.set n1 (BitVec.ofInt 64 x)) m x (by simp)
    refine ⟨f4, ?_, hr4, by omega, by omega, ?_⟩
    · rw [Lir.execOps_append, Lir.execOps_append, hx1, Option.bind_some]
      have h3 : Lir.execOps [Lir.Op.move n1 ra] f1 m = some (f1.set n1 (BitVec.ofInt 64 x), m) := by
        simp [Lir.execOps, Lir.Op.exec, hr1]
      rw [h3, Option.bind_some, hx4]
    · intro r hr
      rw [hp4 r (by omega)]
      simp [show r ≠ n1 by omega, hp1 r hr]
  | .cmp rel a b, next, ops, dst, next', hg, fr, hok, v, hv => by
    simp only [gen, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hg
    obtain ⟨⟨oa, ra, n1⟩, hga, ⟨ob, rb, n2⟩, hgb, c, hc, rfl, rfl, rfl⟩ := hg
    dsimp only at hgb ⊢
    simp only [IExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨x, hxa, y, hyb, rfl⟩ := hv
    obtain ⟨hoka, hokb⟩ := hok
    obtain ⟨f1, hx1, hr1, hra, hle1, hp1⟩ := gen_sound a hga hoka hxa
    obtain ⟨f2, hx2, hr2, hrb, hle2, hp2⟩ := gen_sound b hgb (hokb.mono hle1 hp1) hyb
    have hce := cond_sound hc (IExpr.eval_range hoka hxa) (IExpr.eval_range hokb hyb)
    refine ⟨f2.set n2 (Lir.ofBool (rel.eval x y)), ?_, by simp [ofBool_eq], by omega, by omega, ?_⟩
    · rw [Lir.execOps_append, Lir.execOps_append, hx1, Option.bind_some, hx2, Option.bind_some]
      simp [Lir.execOps, Lir.Op.exec, hr2, hp2 ra hra, hr1, Lir.Binop.eval, hce]
    · intro r hr; simp [show r ≠ n2 by omega, hp2 r (by omega), hp1 r hr]

/-- A whole expression from the frame of its variables: the operations run without touching
memory or the variables' registers and leave the value in the result register. -/
theorem compile_sound {ρ : Nat → Int} {e : IExpr} {base : Nat} {ops : List (Lir.Op Nat)}
    {dst next' : Nat} (hg : gen base e = some (ops, dst, next')) {fr : Lir.Frame Nat}
    (hok : e.VarsOk ρ fr base) {v : Int} (hv : e.eval ρ = some v) (m : Lir.Memory) :
    ∃ fr', Lir.execOps ops fr m = some (fr', m) ∧ fr'.get dst = some (BitVec.ofInt 64 v) ∧
      ∀ r, r < base → fr'.get r = fr.get r := by
  obtain ⟨fr', h1, h2, _, _, h5⟩ := gen_sound e hg hok hv (m := m)
  exact ⟨fr', h1, h2, h5⟩

/-! ## Examples

The fragment accepts the usual operators of `int` and `unsigned` code, and the values are
Cerberus's. -/

/-- `x + 1` at `int`, `x / y`, `x < y`, and unsigned `x * y`. -/
example : (gen 2 (.catchI .s32 .add (.var 0 (-2147483648) 2147483647) (.lit 1))).isSome := by decide
example : (gen 2 (.catchI .s32 .div (.var 0 (-2147483648) 2147483647)
    (.var 1 (-2147483648) 2147483647))).isSome := by decide
example : (gen 2 (.cmp .lt (.var 0 (-2147483648) 2147483647)
    (.var 1 (-2147483648) 2147483647))).isSome := by decide
example : (gen 2 (.wrapI .u32 .mul (.var 0 0 4294967295) (.var 1 0 4294967295))).isSome := by decide

/-- `INT_MAX + 1` is undefined, `0u - 1` wraps, `(int)4294967295` is `-1`, `-7 / 2` truncates. -/
example : (IExpr.catchI .s32 .add (.lit 2147483647) (.lit 1)).eval (fun _ => 0) = none := by decide
example : (IExpr.wrapI .u32 .sub (.lit 0) (.lit 1)).eval (fun _ => 0) = some 4294967295 := by decide
example : (IExpr.conv .s32 (.lit 4294967295)).eval (fun _ => 0) = some (-1) := by decide
example : (IExpr.catchI .s32 .div (.lit (-7)) (.lit 2)).eval (fun _ => 0) = some (-3) := by decide

/-- `int` is `s32`, `unsigned long` is `u64`, and `_Bool` is refused. -/
example : Kind.ofIntegerType (.signed .int) = some .s32 := by decide
example : Kind.ofIntegerType (.unsigned .long) = some .u64 := by decide
example : Kind.ofIntegerType .bool = none := by decide

end Silmaril.Compile.Core.Verified.Arith
