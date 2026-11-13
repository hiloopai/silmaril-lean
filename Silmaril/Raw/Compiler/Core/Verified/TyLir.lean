module

public import Silmaril.Compiler.Core.Verified.TyExpr.Defs
public import Silmaril.Compiler.Core.Verified.IntExprLir.Defs
/-! # Typed integer expressions in Lir registers

`t.ops d` computes the closed term `t` (`TyExpr`) into register `d`, the temporaries in the
registers above `d`, on 64-bit words: a literal is a `const`, `e₁ op e₂` the code of `e₁` into
`d`, of `e₂` into `d + 1`, the conversions of both operands to the operator's type `T`
(`convOps`: sign or zero extension from the type's width, nothing for 8-byte types), then

* `+`, `-`, `*` at a signed `T`: the 64-bit `add`/`sub`/`mul`;
* at an unsigned `T`: the 64-bit operation, then the conversion of the result;
* a comparison: the signed or unsigned 64-bit `cmp` (by `T`'s signedness), then
  `c₂ + (c₁ - c₂) * cmp`.

`ops_exec`: the code runs from every frame without getting stuck and without touching memory,
leaves the word of `t.val zero` in `d` and every register below `d` unchanged. On words, the
conversion to `T` is the wrap-around `TyConv.cv`, `+`, `-`, `*` are the integer operators
modulo `2^64`, and the comparisons of words of values of `T` are those of the values. No `Ok`
is needed: Core fixes the result only when it is defined (`TyExpr.term_runs`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyLir

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Machine
open TyActions (supported width signed Fits)
open TyConv (cv modulus)
open TyGuard (G)
open TyExpr (Term zero)

/-! ## Words -/

theorem setWidth_ofInt (b : Nat) (hb : b ≤ 64) (n : Int) :
    (BitVec.ofInt 64 n).setWidth b = BitVec.ofInt b n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have h2 : (2:Int)^b ∣ 2^64 := pow_dvd_pow 2 hb
  have e := Int.emod_emod_of_dvd n h2
  have p1 : 0 ≤ n % 2^64 := Int.emod_nonneg _ (by positivity)
  have p2 : 0 ≤ n % 2^b := Int.emod_nonneg _ (by positivity)
  zify [p1, p2]
  push_cast
  rw [Int.toNat_of_nonneg (by norm_num at p1 ⊢; exact p1), Int.toNat_of_nonneg p2]
  norm_num at e ⊢
  exact e

theorem sext_ofInt (b : Nat) (hb' : b ≤ 64) (n : Int) :
    ((BitVec.ofInt 64 n).setWidth b).signExtend 64 = BitVec.ofInt 64 (n.bmod (2^b)) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le hb', setWidth_ofInt b hb', BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  have pos : 0 < 2^b := by positivity
  have l1 := Int.le_bmod (x := n) pos
  have l2 := Int.bmod_lt (x := n) pos
  have hp : (2:Int)^b ≤ 2^64 := pow_le_pow_right₀ (by norm_num) hb'
  simp only [Nat.cast_pow, Nat.cast_ofNat] at l1 l2 ⊢
  symm
  apply Int.bmod_eq_of_le <;> push_cast <;> omega

theorem zext_ofInt (b : Nat) (hb' : b ≤ 64) (n : Int) :
    ((BitVec.ofInt 64 n).setWidth b).setWidth 64 = BitVec.ofInt 64 (n % (2^b)) := by
  rw [setWidth_ofInt b hb']
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have p2 : 0 ≤ n % 2^b := Int.emod_nonneg _ (by positivity)
  have p3 : n % 2^b < 2^b := Int.emod_lt_of_pos _ (by positivity)
  have hp : (2:Int)^b ≤ 2^64 := pow_le_pow_right₀ (by norm_num) hb'
  rw [Int.emod_eq_of_lt (a := n % 2^b) (b := 2^64) p2 (by omega)]
  have : (n % 2^b).toNat < 2^64 := by omega
  exact Nat.mod_eq_of_lt this

theorem ofInt_congr {a b : Int} (h : a % 2^64 = b % 2^64) : BitVec.ofInt 64 a = BitVec.ofInt 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  norm_num at h ⊢
  rw [h]

theorem modulus_eq (ity : IntegerType) : modulus ity = 2 ^ (8 * width ity) := by
  unfold modulus
  rw [pow_mul]
  norm_num

theorem cv_eq {ity : IntegerType} (hs : supported ity = true) (n : Int) :
    cv ity n = if n % modulus ity ≤ (TyActions.bounds ity).2 then n % modulus ity
      else n % modulus ity - modulus ity := by
  unfold cv Dynamics.wrap
  rw [TyConv.bounds_span hs]

theorem cast_modulus (ity : IntegerType) : (((2 ^ (8 * width ity) : Nat)) : Int) = modulus ity := by
  rw [modulus_eq]; norm_num

/-- The conversion of a signed type is the balanced residue. -/
theorem cv_signed {ity : IntegerType} (hs : supported ity = true) (hsg : signed ity = true) (n : Int) :
    cv ity n = n.bmod (2 ^ (8 * width ity)) := by
  have he := TyConv.modulus_even hs
  rw [cv_eq hs, TyConv.bounds_eq hs, hsg]
  simp only [↓reduceIte]
  unfold Int.bmod
  rw [cast_modulus]
  dsimp only
  split <;> split <;> omega

/-- The conversion of an unsigned type is the residue. -/
theorem cv_unsigned {ity : IntegerType} (hs : supported ity = true) (hsg : signed ity = false) (n : Int) :
    cv ity n = n % (2 ^ (8 * width ity)) := by
  have pos := TyConv.modulus_pos ity
  rw [cv_eq hs, TyConv.bounds_eq hs, hsg]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 := Int.emod_lt_of_pos n pos
  rw [ite_eq_left (by omega), ← cast_modulus]
  norm_num

/-! ## Conversions -/

/-- The conversion of register `r` to `ity`. -/
def convOps (ity : IntegerType) (r : Mir.Reg) : List (Lir.Op Mir.Reg) :=
  match width ity, signed ity with
  | 1, true => [.unary .sext8 r r]
  | 1, false => [.unary .zext8 r r]
  | 2, true => [.unary .sext16 r r]
  | 2, false => [.unary .zext16 r r]
  | 4, true => [.unary .sext32 r r]
  | 4, false => [.unary .zext32 r r]
  | _, _ => []

theorem convOps_exec {ity : IntegerType} (hs : supported ity = true) (r : Nat)
    (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory) {n : Int} (h : fr.get r = some (BitVec.ofInt 64 n)) :
    ∃ fr', Lir.execOps (convOps ity r) fr mem = some (fr', mem) ∧
      fr'.get r = some (BitVec.ofInt 64 (cv ity n)) ∧ ∀ r', r' ≠ r → fr'.get r' = fr.get r' := by
  have one : ∀ (u : Lir.Unop) (v : Lir.Word), u.eval (BitVec.ofInt 64 n) = v →
      ∃ fr', Lir.execOps [.unary u r r] fr mem = some (fr', mem) ∧ fr'.get r = some v ∧
        ∀ r', r' ≠ r → fr'.get r' = fr.get r' := by
    intro u v hv
    refine ⟨fr.set r v, by simp [Lir.execOps, Lir.Op.exec, h, hv], by simp, fun r' hr => by simp [hr]⟩
  rcases TyActions.width_cases hs with hw | hw | hw | hw <;> cases hsg : signed ity <;>
    simp only [convOps, hw, hsg]
  all_goals first
    | (refine one _ _ ?_
       first
       | (rw [cv_signed hs hsg, hw]; exact sext_ofInt _ (by norm_num) n)
       | (rw [cv_unsigned hs hsg, hw]; exact zext_ofInt _ (by norm_num) n)
       | (rw [cv_unsigned hs hsg, hw]; simp only [Lir.Unop.eval, Lir.of32, Lir.lo32];
          exact zext_ofInt _ (by norm_num) n))
    | (refine ⟨fr, by simp, ?_, fun _ _ => rfl⟩
       rw [h, ofInt_congr]
       have e := TyConv.cv_emod hs n
       rw [modulus_eq, hw] at e
       exact e.symm)

/-! ## Comparisons -/

/-- The Lir condition of a relation at a type of signedness `sg`. -/
def lirCond (sg : Bool) : BinOp → Lir.Cond
  | .lt => if sg then .lts else .ltu
  | .le => if sg then .les else .leu
  | .gt => if sg then .gts else .gtu
  | .ge => if sg then .ges else .geu
  | _ => .eq

theorem fits_range {ity : IntegerType} (hs : supported ity = true) {v : Int} (h : Fits ity v) :
    (signed ity = true → -9223372036854775808 ≤ v ∧ v < 9223372036854775808) ∧
      (signed ity = false → 0 ≤ v ∧ v < 18446744073709551616) := by
  rw [TyConv.fits_iff, TyConv.bounds_eq hs] at h
  have hm : modulus ity ≤ 18446744073709551616 := by
    rw [modulus_eq]
    have := TyActions.width_le hs
    calc (2 : Int) ^ (8 * width ity) ≤ 2 ^ 64 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 18446744073709551616 := by norm_num
  have he := TyConv.modulus_even hs
  cases hsg : signed ity <;> simp only [hsg, Bool.false_eq_true, ↓reduceIte] at h <;> simp <;> omega

theorem lirCond_eval {ity : IntegerType} (hs : supported ity = true) {r : BinOp} (hr : Guard.rel r = true)
    {x y : Int} (hx : Fits ity x) (hy : Fits ity y) :
    (lirCond (signed ity) r).eval (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = Guard.holds r x y := by
  obtain ⟨sx, ux⟩ := fits_range hs hx
  obtain ⟨sy, uy⟩ := fits_range hs hy
  cases hsg : signed ity
  · obtain ⟨x0, x1⟩ := ux hsg
    obtain ⟨y0, y1⟩ := uy hsg
    have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
    have ex : (BitVec.ofInt 64 x).toNat = x.toNat := by
      rw [Arith.ofInt_eq_ofNat x0, BitVec.toNat_ofNat, p64]; exact Nat.mod_eq_of_lt (by omega)
    have ey : (BitVec.ofInt 64 y).toNat = y.toNat := by
      rw [Arith.ofInt_eq_ofNat y0, BitVec.toNat_ofNat, p64]; exact Nat.mod_eq_of_lt (by omega)
    cases r <;> simp [Guard.rel] at hr <;>
      simp [lirCond, Lir.Cond.eval, Guard.holds, ex, ey, ← BitVec.toNat_inj] <;> omega
  · obtain ⟨x0, x1⟩ := sx hsg
    obtain ⟨y0, y1⟩ := sy hsg
    have ex := Arith.toInt_ofInt_of_fits (v := x) (by omega) (by omega)
    have ey := Arith.toInt_ofInt_of_fits (v := y) (by omega) (by omega)
    cases r <;> simp [Guard.rel] at hr <;>
      simp [lirCond, Lir.Cond.eval, Guard.holds, ex, ey, ← BitVec.toInt_inj]

/-! ## Guards -/

/-- The code of a guard on the operands in `d` and `d + 1`, the result in `d`. -/
def gops (d : Mir.Reg) : G → List (Lir.Op Mir.Reg)
  | .arith ity op => convOps ity d ++ convOps ity (d + 1) ++ [.binary (IntExpr.binop op) d d (d + 1)]
  | .wrap ity op => convOps ity d ++ convOps ity (d + 1) ++ [.binary (IntExpr.binop op) d d (d + 1)] ++
      convOps ity d
  | .cmp ity r c₁ c₂ => convOps ity d ++ convOps ity (d + 1) ++
      [.binary (.cmp (lirCond (signed ity) r)) d d (d + 1), .const (d + 1) (BitVec.ofInt 64 (c₁ - c₂)),
        .binary .mul d d (d + 1), .const (d + 1) (BitVec.ofInt 64 c₂), .binary .add d d (d + 1)]
  | .bit ity o => convOps ity d ++ convOps ity (d + 1) ++ [.binary (IntExpr.bitop o) d d (d + 1)]

/-- The guards that the recogniser produces. -/
def _root_.Silmaril.Compile.Core.Verified.TyGuard.G.Wf : G → Prop
  | .arith ity op | .wrap ity op => supported ity = true ∧ Guard.arith op = true
  | .cmp ity r _ _ => supported ity = true ∧ Guard.rel r = true
  | .bit ity _ => supported ity = true

theorem conv_two {ity : IntegerType} (hs : supported ity = true) (d : Nat)
    (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory) {x y : Int}
    (hx : fr.get d = some (BitVec.ofInt 64 x)) (hy : fr.get (d + 1) = some (BitVec.ofInt 64 y)) :
    ∃ fr', Lir.execOps (convOps ity d ++ convOps ity (d + 1)) fr mem = some (fr', mem) ∧
      fr'.get d = some (BitVec.ofInt 64 (cv ity x)) ∧ fr'.get (d + 1) = some (BitVec.ofInt 64 (cv ity y)) ∧
      ∀ r, r < d → fr'.get r = fr.get r := by
  obtain ⟨fr₁, x₁, g₁, p₁⟩ := convOps_exec hs d fr mem hx
  obtain ⟨fr₂, x₂, g₂, p₂⟩ := convOps_exec hs (d + 1) fr₁ mem
    (by rw [p₁ (d + 1) (by omega)]; exact hy)
  refine ⟨fr₂, by rw [Lir.execOps_append, x₁]; simpa using x₂, by rw [p₂ d (by omega)]; exact g₁, g₂,
    fun r hr => by rw [p₂ r (by omega), p₁ r (by omega)]⟩

theorem gops_exec {g : G} (wf : g.Wf) (d : Nat) (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory) {x y : Int}
    (hx : fr.get d = some (BitVec.ofInt 64 x)) (hy : fr.get (d + 1) = some (BitVec.ofInt 64 y)) :
    ∃ fr', Lir.execOps (gops d g) fr mem = some (fr', mem) ∧
      fr'.get d = some (BitVec.ofInt 64 (g.val x y)) ∧ ∀ r, r < d → fr'.get r = fr.get r := by
  cases g with
  | arith ity op =>
    obtain ⟨hs, har⟩ := wf
    obtain ⟨fr₁, x₁, g₁, h₁, p₁⟩ := conv_two hs d fr mem hx hy
    refine ⟨fr₁.set d (BitVec.ofInt 64 (Guard.apply op (cv ity x) (cv ity y))), ?_, by simp [G.val],
      fun r hr => by rw [IntExpr.get_below hr, p₁ r hr]⟩
    simp only [gops, Lir.execOps_append, x₁, Option.bind_some]
    simp [Lir.execOps, Lir.Op.exec, g₁, h₁, IntExpr.binop_eval]
  | wrap ity op =>
    obtain ⟨hs, har⟩ := wf
    obtain ⟨fr₁, x₁, g₁, h₁, p₁⟩ := conv_two hs d fr mem hx hy
    let fr₂ := fr₁.set d (BitVec.ofInt 64 (Guard.apply op (cv ity x) (cv ity y)))
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := convOps_exec hs d fr₂ mem (n := Guard.apply op (cv ity x) (cv ity y))
      (by simp [fr₂])
    refine ⟨fr₃, ?_, by simpa [G.val] using g₃, fun r hr => ?_⟩
    · simp only [gops, Lir.execOps_append, x₁, Option.bind_some]
      have : Lir.execOps [.binary (IntExpr.binop op) d d (d + 1)] fr₁ mem = some (fr₂, mem) := by
        simp [Lir.execOps, Lir.Op.exec, g₁, h₁, IntExpr.binop_eval, fr₂]
      rw [this]
      simpa using x₃
    · rw [p₃ r (by omega), IntExpr.get_below hr, p₁ r hr]
  | cmp ity rl c₁ c₂ =>
    obtain ⟨hs, hr⟩ := wf
    obtain ⟨fr₁, x₁, g₁, h₁, p₁⟩ := conv_two hs d fr mem hx hy
    let f := Lir.ofBool ((lirCond (signed ity) rl).eval (BitVec.ofInt 64 (cv ity x))
      (BitVec.ofInt 64 (cv ity y)))
    let K := BitVec.ofInt 64 (c₁ - c₂)
    let C := BitVec.ofInt 64 c₂
    refine ⟨((((fr₁.set d f).set (d + 1) K).set d (f * K)).set (d + 1) C).set d (f * K + C), ?_, ?_,
      fun r hr => ?_⟩
    · simp only [gops, Lir.execOps_append, x₁, Option.bind_some]
      simp [Lir.execOps, Lir.Op.exec, g₁, h₁, Lir.Binop.eval, f, K, C]
    · simp only [Lir.Frame.get_set, ↓reduceIte, f, K, C, lirCond_eval hs hr (TyConv.cv_fits hs x)
        (TyConv.cv_fits hs y), IntExpr.select_cmp, G.val]
    · have r1 : r < d + 1 := by omega
      rw [IntExpr.get_below hr, IntExpr.get_below r1, IntExpr.get_below hr, IntExpr.get_below r1,
        IntExpr.get_below hr, p₁ r hr]
  | bit ity o =>
    obtain ⟨fr₁, x₁, g₁, h₁, p₁⟩ := conv_two wf d fr mem hx hy
    refine ⟨fr₁.set d (BitVec.ofInt 64 (o.apply (cv ity x) (cv ity y))), ?_, by simp [G.val],
      fun r hr => by rw [IntExpr.get_below hr, p₁ r hr]⟩
    simp only [gops, Lir.execOps_append, x₁, Option.bind_some]
    simp [Lir.execOps, Lir.Op.exec, g₁, h₁, IntExpr.bitop_eval]

/-! ## Terms -/

/-- The guards of a term are those of the recogniser. -/
def _root_.Silmaril.Compile.Core.Verified.TyExpr.Term.Wf : Term → Prop
  | .lit _ | .var _ _ => True
  | .bin g a b => g.Wf ∧ a.Wf ∧ b.Wf
  | .ebin g a b => g.Wf ∧ a.Wf ∧ b.Wf
  | .un g a => g.Wf ∧ a.Wf

/-- The code of the closed term `t` into register `d` (a read, which a closed term has none
of, is `0`). -/
def _root_.Silmaril.Compile.Core.Verified.TyExpr.Term.ops (d : Mir.Reg) : Term → List (Lir.Op Mir.Reg)
  | .lit c => [.const d (BitVec.ofInt 64 c)]
  | .var _ _ => [.const d 0]
  | .bin g a b => a.ops d ++ b.ops (d + 1) ++ gops d g
  | .ebin g a b => a.ops d ++ b.ops (d + 1) ++ gops d g
  | .un g a => [.const d 0] ++ a.ops (d + 1) ++ gops d g

/-- **The code of `t`** runs from every frame, leaves the word of `t.val zero` in `d` and the
registers below `d` as they were. -/
theorem ops_exec : (t : Term) → t.Wf → (d : Nat) → (fr : Lir.Frame Mir.Reg) → (mem : Lir.Memory) →
    ∃ fr', Lir.execOps (t.ops d) fr mem = some (fr', mem) ∧
      fr'.get d = some (BitVec.ofInt 64 (t.val zero)) ∧ ∀ r : Nat, r < d → fr'.get r = fr.get r
  | .lit c, _, d, fr, mem =>
    ⟨fr.set d (BitVec.ofInt 64 c), by simp [Term.ops, Lir.execOps, Lir.Op.exec], by simp [Term.val],
      fun r hr => IntExpr.get_below hr _⟩
  | .var q _, _, d, fr, mem =>
    ⟨fr.set d 0, by simp [Term.ops, Lir.execOps, Lir.Op.exec], by simp [Term.val, zero],
      fun r hr => IntExpr.get_below hr _⟩
  | .bin g a b, ⟨wg, wa, wb⟩, d, fr, mem => by
    obtain ⟨fr₁, x₁, g₁, p₁⟩ := ops_exec a wa d fr mem
    obtain ⟨fr₂, x₂, g₂, p₂⟩ := ops_exec b wb (d + 1) fr₁ mem
    have gd : fr₂.get d = some (BitVec.ofInt 64 (a.val zero)) := by
      rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := gops_exec wg d fr₂ mem gd g₂
    refine ⟨fr₃, ?_, by simpa [Term.val] using g₃, fun r hr => ?_⟩
    · simp only [Term.ops, Lir.execOps_append, x₁, Option.bind_some, x₂]
      exact x₃
    · rw [p₃ r hr, p₂ r (Nat.lt_succ_of_lt hr), p₁ r hr]
  | .ebin g a b, ⟨wg, wa, wb⟩, d, fr, mem => by
    obtain ⟨fr₁, x₁, g₁, p₁⟩ := ops_exec a wa d fr mem
    obtain ⟨fr₂, x₂, g₂, p₂⟩ := ops_exec b wb (d + 1) fr₁ mem
    have gd : fr₂.get d = some (BitVec.ofInt 64 (a.val zero)) := by
      rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := gops_exec wg d fr₂ mem gd g₂
    refine ⟨fr₃, ?_, by simpa [Term.val] using g₃, fun r hr => ?_⟩
    · simp only [Term.ops, Lir.execOps_append, x₁, Option.bind_some, x₂]
      exact x₃
    · rw [p₃ r hr, p₂ r (Nat.lt_succ_of_lt hr), p₁ r hr]
  | .un g a, ⟨wg, wa⟩, d, fr, mem => by
    let fr₀ := fr.set d (BitVec.ofInt 64 0)
    obtain ⟨fr₂, x₂, g₂, p₂⟩ := ops_exec a wa (d + 1) fr₀ mem
    have gd : fr₂.get d = some (BitVec.ofInt 64 0) := by
      rw [p₂ d (Nat.lt_succ_self d)]; simp [fr₀]
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := gops_exec wg d fr₂ mem gd g₂
    refine ⟨fr₃, ?_, by simpa [Term.val] using g₃, fun r hr => ?_⟩
    · simp only [Term.ops, Lir.execOps_append]
      have h0 : Lir.execOps [Lir.Op.const d 0] fr mem = some (fr₀, mem) := by
        simp [Lir.execOps, Lir.Op.exec, fr₀]
      rw [h0]
      simp only [Option.bind_some, x₂]
      exact x₃
    · rw [p₃ r hr, p₂ r (Nat.lt_succ_of_lt hr)]
      exact IntExpr.get_below hr _

/-- The code of `main`: the closed term into register `0`. -/
def mainOps (t : Term) : List (Lir.Op Mir.Reg) := t.ops 0

theorem mainOps_exec {t : Term} (wf : t.Wf) (fr0 : Lir.Frame Mir.Reg) (mem : Lir.Memory) :
    ∃ fr, Lir.execOps (mainOps t) fr0 mem = some (fr, mem) ∧
      fr.get 0 = some (BitVec.ofInt 64 (t.val zero)) := by
  obtain ⟨fr, x, g, -⟩ := ops_exec t wf 0 fr0 mem
  exact ⟨fr, x, g⟩

end Silmaril.Compile.Core.Verified.TyLir
