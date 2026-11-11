module

public import Silmaril.Proofs.Wasm.Auto.Bridge.Mod
public import Silmaril.Wasm.Auto.Equiv.Thms

/-!
# The lemma library of residual goals

`lemmaGoals_hold`: every goal of `Silmaril.Wasm.Auto.Bridge.lemmaGoals` holds (the `div10` goal is
`div10_goal`, the Granlund–Montgomery identity `div10_bv64` proved by `omega` on `toNat`); `modEquiv_of_discharged`: residual goals all in the library prove the equivalence.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Front (ModEquiv)

theorem and_mask (n : Nat) : n &&& 4294967295 = n % 2 ^ 32 := by
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem and_mask' (n : Nat) : 4294967295 &&& n = n % 2 ^ 32 := by
  rw [Nat.and_comm, and_mask]

/-- The `div10` goal as a `BitVec 64` identity (Granlund–Montgomery division by `10`),
by `omega` on `toNat` once the products are shown not to wrap. -/
theorem div10_bv64 (x : BitVec 64) :
    ((3435973836#64 * (x >>> 32) +
        ((((4294967295#64 &&& 3435973836#64 * (x &&& 4294967295#64)) +
              ((4294967295#64 &&& 3435973837#64 * (x >>> 32)) +
                (3435973837#64 * (x &&& 4294967295#64)) >>> 32)) >>> 32) +
          ((3435973836#64 * (x &&& 4294967295#64)) >>> 32 +
            (3435973837#64 * (x >>> 32)) >>> 32))) >>> 3) = x / 10#64 := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat < 2 ^ 64 := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow,
    Nat.reduceMod, and_mask, and_mask']
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  omega

/-- The `div10` goal of the lemma library holds. -/
theorem div10_goal : Goal.Holds (.i64, div10Lhs, .bin (.div .unsigned) (.var 0) (.const 10)) := by
  intro ρ
  have hne : BitVec.ofNat (IntType.width .i64) 10 ≠ 0#(IntType.width .i64) := by decide
  simp only [div10Lhs, ev, binV_shrU, binV_add, binV_mul, binV_and, binV_divU hne]
  generalize ρ .i64 0 = x
  exact div10_bv64 x

theorem lemmaGoals_hold : ∀ g ∈ lemmaGoals, g.Holds := by
  intro g hg
  simp only [lemmaGoals, List.mem_singleton] at hg
  subst hg
  exact div10_goal

theorem discharged_sound {gs : List Goal} (h : discharged gs = true) : ∀ g ∈ gs, g.Holds := by
  intro g hg
  have hc := List.all_eq_true.mp h g hg
  exact lemmaGoals_hold g (List.contains_iff_mem.mp hc)

/-- **Residual goals in the lemma library prove module equivalence**, every profile. -/
theorem modEquiv_of_discharged {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {P : Numerics.Profile} {m₁ m₂ : Module} {j : Nat} {gs : List Goal}
    (h : fnResiduals m₁ m₂ j = some gs) (hd : discharged gs = true) : ModEquiv R P m₁ m₂ j :=
  modEquiv_of_fnResiduals hR h (discharged_sound hd)

end Silmaril.Proofs.Wasm.Auto.Bridge