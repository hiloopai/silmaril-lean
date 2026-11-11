module

public import Silmaril.Wasm.Auto.VCGen.Defs

/-!
# The reflective VC generator: denotation lemmas

Conjunctions (`Fm.den_conj`), substitution (`Tm.den_subst`, `Fm.den_subst`: a placeholder
denotes the value it is replaced by, `locEnv`), scope (`Tm.den_scoped`, `Fm.den_scoped`: a
scoped formula depends on its parameters only, `Agree`), path conditions (`den_condF`,
`den_ncondF`), stacks (`pop1_eq`) and the side conditions of division (`intBinOp_of_safe`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.VCGen

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {F : Fns}

/-! ## Conjunctions and validity -/

theorem Fm.den_conj (ρ ξ : Env) (l : List Fm) : (Fm.conj l).den F ρ ξ ↔ ∀ p ∈ l, p.den F ρ ξ := by
  induction l with
  | nil => simp [Fm.conj, Fm.den]
  | cons p ps ih =>
    cases ps with
    | nil => simp [Fm.conj]
    | cons q qs => simp [Fm.conj, Fm.den, ih]

theorem allValid_append {l₁ l₂ : List Fm} :
    AllValid F (l₁ ++ l₂) ↔ AllValid F l₁ ∧ AllValid F l₂ := by
  induction l₁ with
  | nil => simp [AllValid]
  | cons p ps ih => simp [AllValid, ih, and_assoc]

theorem allValid_iff {l : List Fm} : AllValid F l ↔ ∀ φ ∈ l, Valid F φ := by
  induction l with
  | nil => simp [AllValid]
  | cons p ps ih => simp [AllValid, ih]

theorem allValid_map_vc {σ : SSt} {l : List Fm} {ρ : Env} (h : AllValid F (l.map (vc σ)))
    (hpc : ∀ p ∈ σ.pc, p.den F ρ ρ) : ∀ φ ∈ l, φ.den F ρ ρ := by
  intro φ hφ
  have := (allValid_iff.mp h) (vc σ φ) (List.mem_map_of_mem hφ) ρ
  exact this ((Fm.den_conj ρ ρ σ.pc).mpr hpc)

theorem vc_holds {σ : SSt} {φ : Fm} {ρ : Env} (h : Valid F (vc σ φ))
    (hpc : ∀ p ∈ σ.pc, p.den F ρ ρ) : φ.den F ρ ρ :=
  h ρ ((Fm.den_conj ρ ρ σ.pc).mpr hpc)

theorem not_bad {σ : SSt} {ρ : Env} (h : AllValid F (bad σ)) (hpc : ∀ p ∈ σ.pc, p.den F ρ ρ) :
    False :=
  vc_holds (φ := .ff) h.1 hpc

/-! ## Substitution -/

theorem locEnv_eq_valEnv (ρ ξ : Env) (ls : List SV) :
    locEnv F ρ ξ ls = valEnv (ls.map (SV.den F ρ ξ)) := by
  simp only [locEnv, valEnv, List.getElem?_map, Env.mk.injEq]
  constructor
  · funext j
    rcases ls[j]? with _ | (a | a) <;> rfl
  · funext j
    rcases ls[j]? with _ | (a | a) <;> rfl

theorem locEnv_congr {ρ ρ' ξ ξ' : Env} {ls ls' : List SV}
    (h : ls.map (SV.den F ρ ξ) = ls'.map (SV.den F ρ' ξ')) :
    locEnv F ρ ξ ls = locEnv F ρ' ξ' ls' := by
  rw [locEnv_eq_valEnv, locEnv_eq_valEnv, h]

theorem Tm.den_subst (ρ ξ : Env) (ls : List SV) :
    ∀ {t : IntType} (a : Tm t), (a.subst ls).den F ρ ξ = a.den F ρ (locEnv F ρ ξ ls)
  | _, .var t i => rfl
  | _, .loc t j => by
    simp only [Tm.subst, Tm.den]
    rcases h : ls[j]? with _ | (a | a) <;> rcases t <;>
      simp [Tm.den, Env.get, locEnv, h, SV.as, Option.getD] <;> rfl
  | _, .lit t n => rfl
  | _, .un op a => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls a]
  | _, .bin op a b => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls a, Tm.den_subst ρ ξ ls b]
  | _, .rel op a b => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls a, Tm.den_subst ρ ξ ls b]; rfl
  | _, .eqz a => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls a]; rfl
  | _, .ite c a b => by
    simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls c, Tm.den_subst ρ ξ ls a,
      Tm.den_subst ρ ξ ls b]
  | _, .wrap a => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls a]; rfl
  | _, .ext sx a => by cases sx <;> simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls a] <;> rfl
  | _, .fn k a => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls a]
  | _, .fn2 k a b => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls a, Tm.den_subst ρ ξ ls b]

theorem Fm.den_subst (ρ ξ : Env) (ls : List SV) :
    ∀ φ : Fm, (φ.subst ls).den F ρ ξ ↔ φ.den F ρ (locEnv F ρ ξ ls)
  | .tt => Iff.rfl
  | .ff => Iff.rfl
  | .rel op a b => by simp only [Fm.subst, Fm.den, Tm.den_subst]
  | .nz a => by simp only [Fm.subst, Fm.den, Tm.den_subst]
  | .not p => by simp only [Fm.subst, Fm.den, Fm.den_subst ρ ξ ls p]
  | .and p q => by simp only [Fm.subst, Fm.den, Fm.den_subst ρ ξ ls p, Fm.den_subst ρ ξ ls q]
  | .or p q => by simp only [Fm.subst, Fm.den, Fm.den_subst ρ ξ ls p, Fm.den_subst ρ ξ ls q]
  | .imp p q => by simp only [Fm.subst, Fm.den, Fm.den_subst ρ ξ ls p, Fm.den_subst ρ ξ ls q]

/-! ## Scope -/

theorem Agree.trans {ps : List IntType} {ρ₁ ρ₂ ρ₃ : Env} (h₁ : Agree ps ρ₁ ρ₂)
    (h₂ : Agree ps ρ₂ ρ₃) : Agree ps ρ₁ ρ₃ := fun i t h => (h₁ i t h).trans (h₂ i t h)

theorem Agree.symm {ps : List IntType} {ρ₁ ρ₂ : Env} (h : Agree ps ρ₁ ρ₂) : Agree ps ρ₂ ρ₁ :=
  fun i t hi => (h i t hi).symm

theorem Agree.refl (ps : List IntType) (ρ : Env) : Agree ps ρ ρ := fun _ _ _ => rfl

theorem Tm.den_scoped {ps : List IntType} {ρ ρ' : Env} (hρ : Agree ps ρ ρ') (ξ : Env) :
    ∀ {t : IntType} (a : Tm t), a.scoped ps = true → a.den F ρ ξ = a.den F ρ' ξ
  | _, .var t i, h => hρ i t (by simpa [Tm.scoped] using h)
  | _, .loc t j, _ => rfl
  | _, .lit t n, _ => rfl
  | _, .un op a, h => by simp only [Tm.den, Tm.den_scoped hρ ξ a h]
  | _, .bin op a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_scoped hρ ξ a h.1, Tm.den_scoped hρ ξ b h.2]
  | _, .rel op a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_scoped hρ ξ a h.1, Tm.den_scoped hρ ξ b h.2]; rfl
  | _, .eqz a, h => by simp only [Tm.den, Tm.den_scoped hρ ξ a h]; rfl
  | _, .ite c a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_scoped hρ ξ c h.1.1, Tm.den_scoped hρ ξ a h.1.2,
      Tm.den_scoped hρ ξ b h.2]
  | _, .wrap a, h => by simp only [Tm.den, Tm.den_scoped hρ ξ a h]; rfl
  | _, .ext sx a, h => by cases sx <;> simp only [Tm.den, Tm.den_scoped hρ ξ a h] <;> rfl
  | _, .fn k a, h => by simp only [Tm.den, Tm.den_scoped hρ ξ a h]
  | _, .fn2 k a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_scoped hρ ξ a h.1, Tm.den_scoped hρ ξ b h.2]

theorem Fm.den_scoped {ps : List IntType} {ρ ρ' : Env} (hρ : Agree ps ρ ρ') (ξ : Env) :
    ∀ φ : Fm, φ.scoped ps = true → (φ.den F ρ ξ ↔ φ.den F ρ' ξ)
  | .tt, _ => Iff.rfl
  | .ff, _ => Iff.rfl
  | .rel op a b, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.den, Tm.den_scoped hρ ξ a h.1, Tm.den_scoped hρ ξ b h.2]
  | .nz a, h => by simp only [Fm.den, Tm.den_scoped hρ ξ a h]
  | .not p, h => by simp only [Fm.den, Fm.den_scoped hρ ξ p h]
  | .and p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.den, Fm.den_scoped hρ ξ p h.1, Fm.den_scoped hρ ξ q h.2]
  | .or p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.den, Fm.den_scoped hρ ξ p h.1, Fm.den_scoped hρ ξ q h.2]
  | .imp p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.den, Fm.den_scoped hρ ξ p h.1, Fm.den_scoped hρ ξ q h.2]

/-! ## Symbolic values -/

theorem SV.den_of (ρ ξ : Env) : ∀ (t : IntType) (a : Tm t),
    (SV.of t a).den F ρ ξ = .num ⟨.int t, a.den F ρ ξ⟩
  | .i32, _ => rfl
  | .i64, _ => rfl

theorem SV.ty_of : ∀ (t : IntType) (a : Tm t), (SV.of t a).ty = t
  | .i32, _ => rfl
  | .i64, _ => rfl

theorem pop1_eq {t : IntType} {st st' : List SV} {a : Tm t} (h : pop1 t st = some (a, st')) :
    st = SV.of t a :: st' := by
  cases st with
  | nil => simp [pop1] at h
  | cons v r =>
    cases v <;> cases t <;> simp [pop1, SV.as] at h <;> obtain ⟨rfl, rfl⟩ := h <;> rfl

theorem selV_den {c : Tm .i32} {v₁ v₂ v : SV} (h : selV c v₁ v₂ = some v) (ρ ξ : Env) :
    v.den F ρ ξ = cond (nz32 (c.den F ρ ξ)) (v₁.den F ρ ξ) (v₂.den F ρ ξ) := by
  cases v₁ <;> cases v₂ <;> simp only [selV, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    cases hc : nz32 (c.den F ρ ξ) <;> simp [SV.den, Tm.den, iteT, hc] <;> rfl

/-! ## Path conditions -/

theorem bool32_ne_zero (b : Bool) : bool32 b ≠ 0 ↔ b = true := by
  cases b <;> decide

theorem bool32_bne_zero (b : Bool) : (bool32 b != 0) = b := by
  cases b <;> decide

theorem relB_iff (n : Nat) (op : IntRelOp) (x y : BitVec n) : relB n op x y = true ↔ relW n op x y := by
  rcases op with _ | _ | (_ | _) | (_ | _) | (_ | _) | (_ | _) <;>
    simp [relB, relW, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle]

theorem relV_ne_zero (t : IntType) (op : IntRelOp) (x y : BitVec t.width) :
    relV t op x y ≠ 0 ↔ relP t op x y := by
  cases t <;> exact (bool32_ne_zero _).trans (relB_iff _ _ _ _)

theorem eqzV_ne_zero : ∀ (t : IntType) (x : BitVec t.width), eqzV t x ≠ 0 ↔ x = litT t 0
  | .i32, _ => (bool32_ne_zero _).trans (beq_iff_eq.trans Iff.rfl)
  | .i64, _ => (bool32_ne_zero _).trans (beq_iff_eq.trans Iff.rfl)

theorem intRelOp_eq_relV (t : IntType) (op : IntRelOp) (x y : BitVec t.width) :
    intRelOp t op x y = relV t op x y := by
  cases t <;> rcases op with _ | _ | (_ | _) | (_ | _) | (_ | _) | (_ | _) <;> rfl

theorem intTestOp_eq_eqzV (t : IntType) (op : IntTestOp) (x : BitVec t.width) :
    intTestOp t op x = eqzV t x := by
  cases t <;> rfl

theorem intUnOp_eq_unT (t : IntType) (op : IntUnOp) (x : BitVec t.width) :
    intUnOp t op x = unT t op x := by
  cases t <;> cases op <;> rfl

theorem litT_toNat : ∀ (t : IntType) (c : BitVec t.width), litT t c.toNat = c
  | .i32, c => BitVec.eq_of_toNat_eq ((BitVec.toNat_ofNat _ _).trans (Nat.mod_eq_of_lt c.isLt))
  | .i64, c => BitVec.eq_of_toNat_eq ((BitVec.toNat_ofNat _ _).trans (Nat.mod_eq_of_lt c.isLt))

theorem nz32_iff (x : BitVec 32) : nz32 x = true ↔ x ≠ 0 := bne_iff_ne

theorem den_condF (ρ ξ : Env) (c : Tm .i32) :
    (condF c).den F ρ ξ ↔ (c.den F ρ ξ : BitVec 32) ≠ 0 := by
  cases c with
  | rel op a b => exact (relV_ne_zero _ _ _ _).symm
  | @eqz t a =>
    simp only [condF, Fm.den, relP, Tm.den]
    cases t <;> exact (eqzV_ne_zero _ (a.den F ρ ξ)).symm
  | _ => exact nz32_iff _

theorem den_ncondF (ρ ξ : Env) (c : Tm .i32) :
    (ncondF c).den F ρ ξ ↔ (c.den F ρ ξ : BitVec 32) = 0 := by
  cases c with
  | rel op a b => exact (not_congr (relV_ne_zero _ _ _ _)).symm.trans not_not
  | @eqz t a =>
    simp only [ncondF, Fm.den, relP, Tm.den]
    cases t <;> exact (not_congr (eqzV_ne_zero _ (a.den F ρ ξ))).symm.trans not_not
  | _ => exact (not_congr (nz32_iff _)).trans not_not

/-! ## Division and remainder -/

/-- The side condition `b ≠ 0`. -/
theorem den_ne_zero {t : IntType} {b : Tm t} {ρ ξ : Env}
    (h : (Fm.rel .ne b (.lit t 0)).den F ρ ξ) : ¬ b.den F ρ ξ = 0 := by
  intro hb
  have h' : ¬ b.den F ρ ξ = litT t 0 := by cases t <;> exact h
  exact h' (by rw [hb]; cases t <;> rfl)

theorem intBinOp_sdiv {t : IntType} {a b : Tm t} {ρ ξ : Env}
    (h : ∀ φ ∈ safeF t (.div .signed) a b, φ.den F ρ ξ) :
    intBinOp t (.div .signed) (a.den F ρ ξ) (b.den F ρ ξ) =
      .ok (binT t (.div .signed) (a.den F ρ ξ) (b.den F ρ ξ)) := by
  have hb : ¬ b.den F ρ ξ = 0 := den_ne_zero (h _ (by simp [safeF]))
  have hov := h (.not (.and (.rel .eq a (.lit t (2 ^ (t.width - 1))))
      (.rel .eq b (.lit t (2 ^ t.width - 1))))) (by simp [safeF])
  simp only [intBinOp]
  split
  next hz => exact absurd hz hb
  next =>
    split
    next hm =>
      refine absurd ?_ hov
      obtain ⟨h₁, h₂⟩ := hm
      cases t
      · exact ⟨h₁.trans (by decide : BitVec.intMin 32 = BitVec.ofNat 32 (2 ^ 31)),
          h₂.trans (by decide : (-1 : BitVec 32) = BitVec.ofNat 32 (2 ^ 32 - 1))⟩
      · exact ⟨h₁.trans (by decide : BitVec.intMin 64 = BitVec.ofNat 64 (2 ^ 63)),
          h₂.trans (by decide : (-1 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 1))⟩
    next => cases t <;> rfl

theorem intBinOp_of_safe {t : IntType} {op : IntBinOp} {a b : Tm t} {ρ ξ : Env}
    (h : ∀ φ ∈ safeF t op a b, φ.den F ρ ξ) :
    intBinOp t op (a.den F ρ ξ) (b.den F ρ ξ) = .ok (binT t op (a.den F ρ ξ) (b.den F ρ ξ)) := by
  cases op with
  | div sx =>
    cases sx with
    | signed => exact intBinOp_sdiv h
    | unsigned =>
      have hb : ¬ b.den F ρ ξ = 0 := den_ne_zero (h _ (by simp [safeF]))
      simp only [intBinOp]
      split
      next hz => exact absurd hz hb
      next => cases t <;> rfl
  | rem sx =>
    have hb : ¬ b.den F ρ ξ = 0 := den_ne_zero (h _ (by simp [safeF]))
    cases sx <;> simp only [intBinOp] <;> split
    all_goals first | exact absurd ‹_› hb | (cases t <;> rfl)
  | shr sx => cases t <;> cases sx <;> rfl
  | _ => cases t <;> rfl

end Silmaril.Proofs.Wasm.Auto.VCGen