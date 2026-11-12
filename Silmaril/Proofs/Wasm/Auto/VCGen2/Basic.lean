module

public import Silmaril.Wasm.Auto.VCGen2.Defs
public import Silmaril.Wasm.Auto.VCGen.Thms

/-!
# The VC generator with SSA names and memory: denotation lemmas

Conjunctions and validity, substitution (`Tm.den_subst`, `Fm.den_subst`, `locEnv`), scope
(`Tm.den_scoped`, `Fm.den_scoped`, `Agree`: parameters and the memory at entry), **freshness**
(`Tm.den_eqBelow`, `Fm.den_eqBelow`: a term below `n` does not see the environment from `n` on,
`EqBelow`; monotonicity of `below`), stacks, path conditions and division side conditions.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.VCGen2

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen2
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.VCGen (binW relW relB unW litT unT binT relP relV eqzV nz32 iteT wrapW
  extSW extUW)

variable {F : Fns}

theorem Tm.dens32_eq_map (ρ ξ : Env) (as : List (Tm .i32)) :
    Tm.dens32 F ρ ξ as = as.map fun a => (a.den F ρ ξ : BitVec 32) := by
  induction as with
  | nil => rfl
  | cons a as ih => exact congrArg _ ih

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

theorem locEnv_eq_valEnv (ρ ξ : Env) (ls : List SV) (cm : Nat) :
    locEnv F ρ ξ ls cm = valEnv (ls.map (SV.den F ρ ξ)) (ρ.mem cm) := by
  simp only [locEnv, valEnv, List.getElem?_map, Env.mk.injEq]
  refine ⟨?_, ?_, trivial⟩
  · funext j
    rcases ls[j]? with _ | (a | a) <;> rfl
  · funext j
    rcases ls[j]? with _ | (a | a) <;> rfl

theorem MR.den_subst (ρ ξ : Env) (ls : List SV) (cm : Nat) :
    ∀ m : MR, (m.subst cm).den ρ ξ = m.den ρ (locEnv F ρ ξ ls cm)
  | .v _ => rfl
  | .cur => rfl

theorem Tm.den_subst (ρ ξ : Env) (ls : List SV) (cm : Nat) :
    ∀ {t : IntType} (a : Tm t), (a.subst ls cm).den F ρ ξ = a.den F ρ (locEnv F ρ ξ ls cm)
  | _, .var t i => rfl
  | _, .loc t j => by
    simp only [Tm.subst, Tm.den]
    rcases h : ls[j]? with _ | (a | a) <;> rcases t <;>
      simp [Tm.den, Env.get, locEnv, h, SV.as, Option.getD] <;> rfl
  | _, .lit t n => rfl
  | _, .un op a => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a]
  | _, .bin op a b => by
    simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a, Tm.den_subst ρ ξ ls cm b]
  | _, .rel op a b => by
    simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a, Tm.den_subst ρ ξ ls cm b]; rfl
  | _, .eqz a => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a]; rfl
  | _, .ite c a b => by
    simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm c, Tm.den_subst ρ ξ ls cm a,
      Tm.den_subst ρ ξ ls cm b]
  | _, .wrap a => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a]; rfl
  | _, .ext sx a => by cases sx <;> simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a] <;> rfl
  | _, .fn k a => by simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a]
  | _, .fn2 k a b => by
    simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a, Tm.den_subst ρ ξ ls cm b]
  | _, .load t n sx m a off => by
    simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a, MR.den_subst (F := F) ρ ξ ls cm m]
  | _, .mfn k m a b => by
    simp only [Tm.subst, Tm.den, Tm.den_subst ρ ξ ls cm a, Tm.den_subst ρ ξ ls cm b,
      MR.den_subst (F := F) ρ ξ ls cm m]; rfl

theorem Fm.den_subst (ρ ξ : Env) (ls : List SV) (cm : Nat) :
    ∀ φ : Fm, (φ.subst ls cm).den F ρ ξ ↔ φ.den F ρ (locEnv F ρ ξ ls cm)
  | .tt => Iff.rfl
  | .ff => Iff.rfl
  | .rel op a b => by simp only [Fm.subst, Fm.den, Tm.den_subst]
  | .nz a => by simp only [Fm.subst, Fm.den, Tm.den_subst]
  | .not p => by simp only [Fm.subst, Fm.den, Fm.den_subst ρ ξ ls cm p]
  | .and p q => by simp only [Fm.subst, Fm.den, Fm.den_subst ρ ξ ls cm p, Fm.den_subst ρ ξ ls cm q]
  | .or p q => by simp only [Fm.subst, Fm.den, Fm.den_subst ρ ξ ls cm p, Fm.den_subst ρ ξ ls cm q]
  | .imp p q => by simp only [Fm.subst, Fm.den, Fm.den_subst ρ ξ ls cm p, Fm.den_subst ρ ξ ls cm q]
  | .inb m a n => by simp only [Fm.subst, Fm.den, Tm.den_subst, MR.den_subst (F := F) ρ ξ ls cm m]
  | .pr k m as => by
    have key : ∀ l : List (Tm .i32), (l.map (Tm.subst ls cm)).map
        (fun a => (a.den F ρ ξ : BitVec 32)) =
          l.map (fun a => (a.den F ρ (locEnv F ρ ξ ls cm) : BitVec 32)) := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => exact congrArg₂ List.cons (Tm.den_subst ρ ξ ls cm a) ih
    simp only [Fm.subst, Fm.den, MR.den_subst (F := F) ρ ξ ls cm m, Tm.dens32_eq_map]
    exact iff_of_eq (congrArg _ (key as))
  | .meq m₁ m₂ => by simp only [Fm.subst, Fm.den, MR.den_subst (F := F) ρ ξ ls cm]
  | .st k m n a off v => by
    simp only [Fm.subst, Fm.den, Tm.den_subst, MR.den_subst (F := F) ρ ξ ls cm m]

/-! ## Scope -/

theorem Agree.trans {ps : List IntType} {ρ₁ ρ₂ ρ₃ : Env} (h₁ : Agree ps ρ₁ ρ₂)
    (h₂ : Agree ps ρ₂ ρ₃) : Agree ps ρ₁ ρ₃ :=
  ⟨fun i t h => (h₁.1 i t h).trans (h₂.1 i t h), h₁.2.trans h₂.2⟩

theorem Agree.symm {ps : List IntType} {ρ₁ ρ₂ : Env} (h : Agree ps ρ₁ ρ₂) : Agree ps ρ₂ ρ₁ :=
  ⟨fun i t hi => (h.1 i t hi).symm, h.2.symm⟩

theorem Agree.refl (ps : List IntType) (ρ : Env) : Agree ps ρ ρ := ⟨fun _ _ _ => rfl, rfl⟩

theorem MR.den_scoped {ps : List IntType} {ρ ρ' : Env} (hρ : Agree ps ρ ρ') (ξ : Env) :
    ∀ m : MR, m.scoped = true → m.den ρ ξ = m.den ρ' ξ
  | .v k, h => by
    obtain rfl : k = 0 := by simpa [MR.scoped] using h
    exact hρ.2
  | .cur, _ => rfl

theorem Tm.den_scoped {ps : List IntType} {ρ ρ' : Env} (hρ : Agree ps ρ ρ') (ξ : Env) :
    ∀ {t : IntType} (a : Tm t), a.scoped ps = true → a.den F ρ ξ = a.den F ρ' ξ
  | _, .var t i, h => hρ.1 i t (by simpa [Tm.scoped] using h)
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
  | _, .load t n sx m a off, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_scoped hρ ξ a h.2, MR.den_scoped hρ ξ m h.1]
  | _, .mfn k m a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_scoped hρ ξ a h.1.2, Tm.den_scoped hρ ξ b h.2,
      MR.den_scoped hρ ξ m h.1.1]; rfl

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
  | .inb m a n, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.den, Tm.den_scoped hρ ξ a h.2, MR.den_scoped hρ ξ m h.1]
  | .pr k m as, h => by
    simp only [Fm.scoped, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Fm.den, MR.den_scoped hρ ξ m h.1, Tm.dens32_eq_map]
    exact iff_of_eq (congrArg _ (List.map_congr_left fun a ha => Tm.den_scoped hρ ξ a (h.2 a ha)))
  | .meq m₁ m₂, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.den, MR.den_scoped hρ ξ m₁ h.1, MR.den_scoped hρ ξ m₂ h.2]
  | .st _ _ _ _ _ _, h => by simp [Fm.scoped] at h

/-! ## Freshness -/

theorem EqBelow.get {n : Nat} {ρ ρ' : Env} (h : EqBelow n ρ ρ') {i : Nat} (hi : i < n) :
    ∀ t, ρ.get t i = ρ'.get t i
  | .i32 => (h i hi).1
  | .i64 => (h i hi).2.1

theorem EqBelow.refl (n : Nat) (ρ : Env) : EqBelow n ρ ρ := fun _ _ => ⟨rfl, rfl, rfl⟩

theorem EqBelow.symm {n : Nat} {ρ ρ' : Env} (h : EqBelow n ρ ρ') : EqBelow n ρ' ρ :=
  fun i hi => ⟨(h i hi).1.symm, (h i hi).2.1.symm, (h i hi).2.2.symm⟩

theorem EqBelow.mono {n n' : Nat} {ρ ρ' : Env} (h : EqBelow n ρ ρ') (hn : n' ≤ n) :
    EqBelow n' ρ ρ' := fun i hi => h i (by omega)

theorem MR.den_eqBelow {n : Nat} {ρ ρ' ξ ξ' : Env} (hρ : EqBelow n ρ ρ') (hξ : EqBelow n ξ ξ') :
    ∀ m : MR, m.vlt n = true → m.den ρ ξ = m.den ρ' ξ'
  | .v k, h => (hρ k (by simpa [MR.vlt] using h)).2.2
  | .cur, h => (hξ 0 (by simpa [MR.vlt] using h)).2.2

theorem Tm.den_eqBelow {n : Nat} {ρ ρ' ξ ξ' : Env} (hρ : EqBelow n ρ ρ') (hξ : EqBelow n ξ ξ') :
    ∀ {t : IntType} (a : Tm t), a.vlt n = true → a.den F ρ ξ = a.den F ρ' ξ'
  | _, .var t i, h => EqBelow.get hρ (by simpa [Tm.vlt] using h) t
  | _, .loc t j, h => EqBelow.get hξ (by simpa [Tm.vlt] using h) t
  | _, .lit t n, _ => rfl
  | _, .un op a, h => by simp only [Tm.den, Tm.den_eqBelow hρ hξ a h]
  | _, .bin op a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_eqBelow hρ hξ a h.1, Tm.den_eqBelow hρ hξ b h.2]
  | _, .rel op a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_eqBelow hρ hξ a h.1, Tm.den_eqBelow hρ hξ b h.2]; rfl
  | _, .eqz a, h => by simp only [Tm.den, Tm.den_eqBelow hρ hξ a h]; rfl
  | _, .ite c a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_eqBelow hρ hξ c h.1.1, Tm.den_eqBelow hρ hξ a h.1.2,
      Tm.den_eqBelow hρ hξ b h.2]
  | _, .wrap a, h => by simp only [Tm.den, Tm.den_eqBelow hρ hξ a h]; rfl
  | _, .ext sx a, h => by cases sx <;> simp only [Tm.den, Tm.den_eqBelow hρ hξ a h] <;> rfl
  | _, .fn k a, h => by simp only [Tm.den, Tm.den_eqBelow hρ hξ a h]
  | _, .fn2 k a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_eqBelow hρ hξ a h.1, Tm.den_eqBelow hρ hξ b h.2]
  | _, .load t n sx m a off, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_eqBelow hρ hξ a h.2, MR.den_eqBelow hρ hξ m h.1]
  | _, .mfn k m a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_eqBelow hρ hξ a h.1.2, Tm.den_eqBelow hρ hξ b h.2,
      MR.den_eqBelow hρ hξ m h.1.1]; rfl

theorem Fm.den_eqBelow {n : Nat} {ρ ρ' ξ ξ' : Env} (hρ : EqBelow n ρ ρ') (hξ : EqBelow n ξ ξ') :
    ∀ φ : Fm, φ.vlt n = true → (φ.den F ρ ξ ↔ φ.den F ρ' ξ')
  | .tt, _ => Iff.rfl
  | .ff, _ => Iff.rfl
  | .rel op a b, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h
    simp only [Fm.den, Tm.den_eqBelow hρ hξ a h.1, Tm.den_eqBelow hρ hξ b h.2]
  | .nz a, h => by simp only [Fm.den, Tm.den_eqBelow hρ hξ a h]
  | .not p, h => by simp only [Fm.den, Fm.den_eqBelow hρ hξ p h]
  | .and p q, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h
    simp only [Fm.den, Fm.den_eqBelow hρ hξ p h.1, Fm.den_eqBelow hρ hξ q h.2]
  | .or p q, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h
    simp only [Fm.den, Fm.den_eqBelow hρ hξ p h.1, Fm.den_eqBelow hρ hξ q h.2]
  | .imp p q, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h
    simp only [Fm.den, Fm.den_eqBelow hρ hξ p h.1, Fm.den_eqBelow hρ hξ q h.2]
  | .inb m a k, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h
    simp only [Fm.den, Tm.den_eqBelow hρ hξ a h.2, MR.den_eqBelow hρ hξ m h.1]
  | .pr k m as, h => by
    simp only [Fm.vlt, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Fm.den, MR.den_eqBelow hρ hξ m h.1, Tm.dens32_eq_map]
    exact iff_of_eq (congrArg _ (List.map_congr_left fun a ha => Tm.den_eqBelow hρ hξ a (h.2 a ha)))
  | .meq m₁ m₂, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h
    simp only [Fm.den, MR.den_eqBelow hρ hξ m₁ h.1, MR.den_eqBelow hρ hξ m₂ h.2]
  | .st k m _ a _ v, h => by
    simp only [Fm.vlt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Fm.den, Tm.den_eqBelow hρ hξ a h.1.2, Tm.den_eqBelow hρ hξ v h.2,
      MR.den_eqBelow hρ hξ m h.1.1.2, (hρ k h.1.1.1).2.2]

theorem SV.den_eqBelow {n : Nat} {ρ ρ' ξ ξ' : Env} (hρ : EqBelow n ρ ρ') (hξ : EqBelow n ξ ξ') :
    ∀ v : SV, v.vlt n = true → v.den F ρ ξ = v.den F ρ' ξ'
  | .i32 a, h => by simp only [SV.den, Tm.den_eqBelow hρ hξ a h]
  | .i64 a, h => by simp only [SV.den, Tm.den_eqBelow hρ hξ a h]

theorem MR.vlt_mono {n n' : Nat} (hn : n ≤ n') : ∀ m : MR, m.vlt n = true → m.vlt n' = true
  | .v k, h => by simp only [MR.vlt, decide_eq_true_eq] at h ⊢; omega
  | .cur, h => by simp only [MR.vlt, decide_eq_true_eq] at h ⊢; omega

theorem Tm.vlt_mono {n n' : Nat} (hn : n ≤ n') :
    ∀ {t : IntType} (a : Tm t), a.vlt n = true → a.vlt n' = true
  | _, .var _ i, h => by simp only [Tm.vlt, decide_eq_true_eq] at h ⊢; omega
  | _, .loc _ j, h => by simp only [Tm.vlt, decide_eq_true_eq] at h ⊢; omega
  | _, .lit _ _, _ => rfl
  | _, .un _ a, h => Tm.vlt_mono hn a h
  | _, .bin _ a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨Tm.vlt_mono hn a h.1, Tm.vlt_mono hn b h.2⟩
  | _, .rel _ a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨Tm.vlt_mono hn a h.1, Tm.vlt_mono hn b h.2⟩
  | _, .eqz a, h => Tm.vlt_mono hn a h
  | _, .ite c a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨Tm.vlt_mono hn c h.1.1, Tm.vlt_mono hn a h.1.2⟩, Tm.vlt_mono hn b h.2⟩
  | _, .wrap a, h => Tm.vlt_mono hn a h
  | _, .ext _ a, h => Tm.vlt_mono hn a h
  | _, .fn _ a, h => Tm.vlt_mono hn a h
  | _, .fn2 _ a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨Tm.vlt_mono hn a h.1, Tm.vlt_mono hn b h.2⟩
  | _, .load _ _ _ m a _, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨MR.vlt_mono hn m h.1, Tm.vlt_mono hn a h.2⟩
  | _, .mfn _ m a b, h => by
    simp only [Tm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨MR.vlt_mono hn m h.1.1, Tm.vlt_mono hn a h.1.2⟩, Tm.vlt_mono hn b h.2⟩

theorem Fm.vlt_mono {n n' : Nat} (hn : n ≤ n') : ∀ φ : Fm, φ.vlt n = true → φ.vlt n' = true
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .rel _ a b, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨Tm.vlt_mono hn a h.1, Tm.vlt_mono hn b h.2⟩
  | .nz a, h => Tm.vlt_mono hn a h
  | .not p, h => Fm.vlt_mono hn p h
  | .and p q, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨Fm.vlt_mono hn p h.1, Fm.vlt_mono hn q h.2⟩
  | .or p q, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨Fm.vlt_mono hn p h.1, Fm.vlt_mono hn q h.2⟩
  | .imp p q, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨Fm.vlt_mono hn p h.1, Fm.vlt_mono hn q h.2⟩
  | .inb m a _, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨MR.vlt_mono hn m h.1, Tm.vlt_mono hn a h.2⟩
  | .pr _ m as, h => by
    simp only [Fm.vlt, Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨MR.vlt_mono hn m h.1, fun a ha => Tm.vlt_mono hn a (h.2 a ha)⟩
  | .meq m₁ m₂, h => by
    simp only [Fm.vlt, Bool.and_eq_true] at h ⊢
    exact ⟨MR.vlt_mono hn m₁ h.1, MR.vlt_mono hn m₂ h.2⟩
  | .st k m _ a _ v, h => by
    simp only [Fm.vlt, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨⟨by omega, MR.vlt_mono hn m h.1.1.2⟩, Tm.vlt_mono hn a h.1.2⟩,
      Tm.vlt_mono hn v h.2⟩

theorem SV.vlt_mono {n n' : Nat} (hn : n ≤ n') : ∀ v : SV, v.vlt n = true → v.vlt n' = true
  | .i32 a, h => Tm.vlt_mono hn a h
  | .i64 a, h => Tm.vlt_mono hn a h

/-- A scoped annotation, substituted with values below `n` and a memory variable below `n`, is
below `n` (if the parameters are). -/
theorem MR.vlt_subst {n cm : Nat} (hcm : cm < n) (h0 : 0 < n) :
    ∀ m : MR, m.scoped = true → (m.subst cm).vlt n = true
  | .v k, h => by
    obtain rfl : k = 0 := by simpa [MR.scoped] using h
    simpa [MR.subst, MR.vlt] using h0
  | .cur, _ => by simpa [MR.subst, MR.vlt] using hcm

theorem SV.vlt_as {n : Nat} {v : SV} {t : IntType} {a : Tm t} (hv : v.vlt n = true)
    (h : v.as t = some a) : a.vlt n = true := by
  cases v <;> cases t <;> simp only [SV.as, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact hv

theorem Tm.vlt_subst {n cm : Nat} {ps : List IntType} {ls : List SV} (hp : ps.length ≤ n)
    (hcm : cm < n) (h0 : 0 < n) (hls : ∀ v ∈ ls, v.vlt n = true) :
    ∀ {t : IntType} (a : Tm t), a.scoped ps = true → (a.subst ls cm).vlt n = true
  | _, .var t i, h => by
    have := (List.getElem?_eq_some_iff.mp (by simpa [Tm.scoped] using h)).1
    simp only [Tm.subst, Tm.vlt, decide_eq_true_eq]
    omega
  | _, .loc t j, _ => by
    rcases hj : ls[j]? with _ | v
    · simp [Tm.subst, hj, Tm.vlt]
    · rcases ha : v.as t with _ | a
      · simp [Tm.subst, hj, ha, Tm.vlt]
      · simpa [Tm.subst, hj, ha] using SV.vlt_as (hls v (List.mem_of_getElem? hj)) ha
  | _, .lit _ _, _ => rfl
  | _, .un _ a, h => Tm.vlt_subst hp hcm h0 hls a h
  | _, .bin _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨Tm.vlt_subst hp hcm h0 hls a h.1, Tm.vlt_subst hp hcm h0 hls b h.2⟩
  | _, .rel _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨Tm.vlt_subst hp hcm h0 hls a h.1, Tm.vlt_subst hp hcm h0 hls b h.2⟩
  | _, .eqz a, h => Tm.vlt_subst hp hcm h0 hls a h
  | _, .ite c a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨⟨Tm.vlt_subst hp hcm h0 hls c h.1.1, Tm.vlt_subst hp hcm h0 hls a h.1.2⟩,
      Tm.vlt_subst hp hcm h0 hls b h.2⟩
  | _, .wrap a, h => Tm.vlt_subst hp hcm h0 hls a h
  | _, .ext _ a, h => Tm.vlt_subst hp hcm h0 hls a h
  | _, .fn _ a, h => Tm.vlt_subst hp hcm h0 hls a h
  | _, .fn2 _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨Tm.vlt_subst hp hcm h0 hls a h.1, Tm.vlt_subst hp hcm h0 hls b h.2⟩
  | _, .load _ _ _ m a _, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨MR.vlt_subst hcm h0 m h.1, Tm.vlt_subst hp hcm h0 hls a h.2⟩
  | _, .mfn _ m a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨⟨MR.vlt_subst hcm h0 m h.1.1, Tm.vlt_subst hp hcm h0 hls a h.1.2⟩,
      Tm.vlt_subst hp hcm h0 hls b h.2⟩

theorem Fm.vlt_subst {n cm : Nat} {ps : List IntType} {ls : List SV} (hp : ps.length ≤ n)
    (hcm : cm < n) (h0 : 0 < n) (hls : ∀ v ∈ ls, v.vlt n = true) :
    ∀ φ : Fm, φ.scoped ps = true → (φ.subst ls cm).vlt n = true
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .rel _ a b, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨Tm.vlt_subst hp hcm h0 hls a h.1, Tm.vlt_subst hp hcm h0 hls b h.2⟩
  | .nz a, h => Tm.vlt_subst hp hcm h0 hls a h
  | .not p, h => Fm.vlt_subst hp hcm h0 hls p h
  | .and p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨Fm.vlt_subst hp hcm h0 hls p h.1, Fm.vlt_subst hp hcm h0 hls q h.2⟩
  | .or p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨Fm.vlt_subst hp hcm h0 hls p h.1, Fm.vlt_subst hp hcm h0 hls q h.2⟩
  | .imp p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨Fm.vlt_subst hp hcm h0 hls p h.1, Fm.vlt_subst hp hcm h0 hls q h.2⟩
  | .inb m a _, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨MR.vlt_subst hcm h0 m h.1, Tm.vlt_subst hp hcm h0 hls a h.2⟩
  | .pr _ m as, h => by
    simp only [Fm.scoped, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Fm.subst, Fm.vlt, Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨MR.vlt_subst hcm h0 m h.1, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact Tm.vlt_subst hp hcm h0 hls a (h.2 a ha)
  | .meq m₁ m₂, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨MR.vlt_subst hcm h0 m₁ h.1, MR.vlt_subst hcm h0 m₂ h.2⟩
  | .st _ _ _ _ _ _, h => by simp [Fm.scoped] at h

/-! ## Symbolic values -/

theorem SV.den_of (ρ ξ : Env) : ∀ (t : IntType) (a : Tm t),
    (SV.of t a).den F ρ ξ = .num ⟨.int t, a.den F ρ ξ⟩
  | .i32, _ => rfl
  | .i64, _ => rfl

theorem SV.ty_of : ∀ (t : IntType) (a : Tm t), (SV.of t a).ty = t
  | .i32, _ => rfl
  | .i64, _ => rfl

theorem SV.vlt_of {n : Nat} : ∀ (t : IntType) (a : Tm t), (SV.of t a).vlt n = a.vlt n
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

theorem selV_vlt {n : Nat} {c : Tm .i32} {v₁ v₂ v : SV} (h : selV c v₁ v₂ = some v)
    (hc : c.vlt n = true) (h₁ : v₁.vlt n = true) (h₂ : v₂.vlt n = true) :
    v.vlt n = true := by
  cases v₁ <;> cases v₂ <;> simp only [selV, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp_all [SV.vlt, Tm.vlt]

/-! ## Path conditions -/

open Silmaril.Wasm.Auto.VCGen (relV_ne_zero eqzV_ne_zero nz32_iff) in
theorem den_condF (ρ ξ : Env) (c : Tm .i32) :
    (condF c).den F ρ ξ ↔ (c.den F ρ ξ : BitVec 32) ≠ 0 := by
  cases c with
  | rel op a b => exact (relV_ne_zero _ _ _ _).symm
  | @eqz t a =>
    simp only [condF, Fm.den, relP, Tm.den]
    cases t <;> exact (eqzV_ne_zero _ (a.den F ρ ξ)).symm
  | _ => exact nz32_iff _

open Silmaril.Wasm.Auto.VCGen (relV_ne_zero eqzV_ne_zero nz32_iff) in
theorem den_ncondF (ρ ξ : Env) (c : Tm .i32) :
    (ncondF c).den F ρ ξ ↔ (c.den F ρ ξ : BitVec 32) = 0 := by
  cases c with
  | rel op a b => exact (not_congr (relV_ne_zero _ _ _ _)).symm.trans not_not
  | @eqz t a =>
    simp only [ncondF, Fm.den, relP, Tm.den]
    cases t <;> exact (not_congr (eqzV_ne_zero _ (a.den F ρ ξ))).symm.trans not_not
  | _ => exact (not_congr (nz32_iff _)).trans not_not

theorem condF_vlt {n : Nat} {c : Tm .i32} (h : c.vlt n = true) : (condF c).vlt n = true := by
  cases c <;> simp_all [condF, Fm.vlt, Tm.vlt]

theorem ncondF_vlt {n : Nat} {c : Tm .i32} (h : c.vlt n = true) :
    (ncondF c).vlt n = true := by
  cases c <;> simp_all [ncondF, Fm.vlt, Tm.vlt]

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

end Silmaril.Proofs.Wasm.Auto.VCGen2