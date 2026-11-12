module

public import Silmaril.Proofs.Wasm.Auto2.VCGen.Basic

/-!
# The VC generator with SSA names and memory: renaming a callee's annotations

`Tm.den_ren`, `Fm.den_ren`: a callee's annotation renamed to a call site (`ren n m`: parameter
`i` is variable `n + i`, the memory at entry is memory variable `m`) means the annotation in the
environment `renEnv ρ n m`. `Fm.vlt_ren_subst`: renamed and substituted, it is below the next
fresh variable.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCGen

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {F : Fns}

/-- The callee's environment at a call site: parameter `i` is variable `n + i`, the memory at
entry is memory variable `m`. -/
def renEnv (ρ : Env) (n m : Nat) : Env where
  e32 i := ρ.e32 (n + i)
  e64 i := ρ.e64 (n + i)
  mem _ := ρ.mem m

theorem renEnv_get (ρ : Env) (n m : Nat) : ∀ (t : IntType) (i : Nat),
    (renEnv ρ n m).get t i = ρ.get t (n + i)
  | .i32, _ => rfl
  | .i64, _ => rfl

theorem MR.den_ren (ρ ξ : Env) (n m : Nat) :
    ∀ r : MR, (r.ren m).den ρ ξ = r.den (renEnv ρ n m) ξ
  | .v _ => rfl
  | .cur => rfl

theorem Tm.den_ren (ρ ξ : Env) (n m : Nat) :
    ∀ {t : IntType} (a : Tm t), (a.ren n m).den F ρ ξ = a.den F (renEnv ρ n m) ξ
  | _, .var t i => (renEnv_get ρ n m t i).symm
  | _, .loc _ _ => rfl
  | _, .lit _ _ => rfl
  | _, .un _ a => by simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a]
  | _, .bin _ a b => by simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a, Tm.den_ren ρ ξ n m b]
  | _, .rel _ a b => by simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a, Tm.den_ren ρ ξ n m b]; rfl
  | _, .eqz a => by simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a]; rfl
  | _, .ite c a b => by
    simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m c, Tm.den_ren ρ ξ n m a, Tm.den_ren ρ ξ n m b]
  | _, .wrap a => by simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a]; rfl
  | _, .ext sx a => by cases sx <;> simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a] <;> rfl
  | _, .fn _ a => by simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a]
  | _, .fn2 _ a b => by simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a, Tm.den_ren ρ ξ n m b]
  | _, .load _ _ _ r a _ => by
    simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a, MR.den_ren ρ ξ n m r]
  | _, .mfn _ r a b => by
    simp only [Tm.ren, Tm.den, Tm.den_ren ρ ξ n m a, Tm.den_ren ρ ξ n m b, MR.den_ren ρ ξ n m r]; rfl

theorem Tm.dens32_ren (ρ ξ : Env) (n m : Nat) (as : List (Tm .i32)) :
    Tm.dens32 F ρ ξ (as.map (Tm.ren n m)) = Tm.dens32 F (renEnv ρ n m) ξ as := by
  induction as with
  | nil => rfl
  | cons a as ih => exact congrArg₂ List.cons (Tm.den_ren ρ ξ n m a) ih

theorem Fm.den_ren {ps : List IntType} (ρ ξ : Env) (n m : Nat) :
    ∀ φ : Fm, φ.scoped ps = true → ((φ.ren n m).den F ρ ξ ↔ φ.den F (renEnv ρ n m) ξ)
  | .tt, _ => Iff.rfl
  | .ff, _ => Iff.rfl
  | .rel _ a b, _ => by simp only [Fm.ren, Fm.den, Tm.den_ren]
  | .nz a, _ => by simp only [Fm.ren, Fm.den, Tm.den_ren]
  | .not p, h => by simp only [Fm.ren, Fm.den, Fm.den_ren ρ ξ n m p h]
  | .and p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.ren, Fm.den, Fm.den_ren ρ ξ n m p h.1, Fm.den_ren ρ ξ n m q h.2]
  | .or p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.ren, Fm.den, Fm.den_ren ρ ξ n m p h.1, Fm.den_ren ρ ξ n m q h.2]
  | .imp p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.ren, Fm.den, Fm.den_ren ρ ξ n m p h.1, Fm.den_ren ρ ξ n m q h.2]
  | .inb r a _, _ => by simp only [Fm.ren, Fm.den, Tm.den_ren, MR.den_ren ρ ξ n m r]
  | .pr _ r as, _ => by simp only [Fm.ren, Fm.den, Tm.dens32_ren, MR.den_ren ρ ξ n m r]
  | .pr2 _ r₁ r₂ as, _ => by
    simp only [Fm.ren, Fm.den, Tm.dens32_ren, MR.den_ren ρ ξ n m r₁, MR.den_ren ρ ξ n m r₂]
  | .meq r₁ r₂, _ => by simp only [Fm.ren, Fm.den, MR.den_ren ρ ξ n m]
  | .st _ _ _ _ _ _, h => by simp [Fm.scoped] at h

theorem MR.scoped_subst_zero : ∀ m : MR, m.scoped = true → (m.subst 0).scoped = true
  | .v _, h => h
  | .cur, _ => rfl

theorem Tm.scoped_subst_nil {ps : List IntType} :
    ∀ {t : IntType} (a : Tm t), a.scoped ps = true → (a.subst [] 0).scoped ps = true
  | _, .var _ _, h => h
  | _, .loc _ _, _ => rfl
  | _, .lit _ _, _ => rfl
  | _, .un _ a, h => Tm.scoped_subst_nil a h
  | _, .bin _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.scoped, Bool.and_eq_true]
    exact ⟨Tm.scoped_subst_nil a h.1, Tm.scoped_subst_nil b h.2⟩
  | _, .rel _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.scoped, Bool.and_eq_true]
    exact ⟨Tm.scoped_subst_nil a h.1, Tm.scoped_subst_nil b h.2⟩
  | _, .eqz a, h => Tm.scoped_subst_nil a h
  | _, .ite c a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.scoped, Bool.and_eq_true]
    exact ⟨⟨Tm.scoped_subst_nil c h.1.1, Tm.scoped_subst_nil a h.1.2⟩, Tm.scoped_subst_nil b h.2⟩
  | _, .wrap a, h => Tm.scoped_subst_nil a h
  | _, .ext _ a, h => Tm.scoped_subst_nil a h
  | _, .fn _ a, h => Tm.scoped_subst_nil a h
  | _, .fn2 _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.scoped, Bool.and_eq_true]
    exact ⟨Tm.scoped_subst_nil a h.1, Tm.scoped_subst_nil b h.2⟩
  | _, .load _ _ _ m a _, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.scoped, Bool.and_eq_true]
    exact ⟨MR.scoped_subst_zero m h.1, Tm.scoped_subst_nil a h.2⟩
  | _, .mfn _ m a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.subst, Tm.scoped, Bool.and_eq_true]
    exact ⟨⟨MR.scoped_subst_zero m h.1.1, Tm.scoped_subst_nil a h.1.2⟩, Tm.scoped_subst_nil b h.2⟩

theorem Fm.scoped_subst_nil {ps : List IntType} : ∀ φ : Fm, φ.scoped ps = true →
    (φ.subst [] 0).scoped ps = true
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .rel _ a b, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.scoped, Bool.and_eq_true]
    exact ⟨Tm.scoped_subst_nil a h.1, Tm.scoped_subst_nil b h.2⟩
  | .nz a, h => Tm.scoped_subst_nil a h
  | .not p, h => Fm.scoped_subst_nil p h
  | .and p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.scoped, Bool.and_eq_true]
    exact ⟨Fm.scoped_subst_nil p h.1, Fm.scoped_subst_nil q h.2⟩
  | .or p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.scoped, Bool.and_eq_true]
    exact ⟨Fm.scoped_subst_nil p h.1, Fm.scoped_subst_nil q h.2⟩
  | .imp p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.scoped, Bool.and_eq_true]
    exact ⟨Fm.scoped_subst_nil p h.1, Fm.scoped_subst_nil q h.2⟩
  | .inb m a _, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.scoped, Bool.and_eq_true]
    exact ⟨MR.scoped_subst_zero m h.1, Tm.scoped_subst_nil a h.2⟩
  | .pr _ m as, h => by
    simp only [Fm.scoped, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Fm.subst, Fm.scoped, Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨MR.scoped_subst_zero m h.1, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact Tm.scoped_subst_nil a (h.2 a ha)
  | .pr2 _ m₁ m₂ as, h => by
    simp only [Fm.scoped, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Fm.subst, Fm.scoped, Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨⟨MR.scoped_subst_zero m₁ h.1.1, MR.scoped_subst_zero m₂ h.1.2⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact Tm.scoped_subst_nil a (h.2 a ha)
  | .meq m₁ m₂, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.subst, Fm.scoped, Bool.and_eq_true]
    exact ⟨MR.scoped_subst_zero m₁ h.1, MR.scoped_subst_zero m₂ h.2⟩
  | .st _ _ _ _ _ _, h => by simp [Fm.scoped] at h

/-- The precondition does not depend on the placeholder environment. -/
theorem preF_den_iff {S : FnSpec} (ρ ξ ξ' : Env) : S.preF.den F ρ ξ ↔ S.preF.den F ρ ξ' := by
  have : locEnv F ρ ξ [] 0 = locEnv F ρ ξ' [] 0 := by simp [locEnv]
  rw [FnSpec.preF, Fm.den_subst, Fm.den_subst, this]

/-! ## Well-scoped specifications -/

theorem wellScoped_pre {S : FnSpec} (hS : S.wellScoped = true) : S.pre.scoped S.ents = true := by
  simp only [FnSpec.wellScoped, Bool.and_eq_true] at hS
  exact hS.1.1.1

theorem wellScoped_post {S : FnSpec} (hS : S.wellScoped = true) :
    S.post.scoped S.ents = true := by
  simp only [FnSpec.wellScoped, Bool.and_eq_true] at hS
  exact hS.1.1.2

theorem wellScoped_inv {S : FnSpec} (hS : S.wellScoped = true) :
    ∀ φ ∈ S.inv, φ.scoped S.ents = true := by
  simp only [FnSpec.wellScoped, Bool.and_eq_true, List.all_eq_true] at hS
  exact hS.1.2

theorem wellScoped_calls {S : FnSpec} (hS : S.wellScoped = true) :
    ∀ c ∈ S.calls, c.2.1.pre.scoped c.2.1.ents = true ∧ c.2.1.post.scoped c.2.1.ents = true := by
  simp only [FnSpec.wellScoped, Bool.and_eq_true, List.all_eq_true] at hS
  exact hS.2

/-! ## Freshness -/

section Vlt

variable {N n m cm : Nat} {ps : List IntType} {ls : List SV}

theorem MR.vlt_ren_subst (hm : m < N) (hcm : cm < N) : ∀ r : MR, ((r.ren m).subst cm).vlt N = true
  | .v _ => by simpa [MR.ren, MR.subst, MR.vlt] using hm
  | .cur => by simpa [MR.ren, MR.subst, MR.vlt] using hcm

theorem Tm.vlt_ren_subst (hn : n + ps.length ≤ N) (hm : m < N) (hcm : cm < N)
    (hls : ∀ v ∈ ls, v.vlt N = true) :
    ∀ {t : IntType} (a : Tm t), a.scoped ps = true → ((a.ren n m).subst ls cm).vlt N = true
  | _, .var t i, h => by
    have := (List.getElem?_eq_some_iff.mp (by simpa [Tm.scoped] using h)).1
    simp only [Tm.ren, Tm.subst, Tm.vlt, decide_eq_true_eq]
    omega
  | _, .loc t j, _ => by
    rcases hj : ls[j]? with _ | v
    · simp [Tm.ren, Tm.subst, hj, Tm.vlt]
    · rcases ha : v.as t with _ | a
      · simp [Tm.ren, Tm.subst, hj, ha, Tm.vlt]
      · simpa [Tm.ren, Tm.subst, hj, ha] using SV.vlt_as (hls v (List.mem_of_getElem? hj)) ha
  | _, .lit _ _, _ => rfl
  | _, .un _ a, h => Tm.vlt_ren_subst hn hm hcm hls a h
  | _, .bin _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.ren, Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨Tm.vlt_ren_subst hn hm hcm hls a h.1, Tm.vlt_ren_subst hn hm hcm hls b h.2⟩
  | _, .rel _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.ren, Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨Tm.vlt_ren_subst hn hm hcm hls a h.1, Tm.vlt_ren_subst hn hm hcm hls b h.2⟩
  | _, .eqz a, h => Tm.vlt_ren_subst hn hm hcm hls a h
  | _, .ite c a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.ren, Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨⟨Tm.vlt_ren_subst hn hm hcm hls c h.1.1, Tm.vlt_ren_subst hn hm hcm hls a h.1.2⟩,
      Tm.vlt_ren_subst hn hm hcm hls b h.2⟩
  | _, .wrap a, h => Tm.vlt_ren_subst hn hm hcm hls a h
  | _, .ext _ a, h => Tm.vlt_ren_subst hn hm hcm hls a h
  | _, .fn _ a, h => Tm.vlt_ren_subst hn hm hcm hls a h
  | _, .fn2 _ a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.ren, Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨Tm.vlt_ren_subst hn hm hcm hls a h.1, Tm.vlt_ren_subst hn hm hcm hls b h.2⟩
  | _, .load _ _ _ r a _, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.ren, Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨MR.vlt_ren_subst hm hcm r, Tm.vlt_ren_subst hn hm hcm hls a h.2⟩
  | _, .mfn _ r a b, h => by
    simp only [Tm.scoped, Bool.and_eq_true] at h
    simp only [Tm.ren, Tm.subst, Tm.vlt, Bool.and_eq_true]
    exact ⟨⟨MR.vlt_ren_subst hm hcm r, Tm.vlt_ren_subst hn hm hcm hls a h.1.2⟩,
      Tm.vlt_ren_subst hn hm hcm hls b h.2⟩

theorem Fm.vlt_ren_subst (hn : n + ps.length ≤ N) (hm : m < N) (hcm : cm < N)
    (hls : ∀ v ∈ ls, v.vlt N = true) :
    ∀ φ : Fm, φ.scoped ps = true → ((φ.ren n m).subst ls cm).vlt N = true
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .rel _ a b, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.ren, Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨Tm.vlt_ren_subst hn hm hcm hls a h.1, Tm.vlt_ren_subst hn hm hcm hls b h.2⟩
  | .nz a, h => Tm.vlt_ren_subst hn hm hcm hls a h
  | .not p, h => Fm.vlt_ren_subst hn hm hcm hls p h
  | .and p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.ren, Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨Fm.vlt_ren_subst hn hm hcm hls p h.1, Fm.vlt_ren_subst hn hm hcm hls q h.2⟩
  | .or p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.ren, Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨Fm.vlt_ren_subst hn hm hcm hls p h.1, Fm.vlt_ren_subst hn hm hcm hls q h.2⟩
  | .imp p q, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.ren, Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨Fm.vlt_ren_subst hn hm hcm hls p h.1, Fm.vlt_ren_subst hn hm hcm hls q h.2⟩
  | .inb r a _, h => by
    simp only [Fm.scoped, Bool.and_eq_true] at h
    simp only [Fm.ren, Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨MR.vlt_ren_subst hm hcm r, Tm.vlt_ren_subst hn hm hcm hls a h.2⟩
  | .pr _ r as, h => by
    simp only [Fm.scoped, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Fm.ren, Fm.subst, Fm.vlt, Bool.and_eq_true, List.all_eq_true, List.map_map,
      List.mem_map, Function.comp_apply]
    refine ⟨MR.vlt_ren_subst hm hcm r, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact Tm.vlt_ren_subst hn hm hcm hls a (h.2 a ha)
  | .pr2 _ r₁ r₂ as, h => by
    simp only [Fm.scoped, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Fm.ren, Fm.subst, Fm.vlt, Bool.and_eq_true, List.all_eq_true, List.map_map,
      List.mem_map, Function.comp_apply]
    refine ⟨⟨MR.vlt_ren_subst hm hcm r₁, MR.vlt_ren_subst hm hcm r₂⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact Tm.vlt_ren_subst hn hm hcm hls a (h.2 a ha)
  | .meq r₁ r₂, _ => by
    simp only [Fm.ren, Fm.subst, Fm.vlt, Bool.and_eq_true]
    exact ⟨MR.vlt_ren_subst hm hcm r₁, MR.vlt_ren_subst hm hcm r₂⟩
  | .st _ _ _ _ _ _, h => by simp [Fm.scoped] at h

end Vlt

end Silmaril.Wasm.Auto2.VCGen
