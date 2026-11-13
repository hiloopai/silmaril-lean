module

public import Silmaril.Wasm.Models.FunRefClo.Defs
public import Silmaril.Wasm.Models.Game.Thms
public import Mathlib.Data.List.Forall2
public import Silmaril.Wasm.Models.FunRef.Thms

/-!
# FunRefClo: fuel, type preservation and the game reading

* `eval_succ`, `eval_le`: more fuel gives the same result; `Prog.Eval.unique`.
* `eval_sound`: **type preservation** with a heap typing. A well-typed term that evaluates in a
  typed heap and environment returns a value of its type in a typed heap extending the heap
  typing. Closures and cells together give general recursion, so there is no normalisation.
* `Prog.Eval.sound`, `Prog.obs_eq`, `Prog.obs_eq_word`, `strat_answers`: as for FunClo.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefClo

open Silmaril.Wasm (Behaviour)
open Silmaril.Games
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunRef (getElem?_of_prefix forall₂_getElem? forall₂_set)

/-! ## Fuel -/

/-- One more unit of fuel gives the same result. -/
theorem eval_succ : ∀ {k : Nat} {σ : Heap} {ρ : List Val} {e : Tm} {r : Val × Heap},
    eval k σ ρ e = some r → eval (k + 1) σ ρ e = some r
  | 0, _, _, _, _, h => by simp [eval] at h
  | k + 1, σ, ρ, e, r, h => by
    cases e with
    | var i => exact h
    | int n => exact h
    | bool b => exact h
    | fix b => exact h
    | arith op a b =>
      simp only [eval] at h ⊢
      split at h
      · next x σ₁ ha =>
        split at h
        · next y σ₂ hb => simp only [eval_succ ha, eval_succ hb]; exact h
        · cases h
      · cases h
    | cmp op a b =>
      simp only [eval] at h ⊢
      split at h
      · next x σ₁ ha =>
        split at h
        · next y σ₂ hb => simp only [eval_succ ha, eval_succ hb]; exact h
        · cases h
      · cases h
    | ite c t e =>
      simp only [eval] at h ⊢
      split at h
      · next σ₁ hc => simp only [eval_succ hc]; exact eval_succ h
      · next σ₁ hc => simp only [eval_succ hc]; exact eval_succ h
      · cases h
    | let_ a b =>
      simp only [eval] at h ⊢
      split at h
      · next u σ₁ hu => simp only [eval_succ hu]; exact eval_succ h
      · cases h
    | pair a b =>
      simp only [eval] at h ⊢
      split at h
      · next x σ₁ ha =>
        split at h
        · next y σ₂ hb => simp only [eval_succ ha, eval_succ hb]; exact h
        · cases h
      · cases h
    | fst e =>
      simp only [eval] at h ⊢
      split at h
      · next x y σ₁ he => simp only [eval_succ he]; exact h
      · cases h
    | snd e =>
      simp only [eval] at h ⊢
      split at h
      · next x y σ₁ he => simp only [eval_succ he]; exact h
      · cases h
    | inl e =>
      simp only [eval, Option.map_eq_some_iff] at h ⊢
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨u, eval_succ hu, rfl⟩
    | inr e =>
      simp only [eval, Option.map_eq_some_iff] at h ⊢
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨u, eval_succ hu, rfl⟩
    | case e l r =>
      simp only [eval] at h ⊢
      split at h
      · next u σ₁ hu => simp only [eval_succ hu]; exact eval_succ h
      · next u σ₁ hu => simp only [eval_succ hu]; exact eval_succ h
      · cases h
    | app f a =>
      simp only [eval] at h ⊢
      split at h
      · next b ρ' σ₁ hf =>
        split at h
        · next u σ₂ ha => simp only [eval_succ hf, eval_succ ha]; exact eval_succ h
        · cases h
      · cases h
    | ref e =>
      simp only [eval] at h ⊢
      split at h
      · next u σ₁ hu => simp only [eval_succ hu]; exact h
      · cases h
    | get e =>
      simp only [eval] at h ⊢
      split at h
      · next l σ₁ he => simp only [eval_succ he]; exact h
      · cases h
    | set a b =>
      simp only [eval] at h ⊢
      split at h
      · next l σ₁ ha =>
        split at h
        · next u σ₂ hb => simp only [eval_succ ha, eval_succ hb]; exact h
        · cases h
      · cases h

/-- **More fuel gives the same result.** -/
theorem eval_le {k k' : Nat} {σ : Heap} {ρ : List Val} {e : Tm} {r : Val × Heap}
    (h : eval k σ ρ e = some r) (hk : k ≤ k') : eval k' σ ρ e = some r := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => exact h
  | succ j ih => exact eval_succ (ih (Nat.le_add_right _ _))

theorem eval_det {k k' : Nat} {σ : Heap} {ρ : List Val} {e : Tm} {r r' : Val × Heap}
    (h : eval k σ ρ e = some r) (h' : eval k' σ ρ e = some r') : r = r' := by
  have h₁ := eval_le h (Nat.le_max_left k k')
  have h₂ := eval_le h' (Nat.le_max_right k k')
  exact Option.some.inj (h₁.symm.trans h₂)

/-- A program returns at most one value on an argument. -/
theorem Prog.Eval.unique {p : Prog} {n : BitVec 31} {v v' : Val} (h : p.Eval n v)
    (h' : p.Eval n v') : v = v' := by
  obtain ⟨k, σ, hk⟩ := h
  obtain ⟨k', σ', hk'⟩ := h'
  exact congrArg Prod.fst (eval_det hk hk')

/-! ## Typed values and heaps -/

mutual
/-- Typing survives heap growth. -/
theorem ValTy.mono {Ψ Ψ' : List Ty} (h : Ψ <+: Ψ') : ∀ {v : Val} {τ : Ty},
    ValTy Ψ v τ → ValTy Ψ' v τ
  | _, _, .int n => .int n
  | _, _, .bool b => .bool b
  | _, _, .pair ha hb => .pair (ValTy.mono h ha) (ValTy.mono h hb)
  | _, _, .inl τ hv => .inl τ (ValTy.mono h hv)
  | _, _, .inr σ hv => .inr σ (ValTy.mono h hv)
  | _, _, .clo hρ hb => .clo (EnvTy.mono h hρ) hb
  | _, _, .loc hl => .loc (getElem?_of_prefix h hl)

/-- Environment typing survives heap growth. -/
theorem EnvTy.mono {Ψ Ψ' : List Ty} (h : Ψ <+: Ψ') : ∀ {ρ : List Val} {Γ : List Ty},
    EnvTy Ψ ρ Γ → EnvTy Ψ' ρ Γ
  | _, _, .nil => .nil
  | _, _, .cons hv hρ => .cons (ValTy.mono h hv) (EnvTy.mono h hρ)
end

theorem EnvTy.getElem? {Ψ : List Ty} : ∀ {ρ : List Val} {Γ : List Ty}, EnvTy Ψ ρ Γ →
    ∀ {i : Nat} {τ : Ty}, Γ[i]? = some τ → ∃ v, ρ[i]? = some v ∧ ValTy Ψ v τ
  | _, _, .nil, _, _, hi => absurd hi (by simp)
  | _, _, .cons hv _, 0, _, hi => ⟨_, rfl, (Option.some.inj hi) ▸ hv⟩
  | _, _, .cons _ h, i + 1, _, hi => EnvTy.getElem? h (i := i) hi

theorem ValTy.int_inv {Ψ : List Ty} {v : Val} (h : ValTy Ψ v .int) : ∃ n, v = .int n := by
  cases h
  exact ⟨_, rfl⟩

theorem ValTy.bool_inv {Ψ : List Ty} {v : Val} (h : ValTy Ψ v .bool) : ∃ b, v = .bool b := by
  cases h
  exact ⟨_, rfl⟩

theorem ValTy.prod_inv {Ψ : List Ty} {v : Val} {σ τ : Ty} (h : ValTy Ψ v (.prod σ τ)) :
    ∃ a b, v = .pair a b ∧ ValTy Ψ a σ ∧ ValTy Ψ b τ := by
  cases h with
  | pair ha hb => exact ⟨_, _, rfl, ha, hb⟩

theorem ValTy.sum_inv {Ψ : List Ty} {v : Val} {σ τ : Ty} (h : ValTy Ψ v (.sum σ τ)) :
    (∃ a, v = .inl a ∧ ValTy Ψ a σ) ∨ (∃ b, v = .inr b ∧ ValTy Ψ b τ) := by
  cases h with
  | inl _ ha => exact .inl ⟨_, rfl, ha⟩
  | inr _ hb => exact .inr ⟨_, rfl, hb⟩

theorem ValTy.arr_inv {Ψ : List Ty} {v : Val} {σ τ : Ty} (h : ValTy Ψ v (.arr σ τ)) :
    ∃ b ρ Γ, v = .clo b ρ ∧ EnvTy Ψ ρ Γ ∧ HasTy (σ :: .arr σ τ :: Γ) b τ := by
  cases h with
  | clo hρ hb => exact ⟨_, _, _, rfl, hρ, hb⟩

theorem ValTy.ref_inv {Ψ : List Ty} {v : Val} {τ : Ty} (h : ValTy Ψ v (.ref τ)) :
    ∃ l, v = .loc l ∧ Ψ[l]? = some τ := by
  cases h with
  | loc hl => exact ⟨_, rfl, hl⟩

theorem HeapTy.alloc {Ψ : List Ty} {σ : Heap} (h : HeapTy Ψ σ) {v : Val} {τ : Ty}
    (hv : ValTy Ψ v τ) : HeapTy (Ψ ++ [τ]) (σ ++ [v]) :=
  List.rel_append (h.imp fun _ _ hu => hu.mono (List.prefix_append _ _))
    (.cons (hv.mono (List.prefix_append _ _)) .nil)

theorem HeapTy.set {Ψ : List Ty} {σ : Heap} (h : HeapTy Ψ σ) {l : Nat} {τ : Ty}
    (hl : Ψ[l]? = some τ) {v : Val} (hv : ValTy Ψ v τ) : HeapTy Ψ (σ.set l v) :=
  forall₂_set h hl hv

/-! ## Type preservation -/

/-- A typed result: a value of type `τ` in a typed heap extending `Ψ`. -/
def Out (Ψ : List Ty) (τ : Ty) (v : Val) (σ' : Heap) : Prop :=
  ∃ Ψ', Ψ <+: Ψ' ∧ HeapTy Ψ' σ' ∧ ValTy Ψ' v τ

theorem Out.of_prefix {Ψ Ψ₁ : List Ty} (h : Ψ <+: Ψ₁) {τ : Ty} {v : Val} {σ' : Heap}
    (ho : Out Ψ₁ τ v σ') : Out Ψ τ v σ' :=
  let ⟨Ψ', hΨ', hσ', hv⟩ := ho
  ⟨Ψ', h.trans hΨ', hσ', hv⟩

/-- What type preservation says at fuel `k`. -/
def Pres (k : Nat) : Prop :=
  ∀ ⦃Γ : List Ty⦄ ⦃e : Tm⦄ ⦃τ : Ty⦄, HasTy Γ e τ → ∀ ⦃Ψ : List Ty⦄ ⦃σ : Heap⦄ ⦃ρ : List Val⦄
    ⦃v : Val⦄ ⦃σ' : Heap⦄, HeapTy Ψ σ → EnvTy Ψ ρ Γ → eval k σ ρ e = some (v, σ') → Out Ψ τ v σ'

section Pres

variable {k : Nat} (ih : Pres k) {Γ : List Ty} {Ψ : List Ty} {σ : Heap} {ρ : List Val}
  {v : Val} {σ' : Heap} (hσ : HeapTy Ψ σ) (hρ : EnvTy Ψ ρ Γ)
include ih hσ hρ

theorem pres_arith {op : Arith} {a b : Tm} (ha : HasTy Γ a .int) (hb : HasTy Γ b .int)
    (h : eval (k + 1) σ ρ (.arith op a b) = some (v, σ')) : Out Ψ .int v σ' := by
  simp only [eval] at h
  split at h
  · next x σ₁ hxa =>
    split at h
    · next y σ₂ hyb =>
      obtain ⟨Ψ₁, h₁, hσ₁, -⟩ := ih ha hσ hρ hxa
      obtain ⟨Ψ₂, h₂, hσ₂, -⟩ := ih hb hσ₁ (hρ.mono h₁) hyb
      cases h
      exact ⟨Ψ₂, h₁.trans h₂, hσ₂, .int _⟩
    · cases h
  · cases h

theorem pres_cmp {op : Cmp} {a b : Tm} (ha : HasTy Γ a .int) (hb : HasTy Γ b .int)
    (h : eval (k + 1) σ ρ (.cmp op a b) = some (v, σ')) : Out Ψ .bool v σ' := by
  simp only [eval] at h
  split at h
  · next x σ₁ hxa =>
    split at h
    · next y σ₂ hyb =>
      obtain ⟨Ψ₁, h₁, hσ₁, -⟩ := ih ha hσ hρ hxa
      obtain ⟨Ψ₂, h₂, hσ₂, -⟩ := ih hb hσ₁ (hρ.mono h₁) hyb
      cases h
      exact ⟨Ψ₂, h₁.trans h₂, hσ₂, .bool _⟩
    · cases h
  · cases h

theorem pres_ite {c t e : Tm} {τ : Ty} (hc : HasTy Γ c .bool) (ht : HasTy Γ t τ)
    (he : HasTy Γ e τ) (h : eval (k + 1) σ ρ (.ite c t e) = some (v, σ')) : Out Ψ τ v σ' := by
  simp only [eval] at h
  split at h
  · next σ₁ hcv =>
    obtain ⟨Ψ₁, h₁, hσ₁, -⟩ := ih hc hσ hρ hcv
    exact (ih ht hσ₁ (hρ.mono h₁) h).of_prefix h₁
  · next σ₁ hcv =>
    obtain ⟨Ψ₁, h₁, hσ₁, -⟩ := ih hc hσ hρ hcv
    exact (ih he hσ₁ (hρ.mono h₁) h).of_prefix h₁
  · cases h

theorem pres_let {a b : Tm} {σa τ : Ty} (ha : HasTy Γ a σa) (hb : HasTy (σa :: Γ) b τ)
    (h : eval (k + 1) σ ρ (.let_ a b) = some (v, σ')) : Out Ψ τ v σ' := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu =>
    obtain ⟨Ψ₁, h₁, hσ₁, htu⟩ := ih ha hσ hρ hu
    exact (ih hb hσ₁ (.cons htu (hρ.mono h₁)) h).of_prefix h₁
  · cases h

theorem pres_pair {a b : Tm} {σa τ : Ty} (ha : HasTy Γ a σa) (hb : HasTy Γ b τ)
    (h : eval (k + 1) σ ρ (.pair a b) = some (v, σ')) : Out Ψ (.prod σa τ) v σ' := by
  simp only [eval] at h
  split at h
  · next x σ₁ hx =>
    split at h
    · next y σ₂ hy =>
      obtain ⟨Ψ₁, h₁, hσ₁, htx⟩ := ih ha hσ hρ hx
      obtain ⟨Ψ₂, h₂, hσ₂, hty⟩ := ih hb hσ₁ (hρ.mono h₁) hy
      cases h
      exact ⟨Ψ₂, h₁.trans h₂, hσ₂, .pair (htx.mono h₂) hty⟩
    · cases h
  · cases h

theorem pres_fst {e : Tm} {σa τ : Ty} (he : HasTy Γ e (.prod σa τ))
    (h : eval (k + 1) σ ρ (.fst e) = some (v, σ')) : Out Ψ σa v σ' := by
  simp only [eval] at h
  split at h
  · next x y σ₁ hx =>
    obtain ⟨Ψ₁, h₁, hσ₁, htv⟩ := ih he hσ hρ hx
    obtain ⟨a, b, hab, hta, -⟩ := htv.prod_inv
    cases hab
    cases h
    exact ⟨Ψ₁, h₁, hσ₁, hta⟩
  · cases h

theorem pres_snd {e : Tm} {σa τ : Ty} (he : HasTy Γ e (.prod σa τ))
    (h : eval (k + 1) σ ρ (.snd e) = some (v, σ')) : Out Ψ τ v σ' := by
  simp only [eval] at h
  split at h
  · next x y σ₁ hx =>
    obtain ⟨Ψ₁, h₁, hσ₁, htv⟩ := ih he hσ hρ hx
    obtain ⟨a, b, hab, -, htb⟩ := htv.prod_inv
    cases hab
    cases h
    exact ⟨Ψ₁, h₁, hσ₁, htb⟩
  · cases h

theorem pres_inl {e : Tm} {σa : Ty} (τ : Ty) (he : HasTy Γ e σa)
    (h : eval (k + 1) σ ρ (.inl e) = some (v, σ')) : Out Ψ (.sum σa τ) v σ' := by
  obtain ⟨⟨u, σ₁⟩, hu, heq⟩ : ∃ r, eval k σ ρ e = some r ∧ (Val.inl r.1, r.2) = (v, σ') := by
    simpa only [eval, Option.map_eq_some_iff] using h
  cases heq
  obtain ⟨Ψ₁, h₁, hσ₁, htu⟩ := ih he hσ hρ hu
  exact ⟨Ψ₁, h₁, hσ₁, .inl τ htu⟩

theorem pres_inr {e : Tm} {τ : Ty} (σa : Ty) (he : HasTy Γ e τ)
    (h : eval (k + 1) σ ρ (.inr e) = some (v, σ')) : Out Ψ (.sum σa τ) v σ' := by
  obtain ⟨⟨u, σ₁⟩, hu, heq⟩ : ∃ r, eval k σ ρ e = some r ∧ (Val.inr r.1, r.2) = (v, σ') := by
    simpa only [eval, Option.map_eq_some_iff] using h
  cases heq
  obtain ⟨Ψ₁, h₁, hσ₁, htu⟩ := ih he hσ hρ hu
  exact ⟨Ψ₁, h₁, hσ₁, .inr σa htu⟩

theorem pres_case {e l r : Tm} {σa τ υ : Ty} (he : HasTy Γ e (.sum σa τ))
    (hl : HasTy (σa :: Γ) l υ) (hr : HasTy (τ :: Γ) r υ)
    (h : eval (k + 1) σ ρ (.case e l r) = some (v, σ')) : Out Ψ υ v σ' := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu =>
    obtain ⟨Ψ₁, h₁, hσ₁, htu⟩ := ih he hσ hρ hu
    obtain ⟨a, ha, hta⟩ | ⟨b, hb, -⟩ := htu.sum_inv
    · cases ha
      exact (ih hl hσ₁ (.cons hta (hρ.mono h₁)) h).of_prefix h₁
    · cases hb
  · next u σ₁ hu =>
    obtain ⟨Ψ₁, h₁, hσ₁, htu⟩ := ih he hσ hρ hu
    obtain ⟨a, ha, -⟩ | ⟨b, hb, htb⟩ := htu.sum_inv
    · cases ha
    · cases hb
      exact (ih hr hσ₁ (.cons htb (hρ.mono h₁)) h).of_prefix h₁
  · cases h

theorem pres_app {f a : Tm} {σa τ : Ty} (hf : HasTy Γ f (.arr σa τ)) (ha : HasTy Γ a σa)
    (h : eval (k + 1) σ ρ (.app f a) = some (v, σ')) : Out Ψ τ v σ' := by
  simp only [eval] at h
  split at h
  · next b ρ' σ₁ hef =>
    split at h
    · next u σ₂ hea =>
      obtain ⟨Ψ₁, h₁, hσ₁, htf⟩ := ih hf hσ hρ hef
      obtain ⟨Ψ₂, h₂, hσ₂, htu⟩ := ih ha hσ₁ (hρ.mono h₁) hea
      obtain ⟨b', ρ'', Γ', hc, hρ', hb⟩ := htf.arr_inv
      cases hc
      have henv : EnvTy Ψ₂ (u :: .clo b ρ' :: ρ') (σa :: .arr σa τ :: Γ') :=
        .cons htu (.cons (htf.mono h₂) (hρ'.mono h₂))
      exact (ih hb hσ₂ henv h).of_prefix (h₁.trans h₂)
    · cases h
  · cases h

theorem pres_ref {e : Tm} {τ : Ty} (he : HasTy Γ e τ)
    (h : eval (k + 1) σ ρ (.ref e) = some (v, σ')) : Out Ψ (.ref τ) v σ' := by
  simp only [eval] at h
  split at h
  · next u σ₁ hu =>
    obtain ⟨Ψ₁, h₁, hσ₁, htu⟩ := ih he hσ hρ hu
    cases h
    have hlen : σ₁.length = Ψ₁.length := hσ₁.length_eq
    have hloc : (Ψ₁ ++ [τ])[σ₁.length]? = some τ := by simp [hlen]
    exact ⟨Ψ₁ ++ [τ], h₁.trans (List.prefix_append _ _), hσ₁.alloc htu, .loc hloc⟩
  · cases h

theorem pres_get {e : Tm} {τ : Ty} (he : HasTy Γ e (.ref τ))
    (h : eval (k + 1) σ ρ (.get e) = some (v, σ')) : Out Ψ τ v σ' := by
  simp only [eval] at h
  split at h
  · next l σ₁ hl =>
    obtain ⟨Ψ₁, h₁, hσ₁, htl⟩ := ih he hσ hρ hl
    obtain ⟨l', hl', hΨl⟩ := htl.ref_inv
    cases hl'
    obtain ⟨u, hu, htu⟩ := forall₂_getElem? hσ₁ hΨl
    have hvu : (v, σ') = (u, σ₁) := by
      rw [hu] at h; exact (Option.some.inj h).symm
    cases hvu
    exact ⟨Ψ₁, h₁, hσ₁, htu⟩
  · cases h

theorem pres_set {a b : Tm} {τ : Ty} (ha : HasTy Γ a (.ref τ)) (hb : HasTy Γ b τ)
    (h : eval (k + 1) σ ρ (.set a b) = some (v, σ')) : Out Ψ .bool v σ' := by
  simp only [eval] at h
  split at h
  · next l σ₁ hl =>
    split at h
    · next u σ₂ hu =>
      obtain ⟨Ψ₁, h₁, hσ₁, htl⟩ := ih ha hσ hρ hl
      obtain ⟨Ψ₂, h₂, hσ₂, htu⟩ := ih hb hσ₁ (hρ.mono h₁) hu
      obtain ⟨l', hl', hΨl⟩ := htl.ref_inv
      cases hl'
      split at h
      · cases h
        exact ⟨Ψ₂, h₁.trans h₂, hσ₂.set (getElem?_of_prefix h₂ hΨl) htu, .bool true⟩
      · cases h
    · cases h
  · cases h

end Pres

theorem pres_succ {k : Nat} (ih : Pres k) : Pres (k + 1) := by
  intro Γ e τ ht Ψ σ ρ v σ' hσ hρ h
  cases ht with
  | var hi =>
    obtain ⟨u, hu, htu⟩ := hρ.getElem? hi
    have hvu : (v, σ') = (u, σ) := by
      simp only [eval, hu, Option.map_some] at h; exact (Option.some.inj h).symm
    cases hvu
    exact ⟨Ψ, List.prefix_refl _, hσ, htu⟩
  | int n => cases h; exact ⟨Ψ, List.prefix_refl _, hσ, .int n⟩
  | bool b => cases h; exact ⟨Ψ, List.prefix_refl _, hσ, .bool b⟩
  | arith op ha hb => exact pres_arith ih hσ hρ ha hb h
  | cmp op ha hb => exact pres_cmp ih hσ hρ ha hb h
  | ite hc htt hte => exact pres_ite ih hσ hρ hc htt hte h
  | let_ ha hb => exact pres_let ih hσ hρ ha hb h
  | pair ha hb => exact pres_pair ih hσ hρ ha hb h
  | fst he => exact pres_fst ih hσ hρ he h
  | snd he => exact pres_snd ih hσ hρ he h
  | inl τ' he => exact pres_inl ih hσ hρ τ' he h
  | inr σ'' he => exact pres_inr ih hσ hρ σ'' he h
  | case he hl hr => exact pres_case ih hσ hρ he hl hr h
  | fix hb => cases h; exact ⟨Ψ, List.prefix_refl _, hσ, .clo hρ hb⟩
  | app hf ha => exact pres_app ih hσ hρ hf ha h
  | ref he => exact pres_ref ih hσ hρ he h
  | get he => exact pres_get ih hσ hρ he h
  | set ha hb => exact pres_set ih hσ hρ ha hb h

/-- **Type preservation.** -/
theorem eval_sound : ∀ k, Pres k
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ h => by simp [eval] at h
  | k + 1 => pres_succ (eval_sound k)

/-- A well-typed program returns a value of its result type. -/
theorem Prog.Eval.sound {p : Prog} (hp : p.WellTyped) {n : BitVec 31} {v : Val}
    (h : p.Eval n v) : ∃ Ψ, ValTy Ψ v p.res := by
  obtain ⟨k, σ, hk⟩ := h
  obtain ⟨Ψ, -, -, hv⟩ := eval_sound k hp.1 (Ψ := []) .nil (.cons (.int n) .nil) hk
  exact ⟨Ψ, hv⟩

/-! ## Observations -/

theorem Prog.obs_eq {p : Prog} {n : BitVec 31} {v : Val} (hv : p.Eval n v) :
    p.obs n = {.returns [obsWord v]} := by
  ext b
  constructor
  · rintro ⟨v', hv', rfl⟩
    rw [hv.unique hv']
    rfl
  · intro hb
    exact ⟨v, hv, hb⟩

open Classical in
/-- The word a program returns on `n` (`0` if it does not terminate). -/
noncomputable def Prog.word (p : Prog) (n : BitVec 31) : BitVec 31 :=
  if h : ∃ v, p.Eval n v then obsWord h.choose else 0

theorem Prog.word_eq {p : Prog} {n : BitVec 31} {v : Val} (hv : p.Eval n v) :
    p.word n = obsWord v := by
  have h : ∃ v, p.Eval n v := ⟨v, hv⟩
  simp only [Prog.word, h, ↓reduceDIte]
  rw [h.choose_spec.unique hv]

theorem Prog.obs_eq_word {p : Prog} (ht : p.Terminates) (n : BitVec 31) :
    p.obs n = {.returns [p.word n]} := by
  obtain ⟨v, hv⟩ := ht n
  rw [Prog.obs_eq hv, Prog.word_eq hv]

/-- Every answer to the call `n` returns the program's word on `n`. -/
def AnsIs (p : Prog) : Set (List (Move Sig.empty (callSig (BitVec 31) (Behaviour (BitVec 31))))) :=
  {s | ∀ n o, (.inr (.ans n o) : Move Sig.empty (callSig (BitVec 31) (Behaviour (BitVec 31)))) ∈ s →
    o = .returns [p.word n]}

/-- `funRefCloModel.strat p ⊨ □ AnsIs p` in `GInst`, for a terminating program. -/
theorem strat_answers {p : Prog} (ht : p.Terminates) :
    (GSen.box (AnsIs p)).holds (funRefCloModel.strat p) := by
  intro s hs n o hm
  have ho : o ∈ p.obs n := hs.2 n o hm
  rw [Prog.obs_eq_word ht n] at ho
  exact ho

end Silmaril.Wasm.Models.FunRefClo
