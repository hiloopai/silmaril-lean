module

public import Silmaril.Calculi.LambdaCube.PER.SystemF

@[expose] public section

set_option autoImplicit true

/-! # Polymorphism is not set-theoretic (Reynolds 1984)

J. C. Reynolds [reynolds-1984-polymorphism-not-set-theoretic], *Polymorphism is not set-theoretic*,
INRIA RR-0296 (1984).
Page numbers are the printed ones (PDF page = printed + 4).

`SetModel` transcribes the twelve assumptions of the section "Set-Theoretic
Semantics" (pp. 2–4) for the System F syntax of `PER/SystemF.lean`, whose type
variables are global and whose term contexts list only term variables, as in
the paper. Sets are Lean types in a fixed universe `Type u`; the ambient logic
is Lean's (classical, with choice). Adaptations to de Bruijn syntax:

* (1) `den_var`: `S#` extends `S`; `S#*π` is `CtxDen`, a product over the
  context entries.
* (3) and (4) quantify over the free type variables `Ty.FreeIn`/`Tm.TyFreeIn`;
  (4) compares the two environments pointwise by `HEq` (their values have
  provably equal types).
* (5) extension of `π` is appending older term variables (`Γ ++ Δ`), which
  keeps de Bruijn indices of `Γ`. This is weaker than the paper's arbitrary
  `π' ⊇ π`, but it is all that the proof uses: on p. 6 (rendered page checked)
  (5) extends `[p:P]` to `[p:P, h:…]` for `p[s]`, and `[p:P]` to the context of
  `λf. f(λg. h(λp. g(p[s]f)))` inside `M`; in both the new variables are bound
  outside, i.e. older.
* (12) `e ∈ E_{π−τ,ω}` (p. 4: `τ` is not free in the context) is the side
  condition `∀ B ∈ Γ, ¬ B.FreeIn 0`; `Λτ.e` is `tlam (e.tyRename rebind)` where
  `rebind` sends `0 ↦ 0` and `n + 1 ↦ n + 2`, so that `τ` (index `0`) is
  rebound; instantiating at `τ` returns the type `A` up to a provable
  equation, hence `HEq`.
* No assumption is made about `S#(Λτ.ω)`: it is an arbitrary set. In
  particular `∀` need not be a product.

The proof follows the paper: Lemma 1 (p. 4), Lemma 2 (pp. 5–6), Lemma 3
(pp. 7–8), Lemma 4 (pp. 9–10), Theorem (p. 11). Lemmas 3, 4 and the final step
are statements about sets only and are stated for an arbitrary `B`.

`UniverseModel.subsingleton` is the textbook form: a universe of sets closed
under full function spaces and products over the whole universe has only
subsingleton members. It is not a corollary of `SetModel.false` (Reynolds' weak
initiality instantiates at arbitrary sets, not only at universe members); it is
proved directly by Cantor, comparing `El (pi (fun x => arr x x))` with its
members. A claim of emptiness would be false: `UniverseModel.boolUniverse` (empty and unit) is such a universe.

Contrast: the PER model (`PER/SystemF.lean`) interprets `∀` by an intersection
of PERs on one fixed carrier. The intersection is again a PER on that carrier,
so no size increase occurs.
-/

namespace Silmaril.Calculi.LambdaCube.PERModel.Reynolds

open SystemF

universe u

/-- The functor `T s = (s → B) → B` on objects. -/
abbrev T (B s : Type u) : Type u := (s → B) → B

/-- The functor `T` on maps: `T p h = λg. h (p ; g)` (p. 5). -/
def Tmap {B s s' : Type u} (p : s → s') : T B s → T B s' := fun h g => h (g ∘ p)

/-- Environments for a term context: `S#*π = Π_{v ∈ dom π} S#(π v)` (assumption (1)). -/
def CtxDen (den : Ty → (ℕ → Type u) → Type u) (Γ : Ctx) (S : ℕ → Type u) : Type u :=
  (n : ℕ) → (A : Ty) → Γ[n]? = some A → den A S

/-- Extend an environment by a value for the newest term variable. -/
def CtxDen.cons {den : Ty → (ℕ → Type u) → Type u} {Γ : Ctx} {S : ℕ → Type u} {A : Ty}
    (x : den A S) (η : CtxDen den Γ S) : CtxDen den (A :: Γ) S
  | 0, B, h => cast (congrArg (fun X => den X S) (Option.some.inj (by simpa using h))) x
  | n + 1, B, h => η n B (by simpa using h)

/-- The renaming that rebinds type variable `0` under a new binder (for (12)). -/
def rebind : ℕ → ℕ := scons 0 (fun n => n + 2)

/-- Reynolds' set-theoretic semantics of System F, assumptions (1)–(12), pp. 3–4. -/
structure SetModel where
  /-- `S#`: the set denoted by a type under a set assignment. -/
  den : Ty → (ℕ → Type u) → Type u
  /-- (1) `S#` extends `S`. -/
  den_var : ∀ n S, den (.var n) S = S n
  /-- (2) The semantic function of a typed term. -/
  μ : ∀ {Γ t A}, Typed Γ t A → (S : ℕ → Type u) → CtxDen den Γ S → den A S
  /-- (3) A type denotes a set depending only on its free type variables. -/
  den_congr : ∀ A (S S' : ℕ → Type u), (∀ n, A.FreeIn n → S n = S' n) → den A S = den A S'
  /-- (4) A term denotes depending only on the relevant free type variables
  and on the values of the context variables. -/
  -- Environment values are compared pointwise: whole-environment HEq would
  -- impose agreement at types outside the context. This follows Reynolds'
  -- `η v = η' v` for `v ∈ dom π` (p. 3).
  μ_congr : ∀ {Γ t A} (h : Typed Γ t A) (S S' : ℕ → Type u)
    (η : CtxDen den Γ S) (η' : CtxDen den Γ S'),
    (∀ n, (t.TyFreeIn n ∨ A.FreeIn n ∨ ∃ B ∈ Γ, B.FreeIn n) → S n = S' n) →
    (∀ n B (hn : Γ[n]? = some B), HEq (η n B hn) (η' n B hn)) → HEq (μ h S η) (μ h S' η')
  /-- (5) Extending the context and the environment does not change meanings. -/
  μ_extend : ∀ {Γ Δ t A} (h : Typed Γ t A) (h' : Typed (Γ ++ Δ) t A) (S : ℕ → Type u)
    (η : CtxDen den Γ S) (η' : CtxDen den (Γ ++ Δ) S),
    (∀ n B (hn : Γ[n]? = some B) (hn' : (Γ ++ Δ)[n]? = some B), η n B hn = η' n B hn') →
    μ h S η = μ h' S η'
  /-- (6) `→` denotes the full function space. -/
  den_arr : ∀ A B S, den (.arr A B) S = (den A S → den B S)
  /-- (7) Variables. -/
  μ_var : ∀ {Γ n A} (h : Typed Γ (.var n) A) S (η : CtxDen den Γ S) (hn : Γ[n]? = some A),
    μ h S η = η n A hn
  /-- (8) Application. -/
  μ_app : ∀ {Γ t u A B} (h : Typed Γ (.app t u) B) (ht : Typed Γ t (.arr A B))
    (hu : Typed Γ u A) S (η : CtxDen den Γ S),
    μ h S η = cast (den_arr A B S) (μ ht S η) (μ hu S η)
  /-- (9) Abstraction. -/
  μ_lam : ∀ {Γ t A B} (h : Typed Γ (.lam A t) (.arr A B)) (ht : Typed (A :: Γ) t B)
    S (η : CtxDen den Γ S),
    cast (den_arr A B S) (μ h S η) = fun x => μ ht S (CtxDen.cons x η)
  /-- (10) β-reduction is sound. -/
  μ_beta : ∀ {Γ t u A B} (h : Typed Γ (.app (.lam A t) u) B) (h' : Typed Γ (t.substOne u) B)
    S (η : CtxDen den Γ S), μ h S η = μ h' S η
  /-- (11) Type application depends only on the meaning of the polymorphic term. -/
  μ_tapp : ∀ {Γ t₁ t₂ A C} (h₁ : Typed Γ t₁ (.all A)) (h₂ : Typed Γ t₂ (.all A)),
    (∀ S η, μ h₁ S η = μ h₂ S η) →
    ∀ (k₁ : Typed Γ (.tapp t₁ C) (A.substOne C)) (k₂ : Typed Γ (.tapp t₂ C) (A.substOne C))
      S η, μ k₁ S η = μ k₂ S η
  /-- (12) Type β-reduction `(Λτ.e)[τ] = e` for `τ` not free in the context. -/
  -- The freshness premise is `τ ∉ FTV(π v)` in assumption (12), p. 4.
  μ_tbeta : ∀ {Γ e A A'} (_hΓ : ∀ B ∈ Γ, ¬ B.FreeIn 0) (h : Typed Γ e A)
    (h' : Typed Γ (.tapp (.tlam (e.tyRename rebind)) (.var 0)) A') S (η : CtxDen den Γ S),
    HEq (μ h' S η) (μ h S η)

/-! ### The terms of Lemma 2 (p. 5) -/

/-- `T τ = (τ → bool) → bool` as a System F type. -/
abbrev TTy (X : Ty) : Ty := .arr (.arr X boolTy) boolTy

/-- `G = τ → bool`, with `τ` the type variable `0`. -/
abbrev GTy : Ty := .arr (.var 0) boolTy

/-- `F = T τ → τ`, with `τ` the type variable `0`. -/
abbrev FTy : Ty := .arr (TTy (.var 0)) (.var 0)

/-- `ρ = ∀τ. (T τ → τ) → τ`; Reynolds' `P` is `S#ρ`. -/
abbrev ρTy : Ty := .all (.arr FTy (.var 0))

/-- `g (p[τ] f)` under `λf. λg. λp.` (term variables `p = 0`, `g = 1`, `f = 2`). -/
abbrev b3Tm : Tm := .app (.var 1) (.app (.tapp (.var 0) (.var 0)) (.var 2))

/-- `h (λp:ρ. g (p[τ] f))` (`g = 0`, `f = 1`, `h = 2`). -/
abbrev b2Tm : Tm := .app (.var 2) (.lam ρTy b3Tm)

/-- `f (λg:G. h (λp:ρ. g (p[τ] f)))` (`f = 0`, `h = 1`). -/
abbrev b1Tm : Tm := .app (.var 0) (.lam GTy b2Tm)

/-- `λf:F. f (λg. h (λp. g (p[τ] f)))`, with `h` the term variable `0`. -/
abbrev eTm : Tm := .lam FTy b1Tm

/-- `H = λh:T ρ. Λτ. λf:F. f (λg. h (λp. g (p[τ] f)))` (p. 5). -/
abbrev HTm : Tm := .lam (TTy ρTy) (.tlam eTm)

theorem typed_tapp0 (Γ : Ctx) :
    Typed (ρTy :: Γ) (.tapp (.var 0) (.var 0)) (.arr FTy (.var 0)) :=
  (Typed.tapp (A := .arr FTy (.var 0)) (B := .var 0) (.var rfl) : _)

theorem typed_b3 (Γ : Ctx) : Typed (ρTy :: GTy :: FTy :: Γ) b3Tm boolTy :=
  .app (A := .var 0) (.var rfl) (.app (A := FTy) (typed_tapp0 _) (.var rfl))

theorem typed_b2 (Γ : Ctx) : Typed (GTy :: FTy :: TTy ρTy :: Γ) b2Tm boolTy :=
  .app (A := .arr ρTy boolTy) (.var rfl) (.lam (typed_b3 _))

theorem typed_b1 (Γ : Ctx) : Typed (FTy :: TTy ρTy :: Γ) b1Tm (.var 0) :=
  .app (A := .arr GTy boolTy) (.var rfl) (.lam (typed_b2 _))

theorem typed_eTm (Γ : Ctx) : Typed (TTy ρTy :: Γ) eTm (.arr FTy (.var 0)) :=
  .lam (typed_b1 _)

theorem typed_tlam_eTm (Γ : Ctx) : Typed (TTy ρTy :: Γ) (.tlam eTm) ρTy :=
  .tlam (typed_eTm (Γ.map (Ty.rename Nat.succ)))

theorem typed_HTm (Γ : Ctx) : Typed Γ HTm (.arr (TTy ρTy) ρTy) :=
  .lam (typed_tlam_eTm _)

theorem typed_M (Γ : Ctx) : Typed (TTy ρTy :: Γ) (.app HTm (.var 0)) ρTy :=
  .app (typed_HTm _) (.var rfl)

/-- Application of heterogeneously equal functions to heterogeneously equal
arguments. -/
theorem heq_app {α α' β β' : Type u} (hα : α = α') (hβ : β = β') {F : α → β} {F' : α' → β'}
    (hF : HEq F F') {a : α} {a' : α'} (ha : HEq a a') : HEq (F a) (F' a') := by
  subst hα; subst hβ; cases hF; cases ha; rfl

namespace SetModel

/-- Lemma 1 (p. 4): the closed type `Λs. s → s → s` denotes a set with at least
two elements, for every set assignment. -/
theorem lemma1 (m : SetModel.{u}) :
    ∀ S, Nontrivial (m.den boolTy S) := by
  intro S0
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hcl : ∀ n, ¬ boolTy.FreeIn n := by intro n; simp [boolTy, Ty.FreeIn]
  have hsub : ∀ S, Subsingleton (m.den boolTy S) := fun S => by
    rw [m.den_congr boolTy S S0 (fun n h => absurd h (hcl n))]; exact hnt
  have v1 : Typed [.var 0, .var 0] (.var 1) (.var 0) := .var rfl
  have v0 : Typed [.var 0, .var 0] (.var 0) (.var 0) := .var rfl
  have i1 : Typed [.var 0] (.lam (.var 0) (.var 1)) (.arr (.var 0) (.var 0)) := .lam v1
  have i0 : Typed [.var 0] (.lam (.var 0) (.var 0)) (.arr (.var 0) (.var 0)) := .lam v0
  have e1 : Typed [] (.lam (.var 0) (.lam (.var 0) (.var 1)))
      (.arr (.var 0) (.arr (.var 0) (.var 0))) := .lam i1
  have e0 : Typed [] (.lam (.var 0) (.lam (.var 0) (.var 0)))
      (.arr (.var 0) (.arr (.var 0) (.var 0))) := .lam i0
  have t1 : Typed [] (.tlam (.lam (.var 0) (.lam (.var 0) (.var 1)))) boolTy := .tlam e1
  have t0 : Typed [] (.tlam (.lam (.var 0) (.lam (.var 0) (.var 0)))) boolTy := .tlam e0
  have k1 : Typed [] (.tapp (.tlam ((Tm.lam (.var 0) (.lam (.var 0) (.var 1))).tyRename rebind))
      (.var 0)) ((Ty.arr (.var 0) (.arr (.var 0) (.var 0))).substOne (.var 0)) := .tapp t1
  have k0 : Typed [] (.tapp (.tlam ((Tm.lam (.var 0) (.lam (.var 0) (.var 0))).tyRename rebind))
      (.var 0)) ((Ty.arr (.var 0) (.arr (.var 0) (.var 0))).substOne (.var 0)) := .tapp t0
  let S : ℕ → Type u := fun _ => ULift Bool
  let η : CtxDen m.den [] S := fun n A h => absurd h (by simp)
  have hk : m.μ k1 S η = m.μ k0 S η :=
    m.μ_tapp t1 t0 (fun S η => (hsub S).elim _ _) k1 k0 S η
  have hb1 := m.μ_tbeta (by simp) e1 k1 S η
  have hb0 := m.μ_tbeta (by simp) e0 k0 S η
  have he : m.μ e1 S η = m.μ e0 S η := eq_of_heq (hb1.symm.trans ((heq_of_eq hk).trans hb0))
  let x : m.den (.var 0) S := cast (m.den_var 0 S).symm (ULift.up true)
  let y : m.den (.var 0) S := cast (m.den_var 0 S).symm (ULift.up false)
  have c1 : cast (m.den_arr _ _ S) (cast (m.den_arr _ _ S) (m.μ e1 S η) x) y = x := by
    rw [m.μ_lam e1 i1 S η]
    dsimp only
    rw [m.μ_lam i1 v1 S _]
    dsimp only
    rw [m.μ_var v1 S _ rfl]
    rfl
  have c0 : cast (m.den_arr _ _ S) (cast (m.den_arr _ _ S) (m.μ e0 S η) x) y = y := by
    rw [m.μ_lam e0 i0 S η]
    dsimp only
    rw [m.μ_lam i0 v0 S _]
    dsimp only
    rw [m.μ_var v0 S _ rfl]
    rfl
  rw [he, c0] at c1
  have := congrArg (cast (m.den_var 0 S)) c1
  simp [x, y] at this
  exact Bool.false_ne_true (congrArg ULift.down this)

/-- Lemma 2 (pp. 5–6): a weakly initial `T`-algebra. -/
theorem lemma2 (m : SetModel.{u}) :
    ∃ (B : Type u) (_ : Nontrivial B) (P : Type u) (H : T B P → P),
      ∀ (s : Type u) (f : T B s → s), ∃ p : P → s, ∀ h, p (H h) = f (Tmap p h) := by
  have cB : ∀ n, ¬ boolTy.FreeIn n := by intro n; simp [boolTy, Ty.FreeIn]
  have cρ : ∀ n, ¬ ρTy.FreeIn n := by intro n; simp [boolTy, Ty.FreeIn]
  let Sb : ℕ → Type u := fun _ => PUnit
  have hB : ∀ S, m.den boolTy S = m.den boolTy Sb := fun S =>
    m.den_congr _ _ _ (fun n h => absurd h (cB n))
  have hP : ∀ S, m.den ρTy S = m.den ρTy Sb := fun S =>
    m.den_congr _ _ _ (fun n h => absurd h (cρ n))
  have hTT : ∀ S, m.den (TTy ρTy) S = T (m.den boolTy Sb) (m.den ρTy Sb) := fun S => by
    rw [m.den_arr, m.den_arr, hP S, hB S]
  let ε : ∀ S, CtxDen m.den [] S := fun _ _ _ h => absurd h (by simp)
  have hH0 := typed_HTm []
  let H : T (m.den boolTy Sb) (m.den ρTy Sb) → m.den ρTy Sb := fun h =>
    cast (m.den_arr _ _ Sb) (m.μ hH0 Sb (ε Sb)) (cast (hTT Sb).symm h)
  -- `H` is a closed term: its meaning does not depend on the set assignment ((4)).
  have hHS : ∀ S, HEq (m.μ hH0 S (ε S)) (m.μ hH0 Sb (ε Sb)) := fun S =>
    m.μ_congr hH0 S Sb _ _ (fun n hn => absurd hn (by
      simp [boolTy, Tm.TyFreeIn, Ty.FreeIn]))
      (fun _ _ h => absurd h (by simp))
  refine ⟨m.den boolTy Sb, m.lemma1 Sb, m.den ρTy Sb, H, fun s f => ?_⟩
  let S : ℕ → Type u := fun _ => s
  have hv : m.den (.var 0) S = s := m.den_var 0 S
  have hF : m.den FTy S = (T (m.den boolTy Sb) s → s) := by
    rw [m.den_arr, m.den_arr, m.den_arr, hv, hB S]
  let f' : m.den FTy S := cast hF.symm f
  have hq := typed_tapp0 []
  -- `p x = x[τ] f` with `S τ = s` (p. 5).
  let pS : m.den ρTy S → s := fun x =>
    cast hv (cast (m.den_arr _ _ S) (m.μ hq S (CtxDen.cons x (ε S))) f')
  let p : m.den ρTy Sb → s := fun x => pS (cast (hP S).symm x)
  refine ⟨p, fun h => ?_⟩
  let h' : m.den (TTy ρTy) S := cast (hTT S).symm h
  let η₁ : CtxDen m.den [TTy ρTy] S := CtxDen.cons h' (ε S)
  have hM := typed_M []
  have hH1 := typed_HTm [TTy ρTy]
  have hu : Typed [TTy ρTy] (.var 0) (TTy ρTy) := .var rfl
  -- Claim 1: `H h`, moved to `S`, is the meaning of the term `H h`.
  have c1 : cast (hP S).symm (H h) = m.μ hM S η₁ := by
    have ex : m.μ hH1 S η₁ = m.μ hH0 S (ε S) :=
      (m.μ_extend (Γ := []) hH0 hH1 S (ε S) η₁ (fun _ _ hn _ => absurd hn (by simp))).symm
    rw [m.μ_app hM hH1 hu S η₁, m.μ_var hu S η₁ rfl, ex]
    apply eq_of_heq
    show HEq (cast (hP S).symm (cast (m.den_arr _ _ Sb) (m.μ hH0 Sb (ε Sb)) (cast (hTT Sb).symm h))) _
    refine (cast_heq _ _).trans (heq_app (F := cast (m.den_arr _ _ Sb) (m.μ hH0 Sb (ε Sb)))
      (a := cast (hTT Sb).symm h) ((hTT Sb).trans (hTT S).symm) (hP S).symm
      ((cast_heq _ _).trans ((hHS S).symm.trans (cast_heq _ _).symm)) ?_)
    show HEq (cast (hTT Sb).symm h) (cast rfl (cast (hTT S).symm h))
    exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)).symm
  -- Claim 2: `(λp. p[τ]) (H h)` reduces to `(H h)[τ]` ((5), (8)–(10)).
  have hq' : Typed [ρTy, TTy ρTy] (.tapp (.var 0) (.var 0)) (.arr FTy (.var 0)) := typed_tapp0 _
  have hlam : Typed [TTy ρTy] (.lam ρTy (.tapp (.var 0) (.var 0)))
      (.arr ρTy (.arr FTy (.var 0))) := .lam hq'
  have hN : Typed [TTy ρTy] (.app (.lam ρTy (.tapp (.var 0) (.var 0))) (.app HTm (.var 0)))
      (.arr FTy (.var 0)) := .app hlam hM
  have hR : Typed [TTy ρTy] ((Tm.tapp (.var 0) (.var 0)).substOne (.app HTm (.var 0)))
      (.arr FTy (.var 0)) := (Typed.tapp (A := .arr FTy (.var 0)) (B := .var 0) hM : _)
  have c2 : m.μ hq S (CtxDen.cons (m.μ hM S η₁) (ε S)) = m.μ hR S η₁ := by
    rw [← m.μ_beta hN hR S η₁, m.μ_app hN hlam hM S η₁, m.μ_lam hlam hq' S η₁]
    exact m.μ_extend (Γ := [ρTy]) (Δ := [TTy ρTy]) hq hq' S _ _ (fun n _ hn _ => by
      cases n with
      | zero => rfl
      | succ n => simp at hn)
  -- Claim 3: `(H h)[τ] = e` by (10), (11), (12).
  have he := typed_eTm []
  have htl := typed_tlam_eTm []
  have hTB : Typed [TTy ρTy] (.tapp (.tlam (eTm.tyRename rebind)) (.var 0))
      ((Ty.arr FTy (.var 0)).substOne (.var 0)) := (Typed.tapp (A := .arr FTy (.var 0)) htl : _)
  have hMt : ∀ S η, m.μ hM S η = m.μ htl S η := fun S η => m.μ_beta hM htl S η
  have c3 : m.μ hR S η₁ = m.μ he S η₁ := by
    have k1 := m.μ_tapp hM htl hMt hR hTB S η₁
    have k2 := m.μ_tbeta (by simp [ρTy, FTy, TTy, boolTy, Ty.FreeIn]) he hTB S η₁
    exact eq_of_heq ((heq_of_eq k1).trans k2)
  -- Claim 4: unfold `e f`.
  have hb1 := typed_b1 []
  have hfv : Typed [FTy, TTy ρTy] (.var 0) (.arr (.arr GTy boolTy) (.var 0)) := .var rfl
  have hlG : Typed [FTy, TTy ρTy] (.lam GTy b2Tm) (.arr GTy boolTy) := .lam (typed_b2 [])
  have c4 : p (H h) = cast hv (cast (m.den_arr _ _ S) f' (m.μ hlG S (CtxDen.cons f' η₁))) := by
    show pS (cast (hP S).symm (H h)) = _
    rw [c1]
    show cast hv (cast (m.den_arr _ _ S) (m.μ hq S (CtxDen.cons (m.μ hM S η₁) (ε S))) f') = _
    rw [c2, c3, congrFun (m.μ_lam he hb1 S η₁) f', m.μ_app hb1 hfv hlG S _,
      m.μ_var hfv S _ rfl]
    rfl
  rw [c4]
  apply eq_of_heq
  have hGB : m.den (.arr GTy boolTy) S = T (m.den boolTy Sb) s := by
    rw [m.den_arr, m.den_arr, hv, hB S]
  refine (cast_heq _ _).trans (heq_app hGB hv ((cast_heq _ _).trans (cast_heq _ _)) ?_)
  -- `λg. h (λp. g (p[τ] f))` is `Tmap p h`.
  refine (cast_heq (m.den_arr _ _ S) _).symm.trans ?_
  rw [m.μ_lam hlG (typed_b2 []) S _]
  have hG : m.den GTy S = (s → m.den boolTy Sb) := by rw [m.den_arr, hv, hB S]
  apply Function.hfunext hG
  intro g g0 hgg
  show HEq (m.μ (typed_b2 []) S (CtxDen.cons g (CtxDen.cons f' η₁))) (h (g0 ∘ p))
  have hhv : Typed [GTy, FTy, TTy ρTy] (.var 2) (.arr (.arr ρTy boolTy) boolTy) := .var rfl
  have hlρ : Typed [GTy, FTy, TTy ρTy] (.lam ρTy b3Tm) (.arr ρTy boolTy) := .lam (typed_b3 _)
  rw [m.μ_app (typed_b2 []) hhv hlρ S _, m.μ_var hhv S _ rfl]
  have hρB : m.den (.arr ρTy boolTy) S = (m.den ρTy Sb → m.den boolTy Sb) := by
    rw [m.den_arr, hP S, hB S]
  refine heq_app hρB (hB S) ((cast_heq _ _).trans ?_) ?_
  · show HEq (cast rfl h') h
    exact (cast_heq _ _).trans (cast_heq _ _)
  refine (cast_heq (m.den_arr _ _ S) _).symm.trans ?_
  rw [m.μ_lam hlρ (typed_b3 _) S _]
  apply Function.hfunext (hP S)
  intro x x0 hxx
  show HEq (m.μ (typed_b3 [TTy ρTy]) S (CtxDen.cons x (CtxDen.cons g (CtxDen.cons f' η₁))))
    (g0 (p x0))
  have hg : Typed [ρTy, GTy, FTy, TTy ρTy] (.var 1) (.arr (.var 0) boolTy) := .var rfl
  have hb3a : Typed [ρTy, GTy, FTy, TTy ρTy] (.tapp (.var 0) (.var 0)) (.arr FTy (.var 0)) :=
    typed_tapp0 _
  have hv2f : Typed [ρTy, GTy, FTy, TTy ρTy] (.var 2) FTy := .var rfl
  have happ : Typed [ρTy, GTy, FTy, TTy ρTy] (.app (.tapp (.var 0) (.var 0)) (.var 2)) (.var 0) :=
    .app hb3a hv2f
  rw [m.μ_app (typed_b3 _) hg happ S _, m.μ_var hg S _ rfl]
  refine heq_app hv (hB S) ((cast_heq _ _).trans ?_) ?_
  · show HEq (cast rfl g) g0
    exact (cast_heq _ _).trans hgg
  rw [m.μ_app happ hb3a hv2f S _, m.μ_var hv2f S _ rfl]
  have hx : x = cast (hP S).symm x0 := eq_of_heq (hxx.trans (cast_heq _ _).symm)
  subst hx
  have ex2 : m.μ hb3a S (CtxDen.cons (cast (hP S).symm x0) (CtxDen.cons g (CtxDen.cons f' η₁))) =
      m.μ hq S (CtxDen.cons (cast (hP S).symm x0) (ε S)) :=
    (m.μ_extend (Γ := [ρTy]) (Δ := [GTy, FTy, TTy ρTy]) hq hb3a S _ _ (fun n _ hn _ => by
      cases n with
      | zero => rfl
      | succ n => simp at hn)).symm
  rw [ex2]
  exact (cast_heq hv _).symm

end SetModel

/-! ### Algebras of `T` -/

theorem Tmap_id {B s : Type u} (h : T B s) : Tmap id h = h := rfl

theorem Tmap_comp {B s s' s'' : Type u} (p : s → s') (q : s' → s'') (h : T B s) :
    Tmap q (Tmap p h) = Tmap (q ∘ p) h := rfl

/-- The equalizer of all endomorphisms of a weakly initial `T`-algebra is an
initial `T`-algebra (Freyd's construction; `T` needs no preservation property
because the equalizer of algebra maps is a subalgebra for any `Tmap`). -/
theorem initial_of_weak (B P : Type u) (H : T B P → P)
    (weak : ∀ (s : Type u) (f : T B s → s), ∃ p : P → s, ∀ h, p (H h) = f (Tmap p h)) :
    ∃ (E : Type u) (HE : T B E → E),
      ∀ (s : Type u) (f : T B s → s), ∃! p : E → s, ∀ h, p (HE h) = f (Tmap p h) := by
  let E := {x : P // ∀ e : P → P, (∀ h, e (H h) = H (Tmap e h)) → e x = x}
  let HE : T B E → E := fun h => ⟨H (Tmap Subtype.val h), fun e he => by
    rw [he, Tmap_comp]
    have : e ∘ Subtype.val = (Subtype.val : E → P) := funext fun y => y.2 e he
    rw [this]⟩
  refine ⟨E, HE, fun s f => ?_⟩
  obtain ⟨p, hp⟩ := weak s f
  have hpE : ∀ h, (p ∘ Subtype.val) (HE h) = f (Tmap (p ∘ Subtype.val) h) := fun h => by
    show p (H (Tmap Subtype.val h)) = _
    rw [hp]; rfl
  -- uniqueness: equalize two algebra maps
  have uniq : ∀ u w : E → s, (∀ h, u (HE h) = f (Tmap u h)) →
      (∀ h, w (HE h) = f (Tmap w h)) → u = w := by
    intro u w hu hw
    let E' := {x : E // u x = w x}
    let HE' : T B E' → E' := fun h => ⟨HE (Tmap Subtype.val h), by
      rw [hu, hw, Tmap_comp, Tmap_comp]
      have : u ∘ Subtype.val = w ∘ (Subtype.val : E' → E) := funext fun y => y.2
      rw [this]⟩
    obtain ⟨q, hq⟩ := weak E' HE'
    let e : P → P := fun x => (q x).1.1
    have he : ∀ h, e (H h) = H (Tmap e h) := fun h => by
      show (q (H h)).1.1 = _
      rw [hq]; rfl
    funext x
    have hx : (q x.1).1 = x := Subtype.ext (x.2 e he)
    rw [← hx]; exact (q x.1).2
  exact ⟨p ∘ Subtype.val, hpE, fun v hv => uniq v _ hv hpE⟩

/-- Lemma 3 (pp. 7–8): restricting to parametric elements makes the mediating
map `p'` canonical: any other algebra map `ψ` satisfies `p' = p'_{P',H'} ; ψ`. -/
theorem lemma3 (B P : Type u) (H : T B P → P)
    (weak : ∀ (s : Type u) (f : T B s → s), ∃ p : P → s, ∀ h, p (H h) = f (Tmap p h)) :
    ∃ (P' : Type u) (H' : T B P' → P') (p' : ∀ (s : Type u), (T B s → s) → P' → s),
      ∀ (s : Type u) (f : T B s → s),
        (∀ h, p' s f (H' h) = f (Tmap (p' s f) h)) ∧
        ∀ ψ : P' → s, (∀ h, ψ (H' h) = f (Tmap ψ h)) → p' s f = ψ ∘ p' P' H' := by
  obtain ⟨E, HE, init⟩ := initial_of_weak B P H weak
  let p' : ∀ (s : Type u), (T B s → s) → E → s := fun s f => (init s f).exists.choose
  have spec : ∀ s f h, p' s f (HE h) = f (Tmap (p' s f) h) := fun s f =>
    (init s f).exists.choose_spec
  have hid : p' E HE = id := (init E HE).unique (spec E HE) (fun _ => rfl)
  refine ⟨E, HE, p', fun s f => ⟨spec s f, fun ψ hψ => ?_⟩⟩
  rw [hid]
  exact (init s f).unique (spec s f) hψ

/-- Lemma 4 (pp. 9–10): an initial `T`-algebra. -/
theorem lemma4 (B P' : Type u) (H' : T B P' → P') (p' : ∀ (s : Type u), (T B s → s) → P' → s)
    (h : ∀ (s : Type u) (f : T B s → s),
        (∀ h, p' s f (H' h) = f (Tmap (p' s f) h)) ∧
        ∀ ψ : P' → s, (∀ h, ψ (H' h) = f (Tmap ψ h)) → p' s f = ψ ∘ p' P' H') :
    ∃ (P'' : Type u) (H'' : T B P'' → P''),
      ∀ (s : Type u) (f : T B s → s), ∃! p : P'' → s, ∀ h, p (H'' h) = f (Tmap p h) := by
  let e := p' P' H'
  have he : ∀ k, e (H' k) = H' (Tmap e k) := (h P' H').1
  have idem : ∀ x, e (e x) = e x := fun x => (congrFun ((h P' H').2 e he) x).symm
  let P'' := {x : P' // e x = x}
  let ι : P'' → P' := Subtype.val
  let H'' : T B P'' → P'' := fun k => ⟨H' (Tmap ι k), by
    rw [he, Tmap_comp]
    have : e ∘ ι = ι := funext fun y => y.2
    rw [this]⟩
  let r : P' → P'' := fun x => ⟨e x, idem x⟩
  refine ⟨P'', H'', fun s f => ⟨p' s f ∘ ι, fun k => ?_, fun ψ hψ => ?_⟩⟩
  · show p' s f (H' (Tmap ι k)) = _
    rw [(h s f).1]; rfl
  · have hr : ∀ k, (ψ ∘ r) (H' k) = f (Tmap (ψ ∘ r) k) := fun k => by
      have : r (H' k) = H'' (Tmap r k) := Subtype.ext (by
        show e (H' k) = H' (Tmap ι (Tmap r k))
        rw [he]; rfl)
      show ψ (r (H' k)) = _
      rw [this, hψ]; rfl
    have key := (h s f).2 (ψ ∘ r) hr
    funext x
    show ψ x = p' s f x.1
    rw [key]
    show ψ x = ψ (r (e x.1))
    congr 1
    exact Subtype.ext (by show x.1 = e (e x.1); rw [x.2, x.2])

/-- Lambek's lemma (p. 11, after [5, 6]): the structure map of an initial
`T`-algebra is a bijection. This is the set-level content of Mathlib's
`CategoryTheory.Endofunctor.Algebra.Initial.str_isIso`; it is proved directly here
because `init` is stated as unique existence of a mediating function rather than as
`Limits.IsInitial` in `Endofunctor.Algebra`, and the direct argument is shorter than
packaging `T B` as a functor and converting. -/
theorem initial_bijective (B P : Type u) (H : T B P → P)
    (init : ∀ (s : Type u) (f : T B s → s), ∃! p : P → s, ∀ h, p (H h) = f (Tmap p h)) :
    Function.Bijective H := by
  obtain ⟨k, hk⟩ := (init (T B P) (Tmap H)).exists
  have hHk : H ∘ k = id :=
    (init P H).unique (y₁ := H ∘ k) (fun h => by
      show H (k (H h)) = _
      rw [hk]; rfl) (fun _ => rfl)
  have hkH : ∀ h, k (H h) = h := fun h => by
    rw [hk, Tmap_comp, hHk]; rfl
  exact ⟨Function.LeftInverse.injective hkH,
    Function.RightInverse.surjective (fun x => congrFun hHk x)⟩

/-- Cantor: `(P → B) → B` is strictly larger than `P` when `B` has two elements.
Reduced to Mathlib's `Function.cantor_injective` via the injection
`Set P ↪ T B P` given by indicator functions. -/
theorem not_bijective (B P : Type u) [Nontrivial B] (H : T B P → P) :
    ¬ Function.Bijective H := by
  classical
  intro hb
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne B
  let χ : (P → B) → T B P := fun g φ => if φ = g then b1 else b0
  let c : Set P → (P → B) := fun q x => if x ∈ q then b1 else b0
  apply Function.cantor_injective (fun q => H (χ (c q)))
  intro q q' hqq
  have h1 : χ (c q) = χ (c q') := hb.injective hqq
  have h2 : c q = c q' := by
    by_contra hc
    have := congrFun h1 (c q)
    simp only [χ, ite_true, hc, ite_false] at this
    exact hne this.symm
  ext x
  have := congrFun h2 x
  by_cases hx : x ∈ q <;> by_cases hx' : x ∈ q' <;> simp only [c, hx, hx', ite_true, ite_false] at this
  · exact iff_of_true hx hx'
  · exact absurd this.symm hne
  · exact absurd this hne
  · exact iff_of_false hx hx'

/-- Reynolds' theorem (p. 11): the twelve full-function-space semantic laws
of `SetModel` cannot hold together in one fixed universe. -/
theorem SetModel.false (m : SetModel.{u}) : False := by
  obtain ⟨B, hB, P, H, weak⟩ := m.lemma2
  obtain ⟨P', H', p', h⟩ := lemma3 B P H weak
  obtain ⟨P'', H'', init⟩ := lemma4 B P' H' p' h
  exact not_bijective B P'' H'' (initial_bijective B P'' H'' init)

theorem isEmpty_setModel : IsEmpty SetModel.{u} := ⟨SetModel.false⟩

/-! ## Universes closed under products over themselves -/

/-- A universe of sets closed under full function spaces and under products
indexed by the whole universe: the "∀ as product" reading of a set model. -/
structure UniverseModel where
  U : Type u
  El : U → Type u
  arr : U → U → U
  el_arr : ∀ a b, El (arr a b) ≃ (El a → El b)
  pi : (U → U) → U
  el_pi : ∀ F, El (pi F) ≃ ∀ a, El (F a)

namespace UniverseModel

/-- Every member of such a universe has at most one element. -/
theorem subsingleton (m : UniverseModel.{u}) (a : m.U) : Subsingleton (m.El a) := by
  classical
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨x0, x1, hne⟩ := exists_pair_ne (m.El a)
  let F : m.U → m.U := fun y => m.arr y a
  let Q := m.pi F
  let φ : m.El Q → m.El Q → m.El a := fun q e => m.el_arr Q a (m.el_pi F q Q) e
  let g : m.El Q → m.El a := fun e => if φ e e = x0 then x1 else x0
  let q : m.El Q := (m.el_pi F).symm (fun y => (m.el_arr y a).symm
    (fun e => if h : y = Q then g (cast (congrArg m.El h) e) else x0))
  have hq : φ q q = g q := by simp [φ, q]
  by_cases h0 : φ q q = x0
  · have : g q = x1 := by simp [g, h0]
    rw [hq, this] at h0; exact hne h0.symm
  · have : g q = x0 := by simp [g, h0]
    rw [hq, this] at h0; exact h0 rfl

/-- An element of `{∅, 1}` from the code being `true`. -/
def elOf : ∀ {b : Bool}, b = true → (if b then PUnit.{1} else PEmpty.{1})
  | true, _ => PUnit.unit
  | false, h => nomatch h

theorem elTo : ∀ {b : Bool}, (if b then PUnit.{1} else PEmpty.{1}) → b = true
  | true, _ => rfl
  | false, x => PEmpty.elim x

instance elSubsingleton (b : Bool) : Subsingleton (if b then PUnit.{1} else PEmpty.{1}) := by
  cases b
  · exact (inferInstance : Subsingleton PEmpty.{1})
  · exact (inferInstance : Subsingleton PUnit.{1})

/-- The universe `{∅, 1}` (codes `false`, `true`), showing that the
subsingleton conclusion cannot be strengthened to emptiness. -/
def boolUniverse : UniverseModel.{0} where
  U := Bool
  El b := if b then PUnit.{1} else PEmpty.{1}
  arr a b := !a || b
  el_arr a b := equivOfSubsingletonOfSubsingleton
    (fun x y => elOf (by have := elTo x; have := elTo y; cases a <;> cases b <;> simp_all))
    (fun g => elOf (by
      cases a
      · rfl
      · simpa using elTo (g (elOf rfl))))
  pi F := F false && F true
  el_pi F := equivOfSubsingletonOfSubsingleton
    (fun x c => elOf (by have := elTo x; cases c <;> simp_all))
    (fun k => elOf (by simp [elTo (k false), elTo (k true)]))

theorem boolUniverse_true_nonempty : Nonempty (boolUniverse.El true) := by
  unfold boolUniverse
  exact ⟨PUnit.unit⟩

end UniverseModel

end Silmaril.Calculi.LambdaCube.PERModel.Reynolds
