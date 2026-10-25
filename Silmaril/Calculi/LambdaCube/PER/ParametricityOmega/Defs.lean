module

public import Silmaril.Calculi.LambdaCube.PER.Parametricity
public import Silmaril.Calculi.LambdaCube.PER.SystemFOmega

@[expose] public section

set_option autoImplicit true

/-! # Relational parametricity for Fω

Atkey [atkey-2012-relational-parametricity-higher-kinds] (CSL 2012, §3,
Theorem 1 on PDF p. 7 and the abstraction theorem, Theorem 3, on PDF p. 8)
interprets kinds as reflexive graphs: `*` by types together with relations
between them, `κ₁ → κ₂` by relation-preserving maps. We use the simplified
*purely relational* version over the realizers of a combinatory algebra:

* `Kind.RSem`: `*` denotes relations on realizers `M.D → M.D → Prop`, and an
  arrow kind denotes all functions between the relational denotations (so a
  higher-kinded variable is a relation transformer, Atkey's relational action
  without the object part);
* `Con.rinterp` mirrors `Con.interp` (`PER/SystemFOmega.lean`): `→` is the
  logical relation, `∀ (α : κ)` intersects over all relational denotations of `κ`;
* `ConEq.rsound`: βη-equal constructors denote the same relation transformer;
* `Typed.abstraction`: the erasure of a typed Fω term is related to itself under
  related environments in this relation-transformer model.

Restricted to kind `*`, this is the purely relational Reynolds model of System F
(`SystemF.Ty.rinterp`, Reynolds 1983 (R1)–(R5)); `rinterp_ofF` relates the two,
and System F's relational abstraction theorem `SystemF.Typed.abstraction_rel` is
the kind-`*` instance. Free theorems: `free_id` and the higher-kinded
`free_hkId` (every inhabitant of `∀ F : * → *. ∀ X. F X → F X` realizes the
identity).

The PER-saturated relations of `PER/Parametricity.lean` are the System F
version that stays inside the PER model; their extension to Fω (a reflexive-graph model over PERs) is future work.
-/

namespace Silmaril.Calculi.LambdaCube.PERModel

namespace SystemFOmega

/-- Relational denotations of kinds: relations on realizers at `*`, functions
between relational denotations at arrows. -/
def Kind.RSem (D : Type u) : Kind → Type u
  | .star => D → D → Prop
  | .arr k l => Kind.RSem D k → Kind.RSem D l

/-- The canonical inhabitant: the empty relation, pointwise. -/
def Kind.rdefault {D : Type u} : (k : Kind) → k.RSem D
  | .star => fun _ _ => False
  | .arr _ l => fun _ => Kind.rdefault l

/-- A relational denotation of some kind. -/
abbrev REntry (D : Type u) := Σ k : Kind, k.RSem D

variable (M : CombAlg.{u})

/-- The relational interpretation of constructors at a requested kind,
mirroring `Con.interp`. -/
noncomputable def Con.rinterp : Con → (ℕ → REntry M.D) → (k : Kind) → k.RSem M.D
  | .var n, ξ, k =>
      if h : (ξ n).1 = k then cast (congrArg (Kind.RSem M.D) h) (ξ n).2 else Kind.rdefault k
  | .arr A B, ξ, .star => fun f g =>
      ∀ a b, Con.rinterp A ξ .star a b → Con.rinterp B ξ .star (M.app f a) (M.app g b)
  | .all k' A, ξ, .star => fun e e' =>
      ∀ X : k'.RSem M.D, Con.rinterp A (scons ⟨k', X⟩ ξ) .star e e'
  | .lam _ A, ξ, .arr k l => fun X => Con.rinterp A (scons ⟨k, X⟩ ξ) l
  | .app A B, ξ, l =>
      match B.infer (fun n => (ξ n).1) with
      | some k => Con.rinterp A ξ (.arr k l) (Con.rinterp B ξ k)
      | none => Kind.rdefault l
  | _, _, k => Kind.rdefault k

/-- A relational environment fits a kind context. -/
def RFits (Δ : KCtx) (ξ : ℕ → REntry M.D) : Prop :=
  ∀ n k, Δ[n]? = some k → (ξ n).1 = k

/-- Related realizer environments for a term context. -/
def RelCtx (Γ : Ctx) (ξ : ℕ → REntry M.D) (ρ₁ ρ₂ : ℕ → M.D) : Prop :=
  ∀ n (A : Con), Γ[n]? = some A → A.rinterp M ξ .star (ρ₁ n) (ρ₂ n)

variable {M}

theorem RFits.cons {Δ : KCtx} {ξ : ℕ → REntry M.D} (hξ : RFits M Δ ξ) {k : Kind}
    (X : k.RSem M.D) : RFits M (k :: Δ) (scons ⟨k, X⟩ ξ) := by
  intro n k' h
  cases n with
  | zero => simpa using h
  | succ n => exact hξ n k' (by simpa using h)

theorem Con.rinterp_var_eq (n : ℕ) (ξ : ℕ → REntry M.D) (k : Kind) :
    (Con.var n).rinterp M ξ k =
      if h : (ξ n).1 = k then cast (congrArg (Kind.RSem M.D) h) (ξ n).2 else Kind.rdefault k := by
  rfl

theorem rentry_cast_eq {D : Type u} (e : REntry D) {k : Kind} (h : e.1 = k) :
    e = ⟨k, cast (congrArg (Kind.RSem D) h) e.2⟩ := by
  obtain ⟨k0, x⟩ := e; subst h; rfl

theorem rentry_cast_of_eq {D : Type u} (e : REntry D) {k : Kind} {X : k.RSem D}
    (he : e = ⟨k, X⟩) :
    (if h : e.1 = k then cast (congrArg (Kind.RSem D) h) e.2 else Kind.rdefault k) = X := by
  subst he; simp

theorem rinterp_var_of_eq {ξ : ℕ → REntry M.D} {n : ℕ} {k : Kind} {X : k.RSem M.D}
    (he : ξ n = ⟨k, X⟩) : (Con.var n).rinterp M ξ k = X := by
  rw [Con.rinterp_var_eq]; exact rentry_cast_of_eq _ he

theorem rentry_eq_of_fst {ξ : ℕ → REntry M.D} {n : ℕ} {k : Kind} (h : (ξ n).1 = k) :
    ξ n = ⟨k, (Con.var n).rinterp M ξ k⟩ := by
  rw [Con.rinterp_var_eq]
  split
  · exact rentry_cast_eq _ h
  · exact absurd h ‹_›

theorem Con.rinterp_app_eq (A B : Con) (ξ : ℕ → REntry M.D) (l : Kind) :
    (Con.app A B).rinterp M ξ l =
      match B.infer (fun n => (ξ n).1) with
      | some k => A.rinterp M ξ (.arr k l) (B.rinterp M ξ k)
      | none => Kind.rdefault l := by
  rfl

theorem rinterp_app_of_infer {A B : Con} {ξ : ℕ → REntry M.D} {k l : Kind}
    (h : B.infer (fun n => (ξ n).1) = some k) :
    (Con.app A B).rinterp M ξ l = A.rinterp M ξ (.arr k l) (B.rinterp M ξ k) := by
  simp only [Con.rinterp_app_eq, h]

theorem rinterp_app_of_none {A B : Con} {ξ : ℕ → REntry M.D} {l : Kind}
    (h : B.infer (fun n => (ξ n).1) = none) :
    (Con.app A B).rinterp M ξ l = Kind.rdefault l := by
  simp only [Con.rinterp_app_eq, h]

theorem Con.rinterp_arr_star (A B : Con) (ξ : ℕ → REntry M.D) :
    (Con.arr A B).rinterp M ξ .star = fun f g =>
      ∀ a b, A.rinterp M ξ .star a b → B.rinterp M ξ .star (M.app f a) (M.app g b) := by
  rfl

theorem Con.rinterp_all_star (k' : Kind) (A : Con) (ξ : ℕ → REntry M.D) :
    (Con.all k' A).rinterp M ξ .star = fun e e' =>
      ∀ X : k'.RSem M.D, A.rinterp M (scons ⟨k', X⟩ ξ) .star e e' := by
  rfl

theorem Con.rinterp_lam_arr (k₀ : Kind) (A : Con) (ξ : ℕ → REntry M.D) (k l : Kind) :
    (Con.lam k₀ A).rinterp M ξ (.arr k l) = fun X => A.rinterp M (scons ⟨k, X⟩ ξ) l := by
  rfl

theorem Con.rinterp_arr_arr (A B : Con) (ξ : ℕ → REntry M.D) (k l : Kind) :
    (Con.arr A B).rinterp M ξ (.arr k l) = Kind.rdefault (.arr k l) := by
  rfl

theorem Con.rinterp_all_arr (k' : Kind) (A : Con) (ξ : ℕ → REntry M.D) (k l : Kind) :
    (Con.all k' A).rinterp M ξ (.arr k l) = Kind.rdefault (.arr k l) := by
  rfl

theorem Con.rinterp_lam_star (k₀ : Kind) (A : Con) (ξ : ℕ → REntry M.D) :
    (Con.lam k₀ A).rinterp M ξ .star = Kind.rdefault .star := by
  rfl

theorem Con.rinterp_rename (r : ℕ → ℕ) (A : Con) (ξ : ℕ → REntry M.D) (k : Kind) :
    (A.rename r).rinterp M ξ k = A.rinterp M (ξ ∘ r) k := by
  induction A generalizing r ξ k with
  | var n => simp only [Con.rename, Con.rinterp_var_eq, Function.comp_apply]
  | arr _ _ ihA ihB =>
    cases k with
    | star => simp only [Con.rename, Con.rinterp_arr_star, ihA, ihB]; rfl
    | arr _ _ => simp only [Con.rename, Con.rinterp_arr_arr]
  | all k' A ih =>
    cases k with
    | star => simp only [Con.rename, Con.rinterp_all_star, ih, scons_comp_lift]; rfl
    | arr _ _ => simp only [Con.rename, Con.rinterp_all_arr]
  | lam _ A ih =>
    cases k with
    | star => simp only [Con.rename, Con.rinterp_lam_star]
    | arr a b => simp only [Con.rename, Con.rinterp_lam_arr, ih, scons_comp_lift]; rfl
  | app A B ihA ihB =>
    simp only [Con.rename]
    have hi : (B.rename r).infer (fun n => (ξ n).1) = B.infer (fun n => ((ξ ∘ r) n).1) :=
      Con.infer_rename r B _
    cases hk : B.infer (fun n => ((ξ ∘ r) n).1) with
    | some k0 =>
      rw [rinterp_app_of_infer (hi.trans hk), rinterp_app_of_infer hk, ihA, ihB]
    | none =>
      rw [rinterp_app_of_none (hi.trans hk), rinterp_app_of_none hk]

/-- Relational substitutions lift under a binder. -/
theorem rinterp_subst_lift {Δ Δ' : KCtx} {σ : ℕ → Con} {ξ ξ' : ℕ → REntry M.D}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k' ∧ ξ' n = ⟨k', (σ n).rinterp M ξ k'⟩)
    (k0 : Kind) (X : k0.RSem M.D) :
    ∀ n k', (k0 :: Δ)[n]? = some k' → Kinded (k0 :: Δ') (Con.liftSub σ n) k' ∧
      scons ⟨k0, X⟩ ξ' n = ⟨k', (Con.liftSub σ n).rinterp M (scons ⟨k0, X⟩ ξ) k'⟩ := by
  intro n k' h
  cases n with
  | zero =>
    simp at h; subst h
    exact ⟨.var (by simp),
      congrArg (Sigma.mk _) (rinterp_var_of_eq (ξ := scons ⟨_, X⟩ ξ) (n := 0) rfl).symm⟩
  | succ n =>
    obtain ⟨hk, he⟩ := hσ n k' (by simpa using h)
    refine ⟨hk.rename (kren_succ k0), ?_⟩
    rw [show scons (⟨k0, X⟩ : REntry M.D) ξ' (n + 1) = ξ' n from rfl, he]
    exact congrArg (Sigma.mk k') (Con.rinterp_rename Nat.succ (σ n) (scons ⟨k0, X⟩ ξ) k').symm

/-- The relational substitution lemma for simultaneous substitutions. -/
theorem Con.rinterp_subst (h : Kinded Δ A k) {Δ' : KCtx} {σ : ℕ → Con}
    {ξ ξ' : ℕ → REntry M.D}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k' ∧ ξ' n = ⟨k', (σ n).rinterp M ξ k'⟩)
    (hξ : RFits M Δ' ξ) :
    (A.subst σ).rinterp M ξ k = A.rinterp M ξ' k := by
  induction h generalizing Δ' σ ξ ξ' with
  | var h => exact (rinterp_var_of_eq (hσ _ _ h).2).symm
  | arr _ _ ih1 ih2 =>
    simp only [Con.subst, Con.rinterp_arr_star, ih1 (hσ := hσ) (hξ := hξ),
      ih2 (hσ := hσ) (hξ := hξ)]; rfl
  | all _ ih =>
    simp only [Con.subst, Con.rinterp_all_star]
    funext e e'
    exact forall_congr fun X => by
      rw [ih (hσ := rinterp_subst_lift hσ _ X) (hξ := hξ.cons X)]
  | lam _ ih =>
    simp only [Con.subst, Con.rinterp_lam_arr]
    exact funext fun X => ih (hσ := rinterp_subst_lift hσ _ X) (hξ := hξ.cons X)
  | app _ hB ih1 ih2 =>
    simp only [Con.subst]
    rw [rinterp_app_of_infer ((hB.subst fun n k' hn => (hσ n k' hn).1).infer hξ),
      rinterp_app_of_infer (hB.infer (κ := fun n => (ξ' n).1) fun n k' hn => by
        rw [(hσ n k' hn).2]),
      ih1 (hσ := hσ) (hξ := hξ),
      ih2 (hσ := hσ) (hξ := hξ)]

/-- The relational substitution lemma for well-kinded constructors. -/
theorem Con.rinterp_substOne (hA : Kinded (k :: Δ) A l) (hB : Kinded Δ B k)
    {ξ : ℕ → REntry M.D} (hξ : RFits M Δ ξ) :
    (A.substOne B).rinterp M ξ l = A.rinterp M (scons ⟨k, B.rinterp M ξ k⟩ ξ) l := by
  refine Con.rinterp_subst hA (fun n k' h => ?_) hξ
  cases n with
  | zero =>
    simp at h; subst h
    exact ⟨hB, rfl⟩
  | succ n =>
    have h' : Δ[n]? = some k' := by simpa using h
    exact ⟨.var h', rentry_eq_of_fst (hξ n k' h')⟩

theorem rinterp_eta {A : Con} {k l : Kind} {ξ : ℕ → REntry M.D} (X : k.RSem M.D) :
    (Con.app (A.rename Nat.succ) (.var 0)).rinterp M (scons ⟨k, X⟩ ξ) l =
      A.rinterp M ξ (.arr k l) X := by
  rw [rinterp_app_of_infer (A := A.rename Nat.succ) (B := .var 0) (ξ := scons ⟨k, X⟩ ξ)
      (k := k) (l := l) rfl,
    Con.rinterp_rename, scons_comp_succ,
    rinterp_var_of_eq (ξ := scons ⟨k, X⟩ ξ) (n := 0) (k := k) (X := X) rfl]

/-- βη-equal constructors have the same relational denotation. -/
theorem ConEq.rsound (h : ConEq Δ A B k) {ξ : ℕ → REntry M.D} (hξ : RFits M Δ ξ) :
    A.rinterp M ξ k = B.rinterp M ξ k := by
  induction h generalizing ξ with
  | refl => rfl
  | symm _ ih => exact (ih (hξ := hξ)).symm
  | trans _ _ ih1 ih2 => exact (ih1 (hξ := hξ)).trans (ih2 (hξ := hξ))
  | beta hA hB =>
    exact (rinterp_app_of_infer (hB.infer hξ)).trans (Con.rinterp_substOne hA hB hξ).symm
  | eta _ =>
    rw [Con.rinterp_lam_arr]
    exact funext fun X => rinterp_eta X
  | arr _ _ ih1 ih2 =>
    simp only [Con.rinterp_arr_star, ih1 (hξ := hξ), ih2 (hξ := hξ)]; rfl
  | all _ ih =>
    simp only [Con.rinterp_all_star]
    funext e e'
    exact forall_congr fun X => by rw [ih (hξ := hξ.cons X)]
  | lam _ ih =>
    simp only [Con.rinterp_lam_arr]
    exact funext fun X => ih (hξ := hξ.cons X)
  | app _ hB ih1 ih2 =>
    rw [rinterp_app_of_infer (hB.kinded_left.infer hξ),
      rinterp_app_of_infer (hB.kinded_right.infer hξ), ih1 (hξ := hξ), ih2 (hξ := hξ)]

theorem RelCtx.cons {Γ : Ctx} {ξ : ℕ → REntry M.D} {ρ₁ ρ₂ : ℕ → M.D}
    (h : RelCtx M Γ ξ ρ₁ ρ₂) {A : Con} {a b : M.D} (ha : A.rinterp M ξ .star a b) :
    RelCtx M (A :: Γ) ξ (scons a ρ₁) (scons b ρ₂) := by
  intro n C hn
  cases n with
  | zero => simp at hn; subst hn; exact ha
  | succ n => exact h n C (by simpa using hn)

theorem RelCtx.shift {Γ : Ctx} {ξ : ℕ → REntry M.D} {ρ₁ ρ₂ : ℕ → M.D}
    (h : RelCtx M Γ ξ ρ₁ ρ₂) {k : Kind} (X : k.RSem M.D) :
    RelCtx M (Γ.map (Con.rename Nat.succ)) (scons ⟨k, X⟩ ξ) ρ₁ ρ₂ := by
  intro n C hn
  simp at hn
  obtain ⟨C0, hC0, rfl⟩ := hn
  rw [Con.rinterp_rename, scons_comp_succ]
  exact h n C0 hC0

/-- `∀ (X : *). X → X`. -/
def idTy : Con := .all .star (.arr (.var 0) (.var 0))

/-- `∀ (F : * → *). ∀ (X : *). F X → F X`. -/
def hkIdTy : Con :=
  .all (.arr .star .star) (.all .star (.arr (.app (.var 1) (.var 0)) (.app (.var 1) (.var 0))))


end SystemFOmega


/-! ## The kind-`*` fragment: Reynolds' relational model of System F -/

namespace SystemF

variable (M : CombAlg.{u})

/-- The purely relational interpretation of System F types (Reynolds 1983,
(R1)–(R4) on printed p. 515 and (R5) on printed p. 520, with relations on the
realizers of `M` in place of relations between sets). -/
def Ty.rinterp : Ty → (ℕ → M.D → M.D → Prop) → M.D → M.D → Prop
  | .var n, R => R n
  | .arr A B, R => fun f g =>
      ∀ a b, Ty.rinterp A R a b → Ty.rinterp B R (M.app f a) (M.app g b)
  | .all A, R => fun e e' => ∀ S : M.D → M.D → Prop, Ty.rinterp A (scons S R) e e'

variable {M}

/-- The Fω relational interpretation of an embedded System F type is its
System F relational interpretation. -/
theorem rinterp_ofF (A : Ty) (R : ℕ → M.D → M.D → Prop) :
    (SystemFOmega.ofF A).rinterp M (fun n => ⟨.star, R n⟩) .star = A.rinterp M R := by
  induction A generalizing R with
  | var n =>
    rw [SystemFOmega.ofF, Ty.rinterp]
    exact SystemFOmega.rinterp_var_of_eq rfl
  | arr _ _ ihA ihB =>
    rw [SystemFOmega.ofF, Ty.rinterp, SystemFOmega.Con.rinterp_arr_star, ihA, ihB]
  | all A ih =>
    rw [SystemFOmega.ofF, Ty.rinterp, SystemFOmega.Con.rinterp_all_star]
    funext e e'
    refine forall_congr fun (X : M.D → M.D → Prop) => ?_
    have e : scons (⟨.star, X⟩ : SystemFOmega.REntry M.D) (fun n => ⟨.star, R n⟩) =
        fun n => ⟨.star, scons X R n⟩ := by
      funext n; cases n <;> rfl
    rw [e]; exact congrFun (congrFun (ih (scons X R)) _) _

theorem Ty.exists_freeIn_bound (A : Ty) : ∃ n, ∀ m, A.FreeIn m → m < n := by
  induction A with
  | var k => exact ⟨k + 1, fun m hm => by simp only [Ty.FreeIn] at hm; omega⟩
  | arr _ _ ihA ihB =>
    obtain ⟨n₁, h₁⟩ := ihA
    obtain ⟨n₂, h₂⟩ := ihB
    refine ⟨max n₁ n₂, fun m hm => ?_⟩
    rcases hm with hm | hm
    · exact lt_max_of_lt_left (h₁ m hm)
    · exact lt_max_of_lt_right (h₂ m hm)
  | all _ ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n, fun m hm => by have := h (m + 1) hm; omega⟩

theorem Tm.exists_tyFreeIn_bound (t : Tm) : ∃ n, ∀ m, t.TyFreeIn m → m < n := by
  induction t with
  | var _ => exact ⟨0, fun _ hm => hm.elim⟩
  | app _ _ iht ihu =>
    obtain ⟨n₁, h₁⟩ := iht
    obtain ⟨n₂, h₂⟩ := ihu
    refine ⟨max n₁ n₂, fun m hm => ?_⟩
    rcases hm with hm | hm
    · exact lt_max_of_lt_left (h₁ m hm)
    · exact lt_max_of_lt_right (h₂ m hm)
  | lam A _ ih =>
    obtain ⟨n₁, h₁⟩ := A.exists_freeIn_bound
    obtain ⟨n₂, h₂⟩ := ih
    refine ⟨max n₁ n₂, fun m hm => ?_⟩
    rcases hm with hm | hm
    · exact lt_max_of_lt_left (h₁ m hm)
    · exact lt_max_of_lt_right (h₂ m hm)
  | tapp _ A ih =>
    obtain ⟨n₁, h₁⟩ := ih
    obtain ⟨n₂, h₂⟩ := A.exists_freeIn_bound
    refine ⟨max n₁ n₂, fun m hm => ?_⟩
    rcases hm with hm | hm
    · exact lt_max_of_lt_left (h₁ m hm)
    · exact lt_max_of_lt_right (h₂ m hm)
  | tlam _ ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n, fun m hm => by have := h (m + 1) hm; omega⟩

theorem ctx_exists_freeIn_bound (Γ : Ctx) : ∃ n, ∀ B ∈ Γ, ∀ m, Ty.FreeIn m B → m < n := by
  induction Γ with
  | nil => exact ⟨0, fun _ hB => by simp at hB⟩
  | cons A Γ ih =>
    obtain ⟨n₁, h₁⟩ := A.exists_freeIn_bound
    obtain ⟨n₂, h₂⟩ := ih
    refine ⟨max n₁ n₂, fun B hB m hm => ?_⟩
    rcases List.mem_cons.mp hB with rfl | hB
    · exact lt_max_of_lt_left (h₁ m hm)
    · exact lt_max_of_lt_right (h₂ B hB m hm)


end SystemF

end Silmaril.Calculi.LambdaCube.PERModel
