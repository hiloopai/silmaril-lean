module

public import Silmaril.Calculi.LambdaCube.PER.SystemF

@[expose] public section

set_option autoImplicit true

/-! # System Fω (λω) and its PER model

Church-style Fω with a kind context `Δ` for type-constructor variables and a
term context `Γ` of types, both de Bruijn. Constructor equality `ConEq` is the
typed βη-theory; typing has a conversion rule. `ConBEq`/`TypedB` are the
β-only variants that embed in the cube's λω corner (whose `Pseudo.Conv` has no η);
`Typed.kinded` is the regularity lemma used by the soundness proofs.

Kinds are interpreted as sets of PER-transformers (`Kind.Sem`):
`⟦*⟧ = PER M.D` and `⟦k → l⟧ = ⟦k⟧ → ⟦l⟧` (the full function space, which is
fine: kinds are predicative). Constructors are interpreted by `Con.interp`,
total on raw syntax (ill-kinded pieces go to `Kind.default`); application uses
the annotation-driven kind inference `Con.infer`. `∀k.A` is the intersection
over the whole of `⟦k⟧`.

Main statements: `ConEq.sound` (equal constructors denote equal
PER-transformers), `Typed.sound` and `TmEq.sound` (fundamental lemma and
βη-soundness), and the embedding of System F as the fragment with
only kind `*` (`typed_toOmega`, `interp_toOmega`).
-/

namespace Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega

/-- Kinds. -/
inductive Kind where
  | star
  | arr (k l : Kind)
  deriving DecidableEq

/-- Type constructors. -/
inductive Con where
  | var (n : ℕ)
  | arr (A B : Con)
  | all (k : Kind) (A : Con)
  | lam (k : Kind) (A : Con)
  | app (A B : Con)
  deriving DecidableEq

namespace Con

/-- Renaming of constructor variables. -/
def rename (ρ : ℕ → ℕ) : Con → Con
  | var n => var (ρ n)
  | arr A B => arr (rename ρ A) (rename ρ B)
  | all k A => all k (rename (scons 0 (Nat.succ ∘ ρ)) A)
  | lam k A => lam k (rename (scons 0 (Nat.succ ∘ ρ)) A)
  | app A B => app (rename ρ A) (rename ρ B)

/-- Lift a substitution under a constructor binder. -/
def liftSub (σ : ℕ → Con) : ℕ → Con := scons (var 0) (fun n => rename Nat.succ (σ n))

/-- Simultaneous substitution. -/
def subst (σ : ℕ → Con) : Con → Con
  | var n => σ n
  | arr A B => arr (subst σ A) (subst σ B)
  | all k A => all k (subst (liftSub σ) A)
  | lam k A => lam k (subst (liftSub σ) A)
  | app A B => app (subst σ A) (subst σ B)

/-- Instantiate variable `0` and lower the others. -/
def substOne (A B : Con) : Con := subst (scons B var) A

/-- Constructor variable `n` occurs free. -/
def FreeIn : ℕ → Con → Prop
  | n, var m => n = m
  | n, arr A B => FreeIn n A ∨ FreeIn n B
  | n, all _ A => FreeIn (n + 1) A
  | n, lam _ A => FreeIn (n + 1) A
  | n, app A B => FreeIn n A ∨ FreeIn n B

/-- Kind inference from binder annotations, given kinds of the free variables. -/
def infer : Con → (ℕ → Kind) → Option Kind
  | var n, κ => some (κ n)
  | arr _ _, _ => some .star
  | all _ _, _ => some .star
  | lam k A, κ => (infer A (scons k κ)).map (Kind.arr k)
  | app A _, κ =>
      match infer A κ with
      | some (.arr _ l) => some l
      | _ => none

end Con

/-- Kind contexts; the newest variable is first. -/
abbrev KCtx := List Kind

/-- Kinding. -/
inductive Kinded : KCtx → Con → Kind → Prop where
  | var : Δ[n]? = some k → Kinded Δ (.var n) k
  | arr : Kinded Δ A .star → Kinded Δ B .star → Kinded Δ (.arr A B) .star
  | all : Kinded (k :: Δ) A .star → Kinded Δ (.all k A) .star
  | lam : Kinded (k :: Δ) A l → Kinded Δ (.lam k A) (.arr k l)
  | app : Kinded Δ A (.arr k l) → Kinded Δ B k → Kinded Δ (.app A B) l

/-- Typed βη-equality of constructors. -/
inductive ConEq : KCtx → Con → Con → Kind → Prop where
  | refl : Kinded Δ A k → ConEq Δ A A k
  | symm : ConEq Δ A B k → ConEq Δ B A k
  | trans : ConEq Δ A B k → ConEq Δ B C k → ConEq Δ A C k
  | beta : Kinded (k :: Δ) A l → Kinded Δ B k →
      ConEq Δ (.app (.lam k A) B) (A.substOne B) l
  | eta : Kinded Δ A (.arr k l) →
      ConEq Δ (.lam k (.app (A.rename Nat.succ) (.var 0))) A (.arr k l)
  | arr : ConEq Δ A A' .star → ConEq Δ B B' .star → ConEq Δ (.arr A B) (.arr A' B') .star
  | all : ConEq (k :: Δ) A A' .star → ConEq Δ (.all k A) (.all k A') .star
  | lam : ConEq (k :: Δ) A A' l → ConEq Δ (.lam k A) (.lam k A') (.arr k l)
  | app : ConEq Δ A A' (.arr k l) → ConEq Δ B B' k → ConEq Δ (.app A B) (.app A' B') l

/-! ### Syntactic metatheory of kinding -/

theorem scons_comp_succ {α : Sort _} (x : α) (f : ℕ → α) : scons x f ∘ Nat.succ = f := rfl

theorem scons_comp_lift {α : Sort _} (x : α) (f : ℕ → α) (r : ℕ → ℕ) :
    scons x f ∘ scons 0 (Nat.succ ∘ r) = scons x (f ∘ r) := by
  funext n; cases n <;> rfl

/-- Renamings that preserve kinds lift under a binder. -/
theorem kren_lift {Δ Δ' : KCtx} {r : ℕ → ℕ}
    (hr : ∀ n k', Δ[n]? = some k' → Δ'[r n]? = some k') (k : Kind) :
    ∀ n k', (k :: Δ)[n]? = some k' → (k :: Δ')[scons 0 (Nat.succ ∘ r) n]? = some k' := by
  intro n k' h
  cases n with
  | zero => simpa using h
  | succ n => simpa using hr n k' (by simpa using h)

theorem kren_succ {Δ : KCtx} (k : Kind) :
    ∀ n k', Δ[n]? = some k' → (k :: Δ)[Nat.succ n]? = some k' := by
  intro n k' h; simpa using h

/-- Weakening of kinding along a renaming that preserves the kinds of variables. -/
theorem Kinded.rename (h : Kinded Δ A k) {Δ' : KCtx} {r : ℕ → ℕ}
    (hr : ∀ n k', Δ[n]? = some k' → Δ'[r n]? = some k') :
    Kinded Δ' (A.rename r) k := by
  induction h generalizing Δ' r with
  | var h => exact .var (hr _ _ h)
  | arr _ _ ih1 ih2 => exact .arr (ih1 hr) (ih2 hr)
  | all _ ih => exact .all (ih (kren_lift hr _))
  | lam _ ih => exact .lam (ih (kren_lift hr _))
  | app _ _ ih1 ih2 => exact .app (ih1 hr) (ih2 hr)

/-- Kind-preserving substitutions lift under a binder. -/
theorem ksub_lift {Δ Δ' : KCtx} {σ : ℕ → Con}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k') (k : Kind) :
    ∀ n k', (k :: Δ)[n]? = some k' → Kinded (k :: Δ') (Con.liftSub σ n) k' := by
  intro n k' h
  cases n with
  | zero => exact .var (by simpa using h)
  | succ n => exact (hσ n k' (by simpa using h)).rename (kren_succ k)

/-- Kinding is closed under kind-preserving substitution. -/
theorem Kinded.subst (h : Kinded Δ A k) {Δ' : KCtx} {σ : ℕ → Con}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k') :
    Kinded Δ' (A.subst σ) k := by
  induction h generalizing Δ' σ with
  | var h => exact hσ _ _ h
  | arr _ _ ih1 ih2 => exact .arr (ih1 hσ) (ih2 hσ)
  | all _ ih => exact .all (ih (ksub_lift hσ _))
  | lam _ ih => exact .lam (ih (ksub_lift hσ _))
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)

/-- Kinding is closed under instantiation of the newest variable. -/
theorem Kinded.substOne (hA : Kinded (k :: Δ) A l) (hB : Kinded Δ B k) :
    Kinded Δ (A.substOne B) l := by
  refine hA.subst fun n k' h => ?_
  cases n with
  | zero =>
    simp at h; subst h; exact hB
  | succ n => exact .var (by simpa using h)

theorem ConEq.kinded (h : ConEq Δ A B k) : Kinded Δ A k ∧ Kinded Δ B k := by
  induction h with
  | refl h => exact ⟨h, h⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | beta hA hB => exact ⟨.app (.lam hA) hB, hA.substOne hB⟩
  | eta hA => exact ⟨.lam (.app (hA.rename (kren_succ _)) (.var (by simp))), hA⟩
  | arr _ _ ih1 ih2 => exact ⟨.arr ih1.1 ih2.1, .arr ih1.2 ih2.2⟩
  | all _ ih => exact ⟨.all ih.1, .all ih.2⟩
  | lam _ ih => exact ⟨.lam ih.1, .lam ih.2⟩
  | app _ _ ih1 ih2 => exact ⟨.app ih1.1 ih2.1, .app ih1.2 ih2.2⟩

theorem ConEq.kinded_left (h : ConEq Δ A B k) : Kinded Δ A k := h.kinded.1

theorem ConEq.kinded_right (h : ConEq Δ A B k) : Kinded Δ B k := h.kinded.2

/-- Typed β-equality of constructors: `ConEq` without `eta`. The cube's
`Pseudo.Conv` is β-only, so this is the constructor equality that the λω
corner can follow (`TypedB.toPTS` in `PER/Cube.lean`). -/
inductive ConBEq : KCtx → Con → Con → Kind → Prop where
  | refl : Kinded Δ A k → ConBEq Δ A A k
  | symm : ConBEq Δ A B k → ConBEq Δ B A k
  | trans : ConBEq Δ A B k → ConBEq Δ B C k → ConBEq Δ A C k
  | beta : Kinded (k :: Δ) A l → Kinded Δ B k →
      ConBEq Δ (.app (.lam k A) B) (A.substOne B) l
  | arr : ConBEq Δ A A' .star → ConBEq Δ B B' .star → ConBEq Δ (.arr A B) (.arr A' B') .star
  | all : ConBEq (k :: Δ) A A' .star → ConBEq Δ (.all k A) (.all k A') .star
  | lam : ConBEq (k :: Δ) A A' l → ConBEq Δ (.lam k A) (.lam k A') (.arr k l)
  | app : ConBEq Δ A A' (.arr k l) → ConBEq Δ B B' k → ConBEq Δ (.app A B) (.app A' B') l

theorem ConBEq.toConEq (h : ConBEq Δ A B k) : ConEq Δ A B k := by
  induction h with
  | refl h => exact .refl h
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta hA hB => exact .beta hA hB
  | arr _ _ ih1 ih2 => exact .arr ih1 ih2
  | all _ ih => exact .all ih
  | lam _ ih => exact .lam ih
  | app _ _ ih1 ih2 => exact .app ih1 ih2

/-- Church-style Fω terms. -/
inductive Tm where
  | var (n : ℕ)
  | app (t u : Tm)
  | lam (A : Con) (t : Tm)
  | tapp (t : Tm) (C : Con)
  | tlam (k : Kind) (t : Tm)
  deriving DecidableEq

namespace Tm

/-- Rename constructor variables in annotations. -/
def tyRename (ρ : ℕ → ℕ) : Tm → Tm
  | var n => var n
  | app t u => app (tyRename ρ t) (tyRename ρ u)
  | lam A t => lam (A.rename ρ) (tyRename ρ t)
  | tapp t C => tapp (tyRename ρ t) (C.rename ρ)
  | tlam k t => tlam k (tyRename (scons 0 (Nat.succ ∘ ρ)) t)

/-- Substitute constructors in annotations. -/
def tySubst (σ : ℕ → Con) : Tm → Tm
  | var n => var n
  | app t u => app (tySubst σ t) (tySubst σ u)
  | lam A t => lam (A.subst σ) (tySubst σ t)
  | tapp t C => tapp (tySubst σ t) (C.subst σ)
  | tlam k t => tlam k (tySubst (Con.liftSub σ) t)

/-- Instantiate constructor variable `0` in annotations. -/
def tySubstOne (t : Tm) (C : Con) : Tm := tySubst (scons C Con.var) t

/-- Rename term variables. -/
def rename (ρ : ℕ → ℕ) : Tm → Tm
  | var n => var (ρ n)
  | app t u => app (rename ρ t) (rename ρ u)
  | lam A t => lam A (rename (scons 0 (Nat.succ ∘ ρ)) t)
  | tapp t C => tapp (rename ρ t) C
  | tlam k t => tlam k (rename ρ t)

/-- Lift a term substitution under a term binder. -/
def liftSub (σ : ℕ → Tm) : ℕ → Tm := scons (var 0) (fun n => rename Nat.succ (σ n))

/-- Simultaneous substitution of term variables. -/
def subst (σ : ℕ → Tm) : Tm → Tm
  | var n => σ n
  | app t u => app (subst σ t) (subst σ u)
  | lam A t => lam A (subst (liftSub σ) t)
  | tapp t C => tapp (subst σ t) C
  | tlam k t => tlam k (subst (fun n => tyRename Nat.succ (σ n)) t)

/-- Substitute for term variable `0`. -/
def substOne (t u : Tm) : Tm := subst (scons u var) t

/-- Constructor variable `n` occurs free in an annotation. -/
def TyFreeIn : ℕ → Tm → Prop
  | _, var _ => False
  | n, app t u => TyFreeIn n t ∨ TyFreeIn n u
  | n, lam A t => A.FreeIn n ∨ TyFreeIn n t
  | n, tapp t C => TyFreeIn n t ∨ C.FreeIn n
  | n, tlam _ t => TyFreeIn (n + 1) t

/-- Curry-style erasure. -/
def erase : Tm → ULam
  | var n => .var n
  | app t u => .app (erase t) (erase u)
  | lam _ t => .lam (erase t)
  | tapp t _ => erase t
  | tlam _ t => erase t

end Tm

/-- Term contexts. -/
abbrev Ctx := List Con

/-- Typing of Fω, with conversion. -/
inductive Typed : KCtx → Ctx → Tm → Con → Prop where
  | var : Γ[n]? = some A → Typed Δ Γ (.var n) A
  | app : Typed Δ Γ t (.arr A B) → Typed Δ Γ u A → Typed Δ Γ (.app t u) B
  | lam : Kinded Δ A .star → Typed Δ (A :: Γ) t B → Typed Δ Γ (.lam A t) (.arr A B)
  | tlam : Typed (k :: Δ) (Γ.map (Con.rename Nat.succ)) t A →
      Typed Δ Γ (.tlam k t) (.all k A)
  | tapp : Typed Δ Γ t (.all k A) → Kinded Δ C k → Typed Δ Γ (.tapp t C) (A.substOne C)
  | conv : Typed Δ Γ t A → ConEq Δ A B .star → Typed Δ Γ t B

/-- Fω typing with β-only type conversion (`ConBEq`). This is the fragment of
`Typed` that embeds in the cube's λω corner, whose conversion has no η. -/
inductive TypedB : KCtx → Ctx → Tm → Con → Prop where
  | var : Γ[n]? = some A → TypedB Δ Γ (.var n) A
  | app : TypedB Δ Γ t (.arr A B) → TypedB Δ Γ u A → TypedB Δ Γ (.app t u) B
  | lam : Kinded Δ A .star → TypedB Δ (A :: Γ) t B → TypedB Δ Γ (.lam A t) (.arr A B)
  | tlam : TypedB (k :: Δ) (Γ.map (Con.rename Nat.succ)) t A →
      TypedB Δ Γ (.tlam k t) (.all k A)
  | tapp : TypedB Δ Γ t (.all k A) → Kinded Δ C k → TypedB Δ Γ (.tapp t C) (A.substOne C)
  | conv : TypedB Δ Γ t A → ConBEq Δ A B .star → TypedB Δ Γ t B

theorem TypedB.toTyped (h : TypedB Δ Γ t A) : Typed Δ Γ t A := by
  induction h with
  | var h => exact .var h
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam hA _ ih => exact .lam hA ih
  | tlam _ ih => exact .tlam ih
  | tapp _ hC ih => exact .tapp ih hC
  | conv _ hAB ih => exact .conv ih hAB.toConEq

theorem ctx_cons_kinded {Δ : KCtx} {Γ : Ctx} {A : Con} (hA : Kinded Δ A .star)
    (hΓ : ∀ B ∈ Γ, Kinded Δ B .star) : ∀ B ∈ A :: Γ, Kinded Δ B .star := by
  intro B hB
  rcases List.mem_cons.mp hB with rfl | hB
  exacts [hA, hΓ B hB]

theorem ctx_shift_kinded {Δ : KCtx} {Γ : Ctx} (hΓ : ∀ B ∈ Γ, Kinded Δ B .star) {k : Kind} :
    ∀ B ∈ Γ.map (Con.rename Nat.succ), Kinded (k :: Δ) B .star := by
  intro B hB
  obtain ⟨B0, hB0, rfl⟩ := List.mem_map.mp hB
  exact (hΓ B0 hB0).rename (kren_succ k)

/-- Regularity: in a well-kinded context, typed terms have well-kinded types. -/
theorem Typed.kinded (h : Typed Δ Γ t A) (hΓ : ∀ B ∈ Γ, Kinded Δ B .star) :
    Kinded Δ A .star := by
  induction h with
  | var hn => exact hΓ _ (List.mem_iff_getElem?.mpr ⟨_, hn⟩)
  | app _ _ ih _ => cases ih hΓ with | arr _ hB => exact hB
  | lam hA _ ih => exact .arr hA (ih (ctx_cons_kinded hA hΓ))
  | tlam _ ih => exact .all (ih (ctx_shift_kinded hΓ))
  | tapp _ hC ih => cases ih hΓ with | all hA => exact hA.substOne hC
  | conv _ hAB _ => exact hAB.kinded_right

/-- Typed βη-equality of terms. -/
inductive TmEq : KCtx → Ctx → Tm → Tm → Con → Prop where
  | refl : Typed Δ Γ t A → TmEq Δ Γ t t A
  | symm : TmEq Δ Γ t u A → TmEq Δ Γ u t A
  | trans : TmEq Δ Γ t u A → TmEq Δ Γ u v A → TmEq Δ Γ t v A
  | beta : Kinded Δ A .star → Typed Δ (A :: Γ) t B → Typed Δ Γ u A →
      TmEq Δ Γ (.app (.lam A t) u) (t.substOne u) B
  | eta : Kinded Δ A .star → Typed Δ Γ t (.arr A B) →
      TmEq Δ Γ (.lam A (.app (t.rename Nat.succ) (.var 0))) t (.arr A B)
  | tbeta : Typed (k :: Δ) (Γ.map (Con.rename Nat.succ)) t A → Kinded Δ C k →
      TmEq Δ Γ (.tapp (.tlam k t) C) (t.tySubstOne C) (A.substOne C)
  | teta : Typed Δ Γ t (.all k A) →
      TmEq Δ Γ (.tlam k (.tapp (t.tyRename Nat.succ) (.var 0))) t (.all k A)
  | app : TmEq Δ Γ t t' (.arr A B) → TmEq Δ Γ u u' A → TmEq Δ Γ (.app t u) (.app t' u') B
  | lam : Kinded Δ A .star → TmEq Δ (A :: Γ) t t' B →
      TmEq Δ Γ (.lam A t) (.lam A t') (.arr A B)
  | tapp : TmEq Δ Γ t t' (.all k A) → Kinded Δ C k →
      TmEq Δ Γ (.tapp t C) (.tapp t' C) (A.substOne C)
  -- Type arguments may vary by constructor equality: x C and x ((λα.α) C)
  -- have β-convertible encodings, and conversion reflection needs this rule.
  /-- Type arguments may be replaced by equal constructors. (A lambda-annotation
  congruence is derivable from `eta`, `beta` and `conv`.) -/
  | tappConv : Typed Δ Γ t (.all k A) → ConEq Δ C C' k →
      TmEq Δ Γ (.tapp t C) (.tapp t C') (A.substOne C)
  | tlam : TmEq (k :: Δ) (Γ.map (Con.rename Nat.succ)) t t' A →
      TmEq Δ Γ (.tlam k t) (.tlam k t') (.all k A)
  | conv : TmEq Δ Γ t u A → ConEq Δ A B .star → TmEq Δ Γ t u B

/-! ## Kinds as sets of PER-transformers -/

/-- The semantic kind: PERs at `*`, full function spaces at arrows. -/
def Kind.Sem (D : Type u) : Kind → Type u
  | .star => PER D
  | .arr k l => Kind.Sem D k → Kind.Sem D l

/-- A canonical inhabitant of each semantic kind (the empty PER, pointwise). -/
def Kind.default {D : Type u} : (k : Kind) → k.Sem D
  | .star => PER.bot
  | .arr _ l => fun _ => Kind.default l

/-- A semantic constructor of some kind. -/
abbrev SemEntry (D : Type u) := Σ k : Kind, k.Sem D

variable (M : CombAlg.{u})

/-- Interpretation of constructors at a requested kind. -/
def Con.interp : Con → (ℕ → SemEntry M.D) → (k : Kind) → k.Sem M.D
  | .var n, ξ, k =>
      if h : (ξ n).1 = k then cast (congrArg (Kind.Sem M.D) h) (ξ n).2 else Kind.default k
  | .arr A B, ξ, .star => PER.arrow M (Con.interp A ξ .star) (Con.interp B ξ .star)
  | .all k' A, ξ, .star =>
      PER.iInf fun X : k'.Sem M.D => Con.interp A (scons ⟨k', X⟩ ξ) .star
  | .lam _ A, ξ, .arr k l => fun X => Con.interp A (scons ⟨k, X⟩ ξ) l
  | .app A B, ξ, l =>
      match B.infer (fun n => (ξ n).1) with
      | some k => Con.interp A ξ (.arr k l) (Con.interp B ξ k)
      | none => Kind.default l
  | _, _, k => Kind.default k

/-- A semantic environment fits a kind context. -/
def Fits (Δ : KCtx) (ξ : ℕ → SemEntry M.D) : Prop := ∀ n k, Δ[n]? = some k → (ξ n).1 = k

/-- Related realizer environments for a term context. -/
def EnvRel (Γ : Ctx) (ξ : ℕ → SemEntry M.D) (ρ ρ' : ℕ → M.D) : Prop :=
  ∀ n (A : Con), Γ[n]? = some A → ((A.interp M ξ .star).rel (ρ n) (ρ' n))

/-- Semantic equality of terms at a type. -/
def ValidEq (Δ : KCtx) (Γ : Ctx) (t u : Tm) (A : Con) : Prop :=
  ∀ ξ ρ ρ', Fits M Δ ξ → EnvRel M Γ ξ ρ ρ' →
    (A.interp M ξ .star).rel (t.erase.eval M ρ) (u.erase.eval M ρ')

/-- Semantic typing. -/
def Valid (Δ : KCtx) (Γ : Ctx) (t : Tm) (A : Con) : Prop := ValidEq M Δ Γ t t A

variable {M}

/-- Kind contexts lift: extending by `k` is matched by `scons k`. -/
theorem kctx_lift {Δ : KCtx} {κ : ℕ → Kind} (hκ : ∀ n k, Δ[n]? = some k → κ n = k) (k : Kind) :
    ∀ n k', (k :: Δ)[n]? = some k' → scons k κ n = k' := by
  intro n k' h
  cases n with
  | zero => simpa using h
  | succ n => exact hκ n k' (by simpa using h)

theorem Kinded.infer (h : Kinded Δ A k) {κ : ℕ → Kind} (hκ : ∀ n k, Δ[n]? = some k → κ n = k) :
    A.infer κ = some k := by
  induction h generalizing κ with
  | var h => simp [Con.infer, hκ _ _ h]
  | arr => rfl
  | all => rfl
  | lam _ ih => simp [Con.infer, ih (kctx_lift hκ _)]
  | app _ _ ih1 _ => simp [Con.infer, ih1 hκ]

theorem Kinded.infer_fits (h : Kinded Δ A k) {ξ : ℕ → SemEntry M.D} (hξ : Fits M Δ ξ) :
    A.infer (fun n => (ξ n).1) = some k :=
  h.infer hξ

theorem Con.infer_rename (r : ℕ → ℕ) (A : Con) (κ : ℕ → Kind) :
    (A.rename r).infer κ = A.infer (κ ∘ r) := by
  induction A generalizing r κ with
  | var _ => rfl
  | arr => rfl
  | all => rfl
  | lam _ _ ih => simp only [Con.rename, Con.infer, ih, scons_comp_lift]
  | app _ _ ihA _ => simp only [Con.rename, Con.infer, ihA]

theorem Fits.cons {Δ : KCtx} {ξ : ℕ → SemEntry M.D} (hξ : Fits M Δ ξ) {k : Kind}
    (X : k.Sem M.D) : Fits M (k :: Δ) (scons ⟨k, X⟩ ξ) := by
  intro n k' h
  cases n with
  | zero => simpa using h
  | succ n => exact hξ n k' (by simpa using h)

theorem Con.interp_var_eq (n : ℕ) (ξ : ℕ → SemEntry M.D) (k : Kind) :
    (Con.var n).interp M ξ k =
      if h : (ξ n).1 = k then cast (congrArg (Kind.Sem M.D) h) (ξ n).2 else Kind.default k :=
  rfl

theorem semEntry_cast_eq {D : Type u} (e : SemEntry D) {k : Kind} (h : e.1 = k) :
    e = ⟨k, cast (congrArg (Kind.Sem D) h) e.2⟩ := by
  obtain ⟨k0, x⟩ := e; subst h; rfl

theorem semEntry_cast_of_eq {D : Type u} (e : SemEntry D) {k : Kind} {X : k.Sem D}
    (he : e = ⟨k, X⟩) :
    (if h : e.1 = k then cast (congrArg (Kind.Sem D) h) e.2 else Kind.default k) = X := by
  subst he; simp

theorem interp_var_of_eq {ξ : ℕ → SemEntry M.D} {n : ℕ} {k : Kind} {X : k.Sem M.D}
    (he : ξ n = ⟨k, X⟩) : (Con.var n).interp M ξ k = X := by
  rw [Con.interp_var_eq]; exact semEntry_cast_of_eq _ he

theorem entry_eq_of_fst {ξ : ℕ → SemEntry M.D} {n : ℕ} {k : Kind} (h : (ξ n).1 = k) :
    ξ n = ⟨k, (Con.var n).interp M ξ k⟩ := by
  rw [Con.interp_var_eq]
  split
  · exact semEntry_cast_eq _ h
  · exact absurd h ‹_›

theorem Con.interp_app_eq (A B : Con) (ξ : ℕ → SemEntry M.D) (l : Kind) :
    (Con.app A B).interp M ξ l =
      match B.infer (fun n => (ξ n).1) with
      | some k => A.interp M ξ (.arr k l) (B.interp M ξ k)
      | none => Kind.default l :=
  rfl

theorem interp_app_of_infer {A B : Con} {ξ : ℕ → SemEntry M.D} {k l : Kind}
    (h : B.infer (fun n => (ξ n).1) = some k) :
    (Con.app A B).interp M ξ l = A.interp M ξ (.arr k l) (B.interp M ξ k) := by
  simp only [Con.interp_app_eq, h]

theorem interp_app_of_none {A B : Con} {ξ : ℕ → SemEntry M.D} {l : Kind}
    (h : B.infer (fun n => (ξ n).1) = none) :
    (Con.app A B).interp M ξ l = Kind.default l := by
  simp only [Con.interp_app_eq, h]

theorem Con.interp_rename (r : ℕ → ℕ) (A : Con) (ξ : ℕ → SemEntry M.D) (k : Kind) :
    (A.rename r).interp M ξ k = A.interp M (ξ ∘ r) k := by
  induction A generalizing r ξ k with
  | var _ => rfl
  | arr _ _ ihA ihB =>
    cases k with
    | star =>
      show PER.arrow M _ _ = PER.arrow M _ _
      rw [ihA, ihB]
    | arr _ _ => rfl
  | all k' A ih =>
    cases k with
    | star =>
      show PER.iInf _ = PER.iInf _
      exact congrArg PER.iInf (funext fun X => by
        show (A.rename _).interp M (scons ⟨k', X⟩ ξ) .star = A.interp M (scons ⟨k', X⟩ (ξ ∘ r)) .star
        rw [ih, scons_comp_lift])
    | arr _ _ => rfl
  | lam _ A ih =>
    cases k with
    | star => rfl
    | arr a b =>
      refine funext fun X => ?_
      show (A.rename _).interp M (scons ⟨a, X⟩ ξ) b = A.interp M (scons ⟨a, X⟩ (ξ ∘ r)) b
      rw [ih, scons_comp_lift]
  | app A B ihA ihB =>
    show (Con.app (A.rename r) (B.rename r)).interp M ξ k = _
    have hi : (B.rename r).infer (fun n => (ξ n).1) = B.infer (fun n => ((ξ ∘ r) n).1) :=
      Con.infer_rename r B _
    cases hk : B.infer (fun n => ((ξ ∘ r) n).1) with
    | some k0 =>
      rw [interp_app_of_infer (hi.trans hk), interp_app_of_infer hk, ihA, ihB]
    | none =>
      rw [interp_app_of_none (hi.trans hk), interp_app_of_none hk]

/-- Semantic substitutions lift under a binder. -/
theorem interp_subst_lift {Δ Δ' : KCtx} {σ : ℕ → Con} {ξ ξ' : ℕ → SemEntry M.D}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k' ∧ ξ' n = ⟨k', (σ n).interp M ξ k'⟩)
    (k0 : Kind) (X : k0.Sem M.D) :
    ∀ n k', (k0 :: Δ)[n]? = some k' → Kinded (k0 :: Δ') (Con.liftSub σ n) k' ∧
      scons ⟨k0, X⟩ ξ' n = ⟨k', (Con.liftSub σ n).interp M (scons ⟨k0, X⟩ ξ) k'⟩ := by
  intro n k' h
  cases n with
  | zero =>
    simp at h; subst h
    exact ⟨.var (by simp),
      congrArg (Sigma.mk _) (interp_var_of_eq (ξ := scons ⟨_, X⟩ ξ) (n := 0) rfl).symm⟩
  | succ n =>
    obtain ⟨hk, he⟩ := hσ n k' (by simpa using h)
    refine ⟨hk.rename (kren_succ k0), ?_⟩
    rw [show scons (⟨k0, X⟩ : SemEntry M.D) ξ' (n + 1) = ξ' n from rfl, he]
    exact congrArg (Sigma.mk k') (Con.interp_rename Nat.succ (σ n) (scons ⟨k0, X⟩ ξ) k').symm

/-- The semantic substitution lemma, for well-kinded constructors. -/
theorem Con.interp_subst (h : Kinded Δ A k) {Δ' : KCtx} {σ : ℕ → Con}
    {ξ ξ' : ℕ → SemEntry M.D}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k' ∧ ξ' n = ⟨k', (σ n).interp M ξ k'⟩)
    (hξ : Fits M Δ' ξ) :
    (A.subst σ).interp M ξ k = A.interp M ξ' k := by
  induction h generalizing Δ' σ ξ ξ' with
  | var h => exact (interp_var_of_eq (hσ _ _ h).2).symm
  | arr _ _ ih1 ih2 =>
    show PER.arrow M _ _ = PER.arrow M _ _
    rw [ih1 (hσ := hσ) (hξ := hξ), ih2 (hσ := hσ) (hξ := hξ)]
  | all _ ih =>
    show PER.iInf _ = PER.iInf _
    exact congrArg PER.iInf (funext fun X =>
      ih (hσ := interp_subst_lift hσ _ X) (hξ := hξ.cons X))
  | lam _ ih =>
    exact funext fun X => ih (hσ := interp_subst_lift hσ _ X) (hξ := hξ.cons X)
  | app _ hB ih1 ih2 =>
    show (Con.app (Con.subst σ _) (Con.subst σ _)).interp M ξ _ = _
    rw [interp_app_of_infer ((hB.subst fun n k' hn => (hσ n k' hn).1).infer_fits hξ),
      interp_app_of_infer (hB.infer_fits (ξ := ξ') fun n k' hn => by rw [(hσ n k' hn).2]),
      ih1 (hσ := hσ) (hξ := hξ),
      ih2 (hσ := hσ) (hξ := hξ)]

theorem Con.interp_substOne (hA : Kinded (k :: Δ) A l) (hB : Kinded Δ B k)
    {ξ : ℕ → SemEntry M.D} (hξ : Fits M Δ ξ) :
    (A.substOne B).interp M ξ l = A.interp M (scons ⟨k, B.interp M ξ k⟩ ξ) l := by
  refine Con.interp_subst hA (fun n k' h => ?_) hξ
  cases n with
  | zero =>
    simp at h; subst h
    exact ⟨hB, rfl⟩
  | succ n =>
    have h' : Δ[n]? = some k' := by simpa using h
    exact ⟨.var h', entry_eq_of_fst (hξ n k' h')⟩

theorem interp_eta {A : Con} {k l : Kind} {ξ : ℕ → SemEntry M.D} (X : k.Sem M.D) :
    (Con.app (A.rename Nat.succ) (.var 0)).interp M (scons ⟨k, X⟩ ξ) l =
      A.interp M ξ (.arr k l) X := by
  rw [interp_app_of_infer (A := A.rename Nat.succ) (B := .var 0) (ξ := scons ⟨k, X⟩ ξ)
      (k := k) (l := l) rfl,
    Con.interp_rename, scons_comp_succ,
    interp_var_of_eq (ξ := scons ⟨k, X⟩ ξ) (n := 0) (k := k) (X := X) rfl]

/-- Equal constructors denote equal PER-transformers. -/
theorem ConEq.sound (h : ConEq Δ A B k) {ξ : ℕ → SemEntry M.D} (hξ : Fits M Δ ξ) :
    A.interp M ξ k = B.interp M ξ k := by
  induction h generalizing ξ with
  | refl => rfl
  | symm _ ih => exact (ih (hξ := hξ)).symm
  | trans _ _ ih1 ih2 => exact (ih1 (hξ := hξ)).trans (ih2 (hξ := hξ))
  | beta hA hB =>
    exact (interp_app_of_infer (hB.infer_fits hξ)).trans (Con.interp_substOne hA hB hξ).symm
  | eta _ => exact funext fun X => interp_eta X
  | arr _ _ ih1 ih2 =>
    show PER.arrow M _ _ = PER.arrow M _ _
    rw [ih1 (hξ := hξ), ih2 (hξ := hξ)]
  | all _ ih =>
    show PER.iInf _ = PER.iInf _
    exact congrArg PER.iInf (funext fun X => ih (hξ := hξ.cons X))
  | lam _ ih => exact funext fun X => ih (hξ := hξ.cons X)
  | app _ hB ih1 ih2 =>
    rw [interp_app_of_infer (hB.kinded_left.infer_fits hξ),
      interp_app_of_infer (hB.kinded_right.infer_fits hξ), ih1 (hξ := hξ), ih2 (hξ := hξ)]

/-! ### Terms: erasure, environments, the fundamental lemma -/

theorem Tm.erase_tyRename (r : ℕ → ℕ) (t : Tm) : (t.tyRename r).erase = t.erase := by
  induction t generalizing r <;> simp_all [Tm.tyRename, Tm.erase]

theorem Tm.erase_tySubst (σ : ℕ → Con) (t : Tm) : (t.tySubst σ).erase = t.erase := by
  induction t generalizing σ <;> simp_all [Tm.tySubst, Tm.erase]

theorem Tm.erase_rename (r : ℕ → ℕ) (t : Tm) : (t.rename r).erase = t.erase.rename r := by
  induction t generalizing r <;> simp_all [Tm.rename, Tm.erase, ULam.rename]

theorem Tm.subst_var (t : Tm) : t.subst Tm.var = t := by
  induction t with
  | var _ => rfl
  | app _ _ iht ihu => simp only [Tm.subst, iht, ihu]
  | lam _ _ ih =>
    have h : Tm.liftSub Tm.var = Tm.var := by funext n; cases n <;> rfl
    simp only [Tm.subst, h, ih]
  | tapp _ _ ih => simp only [Tm.subst, ih]
  | tlam k _ ih => exact congrArg (Tm.tlam k) ih

theorem EnvRel.symm {Γ : Ctx} {ξ : ℕ → SemEntry M.D} {ρ ρ' : ℕ → M.D}
    (h : EnvRel M Γ ξ ρ ρ') : EnvRel M Γ ξ ρ' ρ :=
  fun n A hn => PER.symm _ (h n A hn)

theorem EnvRel.refl_right {Γ : Ctx} {ξ : ℕ → SemEntry M.D} {ρ ρ' : ℕ → M.D}
    (h : EnvRel M Γ ξ ρ ρ') : EnvRel M Γ ξ ρ' ρ' :=
  fun n A hn => PER.trans _ (PER.symm _ (h n A hn)) (h n A hn)

theorem EnvRel.cons {Γ : Ctx} {ξ : ℕ → SemEntry M.D} {ρ ρ' : ℕ → M.D}
    (h : EnvRel M Γ ξ ρ ρ') {A : Con} {a a' : M.D} (ha : (A.interp M ξ .star).rel a a') :
    EnvRel M (A :: Γ) ξ (scons a ρ) (scons a' ρ') := by
  intro n C hn
  cases n with
  | zero => simp at hn; subst hn; exact ha
  | succ n => exact h n C (by simpa using hn)

theorem EnvRel.shift {Γ : Ctx} {ξ : ℕ → SemEntry M.D} {ρ ρ' : ℕ → M.D}
    (h : EnvRel M Γ ξ ρ ρ') {k : Kind} (X : k.Sem M.D) :
    EnvRel M (Γ.map (Con.rename Nat.succ)) (scons ⟨k, X⟩ ξ) ρ ρ' := by
  intro n C hn
  simp at hn
  obtain ⟨C0, hC0, rfl⟩ := hn
  rw [Con.interp_rename, scons_comp_succ]
  exact h n C0 hC0

theorem subst_rel_lift {Γ' : Ctx} {A : Con} {ξ : ℕ → SemEntry M.D} {σ : ℕ → Tm}
    {τ ρ' : ℕ → M.D}
    (hσ : ∀ (n : ℕ) (C : Con), Γ'[n]? = some C → (C.interp M ξ .star).rel (τ n) ((σ n).erase.eval M ρ'))
    {a a' : M.D} (ha : (A.interp M ξ .star).rel a a') :
    ∀ (n : ℕ) (C : Con), (A :: Γ')[n]? = some C →
      (C.interp M ξ .star).rel (scons a τ n) ((Tm.liftSub σ n).erase.eval M (scons a' ρ')) := by
  intro n C h
  cases n with
  | zero => simp at h; subst h; exact ha
  | succ n =>
    have := hσ n C (by simpa using h)
    show (C.interp M ξ .star).rel (τ n) (((σ n).rename Nat.succ).erase.eval M (scons a' ρ'))
    rw [Tm.erase_rename, ULam.eval_rename, scons_comp_succ]
    exact this

theorem subst_rel_shift {Γ' : Ctx} {ξ : ℕ → SemEntry M.D} {σ : ℕ → Tm} {τ ρ' : ℕ → M.D}
    (hσ : ∀ (n : ℕ) (C : Con), Γ'[n]? = some C → (C.interp M ξ .star).rel (τ n) ((σ n).erase.eval M ρ'))
    {k : Kind} (X : k.Sem M.D) :
    ∀ (n : ℕ) (C : Con), (Γ'.map (Con.rename Nat.succ))[n]? = some C →
      (C.interp M (scons ⟨k, X⟩ ξ) .star).rel (τ n)
        ((Tm.tyRename Nat.succ (σ n)).erase.eval M ρ') := by
  intro n C h
  simp at h
  obtain ⟨C0, hC0, rfl⟩ := h
  rw [Con.interp_rename, scons_comp_succ, Tm.erase_tyRename]
  exact hσ n C0 hC0

/-- The fundamental lemma, generalized over a substitution related up to the PERs. -/
theorem Typed.subst_rel (h : Typed Δ Γ' t B) (hΓ' : ∀ C ∈ Γ', Kinded Δ C .star)
    {ξ : ℕ → SemEntry M.D} (hξ : Fits M Δ ξ) {σ : ℕ → Tm} {τ ρ' : ℕ → M.D}
    (hσ : ∀ (n : ℕ) (A : Con), Γ'[n]? = some A → (A.interp M ξ .star).rel (τ n) ((σ n).erase.eval M ρ')) :
    (B.interp M ξ .star).rel (t.erase.eval M τ) ((t.subst σ).erase.eval M ρ') := by
  induction h generalizing ξ σ τ ρ' with
  | var hn => exact hσ _ _ hn
  | app _ _ ih1 ih2 =>
    have h1 := ih1 (hΓ' := hΓ') (hξ := hξ) (hσ := hσ)
    exact h1 _ _ (ih2 (hΓ' := hΓ') (hξ := hξ) (hσ := hσ))
  | lam hA _ ih =>
    intro a a' ha
    simp only [Tm.erase, Tm.subst]
    rw [ULam.eval_lam, ULam.eval_lam]
    exact ih (hΓ' := ctx_cons_kinded hA hΓ') (hξ := hξ) (hσ := subst_rel_lift hσ ha)
  | tlam _ ih =>
    intro X
    exact ih (hΓ' := ctx_shift_kinded hΓ') (hξ := hξ.cons X) (hσ := subst_rel_shift hσ X)
  | tapp ht hC ih =>
    cases ht.kinded hΓ' with
    | all hA =>
      rw [Con.interp_substOne hA hC hξ]
      exact ih (hΓ' := hΓ') (hξ := hξ) (hσ := hσ) _
  | conv _ hAB ih =>
    rw [← ConEq.sound hAB hξ]
    exact ih (hΓ' := hΓ') (hξ := hξ) (hσ := hσ)

/-- The fundamental lemma for Fω, for a well-kinded context (types of
ill-kinded contexts may use a variable at two kinds, where `Con.interp` is junk). -/
theorem Typed.sound (h : Typed Δ Γ t A) (hΓ : ∀ B ∈ Γ, Kinded Δ B .star) :
    Valid M Δ Γ t A := by
  intro ξ ρ ρ' hξ hρ
  have := Typed.subst_rel h hΓ hξ (σ := Tm.var) (τ := ρ) (ρ' := ρ') hρ
  rwa [Tm.subst_var] at this

/-- Substitution up to the PER (β-soundness in a combinatory algebra). -/
theorem Typed.subst_sound (ht : Typed Δ (A :: Γ) t B) (hu : Typed Δ Γ u A)
    (hA : Kinded Δ A .star) (hΓ : ∀ C ∈ Γ, Kinded Δ C .star)
    {ξ : ℕ → SemEntry M.D} (hξ : Fits M Δ ξ) {ρ ρ' : ℕ → M.D} (hρ : EnvRel M Γ ξ ρ ρ') :
    (B.interp M ξ .star).rel (t.erase.eval M (scons (u.erase.eval M ρ) ρ))
      ((t.substOne u).erase.eval M ρ') := by
  refine Typed.subst_rel ht (ctx_cons_kinded hA hΓ) hξ (σ := scons u Tm.var) fun n C h => ?_
  cases n with
  | zero =>
    simp at h; subst h
    exact Typed.sound hu hΓ ξ ρ ρ' hξ hρ
  | succ n => exact hρ n C (by simpa using h)

/-- Regularity of term equality. -/
theorem TmEq.kinded (h : TmEq Δ Γ t u A) (hΓ : ∀ B ∈ Γ, Kinded Δ B .star) :
    Kinded Δ A .star := by
  induction h with
  | refl ht => exact ht.kinded hΓ
  | symm _ ih => exact ih hΓ
  | trans _ _ ih _ => exact ih hΓ
  | beta hA ht _ => exact ht.kinded (ctx_cons_kinded hA hΓ)
  | eta _ ht => exact ht.kinded hΓ
  | tbeta ht hC => exact (ht.kinded (ctx_shift_kinded hΓ)).substOne hC
  | teta ht => exact ht.kinded hΓ
  | app _ _ ih _ => cases ih hΓ with | arr _ hB => exact hB
  | lam hA _ ih => exact .arr hA (ih (ctx_cons_kinded hA hΓ))
  | tapp _ hC ih => cases ih hΓ with | all hA => exact hA.substOne hC
  | tappConv ht hC => cases ht.kinded hΓ with | all hA => exact hA.substOne hC.kinded_left
  | tlam _ ih => exact .all (ih (ctx_shift_kinded hΓ))
  | conv _ hAB _ => exact hAB.kinded_right

/-- βη-soundness for Fω. -/
theorem TmEq.sound (h : TmEq Δ Γ t u A) (hΓ : ∀ B ∈ Γ, Kinded Δ B .star) :
    ValidEq M Δ Γ t u A := by
  induction h with
  | refl ht => exact Typed.sound ht hΓ
  | symm _ ih =>
    intro ξ ρ ρ' hξ hρ
    exact PER.symm _ (ih hΓ ξ ρ' ρ hξ hρ.symm)
  | trans _ _ ih1 ih2 =>
    intro ξ ρ ρ' hξ hρ
    exact PER.trans _ (ih1 hΓ ξ ρ ρ' hξ hρ) (ih2 hΓ ξ ρ' ρ' hξ hρ.refl_right)
  | beta hA ht hu =>
    intro ξ ρ ρ' hξ hρ
    simp only [Tm.erase, ULam.eval_app]
    rw [ULam.eval_lam]
    exact Typed.subst_sound ht hu hA hΓ hξ hρ
  | eta _ ht =>
    intro ξ ρ ρ' hξ hρ a a' ha
    simp only [Tm.erase]
    rw [ULam.eval_lam, ULam.eval_app, Tm.erase_rename, ULam.eval_rename, scons_comp_succ]
    exact Typed.sound ht hΓ ξ ρ ρ' hξ hρ a a' ha
  | tbeta ht hC =>
    intro ξ ρ ρ' hξ hρ
    have := Typed.sound (Typed.tapp (Typed.tlam ht) hC) hΓ ξ ρ ρ' hξ hρ
    simpa only [Tm.erase, Tm.tySubstOne, Tm.erase_tySubst] using this
  | teta ht =>
    intro ξ ρ ρ' hξ hρ
    have := Typed.sound ht hΓ ξ ρ ρ' hξ hρ
    simpa only [Tm.erase, Tm.erase_tyRename] using this
  | app _ _ ih1 ih2 =>
    intro ξ ρ ρ' hξ hρ
    exact ih1 hΓ ξ ρ ρ' hξ hρ _ _ (ih2 hΓ ξ ρ ρ' hξ hρ)
  | lam hA _ ih =>
    intro ξ ρ ρ' hξ hρ a a' ha
    simp only [Tm.erase]
    rw [ULam.eval_lam, ULam.eval_lam]
    exact ih (ctx_cons_kinded hA hΓ) ξ _ _ hξ (hρ.cons ha)
  | tapp ht hC ih =>
    intro ξ ρ ρ' hξ hρ
    cases ht.kinded hΓ with
    | all hA =>
      rw [Con.interp_substOne hA hC hξ]
      exact ih hΓ ξ ρ ρ' hξ hρ _
  | tappConv ht hC =>
    intro ξ ρ ρ' hξ hρ
    have := Typed.sound (Typed.tapp ht hC.kinded_left) hΓ ξ ρ ρ' hξ hρ
    simpa only [Tm.erase] using this
  | tlam _ ih =>
    intro ξ ρ ρ' hξ hρ X
    exact ih (ctx_shift_kinded hΓ) _ ρ ρ' (hξ.cons X) (hρ.shift X)
  | conv _ hAB ih =>
    intro ξ ρ ρ' hξ hρ
    rw [← ConEq.sound hAB hξ]
    exact ih hΓ ξ ρ ρ' hξ hρ

/-! ## System F as the kind-`*` fragment -/

/-- System F types as Fω constructors of kind `*`. -/
def ofF : SystemF.Ty → Con
  | .var n => .var n
  | .arr A B => .arr (ofF A) (ofF B)
  | .all A => .all .star (ofF A)

/-- System F terms as Fω terms. -/
def ofFTm : SystemF.Tm → Tm
  | .var n => .var n
  | .app t u => .app (ofFTm t) (ofFTm u)
  | .lam A t => .lam (ofF A) (ofFTm t)
  | .tapp t A => .tapp (ofFTm t) (ofF A)
  | .tlam t => .tlam .star (ofFTm t)

theorem erase_ofFTm (t : SystemF.Tm) : (ofFTm t).erase = t.erase := by
  induction t with
  | var _ => rfl
  | app _ _ iht ihu => simp only [ofFTm, Tm.erase, SystemF.Tm.erase, iht, ihu]
  | lam _ _ ih => simp only [ofFTm, Tm.erase, SystemF.Tm.erase, ih]
  | tapp _ _ ih => simp only [ofFTm, Tm.erase, SystemF.Tm.erase, ih]
  | tlam _ ih => simp only [ofFTm, Tm.erase, SystemF.Tm.erase, ih]

theorem ofF_rename (r : ℕ → ℕ) (A : SystemF.Ty) : ofF (A.rename r) = (ofF A).rename r := by
  induction A generalizing r with
  | var _ => rfl
  | arr _ _ ihA ihB => simp only [SystemF.Ty.rename, ofF, Con.rename, ihA, ihB]
  | all _ ih => simp only [SystemF.Ty.rename, ofF, Con.rename, ih]

theorem ofF_liftSub (σ : ℕ → SystemF.Ty) :
    ofF ∘ SystemF.Ty.liftSub σ = Con.liftSub (ofF ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact ofF_rename Nat.succ (σ n)

theorem ofF_subst (σ : ℕ → SystemF.Ty) (A : SystemF.Ty) :
    ofF (A.subst σ) = (ofF A).subst (ofF ∘ σ) := by
  induction A generalizing σ with
  | var _ => rfl
  | arr _ _ ihA ihB => simp only [SystemF.Ty.subst, ofF, Con.subst, ihA, ihB]
  | all _ ih => simp only [SystemF.Ty.subst, ofF, Con.subst, ih, ofF_liftSub]

theorem ofF_substOne (A B : SystemF.Ty) : ofF (A.substOne B) = (ofF A).substOne (ofF B) := by
  unfold SystemF.Ty.substOne Con.substOne
  rw [ofF_subst]
  congr 1
  funext n
  cases n <;> rfl

theorem map_ofF_shift (Γ : SystemF.Ctx) :
    (Γ.map ofF).map (Con.rename Nat.succ) = (Γ.map (SystemF.Ty.rename Nat.succ)).map ofF := by
  simp only [List.map_map]
  congr 1
  funext B
  exact (ofF_rename Nat.succ B).symm

theorem freeIn_rename_F {B : SystemF.Ty} {r : ℕ → ℕ} {m : ℕ} (h : (B.rename r).FreeIn m) :
    ∃ j, B.FreeIn j ∧ m = r j := by
  induction B generalizing r m with
  | var n => exact ⟨n, rfl, h⟩
  | arr _ _ ihA ihB =>
    rcases h with h | h
    · obtain ⟨j, hj, e⟩ := ihA h; exact ⟨j, Or.inl hj, e⟩
    · obtain ⟨j, hj, e⟩ := ihB h; exact ⟨j, Or.inr hj, e⟩
  | all _ ih =>
    obtain ⟨j, hj, e⟩ := ih (r := scons 0 (Nat.succ ∘ r)) (m := m + 1) h
    cases j with
    | zero => simp at e
    | succ j => exact ⟨j, hj, by simpa using e⟩

theorem kinded_ofF (A : SystemF.Ty) (n : ℕ) (h : ∀ m, A.FreeIn m → m < n) :
    Kinded (List.replicate n .star) (ofF A) .star := by
  induction A generalizing n with
  | var m => exact .var (by simp [h m rfl])
  | arr _ _ ihA ihB =>
    exact .arr (ihA n fun m hm => h m (Or.inl hm)) (ihB n fun m hm => h m (Or.inr hm))
  | all _ ih =>
    refine .all (ih (n + 1) fun m hm => ?_)
    cases m with
    | zero => omega
    | succ m => have := h m hm; omega

/-- System F typing embeds, given enough kind-`*` variables for the free type
variables of the context and the annotations. -/
theorem typed_ofF (h : SystemF.Typed Γ t A) (n : ℕ)
    (hΓ : ∀ B ∈ Γ, ∀ m, B.FreeIn m → m < n) (ht : ∀ m, t.TyFreeIn m → m < n) :
    Typed (List.replicate n .star) (Γ.map ofF) (ofFTm t) (ofF A) := by
  induction h generalizing n with
  | var hn => exact .var (by simp [hn])
  | app _ _ ih1 ih2 =>
    exact .app (ih1 (n := n) (hΓ := hΓ) (ht := fun m hm => ht m (Or.inl hm)))
      (ih2 (n := n) (hΓ := hΓ) (ht := fun m hm => ht m (Or.inr hm)))
  | lam _ ih =>
    refine .lam (kinded_ofF _ n fun m hm => ht m (Or.inl hm)) ?_
    exact ih (n := n)
      (hΓ := fun C hC => by
        rcases List.mem_cons.mp hC with rfl | hC
        exacts [fun m hm => ht m (Or.inl hm), hΓ C hC])
      (ht := fun m hm => ht m (Or.inr hm))
  | tlam _ ih =>
    have h1 := ih (n := n + 1)
      (hΓ := fun B hB m hm => by
        obtain ⟨B0, hB0, rfl⟩ := List.mem_map.mp hB
        obtain ⟨j, hj, rfl⟩ := freeIn_rename_F hm
        exact Nat.succ_lt_succ (hΓ B0 hB0 j hj))
      (ht := fun m hm => by
        cases m with
        | zero => omega
        | succ m => exact Nat.succ_lt_succ (ht m hm))
    refine Typed.tlam ?_
    rw [map_ofF_shift]
    exact h1
  | tapp _ ih =>
    rw [ofF_substOne]
    exact Typed.tapp (ih (n := n) (hΓ := hΓ) (ht := fun m hm => ht m (Or.inl hm)))
      (kinded_ofF _ n fun m hm => ht m (Or.inr hm))

/-- The two PER interpretations agree on System F types. -/
theorem interp_ofF (A : SystemF.Ty) (η : ℕ → PER M.D) :
    (ofF A).interp M (fun n => ⟨.star, η n⟩) .star = A.interp M η := by
  induction A generalizing η with
  | var n =>
    show (Con.var n).interp M (fun n => ⟨.star, η n⟩) .star = η n
    exact interp_var_of_eq rfl
  | arr _ _ ihA ihB =>
    show PER.arrow M _ _ = PER.arrow M _ _
    rw [ihA, ihB]
  | all A ih =>
    show PER.iInf (fun X : PER M.D =>
        (ofF A).interp M (scons ⟨.star, X⟩ fun n => ⟨.star, η n⟩) .star) =
      PER.iInf (fun X : PER M.D => A.interp M (scons X η))
    refine congrArg PER.iInf (funext fun X => ?_)
    show (ofF A).interp M (scons ⟨.star, X⟩ fun n => ⟨.star, η n⟩) .star = A.interp M (scons X η)
    have e : scons (⟨.star, X⟩ : SemEntry M.D) (fun n => ⟨.star, η n⟩) =
        fun n => ⟨.star, scons X η n⟩ := by
      funext n; cases n <;> rfl
    rw [e]
    exact ih _

end Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega
