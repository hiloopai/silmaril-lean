module

public import Silmaril.Calculi.LambdaCube.PER.SystemFOmega
public import Silmaril.Calculi.LambdaCube.Semantics
public import Silmaril.Calculi.LambdaCube.PTSMetatheory

@[expose] public section

set_option autoImplicit true

/-! # PER models as models of the cube institutions

The cube (`LambdaCube.PTS`) uses one pseudo-term syntax with *mixed* de Bruijn
contexts: type and term variables share one index space. System F and Fω here
keep the two scopes apart. A `Layout` records the interleaving of binders
(innermost first, `true` for a type binder); a telescope `Tele` is a mixed
context from which both the separated contexts and the PTS context are read.

* `Typed.toPTS`: F typing embeds in the λ2 corner. For Fω only the β-only
  typing `TypedB` embeds in the λω corner (`TypedB.toPTS`): the cube's
  `Pseudo.Conv` has no η, and `Typed.toPTS_false` refutes the embedding of the
  βη typing `Typed` (witness `x : H F` typed at `H (λα. F α)`).
* `reflect`: every λ2 (λω) PTS typing over an encoded context, at a type of
  sort `*`, is the encoding of a separated-syntax typing (generation lemmas;
  needs Church–Rosser and subject reduction for `Pseudo.Conv`).
* `conv_reflect`: untyped β-conversion between encodings of typed terms is
  derivable typed equality. For Fω the β-only version is `conv_reflectB`; it
  needs `TmEq.tappConv` (type arguments change up to `ConEq`), since
  `Pseudo.Conv` reduces inside type arguments. The βη version
  `SystemFOmega.conv_reflect` is in `PER/OmegaConvReflect.lean`.
* `systemFSemantics`, `systemFOmegaSemantics`: the PER models over arbitrary
  total combinatory algebras, as `Semantics Corner.systemF` and
  `Semantics Corner.systemFOmega`, hence single-signature institutions
  (`Semantics.inst`). Models form the discrete category on combinatory
  algebras. A sentence holds when *every* decoding of it (with type variables
  bounded by the telescope, which makes decodings unique) is semantically valid
  (`Valid`, `ValidEq`), without assuming the decoded judgment is typed.
  Judgments with no bounded decoding satisfy this clause vacuously. Soundness goes through
  `reflect` (the decoding is typed), uniqueness of decodings, `Typed.sound`, and
  for equations `conv_reflect` (`conv_reflectB` for Fω) and `TmEq.sound`.
-/

namespace Silmaril.Calculi.LambdaCube.PERModel

open CategoryTheory
open Silmaril.Logic.Institution

/-- Binder interleaving, innermost first: `true` = type binder, `false` = term binder. -/
abbrev Layout := List Bool

namespace Layout

/-- Mixed index of the `j`-th type variable. Indices beyond the layout keep counting. -/
def tyIdx : Layout → ℕ → ℕ
  | [], j => j
  | true :: _, 0 => 0
  | true :: L, j + 1 => tyIdx L j + 1
  | false :: L, j => tyIdx L j + 1

/-- Mixed index of the `i`-th term variable. -/
def tmIdx : Layout → ℕ → ℕ
  | [], i => i
  | false :: _, 0 => 0
  | false :: L, i + 1 => tmIdx L i + 1
  | true :: L, i => tmIdx L i + 1


theorem tyIdx_inj : ∀ (L : Layout) (j j' : ℕ), L.tyIdx j = L.tyIdx j' → j = j'
  | [], _, _, h => h
  | true :: _, 0, 0, _ => rfl
  | true :: _, 0, _ + 1, h => by simp [tyIdx] at h
  | true :: _, _ + 1, 0, h => by simp [tyIdx] at h
  | true :: L, j + 1, j' + 1, h => by
    simp only [tyIdx, Nat.add_right_cancel_iff] at h
    rw [tyIdx_inj L j j' h]
  | false :: L, j, j', h => by
    simp only [tyIdx, Nat.add_right_cancel_iff] at h
    exact tyIdx_inj L j j' h

theorem tmIdx_inj : ∀ (L : Layout) (i i' : ℕ), L.tmIdx i = L.tmIdx i' → i = i'
  | [], _, _, h => h
  | false :: _, 0, 0, _ => rfl
  | false :: _, 0, _ + 1, h => by simp [tmIdx] at h
  | false :: _, _ + 1, 0, h => by simp [tmIdx] at h
  | false :: L, i + 1, i' + 1, h => by
    simp only [tmIdx, Nat.add_right_cancel_iff] at h
    rw [tmIdx_inj L i i' h]
  | true :: L, i, i', h => by
    simp only [tmIdx, Nat.add_right_cancel_iff] at h
    exact tmIdx_inj L i i' h

theorem count_false (L : Layout) : (false :: L).count true = L.count true := by simp

theorem count_true (L : Layout) : (true :: L).count true = L.count true + 1 := by simp

/-- A bound type variable never shares its mixed index with a term variable. -/
theorem tmIdx_ne_tyIdx : ∀ (L : Layout) (i j : ℕ), j < L.count true → L.tmIdx i ≠ L.tyIdx j
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | true :: L, i, 0, _ => by simp [tmIdx, tyIdx]
  | true :: L, i, j + 1, h => by
    rw [count_true] at h
    simp only [tmIdx, tyIdx, ne_eq, Nat.add_right_cancel_iff]
    exact tmIdx_ne_tyIdx L i j (by omega)
  | false :: L, 0, j, _ => by simp [tmIdx, tyIdx]
  | false :: L, i + 1, j, h => by
    rw [count_false] at h
    simp only [tmIdx, tyIdx, ne_eq, Nat.add_right_cancel_iff]
    exact tmIdx_ne_tyIdx L i j h

end Layout

/-! ## System F in the λ2 corner -/

namespace SystemF

open SystemF

/-- Encoding of F types as pseudo-terms. -/
def Ty.toPseudo : Layout → Ty → Pseudo CubeSort
  | L, .var j => .var (L.tyIdx j)
  | L, .arr A B => .pi (Ty.toPseudo L A) (Ty.toPseudo (false :: L) B)
  | L, .all A => .pi (.sort .star) (Ty.toPseudo (true :: L) A)

/-- Encoding of F terms as pseudo-terms. -/
def Tm.toPseudo : Layout → Tm → Pseudo CubeSort
  | L, .var i => .var (L.tmIdx i)
  | L, .app t u => .app (Tm.toPseudo L t) (Tm.toPseudo L u)
  | L, .lam A t => .lam (A.toPseudo L) (Tm.toPseudo (false :: L) t)
  | L, .tapp t A => .app (Tm.toPseudo L t) (A.toPseudo L)
  | L, .tlam t => .lam (.sort .star) (Tm.toPseudo (true :: L) t)

/-- Mixed context entries; a term entry's type is relative to the older tail. -/
inductive Entry where
  | ty
  | tm (A : Ty)

/-- Mixed telescopes, innermost first. -/
abbrev Tele := List Entry

namespace Tele

def layout : Tele → Layout
  | [] => []
  | .ty :: T => true :: layout T
  | .tm _ :: T => false :: layout T

def numTy : Tele → ℕ
  | [] => 0
  | .ty :: T => numTy T + 1
  | .tm _ :: T => numTy T

/-- The separated term context. -/
def ctx : Tele → Ctx
  | [] => []
  | .ty :: T => (ctx T).map (Ty.rename Nat.succ)
  | .tm A :: T => A :: ctx T

/-- The PTS context. -/
def toPseudo : Tele → List (Pseudo CubeSort)
  | [] => []
  | .ty :: T => .sort .star :: toPseudo T
  | .tm A :: T => A.toPseudo (layout T) :: toPseudo T

/-- Every entry's type only uses type variables bound earlier in the telescope. -/
def WF : Tele → Prop
  | [] => True
  | .ty :: T => WF T
  | .tm A :: T => (∀ m, A.FreeIn m → m < numTy T) ∧ WF T

end Tele

/-! ### Encoding lemmas -/

local notation "HF" => HasType Corner.systemF.specification

theorem Ty.rename_eq_self (A : Ty) : ∀ r : ℕ → ℕ, (∀ n, r n = n) → A.rename r = A := by
  induction A with
  | var n => intro r h; simp [Ty.rename, h]
  | arr A B ihA ihB => intro r h; simp [Ty.rename, ihA r h, ihB r h]
  | all A ih =>
    intro r h
    simp only [Ty.rename]
    rw [ih (scons 0 (Nat.succ ∘ r)) (fun n => by cases n <;> simp [h])]

theorem Ty.subst_eq_self (A : Ty) : ∀ σ : ℕ → Ty, (∀ n, σ n = .var n) → A.subst σ = A := by
  induction A with
  | var n => intro σ h; simp [Ty.subst, h]
  | arr A B ihA ihB => intro σ h; simp [Ty.subst, ihA σ h, ihB σ h]
  | all A ih =>
    intro σ h
    simp only [Ty.subst]
    rw [ih (Ty.liftSub σ) (fun n => by cases n <;> simp [Ty.liftSub, h, Ty.rename])]

theorem Ty.toPseudo_rename (A : Ty) : ∀ (L L' : Layout) (r ρ : ℕ → ℕ),
    (∀ j, L'.tyIdx (r j) = ρ (L.tyIdx j)) →
    (A.rename r).toPseudo L' = (A.toPseudo L).rename ρ := by
  induction A with
  | var j => intro L L' r ρ h; simp [Ty.rename, Ty.toPseudo, Pseudo.rename, h]
  | arr A B ihA ihB =>
    intro L L' r ρ h
    simp only [Ty.rename, Ty.toPseudo, Pseudo.rename]
    rw [ihA L L' r ρ h, ihB (false :: L) (false :: L') r (DeBruijn.lift ρ)
      (fun j => by simp [Layout.tyIdx, h, DeBruijn.lift])]
  | all A ih =>
    intro L L' r ρ h
    simp only [Ty.rename, Ty.toPseudo, Pseudo.rename]
    rw [ih (true :: L) (true :: L') (scons 0 (Nat.succ ∘ r)) (DeBruijn.lift ρ)
      (fun j => by cases j <;> simp [Layout.tyIdx, h, DeBruijn.lift])]

theorem Ty.toPseudo_succ_false (A : Ty) (L : Layout) :
    A.toPseudo (false :: L) = (A.toPseudo L).rename Nat.succ := by
  have := A.toPseudo_rename L (false :: L) id Nat.succ (fun j => by simp [Layout.tyIdx])
  rwa [A.rename_eq_self id (fun _ => rfl)] at this

theorem Ty.toPseudo_rename_succ_true (A : Ty) (L : Layout) :
    (A.rename Nat.succ).toPseudo (true :: L) = (A.toPseudo L).rename Nat.succ :=
  A.toPseudo_rename L (true :: L) Nat.succ Nat.succ (fun j => by simp [Layout.tyIdx])

theorem Ty.toPseudo_subst (A : Ty) : ∀ (L L' : Layout) (σ : ℕ → Ty)
    (τ : ℕ → Pseudo CubeSort), (∀ j, (σ j).toPseudo L' = τ (L.tyIdx j)) →
    (A.subst σ).toPseudo L' = (A.toPseudo L).subst τ := by
  induction A with
  | var j => intro L L' σ τ h; simp [Ty.subst, Ty.toPseudo, Pseudo.subst, h]
  | arr A B ihA ihB =>
    intro L L' σ τ h
    simp only [Ty.subst, Ty.toPseudo, Pseudo.subst]
    rw [ihA L L' σ τ h, ihB (false :: L) (false :: L') σ (Pseudo.liftSub τ)
      (fun j => by simp [Layout.tyIdx, Pseudo.liftSub, Ty.toPseudo_succ_false, h])]
  | all A ih =>
    intro L L' σ τ h
    simp only [Ty.subst, Ty.toPseudo, Pseudo.subst]
    rw [ih (true :: L) (true :: L') (Ty.liftSub σ) (Pseudo.liftSub τ) (fun j => by
      cases j with
      | zero => simp [Ty.liftSub, Layout.tyIdx, Ty.toPseudo, Pseudo.liftSub]
      | succ j =>
        simp [Ty.liftSub, Layout.tyIdx, Pseudo.liftSub, Ty.toPseudo_rename_succ_true, h])]

theorem Ty.toPseudo_substOne (A B : Ty) (L : Layout) :
    (A.substOne B).toPseudo L = (A.toPseudo (true :: L)).substOne (B.toPseudo L) :=
  A.toPseudo_subst (true :: L) L (scons B Ty.var) (fun | 0 => B.toPseudo L | n + 1 => .var n)
    (fun j => by cases j <;> simp [Layout.tyIdx, Ty.toPseudo])

theorem Ty.toPseudo_false_substOne (A : Ty) (L : Layout) (a : Pseudo CubeSort) :
    (A.toPseudo (false :: L)).substOne a = A.toPseudo L := by
  have := A.toPseudo_subst (false :: L) L Ty.var (fun | 0 => a | n + 1 => .var n)
    (fun j => by simp [Layout.tyIdx, Ty.toPseudo])
  rw [A.subst_eq_self Ty.var (fun _ => rfl)] at this
  exact this.symm

theorem Ty.freeIn_rename (A : Ty) : ∀ (r : ℕ → ℕ) m, (A.rename r).FreeIn m →
    ∃ j, A.FreeIn j ∧ m = r j := by
  induction A with
  | var n => intro r m h; exact ⟨n, rfl, h⟩
  | arr A B ihA ihB =>
    intro r m h
    simp only [Ty.rename, Ty.FreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := ihA r m h; exact ⟨j, Or.inl hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ihB r m h; exact ⟨j, Or.inr hj, rfl⟩
  | all A ih =>
    intro r m h
    simp only [Ty.rename, Ty.FreeIn] at h
    obtain ⟨j, hj, he⟩ := ih (scons 0 (Nat.succ ∘ r)) (m + 1) h
    cases j with
    | zero => simp at he
    | succ j => exact ⟨j, hj, by simp at he; omega⟩

theorem Ty.freeIn_subst (A : Ty) : ∀ (σ : ℕ → Ty) m, (A.subst σ).FreeIn m →
    ∃ j, A.FreeIn j ∧ (σ j).FreeIn m := by
  induction A with
  | var n => intro σ m h; exact ⟨n, rfl, h⟩
  | arr A B ihA ihB =>
    intro σ m h
    simp only [Ty.subst, Ty.FreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, h'⟩ := ihA σ m h; exact ⟨j, Or.inl hj, h'⟩
    · obtain ⟨j, hj, h'⟩ := ihB σ m h; exact ⟨j, Or.inr hj, h'⟩
  | all A ih =>
    intro σ m h
    simp only [Ty.subst, Ty.FreeIn] at h
    obtain ⟨j, hj, h'⟩ := ih (Ty.liftSub σ) (m + 1) h
    cases j with
    | zero => simp [Ty.liftSub, Ty.FreeIn] at h'
    | succ j =>
      simp only [Ty.liftSub, scons_succ] at h'
      obtain ⟨i, hi, he⟩ := (σ j).freeIn_rename _ _ h'
      exact ⟨j, hj, by rw [show m = i by simp at he; omega]; exact hi⟩

theorem Ty.bnd_substOne {A B : Ty} {n : ℕ} (hA : ∀ m, (Ty.all A).FreeIn m → m < n)
    (hB : ∀ m, B.FreeIn m → m < n) : ∀ m, (A.substOne B).FreeIn m → m < n := by
  intro m hm
  obtain ⟨j, hj, hm'⟩ := A.freeIn_subst _ m hm
  cases j with
  | zero => exact hB m hm'
  | succ j =>
    have : m = j := hm'
    subst this
    exact hA m hj

/-- Encodings of F types contain no β-redex. -/
theorem Ty.noRedex_toPseudo (A : Ty) : ∀ L : Layout, (A.toPseudo L).NoRedex := by
  induction A with
  | var j => intro L; trivial
  | arr A B ihA ihB => intro L; exact ⟨ihA L, ihB _⟩
  | all A ih => intro L; exact ⟨trivial, ih _⟩

/-- Convertible encodings of F types are equal (Church–Rosser). -/
theorem Ty.toPseudo_eq_of_conv {A B : Ty} {L : Layout}
    (h : Pseudo.Conv (A.toPseudo L) (B.toPseudo L)) : A.toPseudo L = B.toPseudo L :=
  h.eq_of_noRedex (A.noRedex_toPseudo L) (B.noRedex_toPseudo L)

/-- Encoded types bounded by the available type variables have sort `*`. -/
theorem Ty.toPseudo_wf (A : Ty) : ∀ (Γ : List (Pseudo CubeSort)) (L : Layout) (n : ℕ),
    HF Γ (.sort .star) (.sort .box) →
    (∀ j < n, HF Γ (.var (L.tyIdx j)) (.sort .star)) →
    (∀ m, A.FreeIn m → m < n) → HF Γ (A.toPseudo L) (.sort .star) := by
  induction A with
  | var j => intro Γ L n _ hv hb; exact hv j (hb j rfl)
  | arr A B ihA ihB =>
    intro Γ L n hΓ hv hb
    have hA := ihA Γ L n hΓ hv (fun m h => hb m (Or.inl h))
    have hB' := (ihB Γ L n hΓ hv (fun m h => hb m (Or.inr h))).weak hA
    erw [← Ty.toPseudo_succ_false] at hB'
    exact .pi hA hB' ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | all A ih =>
    intro Γ L n hΓ hv hb
    refine .pi hΓ (ih (.sort .star :: Γ) (true :: L) (n + 1) (hΓ.weak hΓ) ?_ ?_)
      ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · intro j hj
      cases j with
      | zero => exact .var hΓ
      | succ j => exact (hv j (by omega)).weak hΓ
    · intro m hm
      cases m with
      | zero => omega
      | succ m => exact Nat.succ_lt_succ (hb m hm)

theorem Tele.pts_valid : ∀ T : Tele, T.WF → HF T.toPseudo (.sort .star) (.sort .box) ∧
    ∀ j < T.numTy, HF T.toPseudo (.var (T.layout.tyIdx j)) (.sort .star)
  | [], _ => ⟨.start ⟨rfl, rfl⟩, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | .ty :: T, hT => by
    obtain ⟨h1, h2⟩ := Tele.pts_valid T hT
    refine ⟨h1.weak h1, fun j hj => ?_⟩
    cases j with
    | zero => exact .var h1
    | succ j => exact (h2 j (by simp only [Tele.numTy] at hj; omega)).weak h1
  | .tm B :: T, hT => by
    obtain ⟨hB, hT⟩ := hT
    obtain ⟨h1, h2⟩ := Tele.pts_valid T hT
    have hw := B.toPseudo_wf _ _ _ h1 h2 hB
    exact ⟨h1.weak hw, fun j hj => (h2 j hj).weak hw⟩

theorem Tele.pts_var : ∀ (T : Tele), T.WF → ∀ n A, T.ctx[n]? = some A →
    HF T.toPseudo (.var (T.layout.tmIdx n)) (A.toPseudo T.layout) ∧
      ∀ m, A.FreeIn m → m < T.numTy
  | [], _, n, A, h => by simp [Tele.ctx] at h
  | .ty :: T, hT, n, A, h => by
    simp [Tele.ctx] at h
    obtain ⟨A', hA', rfl⟩ := h
    obtain ⟨h1, h2⟩ := Tele.pts_var T hT n A' hA'
    refine ⟨?_, ?_⟩
    · have := h1.weak (Tele.pts_valid T hT).1
      erw [← Ty.toPseudo_rename_succ_true] at this
      exact this
    · intro m hm
      obtain ⟨j, hj, rfl⟩ := A'.freeIn_rename _ m hm
      exact Nat.succ_lt_succ (h2 j hj)
  | .tm B :: T, hT, 0, A, h => by
    obtain ⟨hB, hT⟩ := hT
    simp only [Tele.ctx, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have hw := B.toPseudo_wf _ _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2 hB
    refine ⟨?_, hB⟩
    have := HasType.var hw
    erw [← Ty.toPseudo_succ_false] at this
    exact this
  | .tm B :: T, hT, n + 1, A, h => by
    obtain ⟨hB, hT⟩ := hT
    simp only [Tele.ctx, List.getElem?_cons_succ] at h
    obtain ⟨h1, h2⟩ := Tele.pts_var T hT n A h
    have hw := B.toPseudo_wf _ _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2 hB
    have := h1.weak hw
    erw [← Ty.toPseudo_succ_false] at this
    exact ⟨this, h2⟩

theorem Typed.toPTS_aux (h : Typed Γ t A) : ∀ T : Tele, Γ = T.ctx → T.WF →
    (∀ m, t.TyFreeIn m → m < T.numTy) →
    HF T.toPseudo (t.toPseudo T.layout) (A.toPseudo T.layout) ∧
      ∀ m, A.FreeIn m → m < T.numTy := by
  induction h with
  | var hn =>
    intro T hΓ hT _
    subst hΓ
    exact Tele.pts_var T hT _ _ hn
  | app _ _ ih₁ ih₂ =>
    intro T hΓ hT ht
    obtain ⟨h₁, b₁⟩ := ih₁ T hΓ hT (fun m hm => ht m (Or.inl hm))
    obtain ⟨h₂, _⟩ := ih₂ T hΓ hT (fun m hm => ht m (Or.inr hm))
    simp only [Ty.toPseudo] at h₁
    have := HasType.app h₁ h₂
    erw [Ty.toPseudo_false_substOne] at this
    exact ⟨this, fun m hm => b₁ m (Or.inr hm)⟩
  | @lam A Γ t B _ ih =>
    intro T hΓ hT ht
    subst hΓ
    obtain ⟨h₁, b₁⟩ := ih (.tm A :: T) rfl ⟨fun m hm => ht m (Or.inl hm), hT⟩
      (fun m hm => ht m (Or.inr hm))
    have hb : ∀ m, (Ty.arr A B).FreeIn m → m < T.numTy := fun m hm =>
      Or.elim hm (fun hm => ht m (Or.inl hm)) (fun hm => b₁ m hm)
    exact ⟨.lam h₁ ((Ty.arr A B).toPseudo_wf _ _ _ (Tele.pts_valid T hT).1
      (Tele.pts_valid T hT).2 hb), hb⟩
  | @tlam t A Γ _ ih =>
    intro T hΓ hT ht
    subst hΓ
    obtain ⟨h₁, b₁⟩ := ih (.ty :: T) rfl hT (fun m hm => by
      cases m with
      | zero => exact Nat.zero_lt_succ _
      | succ m => exact Nat.succ_lt_succ (ht m hm))
    have hb : ∀ m, (Ty.all A).FreeIn m → m < T.numTy := fun m hm =>
      Nat.lt_of_succ_lt_succ (b₁ (m + 1) hm)
    exact ⟨.lam h₁ ((Ty.all A).toPseudo_wf _ _ _ (Tele.pts_valid T hT).1
      (Tele.pts_valid T hT).2 hb), hb⟩
  | @tapp Γ t A B _ ih =>
    intro T hΓ hT ht
    obtain ⟨h₁, b₁⟩ := ih T hΓ hT (fun m hm => ht m (Or.inl hm))
    have hB : ∀ m, B.FreeIn m → m < T.numTy := fun m hm => ht m (Or.inr hm)
    have hw := B.toPseudo_wf _ _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2 hB
    simp only [Ty.toPseudo] at h₁
    have := HasType.app h₁ hw
    erw [← Ty.toPseudo_substOne] at this
    exact ⟨this, Ty.bnd_substOne b₁ hB⟩

/-- F typing embeds in the λ2 corner of the cube. -/
theorem Typed.toPTS {T : Tele} (hT : T.WF) (h : Typed T.ctx t A)
    (ht : ∀ m, t.TyFreeIn m → m < T.numTy) :
    HasType Corner.systemF.specification T.toPseudo (t.toPseudo T.layout) (A.toPseudo T.layout) :=
  (Typed.toPTS_aux h T rfl hT ht).1

/-! ### Generation over encoded telescopes

`classify` is the generation lemma for λ2 derivations whose context is an
encoded telescope: every derivable `Γ ⊢ t : B` is `* : □`, the encoding of a
well-scoped F type at `*`, or the encoding of a typed F term whose type
encoding is convertible to `B`. The proof needs only Church–Rosser (F type
encodings are redex-free), not subject reduction. -/


theorem Tele.numTy_eq : ∀ T : Tele, T.numTy = T.layout.count true
  | [] => rfl
  | .ty :: T => by simp [Tele.numTy, Tele.layout, Tele.numTy_eq T]
  | .tm _ :: T => by simp [Tele.numTy, Tele.layout, Tele.numTy_eq T]

theorem Ty.toPseudo_ne_sort (A : Ty) (L : Layout) (s : CubeSort) :
    A.toPseudo L ≠ .sort s := by
  cases A <;> simp [Ty.toPseudo]

theorem Tm.toPseudo_ne_sort (t : Tm) (L : Layout) (s : CubeSort) :
    t.toPseudo L ≠ .sort s := by
  cases t <;> simp [Tm.toPseudo]

/-- Type encodings are injective at a fixed layout. -/
theorem Ty.toPseudo_inj (A : Ty) : ∀ (B : Ty) (L : Layout), A.toPseudo L = B.toPseudo L → A = B := by
  induction A with
  | var j =>
    intro B L h
    cases B <;> simp only [Ty.toPseudo, Pseudo.var.injEq, reduceCtorEq] at h
    rw [L.tyIdx_inj _ _ h]
  | arr A B ihA ihB =>
    intro C L h
    cases C <;> simp only [Ty.toPseudo, Pseudo.pi.injEq, reduceCtorEq] at h
    case arr A' B' => rw [ihA A' L h.1, ihB B' _ h.2]
    case all A' => exact absurd h.1 (A.toPseudo_ne_sort L _)
  | all A ih =>
    intro C L h
    cases C <;> simp only [Ty.toPseudo, Pseudo.pi.injEq, reduceCtorEq] at h
    case arr A' B' => exact absurd h.1.symm (A'.toPseudo_ne_sort L _)
    case all A' => rw [ih A' _ h.2]

theorem Tm.toPseudo_ne_ty (u : Tm) (A : Ty) (L : Layout)
    (hA : ∀ m, A.FreeIn m → m < L.count true) : u.toPseudo L ≠ A.toPseudo L := by
  intro h
  cases u <;> cases A <;> simp only [Tm.toPseudo, Ty.toPseudo, Pseudo.var.injEq,
    reduceCtorEq] at h
  exact L.tmIdx_ne_tyIdx _ _ (hA _ rfl) h

/-- Term encodings are injective on terms whose type variables are bound. -/
theorem Tm.toPseudo_inj_bnd (t : Tm) : ∀ (u : Tm) (L : Layout),
    (∀ m, t.TyFreeIn m → m < L.count true) → (∀ m, u.TyFreeIn m → m < L.count true) →
    t.toPseudo L = u.toPseudo L → t = u := by
  induction t with
  | var i =>
    intro u L _ _ h
    cases u <;> simp only [Tm.toPseudo, Pseudo.var.injEq, reduceCtorEq] at h
    rw [L.tmIdx_inj _ _ h]
  | app t u iht ihu =>
    intro v L ht hv h
    cases v <;> simp only [Tm.toPseudo, Pseudo.app.injEq, reduceCtorEq] at h
    case app t' u' =>
      rw [iht t' L (fun m hm => ht m (Or.inl hm)) (fun m hm => hv m (Or.inl hm)) h.1,
        ihu u' L (fun m hm => ht m (Or.inr hm)) (fun m hm => hv m (Or.inr hm)) h.2]
    case tapp t' A => exact absurd h.2 (u.toPseudo_ne_ty A L (fun m hm => hv m (Or.inr hm)))
  | lam A t ih =>
    intro v L ht hv h
    cases v <;> simp only [Tm.toPseudo, Pseudo.lam.injEq, reduceCtorEq] at h
    case lam A' t' =>
      rw [Ty.toPseudo_inj A A' L h.1, ih t' (false :: L)
        (fun m hm => by rw [Layout.count_false]; exact ht m (Or.inr hm))
        (fun m hm => by rw [Layout.count_false]; exact hv m (Or.inr hm)) h.2]
    case tlam t' => exact absurd h.1 (A.toPseudo_ne_sort L _)
  | tapp t A ih =>
    intro v L ht hv h
    cases v <;> simp only [Tm.toPseudo, Pseudo.app.injEq, reduceCtorEq] at h
    case app t' u' => exact absurd h.2.symm (u'.toPseudo_ne_ty A L (fun m hm => ht m (Or.inr hm)))
    case tapp t' A' =>
      rw [ih t' L (fun m hm => ht m (Or.inl hm)) (fun m hm => hv m (Or.inl hm)) h.1,
        Ty.toPseudo_inj A A' L h.2]
  | tlam t ih =>
    intro v L ht hv h
    cases v <;> simp only [Tm.toPseudo, Pseudo.lam.injEq, reduceCtorEq] at h
    case lam A' t' => exact absurd h.1.symm (A'.toPseudo_ne_sort L _)
    case tlam t' =>
      have hb : ∀ (s : Tm), (∀ m, (Tm.tlam s).TyFreeIn m → m < L.count true) →
          ∀ m, s.TyFreeIn m → m < (true :: L).count true := by
        intro s hs m hm
        rw [Layout.count_true]
        cases m with
        | zero => exact Nat.zero_lt_succ _
        | succ m => exact Nat.succ_lt_succ (hs m hm)
      rw [ih t' (true :: L) (hb t ht) (hb t' hv) h.2]

/-- Church-style F typing is unique. -/
theorem Typed.unique (h : Typed Γ t A) : ∀ {B}, Typed Γ t B → A = B := by
  induction h with
  | var hn =>
    intro B h'
    cases h' with
    | var hn' => rw [hn] at hn'; exact Option.some.inj hn'
  | app _ _ ih₁ _ =>
    intro B h'
    cases h' with
    | app h₁ _ => have e := ih₁ h₁; cases e; rfl
  | lam _ ih =>
    intro B h'
    cases h' with
    | lam h₁ => rw [ih h₁]
  | tlam _ ih =>
    intro B h'
    cases h' with
    | tlam h₁ => rw [ih h₁]
  | tapp _ ih =>
    intro B h'
    cases h' with
    | tapp h₁ => have e := ih h₁; cases e; rfl

/-- Term encodings are injective on typed terms, at any layout. -/
theorem Tm.toPseudo_inj_typed (h : Typed Γ t A) : ∀ {u B L}, Typed Γ u B →
    t.toPseudo L = u.toPseudo L → t = u := by
  induction h with
  | var _ =>
    intro u B L _ e
    cases u <;> simp only [Tm.toPseudo, Pseudo.var.injEq, reduceCtorEq] at e
    rw [L.tmIdx_inj _ _ e]
  | app h₁ _ ih₁ ih₂ =>
    intro u B L hu e
    cases hu with
    | var _ => simp [Tm.toPseudo] at e
    | lam _ => simp [Tm.toPseudo] at e
    | tlam _ => simp [Tm.toPseudo] at e
    | app k₁ k₂ =>
      simp only [Tm.toPseudo, Pseudo.app.injEq] at e
      rw [ih₁ k₁ e.1, ih₂ k₂ e.2]
    | tapp k₁ =>
      simp only [Tm.toPseudo, Pseudo.app.injEq] at e
      have e₁ := ih₁ k₁ e.1
      subst e₁
      cases h₁.unique k₁
  | lam _ ih =>
    intro u B L hu e
    cases hu with
    | var _ => simp [Tm.toPseudo] at e
    | app _ _ => simp [Tm.toPseudo] at e
    | tapp _ => simp [Tm.toPseudo] at e
    | tlam _ =>
      simp only [Tm.toPseudo, Pseudo.lam.injEq] at e
      exact absurd e.1 (Ty.toPseudo_ne_sort _ L _)
    | lam k =>
      simp only [Tm.toPseudo, Pseudo.lam.injEq] at e
      have e₁ := Ty.toPseudo_inj _ _ L e.1
      subst e₁
      rw [ih k e.2]
  | tlam _ ih =>
    intro u B L hu e
    cases hu with
    | var _ => simp [Tm.toPseudo] at e
    | app _ _ => simp [Tm.toPseudo] at e
    | tapp _ => simp [Tm.toPseudo] at e
    | lam _ =>
      simp only [Tm.toPseudo, Pseudo.lam.injEq] at e
      exact absurd e.1.symm (Ty.toPseudo_ne_sort _ L _)
    | tlam k =>
      simp only [Tm.toPseudo, Pseudo.lam.injEq] at e
      rw [ih k e.2]
  | tapp h₁ ih =>
    intro u B L hu e
    cases hu with
    | var _ => simp [Tm.toPseudo] at e
    | lam _ => simp [Tm.toPseudo] at e
    | tlam _ => simp [Tm.toPseudo] at e
    | app k₁ _ =>
      simp only [Tm.toPseudo, Pseudo.app.injEq] at e
      have e₁ := ih k₁ e.1
      subst e₁
      cases h₁.unique k₁
    | tapp k₁ =>
      simp only [Tm.toPseudo, Pseudo.app.injEq] at e
      rw [ih k₁ e.1, Ty.toPseudo_inj _ _ L e.2]

/-! ### Renaming and substitution for F syntax and its encoding -/

theorem Ty.rename_substOne (A B : Ty) (r : ℕ → ℕ) :
    (A.substOne B).rename r = (A.rename (scons 0 (Nat.succ ∘ r))).substOne (B.rename r) := by
  simp only [Ty.substOne, Ty.rename_subst, Ty.subst_rename]
  congr 1
  funext n
  cases n <;> rfl

theorem Tm.tyFreeIn_rename (t : Tm) : ∀ (r : ℕ → ℕ) m, (t.rename r).TyFreeIn m → t.TyFreeIn m := by
  induction t with
  | var n => intro r m h; simp [Tm.rename, Tm.TyFreeIn] at h
  | app t u iht ihu =>
    intro r m h
    simp only [Tm.rename, Tm.TyFreeIn] at h ⊢
    exact h.imp (iht r m) (ihu r m)
  | lam A t ih =>
    intro r m h
    simp only [Tm.rename, Tm.TyFreeIn] at h ⊢
    exact h.imp id (ih _ m)
  | tapp t A ih =>
    intro r m h
    simp only [Tm.rename, Tm.TyFreeIn] at h ⊢
    exact h.imp (ih r m) id
  | tlam t ih =>
    intro r m h
    simp only [Tm.rename, Tm.TyFreeIn] at h ⊢
    exact ih r (m + 1) h

theorem Tm.tyFreeIn_tyRename (t : Tm) : ∀ (r : ℕ → ℕ) m, (t.tyRename r).TyFreeIn m →
    ∃ j, t.TyFreeIn j ∧ m = r j := by
  induction t with
  | var n => intro r m h; simp [Tm.tyRename, Tm.TyFreeIn] at h
  | app t u iht ihu =>
    intro r m h
    simp only [Tm.tyRename, Tm.TyFreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := iht r m h; exact ⟨j, Or.inl hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ihu r m h; exact ⟨j, Or.inr hj, rfl⟩
  | lam A t ih =>
    intro r m h
    simp only [Tm.tyRename, Tm.TyFreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := A.freeIn_rename r m h; exact ⟨j, Or.inl hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ih r m h; exact ⟨j, Or.inr hj, rfl⟩
  | tapp t A ih =>
    intro r m h
    simp only [Tm.tyRename, Tm.TyFreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := ih r m h; exact ⟨j, Or.inl hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := A.freeIn_rename r m h; exact ⟨j, Or.inr hj, rfl⟩
  | tlam t ih =>
    intro r m h
    simp only [Tm.tyRename, Tm.TyFreeIn] at h
    obtain ⟨j, hj, he⟩ := ih (scons 0 (Nat.succ ∘ r)) (m + 1) h
    cases j with
    | zero => simp at he
    | succ j => exact ⟨j, hj, by simp at he; omega⟩

theorem Tm.toPseudo_rename (t : Tm) : ∀ (L L' : Layout) (r ρ : ℕ → ℕ),
    (∀ i, L'.tmIdx (r i) = ρ (L.tmIdx i)) → (∀ j, L'.tyIdx j = ρ (L.tyIdx j)) →
    (t.rename r).toPseudo L' = (t.toPseudo L).rename ρ := by
  induction t with
  | var i => intro L L' r ρ h _; simp [Tm.rename, Tm.toPseudo, Pseudo.rename, h]
  | app t u iht ihu =>
    intro L L' r ρ h h'
    simp only [Tm.rename, Tm.toPseudo, Pseudo.rename]
    rw [iht L L' r ρ h h', ihu L L' r ρ h h']
  | lam A t ih =>
    intro L L' r ρ h h'
    have hA : A.toPseudo L' = (A.toPseudo L).rename ρ := by
      have := A.toPseudo_rename L L' id ρ h'
      rwa [A.rename_eq_self id (fun _ => rfl)] at this
    simp only [Tm.rename, Tm.toPseudo, Pseudo.rename]
    rw [hA, ih (false :: L) (false :: L') (scons 0 (Nat.succ ∘ r)) (DeBruijn.lift ρ)
      (fun i => by cases i <;> simp [Layout.tmIdx, DeBruijn.lift, h])
      (fun j => by simp [Layout.tyIdx, DeBruijn.lift, h'])]
  | tapp t A ih =>
    intro L L' r ρ h h'
    have hA : A.toPseudo L' = (A.toPseudo L).rename ρ := by
      have := A.toPseudo_rename L L' id ρ h'
      rwa [A.rename_eq_self id (fun _ => rfl)] at this
    simp only [Tm.rename, Tm.toPseudo, Pseudo.rename]
    rw [hA, ih L L' r ρ h h']
  | tlam t ih =>
    intro L L' r ρ h h'
    simp only [Tm.rename, Tm.toPseudo, Pseudo.rename]
    rw [ih (true :: L) (true :: L') r (DeBruijn.lift ρ)
      (fun i => by simp [Layout.tmIdx, DeBruijn.lift, h])
      (fun j => by cases j <;> simp [Layout.tyIdx, DeBruijn.lift, h'])]

theorem Tm.toPseudo_tyRename (t : Tm) : ∀ (L L' : Layout) (r ρ : ℕ → ℕ),
    (∀ i, L'.tmIdx i = ρ (L.tmIdx i)) → (∀ j, L'.tyIdx (r j) = ρ (L.tyIdx j)) →
    (t.tyRename r).toPseudo L' = (t.toPseudo L).rename ρ := by
  induction t with
  | var i => intro L L' r ρ h _; simp [Tm.tyRename, Tm.toPseudo, Pseudo.rename, h]
  | app t u iht ihu =>
    intro L L' r ρ h h'
    simp only [Tm.tyRename, Tm.toPseudo, Pseudo.rename]
    rw [iht L L' r ρ h h', ihu L L' r ρ h h']
  | lam A t ih =>
    intro L L' r ρ h h'
    simp only [Tm.tyRename, Tm.toPseudo, Pseudo.rename]
    rw [A.toPseudo_rename L L' r ρ h', ih (false :: L) (false :: L') r (DeBruijn.lift ρ)
      (fun i => by cases i <;> simp [Layout.tmIdx, DeBruijn.lift, h])
      (fun j => by simp [Layout.tyIdx, DeBruijn.lift, h'])]
  | tapp t A ih =>
    intro L L' r ρ h h'
    simp only [Tm.tyRename, Tm.toPseudo, Pseudo.rename]
    rw [ih L L' r ρ h h', A.toPseudo_rename L L' r ρ h']
  | tlam t ih =>
    intro L L' r ρ h h'
    simp only [Tm.tyRename, Tm.toPseudo, Pseudo.rename]
    rw [ih (true :: L) (true :: L') (scons 0 (Nat.succ ∘ r)) (DeBruijn.lift ρ)
      (fun i => by simp [Layout.tmIdx, DeBruijn.lift, h])
      (fun j => by cases j <;> simp [Layout.tyIdx, DeBruijn.lift, h'])]

theorem Tm.toPseudo_rename_succ (t : Tm) (L : Layout) :
    (t.rename Nat.succ).toPseudo (false :: L) = (t.toPseudo L).rename Nat.succ :=
  t.toPseudo_rename L (false :: L) Nat.succ Nat.succ (fun _ => rfl) (fun _ => rfl)

theorem Tm.toPseudo_tyRename_succ (t : Tm) (L : Layout) :
    (t.tyRename Nat.succ).toPseudo (true :: L) = (t.toPseudo L).rename Nat.succ :=
  t.toPseudo_tyRename L (true :: L) Nat.succ Nat.succ (fun _ => rfl) (fun _ => rfl)

theorem Tm.toPseudo_tySubst (t : Tm) : ∀ (L L' : Layout) (σ : ℕ → Ty)
    (τ : ℕ → Pseudo CubeSort), (∀ j, (σ j).toPseudo L' = τ (L.tyIdx j)) →
    (∀ i, Pseudo.var (L'.tmIdx i) = τ (L.tmIdx i)) →
    (t.tySubst σ).toPseudo L' = (t.toPseudo L).subst τ := by
  induction t with
  | var i =>
    intro L L' σ τ _ h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    exact h' i
  | app t u iht ihu =>
    intro L L' σ τ h h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    rw [iht L L' σ τ h h', ihu L L' σ τ h h']
  | lam A t ih =>
    intro L L' σ τ h h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    rw [A.toPseudo_subst L L' σ τ h, ih (false :: L) (false :: L') σ (Pseudo.liftSub τ)
      (fun j => by simp [Layout.tyIdx, Pseudo.liftSub, Ty.toPseudo_succ_false, h])
      (fun i => by
        cases i with
        | zero => rfl
        | succ i =>
          simp only [Layout.tmIdx, Pseudo.liftSub]
          rw [← h' i]
          rfl)]
  | tapp t A ih =>
    intro L L' σ τ h h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    rw [ih L L' σ τ h h', A.toPseudo_subst L L' σ τ h]
  | tlam t ih =>
    intro L L' σ τ h h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    rw [ih (true :: L) (true :: L') (Ty.liftSub σ) (Pseudo.liftSub τ)
      (fun j => by
        cases j with
        | zero => simp [Ty.liftSub, Layout.tyIdx, Ty.toPseudo, Pseudo.liftSub]
        | succ j =>
          simp [Ty.liftSub, Layout.tyIdx, Pseudo.liftSub, Ty.toPseudo_rename_succ_true, h])
      (fun i => by
        simp only [Layout.tmIdx, Pseudo.liftSub]
        rw [← h' i]
        rfl)]

theorem Tm.toPseudo_subst (t : Tm) : ∀ (L L' : Layout) (σ : ℕ → Tm)
    (τ : ℕ → Pseudo CubeSort), (∀ i, (σ i).toPseudo L' = τ (L.tmIdx i)) →
    (∀ j, Pseudo.var (L'.tyIdx j) = τ (L.tyIdx j)) →
    (t.subst σ).toPseudo L' = (t.toPseudo L).subst τ := by
  induction t with
  | var i =>
    intro L L' σ τ h _
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    exact h i
  | app t u iht ihu =>
    intro L L' σ τ h h'
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    rw [iht L L' σ τ h h', ihu L L' σ τ h h']
  | lam A t ih =>
    intro L L' σ τ h h'
    have hA : A.toPseudo L' = (A.toPseudo L).subst τ := by
      have := A.toPseudo_subst L L' Ty.var τ h'
      rwa [A.subst_eq_self Ty.var (fun _ => rfl)] at this
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    rw [hA, ih (false :: L) (false :: L') (Tm.liftSub σ) (Pseudo.liftSub τ)
      (fun i => by
        cases i with
        | zero => simp [Tm.liftSub, Tm.toPseudo, Layout.tmIdx, Pseudo.liftSub]
        | succ i => simp [Tm.liftSub, Layout.tmIdx, Pseudo.liftSub, Tm.toPseudo_rename_succ, h])
      (fun j => by
        simp only [Layout.tyIdx, Pseudo.liftSub]
        rw [← h' j]
        rfl)]
  | tapp t A ih =>
    intro L L' σ τ h h'
    have hA : A.toPseudo L' = (A.toPseudo L).subst τ := by
      have := A.toPseudo_subst L L' Ty.var τ h'
      rwa [A.subst_eq_self Ty.var (fun _ => rfl)] at this
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    rw [ih L L' σ τ h h', hA]
  | tlam t ih =>
    intro L L' σ τ h h'
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    rw [ih (true :: L) (true :: L') (fun n => (σ n).tyRename Nat.succ) (Pseudo.liftSub τ)
      (fun i => by simp [Layout.tmIdx, Pseudo.liftSub, Tm.toPseudo_tyRename_succ, h])
      (fun j => by
        cases j with
        | zero => rfl
        | succ j =>
          simp only [Layout.tyIdx, Pseudo.liftSub]
          rw [← h' j]
          rfl)]

theorem Tm.toPseudo_substOne (b u : Tm) (L : Layout) :
    (b.substOne u).toPseudo L = (b.toPseudo (false :: L)).substOne (u.toPseudo L) :=
  b.toPseudo_subst (false :: L) L (scons u Tm.var)
    (fun | 0 => u.toPseudo L | n + 1 => .var n) (fun i => by cases i <;> rfl) (fun _ => rfl)

theorem Tm.toPseudo_tySubstOne (b : Tm) (B : Ty) (L : Layout) :
    (b.tySubstOne B).toPseudo L = (b.toPseudo (true :: L)).substOne (B.toPseudo L) :=
  b.toPseudo_tySubst (true :: L) L (scons B Ty.var)
    (fun | 0 => B.toPseudo L | n + 1 => .var n)
    (fun j => by cases j <;> simp [Layout.tyIdx, Ty.toPseudo]) (fun _ => rfl)

/-! ### Classification of λ2 derivations -/

/-- The three shapes of a λ2 judgment over an encoded telescope. -/
def PTSClass (T : Tele) (t B : Pseudo CubeSort) : Prop :=
  (t = .sort .star ∧ B = .sort .box) ∨
  (∃ A : Ty, A.toPseudo T.layout = t ∧ B = .sort .star ∧ ∀ m, A.FreeIn m → m < T.numTy) ∨
  (∃ (t' : Tm) (A : Ty), t'.toPseudo T.layout = t ∧ Pseudo.Conv B (A.toPseudo T.layout) ∧
    Typed T.ctx t' A ∧ (∀ m, t'.TyFreeIn m → m < T.numTy) ∧ ∀ m, A.FreeIn m → m < T.numTy)

theorem conv_sort_ty {s : CubeSort} {A : Ty} {L : Layout}
    (h : Pseudo.Conv (.sort s) (A.toPseudo L)) : False :=
  A.toPseudo_ne_sort L s (h.eq_of_noRedex trivial (A.noRedex_toPseudo L)).symm

/-- Generation for λ2 over encoded telescopes. -/
theorem classify (h : HF Γ t B) : ∀ T : Tele, T.WF → T.toPseudo = Γ → PTSClass T t B := by
  induction h with
  | start hax =>
    intro T _ _
    obtain ⟨rfl, rfl⟩ := hax
    exact Or.inl ⟨rfl, rfl⟩
  | var _ _ =>
    intro T hT hΓ
    cases T with
    | nil => cases hΓ
    | cons e T =>
      cases e with
      | ty =>
        injection hΓ with h1 h2
        subst h1 h2
        exact Or.inr (Or.inl ⟨.var 0, rfl, rfl, fun m (hm : m = 0) => by
          subst hm; exact Nat.succ_pos _⟩)
      | tm A0 =>
        injection hΓ with h1 h2
        subst h1 h2
        obtain ⟨hA0, _⟩ := hT
        exact Or.inr (Or.inr ⟨.var 0, A0, rfl,
          Pseudo.Conv.of_eq (Ty.toPseudo_succ_false A0 _).symm, .var rfl,
          fun _ h => h.elim, hA0⟩)
  | weak _ _ ih₁ _ =>
    intro T hT hΓ
    cases T with
    | nil => cases hΓ
    | cons e T =>
      cases e with
      | ty =>
        injection hΓ with h1 h2
        subst h1 h2
        rcases ih₁ T hT rfl with ⟨rfl, rfl⟩ | ⟨A, rfl, rfl, hb⟩ |
          ⟨t', A, rfl, hc, ht, hbt, hbA⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨A.rename Nat.succ, A.toPseudo_rename_succ_true _, rfl,
            fun m hm => by
              obtain ⟨j, hj, rfl⟩ := A.freeIn_rename _ m hm
              exact Nat.succ_lt_succ (hb j hj)⟩)
        · exact Or.inr (Or.inr ⟨t'.tyRename Nat.succ, A.rename Nat.succ,
            t'.toPseudo_tyRename_succ _,
            (hc.rename Nat.succ).trans_eq (A.toPseudo_rename_succ_true _).symm,
            ht.tyRename Nat.succ,
            fun m hm => by
              obtain ⟨j, hj, rfl⟩ := t'.tyFreeIn_tyRename _ m hm
              exact Nat.succ_lt_succ (hbt j hj),
            fun m hm => by
              obtain ⟨j, hj, rfl⟩ := A.freeIn_rename _ m hm
              exact Nat.succ_lt_succ (hbA j hj)⟩)
      | tm C0 =>
        injection hΓ with h1 h2
        subst h1 h2
        obtain ⟨_, hT⟩ := hT
        rcases ih₁ T hT rfl with ⟨rfl, rfl⟩ | ⟨A, rfl, rfl, hb⟩ |
          ⟨t', A, rfl, hc, ht, hbt, hbA⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨A, A.toPseudo_succ_false _, rfl, hb⟩)
        · exact Or.inr (Or.inr ⟨t'.rename Nat.succ, A, t'.toPseudo_rename_succ _,
            (hc.rename Nat.succ).trans_eq (A.toPseudo_succ_false _).symm,
            ht.rename (r := Nat.succ) (fun n B hn => by simpa [Tele.ctx] using hn),
            fun m hm => hbt m (t'.tyFreeIn_rename _ m hm), hbA⟩)
  | pi _ _ hr ih₁ ih₂ =>
    intro T hT hΓ
    subst hΓ
    obtain ⟨rfl, hr⟩ := hr
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ | ⟨_, _, hc⟩ | ⟨_, _, hc⟩
    · rcases ih₁ T hT rfl with ⟨_, h⟩ | ⟨A0, rfl, _, hbA⟩ | ⟨_, _, _, h, _⟩
      · cases h
      · rcases ih₂ (.tm A0 :: T) ⟨hbA, hT⟩ rfl with ⟨_, h⟩ | ⟨B0, rfl, _, hbB⟩ |
          ⟨_, _, _, h, _⟩
        · cases h
        · exact Or.inr (Or.inl ⟨.arr A0 B0, rfl, rfl, fun m hm => hm.elim (hbA m) (hbB m)⟩)
        · exact (conv_sort_ty h).elim
      · exact (conv_sort_ty h).elim
    · rcases ih₁ T hT rfl with ⟨rfl, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩
      · rcases ih₂ (.ty :: T) hT rfl with ⟨_, h⟩ | ⟨B0, rfl, _, hbB⟩ | ⟨_, _, _, h, _⟩
        · cases h
        · exact Or.inr (Or.inl ⟨.all B0, rfl, rfl,
            fun m hm => Nat.lt_of_succ_lt_succ (hbB (m + 1) hm)⟩)
        · exact (conv_sort_ty h).elim
      · cases h
      · exact (conv_sort_ty h).elim
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
  | lam _ _ ih₁ ih₂ =>
    intro T hT hΓ
    subst hΓ
    rcases ih₂ T hT rfl with ⟨h, _⟩ | ⟨F, hF, _, hbF⟩ | ⟨_, _, _, h, _⟩
    · cases h
    · cases F with
      | var j => cases hF
      | arr A0 B0 =>
        injection hF with e1 e2
        subst e1 e2
        rcases ih₁ (.tm A0 :: T) ⟨fun m hm => hbF m (Or.inl hm), hT⟩ rfl with
          ⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨b0, C0, rfl, hc, hty, hbb, hbC⟩
        · exact absurd h (B0.toPseudo_ne_sort _ _)
        · exact absurd h (B0.toPseudo_ne_sort _ _)
        · exact Or.inr (Or.inr ⟨.lam A0 b0, .arr A0 C0, rfl, Pseudo.Conv.pi (.refl _) hc,
            .lam hty, fun m hm => hm.elim (fun h => hbF m (Or.inl h)) (hbb m),
            fun m hm => hm.elim (fun h => hbF m (Or.inl h)) (hbC m)⟩)
      | all C0 =>
        injection hF with e1 e2
        subst e1 e2
        rcases ih₁ (.ty :: T) hT rfl with
          ⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨b0, D0, rfl, hc, hty, hbb, hbD⟩
        · exact absurd h (C0.toPseudo_ne_sort _ _)
        · exact absurd h (C0.toPseudo_ne_sort _ _)
        · exact Or.inr (Or.inr ⟨.tlam b0, .all D0, rfl, Pseudo.Conv.pi (.refl _) hc,
            .tlam hty, fun m hm => Nat.lt_of_succ_lt_succ (hbb (m + 1) hm),
            fun m hm => Nat.lt_of_succ_lt_succ (hbD (m + 1) hm)⟩)
    · exact (conv_sort_ty h).elim
  | app _ _ ih₁ ih₂ =>
    intro T hT hΓ
    subst hΓ
    rcases ih₁ T hT rfl with ⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨f0, F, rfl, hc, hf, hbf, hbF⟩
    · cases h
    · cases h
    · obtain ⟨X, Y, hXY, hA, hB⟩ := hc.pi_noRedex (F.noRedex_toPseudo _)
      cases F with
      | var j => cases hXY
      | arr A0 B0 =>
        injection hXY with e1 e2
        subst e1 e2
        rcases ih₂ T hT rfl with ⟨_, rfl⟩ | ⟨_, _, rfl, _⟩ | ⟨a0, A1, rfl, hc', ha, hba, _⟩
        · exact (conv_sort_ty hA).elim
        · exact (conv_sort_ty hA).elim
        · have e : A0 = A1 := Ty.toPseudo_inj _ _ _
            ((hA.symm.trans hc').eq_of_noRedex (A0.noRedex_toPseudo _) (A1.noRedex_toPseudo _))
          subst e
          exact Or.inr (Or.inr ⟨.app f0 a0, B0, rfl,
            (hB.substOne_left _).trans_eq (Ty.toPseudo_false_substOne B0 _ _),
            .app hf ha, fun m hm => hm.elim (hbf m) (hba m), fun m hm => hbF m (Or.inr hm)⟩)
      | all C0 =>
        injection hXY with e1 e2
        subst e1 e2
        rcases ih₂ T hT rfl with ⟨_, rfl⟩ | ⟨A2, rfl, rfl, hbA2⟩ | ⟨_, A1, _, hc', _, _, _⟩
        · cases hA.sort_inj
        · exact Or.inr (Or.inr ⟨.tapp f0 A2, C0.substOne A2, rfl,
            (hB.substOne_left _).trans_eq (Ty.toPseudo_substOne C0 A2 _).symm,
            .tapp hf, fun m hm => hm.elim (hbf m) (hbA2 m), Ty.bnd_substOne hbF hbA2⟩)
        · exact (conv_sort_ty (hA.symm.trans hc')).elim
  | conv _ hc _ ih₁ ih₃ =>
    intro T hT hΓ
    rcases ih₁ T hT hΓ with ⟨rfl, rfl⟩ | ⟨A0, rfl, rfl, hb⟩ | ⟨t', A', rfl, hc', ht, hbt, hbA⟩
    · rcases ih₃ T hT hΓ with ⟨rfl, _⟩ | ⟨B0, rfl, _, _⟩ | ⟨_, _, _, h, _⟩
      · cases hc.sort_inj
      · exact (conv_sort_ty hc).elim
      · exact (conv_sort_ty h).elim
    · rcases ih₃ T hT hΓ with ⟨rfl, _⟩ | ⟨B0, rfl, _, _⟩ | ⟨_, _, _, h, _⟩
      · exact Or.inr (Or.inl ⟨A0, rfl, rfl, hb⟩)
      · exact (conv_sort_ty hc).elim
      · exact (conv_sort_ty h).elim
    · exact Or.inr (Or.inr ⟨t', A', rfl, hc.symm.trans hc', ht, hbt, hbA⟩)

/-- A well-scoped decoding of a derivable λ2 typing is an F typing. -/
theorem typed_of_decode {T : Tele} (hT : T.WF)
    (h : HF T.toPseudo (t.toPseudo T.layout) (A.toPseudo T.layout))
    (ht : ∀ m, t.TyFreeIn m → m < T.numTy) : Typed T.ctx t A := by
  rcases classify h T hT rfl with ⟨e, _⟩ | ⟨_, _, e, _⟩ | ⟨t', A', e, hc, ht', hbt, _⟩
  · exact absurd e (t.toPseudo_ne_sort _ _)
  · exact absurd e (A.toPseudo_ne_sort _ _)
  · have e₁ : t' = t := Tm.toPseudo_inj_bnd t' t _
      (fun m hm => by rw [← Tele.numTy_eq]; exact hbt m hm)
      (fun m hm => by rw [← Tele.numTy_eq]; exact ht m hm) e
    subst e₁
    have e₂ : A = A' := Ty.toPseudo_inj A A' _ (Ty.toPseudo_eq_of_conv hc)
    subst e₂
    exact ht'

/-- Parallel reduction of the encoding of a typed term is typed equality. -/
theorem par_reflect (h : Pseudo.Par p v) : ∀ (t : Tm) (Γ : Ctx) (A : Ty) (L : Layout),
    t.toPseudo L = p → Typed Γ t A → ∃ t', t'.toPseudo L = v ∧ TmEq Γ t t' A := by
  induction h with
  | sort s => intro t Γ A L e _; exact absurd e (t.toPseudo_ne_sort _ _)
  | var n => intro t Γ A L e ht; exact ⟨t, e, .refl ht⟩
  | pi _ _ _ _ => intro t Γ A L e _; cases t <;> simp [Tm.toPseudo] at e
  | app _ ha ih₁ ih₂ =>
    intro t Γ A L e ht
    cases t with
    | app t₁ t₂ =>
      injection e with e₁ e₂
      cases ht with
      | app h₁ h₂ =>
        obtain ⟨t₁', r₁, q₁⟩ := ih₁ t₁ Γ _ L e₁ h₁
        obtain ⟨t₂', r₂, q₂⟩ := ih₂ t₂ Γ _ L e₂ h₂
        exact ⟨.app t₁' t₂', by subst r₁ r₂; rfl, .app q₁ q₂⟩
    | tapp t₁ B =>
      injection e with e₁ e₂
      subst e₂
      have e₃ := ha.eq_of_noRedex (B.noRedex_toPseudo L)
      subst e₃
      cases ht with
      | tapp h₁ =>
        obtain ⟨t₁', r₁, q₁⟩ := ih₁ t₁ Γ _ L e₁ h₁
        exact ⟨.tapp t₁' B, by subst r₁; rfl, .tapp q₁⟩
    | var _ => simp [Tm.toPseudo] at e
    | lam _ _ => simp [Tm.toPseudo] at e
    | tlam _ => simp [Tm.toPseudo] at e
  | lam hA _ _ ihb =>
    intro t Γ C L e ht
    cases t with
    | lam A0 b0 =>
      injection e with e₁ e₂
      subst e₁ e₂
      have e₃ := hA.eq_of_noRedex (A0.noRedex_toPseudo L)
      subst e₃
      cases ht with
      | lam h₁ =>
        obtain ⟨b0', r, q⟩ := ihb b0 _ _ (false :: L) rfl h₁
        exact ⟨.lam A0 b0', by subst r; rfl, .lam q⟩
    | tlam b0 =>
      injection e with e₁ e₂
      subst e₁ e₂
      have e₃ := hA.eq_of_noRedex trivial
      subst e₃
      cases ht with
      | tlam h₁ =>
        obtain ⟨b0', r, q⟩ := ihb b0 _ _ (true :: L) rfl h₁
        exact ⟨.tlam b0', by subst r; rfl, .tlam q⟩
    | var _ => simp [Tm.toPseudo] at e
    | app _ _ => simp [Tm.toPseudo] at e
    | tapp _ _ => simp [Tm.toPseudo] at e
  | beta _ _ ha ihb iha =>
    intro t Γ A L e ht
    cases t with
    | app t₁ t₂ =>
      injection e with e₁ e₂
      cases ht with
      | app h₁ h₂ =>
        cases t₁ with
        | lam A0 b0 =>
          injection e₁ with e₃ e₄
          cases h₁ with
          | lam h₁ =>
            obtain ⟨b0', r₁, q₁⟩ := ihb b0 _ _ (false :: L) e₄ h₁
            obtain ⟨t₂', r₂, q₂⟩ := iha t₂ _ _ L e₂ h₂
            subst r₁ r₂
            exact ⟨b0'.substOne t₂', Tm.toPseudo_substOne _ _ _,
              (TmEq.app (TmEq.lam q₁) q₂).trans (.beta q₁.typed_right q₂.typed_right)⟩
        | tlam _ => cases h₁
        | var _ => simp [Tm.toPseudo] at e₁
        | app _ _ => simp [Tm.toPseudo] at e₁
        | tapp _ _ => simp [Tm.toPseudo] at e₁
    | tapp t₁ B =>
      injection e with e₁ e₂
      subst e₂
      have e₅ := ha.eq_of_noRedex (B.noRedex_toPseudo L)
      subst e₅
      cases ht with
      | tapp h₁ =>
        cases t₁ with
        | tlam b0 =>
          injection e₁ with e₃ e₄
          cases h₁ with
          | tlam h₁ =>
            obtain ⟨b0', r₁, q₁⟩ := ihb b0 _ _ (true :: L) e₄ h₁
            subst r₁
            exact ⟨b0'.tySubstOne B, Tm.toPseudo_tySubstOne _ _ _,
              (TmEq.tapp (TmEq.tlam q₁)).trans (.tbeta q₁.typed_right)⟩
        | lam _ _ => cases h₁
        | var _ => simp [Tm.toPseudo] at e₁
        | app _ _ => simp [Tm.toPseudo] at e₁
        | tapp _ _ => simp [Tm.toPseudo] at e₁
    | var _ => simp [Tm.toPseudo] at e
    | lam _ _ => simp [Tm.toPseudo] at e
    | tlam _ => simp [Tm.toPseudo] at e

theorem reflTransGen_par_reflect {L : Layout}
    (h : Relation.ReflTransGen Pseudo.Par (t.toPseudo L) v) (ht : Typed Γ t A) :
    ∃ t', t'.toPseudo L = v ∧ TmEq Γ t t' A := by
  induction h with
  | refl => exact ⟨t, rfl, .refl ht⟩
  | tail _ hp ih =>
    obtain ⟨t', rfl, q⟩ := ih
    obtain ⟨t'', r, q'⟩ := par_reflect hp t' Γ A L rfl q.typed_right
    exact ⟨t'', r, q.trans q'⟩

/-- Reflection: λ2 PTS typings over encoded contexts at types of sort `*`
come from F typings. -/
theorem reflect {T : Tele} (hT : T.WF)
    (h : HasType Corner.systemF.specification T.toPseudo t B)
    (hB : HasType Corner.systemF.specification T.toPseudo B (.sort .star)) :
    ∃ t' A', t'.toPseudo T.layout = t ∧ A'.toPseudo T.layout = B ∧ Typed T.ctx t' A' ∧
      ∀ m, t'.TyFreeIn m → m < T.numTy := by
  rcases classify h T hT rfl with ⟨rfl, rfl⟩ | ⟨A, rfl, rfl, _⟩ |
    ⟨t', A', rfl, hc, ht, hbt, _⟩
  · rcases classify hB T hT rfl with ⟨e, _⟩ | ⟨A, e, _, _⟩ | ⟨t', _, e, _, _, _, _⟩
    · cases e
    · exact absurd e (A.toPseudo_ne_sort _ _)
    · exact absurd e (t'.toPseudo_ne_sort _ _)
  · rcases classify hB T hT rfl with ⟨_, e⟩ | ⟨A, e, _, _⟩ | ⟨t', _, e, _, _, _, _⟩
    · cases e
    · exact absurd e (A.toPseudo_ne_sort _ _)
    · exact absurd e (t'.toPseudo_ne_sort _ _)
  · rcases classify hB T hT rfl with ⟨rfl, _⟩ | ⟨B0, rfl, _, _⟩ | ⟨_, _, _, e, _, _, _⟩
    · exact (conv_sort_ty hc).elim
    · exact ⟨t', A', rfl, (Ty.toPseudo_eq_of_conv hc).symm, ht, hbt⟩
    · exact (conv_sort_ty e).elim

set_option linter.unusedVariables false in
/-- Untyped β-conversion between encodings of typed F terms is typed βη-equality.
The telescope and scoping hypotheses are redundant: encodings are injective on
typed terms (`Tm.toPseudo_inj_typed`), since F typing is unique. -/
theorem conv_reflect {T : Tele} (hT : T.WF) (ht : Typed T.ctx t A) (hu : Typed T.ctx u A)
    (hbt : ∀ m, t.TyFreeIn m → m < T.numTy) (hbu : ∀ m, u.TyFreeIn m → m < T.numTy)
    (h : Pseudo.Conv (t.toPseudo T.layout) (u.toPseudo T.layout)) :
    TmEq T.ctx t u A := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  obtain ⟨t', r₁, q₁⟩ := reflTransGen_par_reflect h₁ ht
  obtain ⟨u', r₂, q₂⟩ := reflTransGen_par_reflect h₂ hu
  have e : t' = u' := Tm.toPseudo_inj_typed q₁.typed_right q₂.typed_right (r₁.trans r₂.symm)
  subst e
  exact q₁.trans q₂.symm

/-- Satisfaction of PTS judgments in the PER model over `M`. -/
-- Quantify over raw bounded decodings; requiring typed decodings here would
-- make the typing clause follow immediately from Typed.sound.
def Sat (M : CombAlg.{0}) : PTSJudgment → Prop
  | .typing Γ t B => ∀ (T : Tele) (t' : Tm) (A : Ty), T.WF → T.toPseudo = Γ →
      t'.toPseudo T.layout = t → A.toPseudo T.layout = B →
      (∀ m, t'.TyFreeIn m → m < T.numTy) → Valid M T.ctx t' A
  | .equation Γ t u B => ∀ (T : Tele) (t' u' : Tm) (A : Ty), T.WF → T.toPseudo = Γ →
      t'.toPseudo T.layout = t → u'.toPseudo T.layout = u → A.toPseudo T.layout = B →
      (∀ m, t'.TyFreeIn m → m < T.numTy) → (∀ m, u'.TyFreeIn m → m < T.numTy) →
      ValidEq M T.ctx t' u' A

theorem sat_sound {j : PTSJudgment} (h : j.Derivable Corner.systemF) (M : CombAlg.{0}) :
    Sat M j := by
  cases j with
  | typing Γ t B =>
    simp only [Sat]
    intro T t' A hT hΓ ht hA hbt
    subst hΓ ht hA
    exact (typed_of_decode hT h hbt).sound
  | equation Γ t u B =>
    simp only [Sat]
    intro T t' u' A hT hΓ ht hu hA hbt hbu
    subst hΓ ht hu hA
    obtain ⟨h₁, h₂, hc⟩ := h
    exact (conv_reflect hT (typed_of_decode hT h₁ hbt) (typed_of_decode hT h₂ hbu)
      hbt hbu hc).sound

/-- The PER models of System F as semantics of the λ2 corner. -/
def systemFSemantics : SystemFSemantics where
  Model := Discrete CombAlg.{0}
  sat X j := Sat X.as j
  sound h X := sat_sound h X.as

end SystemF

/-! ## Fω in the λω corner -/

namespace SystemFOmega

/-- Encoding of kinds. Kinds are closed, so no shifting is needed. -/
def Kind.toPseudo : Kind → Pseudo CubeSort
  | .star => .sort .star
  | .arr k l => .pi (Kind.toPseudo k) (Kind.toPseudo l)

/-- Encoding of constructors. -/
def Con.toPseudo : Layout → Con → Pseudo CubeSort
  | L, .var j => .var (L.tyIdx j)
  | L, .arr A B => .pi (Con.toPseudo L A) (Con.toPseudo (false :: L) B)
  | L, .all k A => .pi k.toPseudo (Con.toPseudo (true :: L) A)
  | L, .lam k A => .lam k.toPseudo (Con.toPseudo (true :: L) A)
  | L, .app A B => .app (Con.toPseudo L A) (Con.toPseudo L B)

/-- Encoding of terms. -/
def Tm.toPseudo : Layout → Tm → Pseudo CubeSort
  | L, .var i => .var (L.tmIdx i)
  | L, .app t u => .app (Tm.toPseudo L t) (Tm.toPseudo L u)
  | L, .lam A t => .lam (A.toPseudo L) (Tm.toPseudo (false :: L) t)
  | L, .tapp t C => .app (Tm.toPseudo L t) (C.toPseudo L)
  | L, .tlam k t => .lam k.toPseudo (Tm.toPseudo (true :: L) t)

/-- Mixed context entries. -/
inductive Entry where
  | ty (k : Kind)
  | tm (A : Con)

/-- Mixed telescopes, innermost first. -/
abbrev Tele := List Entry

namespace Tele

def layout : Tele → Layout
  | [] => []
  | .ty _ :: T => true :: layout T
  | .tm _ :: T => false :: layout T

/-- The kind context. -/
def kctx : Tele → KCtx
  | [] => []
  | .ty k :: T => k :: kctx T
  | .tm _ :: T => kctx T

/-- The separated term context. -/
def ctx : Tele → Ctx
  | [] => []
  | .ty _ :: T => (ctx T).map (Con.rename Nat.succ)
  | .tm A :: T => A :: ctx T

def toPseudo : Tele → List (Pseudo CubeSort)
  | [] => []
  | .ty k :: T => k.toPseudo :: toPseudo T
  | .tm A :: T => A.toPseudo (layout T) :: toPseudo T

/-- Every term entry is a well-kinded type over the older tail. -/
def WF : Tele → Prop
  | [] => True
  | .ty _ :: T => WF T
  | .tm A :: T => Kinded (kctx T) A .star ∧ WF T

theorem WF.ctx_kinded {T : Tele} (h : T.WF) : ∀ B ∈ T.ctx, Kinded T.kctx B .star := by
  induction T with
  | nil => intro B hB; simp [ctx] at hB
  | cons e T ih =>
    cases e with
    | ty k =>
      intro B hB
      simp only [ctx, List.mem_map] at hB
      obtain ⟨B', hB', rfl⟩ := hB
      exact (ih h B' hB').rename (fun n k' hn => by simpa [kctx] using hn)
    | tm A =>
      obtain ⟨hA, hT⟩ := h
      intro B hB
      simp only [ctx, List.mem_cons] at hB
      rcases hB with rfl | hB
      · exact hA
      · exact ih hT B hB

end Tele

/-! ### Encoding lemmas -/

local notation "HW" => HasType Corner.systemFOmega.specification

theorem Kind.toPseudo_rename (k : Kind) : ∀ ρ : ℕ → ℕ, k.toPseudo.rename ρ = k.toPseudo := by
  induction k with
  | star => intro ρ; rfl
  | arr k l ihk ihl => intro ρ; simp only [Kind.toPseudo, Pseudo.rename, ihk, ihl]

theorem Kind.toPseudo_subst (k : Kind) :
    ∀ τ : ℕ → Pseudo CubeSort, k.toPseudo.subst τ = k.toPseudo := by
  induction k with
  | star => intro τ; rfl
  | arr k l ihk ihl => intro τ; simp only [Kind.toPseudo, Pseudo.subst, ihk, ihl]

theorem Kind.toPseudo_substOne (k : Kind) (a : Pseudo CubeSort) :
    k.toPseudo.substOne a = k.toPseudo :=
  k.toPseudo_subst _

theorem Con.rename_eq_self (A : Con) : ∀ r : ℕ → ℕ, (∀ n, r n = n) → A.rename r = A := by
  induction A with
  | var n => intro r h; simp [Con.rename, h]
  | arr A B ihA ihB => intro r h; simp [Con.rename, ihA r h, ihB r h]
  | all k A ih =>
    intro r h
    simp only [Con.rename]
    rw [ih (scons 0 (Nat.succ ∘ r)) (fun n => by cases n <;> simp [h])]
  | lam k A ih =>
    intro r h
    simp only [Con.rename]
    rw [ih (scons 0 (Nat.succ ∘ r)) (fun n => by cases n <;> simp [h])]
  | app A B ihA ihB => intro r h; simp [Con.rename, ihA r h, ihB r h]

theorem Con.subst_eq_self (A : Con) : ∀ σ : ℕ → Con, (∀ n, σ n = .var n) → A.subst σ = A := by
  induction A with
  | var n => intro σ h; simp [Con.subst, h]
  | arr A B ihA ihB => intro σ h; simp [Con.subst, ihA σ h, ihB σ h]
  | all k A ih =>
    intro σ h
    simp only [Con.subst]
    rw [ih (Con.liftSub σ) (fun n => by cases n <;> simp [Con.liftSub, h, Con.rename])]
  | lam k A ih =>
    intro σ h
    simp only [Con.subst]
    rw [ih (Con.liftSub σ) (fun n => by cases n <;> simp [Con.liftSub, h, Con.rename])]
  | app A B ihA ihB => intro σ h; simp [Con.subst, ihA σ h, ihB σ h]

theorem Con.toPseudo_rename (A : Con) : ∀ (L L' : Layout) (r ρ : ℕ → ℕ),
    (∀ j, L'.tyIdx (r j) = ρ (L.tyIdx j)) →
    (A.rename r).toPseudo L' = (A.toPseudo L).rename ρ := by
  induction A with
  | var j => intro L L' r ρ h; simp [Con.rename, Con.toPseudo, Pseudo.rename, h]
  | arr A B ihA ihB =>
    intro L L' r ρ h
    simp only [Con.rename, Con.toPseudo, Pseudo.rename]
    rw [ihA L L' r ρ h, ihB (false :: L) (false :: L') r (DeBruijn.lift ρ)
      (fun j => by simp [Layout.tyIdx, h, DeBruijn.lift])]
  | all k A ih =>
    intro L L' r ρ h
    simp only [Con.rename, Con.toPseudo, Pseudo.rename, Kind.toPseudo_rename]
    rw [ih (true :: L) (true :: L') (scons 0 (Nat.succ ∘ r)) (DeBruijn.lift ρ)
      (fun j => by cases j <;> simp [Layout.tyIdx, h, DeBruijn.lift])]
  | lam k A ih =>
    intro L L' r ρ h
    simp only [Con.rename, Con.toPseudo, Pseudo.rename, Kind.toPseudo_rename]
    rw [ih (true :: L) (true :: L') (scons 0 (Nat.succ ∘ r)) (DeBruijn.lift ρ)
      (fun j => by cases j <;> simp [Layout.tyIdx, h, DeBruijn.lift])]
  | app A B ihA ihB =>
    intro L L' r ρ h
    simp only [Con.rename, Con.toPseudo, Pseudo.rename]
    rw [ihA L L' r ρ h, ihB L L' r ρ h]

theorem Con.toPseudo_succ_false (A : Con) (L : Layout) :
    A.toPseudo (false :: L) = (A.toPseudo L).rename Nat.succ := by
  have := A.toPseudo_rename L (false :: L) id Nat.succ (fun j => by simp [Layout.tyIdx])
  rwa [A.rename_eq_self id (fun _ => rfl)] at this

theorem Con.toPseudo_rename_succ_true (A : Con) (L : Layout) :
    (A.rename Nat.succ).toPseudo (true :: L) = (A.toPseudo L).rename Nat.succ :=
  A.toPseudo_rename L (true :: L) Nat.succ Nat.succ (fun j => by simp [Layout.tyIdx])

theorem Con.toPseudo_subst (A : Con) : ∀ (L L' : Layout) (σ : ℕ → Con)
    (τ : ℕ → Pseudo CubeSort), (∀ j, (σ j).toPseudo L' = τ (L.tyIdx j)) →
    (A.subst σ).toPseudo L' = (A.toPseudo L).subst τ := by
  have lift : ∀ (L L' : Layout) (σ : ℕ → Con) (τ : ℕ → Pseudo CubeSort),
      (∀ j, (σ j).toPseudo L' = τ (L.tyIdx j)) →
      ∀ j, (Con.liftSub σ j).toPseudo (true :: L') =
        Pseudo.liftSub τ (Layout.tyIdx (true :: L) j) := by
    intro L L' σ τ h j
    cases j with
    | zero => simp [Con.liftSub, Layout.tyIdx, Con.toPseudo, Pseudo.liftSub]
    | succ j =>
      simp [Con.liftSub, Layout.tyIdx, Pseudo.liftSub, Con.toPseudo_rename_succ_true, h]
  induction A with
  | var j => intro L L' σ τ h; simp [Con.subst, Con.toPseudo, Pseudo.subst, h]
  | arr A B ihA ihB =>
    intro L L' σ τ h
    simp only [Con.subst, Con.toPseudo, Pseudo.subst]
    rw [ihA L L' σ τ h, ihB (false :: L) (false :: L') σ (Pseudo.liftSub τ)
      (fun j => by simp [Layout.tyIdx, Pseudo.liftSub, Con.toPseudo_succ_false, h])]
  | all k A ih =>
    intro L L' σ τ h
    simp only [Con.subst, Con.toPseudo, Pseudo.subst, Kind.toPseudo_subst]
    rw [ih (true :: L) (true :: L') (Con.liftSub σ) (Pseudo.liftSub τ) (lift L L' σ τ h)]
  | lam k A ih =>
    intro L L' σ τ h
    simp only [Con.subst, Con.toPseudo, Pseudo.subst, Kind.toPseudo_subst]
    rw [ih (true :: L) (true :: L') (Con.liftSub σ) (Pseudo.liftSub τ) (lift L L' σ τ h)]
  | app A B ihA ihB =>
    intro L L' σ τ h
    simp only [Con.subst, Con.toPseudo, Pseudo.subst]
    rw [ihA L L' σ τ h, ihB L L' σ τ h]

theorem Con.toPseudo_substOne (A B : Con) (L : Layout) :
    (A.substOne B).toPseudo L = (A.toPseudo (true :: L)).substOne (B.toPseudo L) :=
  A.toPseudo_subst (true :: L) L (scons B Con.var) (fun | 0 => B.toPseudo L | n + 1 => .var n)
    (fun j => by cases j <;> simp [Layout.tyIdx, Con.toPseudo])

theorem Con.toPseudo_false_substOne (A : Con) (L : Layout) (a : Pseudo CubeSort) :
    (A.toPseudo (false :: L)).substOne a = A.toPseudo L := by
  have := A.toPseudo_subst (false :: L) L Con.var (fun | 0 => a | n + 1 => .var n)
    (fun j => by simp [Layout.tyIdx, Con.toPseudo])
  rw [A.subst_eq_self Con.var (fun _ => rfl)] at this
  exact this.symm

/-- Encoded kinds have sort `□` in any context where `*` does. -/
theorem Kind.toPseudo_wf (k : Kind) : ∀ Γ : List (Pseudo CubeSort),
    HW Γ (.sort .star) (.sort .box) → HW Γ k.toPseudo (.sort .box) := by
  induction k with
  | star => intro Γ h; exact h
  | arr k l ihk ihl =>
    intro Γ h
    have hk := ihk Γ h
    exact .pi hk (ihl _ (h.weak hk)) ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩

theorem ext_ty_var {Γ : List (Pseudo CubeSort)} {L : Layout} {Δ : KCtx} {k : Kind}
    (hk : HW Γ k.toPseudo (.sort .box))
    (hv : ∀ j k', Δ[j]? = some k' → HW Γ (.var (L.tyIdx j)) k'.toPseudo) :
    ∀ j k', (k :: Δ)[j]? = some k' →
      HW (k.toPseudo :: Γ) (.var (Layout.tyIdx (true :: L) j)) k'.toPseudo := by
  intro j k' hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    have := HasType.var hk
    erw [Kind.toPseudo_rename] at this
    exact this
  | succ j =>
    simp only [List.getElem?_cons_succ] at hj
    have := (hv j k' hj).weak hk
    erw [Kind.toPseudo_rename] at this
    exact this

/-- Kinding embeds in the λω corner. -/
theorem Kinded.toPTS (h : Kinded Δ A k) : ∀ (Γ : List (Pseudo CubeSort)) (L : Layout),
    HW Γ (.sort .star) (.sort .box) →
    (∀ j k', Δ[j]? = some k' → HW Γ (.var (L.tyIdx j)) k'.toPseudo) →
    HW Γ (A.toPseudo L) k.toPseudo := by
  induction h with
  | var hn => intro Γ L _ hv; exact hv _ _ hn
  | arr _ _ ihA ihB =>
    intro Γ L hΓ hv
    have hA := ihA Γ L hΓ hv
    have hB' := (ihB Γ L hΓ hv).weak hA
    erw [← Con.toPseudo_succ_false] at hB'
    exact .pi hA hB' ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | @all k Δ A _ ih =>
    intro Γ L hΓ hv
    have hk := k.toPseudo_wf Γ hΓ
    exact .pi hk (ih (k.toPseudo :: Γ) (true :: L) (hΓ.weak hk) (ext_ty_var hk hv))
      ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  | @lam k Δ A l _ ih =>
    intro Γ L hΓ hv
    have hk := k.toPseudo_wf Γ hΓ
    exact .lam (ih (k.toPseudo :: Γ) (true :: L) (hΓ.weak hk) (ext_ty_var hk hv))
      ((Kind.arr k l).toPseudo_wf Γ hΓ)
  | app _ _ ihA ihB =>
    intro Γ L hΓ hv
    have := HasType.app (ihA Γ L hΓ hv) (ihB Γ L hΓ hv)
    erw [Kind.toPseudo_substOne] at this
    exact this

theorem Tele.pts_valid : ∀ T : Tele, T.WF → HW T.toPseudo (.sort .star) (.sort .box) ∧
    ∀ j k, T.kctx[j]? = some k → HW T.toPseudo (.var (T.layout.tyIdx j)) k.toPseudo
  | [], _ => ⟨.start ⟨rfl, rfl⟩, fun _ _ h => by simp [Tele.kctx] at h⟩
  | .ty k :: T, hT => by
    obtain ⟨h1, h2⟩ := Tele.pts_valid T hT
    have hk := k.toPseudo_wf _ h1
    exact ⟨h1.weak hk, ext_ty_var hk h2⟩
  | .tm B :: T, hT => by
    obtain ⟨hB, hT⟩ := hT
    obtain ⟨h1, h2⟩ := Tele.pts_valid T hT
    have hw := hB.toPTS _ _ h1 h2
    refine ⟨h1.weak hw, fun j k hj => ?_⟩
    have := (h2 j k hj).weak hw
    erw [Kind.toPseudo_rename] at this
    exact this

theorem Tele.pts_var : ∀ (T : Tele), T.WF → ∀ n A, T.ctx[n]? = some A →
    HW T.toPseudo (.var (T.layout.tmIdx n)) (A.toPseudo T.layout)
  | [], _, n, A, h => by simp [Tele.ctx] at h
  | .ty k :: T, hT, n, A, h => by
    simp [Tele.ctx] at h
    obtain ⟨A', hA', rfl⟩ := h
    have := (Tele.pts_var T hT n A' hA').weak (k.toPseudo_wf _ (Tele.pts_valid T hT).1)
    erw [← Con.toPseudo_rename_succ_true] at this
    exact this
  | .tm B :: T, hT, 0, A, h => by
    obtain ⟨hB, hT⟩ := hT
    simp only [Tele.ctx, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have := HasType.var (hB.toPTS _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2)
    erw [← Con.toPseudo_succ_false] at this
    exact this
  | .tm B :: T, hT, n + 1, A, h => by
    obtain ⟨hB, hT⟩ := hT
    simp only [Tele.ctx, List.getElem?_cons_succ] at h
    have := (Tele.pts_var T hT n A h).weak
      (hB.toPTS _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2)
    erw [← Con.toPseudo_succ_false] at this
    exact this

/-- β-equal constructors have convertible encodings. -/
theorem ConBEq.toConv (h : ConBEq Δ A B k) :
    ∀ L : Layout, Pseudo.Conv (A.toPseudo L) (B.toPseudo L) := by
  induction h with
  | refl _ => intro L; exact .refl _
  | symm _ ih => intro L; exact (ih L).symm
  | trans _ _ ih₁ ih₂ => intro L; exact (ih₁ L).trans (ih₂ L)
  | beta _ _ => intro L; rw [Con.toPseudo_substOne]; exact .beta _ _ _
  | arr _ _ ih₁ ih₂ => intro L; exact .pi (ih₁ L) (ih₂ (false :: L))
  | all _ ih => intro L; exact .pi (.refl _) (ih (true :: L))
  | lam _ ih => intro L; exact .lam (.refl _) (ih (true :: L))
  | app _ _ ih₁ ih₂ => intro L; exact .app (ih₁ L) (ih₂ L)

theorem TypedB.toPTS_aux (h : TypedB Δ Γ t A) : ∀ T : Tele, Δ = T.kctx → Γ = T.ctx → T.WF →
    HW T.toPseudo (t.toPseudo T.layout) (A.toPseudo T.layout) := by
  induction h with
  | var hn =>
    intro T _ hΓ hT
    subst hΓ
    exact Tele.pts_var T hT _ _ hn
  | app _ _ ih₁ ih₂ =>
    intro T hΔ hΓ hT
    have h₁ := ih₁ T hΔ hΓ hT
    simp only [Con.toPseudo] at h₁
    have := HasType.app h₁ (ih₂ T hΔ hΓ hT)
    erw [Con.toPseudo_false_substOne] at this
    exact this
  | @lam Δ A Γ t B hA ht ih =>
    intro T hΔ hΓ hT
    subst hΔ hΓ
    have h₁ := ih (.tm A :: T) rfl rfl ⟨hA, hT⟩
    have hB : Kinded T.kctx B .star :=
      (TypedB.toTyped ht).kinded (Tele.WF.ctx_kinded (T := .tm A :: T) ⟨hA, hT⟩)
    exact .lam h₁ ((Kinded.arr hA hB).toPTS _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2)
  | @tlam k Δ t A Γ ht ih =>
    intro T hΔ hΓ hT
    subst hΔ hΓ
    have h₁ := ih (.ty k :: T) rfl rfl hT
    have hA : Kinded (k :: T.kctx) A .star :=
      (TypedB.toTyped ht).kinded (Tele.WF.ctx_kinded (T := .ty k :: T) hT)
    exact .lam h₁ ((Kinded.all hA).toPTS _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2)
  | @tapp Δ Γ t k A C _ hC ih =>
    intro T hΔ hΓ hT
    have h₁ := ih T hΔ hΓ hT
    subst hΔ hΓ
    simp only [Con.toPseudo] at h₁
    have := HasType.app h₁ (hC.toPTS _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2)
    erw [← Con.toPseudo_substOne] at this
    exact this
  | @conv Δ Γ t A B _ hc ih =>
    intro T hΔ hΓ hT
    have h₁ := ih T hΔ hΓ hT
    subst hΔ hΓ
    exact .conv h₁ (hc.toConv T.layout)
      ((ConBEq.toConEq hc).kinded_right.toPTS _ _ (Tele.pts_valid T hT).1 (Tele.pts_valid T hT).2)

-- The cube uses β-only conversion, so this embedding uses TypedB.
-- Typed.toPTS_false gives a counterexample for βη conversion.
/-- Fω typing with β-only conversion embeds in the λω corner of the cube. -/
theorem TypedB.toPTS {T : Tele} (hT : T.WF) (h : TypedB T.kctx T.ctx t A) :
    HasType Corner.systemFOmega.specification T.toPseudo
      (t.toPseudo T.layout) (A.toPseudo T.layout) :=
  TypedB.toPTS_aux h T rfl rfl hT

/-! ### η-conversion does not embed

`kctx = [H : (* → *) → *, F : * → *]` and `x : H F`. Fω types `x` at
`H (λα. F α)` by η, but the encodings of `H F` and `H (λα. F α)` are distinct
β-normal pseudo-terms, so `x` has no λω typing at the second one. -/

/-- The telescope `F : * → *, H : (* → *) → *, x : H F` (innermost first). -/
def etaTele : Tele :=
  [.tm (.app (.var 0) (.var 1)), .ty (.arr (.arr .star .star) .star), .ty (.arr .star .star)]

/-- `H (λα. F α)`. -/
def etaTy : Con := .app (.var 0) (.lam .star (.app (.var 2) (.var 0)))

theorem etaTele_wf : etaTele.WF := by
  simp only [etaTele, Tele.WF, Tele.kctx, and_true]
  exact .app (.var rfl) (.var rfl)

theorem typed_etaTy : Typed etaTele.kctx etaTele.ctx (.var 0) etaTy := by
  simp only [etaTele, etaTy, Tele.kctx, Tele.ctx, List.map_nil]
  exact .conv (.var rfl) (.app (.refl (.var rfl)) (.symm (.eta (A := .var 1) (.var rfl))))

/-- No λω typing of `x` at `H (λα. F α)`: by generation for variables its types
are β-convertible to `H F`, and Church–Rosser separates the two β-normal forms. -/
theorem not_hasType_etaTy :
    ¬ HasType Corner.systemFOmega.specification etaTele.toPseudo
      ((Tm.var 0).toPseudo etaTele.layout) (etaTy.toPseudo etaTele.layout) := by
  intro h
  have hc := HasType.var_zero_conv h rfl _ _ rfl
  have hc' : Pseudo.Conv (S := CubeSort) (.app (.var 1) (.var 2))
      (.app (.var 1) (.lam (.sort .star) (.app (.var 3) (.var 0)))) := hc
  have := Pseudo.Conv.eq_of_noRedex hc' (by simp [Pseudo.NoRedex]) (by simp [Pseudo.NoRedex])
  simp at this

/-- The βη typing `Typed` does not embed in the λω corner. -/
theorem Typed.toPTS_false :
    ¬ ∀ (T : Tele) (t : Tm) (A : Con), T.WF → Typed T.kctx T.ctx t A →
      HasType Corner.systemFOmega.specification T.toPseudo
        (t.toPseudo T.layout) (A.toPseudo T.layout) :=
  fun h => not_hasType_etaTy (h _ _ _ etaTele_wf typed_etaTy)

/-! ### Encodings: disjointness and injectivity

Kinds are closed and β-normal; constructor encodings are never kinds or sorts;
constructor encodings are injective at every layout; term encodings are
injective on terms whose constructor variables are bound by the layout. -/

theorem Kind.noRedex_toPseudo : ∀ k : Kind, (k.toPseudo).NoRedex
  | .star => trivial
  | .arr k l => ⟨Kind.noRedex_toPseudo k, Kind.noRedex_toPseudo l⟩

theorem Kind.toPseudo_inj : ∀ (k l : Kind), k.toPseudo = l.toPseudo → k = l
  | .star, .star, _ => rfl
  | .star, .arr _ _, h => by simp [Kind.toPseudo] at h
  | .arr _ _, .star, h => by simp [Kind.toPseudo] at h
  | .arr k l, .arr k' l', h => by
    simp only [Kind.toPseudo, Pseudo.pi.injEq] at h
    rw [Kind.toPseudo_inj k k' h.1, Kind.toPseudo_inj l l' h.2]

theorem Kind.toPseudo_ne_box (k : Kind) : k.toPseudo ≠ .sort .box := by
  cases k <;> simp [Kind.toPseudo]

theorem Kind.eq_star_of_toPseudo {k : Kind} {s : CubeSort} (h : k.toPseudo = .sort s) :
    k = .star ∧ s = .star := by
  cases k with
  | star =>
    simp only [Kind.toPseudo, Pseudo.sort.injEq] at h
    exact ⟨rfl, h.symm⟩
  | arr _ _ => simp [Kind.toPseudo] at h

theorem Con.toPseudo_ne_sort (A : Con) (L : Layout) (s : CubeSort) :
    A.toPseudo L ≠ .sort s := by
  cases A <;> simp [Con.toPseudo]

theorem Con.toPseudo_ne_kind (k : Kind) : ∀ (A : Con) (L : Layout), A.toPseudo L ≠ k.toPseudo := by
  induction k with
  | star => intro A L; exact Con.toPseudo_ne_sort A L _
  | arr k l ihk ihl =>
    intro A L h
    cases A <;> simp only [Con.toPseudo, Kind.toPseudo, Pseudo.pi.injEq, reduceCtorEq] at h
    case arr A B => exact ihk A L h.1
    case all k' A => exact ihl A _ h.2

/-- Constructor encodings are injective at every layout. -/
theorem Con.toPseudo_inj (A : Con) : ∀ (B : Con) (L : Layout),
    A.toPseudo L = B.toPseudo L → A = B := by
  induction A with
  | var j =>
    intro B L h
    cases B <;> simp only [Con.toPseudo, Pseudo.var.injEq, reduceCtorEq] at h
    rw [L.tyIdx_inj _ _ h]
  | arr A B ihA ihB =>
    intro C L h
    cases C <;> simp only [Con.toPseudo, Pseudo.pi.injEq, reduceCtorEq] at h
    case arr A' B' => rw [ihA A' L h.1, ihB B' _ h.2]
    case all k A' => exact absurd h.1 (Con.toPseudo_ne_kind k A L)
  | all k A ih =>
    intro C L h
    cases C <;> simp only [Con.toPseudo, Pseudo.pi.injEq, reduceCtorEq] at h
    case arr A' B' => exact absurd h.1.symm (Con.toPseudo_ne_kind k A' L)
    case all k' A' => rw [Kind.toPseudo_inj k k' h.1, ih A' _ h.2]
  | lam k A ih =>
    intro C L h
    cases C <;> simp only [Con.toPseudo, Pseudo.lam.injEq, reduceCtorEq] at h
    rw [Kind.toPseudo_inj _ _ h.1, ih _ _ h.2]
  | app A B ihA ihB =>
    intro C L h
    cases C <;> simp only [Con.toPseudo, Pseudo.app.injEq, reduceCtorEq] at h
    rw [ihA _ L h.1, ihB _ L h.2]

theorem Tm.toPseudo_ne_sort (t : Tm) (L : Layout) (s : CubeSort) : t.toPseudo L ≠ .sort s := by
  cases t <;> simp [Tm.toPseudo]

theorem Tm.toPseudo_ne_kind (t : Tm) (L : Layout) (k : Kind) : t.toPseudo L ≠ k.toPseudo := by
  cases k <;> cases t <;> simp [Tm.toPseudo, Kind.toPseudo]

theorem Tele.kctx_length : ∀ T : Tele, T.kctx.length = T.layout.count true
  | [] => rfl
  | .ty _ :: T => by simp [Tele.kctx, Tele.layout, Tele.kctx_length T]
  | .tm _ :: T => by simp [Tele.kctx, Tele.layout, Tele.kctx_length T]

theorem Kinded.bounded (h : Kinded Δ A k) : ∀ m, A.FreeIn m → m < Δ.length := by
  induction h with
  | var hn =>
    intro m hm
    simp only [Con.FreeIn] at hm
    subst hm
    simpa using congrArg Option.isSome hn
  | arr _ _ ih1 ih2 =>
    intro m hm
    simp only [Con.FreeIn] at hm
    exact hm.elim (ih1 m) (ih2 m)
  | all _ ih =>
    intro m hm
    have := ih (m + 1) hm
    simp only [List.length_cons] at this
    omega
  | lam _ ih =>
    intro m hm
    have := ih (m + 1) hm
    simp only [List.length_cons] at this
    omega
  | app _ _ ih1 ih2 =>
    intro m hm
    simp only [Con.FreeIn] at hm
    exact hm.elim (ih1 m) (ih2 m)

/-- Typed terms only mention bound constructor variables. -/
theorem Typed.bounded (h : Typed Δ Γ t A) : ∀ m, t.TyFreeIn m → m < Δ.length := by
  induction h with
  | var _ => intro m hm; simp [Tm.TyFreeIn] at hm
  | app _ _ ih1 ih2 =>
    intro m hm
    simp only [Tm.TyFreeIn] at hm
    exact hm.elim (ih1 m) (ih2 m)
  | lam hA _ ih =>
    intro m hm
    simp only [Tm.TyFreeIn] at hm
    exact hm.elim (hA.bounded m) (ih m)
  | tlam _ ih =>
    intro m hm
    have := ih (m + 1) hm
    simp only [List.length_cons] at this
    omega
  | tapp _ hC ih =>
    intro m hm
    simp only [Tm.TyFreeIn] at hm
    exact hm.elim (ih m) (hC.bounded m)
  | conv _ _ ih => exact ih

/-- A bound constructor is never encoded like a term. -/
theorem Tm.toPseudo_ne_con (C : Con) : ∀ (u : Tm) (L : Layout),
    (∀ m, C.FreeIn m → m < L.count true) → u.toPseudo L ≠ C.toPseudo L := by
  induction C with
  | var j =>
    intro u L hC h
    cases u <;> simp only [Tm.toPseudo, Con.toPseudo, Pseudo.var.injEq, reduceCtorEq] at h
    exact L.tmIdx_ne_tyIdx _ _ (hC _ rfl) h
  | arr A B _ _ => intro u L _ h; cases u <;> simp [Tm.toPseudo, Con.toPseudo] at h
  | all k A _ => intro u L _ h; cases u <;> simp [Tm.toPseudo, Con.toPseudo] at h
  | lam k A ih =>
    intro u L hC h
    cases u <;> simp only [Tm.toPseudo, Con.toPseudo, Pseudo.lam.injEq, reduceCtorEq] at h
    case lam A' t' => exact Con.toPseudo_ne_kind k A' L h.1
    case tlam k' t' =>
      refine ih t' (true :: L) (fun m hm => ?_) h.2
      rw [Layout.count_true]
      cases m with
      | zero => exact Nat.zero_lt_succ _
      | succ m => exact Nat.succ_lt_succ (hC m hm)
  | app A B ihA _ =>
    intro u L hC h
    cases u <;> simp only [Tm.toPseudo, Con.toPseudo, Pseudo.app.injEq, reduceCtorEq] at h
    case app t₁ t₂ => exact ihA t₁ L (fun m hm => hC m (Or.inl hm)) h.1
    case tapp t₁ C' => exact ihA t₁ L (fun m hm => hC m (Or.inl hm)) h.1

/-- Term encodings are injective on terms whose constructor variables are bound. -/
theorem Tm.toPseudo_inj_bnd (t : Tm) : ∀ (u : Tm) (L : Layout),
    (∀ m, t.TyFreeIn m → m < L.count true) → (∀ m, u.TyFreeIn m → m < L.count true) →
    t.toPseudo L = u.toPseudo L → t = u := by
  have hb : ∀ (L : Layout) (k : Kind) (s : Tm),
      (∀ m, (Tm.tlam k s).TyFreeIn m → m < L.count true) →
      ∀ m, s.TyFreeIn m → m < (true :: L).count true := by
    intro L k s hs m hm
    rw [Layout.count_true]
    cases m with
    | zero => exact Nat.zero_lt_succ _
    | succ m => exact Nat.succ_lt_succ (hs m hm)
  induction t with
  | var i =>
    intro u L _ _ h
    cases u <;> simp only [Tm.toPseudo, Pseudo.var.injEq, reduceCtorEq] at h
    rw [L.tmIdx_inj _ _ h]
  | app t u iht ihu =>
    intro v L ht hv h
    cases v <;> simp only [Tm.toPseudo, Pseudo.app.injEq, reduceCtorEq] at h
    case app t' u' =>
      rw [iht t' L (fun m hm => ht m (Or.inl hm)) (fun m hm => hv m (Or.inl hm)) h.1,
        ihu u' L (fun m hm => ht m (Or.inr hm)) (fun m hm => hv m (Or.inr hm)) h.2]
    case tapp t' C =>
      exact absurd h.2 (Tm.toPseudo_ne_con C u L (fun m hm => hv m (Or.inr hm)))
  | lam A t ih =>
    intro v L ht hv h
    cases v <;> simp only [Tm.toPseudo, Pseudo.lam.injEq, reduceCtorEq] at h
    case lam A' t' =>
      rw [Con.toPseudo_inj A A' L h.1, ih t' (false :: L)
        (fun m hm => by rw [Layout.count_false]; exact ht m (Or.inr hm))
        (fun m hm => by rw [Layout.count_false]; exact hv m (Or.inr hm)) h.2]
    case tlam k t' => exact absurd h.1 (Con.toPseudo_ne_kind k A L)
  | tapp t C ih =>
    intro v L ht hv h
    cases v <;> simp only [Tm.toPseudo, Pseudo.app.injEq, reduceCtorEq] at h
    case app t' u' =>
      exact absurd h.2.symm (Tm.toPseudo_ne_con C u' L (fun m hm => ht m (Or.inr hm)))
    case tapp t' C' =>
      rw [ih t' L (fun m hm => ht m (Or.inl hm)) (fun m hm => hv m (Or.inl hm)) h.1,
        Con.toPseudo_inj C C' L h.2]
  | tlam k t ih =>
    intro v L ht hv h
    cases v <;> simp only [Tm.toPseudo, Pseudo.lam.injEq, reduceCtorEq] at h
    case lam A' t' => exact absurd h.1.symm (Con.toPseudo_ne_kind k A' L)
    case tlam k' t' =>
      rw [Kind.toPseudo_inj k k' h.1, ih t' (true :: L) (hb L k t ht) (hb L k' t' hv) h.2]

/-! ### Reduction of constructor encodings

Parallel reduction of the encoding of a kinded constructor is `ConBEq`, and stays
an encoding. Hence β-convertible encodings of constructors of the same kind are
`ConBEq` (Church–Rosser), and no kinded constructor converts to a kind or sort. -/

theorem ConBEq.kinded_right (h : ConBEq Δ A B k) : Kinded Δ B k := h.toConEq.kinded_right

theorem Con.par_reflect {p v : Pseudo CubeSort} (h : Pseudo.Par p v) :
    ∀ (A : Con) (L : Layout) (Δ : KCtx) (k : Kind),
    A.toPseudo L = p → Kinded Δ A k → ∃ A' : Con, A'.toPseudo L = v ∧ ConBEq Δ A A' k := by
  induction h with
  | sort s => intro A L Δ k e _; exact absurd e (Con.toPseudo_ne_sort A L s)
  | var n => intro A L Δ k e hA; exact ⟨A, e, .refl hA⟩
  | app _ _ ih₁ ih₂ =>
    intro A L Δ k e hA
    cases A with
    | app A₁ A₂ =>
      injection e with e₁ e₂
      cases hA with
      | app h₁ h₂ =>
        obtain ⟨A₁', r₁, q₁⟩ := ih₁ A₁ L Δ _ e₁ h₁
        obtain ⟨A₂', r₂, q₂⟩ := ih₂ A₂ L Δ _ e₂ h₂
        exact ⟨.app A₁' A₂', by subst r₁ r₂; rfl, .app q₁ q₂⟩
    | var _ | arr _ _ | all _ _ | lam _ _ => simp [Con.toPseudo] at e
  | lam hA _ _ ihb =>
    intro A L Δ k e hk
    cases A with
    | lam k₀ A₀ =>
      injection e with e₁ e₂
      subst e₁ e₂
      have e₃ := hA.eq_of_noRedex (Kind.noRedex_toPseudo k₀)
      subst e₃
      cases hk with
      | lam h₁ =>
        obtain ⟨A₀', r, q⟩ := ihb A₀ (true :: L) _ _ rfl h₁
        exact ⟨.lam k₀ A₀', by subst r; rfl, .lam q⟩
    | var _ | arr _ _ | all _ _ | app _ _ => simp [Con.toPseudo] at e
  | pi hA _ ihA ihB =>
    intro A L Δ k e hk
    cases A with
    | arr A₁ A₂ =>
      injection e with e₁ e₂
      cases hk with
      | arr h₁ h₂ =>
        obtain ⟨A₁', r₁, q₁⟩ := ihA A₁ L Δ _ e₁ h₁
        obtain ⟨A₂', r₂, q₂⟩ := ihB A₂ (false :: L) Δ _ e₂ h₂
        exact ⟨.arr A₁' A₂', by subst r₁ r₂; rfl, .arr q₁ q₂⟩
    | all k₀ A₀ =>
      injection e with e₁ e₂
      subst e₁ e₂
      have e₃ := hA.eq_of_noRedex (Kind.noRedex_toPseudo k₀)
      subst e₃
      cases hk with
      | all h₁ =>
        obtain ⟨A₀', r, q⟩ := ihB A₀ (true :: L) _ _ rfl h₁
        exact ⟨.all k₀ A₀', by subst r; rfl, .all q⟩
    | var _ | lam _ _ | app _ _ => simp [Con.toPseudo] at e
  | beta _ _ _ ihb iha =>
    intro A L Δ k e hk
    cases A with
    | app A₁ A₂ =>
      injection e with e₁ e₂
      cases A₁ with
      | lam k₀ A₀ =>
        injection e₁ with e₃ e₄
        cases hk with
        | app h₁ h₂ =>
          cases h₁ with
          | lam h₁ =>
            obtain ⟨A₀', r₁, q₁⟩ := ihb A₀ (true :: L) _ _ e₄ h₁
            obtain ⟨A₂', r₂, q₂⟩ := iha A₂ L Δ _ e₂ h₂
            subst r₁ r₂
            exact ⟨A₀'.substOne A₂', Con.toPseudo_substOne _ _ _,
              (ConBEq.app (ConBEq.lam q₁) q₂).trans (.beta q₁.kinded_right q₂.kinded_right)⟩
      | var _ | arr _ _ | all _ _ | app _ _ => simp [Con.toPseudo] at e₁
    | var _ | arr _ _ | all _ _ | lam _ _ => simp [Con.toPseudo] at e

theorem Con.reflTransGen_reflect {A : Con} {L : Layout} {v : Pseudo CubeSort} {Δ : KCtx}
    {k : Kind} (h : Relation.ReflTransGen Pseudo.Par (A.toPseudo L) v) (hA : Kinded Δ A k) :
    ∃ A' : Con, A'.toPseudo L = v ∧ ConBEq Δ A A' k := by
  induction h with
  | refl => exact ⟨A, rfl, .refl hA⟩
  | tail _ hp ih =>
    obtain ⟨A', rfl, q⟩ := ih
    obtain ⟨A'', r, q'⟩ := Con.par_reflect hp A' L Δ k rfl q.kinded_right
    exact ⟨A'', r, q.trans q'⟩

/-- β-convertible encodings of constructors of the same kind are `ConBEq`. -/
theorem Con.conv_reflect {A B : Con} {L : Layout} {Δ : KCtx} {k : Kind}
    (h : Pseudo.Conv (A.toPseudo L) (B.toPseudo L)) (hA : Kinded Δ A k) (hB : Kinded Δ B k) :
    ConBEq Δ A B k := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  obtain ⟨A', r₁, q₁⟩ := Con.reflTransGen_reflect h₁ hA
  obtain ⟨B', r₂, q₂⟩ := Con.reflTransGen_reflect h₂ hB
  have e : A' = B' := Con.toPseudo_inj A' B' L (r₁.trans r₂.symm)
  subst e
  exact q₁.trans q₂.symm

theorem Con.conv_noRedex {A : Con} {L : Layout} {p : Pseudo CubeSort} {Δ : KCtx} {k : Kind}
    (h : Pseudo.Conv (A.toPseudo L) p) (hA : Kinded Δ A k) (hp : p.NoRedex) :
    ∃ A' : Con, A'.toPseudo L = p := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  obtain ⟨A', r₁, _⟩ := Con.reflTransGen_reflect h₁ hA
  exact ⟨A', r₁.trans (Pseudo.reflTransGen_par_eq_of_noRedex h₂ hp)⟩

theorem Con.not_conv_kind {A : Con} {L : Layout} {Δ : KCtx} {k : Kind} (hA : Kinded Δ A k)
    (l : Kind) (h : Pseudo.Conv (A.toPseudo L) l.toPseudo) : False := by
  obtain ⟨A', e⟩ := Con.conv_noRedex h hA (Kind.noRedex_toPseudo l)
  exact Con.toPseudo_ne_kind l A' L e

theorem Con.not_conv_sort {A : Con} {L : Layout} {Δ : KCtx} {k : Kind} (hA : Kinded Δ A k)
    (s : CubeSort) (h : Pseudo.Conv (A.toPseudo L) (.sort s)) : False := by
  obtain ⟨A', e⟩ := Con.conv_noRedex h hA trivial
  exact Con.toPseudo_ne_sort A' L s e

/-! ### Renaming for Fω syntax and its encoding -/

theorem Con.toPseudo_nil_rename (A : Con) (r : ℕ → ℕ) :
    (A.rename r).toPseudo [] = (A.toPseudo []).rename r :=
  A.toPseudo_rename [] [] r r (fun _ => rfl)

theorem Con.rename_rename (A : Con) (r r' : ℕ → ℕ) :
    (A.rename r).rename r' = A.rename (r' ∘ r) := by
  apply Con.toPseudo_inj _ _ []
  rw [Con.toPseudo_nil_rename, Con.toPseudo_nil_rename, Con.toPseudo_nil_rename,
    Pseudo.rename_rename]

theorem Con.rename_succ_comm (A : Con) (r : ℕ → ℕ) :
    (A.rename Nat.succ).rename (scons 0 (Nat.succ ∘ r)) = (A.rename r).rename Nat.succ := by
  rw [Con.rename_rename, Con.rename_rename, scons_comp_succ]

theorem Con.rename_substOne (A B : Con) (r : ℕ → ℕ) :
    (A.substOne B).rename r = (A.rename (scons 0 (Nat.succ ∘ r))).substOne (B.rename r) := by
  apply Con.toPseudo_inj _ _ []
  simp only [Con.toPseudo_nil_rename, Con.toPseudo_substOne, Pseudo.rename_substOne]
  rw [A.toPseudo_rename [true] [true] (scons 0 (Nat.succ ∘ r)) (DeBruijn.lift r)
    (fun j => by cases j <;> simp [Layout.tyIdx, DeBruijn.lift])]

theorem ConEq.rename (h : ConEq Δ A B k) {Δ' : KCtx} {r : ℕ → ℕ}
    (hr : ∀ n k', Δ[n]? = some k' → Δ'[r n]? = some k') :
    ConEq Δ' (A.rename r) (B.rename r) k := by
  induction h generalizing Δ' r with
  | refl h => exact .refl (h.rename hr)
  | symm _ ih => exact .symm (ih hr)
  | trans _ _ ih1 ih2 => exact .trans (ih1 hr) (ih2 hr)
  | beta hA hB =>
    rw [Con.rename_substOne]
    exact .beta (hA.rename (kren_lift hr _)) (hB.rename hr)
  | eta hA =>
    simp only [Con.rename, scons_zero, Con.rename_succ_comm]
    exact .eta (hA.rename hr)
  | arr _ _ ih1 ih2 => exact .arr (ih1 hr) (ih2 hr)
  | all _ ih => exact .all (ih (kren_lift hr _))
  | lam _ ih => exact .lam (ih (kren_lift hr _))
  | app _ _ ih1 ih2 => exact .app (ih1 hr) (ih2 hr)

/-- Weakening of Fω typing along a renaming of term variables. -/
theorem Typed.rename (h : Typed Δ Γ t A) {Γ' : Ctx} {r : ℕ → ℕ}
    (hr : ∀ n B, Γ[n]? = some B → Γ'[r n]? = some B) : Typed Δ Γ' (t.rename r) A := by
  induction h generalizing Γ' r with
  | var hn => exact .var (hr _ _ hn)
  | app _ _ ih1 ih2 => exact .app (ih1 hr) (ih2 hr)
  | lam hA _ ih =>
    refine .lam hA (ih ?_)
    intro n B hn
    cases n with
    | zero => simpa using hn
    | succ n => simpa using hr n B (by simpa using hn)
  | tlam _ ih =>
    refine .tlam (ih ?_)
    intro n B hn
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn ⊢
    obtain ⟨B0, hB0, rfl⟩ := hn
    exact ⟨B0, hr n B0 hB0, rfl⟩
  | tapp _ hC ih => exact .tapp (ih hr) hC
  | conv _ hc ih => exact .conv (ih hr) hc

/-- Weakening of Fω typing along a kind-preserving renaming of constructor variables. -/
theorem Typed.tyRename (h : Typed Δ Γ t A) {Δ' : KCtx} {r : ℕ → ℕ}
    (hr : ∀ n k', Δ[n]? = some k' → Δ'[r n]? = some k') :
    Typed Δ' (Γ.map (Con.rename r)) (t.tyRename r) (A.rename r) := by
  induction h generalizing Δ' r with
  | var hn => exact .var (by rw [List.getElem?_map, hn]; rfl)
  | app _ _ ih1 ih2 => exact .app (ih1 hr) (ih2 hr)
  | lam hA _ ih => exact .lam (hA.rename hr) (ih hr)
  | tlam _ ih =>
    refine .tlam ?_
    have e : ∀ Γ₀ : Ctx, (Γ₀.map (Con.rename Nat.succ)).map (Con.rename (scons 0 (Nat.succ ∘ r))) =
        (Γ₀.map (Con.rename r)).map (Con.rename Nat.succ) := by
      intro Γ₀
      simp only [List.map_map]
      congr 1
      funext B
      exact Con.rename_succ_comm B r
    rw [← e]
    exact ih (kren_lift hr _)
  | tapp _ hC ih =>
    rw [Con.rename_substOne]
    exact .tapp (ih hr) (hC.rename hr)
  | conv _ hc ih => exact .conv (ih hr) (hc.rename hr)

theorem Tm.toPseudo_rename (t : Tm) : ∀ (L L' : Layout) (r ρ : ℕ → ℕ),
    (∀ i, L'.tmIdx (r i) = ρ (L.tmIdx i)) → (∀ j, L'.tyIdx j = ρ (L.tyIdx j)) →
    (t.rename r).toPseudo L' = (t.toPseudo L).rename ρ := by
  have hC : ∀ (C : Con) (L L' : Layout) (ρ : ℕ → ℕ), (∀ j, L'.tyIdx j = ρ (L.tyIdx j)) →
      C.toPseudo L' = (C.toPseudo L).rename ρ := by
    intro C L L' ρ h'
    have := C.toPseudo_rename L L' id ρ h'
    rwa [C.rename_eq_self id (fun _ => rfl)] at this
  induction t with
  | var i => intro L L' r ρ h _; simp [Tm.rename, Tm.toPseudo, Pseudo.rename, h]
  | app t u iht ihu =>
    intro L L' r ρ h h'
    simp only [Tm.rename, Tm.toPseudo, Pseudo.rename]
    rw [iht L L' r ρ h h', ihu L L' r ρ h h']
  | lam A t ih =>
    intro L L' r ρ h h'
    simp only [Tm.rename, Tm.toPseudo, Pseudo.rename]
    rw [hC A L L' ρ h', ih (false :: L) (false :: L') (scons 0 (Nat.succ ∘ r)) (DeBruijn.lift ρ)
      (fun i => by cases i <;> simp [Layout.tmIdx, DeBruijn.lift, h])
      (fun j => by simp [Layout.tyIdx, DeBruijn.lift, h'])]
  | tapp t C ih =>
    intro L L' r ρ h h'
    simp only [Tm.rename, Tm.toPseudo, Pseudo.rename]
    rw [hC C L L' ρ h', ih L L' r ρ h h']
  | tlam k t ih =>
    intro L L' r ρ h h'
    simp only [Tm.rename, Tm.toPseudo, Pseudo.rename, Kind.toPseudo_rename]
    rw [ih (true :: L) (true :: L') r (DeBruijn.lift ρ)
      (fun i => by simp [Layout.tmIdx, DeBruijn.lift, h])
      (fun j => by cases j <;> simp [Layout.tyIdx, DeBruijn.lift, h'])]

theorem Tm.toPseudo_tyRename (t : Tm) : ∀ (L L' : Layout) (r ρ : ℕ → ℕ),
    (∀ i, L'.tmIdx i = ρ (L.tmIdx i)) → (∀ j, L'.tyIdx (r j) = ρ (L.tyIdx j)) →
    (t.tyRename r).toPseudo L' = (t.toPseudo L).rename ρ := by
  induction t with
  | var i => intro L L' r ρ h _; simp [Tm.tyRename, Tm.toPseudo, Pseudo.rename, h]
  | app t u iht ihu =>
    intro L L' r ρ h h'
    simp only [Tm.tyRename, Tm.toPseudo, Pseudo.rename]
    rw [iht L L' r ρ h h', ihu L L' r ρ h h']
  | lam A t ih =>
    intro L L' r ρ h h'
    simp only [Tm.tyRename, Tm.toPseudo, Pseudo.rename]
    rw [Con.toPseudo_rename A L L' r ρ h', ih (false :: L) (false :: L') r (DeBruijn.lift ρ)
      (fun i => by cases i <;> simp [Layout.tmIdx, DeBruijn.lift, h])
      (fun j => by simp [Layout.tyIdx, DeBruijn.lift, h'])]
  | tapp t C ih =>
    intro L L' r ρ h h'
    simp only [Tm.tyRename, Tm.toPseudo, Pseudo.rename]
    rw [ih L L' r ρ h h', Con.toPseudo_rename C L L' r ρ h']
  | tlam k t ih =>
    intro L L' r ρ h h'
    simp only [Tm.tyRename, Tm.toPseudo, Pseudo.rename, Kind.toPseudo_rename]
    rw [ih (true :: L) (true :: L') (scons 0 (Nat.succ ∘ r)) (DeBruijn.lift ρ)
      (fun i => by simp [Layout.tmIdx, DeBruijn.lift, h])
      (fun j => by cases j <;> simp [Layout.tyIdx, DeBruijn.lift, h'])]

theorem Tm.toPseudo_rename_succ (t : Tm) (L : Layout) :
    (t.rename Nat.succ).toPseudo (false :: L) = (t.toPseudo L).rename Nat.succ :=
  t.toPseudo_rename L (false :: L) Nat.succ Nat.succ (fun _ => rfl) (fun _ => rfl)

theorem Tm.toPseudo_tyRename_succ (t : Tm) (L : Layout) :
    (t.tyRename Nat.succ).toPseudo (true :: L) = (t.toPseudo L).rename Nat.succ :=
  t.toPseudo_tyRename L (true :: L) Nat.succ Nat.succ (fun _ => rfl) (fun _ => rfl)

theorem Tm.toPseudo_tySubst (t : Tm) : ∀ (L L' : Layout) (σ : ℕ → Con)
    (τ : ℕ → Pseudo CubeSort), (∀ j, (σ j).toPseudo L' = τ (L.tyIdx j)) →
    (∀ i, Pseudo.var (L'.tmIdx i) = τ (L.tmIdx i)) →
    (t.tySubst σ).toPseudo L' = (t.toPseudo L).subst τ := by
  induction t with
  | var i =>
    intro L L' σ τ _ h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    exact h' i
  | app t u iht ihu =>
    intro L L' σ τ h h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    rw [iht L L' σ τ h h', ihu L L' σ τ h h']
  | lam A t ih =>
    intro L L' σ τ h h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    rw [Con.toPseudo_subst A L L' σ τ h, ih (false :: L) (false :: L') σ (Pseudo.liftSub τ)
      (fun j => by simp [Layout.tyIdx, Pseudo.liftSub, Con.toPseudo_succ_false, h])
      (fun i => by
        cases i with
        | zero => rfl
        | succ i =>
          simp only [Layout.tmIdx, Pseudo.liftSub]
          rw [← h' i]
          rfl)]
  | tapp t C ih =>
    intro L L' σ τ h h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst]
    rw [ih L L' σ τ h h', Con.toPseudo_subst C L L' σ τ h]
  | tlam k t ih =>
    intro L L' σ τ h h'
    simp only [Tm.tySubst, Tm.toPseudo, Pseudo.subst, Kind.toPseudo_subst]
    rw [ih (true :: L) (true :: L') (Con.liftSub σ) (Pseudo.liftSub τ)
      (fun j => by
        cases j with
        | zero => simp [Con.liftSub, Layout.tyIdx, Con.toPseudo, Pseudo.liftSub]
        | succ j =>
          simp [Con.liftSub, Layout.tyIdx, Pseudo.liftSub, Con.toPseudo_rename_succ_true, h])
      (fun i => by
        simp only [Layout.tmIdx, Pseudo.liftSub]
        rw [← h' i]
        rfl)]

theorem Tm.toPseudo_subst (t : Tm) : ∀ (L L' : Layout) (σ : ℕ → Tm)
    (τ : ℕ → Pseudo CubeSort), (∀ i, (σ i).toPseudo L' = τ (L.tmIdx i)) →
    (∀ j, Pseudo.var (L'.tyIdx j) = τ (L.tyIdx j)) →
    (t.subst σ).toPseudo L' = (t.toPseudo L).subst τ := by
  have hC : ∀ (C : Con) (L L' : Layout) (τ : ℕ → Pseudo CubeSort),
      (∀ j, Pseudo.var (L'.tyIdx j) = τ (L.tyIdx j)) →
      C.toPseudo L' = (C.toPseudo L).subst τ := by
    intro C L L' τ h'
    have := C.toPseudo_subst L L' Con.var τ h'
    rwa [C.subst_eq_self Con.var (fun _ => rfl)] at this
  induction t with
  | var i =>
    intro L L' σ τ h _
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    exact h i
  | app t u iht ihu =>
    intro L L' σ τ h h'
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    rw [iht L L' σ τ h h', ihu L L' σ τ h h']
  | lam A t ih =>
    intro L L' σ τ h h'
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    rw [hC A L L' τ h', ih (false :: L) (false :: L') (Tm.liftSub σ) (Pseudo.liftSub τ)
      (fun i => by
        cases i with
        | zero => simp [Tm.liftSub, Tm.toPseudo, Layout.tmIdx, Pseudo.liftSub]
        | succ i => simp [Tm.liftSub, Layout.tmIdx, Pseudo.liftSub, Tm.toPseudo_rename_succ, h])
      (fun j => by
        simp only [Layout.tyIdx, Pseudo.liftSub]
        rw [← h' j]
        rfl)]
  | tapp t C ih =>
    intro L L' σ τ h h'
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst]
    rw [ih L L' σ τ h h', hC C L L' τ h']
  | tlam k t ih =>
    intro L L' σ τ h h'
    simp only [Tm.subst, Tm.toPseudo, Pseudo.subst, Kind.toPseudo_subst]
    rw [ih (true :: L) (true :: L') (fun n => (σ n).tyRename Nat.succ) (Pseudo.liftSub τ)
      (fun i => by simp [Layout.tmIdx, Pseudo.liftSub, Tm.toPseudo_tyRename_succ, h])
      (fun j => by
        cases j with
        | zero => rfl
        | succ j =>
          simp only [Layout.tyIdx, Pseudo.liftSub]
          rw [← h' j]
          rfl)]

theorem Tm.toPseudo_substOne (b u : Tm) (L : Layout) :
    (b.substOne u).toPseudo L = (b.toPseudo (false :: L)).substOne (u.toPseudo L) :=
  b.toPseudo_subst (false :: L) L (scons u Tm.var)
    (fun | 0 => u.toPseudo L | n + 1 => .var n) (fun i => by cases i <;> rfl) (fun _ => rfl)

theorem Tm.toPseudo_tySubstOne (b : Tm) (C : Con) (L : Layout) :
    (b.tySubstOne C).toPseudo L = (b.toPseudo (true :: L)).substOne (C.toPseudo L) :=
  b.toPseudo_tySubst (true :: L) L (scons C Con.var)
    (fun | 0 => C.toPseudo L | n + 1 => .var n)
    (fun j => by cases j <;> simp [Layout.tyIdx, Con.toPseudo]) (fun _ => rfl)

/-! ### Substitution for constructors (through the injective encoding) -/

theorem Con.toPseudo_nil_subst (A : Con) (σ : ℕ → Con) :
    (A.subst σ).toPseudo [] = (A.toPseudo []).subst (fun n => (σ n).toPseudo []) :=
  A.toPseudo_subst [] [] σ _ (fun _ => rfl)

theorem Con.toPseudo_true_liftSub (A : Con) (σ : ℕ → Con) :
    (A.subst (Con.liftSub σ)).toPseudo [true] =
      (A.toPseudo [true]).subst (Pseudo.liftSub (fun n => (σ n).toPseudo [])) :=
  A.toPseudo_subst [true] [true] _ _ (fun j => by
    cases j with
    | zero => simp [Con.liftSub, Layout.tyIdx, Con.toPseudo, Pseudo.liftSub]
    | succ j => simp [Con.liftSub, Layout.tyIdx, Pseudo.liftSub, Con.toPseudo_rename_succ_true])

theorem Con.subst_substOne (A C : Con) (σ : ℕ → Con) :
    (A.substOne C).subst σ = (A.subst (Con.liftSub σ)).substOne (C.subst σ) := by
  apply Con.toPseudo_inj _ _ []
  rw [Con.toPseudo_nil_subst, Con.toPseudo_substOne, Con.toPseudo_substOne,
    Con.toPseudo_true_liftSub, Con.toPseudo_nil_subst, Pseudo.subst_substOne]

theorem Con.rename_succ_subst_liftSub (A : Con) (σ : ℕ → Con) :
    (A.rename Nat.succ).subst (Con.liftSub σ) = (A.subst σ).rename Nat.succ := by
  apply Con.toPseudo_inj _ _ []
  rw [Con.toPseudo_nil_subst, Con.toPseudo_nil_rename, Con.toPseudo_nil_rename,
    Con.toPseudo_nil_subst, Pseudo.subst_rename, Pseudo.rename_subst]
  congr 1
  funext n
  simp [Function.comp, Con.liftSub, Con.toPseudo_nil_rename]

theorem Con.rename_succ_substOne (A C : Con) : (A.rename Nat.succ).substOne C = A := by
  apply Con.toPseudo_inj _ _ []
  rw [Con.substOne, Con.toPseudo_nil_subst, Con.toPseudo_nil_rename, Pseudo.subst_rename]
  exact Pseudo.subst_var _ _ (fun _ => rfl)

theorem ConBEq.rename (h : ConBEq Δ A B k) {Δ' : KCtx} {r : ℕ → ℕ}
    (hr : ∀ n k', Δ[n]? = some k' → Δ'[r n]? = some k') :
    ConBEq Δ' (A.rename r) (B.rename r) k := by
  induction h generalizing Δ' r with
  | refl h => exact .refl (h.rename hr)
  | symm _ ih => exact .symm (ih hr)
  | trans _ _ ih1 ih2 => exact .trans (ih1 hr) (ih2 hr)
  | beta hA hB =>
    rw [Con.rename_substOne]
    exact .beta (hA.rename (kren_lift hr _)) (hB.rename hr)
  | arr _ _ ih1 ih2 => exact .arr (ih1 hr) (ih2 hr)
  | all _ ih => exact .all (ih (kren_lift hr _))
  | lam _ ih => exact .lam (ih (kren_lift hr _))
  | app _ _ ih1 ih2 => exact .app (ih1 hr) (ih2 hr)

theorem ConBEq.subst (h : ConBEq Δ A B k) {Δ' : KCtx} {σ : ℕ → Con}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k') :
    ConBEq Δ' (A.subst σ) (B.subst σ) k := by
  induction h generalizing Δ' σ with
  | refl h => exact .refl (h.subst hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ih1 ih2 => exact .trans (ih1 hσ) (ih2 hσ)
  | beta hA hB =>
    rw [Con.subst_substOne]
    exact .beta (hA.subst (ksub_lift hσ _)) (hB.subst hσ)
  | arr _ _ ih1 ih2 => exact .arr (ih1 hσ) (ih2 hσ)
  | all _ ih => exact .all (ih (ksub_lift hσ _))
  | lam _ ih => exact .lam (ih (ksub_lift hσ _))
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)

/-- `ConBEq` is a congruence for instantiation (via Church–Rosser). -/
theorem ConBEq.substOne_congr (hB : ConBEq (k :: Δ) B B' l) (hC : ConBEq Δ C C' k) :
    ConBEq Δ (B.substOne C) (B'.substOne C') l := by
  apply Con.conv_reflect (L := [])
  · rw [Con.toPseudo_substOne, Con.toPseudo_substOne]
    exact ((hB.toConv [true]).substOne_left _).trans
      (Pseudo.Conv.map (fun x => Pseudo.substOne (B'.toPseudo [true]) x)
        (fun _ _ hxy => (Pseudo.Par.refl _).substOne hxy) (hC.toConv []))
  · exact hB.toConEq.kinded_left.substOne hC.toConEq.kinded_left
  · exact hB.toConEq.kinded_right.substOne hC.toConEq.kinded_right

theorem conv_pi_inj {a b a' b' : Pseudo CubeSort} (h : Pseudo.Conv (.pi a b) (.pi a' b')) :
    Pseudo.Conv a a' ∧ Pseudo.Conv b b' := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Pseudo.reflTransGen_par_pi_inv h₁
  obtain ⟨A₂, B₂, e, hA₂, hB₂⟩ := Pseudo.reflTransGen_par_pi_inv h₂
  injection e with e₁ e₂
  subst e₁ e₂
  exact ⟨(Pseudo.reflTransGen_par_toConv hA₁).trans (Pseudo.reflTransGen_par_toConv hA₂).symm,
    (Pseudo.reflTransGen_par_toConv hB₁).trans (Pseudo.reflTransGen_par_toConv hB₂).symm⟩

theorem ConBEq.arr_inj (h : ConBEq Δ (.arr X Y) (.arr X' Y') .star) :
    ConBEq Δ X X' .star ∧ ConBEq Δ Y Y' .star := by
  obtain ⟨c1, c2⟩ := conv_pi_inj (h.toConv [])
  cases h.toConEq.kinded_left with
  | arr hX hY =>
    cases h.toConEq.kinded_right with
    | arr hX' hY' => exact ⟨Con.conv_reflect c1 hX hX', Con.conv_reflect c2 hY hY'⟩

theorem ConBEq.all_inj (h : ConBEq Δ (.all k Y) (.all k' Y') .star) :
    k = k' ∧ ConBEq (k :: Δ) Y Y' .star := by
  obtain ⟨c1, c2⟩ := conv_pi_inj (h.toConv [])
  have e := Kind.toPseudo_inj _ _
    (c1.eq_of_noRedex (Kind.noRedex_toPseudo k) (Kind.noRedex_toPseudo k'))
  subst e
  cases h.toConEq.kinded_left with
  | all hY =>
    cases h.toConEq.kinded_right with
    | all hY' => exact ⟨rfl, Con.conv_reflect c2 hY hY'⟩

theorem ConBEq.arr_ne_all (h : ConBEq Δ (.arr X Y) (.all k Y') .star) : False := by
  obtain ⟨c1, _⟩ := conv_pi_inj (h.toConv [])
  cases h.toConEq.kinded_left with
  | arr hX _ => exact Con.not_conv_kind hX k c1

/-! ### Metatheory of β-only Fω typing -/

theorem TypedB.rename (h : TypedB Δ Γ t A) {Γ' : Ctx} {r : ℕ → ℕ}
    (hr : ∀ n B, Γ[n]? = some B → Γ'[r n]? = some B) : TypedB Δ Γ' (t.rename r) A := by
  induction h generalizing Γ' r with
  | var hn => exact .var (hr _ _ hn)
  | app _ _ ih1 ih2 => exact .app (ih1 hr) (ih2 hr)
  | lam hA _ ih =>
    refine .lam hA (ih ?_)
    intro n B hn
    cases n with
    | zero => simpa using hn
    | succ n => simpa using hr n B (by simpa using hn)
  | tlam _ ih =>
    refine .tlam (ih ?_)
    intro n B hn
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn ⊢
    obtain ⟨B0, hB0, rfl⟩ := hn
    exact ⟨B0, hr n B0 hB0, rfl⟩
  | tapp _ hC ih => exact .tapp (ih hr) hC
  | conv _ hc ih => exact .conv (ih hr) hc

theorem TypedB.tyRename (h : TypedB Δ Γ t A) {Δ' : KCtx} {r : ℕ → ℕ}
    (hr : ∀ n k', Δ[n]? = some k' → Δ'[r n]? = some k') :
    TypedB Δ' (Γ.map (Con.rename r)) (t.tyRename r) (A.rename r) := by
  induction h generalizing Δ' r with
  | var hn => exact .var (by rw [List.getElem?_map, hn]; rfl)
  | app _ _ ih1 ih2 => exact .app (ih1 hr) (ih2 hr)
  | lam hA _ ih => exact .lam (hA.rename hr) (ih hr)
  | tlam _ ih =>
    refine .tlam ?_
    have e : ∀ Γ₀ : Ctx, (Γ₀.map (Con.rename Nat.succ)).map (Con.rename (scons 0 (Nat.succ ∘ r))) =
        (Γ₀.map (Con.rename r)).map (Con.rename Nat.succ) := by
      intro Γ₀
      simp only [List.map_map]
      congr 1
      funext B
      exact Con.rename_succ_comm B r
    rw [← e]
    exact ih (kren_lift hr _)
  | tapp _ hC ih =>
    rw [Con.rename_substOne]
    exact .tapp (ih hr) (hC.rename hr)
  | conv _ hc ih => exact .conv (ih hr) (hc.rename hr)

theorem TypedB.subst (h : TypedB Δ Γ t A) {Γ' : Ctx} {σ : ℕ → Tm}
    (hσ : ∀ n B, Γ[n]? = some B → TypedB Δ Γ' (σ n) B) : TypedB Δ Γ' (t.subst σ) A := by
  induction h generalizing Γ' σ with
  | var hn => exact hσ _ _ hn
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)
  | lam hA _ ih =>
    refine .lam hA (ih ?_)
    intro n B hn
    cases n with
    | zero => exact .var (by simpa using hn)
    | succ n =>
      exact (hσ n B (by simpa using hn)).rename (fun m C hm => by simpa using hm)
  | tlam _ ih =>
    refine .tlam (ih ?_)
    intro n B hn
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
    obtain ⟨B0, hB0, rfl⟩ := hn
    exact (hσ n B0 hB0).tyRename (kren_succ _)
  | tapp _ hC ih => exact .tapp (ih hσ) hC
  | conv _ hc ih => exact .conv (ih hσ) hc

theorem TypedB.substOne (ht : TypedB Δ (A :: Γ) t B) (hu : TypedB Δ Γ u A) :
    TypedB Δ Γ (t.substOne u) B :=
  ht.subst fun n C hn => by
    cases n with
    | zero => simp at hn; subst hn; exact hu
    | succ n => exact .var (by simpa using hn)

theorem TypedB.tySubst (h : TypedB Δ Γ t A) {Δ' : KCtx} {σ : ℕ → Con}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k') :
    TypedB Δ' (Γ.map (Con.subst σ)) (t.tySubst σ) (A.subst σ) := by
  induction h generalizing Δ' σ with
  | var hn => exact .var (by rw [List.getElem?_map, hn]; rfl)
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)
  | lam hA _ ih => exact .lam (hA.subst hσ) (ih hσ)
  | tlam _ ih =>
    refine .tlam ?_
    have e : ∀ Γ₀ : Ctx, (Γ₀.map (Con.rename Nat.succ)).map (Con.subst (Con.liftSub σ)) =
        (Γ₀.map (Con.subst σ)).map (Con.rename Nat.succ) := by
      intro Γ₀
      simp only [List.map_map]
      congr 1
      funext B
      exact Con.rename_succ_subst_liftSub B σ
    rw [← e]
    exact ih (ksub_lift hσ _)
  | tapp _ hC ih =>
    rw [Con.subst_substOne]
    exact .tapp (ih hσ) (hC.subst hσ)
  | conv _ hc ih => exact .conv (ih hσ) (hc.subst hσ)

theorem TypedB.tySubstOne (h : TypedB (k :: Δ) (Γ.map (Con.rename Nat.succ)) t A)
    (hC : Kinded Δ C k) : TypedB Δ Γ (t.tySubstOne C) (A.substOne C) := by
  have := h.tySubst (σ := scons C Con.var) (Δ' := Δ) (fun n k' hn => by
    cases n with
    | zero => simp at hn; subst hn; exact hC
    | succ n => exact .var (by simpa using hn))
  rwa [List.map_map, show (Con.subst (scons C Con.var) ∘ Con.rename Nat.succ) = id from
    funext fun B => Con.rename_succ_substOne B C, List.map_id] at this

/-- Context conversion for `TypedB`. -/
theorem TypedB.ctxConv (h : TypedB Δ Γ t A) {Γ' : Ctx}
    (hΓ : ∀ (n : ℕ) (B : Con), Γ[n]? = some B →
      ∃ B', Γ'[n]? = some B' ∧ ConBEq Δ B' B .star) :
    TypedB Δ Γ' t A := by
  induction h generalizing Γ' with
  | var hn =>
    obtain ⟨B', hB', q⟩ := hΓ _ _ hn
    exact .conv (.var hB') q
  | app _ _ ih1 ih2 => exact .app (ih1 hΓ) (ih2 hΓ)
  | lam hA _ ih =>
    refine .lam hA (ih ?_)
    intro n B hn
    cases n with
    | zero =>
      simp at hn
      subst hn
      exact ⟨_, rfl, .refl hA⟩
    | succ n => simpa using hΓ n B (by simpa using hn)
  | tlam _ ih =>
    refine .tlam (ih ?_)
    intro n B hn
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
    obtain ⟨B0, hB0, rfl⟩ := hn
    obtain ⟨B', hB', q⟩ := hΓ n B0 hB0
    exact ⟨B'.rename Nat.succ, by simp [List.getElem?_map, hB'], q.rename (kren_succ _)⟩
  | tapp _ hC ih => exact .tapp (ih hΓ) hC
  | conv _ hc ih => exact .conv (ih hΓ) hc

/-! ### Generation for β-only Fω typing -/

theorem TypedB.inv_app (h : TypedB Δ Γ s A) : ∀ {t u : Tm}, s = .app t u →
    (∀ B ∈ Γ, Kinded Δ B .star) →
    ∃ X Y, TypedB Δ Γ t (.arr X Y) ∧ TypedB Δ Γ u X ∧ ConBEq Δ Y A .star := by
  induction h with
  | app h₁ h₂ _ _ =>
    intro t u e hΓ
    cases e
    cases h₁.toTyped.kinded hΓ with
    | arr _ hY => exact ⟨_, _, h₁, h₂, .refl hY⟩
  | conv _ hc ih =>
    intro t u e hΓ
    obtain ⟨X, Y, h₁, h₂, q⟩ := ih e hΓ
    exact ⟨X, Y, h₁, h₂, q.trans hc⟩
  | var _ | lam _ _ _ | tlam _ _ | tapp _ _ _ => intro _ _ e; cases e

theorem TypedB.inv_lam (h : TypedB Δ Γ s T) : ∀ {A₀ : Con} {b : Tm}, s = .lam A₀ b →
    (∀ B ∈ Γ, Kinded Δ B .star) →
    Kinded Δ A₀ .star ∧ ∃ B, TypedB Δ (A₀ :: Γ) b B ∧ ConBEq Δ (.arr A₀ B) T .star := by
  induction h with
  | lam hA hb _ =>
    intro A₀ b e hΓ
    cases e
    exact ⟨hA, _, hb, .refl (.arr hA (hb.toTyped.kinded (ctx_cons_kinded hA hΓ)))⟩
  | conv _ hc ih =>
    intro A₀ b e hΓ
    obtain ⟨hA, B, hb, q⟩ := ih e hΓ
    exact ⟨hA, B, hb, q.trans hc⟩
  | var _ | app _ _ _ _ | tlam _ _ | tapp _ _ _ => intro _ _ e; cases e

theorem TypedB.inv_tlam (h : TypedB Δ Γ s T) : ∀ {k : Kind} {b : Tm}, s = .tlam k b →
    (∀ B ∈ Γ, Kinded Δ B .star) →
    ∃ B, TypedB (k :: Δ) (Γ.map (Con.rename Nat.succ)) b B ∧ ConBEq Δ (.all k B) T .star := by
  induction h with
  | tlam hb _ =>
    intro k b e hΓ
    cases e
    exact ⟨_, hb, .refl (.all (hb.toTyped.kinded (ctx_shift_kinded hΓ)))⟩
  | conv _ hc ih =>
    intro k b e hΓ
    obtain ⟨B, hb, q⟩ := ih e hΓ
    exact ⟨B, hb, q.trans hc⟩
  | var _ | app _ _ _ _ | lam _ _ _ | tapp _ _ _ => intro _ _ e; cases e

theorem TypedB.inv_tapp (h : TypedB Δ Γ s T) : ∀ {t : Tm} {C : Con}, s = .tapp t C →
    (∀ B ∈ Γ, Kinded Δ B .star) →
    ∃ k B, TypedB Δ Γ t (.all k B) ∧ Kinded Δ C k ∧ ConBEq Δ (B.substOne C) T .star := by
  induction h with
  | tapp ht hC _ =>
    intro t C e hΓ
    cases e
    cases ht.toTyped.kinded hΓ with
    | all hB => exact ⟨_, _, ht, hC, .refl (hB.substOne hC)⟩
  | conv _ hc ih =>
    intro t C e hΓ
    obtain ⟨k, B, h₁, h₂, q⟩ := ih e hΓ
    exact ⟨k, B, h₁, h₂, q.trans hc⟩
  | var _ | app _ _ _ _ | lam _ _ _ | tlam _ _ => intro _ _ e; cases e

/-! ### Annotation change, derived from `eta` and `beta` -/

theorem Tm.subst_rename (t : Tm) : ∀ (σ : ℕ → Tm) (r : ℕ → ℕ),
    (t.rename r).subst σ = t.subst (σ ∘ r) := by
  induction t with
  | var n => intro σ r; rfl
  | app t u iht ihu => intro σ r; exact congrArg₂ Tm.app (iht σ r) (ihu σ r)
  | lam A t ih =>
    intro σ r
    exact congrArg (Tm.lam A) ((ih _ _).trans
      (congrArg (fun f => t.subst f) (funext fun n => by cases n <;> rfl)))
  | tapp t C ih => intro σ r; exact congrArg (fun x => Tm.tapp x C) (ih σ r)
  | tlam k t ih => intro σ r; exact congrArg (Tm.tlam k) (ih _ _)

theorem Tm.rename_lift_succ_substOne (t : Tm) :
    (t.rename (scons 0 (Nat.succ ∘ Nat.succ))).substOne (.var 0) = t := by
  rw [Tm.substOne, Tm.subst_rename]
  have : (scons (Tm.var 0) Tm.var ∘ scons 0 (Nat.succ ∘ Nat.succ)) = Tm.var := by
    funext n; cases n <;> rfl
  rw [this, Tm.subst_var]

/-- Changing a λ-annotation up to `ConEq` is typed equality. -/
theorem TmEq.lamConv (hA : Kinded Δ A .star) (hA' : Kinded Δ A' .star)
    (hAA : ConEq Δ A A' .star) (hb' : Typed Δ (A' :: Γ) b B)
    (hB : Kinded Δ B .star) : TmEq Δ Γ (.lam A b) (.lam A' b) (.arr A B) := by
  have hs : Typed Δ Γ (.lam A' b) (.arr A B) :=
    .conv (.lam hA' hb') (.arr hAA.symm (.refl hB))
  have hb'' : Typed Δ (A' :: A :: Γ) (b.rename (scons 0 (Nat.succ ∘ Nat.succ))) B :=
    hb'.rename (fun n C hn => by cases n <;> simpa using hn)
  have hβ : TmEq Δ (A :: Γ) (.app ((Tm.lam A' b).rename Nat.succ) (.var 0)) b B := by
    have := TmEq.beta hA' hb''
      (.conv (show Typed Δ (A :: Γ) (.var 0) A from .var rfl) hAA)
    rwa [Tm.rename_lift_succ_substOne] at this
  exact (TmEq.lam hA hβ).symm.trans (.eta hA hs)

/-! ### Classification of λω derivations

Over an encoded telescope every derivable `Γ ⊢ t : B` is a kind at `□`, a kinded
constructor at (exactly) the encoding of its kind, or a typed term at (exactly)
the encoding of a well-kinded type, typed with β-only conversion (`TypedB`).
Exactness survives the conversion rule because the target of a conversion is itself classified, and convertible kinded
constructors are `ConBEq` (`Con.conv_reflect`). -/

/-- The three shapes of a λω judgment over an encoded telescope. -/
def PTSClass (T : Tele) (t B : Pseudo CubeSort) : Prop :=
  (∃ k : Kind, k.toPseudo = t ∧ B = .sort .box) ∨
  (∃ (A : Con) (k : Kind), A.toPseudo T.layout = t ∧ B = k.toPseudo ∧ Kinded T.kctx A k) ∨
  (∃ (t' : Tm) (A : Con), t'.toPseudo T.layout = t ∧ B = A.toPseudo T.layout ∧
    TypedB T.kctx T.ctx t' A ∧ Kinded T.kctx A .star)

/-- Generation for λω over encoded telescopes. -/
theorem classify (h : HW Γ t B) : ∀ T : Tele, T.WF → T.toPseudo = Γ → PTSClass T t B := by
  induction h with
  | start hax =>
    intro T _ _
    obtain ⟨rfl, rfl⟩ := hax
    exact Or.inl ⟨.star, rfl, rfl⟩
  | var _ _ =>
    intro T hT hΓ
    cases T with
    | nil => cases hΓ
    | cons e T =>
      cases e with
      | ty k =>
        injection hΓ with h1 h2
        subst h1 h2
        exact Or.inr (Or.inl ⟨.var 0, k, rfl, Kind.toPseudo_rename k _, .var rfl⟩)
      | tm A0 =>
        injection hΓ with h1 h2
        subst h1 h2
        obtain ⟨hA0, _⟩ := hT
        exact Or.inr (Or.inr ⟨.var 0, A0, rfl, (Con.toPseudo_succ_false A0 _).symm,
          .var rfl, hA0⟩)
  | weak _ _ ih₁ _ =>
    intro T hT hΓ
    cases T with
    | nil => cases hΓ
    | cons e T =>
      cases e with
      | ty k =>
        injection hΓ with h1 h2
        subst h1 h2
        rcases ih₁ T hT rfl with ⟨k', rfl, rfl⟩ | ⟨A, k', rfl, rfl, hA⟩ |
          ⟨t', A, rfl, rfl, ht, hA⟩
        · exact Or.inl ⟨k', (Kind.toPseudo_rename k' _).symm, rfl⟩
        · exact Or.inr (Or.inl ⟨A.rename Nat.succ, k', Con.toPseudo_rename_succ_true A _,
            Kind.toPseudo_rename k' _, hA.rename (kren_succ k)⟩)
        · exact Or.inr (Or.inr ⟨t'.tyRename Nat.succ, A.rename Nat.succ,
            Tm.toPseudo_tyRename_succ t' _, (Con.toPseudo_rename_succ_true A _).symm,
            ht.tyRename (kren_succ k), hA.rename (kren_succ k)⟩)
      | tm C0 =>
        injection hΓ with h1 h2
        subst h1 h2
        obtain ⟨_, hT⟩ := hT
        rcases ih₁ T hT rfl with ⟨k', rfl, rfl⟩ | ⟨A, k', rfl, rfl, hA⟩ |
          ⟨t', A, rfl, rfl, ht, hA⟩
        · exact Or.inl ⟨k', (Kind.toPseudo_rename k' _).symm, rfl⟩
        · exact Or.inr (Or.inl ⟨A, k', Con.toPseudo_succ_false A _,
            Kind.toPseudo_rename k' _, hA⟩)
        · exact Or.inr (Or.inr ⟨t'.rename Nat.succ, A, Tm.toPseudo_rename_succ t' _,
            (Con.toPseudo_succ_false A _).symm,
            ht.rename (fun n B hn => by simpa [Tele.ctx] using hn), hA⟩)
  | pi _ _ hr ih₁ ih₂ =>
    intro T hT hΓ
    subst hΓ
    obtain ⟨rfl, hr⟩ := hr
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨_, _, hc⟩
    · rcases ih₁ T hT rfl with ⟨_, _, h⟩ | ⟨A0, k0, rfl, hk, hA0⟩ | ⟨_, A1, _, h, _, _⟩
      · cases h
      · obtain ⟨rfl, -⟩ := Kind.eq_star_of_toPseudo hk.symm
        rcases ih₂ (.tm A0 :: T) ⟨hA0, hT⟩ rfl with ⟨_, _, h⟩ | ⟨B0, k1, rfl, hk1, hB0⟩ |
          ⟨_, A2, _, h, _, _⟩
        · cases h
        · obtain ⟨rfl, -⟩ := Kind.eq_star_of_toPseudo hk1.symm
          exact Or.inr (Or.inl ⟨.arr A0 B0, .star, rfl, rfl, .arr hA0 hB0⟩)
        · exact absurd h.symm (Con.toPseudo_ne_sort A2 _ _)
      · exact absurd h.symm (Con.toPseudo_ne_sort A1 _ _)
    · rcases ih₁ T hT rfl with ⟨k0, rfl, _⟩ | ⟨_, k1, _, hk, _⟩ | ⟨_, A1, _, h, _, _⟩
      · rcases ih₂ (.ty k0 :: T) hT rfl with ⟨_, _, h⟩ | ⟨B0, k1, rfl, hk1, hB0⟩ |
          ⟨_, A2, _, h, _, _⟩
        · cases h
        · obtain ⟨rfl, -⟩ := Kind.eq_star_of_toPseudo hk1.symm
          exact Or.inr (Or.inl ⟨.all k0 B0, .star, rfl, rfl, .all hB0⟩)
        · exact absurd h.symm (Con.toPseudo_ne_sort A2 _ _)
      · exact absurd hk.symm (Kind.toPseudo_ne_box k1)
      · exact absurd h.symm (Con.toPseudo_ne_sort A1 _ _)
    · rcases ih₁ T hT rfl with ⟨k0, rfl, _⟩ | ⟨_, k1, _, hk, _⟩ | ⟨_, A1, _, h, _, _⟩
      · rcases ih₂ (.ty k0 :: T) hT rfl with ⟨l0, rfl, _⟩ | ⟨_, k2, _, hk2, _⟩ |
          ⟨_, A2, _, h, _, _⟩
        · exact Or.inl ⟨.arr k0 l0, rfl, rfl⟩
        · exact absurd hk2.symm (Kind.toPseudo_ne_box k2)
        · exact absurd h.symm (Con.toPseudo_ne_sort A2 _ _)
      · exact absurd hk.symm (Kind.toPseudo_ne_box k1)
      · exact absurd h.symm (Con.toPseudo_ne_sort A1 _ _)
    · exact absurd hc (by decide)
  | lam _ _ ih₁ ih₂ =>
    intro T hT hΓ
    subst hΓ
    rcases ih₂ T hT rfl with ⟨kf, hkf, _⟩ | ⟨F, kF, hF, hkF, hFk⟩ | ⟨_, A1, _, h, _, _⟩
    · cases kf with
      | star => cases hkf
      | arr k0 l0 =>
        injection hkf with e1 e2
        subst e1 e2
        rcases ih₁ (.ty k0 :: T) hT rfl with ⟨_, _, h⟩ | ⟨b0, l1, rfl, hl, hb0⟩ |
          ⟨_, A2, _, h, _, _⟩
        · exact absurd h (Kind.toPseudo_ne_box l0)
        · have e := Kind.toPseudo_inj _ _ hl
          subst e
          exact Or.inr (Or.inl ⟨.lam k0 b0, .arr k0 l0, rfl, rfl, .lam hb0⟩)
        · exact absurd h.symm (Con.toPseudo_ne_kind l0 A2 _)
    · obtain ⟨rfl, rfl⟩ := Kind.eq_star_of_toPseudo hkF.symm
      cases F with
      | arr X Y =>
        injection hF with e1 e2
        subst e1 e2
        cases hFk with
        | arr hX hY =>
          rcases ih₁ (.tm X :: T) ⟨hX, hT⟩ rfl with ⟨_, _, h⟩ | ⟨_, k2, _, h, _⟩ |
            ⟨b0, A2, rfl, hY', hb, _⟩
          · exact absurd h (Con.toPseudo_ne_sort Y _ _)
          · exact absurd h (Con.toPseudo_ne_kind k2 Y _)
          · have e := Con.toPseudo_inj _ _ _ hY'
            subst e
            exact Or.inr (Or.inr ⟨.lam X b0, .arr X Y, rfl, rfl, .lam hX hb, .arr hX hY⟩)
      | all k0 Y =>
        injection hF with e1 e2
        subst e1 e2
        cases hFk with
        | all hY =>
          rcases ih₁ (.ty k0 :: T) hT rfl with ⟨_, _, h⟩ | ⟨_, k2, _, h, _⟩ |
            ⟨b0, A2, rfl, hY', hb, _⟩
          · exact absurd h (Con.toPseudo_ne_sort Y _ _)
          · exact absurd h (Con.toPseudo_ne_kind k2 Y _)
          · have e := Con.toPseudo_inj _ _ _ hY'
            subst e
            exact Or.inr (Or.inr ⟨.tlam k0 b0, .all k0 Y, rfl, rfl, .tlam hb, .all hY⟩)
      | var _ => cases hF
      | lam _ _ => cases hF
      | app _ _ => cases hF
    · exact absurd h.symm (Con.toPseudo_ne_sort A1 _ _)
  | app _ _ ih₁ ih₂ =>
    intro T hT hΓ
    subst hΓ
    rcases ih₁ T hT rfl with ⟨_, _, h⟩ | ⟨F, kF, rfl, hk, hF⟩ | ⟨f0, F, rfl, hFe, hf, hFk⟩
    · cases h
    · cases kF with
      | star => cases hk
      | arr k1 l1 =>
        injection hk with e1 e2
        subst e1 e2
        rcases ih₂ T hT rfl with ⟨_, _, h⟩ | ⟨a0, k2, rfl, hk2, ha⟩ | ⟨_, A2, _, h, _, _⟩
        · exact absurd h (Kind.toPseudo_ne_box k1)
        · have e := Kind.toPseudo_inj _ _ hk2
          subst e
          exact Or.inr (Or.inl ⟨.app F a0, l1, rfl, Kind.toPseudo_substOne l1 _, .app hF ha⟩)
        · exact absurd h.symm (Con.toPseudo_ne_kind k1 A2 _)
    · cases F with
      | arr X Y =>
        injection hFe with e1 e2
        subst e1 e2
        cases hFk with
        | arr hX hY =>
          rcases ih₂ T hT rfl with ⟨_, _, h⟩ | ⟨_, k2, _, h, _⟩ | ⟨a0, A2, rfl, hX', ha, _⟩
          · exact absurd h (Con.toPseudo_ne_sort X _ _)
          · exact absurd h (Con.toPseudo_ne_kind k2 X _)
          · have e := Con.toPseudo_inj _ _ _ hX'
            subst e
            exact Or.inr (Or.inr ⟨.app f0 a0, Y, rfl, Con.toPseudo_false_substOne Y _ _,
              .app hf ha, hY⟩)
      | all k0 Y =>
        injection hFe with e1 e2
        subst e1 e2
        cases hFk with
        | all hY =>
          rcases ih₂ T hT rfl with ⟨_, _, h⟩ | ⟨C, k2, rfl, hk2, hC⟩ | ⟨_, A2, _, h, _, _⟩
          · exact absurd h (Kind.toPseudo_ne_box k0)
          · have e := Kind.toPseudo_inj _ _ hk2
            subst e
            exact Or.inr (Or.inr ⟨.tapp f0 C, Y.substOne C, rfl,
              (Con.toPseudo_substOne Y C _).symm, .tapp hf hC, hY.substOne hC⟩)
          · exact absurd h.symm (Con.toPseudo_ne_kind k0 A2 _)
      | var _ => cases hFe
      | lam _ _ => cases hFe
      | app _ _ => cases hFe
  | conv _ hc _ ih₁ ih₃ =>
    intro T hT hΓ
    rcases ih₁ T hT hΓ with ⟨k, rfl, rfl⟩ | ⟨A0, k, rfl, rfl, hA0⟩ | ⟨t', A0, rfl, rfl, ht, hA0⟩
    · rcases ih₃ T hT hΓ with ⟨l, rfl, _⟩ | ⟨B0, l, rfl, _, hB0⟩ | ⟨_, A2, _, h, _, _⟩
      · exact absurd (hc.eq_of_noRedex trivial (Kind.noRedex_toPseudo l)).symm
          (Kind.toPseudo_ne_box l)
      · exact (Con.not_conv_sort hB0 .box hc.symm).elim
      · exact absurd h.symm (Con.toPseudo_ne_sort A2 _ _)
    · rcases ih₃ T hT hΓ with ⟨l, rfl, _⟩ | ⟨B0, l, rfl, _, hB0⟩ | ⟨_, A2, _, h, _, _⟩
      · have e := Kind.toPseudo_inj _ _
          (hc.eq_of_noRedex (Kind.noRedex_toPseudo k) (Kind.noRedex_toPseudo l))
        subst e
        exact Or.inr (Or.inl ⟨A0, k, rfl, rfl, hA0⟩)
      · exact (Con.not_conv_kind hB0 k hc.symm).elim
      · exact absurd h.symm (Con.toPseudo_ne_sort A2 _ _)
    · rcases ih₃ T hT hΓ with ⟨l, rfl, _⟩ | ⟨B0, l, rfl, hl, hB0⟩ | ⟨_, A2, _, h, _, _⟩
      · exact (Con.not_conv_kind hA0 l hc).elim
      · obtain ⟨rfl, rfl⟩ := Kind.eq_star_of_toPseudo hl.symm
        exact Or.inr (Or.inr ⟨t', B0, rfl, rfl,
          .conv ht (Con.conv_reflect hc hA0 hB0), hB0⟩)
      · exact absurd h.symm (Con.toPseudo_ne_sort A2 _ _)

/-- A bounded decoding of a derivable λω typing is a β-only Fω typing. -/
theorem typedB_of_decode {T : Tele} (hT : T.WF) {t : Tm} {A : Con}
    (h : HW T.toPseudo (t.toPseudo T.layout) (A.toPseudo T.layout))
    (ht : ∀ m, t.TyFreeIn m → m < T.kctx.length) : TypedB T.kctx T.ctx t A := by
  rcases classify h T hT rfl with ⟨k, e, _⟩ | ⟨_, k, _, e, _⟩ | ⟨t', A', e, e', ht', _⟩
  · exact absurd e.symm (Tm.toPseudo_ne_kind t _ k)
  · exact absurd e (Con.toPseudo_ne_kind k A _)
  · have e₁ : t' = t := Tm.toPseudo_inj_bnd t' t _
      (fun m hm => by rw [← Tele.kctx_length]; exact ht'.toTyped.bounded m hm)
      (fun m hm => by rw [← Tele.kctx_length]; exact ht m hm) e
    subst e₁
    have e₂ : A = A' := Con.toPseudo_inj A A' _ e'
    subst e₂
    exact ht'

/-- A bounded decoding of a derivable λω typing is an Fω typing. -/
theorem typed_of_decode {T : Tele} (hT : T.WF) {t : Tm} {A : Con}
    (h : HW T.toPseudo (t.toPseudo T.layout) (A.toPseudo T.layout))
    (ht : ∀ m, t.TyFreeIn m → m < T.kctx.length) : Typed T.kctx T.ctx t A :=
  (typedB_of_decode hT h ht).toTyped

/-! ### Reduction of term encodings

Parallel reduction of the encoding of a `TypedB` term is typed equality and
preserves `TypedB` (subject reduction). Generation for `TypedB` only needs
injectivity and disjointness of `→` and `∀` under `ConBEq`, which follow from
Church–Rosser for `Pseudo.Conv`. -/

theorem Tm.par_reflect {p v : Pseudo CubeSort} (h : Pseudo.Par p v) :
    ∀ (t : Tm) (L : Layout) (Δ : KCtx) (Γ : Ctx) (A : Con), t.toPseudo L = p →
    TypedB Δ Γ t A → (∀ B ∈ Γ, Kinded Δ B .star) →
    ∃ t' : Tm, t'.toPseudo L = v ∧ TmEq Δ Γ t t' A ∧ TypedB Δ Γ t' A := by
  induction h with
  | sort s => intro t L Δ Γ A e _ _; exact absurd e (Tm.toPseudo_ne_sort t L s)
  | var n => intro t L Δ Γ A e ht _; exact ⟨t, e, .refl ht.toTyped, ht⟩
  | pi _ _ _ _ => intro t L Δ Γ A e _ _; cases t <;> simp [Tm.toPseudo] at e
  | app _ ha ih₁ ih₂ =>
    intro t L Δ Γ A e ht hΓ
    cases t with
    | app t₁ t₂ =>
      injection e with e₁ e₂
      obtain ⟨X, Y, h₁, h₂, q⟩ := ht.inv_app rfl hΓ
      obtain ⟨t₁', r₁, q₁, k₁⟩ := ih₁ t₁ L Δ Γ _ e₁ h₁ hΓ
      obtain ⟨t₂', r₂, q₂, k₂⟩ := ih₂ t₂ L Δ Γ _ e₂ h₂ hΓ
      exact ⟨.app t₁' t₂', by subst r₁ r₂; rfl, .conv (.app q₁ q₂) q.toConEq,
        .conv (.app k₁ k₂) q⟩
    | tapp t₁ C =>
      injection e with e₁ e₂
      obtain ⟨k, B, h₁, hC, q⟩ := ht.inv_tapp rfl hΓ
      have hB : Kinded (k :: Δ) B .star := by
        cases h₁.toTyped.kinded hΓ with
        | all hB => exact hB
      obtain ⟨t₁', r₁, q₁, k₁⟩ := ih₁ t₁ L Δ Γ _ e₁ h₁ hΓ
      obtain ⟨C', r₂, qC⟩ := Con.par_reflect ha C L Δ k e₂ hC
      refine ⟨.tapp t₁' C', by subst r₁ r₂; rfl, ?_, ?_⟩
      · exact .conv ((TmEq.tapp q₁ hC).trans (.tappConv k₁.toTyped qC.toConEq)) q.toConEq
      · exact .conv (.tapp k₁ qC.kinded_right)
          ((ConBEq.substOne_congr (.refl hB) qC.symm).trans q)
    | var _ | lam _ _ | tlam _ _ => simp [Tm.toPseudo] at e
  | lam hX _ _ ihb =>
    intro t L Δ Γ A e ht hΓ
    cases t with
    | lam A₀ b₀ =>
      injection e with e₁ e₂
      obtain ⟨hA₀, B, hb₀, q⟩ := ht.inv_lam rfl hΓ
      obtain ⟨A₀', r₁, qA⟩ := Con.par_reflect hX A₀ L Δ .star e₁ hA₀
      obtain ⟨b₀', r₂, qb, kb⟩ :=
        ihb b₀ (false :: L) Δ (A₀ :: Γ) B e₂ hb₀ (ctx_cons_kinded hA₀ hΓ)
      have hB : Kinded Δ B .star := hb₀.toTyped.kinded (ctx_cons_kinded hA₀ hΓ)
      have kb' : TypedB Δ (A₀' :: Γ) b₀' B := kb.ctxConv (fun n C hn => by
        cases n with
        | zero =>
          simp at hn
          subst hn
          exact ⟨A₀', rfl, qA.symm⟩
        | succ n =>
          exact ⟨C, by simpa using hn,
            .refl (hΓ C (List.mem_iff_getElem?.mpr ⟨n, by simpa using hn⟩))⟩)
      refine ⟨.lam A₀' b₀', by subst r₁ r₂; rfl, ?_, ?_⟩
      · exact .conv ((TmEq.lam hA₀ qb).trans
          (TmEq.lamConv hA₀ qA.kinded_right qA.toConEq kb'.toTyped hB)) q.toConEq
      · exact .conv (.conv (.lam qA.kinded_right kb') (.arr qA.symm (.refl hB))) q
    | tlam k b₀ =>
      injection e with e₁ e₂
      subst e₁
      have e₃ := hX.eq_of_noRedex (Kind.noRedex_toPseudo k)
      subst e₃
      obtain ⟨B, hb₀, q⟩ := ht.inv_tlam rfl hΓ
      obtain ⟨b₀', r₂, qb, kb⟩ :=
        ihb b₀ (true :: L) (k :: Δ) _ B e₂ hb₀ (ctx_shift_kinded hΓ)
      exact ⟨.tlam k b₀', by subst r₂; rfl, .conv (.tlam qb) q.toConEq, .conv (.tlam kb) q⟩
    | var _ | app _ _ | tapp _ _ => simp [Tm.toPseudo] at e
  | beta _ _ ha ihb iha =>
    intro t L Δ Γ A e ht hΓ
    cases t with
    | app t₁ t₂ =>
      injection e with e₁ e₂
      obtain ⟨X₁, Y₁, h₁, h₂, q⟩ := ht.inv_app rfl hΓ
      cases t₁ with
      | lam A₀ b₀ =>
        injection e₁ with e₃ e₄
        obtain ⟨hA₀, B, hb₀, q₁⟩ := h₁.inv_lam rfl hΓ
        obtain ⟨qX, qY⟩ := q₁.arr_inj
        obtain ⟨b₀', r₁, qb, kb⟩ :=
          ihb b₀ (false :: L) Δ (A₀ :: Γ) B e₄ hb₀ (ctx_cons_kinded hA₀ hΓ)
        obtain ⟨t₂', r₂, q₂, k₂⟩ := iha t₂ L Δ Γ X₁ e₂ h₂ hΓ
        subst r₁ r₂
        refine ⟨b₀'.substOne t₂', Tm.toPseudo_substOne _ _ _, ?_, ?_⟩
        · exact .conv ((TmEq.app (.conv (.lam hA₀ qb) q₁.toConEq) q₂).trans
            (.conv (.beta hA₀ kb.toTyped (.conv k₂.toTyped qX.symm.toConEq)) qY.toConEq))
            q.toConEq
        · exact .conv (.conv (kb.substOne (.conv k₂ qX.symm)) qY) q
      | tlam k b₀ =>
        obtain ⟨B, _, q₁⟩ := h₁.inv_tlam rfl hΓ
        exact q₁.symm.arr_ne_all.elim
      | var _ | app _ _ | tapp _ _ => simp [Tm.toPseudo] at e₁
    | tapp t₁ C =>
      injection e with e₁ e₂
      obtain ⟨k, B, h₁, hC, q⟩ := ht.inv_tapp rfl hΓ
      cases t₁ with
      | tlam k₀ b₀ =>
        injection e₁ with e₃ e₄
        obtain ⟨B', hb₀, q₁⟩ := h₁.inv_tlam rfl hΓ
        obtain ⟨rfl, qB⟩ := q₁.all_inj
        obtain ⟨b₀', r₁, qb, kb⟩ := ihb b₀ (true :: L) _ _ B' e₄ hb₀ (ctx_shift_kinded hΓ)
        obtain ⟨C', r₂, qC⟩ := Con.par_reflect ha C L Δ _ e₂ hC
        subst r₁ r₂
        refine ⟨b₀'.tySubstOne C', Tm.toPseudo_tySubstOne _ _ _, ?_, ?_⟩
        · exact .conv ((((TmEq.tapp (.conv (.tlam qb) (ConBEq.all qB).toConEq) hC).trans
            (.tappConv (.conv (.tlam kb.toTyped) (ConBEq.all qB).toConEq) qC.toConEq)).trans
            (.conv (.tbeta kb.toTyped qC.kinded_right)
              (ConBEq.substOne_congr qB qC.symm).toConEq))) q.toConEq
        · exact .conv (.conv (kb.tySubstOne qC.kinded_right)
            (ConBEq.substOne_congr qB qC.symm)) q
      | lam A₀ b₀ =>
        obtain ⟨_, B', _, q₁⟩ := h₁.inv_lam rfl hΓ
        exact q₁.arr_ne_all.elim
      | var _ | app _ _ | tapp _ _ => simp [Tm.toPseudo] at e₁
    | var _ | lam _ _ | tlam _ _ => simp [Tm.toPseudo] at e

theorem Tm.reflTransGen_par_reflect {L : Layout} {t : Tm} {v : Pseudo CubeSort} {Δ : KCtx}
    {Γ : Ctx} {A : Con} (h : Relation.ReflTransGen Pseudo.Par (t.toPseudo L) v)
    (ht : TypedB Δ Γ t A) (hΓ : ∀ B ∈ Γ, Kinded Δ B .star) :
    ∃ t' : Tm, t'.toPseudo L = v ∧ TmEq Δ Γ t t' A ∧ TypedB Δ Γ t' A := by
  induction h with
  | refl => exact ⟨t, rfl, .refl ht.toTyped, ht⟩
  | tail _ hp ih =>
    obtain ⟨t', rfl, q, kt⟩ := ih
    obtain ⟨t'', r, q', kt'⟩ := Tm.par_reflect hp t' L Δ Γ A rfl kt hΓ
    exact ⟨t'', r, q.trans q', kt'⟩

/-- Untyped β-conversion between encodings of β-only typed Fω terms is typed equality. -/
theorem conv_reflectB {T : Tele} (hT : T.WF) {t u : Tm} {A : Con}
    (ht : TypedB T.kctx T.ctx t A) (hu : TypedB T.kctx T.ctx u A)
    (h : Pseudo.Conv (t.toPseudo T.layout) (u.toPseudo T.layout)) :
    TmEq T.kctx T.ctx t u A := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  obtain ⟨t', r₁, q₁, k₁⟩ := Tm.reflTransGen_par_reflect h₁ ht hT.ctx_kinded
  obtain ⟨u', r₂, q₂, k₂⟩ := Tm.reflTransGen_par_reflect h₂ hu hT.ctx_kinded
  have e : t' = u' := Tm.toPseudo_inj_bnd t' u' _
    (fun m hm => by rw [← Tele.kctx_length]; exact k₁.toTyped.bounded m hm)
    (fun m hm => by rw [← Tele.kctx_length]; exact k₂.toTyped.bounded m hm) (r₁.trans r₂.symm)
  subst e
  exact q₁.trans q₂.symm

/-- Reflection for the λω corner. -/
theorem reflect {T : Tele} (hT : T.WF)
    (h : HasType Corner.systemFOmega.specification T.toPseudo t B)
    (hB : HasType Corner.systemFOmega.specification T.toPseudo B (.sort .star)) :
    ∃ t' A', t'.toPseudo T.layout = t ∧ A'.toPseudo T.layout = B ∧
      Typed T.kctx T.ctx t' A' := by
  rcases classify h T hT rfl with ⟨k, rfl, rfl⟩ | ⟨A, k, rfl, rfl, _⟩ |
    ⟨t', A', rfl, rfl, ht, _⟩
  · rcases classify hB T hT rfl with ⟨_, _, e⟩ | ⟨A, _, e, _, _⟩ | ⟨t', _, e, _, _, _⟩
    · cases e
    · exact absurd e (Con.toPseudo_ne_sort A _ _)
    · exact absurd e (Tm.toPseudo_ne_sort t' _ _)
  · rcases classify hB T hT rfl with ⟨_, _, e⟩ | ⟨A2, _, e, _, _⟩ | ⟨t'', _, e, _, _, _⟩
    · cases e
    · exact absurd e (Con.toPseudo_ne_kind k A2 _)
    · exact absurd e (Tm.toPseudo_ne_kind t'' _ k)
  · exact ⟨t', A', rfl, rfl, ht.toTyped⟩

/-- Satisfaction of PTS judgments in the Fω PER model over `M`. -/
-- Decodings are raw and bounded by the telescope; no typing proof is assumed.
-- The bounds distinguish type and term binders in the shared index space.
def Sat (M : CombAlg.{0}) : PTSJudgment → Prop
  | .typing Γ t B => ∀ (T : Tele) (t' : Tm) (A : Con), T.WF → T.toPseudo = Γ →
      t'.toPseudo T.layout = t → A.toPseudo T.layout = B →
      (∀ m, t'.TyFreeIn m → m < T.kctx.length) → Valid M T.kctx T.ctx t' A
  | .equation Γ t u B => ∀ (T : Tele) (t' u' : Tm) (A : Con), T.WF → T.toPseudo = Γ →
      t'.toPseudo T.layout = t → u'.toPseudo T.layout = u → A.toPseudo T.layout = B →
      (∀ m, t'.TyFreeIn m → m < T.kctx.length) → (∀ m, u'.TyFreeIn m → m < T.kctx.length) →
      ValidEq M T.kctx T.ctx t' u' A

/-- Soundness: bounded decodings of derivations are `TypedB` (`typedB_of_decode`);
then `Typed.sound`, and for equations `conv_reflectB` and `TmEq.sound`. -/
theorem sat_sound {j : PTSJudgment} (h : j.Derivable Corner.systemFOmega) (M : CombAlg.{0}) :
    Sat M j := by
  cases j with
  | typing Γ t B =>
    simp only [Sat]
    intro T t' A hT hΓ ht hA hbt
    subst hΓ ht hA
    exact (typed_of_decode hT h hbt).sound hT.ctx_kinded
  | equation Γ t u B =>
    simp only [Sat]
    intro T t' u' A hT hΓ ht hu hA hbt hbu
    subst hΓ ht hu hA
    obtain ⟨h₁, h₂, hc⟩ := h
    exact (conv_reflectB hT (typedB_of_decode hT h₁ hbt) (typedB_of_decode hT h₂ hbu) hc).sound
      hT.ctx_kinded

/-- The PER models of Fω as semantics of the λω corner. -/
def systemFOmegaSemantics : SystemFOmegaSemantics where
  Model := Discrete CombAlg.{0}
  sat X j := Sat X.as j
  sound h X := sat_sound h X.as

end SystemFOmega

end Silmaril.Calculi.LambdaCube.PERModel
