module

public import Silmaril.Games.Zip.Thms
public import Silmaril.Games.Div.Thms

/-!
# Coherent re-association of increasing interactions

The witnesses of `Zip.assoc` are not unique, so re-associating each stage of
an increasing chain of interactions separately does not give an increasing
chain. We re-associate *increments* instead:

* `zip_append`: interactions concatenate.
* `zip_drop`: if `Zip s t p` and `Zip (s ++ ds) (t ++ dt) (p ++ dp)`, then
  `Zip ds dt dp`: the increments of nested interactions interact. (The
  derivation of the smaller interaction is a prefix of that of the larger.)
* `stepA`/`stepB`: one step of the construction, on lists only: extend a
  re-associated interaction along an increment of the outer interaction and
  a matching increment of a source interaction, using `Zip.assoc` on the
  increments only. When the new outer stage covers the whole source stage,
  the whole source stage is used.
* `mergeA`/`mergeB`: by dependent choice, an increasing chain of outer
  interactions whose hidden side is covered by an increasing chain of
  source interactions is re-associated into increasing chains.
-/

public section

namespace Silmaril.Proofs.Games.DivComp

open Silmaril.Games

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

theorem zip_append {s s' : List (α ⊕ β)} {t t' : List (β ⊕ γ)} {p p' : List (α ⊕ γ)}
    (h : Zip s t p) (h' : Zip s' t' p') : Zip (s ++ s') (t ++ t') (p ++ p') := by
  induction h with
  | nil => simpa using h'
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

private theorem drop_left {a : α} {S : List (α ⊕ β)} {T : List (β ⊕ γ)} {P : List (α ⊕ γ)}
    (h : Zip (.inl a :: S) T (.inl a :: P)) : Zip S T P := by
  obtain ⟨cs, t', p', ht, hp, h'⟩ := Zip.inl_left h
  cases cs with
  | nil =>
    have hp' : P = p' := (List.cons.inj hp).2
    rw [ht, hp']
    exact h'
  | cons c cs => simp at hp

private theorem drop_right {c : γ} {S : List (α ⊕ β)} {T : List (β ⊕ γ)} {P : List (α ⊕ γ)}
    (h : Zip S (.inr c :: T) (.inr c :: P)) : Zip S T P := by
  obtain ⟨as, s', p', hs, hp, h'⟩ := Zip.inr_right h
  cases as with
  | nil =>
    have hp' : P = p' := (List.cons.inj hp).2
    rw [hs, hp']
    exact h'
  | cons a as => simp at hp

private theorem drop_sync {b : β} {S : List (α ⊕ β)} {T : List (β ⊕ γ)} {P : List (α ⊕ γ)}
    (h : Zip (.inr b :: S) (.inl b :: T) P) : Zip S T P := by
  obtain ⟨cs, t', p', ht, hp, h'⟩ := Zip.inr_left h
  cases cs with
  | nil =>
    have ht' : T = t' := (List.cons.inj ht).2
    rw [ht', hp]
    exact h'
  | cons c cs => simp at ht

theorem zip_drop {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    ∀ {ds dt dp}, Zip (s ++ ds) (t ++ dt) (p ++ dp) → Zip ds dt dp := by
  induction h with
  | nil => exact fun h => by simpa using h
  | left a _ ih => exact fun h => ih (drop_left h)
  | right c _ ih => exact fun h => ih (drop_right h)
  | sync b _ ih => exact fun h => ih (drop_sync h)

/-- A sub-increment of the source covering an outer increment; the whole
source increment when the outer increment covers it. -/
private theorem pick {dS : List (α ⊕ β)} {dT : List (β ⊕ γ)} {dW du : List (α ⊕ γ)}
    (hd : Zip dS dT dW) (hdu : du <+: dW) : ∃ ds dt, ds <+: dS ∧ dt <+: dT ∧ Zip ds dt du ∧
      (du = dW → ds = dS ∧ dt = dT) := by
  by_cases he : du = dW
  · rw [he]
    exact ⟨dS, dT, List.prefix_refl _, List.prefix_refl _, hd, fun _ => ⟨rfl, rfl⟩⟩
  · obtain ⟨ds, dt, h₁, h₂, h₃⟩ := Zip.of_prefix hd hdu
    exact ⟨ds, dt, h₁, h₂, h₃, fun h => (he h).elim⟩

/-- One step of re-association `(σ;τ);ρ ↦ σ;(τ;ρ)`. -/
theorem stepA {s' : List (α ⊕ β)} {t' : List (β ⊕ γ)} {u : List (α ⊕ γ)} {r : List (γ ⊕ δ)}
    {v : List (β ⊕ δ)} {p : List (α ⊕ δ)} {S : List (α ⊕ β)} {T : List (β ⊕ γ)}
    {W u₁ : List (α ⊕ γ)} {r₁ : List (γ ⊕ δ)} {p₁ : List (α ⊕ δ)}
    (hst : Zip s' t' u) (htr : Zip t' r v) (hsv : Zip s' v p) (hur : Zip u r p)
    (hZ : Zip S T W) (hS : s' <+: S) (hT : t' <+: T) (hW : u₁ <+: W)
    (hu : u <+: u₁) (hr : r <+: r₁) (hp : p <+: p₁) (h₁ : Zip u₁ r₁ p₁) :
    ∃ s'' t'' v'', s' <+: s'' ∧ s'' <+: S ∧ t' <+: t'' ∧ t'' <+: T ∧ v <+: v'' ∧
      Zip s'' t'' u₁ ∧ Zip t'' r₁ v'' ∧ Zip s'' v'' p₁ ∧ (u₁ = W → s'' = S ∧ t'' = T) := by
  obtain ⟨dS, hdS⟩ : ∃ dS, s' ++ dS = S := hS
  obtain ⟨dT, hdT⟩ : ∃ dT, t' ++ dT = T := hT
  obtain ⟨dW, hdW⟩ : ∃ dW, u ++ dW = W := hu.trans hW
  obtain ⟨du, hdu₀⟩ : ∃ du, u ++ du = u₁ := hu
  obtain ⟨dr, hdr⟩ : ∃ dr, r ++ dr = r₁ := hr
  obtain ⟨dp, hdp⟩ : ∃ dp, p ++ dp = p₁ := hp
  have hd : Zip dS dT dW := zip_drop hst (by rw [hdS, hdT, hdW]; exact hZ)
  have hdu : du <+: dW := (List.prefix_append_right_inj u).1 (by rw [hdu₀, hdW]; exact hW)
  have ho : Zip du dr dp := zip_drop hur (by rw [hdu₀, hdr, hdp]; exact h₁)
  obtain ⟨ds, dt, hds, hdt, hz, hmax⟩ := pick hd hdu
  obtain ⟨dv, e₁, e₂⟩ : ∃ dv, Zip dt dr dv ∧ Zip ds dv dp := Zip.assoc.1 ⟨du, hz, ho⟩
  have hfin : u₁ = W → s' ++ ds = S ∧ t' ++ dt = T := fun h => by
    have he : du = dW := List.append_cancel_left (hdu₀.trans (h.trans hdW.symm))
    rw [← hdS, ← hdT, (hmax he).1, (hmax he).2]
    exact ⟨rfl, rfl⟩
  refine ⟨s' ++ ds, t' ++ dt, v ++ dv, List.prefix_append _ _, ?_, List.prefix_append _ _, ?_,
    List.prefix_append _ _, ?_, ?_, ?_, hfin⟩
  · exact hdS ▸ (List.prefix_append_right_inj s').2 hds
  · exact hdT ▸ (List.prefix_append_right_inj t').2 hdt
  · exact hdu₀ ▸ zip_append hst hz
  · exact hdr ▸ zip_append htr e₁
  · exact hdp ▸ zip_append hsv e₂

/-- One step of re-association `σ;(τ;ρ) ↦ (σ;τ);ρ`. -/
theorem stepB {s : List (α ⊕ β)} {t' : List (β ⊕ γ)} {u' : List (α ⊕ γ)} {r' : List (γ ⊕ δ)}
    {v : List (β ⊕ δ)} {p : List (α ⊕ δ)} {T : List (β ⊕ γ)} {R : List (γ ⊕ δ)}
    {Y v₁ : List (β ⊕ δ)} {s₁ : List (α ⊕ β)} {p₁ : List (α ⊕ δ)}
    (htr : Zip t' r' v) (hst : Zip s t' u') (hur : Zip u' r' p) (hsv : Zip s v p)
    (hZ : Zip T R Y) (hT : t' <+: T) (hR : r' <+: R) (hY : v₁ <+: Y)
    (hs : s <+: s₁) (hv : v <+: v₁) (hp : p <+: p₁) (h₁ : Zip s₁ v₁ p₁) :
    ∃ t'' r'' u'', t' <+: t'' ∧ t'' <+: T ∧ r' <+: r'' ∧ r'' <+: R ∧ u' <+: u'' ∧
      Zip t'' r'' v₁ ∧ Zip s₁ t'' u'' ∧ Zip u'' r'' p₁ ∧ (v₁ = Y → t'' = T ∧ r'' = R) := by
  obtain ⟨dT, hdT⟩ : ∃ dT, t' ++ dT = T := hT
  obtain ⟨dR, hdR⟩ : ∃ dR, r' ++ dR = R := hR
  obtain ⟨dY, hdY⟩ : ∃ dY, v ++ dY = Y := hv.trans hY
  obtain ⟨dv, hdv₀⟩ : ∃ dv, v ++ dv = v₁ := hv
  obtain ⟨ds, hds⟩ : ∃ ds, s ++ ds = s₁ := hs
  obtain ⟨dp, hdp⟩ : ∃ dp, p ++ dp = p₁ := hp
  have hd : Zip dT dR dY := zip_drop htr (by rw [hdT, hdR, hdY]; exact hZ)
  have hdv : dv <+: dY := (List.prefix_append_right_inj v).1 (by rw [hdv₀, hdY]; exact hY)
  have ho : Zip ds dv dp := zip_drop hsv (by rw [hds, hdv₀, hdp]; exact h₁)
  obtain ⟨dt, dr, hdt, hdr, hz, hmax⟩ := pick hd hdv
  obtain ⟨du, e₁, e₂⟩ : ∃ du, Zip ds dt du ∧ Zip du dr dp := Zip.assoc.2 ⟨dv, hz, ho⟩
  have hfin : v₁ = Y → t' ++ dt = T ∧ r' ++ dr = R := fun h => by
    have he : dv = dY := List.append_cancel_left (hdv₀.trans (h.trans hdY.symm))
    rw [← hdT, ← hdR, (hmax he).1, (hmax he).2]
    exact ⟨rfl, rfl⟩
  refine ⟨t' ++ dt, r' ++ dr, u' ++ du, List.prefix_append _ _, ?_, List.prefix_append _ _, ?_,
    List.prefix_append _ _, ?_, ?_, ?_, hfin⟩
  · exact hdT ▸ (List.prefix_append_right_inj t').2 hdt
  · exact hdR ▸ (List.prefix_append_right_inj r').2 hdr
  · exact hdv₀ ▸ zip_append htr hz
  · exact hds ▸ zip_append hst e₁
  · exact hdp ▸ zip_append hur e₂

/-- A monotone index sequence above `c` and the identity. -/
private theorem exists_index (c : ℕ → ℕ) :
    ∃ M : ℕ → ℕ, (∀ n, M n ≤ M (n + 1)) ∧ (∀ n, n ≤ M n) ∧ ∀ n, c n ≤ M n := by
  refine ⟨fun n => Nat.rec (max (c 0) 0) (fun k Mk => max Mk (max (c (k + 1)) (k + 1))) n,
    fun n => le_max_left _ _, fun n => ?_, fun n => ?_⟩
  · cases n with
    | zero => exact Nat.zero_le _
    | succ n => exact (le_max_right _ _).trans (le_max_right _ _)
  · cases n with
    | zero => exact le_max_left _ _
    | succ n => exact (le_max_left _ _).trans (le_max_right _ _)

private theorem mono_index {M : ℕ → ℕ} (h : ∀ n, M n ≤ M (n + 1)) {n m : ℕ} (hnm : n ≤ m) :
    M n ≤ M m := by
  induction hnm with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (h _)

/-- **Re-association of chains** `(σ;τ);ρ ↦ σ;(τ;ρ)`. -/
theorem mergeA {u : Chain (α ⊕ γ)} {r : Chain (γ ⊕ δ)} {p : Chain (α ⊕ δ)}
    (hz : ∀ n, Zip (u n) (r n) (p n)) (hmu : u.Mono) (hmr : r.Mono) (hmp : p.Mono)
    {S : Chain (α ⊕ β)} {T : Chain (β ⊕ γ)} {W : Chain (α ⊕ γ)}
    (hZ : ∀ m, Zip (S m) (T m) (W m)) (hmS : S.Mono) (hmT : T.Mono) (hmW : W.Mono)
    (hcov : ∀ n, ∃ m, u n <+: W m) :
    ∃ (s' : Chain (α ⊕ β)) (t' : Chain (β ⊕ γ)) (v' : Chain (β ⊕ δ)) (M : ℕ → ℕ),
      s'.Mono ∧ t'.Mono ∧ v'.Mono ∧ ∀ n, Zip (s' n) (t' n) (u n) ∧ Zip (t' n) (r n) (v' n) ∧
        Zip (s' n) (v' n) (p n) ∧ s' n <+: S (M n) ∧ t' n <+: T (M n) ∧ n ≤ M n ∧
        (u n = W (M n) → s' n = S (M n) ∧ t' n = T (M n)) := by
  choose c hc using hcov
  obtain ⟨M, hMs, hMn, hcM⟩ := exists_index c
  have hW : ∀ n, u n <+: W (M n) := fun n => (hc n).trans (hmW.le (hcM n))
  let P : ℕ → List (α ⊕ β) × List (β ⊕ γ) × List (β ⊕ δ) → Prop := fun n x =>
    Zip x.1 x.2.1 (u n) ∧ Zip x.2.1 (r n) x.2.2 ∧ Zip x.1 x.2.2 (p n) ∧ x.1 <+: S (M n) ∧
      x.2.1 <+: T (M n) ∧ (u n = W (M n) → x.1 = S (M n) ∧ x.2.1 = T (M n))
  have base : ∃ x, P 0 x := by
    obtain ⟨s'', t'', v'', -, h₂, -, h₄, -, h₆, h₇, h₈, h₉⟩ :=
      stepA (s' := []) (t' := []) (u := []) (r := []) (v := []) (p := []) .nil .nil .nil .nil
        (hZ (M 0)) List.nil_prefix List.nil_prefix (hW 0) List.nil_prefix List.nil_prefix
        List.nil_prefix (hz 0)
    exact ⟨(s'', t'', v''), h₆, h₇, h₈, h₂, h₄, h₉⟩
  have step : ∀ n x, P n x → ∃ x', P (n + 1) x' ∧ x.1 <+: x'.1 ∧ x.2.1 <+: x'.2.1 ∧
      x.2.2 <+: x'.2.2 := by
    rintro n ⟨a, b, d⟩ ⟨h₁, h₂, h₃, h₄, h₅, -⟩
    obtain ⟨s'', t'', v'', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
      stepA h₁ h₂ h₃ (hz n) (hZ (M (n + 1))) (h₄.trans (hmS.le (hMs n)))
        (h₅.trans (hmT.le (hMs n))) (hW (n + 1)) (hmu n) (hmr n) (hmp n) (hz (n + 1))
    exact ⟨(s'', t'', v''), ⟨e₆, e₇, e₈, e₂, e₄, e₉⟩, e₁, e₃, e₅⟩
  choose! nxt hnxt using step
  obtain ⟨x₀, hx₀⟩ := base
  let X : ℕ → List (α ⊕ β) × List (β ⊕ γ) × List (β ⊕ δ) :=
    fun n => Nat.rec x₀ (fun k x => nxt k x) n
  have hX : ∀ n, P n (X n) := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => exact (hnxt n (X n) ih).1
  refine ⟨fun n => (X n).1, fun n => (X n).2.1, fun n => (X n).2.2, M,
    fun n => (hnxt n (X n) (hX n)).2.1, fun n => (hnxt n (X n) (hX n)).2.2.1,
    fun n => (hnxt n (X n) (hX n)).2.2.2, fun n => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hX n
  exact ⟨h₁, h₂, h₃, h₄, h₅, hMn n, h₆⟩

/-- **Re-association of chains** `σ;(τ;ρ) ↦ (σ;τ);ρ`. -/
theorem mergeB {s : Chain (α ⊕ β)} {v : Chain (β ⊕ δ)} {p : Chain (α ⊕ δ)}
    (hz : ∀ n, Zip (s n) (v n) (p n)) (hms : s.Mono) (hmv : v.Mono) (hmp : p.Mono)
    {T : Chain (β ⊕ γ)} {R : Chain (γ ⊕ δ)} {Y : Chain (β ⊕ δ)}
    (hZ : ∀ m, Zip (T m) (R m) (Y m)) (hmT : T.Mono) (hmR : R.Mono) (hmY : Y.Mono)
    (hcov : ∀ n, ∃ m, v n <+: Y m) :
    ∃ (t' : Chain (β ⊕ γ)) (r' : Chain (γ ⊕ δ)) (u' : Chain (α ⊕ γ)) (M : ℕ → ℕ),
      t'.Mono ∧ r'.Mono ∧ u'.Mono ∧ ∀ n, Zip (t' n) (r' n) (v n) ∧ Zip (s n) (t' n) (u' n) ∧
        Zip (u' n) (r' n) (p n) ∧ t' n <+: T (M n) ∧ r' n <+: R (M n) ∧ n ≤ M n ∧
        (v n = Y (M n) → t' n = T (M n) ∧ r' n = R (M n)) := by
  choose c hc using hcov
  obtain ⟨M, hMs, hMn, hcM⟩ := exists_index c
  have hY : ∀ n, v n <+: Y (M n) := fun n => (hc n).trans (hmY.le (hcM n))
  let P : ℕ → List (β ⊕ γ) × List (γ ⊕ δ) × List (α ⊕ γ) → Prop := fun n x =>
    Zip x.1 x.2.1 (v n) ∧ Zip (s n) x.1 x.2.2 ∧ Zip x.2.2 x.2.1 (p n) ∧ x.1 <+: T (M n) ∧
      x.2.1 <+: R (M n) ∧ (v n = Y (M n) → x.1 = T (M n) ∧ x.2.1 = R (M n))
  have base : ∃ x, P 0 x := by
    obtain ⟨t'', r'', u'', -, h₂, -, h₄, -, h₆, h₇, h₈, h₉⟩ :=
      stepB (s := []) (t' := []) (u' := []) (r' := []) (v := []) (p := []) .nil .nil .nil .nil
        (hZ (M 0)) List.nil_prefix List.nil_prefix (hY 0) List.nil_prefix List.nil_prefix
        List.nil_prefix (hz 0)
    exact ⟨(t'', r'', u''), h₆, h₇, h₈, h₂, h₄, h₉⟩
  have step : ∀ n x, P n x → ∃ x', P (n + 1) x' ∧ x.1 <+: x'.1 ∧ x.2.1 <+: x'.2.1 ∧
      x.2.2 <+: x'.2.2 := by
    rintro n ⟨a, b, d⟩ ⟨h₁, h₂, h₃, h₄, h₅, -⟩
    obtain ⟨t'', r'', u'', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
      stepB h₁ h₂ h₃ (hz n) (hZ (M (n + 1))) (h₄.trans (hmT.le (hMs n)))
        (h₅.trans (hmR.le (hMs n))) (hY (n + 1)) (hms n) (hmv n) (hmp n) (hz (n + 1))
    exact ⟨(t'', r'', u''), ⟨e₆, e₇, e₈, e₂, e₄, e₉⟩, e₁, e₃, e₅⟩
  choose! nxt hnxt using step
  obtain ⟨x₀, hx₀⟩ := base
  let X : ℕ → List (β ⊕ γ) × List (γ ⊕ δ) × List (α ⊕ γ) :=
    fun n => Nat.rec x₀ (fun k x => nxt k x) n
  have hX : ∀ n, P n (X n) := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => exact (hnxt n (X n) ih).1
  refine ⟨fun n => (X n).1, fun n => (X n).2.1, fun n => (X n).2.2, M,
    fun n => (hnxt n (X n) (hX n)).2.1, fun n => (hnxt n (X n) (hX n)).2.2.1,
    fun n => (hnxt n (X n) (hX n)).2.2.2, fun n => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hX n
  exact ⟨h₁, h₂, h₃, h₄, h₅, hMn n, h₆⟩

end Silmaril.Proofs.Games.DivComp
