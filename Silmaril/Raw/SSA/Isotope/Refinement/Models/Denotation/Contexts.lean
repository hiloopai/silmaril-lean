module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Category
public import Silmaril.Raw.SSA.Isotope.Refinement.ContextWeakening

@[expose] public section

/-! # Interpreting quantitative contexts

Unused slots are omitted from the packed type. Context maps use the chosen
pure copy, discard, and coherence operations of the categorical model.
-/

namespace Silmaril.Isotope.Refinement.Models

universe u v w r
open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem effect_mono {e e' : ε} {A B : τ} {f : M.Hom A B}
    (h : e ≤ e') (hf : M.hasEffect e f) : M.hasEffect e' f := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.mono h hf

theorem identity_effect (e : ε) (A : τ) : M.hasEffect e (M.identity A) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.id e A

theorem compose_effect {e : ε} {A B D : τ} {f : M.Hom A B} {g : M.Hom B D}
    (hf : M.hasEffect e f) (hg : M.hasEffect e g) : M.hasEffect e (M.compose f g) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp hf hg

theorem eqToHom_effect {A B : τ} (h : A = B) (e : ε) :
    M.hasEffect e (@eqToHom τ M.category.toCategoryStruct A B h) := by
  subst B
  exact M.identity_effect e A

theorem left_effect {e : ε} (A : τ) {B D : τ} {f : M.Hom B D}
    (hf : M.hasEffect e f) : M.hasEffect e (M.left A f) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.eqToHom_effect _ _) (M.effects.comp (M.effects.whiskerLeft A hf) (M.eqToHom_effect _ _))

theorem right_effect {e : ε} {A B : τ} {f : M.Hom A B} (D : τ)
    (hf : M.hasEffect e f) : M.hasEffect e (M.right f D) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.eqToHom_effect _ _) (M.effects.comp (M.effects.whiskerRight D hf) (M.eqToHom_effect _ _))

theorem discard_pure (A : τ) (h : Quantity.affine ≤ quantity A) :
    M.hasEffect ⊥ (M.discard A h) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.copyDiscard.discard_pure A h) (M.eqToHom_effect _ _)

theorem copy_pure (A : τ) (h : Quantity.relevant ≤ quantity A) :
    M.hasEffect ⊥ (M.copy A h) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.copyDiscard.copy_pure A h) (M.eqToHom_effect _ _)

theorem associator_pure (A B D : τ) : M.hasEffect ⊥ (M.associator A B D) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.eqToHom_effect _ _) (M.effects.comp (M.effects.associator A B D) (M.eqToHom_effect _ _))
theorem associatorInv_pure (A B D : τ) : M.hasEffect ⊥ (M.associatorInv A B D) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.eqToHom_effect _ _) (M.effects.comp (M.effects.associator_inv A B D) (M.eqToHom_effect _ _))
theorem leftUnitor_pure (A : τ) : M.hasEffect ⊥ (M.leftUnitor A) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.eqToHom_effect _ _) (M.effects.leftUnitor A)
theorem rightUnitor_pure (A : τ) : M.hasEffect ⊥ (M.rightUnitor A) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.eqToHom_effect _ _) (M.effects.rightUnitor A)
theorem leftUnitorInv_pure (A : τ) : M.hasEffect ⊥ (M.leftUnitorInv A) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.effects.leftUnitor_inv A) (M.eqToHom_effect _ _)
theorem rightUnitorInv_pure (A : τ) : M.hasEffect ⊥ (M.rightUnitorInv A) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.effects.rightUnitor_inv A) (M.eqToHom_effect _ _)
theorem braiding_pure (A B : τ) : M.hasEffect ⊥ (M.braiding A B) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.effects.comp (M.eqToHom_effect _ _) (M.effects.comp (M.effects.braiding A B) (M.eqToHom_effect _ _))
theorem tensor_effect {e : ε} {A B D E : τ} {f : M.Hom A B} {g : M.Hom D E}
    (hf : M.hasEffect e f) (hg : M.hasEffect e g) : M.hasEffect e (M.tensor f g) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.compose_effect (M.right_effect D hf) (M.left_effect B hg)
theorem middleSwap_pure (A B D E : τ) : M.hasEffect ⊥ (M.middleSwap A B D E) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  exact M.compose_effect (M.associator_pure _ _ _)
    (M.compose_effect (M.left_effect _ (M.associatorInv_pure _ _ _))
      (M.compose_effect (M.left_effect _ (M.right_effect _ (M.braiding_pure _ _)))
        (M.compose_effect (M.left_effect _ (M.associator_pure _ _ _)) (M.associatorInv_pure _ _ _))))
end SeqData

namespace Denotation

/-- Pack the retained variables, oldest first; a zero-usage slot contributes no object. -/
def packed : {n : Nat} → QCtx τ n → τ
  | 0, _ => Silmaril.unit
  | n + 1, Γ => match (Γ 0).2 with
    | .zero => packed (fun i : Fin n => Γ i.succ)
    | .used _ => product (packed (fun i : Fin n => Γ i.succ)) (Γ 0).1

omit [TypeQuantity τ] in
@[simp] theorem packed_nil : packed (QCtx.nil : QCtx τ 0) = Silmaril.unit := rfl
omit [TypeQuantity τ] in
@[simp] theorem packed_snoc_zero {n : Nat} (Γ : QCtx τ n) (A : τ) :
    packed (Γ.snoc A .zero) = packed Γ := rfl
omit [TypeQuantity τ] in
@[simp] theorem packed_snoc_used {n : Nat} (Γ : QCtx τ n) (A : τ) (q : Quantity) :
    packed (Γ.snoc A (.used q)) = product (packed Γ) A := rfl

/-- Usage can restrict a retained type further, so packing gives an inequality. -/
theorem packed_quantity {n : Nat} (Γ : QCtx τ n) : Γ.linearity ≤ quantity (packed Γ) := by
  induction n with
  | zero => simpa [packed, TypeQuantity.unit_quantity] using (le_top : Γ.linearity ≤ (⊤ : Quantity))
  | succ n ih =>
    have ht : Γ.linearity ≤ QCtx.linearity (fun i : Fin n => Γ i.succ) := by
      rw [QCtx.le_linearity_iff]
      intro i
      exact QCtx.le_linearity_iff.mp le_rfl i.succ
    have hz := QCtx.le_linearity_iff.mp (le_refl Γ.linearity) 0
    cases he : (Γ 0).2 with
    | zero => simpa [packed, he] using ht.trans (ih (fun i => Γ i.succ))
    | used q =>
      simp only [he, Usage.linearity_used] at hz
      simpa [packed, he, TypeQuantity.product_quantity] using
        le_inf (ht.trans (ih (fun i => Γ i.succ))) (hz.trans inf_le_left)

theorem discardable_quantity {n : Nat} {Γ : QCtx τ n} (h : Γ.Discardable) :
    Quantity.affine ≤ quantity (packed Γ) := by
  apply le_trans _ (packed_quantity Γ)
  rw [QCtx.le_linearity_iff]
  intro i
  exact (Usage.zero_le_effective_iff _ _).mp (h i)

variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- The model's chosen discard, justified by all retained variable quantities. -/
def discard {n : Nat} {Γ : QCtx τ n} (h : Γ.Discardable) : M.Hom (packed Γ) Silmaril.unit :=
  M.discard (packed Γ) (discardable_quantity h)

theorem discard_pure {n : Nat} {Γ : QCtx τ n} (h : Γ.Discardable) :
    M.hasEffect ⊥ (discard M h) := M.discard_pure _ _

/-- A context map with its purity certificate. -/
abbrev PureHom (A B : τ) := {f : M.Hom A B // M.hasEffect ⊥ f}

def pureCompose {A B D : τ} (f : PureHom M A B) (g : PureHom M B D) :
    PureHom M A D := ⟨M.compose f.1 g.1, M.compose_effect f.2 g.2⟩
def pureTensor {A B D E : τ} (f : PureHom M A B) (g : PureHom M D E) :
    PureHom M (product A D) (product B E) := ⟨M.tensor f.1 g.1, M.tensor_effect f.2 g.2⟩
def pureRight {A B : τ} (f : PureHom M A B) (D : τ) :
    PureHom M (product A D) (product B D) := ⟨M.right f.1 D, M.right_effect D f.2⟩
def pureLeft (A : τ) {B D : τ} (f : PureHom M B D) :
    PureHom M (product A B) (product A D) := ⟨M.left A f.1, M.left_effect A f.2⟩

def retain (L A : τ) : Usage → τ
  | .zero => L
  | .used _ => product L A

def splitSlot {L B D A : τ} (f : PureHom M L (product B D))
    {q ql qr : Usage} (h : QCtx.SlotSplit A q ql qr) :
    PureHom M (retain L A q) (product (retain B A ql) (retain D A qr)) := by
  cases q <;> cases ql <;> cases qr
  · exact f
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact pureCompose M (pureRight M f A)
      ⟨M.associator B D A, M.associator_pure B D A⟩
  · exact pureCompose M (pureRight M f A)
      (pureCompose M ⟨M.associator B D A, M.associator_pure B D A⟩
        (pureCompose M (pureLeft M B ⟨M.braiding D A, M.braiding_pure D A⟩)
          ⟨M.associatorInv B A D, M.associatorInv_pure B A D⟩))
  · have hc : Quantity.relevant ≤ quantity A := by
      cases h with
      | both h => exact ((Usage.relevant_le_effective_iff _ _).mp h).1.trans inf_le_left
    exact pureCompose M (pureTensor M f ⟨M.copy A hc, M.copy_pure A hc⟩)
      ⟨M.middleSwap B D A A, M.middleSwap_pure B D A A⟩

def splitPure {n : Nat} {Γ Γl Γr : QCtx τ n} (h : QCtx.Split Γ Γl Γr) :
    PureHom M (packed Γ) (product (packed Γl) (packed Γr)) := by
  induction n with
  | zero => exact ⟨M.leftUnitorInv Silmaril.unit, M.leftUnitorInv_pure Silmaril.unit⟩
  | succ n ih =>
    let Γt : QCtx τ n := fun i => Γ i.succ
    let Γlt : QCtx τ n := fun i => Γl i.succ
    let Γrt : QCtx τ n := fun i => Γr i.succ
    have ht : QCtx.Split Γt Γlt Γrt := fun i => h i.succ
    have hl := (h 0).1
    have hr := (h 0).2.1
    have hs := (h 0).2.2
    have hm := splitSlot M (ih ht) hs
    simpa only [packed, hl, hr, retain] using hm

/-- Split retained variables with the chosen copy maps and pure tensor coherence. -/
def split {n : Nat} {Γ Γl Γr : QCtx τ n} (h : QCtx.Split Γ Γl Γr) :
    M.Hom (packed Γ) (product (packed Γl) (packed Γr)) := (splitPure M h).1

theorem split_pure {n : Nat} {Γ Γl Γr : QCtx τ n} (h : QCtx.Split Γ Γl Γr) :
    M.hasEffect ⊥ (split M h) := (splitPure M h).2

def dropRight {L B : τ} (f : PureHom M L B) (A : τ)
    (h : Quantity.affine ≤ quantity A) : PureHom M (product L A) B :=
  pureCompose M (pureRight M f A)
    (pureCompose M (pureLeft M B ⟨M.discard A h, M.discard_pure A h⟩)
      ⟨M.rightUnitor B, M.rightUnitor_pure B⟩)

def variablePure {n : Nat} {Γ : QCtx τ n} (i : Fin n) (h : Γ.VarAllowed i) :
    PureHom M (packed Γ) (Γ i).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      have ht : QCtx.Discardable (fun j : Fin n => Γ j.succ) :=
        fun j => h.2 j.succ (Fin.succ_ne_zero _)
      cases he : (Γ 0).2 with
      | zero =>
        have hf := h.1
        simp only [QCtx.effective, he, Usage.effective_zero, Usage.effective_linear] at hf
        exact False.elim hf
      | used q =>
        simpa only [packed, he] using
          pureCompose M (pureRight M ⟨discard M ht, discard_pure M ht⟩ (Γ 0).1)
            ⟨M.leftUnitor (Γ 0).1, M.leftUnitor_pure (Γ 0).1⟩
    | succ i =>
      have ht : QCtx.VarAllowed (fun j : Fin n => Γ j.succ) i :=
        ⟨h.1, fun j hj => h.2 j.succ (fun he => hj (Fin.succ_injective _ he))⟩
      have hz := h.2 0 (Ne.symm (Fin.succ_ne_zero i))
      cases he : (Γ 0).2 with
      | zero => simpa only [packed, he] using ih i ht
      | used q =>
        have ha : Quantity.affine ≤ quantity (Γ 0).1 := by
          have hb := (Usage.zero_le_effective_iff _ _).mp hz
          simp only [he, Usage.linearity_used] at hb
          exact hb.trans inf_le_left
        simpa only [packed, he] using dropRight M (ih i ht) (Γ 0).1 ha

/-- Select an allowed variable and discard exactly the other retained slots. -/
def «variable» {n : Nat} {Γ : QCtx τ n} (i : Fin n) (h : Γ.VarAllowed i) :
    M.Hom (packed Γ) (Γ i).1 := (variablePure M i h).1

theorem variable_pure {n : Nat} {Γ : QCtx τ n} (i : Fin n) (h : Γ.VarAllowed i) :
    M.hasEffect ⊥ («variable» M i h) := (variablePure M i h).2

/-- Remove an omitted newest source slot from the ordered index embedding. -/
theorem weakening_skip_tail {n m : Nat} {Γ : QCtx τ (n + 1)} {Δ : QCtx τ m}
    {ρ : Fin m → Fin (n + 1)} (h : QCtx.Weakening Γ Δ ρ) (hn : ∀ i, ρ i ≠ 0) :
    QCtx.Weakening (fun i : Fin n => Γ i.succ) Δ (fun i => (ρ i).pred (hn i)) := by
  cases h with
  | cons => exact False.elim (hn 0 rfl)
  | skip h _ => simpa using h

/-- If the newest target slot is not newest in the source, the source slot is omitted. -/
theorem weakening_ne_zero {n m : Nat} {Γ : QCtx τ (n + 1)} {Δ : QCtx τ (m + 1)}
    {ρ : Fin (m + 1) → Fin (n + 1)} (h : QCtx.Weakening Γ Δ ρ) (h0 : ρ 0 ≠ 0) :
    ∀ i, ρ i ≠ 0 := by
  cases h with
  | cons => exact False.elim (h0 rfl)
  | skip => exact fun i => Fin.succ_ne_zero _

theorem weakening_succ_ne_zero {n m : Nat} {Γ : QCtx τ (n + 1)} {Δ : QCtx τ (m + 1)}
    {ρ : Fin (m + 1) → Fin (n + 1)} (h : QCtx.Weakening Γ Δ ρ) (h0 : ρ 0 = 0)
    (i : Fin m) : ρ i.succ ≠ 0 := by
  intro hi
  exact Fin.succ_ne_zero i (h.injective (hi.trans h0.symm))

/-- Remove the retained newest slot from both sides of a weakening. -/
theorem weakening_cons_tail {n m : Nat} {Γ : QCtx τ (n + 1)} {Δ : QCtx τ (m + 1)}
    {ρ : Fin (m + 1) → Fin (n + 1)} (h : QCtx.Weakening Γ Δ ρ) (h0 : ρ 0 = 0) :
    QCtx.Weakening (fun i : Fin n => Γ i.succ) (fun i : Fin m => Δ i.succ)
      (fun i => (ρ i.succ).pred (weakening_succ_ne_zero h h0 i)) := by
  cases h with
  | cons h _ => simpa using h
  | skip => exact False.elim (Fin.succ_ne_zero _ h0)

/-- Interpret quantity restriction of a retained slot, possibly discarding it. -/
def weakenSlot {L B A : τ} (f : PureHom M L B) {q q' : Usage}
    (h : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A)) :
    PureHom M (retain L A q) (retain B A q') := by
  cases q with
  | zero =>
    cases q' with
    | zero => exact f
    | used q' => exact False.elim h
  | used q =>
    cases q' with
    | zero =>
      have ha := (Usage.zero_le_effective_iff _ _).mp h
      exact dropRight M f A (ha.trans inf_le_left)
    | used q' => exact pureRight M f A

/-- Structural recursion is on the source context, never on its proof in `Prop`. -/
def weakenPure {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
    (h : QCtx.Weakening Γ Δ ρ) : PureHom M (packed Γ) (packed Δ) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact ⟨M.identity _, M.identity_effect _ _⟩
    | succ m => exact Fin.elim0 (ρ 0)
  | succ n ih =>
    cases m with
    | zero =>
      exact ⟨discard M (fun i => h.omitted i (fun j => Fin.elim0 j)), discard_pure M _⟩
    | succ m =>
      by_cases h0 : ρ 0 = 0
      · have ht := weakening_cons_tail h h0
        have he : (Γ 0).1 = (Δ 0).1 := by simpa only [h0] using h.types 0
        have hq : Usage.effective (Δ 0).2 (quantity (Γ 0).1) ≤
            Usage.effective (Γ 0).2 (quantity (Γ 0).1) := by
          simpa only [QCtx.effective, h0, he] using h.effective_le 0
        have hf := weakenSlot M (ih ht) hq
        simpa only [packed, retain, he] using hf
      · have hn := weakening_ne_zero h h0
        have ht := weakening_skip_tail h hn
        have hd := h.omitted 0 hn
        cases he : (Γ 0).2 with
        | zero => simpa only [packed, he] using ih ht
        | used q =>
          have ha := (Usage.zero_le_effective_iff _ _).mp hd
          simp only [he, Usage.linearity_used] at ha
          simpa only [packed, he] using dropRight M (ih ht) (Γ 0).1 (ha.trans inf_le_left)

/-- Interpret native weakening by discard and the two tensor actions. -/
def weaken {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
    (h : QCtx.Weakening Γ Δ ρ) : M.Hom (packed Γ) (packed Δ) := (weakenPure M h).1

theorem weaken_pure {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
    (h : QCtx.Weakening Γ Δ ρ) : M.hasEffect ⊥ (weaken M h) := (weakenPure M h).2

/-- Computation on one additional context slot. -/
theorem split_snoc {n : Nat} {Γ Γl Γr : QCtx τ n} (h : QCtx.Split Γ Γl Γr)
    {A : τ} {q ql qr : Usage} (hs : QCtx.SlotSplit A q ql qr) :
    split M (QCtx.Split.snoc h hs) = (splitSlot M (splitPure M h) hs).1 := by
  cases q <;> cases ql <;> cases qr <;> rfl

variable {M} {N : SeqData.{u,v,w,r} τ Φ ε}

/-- Pure context maps are transported by structure-preserving model maps. -/
def mapPure (φ : M.HomMap N) {A B : τ} (f : PureHom M A B) : PureHom N A B :=
  ⟨φ.map f.1, φ.effect f.2⟩

theorem map_discard (φ : M.HomMap N) {n : Nat} {Γ : QCtx τ n} (h : Γ.Discardable) :
    φ.map (discard M h) = discard N h := φ.discard _ _

theorem map_splitSlot (φ : M.HomMap N) {L B D A : τ} (f : PureHom M L (product B D))
    {q ql qr : Usage} (h : QCtx.SlotSplit A q ql qr) :
    φ.map (splitSlot M f h).1 = (splitSlot N (mapPure φ f) h).1 := by
  cases q <;> cases ql <;> cases qr
  all_goals try (solve | cases h)
  all_goals dsimp [retain, PureHom, splitSlot, mapPure, pureCompose, pureRight, pureLeft, pureTensor,
    SeqData.tensor, SeqData.middleSwap]
  all_goals simp only [φ.compose, φ.right, φ.left, φ.associator,
    φ.associatorInv, φ.braiding, φ.copy]


/-- Structure-preserving model maps preserve the interpretation of splitting. -/
theorem map_split (φ : M.HomMap N) {n : Nat} {Γ Γl Γr : QCtx τ n}
    (h : QCtx.Split Γ Γl Γr) : φ.map (split M h) = split N h := by
  induction n with
  | zero => exact φ.leftUnitorInv _
  | succ n ih =>
    let Γt : QCtx τ n := fun i => Γ i.succ
    let Γlt : QCtx τ n := fun i => Γl i.succ
    let Γrt : QCtx τ n := fun i => Γr i.succ
    have ht : QCtx.Split Γt Γlt Γrt := fun i => h i.succ
    have hl : Γlt.snoc (Γ 0).1 (Γl 0).2 = Γl := by
      rw [← (h 0).1]
      exact QCtx.snoc_tail Γl
    have hr : Γrt.snoc (Γ 0).1 (Γr 0).2 = Γr := by
      rw [← (h 0).2.1]
      exact QCtx.snoc_tail Γr
    have hp : mapPure φ (splitPure M ht) = splitPure N ht := Subtype.ext (ih ht)
    have he := map_splitSlot φ (splitPure M ht) (h 0).2.2
    rw [hp] at he
    have hh : φ.map (split M (QCtx.Split.snoc ht (h 0).2.2)) =
        split N (QCtx.Split.snoc ht (h 0).2.2) := by
      change φ.map (splitSlot M (splitPure M ht) (h 0).2.2).1 =
        (splitSlot N (splitPure N ht) (h 0).2.2).1
      exact he
    have hΓ : Γt.snoc (Γ 0).1 (Γ 0).2 = Γ := QCtx.snoc_tail Γ
    have hall : ∀ k : QCtx.Split (Γt.snoc (Γ 0).1 (Γ 0).2)
        (Γlt.snoc (Γ 0).1 (Γl 0).2) (Γrt.snoc (Γ 0).1 (Γr 0).2),
        φ.map (split M k) = split N k := fun _ => hh
    let P (p : QCtx τ (n + 1) × QCtx τ (n + 1) × QCtx τ (n + 1)) :=
      ∀ k : QCtx.Split p.1 p.2.1 p.2.2, φ.map (split M k) = split N k
    have ep := congrArg P (congrArg₂ Prod.mk hΓ (congrArg₂ Prod.mk hl hr))
    exact (ep.mp hall) h

theorem map_dropRight (φ : M.HomMap N) {L B : τ} (f : PureHom M L B) (A : τ)
    (h : Quantity.affine ≤ quantity A) :
    φ.map (dropRight M f A h).1 = (dropRight N (mapPure φ f) A h).1 := by
  dsimp only [dropRight, pureCompose, pureRight, pureLeft, mapPure]
  rw [φ.compose, φ.right, φ.compose, φ.left, φ.discard, φ.rightUnitor]

/-- Variable selection commutes with structure-preserving model maps. -/
theorem map_variable (φ : M.HomMap N) {n : Nat} {Γ : QCtx τ n}
    (i : Fin n) (h : Γ.VarAllowed i) : φ.map («variable» M i h) = «variable» N i h := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hs (Γt : QCtx τ n) (A : τ) (q : Usage) :
        ∀ (j : Fin (n + 1)) (k : (Γt.snoc A q).VarAllowed j),
        φ.map («variable» M j k) = «variable» N j k := by
      intro j k
      cases j using Fin.cases with
      | zero =>
        have ht : Γt.Discardable := fun j => k.2 j.succ (Fin.succ_ne_zero _)
        cases q with
        | zero => exact False.elim k.1
        | used q =>
          change φ.map (M.compose (M.right (discard M ht) A) (M.leftUnitor A)) =
            N.compose (N.right (discard N ht) A) (N.leftUnitor A)
          rw [φ.compose, φ.right, map_discard, φ.leftUnitor]
      | succ j =>
        have ht : Γt.VarAllowed j :=
          ⟨k.1, fun l hl => k.2 l.succ (fun he => hl (Fin.succ_injective _ he))⟩
        cases q with
        | zero => exact ih j ht
        | used q =>
          have ha : Quantity.affine ≤ quantity A :=
            ((Usage.zero_le_effective_iff _ _).mp (k.2 0 (Ne.symm (Fin.succ_ne_zero j)))).trans inf_le_left
          change φ.map (dropRight M (variablePure M j ht) A ha).1 =
            (dropRight N (variablePure N j ht) A ha).1
          rw [map_dropRight]
          have he : mapPure φ (variablePure M j ht) = variablePure N j ht := Subtype.ext (ih j ht)
          rw [he]
    have hall := hs (fun j => Γ j.succ) (Γ 0).1 (Γ 0).2
    let P (G : QCtx τ (n + 1)) := ∀ (j : Fin (n + 1)) (k : G.VarAllowed j),
      φ.map («variable» M j k) = «variable» N j k
    exact ((congrArg P (QCtx.snoc_tail Γ)).mp hall) i h

end Denotation
end Silmaril.Isotope.Refinement.Models
