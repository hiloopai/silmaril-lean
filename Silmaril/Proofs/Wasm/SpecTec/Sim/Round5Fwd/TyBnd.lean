module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.Forward

/-!
# Round 5: `tyBnd` is preserved by substitution, unrolling and expansion

Core-level facts about `Round4.tyBnd` (every `_IDX x` below `2 ^ 32`, every
`list(·)` shorter than `2 ^ 32`): substitution by bounded type uses keeps a type bounded
(`tyBnd_subst`), so unrolling a bounded recursive group does (`tyBnd_unrollrt`), and the
expansion of a bounded defined type is bounded (`tyBnd_of_expand`). With `Bounded c` this bounds
every type the forward rules quantify over.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.Wasm.Validation
open Round4 (tyBnd)

/-- Substitution on a sequence is substitution on its elements. -/
theorem toList_subst {k : TKind} (σ : Subst) (l : Ty (.list k)) :
    (l.subst σ).toList = l.toList.map (Ty.subst σ) := by
  rw [← Ty.ofList_toList l]
  generalize l.toList = L
  induction L with
  | nil => rfl
  | cons a L ih => simp [Ty.subst, ih]

/-- Substitution keeps a sequence's length. -/
theorem length_subst {k : TKind} (σ : Subst) (l : Ty (.list k)) :
    (l.subst σ).toList.length = l.toList.length := by
  rw [toList_subst, List.length_map]

/-- A substitution whose every image is bounded. -/
def SubstBnd (σ : Subst) : Prop := ∀ v u, σ v = some u → tyBnd u = true

/-- Removing the recursion variables keeps a substitution bounded. -/
theorem SubstBnd.minusRecs {σ : Subst} (h : SubstBnd σ) : SubstBnd σ.minusRecs := by
  intro v u hv
  cases v with
  | idx x => exact h _ _ hv
  | recv i => simp [Subst.minusRecs] at hv

/-- **Substitution by bounded type uses keeps a type bounded.** -/
theorem tyBnd_subst {k : TKind} (t : Ty k) {σ : Subst} (hσ : SubstBnd σ)
    (ht : tyBnd t = true) : tyBnd (t.subst σ) = true := by
  induction t generalizing σ with
  | nil => rfl
  | cons a l iha ihl =>
    have h : tyBnd a = true ∧ tyBnd l = true := by simpa only [tyBnd, Bool.and_eq_true] using ht
    simp only [Ty.subst, tyBnd, iha hσ h.1, ihl hσ h.2, Bool.and_self]
  | idx x =>
    show tyBnd ((σ (.idx x)).getD (.idx x)) = true
    cases hv : σ (.idx x) with
    | none => exact ht
    | some u => exact hσ _ _ hv
  | recv i =>
    show tyBnd ((σ (.recv i)).getD (.recv i)) = true
    cases hv : σ (.recv i) with
    | none => rfl
    | some u => exact hσ _ _ hv
  | dt d ih => exact ih hσ ht
  | defn g i ih => exact ih hσ ht
  | abs a => rfl
  | bot => rfl
  | use u ih => exact ih hσ ht
  | ref n h ih => exact ih hσ ht
  | num t => rfl
  | vec t => rfl
  | refv r ih => exact ih hσ ht
  | botv => rfl
  | val t ih => exact ih hσ ht
  | pack p => rfl
  | field m s ih => exact ih hσ ht
  | struct fs ih =>
    have h : fs.toList.length < Round4.bnd32 ∧ tyBnd fs = true := by
      simpa only [tyBnd, Bool.and_eq_true, decide_eq_true_eq] using ht
    simp only [Ty.subst, tyBnd, length_subst, h.1, ih hσ h.2, decide_true, Bool.and_self]
  | array f ih => exact ih hσ ht
  | func ps rs ihp ihr =>
    have h : ((ps.toList.length < Round4.bnd32 ∧ rs.toList.length < Round4.bnd32) ∧
        tyBnd ps = true) ∧ tyBnd rs = true := by
      simpa only [tyBnd, Bool.and_eq_true, decide_eq_true_eq] using ht
    simp only [Ty.subst, tyBnd, length_subst, h.1.1.1, h.1.1.2, ihp hσ h.1.2, ihr hσ h.2,
      decide_true, Bool.and_self]
  | sub fin sups b ihs ihb =>
    have h : tyBnd sups = true ∧ tyBnd b = true := by
      simpa only [tyBnd, Bool.and_eq_true] using ht
    simp only [Ty.subst, tyBnd, ihs hσ h.1, ihb hσ h.2, Bool.and_self]
  | group subs ih =>
    have h : subs.toList.length < Round4.bnd32 ∧ tyBnd subs = true := by
      simpa only [tyBnd, Bool.and_eq_true, decide_eq_true_eq] using ht
    simp only [Ty.subst, tyBnd, length_subst, h.1, ih hσ.minusRecs h.2, decide_true,
      Bool.and_self]

/-- An element of a bounded sequence is bounded. -/
theorem tyBnd_of_mem {k : TKind} {l : Ty (.list k)} (hl : tyBnd l = true) {a : Ty k}
    (ha : a ∈ l.toList) : tyBnd a = true := by
  rw [← Ty.ofList_toList l] at hl
  generalize l.toList = L at hl ha
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    simp only [Ty.ofList_cons, tyBnd, Bool.and_eq_true] at hl
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hl.1
    · exact ih hl.2 ha

/-- Unrolling a bounded recursive group keeps it bounded. -/
theorem tyBnd_unrollrt {rt : CRecType} (h : tyBnd rt = true) : tyBnd (unrollrt rt) = true := by
  cases rt with
  | group subs =>
    simp only [tyBnd, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [unrollrt, tyBnd, length_subst, h.1, decide_true, Bool.true_and]
    refine tyBnd_subst subs ?_ h.2
    intro v u hv
    cases v with
    | idx x => simp at hv
    | recv i =>
      simp only at hv
      split at hv
      · cases hv
        simp only [tyBnd, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h.1, h.2⟩
      · cases hv

/-- The unrolled subtype of a bounded defined type is bounded. -/
theorem tyBnd_unrolldt {d : DefType} {st : CSubType} (hd : tyBnd d = true)
    (h : unrolldt d = some st) : tyBnd st = true := by
  cases d with
  | defn rt i =>
    have hrt : tyBnd (unrollrt rt) = true := tyBnd_unrollrt hd
    have hmem : st ∈ (unrollrt rt).subs.toList := List.mem_of_getElem? h
    cases hu : unrollrt rt with
    | group subs =>
      rw [hu] at hrt hmem
      simp only [tyBnd, Bool.and_eq_true] at hrt
      exact tyBnd_of_mem hrt.2 hmem

/-- **The expansion of a bounded defined type is bounded**, and so are its declared
supertypes. -/
theorem tyBnd_of_unrolldt {d : DefType} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (hd : tyBnd d = true) (h : unrolldt d = some (.sub fin sups ct)) :
    tyBnd sups = true ∧ tyBnd ct = true := by
  have hs : tyBnd (Ty.sub fin sups ct) = true := tyBnd_unrolldt hd h
  simpa only [tyBnd, Bool.and_eq_true] using hs

/-- **The expansion of a bounded defined type is bounded.** -/
theorem tyBnd_of_expand {d : DefType} {ct : CCompType} (hd : tyBnd d = true) (h : Expand d ct) :
    tyBnd ct = true := by
  obtain ⟨hu⟩ := h
  exact (tyBnd_of_unrolldt hd hu).2

/-- The parameter and result types of a bounded function type are bounded. -/
theorem tyBnd_func {ps rs : Ty (.list .val)} (h : tyBnd (Ty.func ps rs) = true) :
    tyBnd ps = true ∧ tyBnd rs = true := by
  simp only [tyBnd, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
