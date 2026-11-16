module

public import Silmaril.Logic.Consequence.Ax.Defs
public import Silmaril.Logic.Consequence.Thms
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Finset.Dedup

/-!
# Context shapes: what the maps forget

**Injective (forget nothing).** `ctxSingle_injective`, `ctxNamed_injective`,
`ctxSet_injective`.

**Not injective.** `ctxFinset_perm` (order), `ctxFinset_dup` (multiplicity),
`ctxFinset_not_injective`; `ctxRange_not_injective` (names).

**Composites.** `ctxRange_ctxNamed`: the premises named by a list are its members;
`ctxSet_ctxFinset`: likewise through `Finset`. So the two routes from lists to sets agree.

**Weakening orders are respected.** `ctxFinset_mono` (`List.Subset` to `⊆`), `ctxSet_mono`,
`ctxRange_mono` (`NamedLE` to `⊆`), `ctxNamed_mono_of_prefix` (a prefix keeps every named
premise); `NamedLE` is a preorder (`namedLE_refl`, `namedLE_trans`).

**Pullbacks.** `pullback_ctxFinset_perm`, `pullback_ctxFinset_dup`: a list system pulled back from
finite sets cannot distinguish permuted or duplicated contexts. `monoWrt_pullback`: pulling back
along a map that sends one weakening relation into another preserves monotonicity.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v u' w

variable {C : Type u} {N : Type w}

theorem ctxSingle_injective : Function.Injective (ctxSingle (C := C)) :=
  fun _ _ h => by simpa [ctxSingle] using h

theorem ctxNamed_injective : Function.Injective (ctxNamed (C := C)) :=
  fun _ _ h => List.ext_getElem? fun n => congrFun h n

theorem ctxSet_injective : Function.Injective (ctxSet (C := C)) := Finset.coe_injective

theorem ctxFinset_perm [DecidableEq C] {l l' : List C} (h : l.Perm l') :
    ctxFinset l = ctxFinset l' := List.toFinset_eq_of_perm l l' h

theorem ctxFinset_dup [DecidableEq C] (c : C) (l : List C) :
    ctxFinset (c :: c :: l) = ctxFinset (c :: l) := by
  simp [ctxFinset]

theorem ctxFinset_not_injective [DecidableEq C] [Nonempty C] :
    ¬ Function.Injective (ctxFinset (C := C)) := fun h => by
  obtain ⟨c⟩ := ‹Nonempty C›
  exact absurd (h (ctxFinset_dup c [])) (by simp)

theorem ctxRange_not_injective [Nonempty C] : ¬ Function.Injective (ctxRange (N := ℕ) (C := C)) :=
  fun h => by
  obtain ⟨c⟩ := ‹Nonempty C›
  have : ctxRange (fun n : ℕ => if n = 0 then some c else none) =
      ctxRange (fun _ : ℕ => some c) := by
    ext d; simp [ctxRange]
  simpa using congrFun (h this) 1

theorem ctxRange_ctxNamed (l : List C) : ctxRange (ctxNamed l) = {c | c ∈ l} := by
  ext c; simp [ctxRange, ctxNamed, List.mem_iff_getElem?]

theorem ctxSet_ctxFinset [DecidableEq C] (l : List C) : ctxSet (ctxFinset l) = {c | c ∈ l} := by
  ext c; simp [ctxSet, ctxFinset]

theorem ctxFinset_mono [DecidableEq C] {l l' : List C} (h : l ⊆ l') :
    ctxFinset l ⊆ ctxFinset l' := fun c hc => by simp only [ctxFinset, List.mem_toFinset] at hc ⊢; exact h hc

theorem ctxSet_mono {s t : Finset C} (h : s ⊆ t) : ctxSet s ⊆ ctxSet t := Finset.coe_subset.2 h

theorem namedLE_refl (Γ : N → Option C) : NamedLE Γ Γ := fun _ _ h => h

theorem namedLE_trans {Γ Δ Θ : N → Option C} (h₁ : NamedLE Γ Δ) (h₂ : NamedLE Δ Θ) :
    NamedLE Γ Θ := fun n c h => h₂ n c (h₁ n c h)

theorem ctxRange_mono {Γ Δ : N → Option C} (h : NamedLE Γ Δ) : ctxRange Γ ⊆ ctxRange Δ :=
  fun _ ⟨n, hn⟩ => ⟨n, h n _ hn⟩

theorem ctxNamed_mono_of_prefix {l l' : List C} (h : l <+: l') :
    NamedLE (ctxNamed l) (ctxNamed l') := fun n _ hn => by
  obtain ⟨t, rfl⟩ := h
  have hlt : n < l.length := by
    by_contra hc; simp [ctxNamed, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hn
  simpa [ctxNamed, List.getElem?_append_left hlt] using hn

namespace System

variable {Ax : Type v} {Ax' : Type u'}

theorem pullback_ctxFinset_perm [DecidableEq C] (S : FinsetSystem C) {l l' : List C}
    (h : l.Perm l') (c : C) : S.pullback ctxFinset id l c ↔ S.pullback ctxFinset id l' c := by
  simp [ctxFinset_perm h]

theorem pullback_ctxFinset_dup [DecidableEq C] (S : FinsetSystem C) (d : C) (l : List C)
    (c : C) : S.pullback ctxFinset id (d :: d :: l) c ↔ S.pullback ctxFinset id (d :: l) c := by
  simp [ctxFinset_dup]

theorem monoWrt_pullback {S : System Ax C} {r : Ax → Ax → Prop} {r' : Ax' → Ax' → Prop}
    {f : Ax' → Ax} (hf : ∀ a b, r' a b → r (f a) (f b)) (hS : S.MonoWrt r) :
    (S.pullback f id).MonoWrt r' := fun a b hab _ h => hS (hf a b hab) h

end System

end Silmaril.Consequence
