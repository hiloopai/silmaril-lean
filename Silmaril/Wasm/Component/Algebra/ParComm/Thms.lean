module

public import Silmaril.Wasm.Component.Algebra.Par.Thms
public import Silmaril.Games.PairMap.Thms
import all Silmaril.Wasm.Component.Algebra.Par.Thms

/-!
# Independent instantiation is commutative

* **`par_comm`** (and `task_par_comm : ParCommLaw`): `par c₁ c₂` is equivalent to `par c₂ c₁`
  with its imports re-read (`reimport … (swapIdx n₁ n₂)`) and its exports re-selected in the
  original order (`select (unswapIdx k₁ k₂)`), for every core semantics `C`.
* **`denU_par_pair`**: the strategy of `par c₁ c₂` is the **pairing** (`Strategy.pair`) of its
  two instances, each composed with its own wiring of the imports, split at the `k₁` exports of
  the first (`splitH k₁`) and masked to `k₁ + k₂` exports. The component semantics builds the
  two instances one after the other (`ext`: the second sees an environment that already
  contains the first); `ext_comp_pair_shiftH` shows that, since the second only uses the
  stateless import environment, the two run side by side. Its game-level ingredient is the
  functoriality of pairing (`Strategy.pair_comp_cross`, `Silmaril.Games.PairMap`).
* Then `par_comm` is the symmetry of pairing (`Strategy.pair_comp_ofHom_swap`,
  `Silmaril.Games.PairSwap`) plus handler equations: `swapIdx_comp_pair` (the re-read imports give
  each instance its original wiring) and `swap_split_select` (exchanging the sides, splitting at
  `k₂` and re-selecting is splitting at `k₁`).

Handler lemmas: `splitH_comp_shiftH_add`, `implsH_map_fwd_comp_fwds` (forwarding read through
forwarding), `swapIdx_take`, `swapIdx_drop`, the lookups of `unswapIdx`.
-/

public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

variable {M : Type}

/-! ## Handler lemmas -/

/-- Forwarding past `n` functions, then splitting at `n + k`, is splitting at `k` and
forwarding the left part past `n`. -/
theorem splitH_comp_shiftH_add (n k : Nat) :
    (splitH (n + k)).comp (shiftH n) =
      (Handler.sumMap (shiftH n) (Handler.id sigU)).comp (splitH k) := by
  funext q
  obtain ⟨i, a⟩ := q
  by_cases hi : i < k
  · have hi' : n + i < n + k := by omega
    simp only [Handler.comp, shiftH, splitH, Prog.interp_call, Prog.interp_pure, Prog.bind_pure,
      hi, hi', ↓reduceIte]
    rfl
  · have hi' : ¬ n + i < n + k := by omega
    have he : n + i - (n + k) = i - k := by omega
    simp only [Handler.comp, shiftH, splitH, Prog.interp_call, Prog.interp_pure, Prog.bind_pure,
      hi, hi', ↓reduceIte]
    rw [he]
    rfl

/-- An extended environment observed by forwarding past its first `n` functions: the new
instance beside the forwarding, then split at `k`. -/
theorem ext_comp_shiftH_add {X : Sig.{0}} (n k : Nat) (A : Strategy X sigU)
    (N : Strategy sigU sigU) :
    (ext (n + k) A N).comp (Strategy.ofHandler (shiftH n)) =
      (A.comp ((Strategy.ofHandler (shiftH n)).pair N)).comp (Strategy.ofHandler (splitH k)) := by
  have h₁ : (Strategy.ofHandler (splitH (n + k))).comp (Strategy.ofHandler (shiftH n)) =
      (Strategy.ofHandler (Handler.sumMap (shiftH n) (Handler.id sigU))).comp
        (Strategy.ofHandler (splitH k)) := by
    rw [← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp, splitH_comp_shiftH_add]
  have h₂ : ((Strategy.id sigU).pair N).comp
      (Strategy.ofHandler (Handler.sumMap (shiftH n) (Handler.id sigU))) =
      (Strategy.ofHandler (shiftH n)).pair N := by
    rw [Strategy.pair_comp_sumMap, Strategy.id_comp, Strategy.ofHandler_id, Strategy.comp_id]
  rw [ext, Strategy.comp_assoc, Strategy.comp_assoc, h₁,
    ← Strategy.comp_assoc ((Strategy.id sigU).pair N), h₂, ← Strategy.comp_assoc]

/-- **Two instances on a stateless environment.** The environment `h` extended by `N₁`,
observed through the new instance `N₁` (forwarding past `n`) beside an instance `c` wired into
the old functions only, is the pairing of the two instances, each on its own copy of `h`. -/
theorem ext_comp_pair_shiftH (n : Nat) (h : Handler sigU sigU) (N₁ : Strategy sigU sigU)
    {ims : List Impl} (hs : ScopedList n ims) {d : Nat} (hd : n ≤ d) (c : Strategy sigU sigU) :
    (ext n (Strategy.ofHandler h) N₁).comp
        ((Strategy.ofHandler (shiftH n)).pair ((Strategy.ofHandler (implsH d ims)).comp c)) =
      ((Strategy.ofHandler h).comp N₁).pair
        ((Strategy.ofHandler (h.comp (implsH n ims))).comp c) := by
  have hsc : implsH d ims = implsH n ims := implsH_mono_scoped hs hd
  have hL : (Strategy.ofHandler (splitH n)).comp (Strategy.ofHandler (shiftH n)) =
      Strategy.ofHandler (Handler.ofHom (Sig.Hom.inr sigU sigU)) := by
    rw [← Strategy.ofHandler_comp, splitH_comp_shiftH]
  have hR : (Strategy.ofHandler (splitH n)).comp ((Strategy.ofHandler (implsH n ims)).comp c) =
      (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl sigU sigU))).comp
        ((Strategy.ofHandler (implsH n ims)).comp c) := by
    rw [← Strategy.comp_assoc, ← Strategy.ofHandler_comp, splitH_comp_implsH_scoped hs le_rfl,
      Strategy.ofHandler_comp, Strategy.comp_assoc]
  have hX : ((Strategy.id sigU).pair N₁).comp
      ((Strategy.ofHandler (Handler.ofHom (Sig.Hom.inr sigU sigU))).pair
        ((Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl sigU sigU))).comp
          ((Strategy.ofHandler (implsH n ims)).comp c))) =
      N₁.pair ((Strategy.ofHandler (implsH n ims)).comp c) := by
    rw [Strategy.pair_comp_cross, Strategy.id_comp]
  rw [ext, hsc, Strategy.comp_assoc, Strategy.comp_assoc, Strategy.ofHandler_comp_pair, hL, hR, hX,
    Strategy.ofHandler_comp_pair, ← Strategy.comp_assoc (Strategy.ofHandler h),
    ← Strategy.ofHandler_comp]

/-- Forwarding into forwarding: the wiring `fwds b m` read through the wiring `ρ` forwards to
`ρ[b], …, ρ[b + m - 1]`. -/
theorem implsH_map_fwd_comp_fwds (e e' : Nat) (ρ : List Nat) {b m : Nat} (hb : b + m ≤ e')
    (hρ : b + m ≤ ρ.length) :
    (implsH e (ρ.map Impl.fwd)).comp (implsH e' (fwds b m)) =
      implsH e (((ρ.drop b).take m).map Impl.fwd) := by
  funext q
  obtain ⟨i, a⟩ := q
  by_cases hi : i < m
  · have hρi : b + i < ρ.length := by omega
    have h₁ : (fwds b m)[i]? = some (Impl.fwd (b + i)) := by
      simp only [fwds, List.getElem?_map, List.getElem?_range hi, Option.map_some]
    have h₂ : (ρ.map Impl.fwd)[b + i]? = some (Impl.fwd ρ[b + i]) := by
      simp only [List.getElem?_map, List.getElem?_eq_getElem hρi, Option.map_some]
    have h₃ : (((ρ.drop b).take m).map Impl.fwd)[i]? = some (Impl.fwd ρ[b + i]) := by
      simp only [List.getElem?_map, List.getElem?_take_of_lt hi, List.getElem?_drop,
        List.getElem?_eq_getElem hρi, Option.map_some]
    have hbi : b + i < e' := by omega
    simp only [Handler.comp, implsH, h₁, h₂, h₃, Impl.prog, runChain, Target.prog, hbi, ↓reduceIte,
      Prog.interp_call, Prog.interp_pure, Prog.bind_pure]
  · have h₁ : (fwds b m)[i]? = none := List.getElem?_eq_none (by simpa [length_fwds] using hi)
    have h₃ : (((ρ.drop b).take m).map Impl.fwd)[i]? = none :=
      List.getElem?_eq_none (by simp only [List.length_map, List.length_take]; omega)
    simp only [Handler.comp, implsH, h₁, h₃, Prog.interp_pure]

/-- The first `n₂` entries of `swapIdx n₁ n₂` forward to the right block of imports. -/
theorem swapIdx_take (n₁ n₂ : Nat) :
    (((swapIdx n₁ n₂).drop 0).take n₂).map Impl.fwd = fwds n₁ n₂ := by
  have hl : ((List.range n₂).map (n₁ + ·)).length = n₂ := by simp
  rw [List.drop_zero, swapIdx, List.take_left' hl, List.map_map]
  rfl

/-- The last `n₁` entries of `swapIdx n₁ n₂` forward to the left block of imports. -/
theorem swapIdx_drop (n₁ n₂ : Nat) :
    (((swapIdx n₁ n₂).drop n₂).take n₁).map Impl.fwd = fwds 0 n₁ := by
  have hl : ((List.range n₂).map (n₁ + ·)).length = n₂ := by simp
  rw [swapIdx, List.drop_left' hl, List.take_of_length_le (by simp), fwds_zero]

theorem length_swapIdx (n₁ n₂ : Nat) : (swapIdx n₁ n₂).length = n₂ + n₁ := by
  simp [swapIdx]

/-- The index list re-selecting the exports of `par c₂ c₁` in the order of `par c₁ c₂`. -/
abbrev unswapIdx (k₁ k₂ : Nat) : List Nat := rightIdx k₂ k₁ ++ List.range k₂

theorem getElem?_unswapIdx_lt {k₁ k₂ i : Nat} (hi : i < k₁) :
    (unswapIdx k₁ k₂)[i]? = some (k₂ + i) := by
  have hl : i < (rightIdx k₂ k₁).length := by simpa [rightIdx] using hi
  rw [List.getElem?_append_left hl]
  simp only [rightIdx, List.getElem?_map, List.getElem?_range hi, Option.map_some]

theorem getElem?_unswapIdx_mid {k₁ k₂ i : Nat} (hi : k₁ ≤ i) (hi' : i < k₁ + k₂) :
    (unswapIdx k₁ k₂)[i]? = some (i - k₁) := by
  have hl : (rightIdx k₂ k₁).length = k₁ := by simp [rightIdx]
  rw [List.getElem?_append_right (by omega), hl, List.getElem?_range (by omega)]

theorem getElem?_unswapIdx_ge {k₁ k₂ i : Nat} (hi : k₁ + k₂ ≤ i) :
    (unswapIdx k₁ k₂)[i]? = none :=
  List.getElem?_eq_none (by simp [rightIdx]; omega)

/-- **The exports of the swapped pairing, re-selected**: exchanging the sides, splitting at
`k₂` and selecting back is splitting at `k₁`. -/
theorem swap_split_select (k₁ k₂ : Nat) :
    (Handler.ofHom (Sig.Hom.swap sigU sigU)).comp ((splitH k₂).comp
        ((maskH (k₂ + k₁)).comp (selectH (unswapIdx k₁ k₂)))) =
      (splitH k₁).comp (maskH (k₁ + k₂)) := by
  funext q
  obtain ⟨i, a⟩ := q
  by_cases h₁ : i < k₁
  · obtain ⟨hm, hs, he, hm'⟩ : k₂ + i < k₂ + k₁ ∧ ¬ k₂ + i < k₂ ∧ k₂ + i - k₂ = i ∧ i < k₁ + k₂ :=
      ⟨by omega, by omega, by omega, by omega⟩
    simp only [Handler.comp, selectH, getElem?_unswapIdx_lt h₁, maskH, Target.prog, hm, hm',
      ↓reduceIte, splitH, hs, h₁, Prog.interp_call, Prog.interp_pure, Prog.bind_pure]
    rw [he]
    rfl
  · by_cases h₂ : i < k₁ + k₂
    · have hm : i - k₁ < k₂ + k₁ := by omega
      have hs : i - k₁ < k₂ := by omega
      simp only [Handler.comp, selectH, getElem?_unswapIdx_mid (Nat.le_of_not_lt h₁) h₂, maskH,
        Target.prog, hm, h₂, ↓reduceIte, splitH, hs, h₁, Prog.interp_call, Prog.interp_pure,
        Prog.bind_pure]
      rfl
    · simp only [Handler.comp, selectH, getElem?_unswapIdx_ge (Nat.le_of_not_lt h₂), maskH,
        Target.prog, h₂, ↓reduceIte, Prog.interp_pure]

variable [CoreModule M]

/-- **Independent instantiation is the pairing of the two instances**, each on its own
wiring of the imports, split at the exports of the first. -/
theorem denU_par_pair (C : CoreSem M) (c₁ c₂ : Comp M) :
    (par c₁ c₂).denU C =
      ((((Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length)
          (fwds 0 c₁.imports.length))).comp (c₁.denU C)).pair
        ((Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length)
          (fwds c₁.imports.length c₂.imports.length))).comp (c₂.denU C))).comp
        (Strategy.ofHandler (splitH c₁.exports.length))).comp
        (Strategy.ofHandler (maskH (c₁.exports.length + c₂.exports.length))) := by
  have hX : implsH (c₁.imports.length + c₂.imports.length + c₁.exports.length +
      c₂.exports.length) (fwds (c₁.imports.length + c₂.imports.length)
        (c₁.exports.length + c₂.exports.length)) =
      (shiftH (c₁.imports.length + c₂.imports.length)).comp
        (maskH (c₁.exports.length + c₂.exports.length)) := by
    rw [Nat.add_assoc _ c₁.exports.length, implsH_fwds_exact]
  have h₁ : (Strategy.ofHandler (maskH (c₁.imports.length + c₂.imports.length))).comp
      ((Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length)
        (fwds 0 c₁.imports.length))).comp (c₁.denU C)) =
      (Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length)
        (fwds 0 c₁.imports.length))).comp (c₁.denU C) := by
    rw [← Strategy.comp_assoc, ← Strategy.ofHandler_comp, maskH_comp_implsH]
  rw [denU_par, hX, Strategy.ofHandler_comp, ← Strategy.comp_assoc, ext_comp_shiftH_add,
    ext_comp_pair_shiftH _ _ _ (ScopedList.fwds _ _) (Nat.le_add_right _ _), maskH_comp_implsH, h₁]

/-- The import wiring of `reimport … (swapIdx …)` below the two instances of `par c₂ c₁`
gives each instance its wiring in `par c₁ c₂`; the pairing comes out swapped. -/
theorem swapIdx_comp_pair (C : CoreSem M) (c₁ c₂ : Comp M) :
    (Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length)
        ((swapIdx c₁.imports.length c₂.imports.length).map Impl.fwd))).comp
      (((Strategy.ofHandler (implsH (c₂.imports.length + c₁.imports.length)
          (fwds 0 c₂.imports.length))).comp (c₂.denU C)).pair
        ((Strategy.ofHandler (implsH (c₂.imports.length + c₁.imports.length)
          (fwds c₂.imports.length c₁.imports.length))).comp (c₁.denU C))) =
      (((Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length)
          (fwds 0 c₁.imports.length))).comp (c₁.denU C)).pair
        ((Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length)
          (fwds c₁.imports.length c₂.imports.length))).comp (c₂.denU C))).comp
        (Strategy.ofHandler (Handler.ofHom (Sig.Hom.swap sigU sigU))) := by
  have hl : c₂.imports.length + c₁.imports.length ≤
      (swapIdx c₁.imports.length c₂.imports.length).length := by
    rw [length_swapIdx]
  have h₂ : (implsH (c₁.imports.length + c₂.imports.length)
      ((swapIdx c₁.imports.length c₂.imports.length).map Impl.fwd)).comp
        (implsH (c₂.imports.length + c₁.imports.length) (fwds 0 c₂.imports.length)) =
      implsH (c₁.imports.length + c₂.imports.length)
        (fwds c₁.imports.length c₂.imports.length) := by
    rw [implsH_map_fwd_comp_fwds _ _ _ (by omega) (by omega), swapIdx_take]
  have h₁ : (implsH (c₁.imports.length + c₂.imports.length)
      ((swapIdx c₁.imports.length c₂.imports.length).map Impl.fwd)).comp
        (implsH (c₂.imports.length + c₁.imports.length)
          (fwds c₂.imports.length c₁.imports.length)) =
      implsH (c₁.imports.length + c₂.imports.length) (fwds 0 c₁.imports.length) := by
    rw [implsH_map_fwd_comp_fwds _ _ _ le_rfl hl, swapIdx_drop]
  rw [Strategy.ofHandler_comp_pair, ← Strategy.comp_assoc, ← Strategy.comp_assoc,
    ← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp, h₁, h₂, Strategy.pair_comp_ofHom_swap]

omit [CoreModule M] in
theorem lt_of_mem_unswapIdx {k₁ k₂ j : Nat} (hj : j ∈ unswapIdx k₁ k₂) : j < k₂ + k₁ := by
  rcases List.mem_append.1 hj with h | h
  · obtain ⟨i, hi, rfl⟩ : ∃ i, i < k₁ ∧ k₂ + i = j := by simpa [rightIdx] using h
    omega
  · have h' : j < k₂ := List.mem_range.1 h
    omega

omit [CoreModule M] in
theorem length_unswapIdx (k₁ k₂ : Nat) : (unswapIdx k₁ k₂).length = k₁ + k₂ := by
  simp [rightIdx]

/-- **Independent instantiation is commutative**: `par c₁ c₂` is `par c₂ c₁` with its imports
re-read (`swapIdx`) and its exports re-selected (`unswapIdx`) in the original order. -/
theorem par_comm (C : CoreSem M) (c₁ c₂ : Comp M) :
    CompEquiv C (par c₁ c₂)
      (select (unswapIdx c₁.exports.length c₂.exports.length)
        (reimport (c₁.imports ++ c₂.imports) (swapIdx c₁.imports.length c₂.imports.length)
          (par c₂ c₁))) := by
  have hx : (reimport (c₁.imports ++ c₂.imports) (swapIdx c₁.imports.length c₂.imports.length)
      (par c₂ c₁)).exports.length = c₂.exports.length + c₁.exports.length := by
    exact ((sizes_wrap _ _ _).2).trans (length_exports_par c₂ c₁)
  have hf : (unswapIdx c₁.exports.length c₂.exports.length).filter
      (· < (reimport (c₁.imports ++ c₂.imports) (swapIdx c₁.imports.length c₂.imports.length)
        (par c₂ c₁)).exports.length) = unswapIdx c₁.exports.length c₂.exports.length := by
    refine List.filter_eq_self.2 fun j hj => ?_
    rw [hx, decide_eq_true_eq]
    exact lt_of_mem_unswapIdx hj
  have hk : (select (unswapIdx c₁.exports.length c₂.exports.length)
      (reimport (c₁.imports ++ c₂.imports) (swapIdx c₁.imports.length c₂.imports.length)
        (par c₂ c₁))).exports.length = c₁.exports.length + c₂.exports.length := by
    show (keptExports _ _ _).length = _
    rw [length_keptExports, hf, length_unswapIdx]
  have hH : (Strategy.ofHandler (Handler.ofHom (Sig.Hom.swap sigU sigU))).comp
      ((Strategy.ofHandler (splitH c₂.exports.length)).comp
        ((Strategy.ofHandler (maskH (c₂.exports.length + c₁.exports.length))).comp
          (Strategy.ofHandler (selectH (unswapIdx c₁.exports.length c₂.exports.length))))) =
      (Strategy.ofHandler (splitH c₁.exports.length)).comp
        (Strategy.ofHandler (maskH (c₁.exports.length + c₂.exports.length))) := by
    rw [← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp,
      ← Strategy.ofHandler_comp, swap_split_select]
  refine ⟨⟨rfl, (length_exports_par c₁ c₂).trans hk.symm⟩, ?_⟩
  rw [denU_select, hf, denU_reimport, denU_par_pair C c₂ c₁, denU_par_pair C c₁ c₂,
    List.length_append, ← Strategy.comp_assoc (Strategy.ofHandler _),
    ← Strategy.comp_assoc (Strategy.ofHandler _), swapIdx_comp_pair]
  simp only [Strategy.comp_assoc]
  rw [hH]

/-- **`ParCommLaw` holds.** -/
theorem task_par_comm : ParCommLaw (M := M) := par_comm

end Silmaril.Wasm.Component.Algebra
