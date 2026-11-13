module

public import Silmaril.Wasm.Component.Algebra.Ops.Thms

/-!
# Independent instantiation: projection laws

`par c₁ c₂` instantiates `c₁` and `c₂` side by side. Hiding the exports of one factor
leaves the other, instantiated on its own part of the imports:

* `par_select_left`: keeping the first `k₁` exports of `par c₁ c₂` is
  `wrap (I₁ ++ I₂) (fwds 0 n₁) c₁`;
* `par_select_right`: keeping the last `k₂` is `wrap (I₁ ++ I₂) (fwds n₁ n₂) c₂`.

So the two factors are **independent**: neither observes the other (there are no
instantiation-time effects in the component semantics: an instance does nothing until
it is called).

**Commutativity.** `ParCommLaw` states that `par c₁ c₂` is equivalent to `par c₂ c₁` with
its imports and exports permuted back. It is proved in
`Silmaril.Wasm.Component.Algebra.ParComm.Thms` (`task_par_comm`), from the symmetry and the
functoriality of `Silmaril.Games.Strategy.pair` at the level of plays.

Helper lemmas: `ScopedList.fwds`, `implsH_mono_scoped`, `ext_comp_implsH_scoped` (an
extended environment observed through functions of the old one is the old one),
`implsH_fwds_comp_selectH`.
-/

public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

variable {M : Type}

/-! ## Scoping of forwarding wiring -/

theorem ScopedList.fwds (b n : Nat) : ScopedList (b + n) (fwds b n) := by
  intro im him
  obtain ⟨j, hj, rfl⟩ : ∃ j, j < n ∧ Impl.fwd (b + j) = im := by
    simpa [Algebra.fwds] using him
  show b + j < b + n
  omega

theorem implsH_mono_scoped {e e' : Nat} {ims : List Impl} (h : ScopedList e ims) (he : e ≤ e') :
    implsH e' ims = implsH e ims := by
  funext q
  simp only [implsH]
  cases hq : ims[q.1]? with
  | none => rfl
  | some im =>
    show Impl.prog e' im q.2 = Impl.prog e im q.2
    rw [Impl.prog_mono (h im (List.mem_of_getElem? hq)) he]

theorem splitH_comp_implsH_scoped {e d : Nat} {ims : List Impl} (h : ScopedList e ims)
    (hd : e ≤ d) :
    (splitH d).comp (implsH e ims) =
      (Handler.ofHom (Sig.Hom.inl sigU sigU)).comp (implsH e ims) := by
  funext q
  simp only [Handler.comp, implsH]
  cases hq : ims[q.1]? with
  | none => rfl
  | some im => exact Impl.prog_interp_splitH (h im (List.mem_of_getElem? hq)) hd q.2

/-- The left projection of a pairing, as a composition. -/
theorem pair_comp_ofHom_inl {E F₁ F₂ : Sig.{0}} (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (σ₁.pair σ₂).comp (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))) = σ₁ :=
  Strategy.pair_restrict_inl σ₁ σ₂

/-- An extended environment observed through functions of the old environment. -/
theorem ext_comp_implsH_scoped {X : Sig.{0}} {e : Nat} {ims : List Impl} (h : ScopedList e ims)
    (D : Strategy X sigU) (N : Strategy sigU sigU) :
    (ext e D N).comp (Strategy.ofHandler (implsH e ims)) =
      D.comp (Strategy.ofHandler (implsH e ims)) := by
  rw [ext, Strategy.comp_assoc, Strategy.comp_assoc, ← Strategy.ofHandler_comp,
    splitH_comp_implsH_scoped h le_rfl, Strategy.ofHandler_comp,
    ← Strategy.comp_assoc ((Strategy.id sigU).pair N), pair_comp_ofHom_inl, Strategy.id_comp]

/-- Selecting among forwarded functions forwards the selected ones. -/
theorem implsH_fwds_comp_selectH (E b n : Nat) (L : List Nat) (hL : ∀ j ∈ L, j < n) :
    (implsH E (fwds b n)).comp (selectH L) = implsH E (L.map fun j => Impl.fwd (b + j)) := by
  funext q
  obtain ⟨i, a⟩ := q
  simp only [Handler.comp, selectH, implsH, List.getElem?_map]
  cases hi : L[i]? with
  | none => rfl
  | some j =>
    have hj : j < n := hL j (List.mem_of_getElem? hi)
    have hf : (fwds b n)[j]? = some (Impl.fwd (b + j)) := by
      simp only [Algebra.fwds, List.getElem?_map, List.getElem?_range hj, Option.map_some]
    simp only [Option.map_some, Prog.interp_call, Prog.interp_pure, Prog.bind_pure, implsH, hf]

/-! ## Projections -/

variable [CoreModule M]

omit [CoreModule M] in
theorem length_exports_par (c₁ c₂ : Comp M) :
    (par c₁ c₂).exports.length = c₁.exports.length + c₂.exports.length := by
  simp only [par, Comp.exports_mk, length_reexport, List.length_append]

/-- **Left projection**: hiding the exports of the right factor. -/
theorem par_select_left (C : CoreSem M) (c₁ c₂ : Comp M) :
    (select (List.range c₁.exports.length) (par c₁ c₂)).denU C =
      (wrap (c₁.imports ++ c₂.imports) (fwds 0 c₁.imports.length) c₁).denU C := by
  have hf : (List.range c₁.exports.length).filter (· < (par c₁ c₂).exports.length) =
      List.range c₁.exports.length := by
    refine List.filter_eq_self.2 fun j hj => ?_
    have hj' : j < c₁.exports.length := by simpa using hj
    simp only [length_exports_par, decide_eq_true_eq]
    omega
  have hsel : (implsH (c₁.imports.length + c₂.imports.length + c₁.exports.length +
      c₂.exports.length) (fwds (c₁.imports.length + c₂.imports.length)
        (c₁.exports.length + c₂.exports.length))).comp
      (selectH (List.range c₁.exports.length)) =
      implsH (c₁.imports.length + c₂.imports.length + c₁.exports.length)
        (fwds (c₁.imports.length + c₂.imports.length) c₁.exports.length) := by
    rw [implsH_fwds_comp_selectH _ _ _ _ (fun j hj => by simp at hj; omega)]
    exact implsH_mono_scoped (ScopedList.fwds _ _) (by omega)
  rw [denU_select, hf, denU_par, Strategy.comp_assoc, ← Strategy.ofHandler_comp, hsel,
    ext_comp_implsH_scoped (ScopedList.fwds _ _), implsH_fwds_exact, Strategy.ofHandler_comp,
    ext_comp_shiftH_comp, ← Strategy.comp_assoc (Strategy.ofHandler (maskH _)),
    ← Strategy.ofHandler_comp, maskH_comp_implsH, Strategy.comp_assoc, denU_comp_maskH,
    denU_wrap, List.length_append]

/-- The indices of the exports of the right factor. -/
abbrev rightIdx (k₁ k₂ : Nat) : List Nat := (List.range k₂).map (k₁ + ·)

/-- **Right projection**: hiding the exports of the left factor. -/
theorem par_select_right (C : CoreSem M) (c₁ c₂ : Comp M) :
    (select (rightIdx c₁.exports.length c₂.exports.length) (par c₁ c₂)).denU C =
      (wrap (c₁.imports ++ c₂.imports) (fwds c₁.imports.length c₂.imports.length) c₂).denU C := by
  have hlt : ∀ j ∈ rightIdx c₁.exports.length c₂.exports.length,
      j < c₁.exports.length + c₂.exports.length := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < c₂.exports.length ∧ c₁.exports.length + i = j := by
      simpa using hj
    omega
  have hf : (rightIdx c₁.exports.length c₂.exports.length).filter
      (· < (par c₁ c₂).exports.length) = rightIdx c₁.exports.length c₂.exports.length := by
    refine List.filter_eq_self.2 fun j hj => ?_
    simp only [length_exports_par, decide_eq_true_eq]
    exact hlt j hj
  have hsel : (implsH (c₁.imports.length + c₂.imports.length + c₁.exports.length +
      c₂.exports.length) (fwds (c₁.imports.length + c₂.imports.length)
        (c₁.exports.length + c₂.exports.length))).comp
      (selectH (rightIdx c₁.exports.length c₂.exports.length)) =
      implsH (c₁.imports.length + c₂.imports.length + c₁.exports.length + c₂.exports.length)
        (fwds (c₁.imports.length + c₂.imports.length + c₁.exports.length)
          c₂.exports.length) := by
    rw [implsH_fwds_comp_selectH _ _ _ _ hlt]
    congr 1
    simp only [rightIdx, Algebra.fwds, List.map_map, Function.comp_def, Nat.add_assoc]
  have hlow : implsH (c₁.imports.length + c₂.imports.length + c₁.exports.length)
      (fwds c₁.imports.length c₂.imports.length) =
      implsH (c₁.imports.length + c₂.imports.length) (fwds c₁.imports.length c₂.imports.length) :=
    implsH_mono_scoped (ScopedList.fwds _ _) (by omega)
  rw [denU_select, hf, denU_par, Strategy.comp_assoc, ← Strategy.ofHandler_comp, hsel,
    implsH_fwds_exact, Strategy.ofHandler_comp, ext_comp_shiftH_comp, Strategy.comp_assoc,
    Strategy.comp_assoc, denU_comp_maskH, hlow, ← Strategy.comp_assoc,
    ext_comp_implsH_scoped (ScopedList.fwds _ _), ← Strategy.ofHandler_comp, maskH_comp_implsH,
    denU_wrap, List.length_append]

/-! ## Commutativity (statement; proved in `Algebra.ParComm`) -/

/-- The wiring that reads the imports of `par c₂ c₁` from those of `par c₁ c₂`. -/
abbrev swapIdx (n₁ n₂ : Nat) : List Nat := (List.range n₂).map (n₁ + ·) ++ List.range n₁

/-- **Commutativity of independent instantiation** (statement). `par c₁ c₂` is equivalent to
`par c₂ c₁` with the imports re-read and the exports re-selected in the original order.
Proved as `Silmaril.Wasm.Component.Algebra.task_par_comm`. -/
def ParCommLaw : Prop :=
  ∀ (C : CoreSem M) (c₁ c₂ : Comp M),
    CompEquiv C (par c₁ c₂)
      (select (rightIdx c₂.exports.length c₁.exports.length ++ List.range c₂.exports.length)
        (reimport (c₁.imports ++ c₂.imports) (swapIdx c₁.imports.length c₂.imports.length)
          (par c₂ c₁)))

end Silmaril.Wasm.Component.Algebra
