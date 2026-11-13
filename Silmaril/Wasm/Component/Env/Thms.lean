module

public import Silmaril.Wasm.Component.Semantics.Thms
public import Silmaril.Wasm.Component.Laws.Defs

/-!
# Environments: handler-level laws

Equalities of handlers over `sigU` used by the structural passes. They are
computations on programs and need no law about strategies.

* `Impl.prog_subst`, `implsH_comp_subst`: interpreting wiring programs by the
  handler of `σ` is substituting `σ` into them (chain concatenation).
* `Impl.prog_mono`, `Impl.prog_interp_splitH`: a program scoped below `e` does
  not see the size of the environment, and only talks to the left of a split
  at `e` or above.
* `widenH_comp_maskH`, `exportsH_comp_maskH`: instances trap beyond their
  exports.
* `splitH_comp_implsH_append`: how the environment extended by a node is
  split.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

variable {M : Type} [CoreModule M]

/-! ## Substitution -/

theorem Impl.trap_prog (e : Nat) (x : Payload) : Impl.trap.prog e x = .pure none := rfl

theorem Impl.trap_subst (σ : List Impl) : Impl.trap.subst σ = Impl.trap := rfl

/-- Interpreting a wiring program by the handler of `σ` substitutes `σ`. -/
theorem Impl.prog_subst (eB : Nat) (σ : List Impl) (im : Impl) (x : Payload) :
    (im.prog σ.length x).interp (implsH eB σ) = (im.subst σ).prog eB x := by
  obtain ⟨c, t⟩ := im
  simp only [Impl.prog, runChain_interp]
  cases t with
  | const res => rfl
  | call r =>
    simp only [Impl.subst]
    by_cases hr : r < σ.length
    · have hx : ∀ y, ((Target.call r).prog σ.length y).interp (implsH eB σ) =
          implsH eB σ (r, y) := fun y => Target.prog_call_interp _ hr y
      simp only [hx, implsH, List.getElem?_eq_getElem hr]
      rw [runChain_append]
      rfl
    · have hn : σ[r]? = none := List.getElem?_eq_none (by omega)
      simp only [hn]
      congr 1
      funext y
      simp [Target.prog, hr]

/-- `implsH` after `implsH`: substitution. -/
theorem implsH_comp_subst (eB : Nat) (σ ims : List Impl) :
    (implsH eB σ).comp (implsH σ.length ims) = implsH eB (ims.map (Impl.subst σ)) := by
  funext q
  simp only [Handler.comp, implsH, List.getElem?_map]
  cases ims[q.1]? with
  | none => rfl
  | some im => exact Impl.prog_subst eB σ im q.2

theorem implsN_comp_subst (eB : Nat) (σ ims : List Impl) (t : Nat) :
    (implsH eB σ).comp (implsN σ.length ims t) = implsN eB (ims.map (Impl.subst σ)) t := by
  funext q
  exact congrFun (implsH_comp_subst eB σ ims) (q.1.val, q.2)

/-- `exportsH` after `implsH`: substitution. -/
theorem implsH_comp_exportsH (eB : Nat) (σ : List Impl) (xs : List Export) :
    (implsH eB σ).comp (exportsH σ.length xs) =
      exportsH eB (xs.map fun x => { x with impl := x.impl.subst σ }) := by
  rw [exportsH, implsH_comp_subst]
  simp [exportsH, Function.comp_def]

/-- `maskH` below `implsH`: the first `n` wiring programs, padded with traps. -/
theorem implsH_comp_maskH (e : Nat) (ims : List Impl) (n : Nat) :
    (implsH e ims).comp (maskH n) =
      implsH e ((List.range n).map fun i => ims[i]?.getD Impl.trap) := by
  funext q
  simp only [Handler.comp, maskH, Target.prog]
  by_cases hq : q.1 < n
  · simp only [hq, ↓reduceIte, Prog.interp_call, Prog.interp_pure, Prog.bind_pure]
    simp only [implsH, List.getElem?_map, List.getElem?_range hq, Option.map_some]
    cases ims[q.1]? <;> rfl
  · simp only [hq, ↓reduceIte, Prog.interp_pure]
    simp only [implsH]
    rw [List.getElem?_eq_none (by simpa using hq)]

/-! ## Scoping -/

theorem Impl.Scoped.mono {e e' : Nat} {im : Impl} (h : im.Scoped e) (he : e ≤ e') :
    im.Scoped e' := by
  obtain ⟨c, t⟩ := im
  cases t with
  | call r => exact Nat.lt_of_lt_of_le (show r < e from h) he
  | const _ => trivial

/-- A scoped program does not see the size of the environment. -/
theorem Impl.prog_mono {e e' : Nat} {im : Impl} (h : im.Scoped e) (he : e ≤ e') :
    im.prog e' = im.prog e := by
  obtain ⟨c, t⟩ := im
  cases t with
  | const _ => rfl
  | call r =>
    have hr : r < e := h
    have hr' : r < e' := Nat.lt_of_lt_of_le hr he
    simp only [Impl.prog]
    congr 1
    funext y
    simp only [Target.prog, hr, hr', ↓reduceIte]

/-- A program scoped below `e` only calls the left of a split at `e` or above. -/
theorem Impl.prog_interp_splitH {e d : Nat} {im : Impl} (h : im.Scoped e) (hd : e ≤ d)
    (x : Payload) :
    (im.prog e x).interp (splitH d) =
      (im.prog e x).interp (Handler.ofHom (Sig.Hom.inl sigU sigU)) := by
  obtain ⟨c, t⟩ := im
  simp only [Impl.prog, runChain_interp]
  congr 1
  funext y
  cases t with
  | const _ => rfl
  | call r =>
    have hr : r < e := h
    simp only [Target.prog, hr, ↓reduceIte, Prog.interp_call, Prog.interp_pure, Prog.bind_pure,
      splitH, Nat.lt_of_lt_of_le hr hd]
    rfl

theorem Impl.subst_scoped {e : Nat} {σ : List Impl} (hσ : ScopedList e σ) (im : Impl) :
    (im.subst σ).Scoped e := by
  obtain ⟨c, t⟩ := im
  cases t with
  | const _ => trivial
  | call r =>
    simp only [Impl.subst]
    cases h : σ[r]? with
    | none => trivial
    | some im' => exact hσ im' (List.mem_of_getElem? h)

/-! ## Instances trap beyond their exports -/

theorem widenH_comp_maskH (w : Nat) : (widenH w).comp (maskH w) = widenH w := by
  funext q
  simp only [Handler.comp, maskH, Target.prog]
  by_cases hq : q.1 < w
  · simp only [hq, ↓reduceIte, Prog.interp_call, Prog.interp_pure, Prog.bind_pure]
  · simp only [hq, ↓reduceIte, Prog.interp_pure, widenH, ↓reduceDIte]

theorem exportsH_comp_maskH (e : Nat) (xs : List Export) :
    (exportsH e xs).comp (maskH xs.length) = exportsH e xs := by
  funext q
  simp only [Handler.comp, maskH, Target.prog]
  by_cases hq : q.1 < xs.length
  · simp only [hq, ↓reduceIte, Prog.interp_call, Prog.interp_pure, Prog.bind_pure]
  · simp only [hq, ↓reduceIte, Prog.interp_pure, exportsH, implsH]
    rw [List.getElem?_eq_none (by simpa using hq)]

theorem maskH_comp_maskH (n : Nat) : (maskH n).comp (maskH n) = maskH n := by
  funext q
  by_cases hq : q.1 < n
  · simp [Handler.comp, maskH, Target.prog, hq, Prog.interp_call]
  · simp [Handler.comp, maskH, Target.prog, hq]

/-- The forwarding of the imports, as wiring programs. -/
theorem implsH_fwd (n : Nat) : implsH n ((List.range n).map Impl.fwd) = maskH n := by
  funext q
  simp only [implsH, maskH, List.getElem?_map]
  by_cases hq : q.1 < n
  · simp [Impl.prog, runChain, Target.prog, hq]
  · rw [List.getElem?_eq_none (by simpa using hq)]
    simp [Target.prog, hq]

/-! ## Splitting an extended environment -/

/-- The environment `σ` (scoped below `eB`) extended by `w` functions of a new
node, split at `eB`, is `σ` on the left and the node, masked, on the right. -/
theorem splitH_comp_implsH_append {eB w : Nat} {σ : List Impl} (hσ : ScopedList eB σ) :
    (splitH eB).comp (implsH (eB + w) (σ ++ (List.range w).map fun i => Impl.fwd (eB + i))) =
      (Handler.sum (implsH eB σ) (maskH w)).comp (splitH σ.length) := by
  funext q
  obtain ⟨r, x⟩ := q
  simp only [Handler.comp]
  by_cases h₁ : r < σ.length
  · show (implsH (eB + w) (σ ++ (List.range w).map fun i => Impl.fwd (eB + i)) (r, x)).interp
        (splitH eB) = (splitH σ.length (r, x)).interp (Handler.sum (implsH eB σ) (maskH w))
    have hs : σ[r]? = some σ[r] := List.getElem?_eq_getElem h₁
    have hsc : σ[r].Scoped eB := hσ _ (List.getElem_mem h₁)
    have hR : (splitH σ.length (r, x)) = .call (.inl (r, x)) fun n => .pure n := by
      simp only [splitH, h₁, ↓reduceIte]
    rw [hR]
    show _ = ((Handler.sum (implsH eB σ) (maskH w) (.inl (r, x))).bind fun n => Prog.pure n)
    rw [Prog.bind_pure]
    simp only [Handler.sum, implsH, List.getElem?_append_left h₁, hs]
    rw [Impl.prog_mono hsc (Nat.le_add_right _ _), Impl.prog_interp_splitH hsc le_rfl]
    rfl
  · show (implsH (eB + w) (σ ++ (List.range w).map fun i => Impl.fwd (eB + i)) (r, x)).interp
        (splitH eB) = (splitH σ.length (r, x)).interp (Handler.sum (implsH eB σ) (maskH w))
    have hR : (splitH σ.length (r, x)) = .call (.inr (r - σ.length, x)) fun n => .pure n := by
      simp only [splitH, h₁, ↓reduceIte]
    rw [hR]
    show _ = ((Handler.sum (implsH eB σ) (maskH w) (.inr (r - σ.length, x))).bind
      fun n => Prog.pure n)
    rw [Prog.bind_pure]
    have hap := List.getElem?_append_right (l₁ := σ)
      (l₂ := (List.range w).map fun i => Impl.fwd (eB + i)) (Nat.le_of_not_lt h₁)
    by_cases h₂ : r - σ.length < w
    · show (implsH (eB + w) (σ ++ (List.range w).map fun i => Impl.fwd (eB + i)) (r, x)).interp
          (splitH eB) = Handler.sum (implsH eB σ) (maskH w) (.inr (r - σ.length, x))
      have h₃ : eB + (r - σ.length) < eB + w := by omega
      have h₄ : ¬ eB + (r - σ.length) < eB := by omega
      simp only [Handler.sum, implsH, hap, List.getElem?_map, maskH, List.getElem?_range h₂,
        Option.map_some, h₂, ↓reduceIte, Impl.prog, runChain, Target.prog, h₃]
      show ((splitH eB (eB + (r - σ.length), x)).bind fun n => Prog.pure n) =
        ((Handler.ofHom (Sig.Hom.inr sigU sigU) (r - σ.length, x)).bind fun n => Prog.pure n)
      simp only [Prog.bind_pure, splitH, h₄, ↓reduceIte]
      generalize hk : eB + (r - σ.length) - eB = k
      obtain rfl : k = r - σ.length := by omega
      rfl
    · show (implsH (eB + w) (σ ++ (List.range w).map fun i => Impl.fwd (eB + i)) (r, x)).interp
          (splitH eB) = Handler.sum (implsH eB σ) (maskH w) (.inr (r - σ.length, x))
      have hnone : ((List.range w).map fun i => Impl.fwd (eB + i))[r - σ.length]? = none :=
        List.getElem?_eq_none (by simpa using h₂)
      simp only [Handler.sum, implsH, hap, hnone, maskH, Target.prog, h₂, ↓reduceIte]
      rfl

end Silmaril.Wasm.Component
