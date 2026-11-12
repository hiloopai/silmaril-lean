module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Structural
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External

/-! # Structural compatibility of external divergence

Loop simulations preserve finite prefixes and divergent bodies, including externally divergent primitives.
Renaming preserves and reflects divergence when the environments agree.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.External

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
  {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α} {prim : Φ → Value α → σ → Prop}

theorem Diverges.fold_core {c : Config α ν Φ σ}
    (h : Semantics.DivergenceStep instr free (Diverges instr free prim) c) :
    Diverges instr free prim c := .fold (.core h)

theorem Diverges.map_loop_body {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {body : Tm ν Φ (n + 1)} {body' : Tm ν Φ (m + 1)}
    (finite : ∀ {current result : Value α} {s s' : σ},
      Eval instr free (extend bound current) body s result s' →
      Eval instr free (extend target current) body' s result s')
    (infinite : ∀ {current : Value α} {s : σ},
      Diverges instr free prim (.term (extend bound current) body s) →
      Diverges instr free prim (.term (extend target current) body' s))
    {current : Value α} {s : σ}
    (h : Diverges instr free prim (.loop bound body current s)) :
    Diverges instr free prim (.loop target body' current s) := by
  let R : Config α ν Φ σ → Prop := fun c =>
    Diverges instr free prim c ∨ ∃ value state,
      c = .loop target body' value state ∧ Diverges instr free prim (.loop bound body value state)
  refine Diverges.coinduct R ?_ (Or.inr ⟨current, s, rfl, h⟩)
  intro c hc
  rcases hc with existing | ⟨value, state, rfl, source⟩
  · exact existing.unfold.mono (fun _ h => Or.inl h)
  · cases source.unfold with | core source =>
    apply DivergenceStep.core
    cases source with
    | loop_body hbody => exact .loop_body (Or.inl (infinite hbody))
    | loop_step head tail => exact .loop_step (finite head) (Or.inr ⟨_, _, rfl, tail⟩)

theorem Diverges.rename_iff {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {s : σ}
    (agree : ∀ i, target (ρ i) = bound i) :
    Diverges instr free prim (.term target (t.rename ρ) s) ↔
      Diverges instr free prim (.term bound t s) := by
  induction t generalizing m s with
  | fv | bv | unit => constructor <;> intro h <;> cases h.unfold with | core h => cases h
  | op f a ih =>
    constructor
    · intro h; cases h.unfold with
      | core h => cases h with | op arg => exact .fold_core (.op ((ih agree).mp arg))
      | primitive arg div => exact .primitive (arg.of_rename agree) div
    · intro h; cases h.unfold with
      | core h => cases h with | op arg => exact .fold_core (.op ((ih agree).mpr arg))
      | primitive arg div => exact .primitive (arg.rename ρ target agree) div
  | let₁ a b iha ihb =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with
      | let₁_arg arg => exact .fold_core (.let₁_arg ((iha agree).mp arg))
      | let₁_body arg body =>
        exact .fold_core (.let₁_body (arg.of_rename agree) ((ihb (extend_rename agree _)).mp body))
    · intro h; cases h.unfold with | core h => cases h with
      | let₁_arg arg => exact .fold_core (.let₁_arg ((iha agree).mpr arg))
      | let₁_body arg body =>
        exact .fold_core (.let₁_body (arg.rename ρ target agree) ((ihb (extend_rename agree _)).mpr body))
  | pair a b iha ihb =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with
      | pair_left left => exact .fold_core (.pair_left ((iha agree).mp left))
      | pair_right left right => exact .fold_core (.pair_right (left.of_rename agree) ((ihb agree).mp right))
    · intro h; cases h.unfold with | core h => cases h with
      | pair_left left => exact .fold_core (.pair_left ((iha agree).mpr left))
      | pair_right left right => exact .fold_core (.pair_right (left.rename ρ target agree) ((ihb agree).mpr right))
  | let₂ a b iha ihb =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with
      | let₂_arg arg => exact .fold_core (.let₂_arg ((iha agree).mp arg))
      | let₂_body arg body =>
        exact .fold_core (.let₂_body (arg.of_rename agree)
          ((ihb (extend_rename (extend_rename agree _) _)).mp body))
    · intro h; cases h.unfold with | core h => cases h with
      | let₂_arg arg => exact .fold_core (.let₂_arg ((iha agree).mpr arg))
      | let₂_body arg body =>
        exact .fold_core (.let₂_body (arg.rename ρ target agree)
          ((ihb (extend_rename (extend_rename agree _) _)).mpr body))
  | inl a ih =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with | inl arg => exact .fold_core (.inl ((ih agree).mp arg))
    · intro h; cases h.unfold with | core h => cases h with | inl arg => exact .fold_core (.inl ((ih agree).mpr arg))
  | inr a ih =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with | inr arg => exact .fold_core (.inr ((ih agree).mp arg))
    · intro h; cases h.unfold with | core h => cases h with | inr arg => exact .fold_core (.inr ((ih agree).mpr arg))
  | case e l r ihe ihl ihr =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with
      | case_scrutinee arg => exact .fold_core (.case_scrutinee ((ihe agree).mp arg))
      | case_inl arg branch => exact .fold_core (.case_inl (arg.of_rename agree)
          ((ihl (extend_rename agree _)).mp branch))
      | case_inr arg branch => exact .fold_core (.case_inr (arg.of_rename agree)
          ((ihr (extend_rename agree _)).mp branch))
    · intro h; cases h.unfold with | core h => cases h with
      | case_scrutinee arg => exact .fold_core (.case_scrutinee ((ihe agree).mpr arg))
      | case_inl arg branch => exact .fold_core (.case_inl (arg.rename ρ target agree)
          ((ihl (extend_rename agree _)).mpr branch))
      | case_inr arg branch => exact .fold_core (.case_inr (arg.rename ρ target agree)
          ((ihr (extend_rename agree _)).mpr branch))
  | abort a ih =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with | abort arg => exact .fold_core (.abort ((ih agree).mp arg))
    · intro h; cases h.unfold with | core h => cases h with | abort arg => exact .fold_core (.abort ((ih agree).mpr arg))
  | iter a b iha ihb =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with
      | iter_init arg => exact .fold_core (.iter_init ((iha agree).mp arg))
      | iter_loop arg loop =>
        exact .fold_core (.iter_loop (arg.of_rename agree)
          (loop.map_loop_body (fun h => h.of_rename (extend_rename agree _))
            (fun h => (ihb (extend_rename agree _)).mp h)))
    · intro h; cases h.unfold with | core h => cases h with
      | iter_init arg => exact .fold_core (.iter_init ((iha agree).mpr arg))
      | iter_loop arg loop =>
        exact .fold_core (.iter_loop (arg.rename ρ target agree)
          (loop.map_loop_body (fun h => h.rename _ _ (extend_rename agree _))
            (fun h => (ihb (extend_rename agree _)).mpr h)))

theorem Diverges.rename {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {s : σ}
    (h : Diverges instr free prim (.term bound t s)) (agree : ∀ i, target (ρ i) = bound i) :
    Diverges instr free prim (.term target (t.rename ρ) s) :=
  (Diverges.rename_iff agree).mpr h

end Silmaril.Isotope.LetIter.Semantics.External
