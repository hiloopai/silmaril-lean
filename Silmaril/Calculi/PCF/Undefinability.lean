module

public import Silmaril.Calculi.TypedLambda.LogicalRelation
public import Silmaril.Calculi.PCF.Por

/-! # Undefinability of parallel or

No closed PCF term denotes parallel or (`por_undefinable`; Theorem 40 of the
notes, whose proof they omit, pointing to Plotkin's activity lemma, to stable
functions, and to logical relations). We follow the logical-relation proof
(Sieber), with Sieber's ternary relation

  `R(d₀, d₁, d₂) :⇔ d₀ = ⊥ ∨ d₁ = ⊥ ∨ d₀ = d₁ = d₂`

at both ground types, extended to all types as a logical relation
(`Silmaril.Calculi.TypedLambda.SieberLogRel` over the model of PCF). Every PCF operator
preserves it (`Sieber.op`):

* constants trivially, since their three components are equal;
* `succ`, `pred` and `zero?` because they are strict (`SieberRel.map`);
* `if` because the relation holds at every type of all triples whose first or
  second component is `⊥` (`SieberLogRel.condFun_mem`);
* `fix` by Scott induction, because the relation is admissible at every type
  (`SieberLogRel.admissible`, `LogRel.fix_mem`).

By the fundamental lemma, the denotation `d` of every closed PCF term
satisfies `R(d, d, d)` (`Sieber.denoteClosed_mem`). Parallel or does not: it
sends the related triples `(true, ⊥, false)` and `(⊥, true, false)` to the
unrelated triple `(true, true, false)`. The proof is purely denotational; it
does not need adequacy.

With the characterization of parallel or by three table entries (`PorSpec`),
the denotation of a closed PCF term `t : bool -> bool -> bool` fails one of
them (`not_porSpec_denoteClosed`).
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Sieber's logical relation on the domain model of PCF. -/
abbrev Sieber : (τ : Ty) → (Fin 3 → (model false).ty τ) → Prop :=
  SieberLogRel (model false)

namespace Sieber

/-- The relation on the argument of a unary operator on `nat`. -/
theorem natArg (xs : Fin 3 → (model false).Env [Ty.nat])
    (hxs : LogRel.Env (model false) (fun _ d => SieberRel d) xs) :
    SieberRel fun i => (xs i Ty.nat .zero : Part ℕ) :=
  hxs _ .zero

/-- Every operator of PCF preserves Sieber's relation. -/
theorem op {as : List Ty} {τ : Ty} (o : Op false as τ) :
    LogRel.OpPreserves (model false) (fun _ d => SieberRel d) o := by
  intro xs hxs
  cases o with
  | zero => exact SieberRel.const (Part.some 0 : Part ℕ)
  | succ => exact SieberRel.map (Flat.map_none Nat.succ) (natArg xs hxs)
  | pred => exact SieberRel.map (Flat.lift_none predPart) (natArg xs hxs)
  | tt => exact SieberRel.const (Part.some true)
  | ff => exact SieberRel.const (Part.some false)
  | isZero => exact SieberRel.map (Flat.map_none fun n : ℕ => n == 0) (natArg xs hxs)
  | ite τ =>
      have hc : SieberRel fun i => (xs i Ty.bool .zero : Part Bool) := hxs _ .zero
      exact SieberLogRel.condFun_mem hc (hxs _ (.succ .zero)) (hxs _ (.succ (.succ .zero)))
  | fix τ => exact LogRel.fix_mem (M := model false) (SieberLogRel.admissible τ) (hxs _ .zero)

/-- The fundamental lemma for Sieber's relation: the denotation `d` of a
closed PCF term satisfies `R(d, d, d)`. -/
theorem denoteClosed_mem {τ : Ty} (t : Closed false τ) : Sieber τ fun _ => denoteClosed t :=
  LogRel.fundamental_closed op t

end Sieber

/-- Parallel or does not satisfy Sieber's relation: it sends the related
triples `(true, ⊥, false)` and `(⊥, true, false)` to `(true, true, false)`. -/
theorem not_sieber_porElem : ¬ Sieber Ty.bool₂ fun _ => porElem := by
  intro h
  have hres := h ![Part.some true, Part.none, Part.some false] (Or.inr (Or.inl rfl))
    ![Part.none, Part.some true, Part.some false] (Or.inl rfl)
  have hres' : SieberRel fun i : Fin 3 =>
      porFun (![Part.some true, Part.none, Part.some false] i)
        (![Part.none, Part.some true, Part.some false] i) := hres
  rcases hres' with h | h | ⟨_, h⟩
  · simp only [Matrix.cons_val_zero, porFun_true_left] at h
    exact Part.some_ne_none true h
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, porFun_true_right] at h
    exact Part.some_ne_none true h
  · simp at h

/-- Undefinability of parallel or (Theorem 40): no closed PCF term
`t : bool -> bool -> bool` has `⟦t⟧ = por`. -/
theorem por_undefinable (t : Closed false Ty.bool₂) : denoteClosed t ≠ porElem := by
  intro h
  have ht := Sieber.denoteClosed_mem t
  rw [h] at ht
  exact not_sieber_porElem ht

/-- The denotation of a closed PCF term `t : bool -> bool -> bool` fails one
of `⟦t⟧(true)(⊥) = true`, `⟦t⟧(⊥)(true) = true` and
`⟦t⟧(false)(false) = false`. -/
theorem not_porSpec_denoteClosed (t : Closed false Ty.bool₂) : ¬ PorSpec (denoteClosed t) :=
  fun h => por_undefinable t h.eq_porElem

end Silmaril.Calculi.PCF
