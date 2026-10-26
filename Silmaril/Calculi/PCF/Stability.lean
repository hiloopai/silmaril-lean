module

public import Silmaril.Calculi.TypedLambda.Stability
public import Silmaril.Calculi.PCF.Por

/-! # Stability of PCF

Berry's stable functions (§8.2 of the notes; `Silmaril.Semantics.Domain.Stable`) on the
domain model of PCF. Parallel or is not stable (`not_stable_porFun`): the
pairs `(true, ⊥)` and `(⊥, true)` are bounded by `(true, true)` and have meet
`(⊥, ⊥)`, but `por(⊥, ⊥) = ⊥` is not the meet `true` of `por(true, ⊥)` and
`por(⊥, true)`. The left sequential or is stable (`stable_orFun`), being
built from the stable conditional (`Silmaril.Semantics.Domain.stable_condFun`).

More generally, the first-order denotation of every closed PCF term
`t : bool -> bool -> bool` is stable (`stable_denoteClosed_bool₂`). The proof
is a logical relation (`Silmaril.Calculi.TypedLambda.MeetLogRel` over the model of PCF,
here `StableRel`), preserved by every PCF operator (`StableRel.op`):

* constants, since constant triples are related (`MeetRel.const`);
* `succ`, `pred` and `zero?`, since flat liftings are stable
  (`Flat.stable_lift`, `Flat.stable_map`);
* `if`, into any type (`MeetLogRel.condFun_mem`);
* `fix`, by Scott induction, since the meet relation on flat domains is
  admissible (`Flat.meetRel_admissible`).

The fundamental lemma then gives the relation for every closed term at every
type (`StableRel.denoteClosed_mem`), which at `bool -> bool -> bool` is exactly
stability of the uncurried function `𝔹⊥ × 𝔹⊥ → 𝔹⊥`. This gives a second
proof that parallel or is not PCF-definable (`por_undefinable_of_stable`).
At higher types the relation is the "hereditary" stability of Berry's model;
we do not compare it with the stable function space of dI-domains, which the
notes do not develop either. As the notes remark, the stable model is still
not fully abstract for PCF.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Parallel or is not stable: `(true, ⊥)` and `(⊥, true)` are bounded with
meet `(⊥, ⊥)`, but `por(⊥, ⊥) = ⊥ ≠ true = por(true, ⊥) ⊓ por(⊥, true)`. -/
theorem not_stable_porFun : ¬ Stable fun p : Part Bool × Part Bool => porFun p.1 p.2 := by
  intro h
  have hb : BddAbove ({(Part.some true, Part.none), (Part.none, Part.some true)} :
      Set (Part Bool × Part Bool)) :=
    ⟨(Part.some true, Part.some true), by
      rintro z (rfl | rfl) <;> constructor <;> first | exact le_rfl | exact bot_le⟩
  have hm : IsGLB ({(Part.some true, Part.none), (Part.none, Part.some true)} :
      Set (Part Bool × Part Bool)) (Part.none, Part.none) := by
    refine isGLB_pair_prod.2 ⟨?_, isGLB_pair_of_le bot_le⟩
    rw [Set.pair_comm]
    exact isGLB_pair_of_le bot_le
  have h' := h hb hm
  simp only [porFun_true_left, porFun_true_right, porFun_none_none,
    Set.pair_eq_singleton] at h'
  exact Part.some_ne_none true (h'.unique isGLB_singleton).symm

/-- The left sequential or `or(x, y) = if(x, true, y)` is stable. -/
theorem stable_orFun : Stable fun p : Part Bool × Part Bool => orFun p.1 p.2 :=
  (stable_condFun (D := Part Bool)).comp
    (Stable.fst.prodMk ((Stable.const (Part.some true)).prodMk Stable.snd))

/-- The stability logical relation on the domain model of PCF. Only PCF
(`p = false`) is covered: in PCF+`por` the operator `por` does not preserve
the relation at `bool`, since parallel or is not stable (`not_stable_porFun`),
so the analogue of `StableRel.op` fails for `p = true`. -/
abbrev StableRel : (τ : Ty) → (Fin 3 → (model false).ty τ) → Prop :=
  MeetLogRel (model false)

namespace StableRel

/-- The meet relation is admissible at both ground types of PCF. -/
theorem admissible_base (b : Base) :
    Admissible {d : Fin 3 → (model false).ty (.base b) | MeetRel d} := by
  cases b
  · exact Flat.meetRel_admissible (X := ℕ)
  · exact Flat.meetRel_admissible (X := Bool)

/-- The relation on the argument of a unary operator on `nat`. -/
theorem natArg (xs : Fin 3 → (model false).Env [Ty.nat])
    (hxs : LogRel.Env (model false) (fun _ d => MeetRel d) xs) :
    MeetRel fun i => (xs i Ty.nat .zero : Part ℕ) :=
  hxs _ .zero

/-- Every operator of PCF preserves the stability relation. -/
theorem op {as : List Ty} {τ : Ty} (o : Op false as τ) :
    LogRel.OpPreserves (model false) (fun _ d => MeetRel d) o := by
  intro xs hxs
  cases o with
  | zero => exact MeetRel.const (Part.some 0 : Part ℕ)
  | succ => exact (Flat.stable_map Nat.succ).meetRel (natArg xs hxs)
  | pred => exact (Flat.stable_lift predPart).meetRel (natArg xs hxs)
  | tt => exact MeetRel.const (Part.some true)
  | ff => exact MeetRel.const (Part.some false)
  | isZero => exact (Flat.stable_map fun n : ℕ => n == 0).meetRel (natArg xs hxs)
  | ite τ =>
      have hc : MeetRel fun i => (xs i Ty.bool .zero : Part Bool) := hxs _ .zero
      exact MeetLogRel.condFun_mem hc (hxs _ (.succ .zero)) (hxs _ (.succ (.succ .zero)))
  | fix τ =>
      exact LogRel.fix_mem (M := model false) (LogRel.admissible admissible_base τ)
        (hxs _ .zero)

/-- The fundamental lemma for the stability relation: the denotation `d` of a
closed PCF term relates `(d, d, d)`. -/
theorem denoteClosed_mem {τ : Ty} (t : Closed false τ) : StableRel τ fun _ => denoteClosed t :=
  LogRel.fundamental_closed op t

end StableRel

/-- The first-order denotation `𝔹⊥ × 𝔹⊥ → 𝔹⊥` of every closed PCF term
`t : bool -> bool -> bool` is stable. -/
theorem stable_denoteClosed_bool₂ (t : Closed false Ty.bool₂) :
    Stable fun p : Part Bool × Part Bool => app₂ (denoteClosed t) p.1 p.2 := by
  intro p q m hb hm
  obtain ⟨hb₁, hb₂⟩ := bddAbove_pair_prod.1 hb
  obtain ⟨hm₁, hm₂⟩ := isGLB_pair_prod.1 hm
  exact (StableRel.denoteClosed_mem t ![p.1, q.1, m.1] ⟨hb₁, hm₁⟩ ![p.2, q.2, m.2] ⟨hb₂, hm₂⟩).2

/-- Undefinability of parallel or, via stability: the denotation of a closed
PCF term `t : bool -> bool -> bool` is stable, and parallel or is not. -/
theorem por_undefinable_of_stable (t : Closed false Ty.bool₂) : denoteClosed t ≠ porElem := by
  intro h
  have ht := stable_denoteClosed_bool₂ t
  rw [h] at ht
  exact not_stable_porFun ht

end Silmaril.Calculi.PCF
