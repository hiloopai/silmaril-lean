module

public import Silmaril.Logic.Consequence.HOL.Standard.Defs
public import Silmaril.Logic.Consequence.HOL.Thms
public import Silmaril.Logic.Consequence.Soundness.Thms
public import Silmaril.Logic.HOLLight.SExp.Thms
public import Silmaril.Logic.HOLLight.Examples
public import Silmaril.Logic.HOLLight.Kernel.Structural
public import Silmaril.Logic.Concrete.Codec.Thms

/-!
# HOL's standard interpretation: soundness, consistency, S-expressions and problems

**Soundness** for the standard interpretation, in every universe: `kernel_soundFor` (the kernel
on propositions, from `HOLLight.Derives.sound`).

**Consistency**, relative to Lean and to the standard model of the initial signature at universe
0:
* `kernel_consistent`: pure HOL does not derive `⊥`;
* `classical_consistent'`: neither does HOL with HOL Light's three classical axioms ETA_AX,
  SELECT_AX and INFINITY_AX (`classicalTheory`). This restates `HOLLight.classical_consistent`
  as consistency of the consequence system.

No claim is made for further axioms or signatures.

**Over S-expressions.** `decodeProp_eq_some_iff`: the pipeline decode, then type-check, then
require `bool` accepts exactly the canonical forms of propositions. `decodeProp_eq_none_iff` names
the two errors: not a canonical term, or not of type `bool`. `propCodec S` is the presentation
`silmaril.hol-light.prop` (version 1).

**Problems**, each derived in the kernel, decoded from its S-expression, and true at the standard
point:
* `truthProp` (`⊤`), pure HOL;
* `reflProp` (`x = x` for a free boolean `x`), pure HOL;
* `emProp` (`⊤ ∨ ¬⊤`), from the classical axioms by excluded middle.
-/

@[expose] public section

namespace Silmaril.Consequence.HOL

open Silmaril.Logic.HOLLight Silmaril.Logic.Concrete
open Silmaril.Logic.Institution.Metatheory (HolSig)
open Silmaril.Logic.Smt (SE)

universe u

/-- **Soundness of the kernel for HOL's standard interpretation**, in every universe. -/
theorem kernel_soundFor (S : HolSig) : (kernel S).SoundFor (points.{u} S) := kernel_le_seq

/-- **Pure HOL is consistent**: the kernel derives no `⊥` from no hypotheses. -/
theorem kernel_consistent : (kernel initialSig).ConsistentWrt (falsityProp initialSig) [] :=
  consistentWrt_of_sound (kernel_soundFor.{0} initialSig) standardPoint (fun _ h => by cases h)
    (fun h => Holds.not_falsity h)

/-- **HOL with ETA, SELECT and INFINITY is consistent.** -/
theorem classical_consistent' :
    (kernelFrom initialSig classicalTheory).ConsistentWrt (falsityProp initialSig) [] :=
  fun h => by
    simp only [kernelFrom, falsityProp, HOLProp.falsity] at h
    exact classical_consistent h

theorem kernel_nontrivial : (kernel initialSig).ContextConsistent [] :=
  fun h => kernel_consistent (h _)

/-! ## Over S-expressions -/

/-- **The pipeline accepts exactly the canonical forms of propositions.** -/
theorem decodeProp_eq_some_iff (S : HolSig) (e : SE) (p : HOLProp S) :
    decodeProp S e = some p ↔ SExp.encodeTm p.1 = e := by
  unfold decodeProp
  split
  · rename_i t h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨t', ht', h⟩ := h
    split at h
    · cases h
      rw [SExp.decodeTm_eq_some_iff] at ht'
      constructor
      · rintro ⟨⟩; exact ht'
      · intro he
        have := SExp.encodeTm_injective (ht'.trans he.symm)
        exact congrArg some (Subtype.ext this)
    · cases h
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro he
    have hd : SExp.decodeTm e = some p.1 := (SExp.decodeTm_eq_some_iff).2 he
    rw [hd] at h
    simp [(Tm.typeOf?_eq_some_iff _ _ _ _).2 p.2] at h

/-- **The pipeline's errors**: not a canonical term, or not of type `bool`. -/
theorem decodeProp_eq_none_iff (S : HolSig) (e : SE) :
    decodeProp S e = none ↔
      SExp.decodeTm e = none ∨ ∃ t, SExp.decodeTm e = some t ∧ ¬ HasType S.sig [] t .bool := by
  constructor
  · intro h
    cases ht : SExp.decodeTm e with
    | none => exact .inl rfl
    | some t =>
      refine .inr ⟨t, rfl, fun ht' => ?_⟩
      have := (decodeProp_eq_some_iff S e ⟨t, ht'⟩).2 ((SExp.decodeTm_eq_some_iff).1 ht)
      rw [h] at this; cases this
  · rintro (h | ⟨t, ht, hb⟩)
    · cases e' : decodeProp S e with
      | none => rfl
      | some p => have := (decodeProp_eq_some_iff S e p).1 e'
                  rw [(SExp.decodeTm_eq_some_iff).2 this] at h; cases h
    · cases e' : decodeProp S e with
      | none => rfl
      | some p =>
        have := (decodeProp_eq_some_iff S e p).1 e'
        rw [(SExp.decodeTm_eq_some_iff).2 this] at ht
        cases ht; exact absurd p.2 hb

/-- **HOL propositions as S-expressions**, `silmaril.hol-light.prop` (version 1): a term's form,
read back with type checking. -/
def propCodec (S : HolSig) : SExpCodec (HOLProp S) where
  name := "silmaril.hol-light.prop"
  version := "1"
  encode p := SExp.encodeTm p.1
  decode := decodeProp S
  decode_eq_some_iff e p := decodeProp_eq_some_iff S e p

/-! ## Concrete problems -/

/-- `⊤`. -/
def truthProp : HOLProp initialSig := ⟨Tm.truth, HasType.truth⟩

/-- `x = x`, for the free boolean variable `x` (number `0`). -/
def reflProp : HOLProp initialSig :=
  ⟨Tm.equal .bool (.fvar 0 .bool) (.fvar 0 .bool), HasType.equal trivial (.fvar 0 trivial) (.fvar 0 trivial)⟩

/-- `⊤ ∨ ¬⊤`. -/
def emProp : HOLProp initialSig :=
  ⟨Tm.disj Tm.truth (Tm.neg Tm.truth), (Examples.excluded_middle HasType.truth).typing⟩

theorem truthProp_derived : kernel initialSig [] truthProp :=
  (Derives.truth : Derives initialSignature [] ∅ Tm.truth)

theorem reflProp_derived : kernel initialSig [] reflProp :=
  (Derives.refl (HasType.fvar (Γ := []) 0 (A := .bool) trivial) :
    Derives initialSignature [] ∅ (Tm.equal .bool (.fvar 0 .bool) (.fvar 0 .bool)))

theorem emProp_derived : kernelFrom initialSig classicalTheory [] emProp :=
  (Examples.excluded_middle (p := Tm.truth) HasType.truth :
    Derives initialSignature classicalTheory ∅ (Tm.disj Tm.truth (Tm.neg Tm.truth)))

/-- `⊤` is true at the standard point. -/
theorem truthProp_true : (points.{0} initialSig).satC standardPoint truthProp :=
  kernel_soundFor.{0} initialSig [] _ truthProp_derived standardPoint (fun _ h => by cases h)

/-- `x = x` is true at the standard point (and at every point). -/
theorem reflProp_true : (points.{0} initialSig).satC standardPoint reflProp :=
  kernel_soundFor.{0} initialSig [] _ reflProp_derived standardPoint (fun _ h => by cases h)

theorem truthProp_decode :
    (propCodec initialSig).decode ((propCodec initialSig).encode truthProp) = some truthProp :=
  (propCodec initialSig).decode_encode _

end Silmaril.Consequence.HOL
