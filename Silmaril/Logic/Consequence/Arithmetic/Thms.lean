module

public import Silmaril.Logic.Consequence.Arithmetic.Defs
public import Silmaril.Logic.Consequence.Soundness.Thms
public import Silmaril.Logic.Arithmetic.Thms
public import Silmaril.Logic.Arithmetic.SExp.Thms

/-!
# Peano and Robinson arithmetic: soundness, consistency, concrete syntax and problems

**Soundness** for the standard interpretation: `pa_soundFor`, `q_soundFor` (from
`Arithmetic.Theorems.pa_sound`, `q_sound`). `q_le_pa`: Q's consequences are PA's.

**Consistency**, relative to Lean and to the standard model ℕ: `pa_consistent`, `q_consistent`
(the empty theory does not derive `false`), and `pa_nontrivial`. These are about PA itself; no
claim is made for PA with added axioms.

**Concrete syntax** (`silmaril.arithmetic.formula`): `paConcrete_consistent`, `paConcrete_sound`.

**Problems**, each a concrete sentence decoded from an explicit S-expression, with a derivation
and its standard truth: `zeroAddZero` (`(= (+ zero zero) zero)`, derived by `paZeroAddZero`) and
`zeroOrSuccessor` (`(forall (or (= (var 0) zero) (exists (= (var 1) (succ (var 0))))))`, derived
by `paZeroOrSuccessor 0`).
-/

@[expose] public section

namespace Silmaril.Consequence.Arithmetic

open Silmaril.Logic.Arithmetic Silmaril.Logic.Arithmetic.Theorems Silmaril.Logic.Concrete
open Silmaril.Logic.Smt (SE)

/-- **PA is sound for ℕ.** -/
theorem pa_soundFor : paDerives.SoundFor standard :=
  fun _ _ ⟨d⟩ _ h => pa_sound d _ h

/-- **Q is sound for ℕ.** -/
theorem q_soundFor : qDerives.SoundFor standard :=
  fun _ _ ⟨d⟩ _ h => q_sound d _ h

theorem q_le_pa : qDerives ≤ paDerives := fun _ _ ⟨d⟩ => q_provable_in_pa d

/-- **PA is consistent**: it does not derive `false`, relative to the standard model ℕ. -/
theorem pa_consistent : paDerives.ConsistentWrt .bot [] :=
  consistentWrt_of_sound pa_soundFor () (by simp [standard, Satisfies]) (by simp [standard, Formula.eval])

/-- **Q is consistent.** -/
theorem q_consistent : qDerives.ConsistentWrt .bot [] :=
  consistentWrt_of_sound q_soundFor () (by simp [standard, Satisfies]) (by simp [standard, Formula.eval])

theorem pa_nontrivial : paDerives.ContextConsistent [] :=
  fun h => pa_consistent (h _)

/-- **PA over S-expressions is consistent**: `false`, as the S-expression `false`, is not derived. -/
theorem paConcrete_consistent :
    (paDerives.viaCodec SExp.sentenceCodec).ConsistentWrt (SExpCodec.Sen.ofAbs .bot) [] :=
  (viaCodec_consistentWrt_iff paDerives SExp.sentenceCodec [] .bot).2 pa_consistent

/-- PA over S-expressions is sound for ℕ over S-expressions. -/
theorem paConcrete_sound : paDerives.viaCodec SExp.sentenceCodec ≤ truth.viaCodec SExp.sentenceCodec :=
  viaCodec_mono SExp.sentenceCodec pa_soundFor

/-! ## Concrete problems -/

/-- `0 + 0 = 0`. -/
def zeroAddZero : Sentence := .equal (.add .zero .zero) .zero

/-- Its concrete form. -/
def zeroAddZeroSExp : SE :=
  .list [.atom "=", .list [.atom "+", .atom "zero", .atom "zero"], .atom "zero"]

theorem zeroAddZero_decode : SExp.sentenceCodec.decode zeroAddZeroSExp = some zeroAddZero :=
  (SExp.sentenceCodec.decode_eq_some_iff _ _).2 (by
    simp [SExp.codec, SExp.encodeFormula, SExp.encodeTerm, zeroAddZero, zeroAddZeroSExp])

/-- The problem has an explicit PA derivation. -/
theorem zeroAddZero_derived : paDerives [] zeroAddZero := ⟨paZeroAddZero⟩

/-- Its standard meaning: `0 + 0 = 0` in ℕ. -/
theorem zeroAddZero_true : zeroAddZero.eval Fin.elim0 := by simp [zeroAddZero, Formula.eval, Term.eval]

/-- Every number is zero or a successor. -/
def zeroOrSuccessor : Sentence := .all (zeroOrSuccessorBody 0)

/-- Its concrete form. -/
def zeroOrSuccessorSExp : SE := SExp.sentenceCodec.encode zeroOrSuccessor

theorem zeroOrSuccessor_decode : SExp.sentenceCodec.decode zeroOrSuccessorSExp = some zeroOrSuccessor :=
  SExp.sentenceCodec.decode_encode _

theorem zeroOrSuccessor_derived : paDerives [] zeroOrSuccessor := ⟨paZeroOrSuccessor 0⟩

/-- Its standard meaning, from soundness. -/
theorem zeroOrSuccessor_true : zeroOrSuccessor.eval Fin.elim0 :=
  pa_soundFor [] _ zeroOrSuccessor_derived () (by simp [standard, Satisfies])

end Silmaril.Consequence.Arithmetic
