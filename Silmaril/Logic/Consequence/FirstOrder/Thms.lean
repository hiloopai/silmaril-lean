module

public import Silmaril.Logic.Consequence.FirstOrder.Defs
public import Silmaril.Logic.Consequence.Soundness.Thms
public import Silmaril.Logic.Institution.Examples.Unsorted.SExp.Thms

/-!
# First-order logic: a specified structure, model existence, consequence and concrete problems

Over `orderSig` (`zero`, `succ`, `<`) and the structure `natStructure` (ℕ):

* `irrefl` (`∀x ¬ x < x`) and `ltSucc` (`∀x x < succ x`) form `orderTheory`;
  `natStructure_models` and `orderTheory_satisfiable`: ℕ is a model, so the theory has a model.
* `succIrrefl` (`∀x ¬ succ x < succ x`) is a semantic consequence of `orderTheory` in **every**
  structure (`orderTheory_entails_succIrrefl`).
* `orderTheory_nontrivial`: the theory's semantic consequence is not everything: `¬ true` does
  not follow, because ℕ is a model.
* Each sentence is decoded from its S-expression in the presentation `silmaril.fol.formula`
  (`irrefl_decode`, …).

There is no derivation system for this logic yet, so nothing here is about derivability.
-/

@[expose] public section

namespace Silmaril.Consequence.FirstOrder

open Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples.UFOL
open Silmaril.Logic.Concrete

/-- Two arguments. -/
def args2 {α : Type} (a b : α) : Fin 2 → α := fun i => if i.val = 0 then a else b
/-- One argument. -/
def args1 {α : Type} (a : α) : Fin 1 → α := fun _ => a

/-- The relation symbol `<`. -/
def lt : orderSig.Rel 2 := ⟨"<", rfl⟩
/-- The operation symbol `succ`. -/
def succ : orderSig.Op 1 := ⟨"succ", rfl⟩

/-- `∀x ¬ x < x`. -/
def irrefl : Sentence orderSig := .all (.not (.rel lt (args2 (.var 0) (.var 0))))
/-- `∀x x < succ x`. -/
def ltSucc : Sentence orderSig := .all (.rel lt (args2 (.var 0) (.app succ (args1 (.var 0)))))
/-- `∀x ¬ succ x < succ x`. -/
def succIrrefl : Sentence orderSig :=
  .all (.not (.rel lt (args2 (.app succ (args1 (.var 0))) (.app succ (args1 (.var 0))))))
/-- `¬ true`, the chosen falsity. -/
def falsity : Sentence orderSig := .not .tt

/-- **A concrete first-order theory.** -/
def orderTheory : List (Sentence orderSig) := [irrefl, ltSucc]

/-- **ℕ is a model of the theory.** -/
theorem natStructure_models : ∀ φ ∈ orderTheory, Sentence.Holds natStructure φ := by
  simp [orderTheory, irrefl, ltSucc, Sentence.Holds, Formula.Holds, Term.eval, natStructure, lt, succ, args1, args2]

theorem orderTheory_satisfiable : Room.Satisfiable (room orderSig) {φ | φ ∈ orderTheory} :=
  ⟨natStructure, natStructure_models⟩

/-- **A semantic consequence in every structure.** -/
theorem orderTheory_entails_succIrrefl : consequence orderSig orderTheory succIrrefl := by
  intro M hM
  have h := hM irrefl (List.mem_cons_self ..)
  intro x
  simpa [irrefl, Sentence.Holds, Formula.Holds, Term.eval, args1, args2] using h (M.op succ fun _ => x)

/-- **The theory's consequence is nontrivial**: `¬ true` does not follow. -/
theorem orderTheory_nontrivial : (consequence orderSig).ConsistentWrt falsity orderTheory := by
  intro h
  have : Sentence.Holds natStructure falsity := h natStructure natStructure_models
  simp [falsity, Sentence.Holds, Formula.Holds] at this

/-- `succIrrefl` holds in ℕ. -/
theorem succIrrefl_true : Sentence.Holds natStructure succIrrefl := by
  simp [succIrrefl, Sentence.Holds, Formula.Holds, Term.eval, natStructure, lt, succ, args1, args2]

/-! ## Concrete syntax -/

/-- The presentation of `orderSig` sentences. -/
abbrev orderCodec : SExpCodec (Sentence orderSig) := SExp.sentenceCodec orderOps orderRels

theorem irrefl_decode : orderCodec.decode (orderCodec.encode irrefl) = some irrefl :=
  orderCodec.decode_encode _

theorem succIrrefl_decode : orderCodec.decode (orderCodec.encode succIrrefl) = some succIrrefl :=
  orderCodec.decode_encode _

end Silmaril.Consequence.FirstOrder
