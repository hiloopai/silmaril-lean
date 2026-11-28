module

import Silmaril.Logic.ACL2.NatListMeasure.Thms
import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
meta import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
meta import Silmaril.Logic.ACL2.NatListMeasure.Defs
import Mathlib.Data.Fin.VecNotation

namespace Silmaril.Logic.ACL2.NatListMeasure.Tests

open Ordinals Recursive

example : ordinalMeasure (.cons .otherAtom (.natural 5)) =
    .makeOrd (.natural 1) 1 (.natural 5) := rfl
example : lt (.cons (.natural 3) (.natural 7)) (.cons (.natural 3) (.natural 8)) := by decide
example : lt (.cons (.natural 999) .otherAtom) (pair (.natural 0) (.natural 0)) := by decide
example : lt (.natural 999) (.cons (.natural 0) .otherAtom) := by decide
example : ¬ lt (pair (.cons (.natural 1) .otherAtom) .otherAtom)
    (pair (.natural 0) (.natural 0)) := by decide

/-- A fixture projection retaining naturals, conses, NIL, and the ACL2-COUNT of
every other atom. Those atoms act as non-naturals in NFIX, POSP, and POS-FIX. -/
inductive Value where
  | nil
  | natural (n : Nat)
  | atom (count : Nat)
  | cons (car cdr : Value)
  deriving DecidableEq, Repr

def Value.project : Value → Encoding
  | .natural n => .natural n
  | .cons x y => .cons x.project y.project
  | _ => .otherAtom

def Value.acl2Count : Value → Nat
  | .nil => 0
  | .natural n | .atom n => n
  | .cons x y => 1 + x.acl2Count + y.acl2Count

def Value.posFix (x : Value) : Nat := if nfix x.project = 0 then 1 else nfix x.project

/-- The measure terms in the ACL2 justification records for the mutual block.
The arguments omitted from the projection occur in neither measure. -/
def evMeasure (x clk : Value) : Encoding := pair clk.project (.natural x.acl2Count)
def listMeasure (x clk : Value) : Encoding := pair (.natural clk.posFix) (.natural x.acl2Count)

theorem call_cdr (a d clk : Value) (h : 0 < nfix clk.project) :
    lt (listMeasure d clk) (evMeasure (.cons a d) clk) := by
  apply (pair_lt_iff _ _ _ _).2
  change clk.posFix < nfix clk.project ∨
    clk.posFix = nfix clk.project ∧ d.acl2Count < 1 + a.acl2Count + d.acl2Count
  simp [Value.posFix, Nat.ne_of_gt h]

theorem list_call_car (a d clk : Value) :
    lt (evMeasure a clk) (listMeasure (.cons a d) clk) := by
  apply (pair_lt_iff _ _ _ _).2
  change nfix clk.project < clk.posFix ∨
    nfix clk.project = clk.posFix ∧ a.acl2Count < 1 + a.acl2Count + d.acl2Count
  by_cases h : nfix clk.project = 0 <;> simp [Value.posFix, h]
  omega

theorem list_call_cdr (a d clk : Value) :
    lt (listMeasure d clk) (listMeasure (.cons a d) clk) := by
  simp [listMeasure, pair_lt_iff, nfix, Value.acl2Count]

-- The exported fallback call passes the looked-up BODY at (1- CLK).
-- Its count can grow arbitrarily. The earlier negated ZP test fixes CLK to a positive integer.
theorem fallback_clock (x resolved : Value) (clk : Nat) (h : 0 < clk) :
    lt (evMeasure resolved (.natural (clk - 1))) (evMeasure x (.natural clk)) :=
  (pair_lt_iff _ _ _ _).2 (Or.inl (Nat.sub_lt h (by decide)))

def primitives : Primitives where
  Value := Value
  nil := .nil
  truth := .atom 0
  cons := .cons
  car := fun | .cons x _ => x | _ => .nil
  cdr := fun | .cons _ y => y | _ => .nil
  consp := fun | .cons .. => true | _ => false
  truth_ne_nil := by decide
  consp_nil := rfl
  consp_truth := rfl
  consp_cons _ _ := rfl
  car_cons _ _ := rfl
  cdr_cons _ _ := rfl
  car_atom x h := by cases x <;> simp_all
  cdr_atom x h := by cases x <;> simp_all

def posName : Name := ⟨"ACL2", "POSP"⟩
def evName : Name := ⟨"GL", "MAGICER-EV"⟩
def listName : Name := ⟨"GL", "MAGICER-EV-LST"⟩

def old : Signature := ⟨fun f => if f = posName then some 1 else none⟩
def members : Signature := ⟨fun f => if f = evName ∨ f = listName then some 2 else none⟩

def pos : old.Symbol 1 := ⟨posName, by decide⟩
def ev : members.Symbol 2 := ⟨evName, by decide⟩
def evList : members.Symbol 2 := ⟨listName, by decide⟩

theorem old_arity {k : Nat} (f : old.Symbol k) : k = 1 := by
  have h := f.property
  change (if f.val = posName then some 1 else none) = some k at h
  split at h <;> simp_all

theorem member_info {k : Nat} (f : members.Symbol k) :
    k = 2 ∧ (f.val = evName ∨ f.val = listName) := by
  have h := f.property
  change (if f.val = evName ∨ f.val = listName then some 2 else none) = some k at h
  split at h <;> simp_all

def oldModel : Model old where
  primitives := primitives
  interpret f args :=
    let clock := args ⟨0, old_arity f ▸ (by decide : 0 < 1)⟩
    primitives.ofBool (decide (0 < nfix clock.project))

-- Project just the lambda argument-list call. A cons CAR rules out the NIL, atom
-- and QUOTE exits. POSP is the successful branch of the logical ZP test.
def evBody : Body old members 2 :=
  .ite (.consp (.car (.var 0)))
    (.ite (.app pos ![.var 1]) (.call evList ![.cdr (.var 0), .var 1]) (.base .nil))
    (.base .nil)

-- Project both calls of the successful list branch. Requiring decrease of the
-- cdr call even if the car call returns an error strengthens its obligation.
def listBody : Body old members 2 :=
  .ite (.consp (.var 0))
    (.apply (.cons (.var 0) (.var 1))
      ![.call ev ![.car (.var 0), .var 1], .call evList ![.cdr (.var 0), .var 1]])
    (.base .nil)

def block : Block old where
  members := members
  fresh := by
    intro name k declared
    have h := (member_info ⟨name, declared⟩).2
    change name = evName ∨ name = listName at h
    obtain rfl | rfl := h <;> decide
  body f := (member_info f).1 ▸ (if f.val = evName then evBody else listBody)

def rank : OrdinalAdmission.Measure block oldModel := fun s =>
  let h := (member_info s.symbol).1
  let x := s.args ⟨0, h ▸ (by decide : 0 < 2)⟩
  let clk := s.args ⟨1, h ▸ (by decide : 1 < 2)⟩
  if s.symbol.val = evName then evMeasure x clk else listMeasure x clk

theorem projection_terminates : Terminates block oldModel rank := by
  rintro ⟨k, f, args⟩
  obtain ⟨hk, hf⟩ := member_info f
  subst k
  rcases hf with h | h
  · have he : f = ev := Subtype.ext h
    subst f
    change evBody.CallsSatisfy oldModel args
      (fun next => lt (rank next) (evMeasure (args 0) (args 1)))
    simp only [evBody, Body.CallsSatisfy, Term.eval]
    refine ⟨fun hcons => ⟨?_, fun _ => trivial⟩, fun _ => trivial⟩
    intro hpos
    have hp : 0 < nfix (Value.project (args 1)) := by
        simp [oldModel, primitives, Primitives.ofBool, Term.eval] at hpos
        omega
    cases hx : args 0 with
    | nil | natural | atom => simp [oldModel, primitives, hx, Primitives.ofBool] at hcons
    | cons a d =>
      have hne : listName ≠ evName := by decide
      simpa [rank, Call.ofTerms, evList, hne, Term.eval, oldModel, primitives, hx]
        using call_cdr a d (args 1) hp
  · have hl : f = evList := Subtype.ext h
    subst f
    change listBody.CallsSatisfy oldModel args
      (fun next => lt (rank next) (listMeasure (args 0) (args 1)))
    simp only [listBody, Body.CallsSatisfy, Term.eval]
    constructor
    · intro hcons
      rw [Fin.forall_fin_two]
      cases hx : args 0 with
      | nil | natural | atom => simp [oldModel, primitives, hx, Primitives.ofBool] at hcons
      | cons a d =>
        have hne : listName ≠ evName := by decide
        simpa [Body.CallsSatisfy, rank, Call.ofTerms, ev, evList, hne, Term.eval, oldModel,
          primitives, hx] using ⟨list_call_car a d (args 1), list_call_cdr a d (args 1)⟩
    · exact fun _ => trivial

theorem admitted : OrdinalAdmission.Terminates block oldModel
    (fun state => ordinalMeasure (rank state)) := projection_terminates.toOrdinal

theorem ev_equation : (block.equation ev).Holds admitted.model := admitted.equation_holds ev
theorem list_equation : (block.equation evList).Holds admitted.model := admitted.equation_holds evList

def run (x clk : Value) : Value := admitted.interpret ⟨2, ev, ![x, clk]⟩

-- Authored projection outputs, not the result values of the stateful upstream interpreter.
#guard run (.cons (.cons .nil .nil) (.cons (.natural 4) .nil)) (.natural 1) == .cons .nil .nil
#guard run (.cons (.cons .nil .nil) (.cons (.natural 4) .nil)) .nil == .nil

#print axioms NatListMeasure.valid
#print axioms NatListMeasure.lt_cons_cons
#print axioms NatListMeasure.wellFounded
#print axioms Terminates.toOrdinal
#print axioms fallback_clock
#print axioms projection_terminates
#print axioms ev_equation
#print axioms list_equation

end Silmaril.Logic.ACL2.NatListMeasure.Tests
