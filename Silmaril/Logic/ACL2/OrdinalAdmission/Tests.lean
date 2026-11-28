module

import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
meta import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
import Mathlib.Data.Fin.VecNotation

namespace Silmaril.Logic.ACL2.OrdinalAdmission.Tests

open Ordinals Recursive

def omega : Encoding := .makeOrd (.natural 1) 1 (.natural 0)
def omegaPowOmega : Encoding := .makeOrd omega 1 (.natural 0)

example : omegaPowOmega.oP = true := by decide
example : (omega.makeOrd 1 omega).oP = true := by decide
example : omegaPowOmega.oLt (omega.makeOrd 1 omega) = true := by decide
example : (Encoding.makeOrd (.natural 8) 100 (.natural 50)).oLt omegaPowOmega = true := by decide
example (n : Nat) : (Encoding.natural n).oLt omega = true := rfl

-- Incorrect car shape, exponent, coefficient, tail, and exponent order.
example : ([
    .otherAtom, .cons (.natural 1) (.natural 0),
    .makeOrd (.natural 0) 1 (.natural 0), .makeOrd (.natural 1) 0 (.natural 0),
    .cons (.cons (.natural 1) .otherAtom) (.natural 0),
    .makeOrd (.natural 1) 1 .otherAtom, .makeOrd (.natural 1) 1 omega,
    .makeOrd (.natural 1) 1 omegaPowOmega] : List Encoding).all
    (fun x => (ValidOrdinal.ofEncoding? x).isNone) = true := by decide

-- Pinned ACL2 8.7 std/basic/two-nats-measure, with NFIX applied at the input boundary.
def twoNats (a b : Nat) : Encoding :=
  .makeOrd (.natural 2) (a + 1) (.makeOrd (.natural 1) (b + 1) (.natural 0))

theorem twoNats_valid (a b : Nat) : (twoNats a b).oP = true := rfl

theorem twoNats_lt (a b c d : Nat) :
    (twoNats a b).oLt (twoNats c d) = true ↔ a < c ∨ a = c ∧ b < d := by
  simp [twoNats, Encoding.makeOrd, Encoding.oLt, Encoding.cmp, Ordering.then_eq_lt,
    Nat.compare_eq_lt]

-- A local test carrier with conses and natural counters.
def primitives : Primitives where
  Value := Encoding
  nil := .otherAtom
  truth := .natural 0
  cons := .cons
  car := fun | .cons x _ => x | _ => .otherAtom
  cdr := fun | .cons _ y => y | _ => .otherAtom
  consp := fun | .cons .. => true | _ => false
  truth_ne_nil := by decide
  consp_nil := rfl
  consp_truth := rfl
  consp_cons _ _ := rfl
  car_cons _ _ := rfl
  cdr_cons _ _ := rfl
  car_atom x h := by cases x <;> simp_all
  cdr_atom x h := by cases x <;> simp_all

def nfix : Encoding → Nat
  | .natural n => n
  | _ => 0

def posName : Name := ⟨"ACL2", "POSP"⟩
def decName : Name := ⟨"ACL2", "NFIX-1-"⟩
def drainName : Name := ⟨"ACL2", "ORDINAL-DRAIN"⟩

def old : Signature := ⟨fun f => if f = posName ∨ f = decName then some 1 else none⟩
def members : Signature := ⟨fun f => if f = drainName then some 2 else none⟩

def pos : old.Symbol 1 := ⟨posName, by decide⟩
def dec : old.Symbol 1 := ⟨decName, by decide⟩
def drain : members.Symbol 2 := ⟨drainName, by decide⟩

theorem old_arity {k : Nat} (f : old.Symbol k) : k = 1 := by
  have h := f.property
  change (if f.val = posName ∨ f.val = decName then some 1 else none) = some k at h
  split at h <;> simp_all

theorem members_arity {k : Nat} (f : members.Symbol k) : k = 2 := by
  have h := f.property
  change (if f.val = drainName then some 2 else none) = some k at h
  split at h <;> simp_all

def oldModel : Model old where
  primitives := primitives
  interpret f args :=
    let n := nfix (args ⟨0, old_arity f ▸ (by decide : 0 < 1)⟩)
    if f.val = posName then primitives.ofBool (decide (0 < n)) else .natural (n - 1)

def tick (call : Body old members 2) : Body old members 2 :=
  .apply (.cons .truth (.var 0)) ![call]

-- Decrement y on the first branch. When y has drained, decrement x and reset y to x.
def body : Body old members 2 :=
  .ite (.app pos ![.var 1])
    (tick (.call drain ![.var 0, .app dec ![.var 1]]))
    (.ite (.app pos ![.var 0])
      (tick (.call drain ![.app dec ![.var 0], .var 0]))
      (.base .nil))

def block : Block old where
  members := members
  fresh := by
    intro name k declared
    have h : name = drainName := by
      by_contra hn
      simp [members, hn] at declared
    subst name
    decide
  body f := members_arity f ▸ body

def measure : Measure block oldModel := fun state =>
  let arity := members_arity state.symbol
  twoNats (nfix (state.args ⟨0, arity ▸ (by decide : 0 < 2)⟩))
    (nfix (state.args ⟨1, arity ▸ (by decide : 1 < 2)⟩))

theorem terminates : Terminates block oldModel measure := by
  refine ⟨fun _ => twoNats_valid _ _, ?_⟩
  rintro ⟨k, f, args⟩
  have hk := members_arity f
  subst k
  change body.CallsSatisfy oldModel args (fun next => Decreases measure next ⟨2, f, args⟩)
  simp only [body, tick, Body.CallsSatisfy, Call.ofTerms, Decreases, measure, Term.eval,
    Fin.forall_fin_one, Matrix.cons_val_zero, twoNats_lt]
  have hd : decName ≠ posName := by decide
  simp [oldModel, pos, dec, hd, primitives, Primitives.ofBool, Term.eval, nfix]
  omega

theorem equation : (block.equation drain).Holds terminates.model :=
  terminates.equation_holds drain

def run (x y : Encoding) : Encoding := terminates.interpret ⟨2, drain, ![x, y]⟩
def ticks : Nat → Encoding
  | 0 => .otherAtom
  | n + 1 => .cons (.natural 0) (ticks n)

-- Execute the admitted recursion on a reset and a non-natural input.
#guard run (.natural 2) (.natural 0) == ticks 5
#guard run .otherAtom (.natural 2) == ticks 2

-- O-P is required even for a state that takes no recursive calls.
example : ¬ Terminates block oldModel (fun _ => .makeOrd (.natural 0) 1 (.natural 0)) := by
  intro h
  have hf := h.valid ⟨2, drain, ![.natural 0, .natural 0]⟩
  contradiction

-- A valid but constant ordinal cannot justify the second-counter call.
example : ¬ Terminates block oldModel (fun _ => .natural 0) := by
  intro h
  have calls := h.decreases ⟨2, drain, ![.otherAtom, .natural 1]⟩
  have impossible : false = true := calls.1 (by decide) 0
  contradiction

#print axioms Encoding.oP_iff
#print axioms ValidOrdinal.lt_iff
#print axioms ValidOrdinal.cmp_eq_eq
#print axioms Encoding.oLt_makeOrd_iff
#print axioms ValidOrdinal.wellFounded
#print axioms Terminates.wellFounded
#print axioms Terminates.equation_holds
#print axioms Terminates.callInduction
#print axioms terminates
#print axioms equation

end Silmaril.Logic.ACL2.OrdinalAdmission.Tests
