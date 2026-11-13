module

public import Silmaril.Cerberus.Elaboration.Freshness.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Freshness
open Silmaril.Cerberus

theorem integer_of_bound (context : Context) (bound : context.next ≤ context.maximum) :
    integer context = .ok (context.next, {context with next := context.next + 1}) :=
  ite_eq_left bound

theorem integer_exhausted (context : Context) (bound : context.maximum < context.next) :
    integer context = .error .exhausted :=
  ite_eq_right (Nat.not_le_of_lt bound)

theorem description_of_bound (context : Context) (value : SymbolDescription)
    (bound : context.next ≤ context.maximum) :
    description value context = .ok
      (⟨context.digest, context.next, value⟩, {context with next := context.next + 1}) := by
  rw [description, integer_of_bound context bound]
  rfl

/-- Changing a display description does not change Cerberus symbol identity. -/
theorem setDescription_key (symbol : Sym) (value : SymbolDescription) :
    (setDescription symbol value).key = symbol.key := rfl

/-- Consecutive allocation results differ by semantic identity, independently
of descriptions; the two-allocation equation below ties these shapes to the API. -/
theorem consecutive_keys_ne (context : Context) (first second : SymbolDescription) :
    (Sym.mk context.digest context.next first).key ≠
      (Sym.mk context.digest (context.next + 1) second).key := by
  intro same
  have numbers : context.next = context.next + 1 := congrArg Prod.snd same
  have increasing : context.next < context.next + 1 := Nat.lt_succ_self context.next
  exact (Nat.ne_of_lt increasing) numbers

theorem two_descriptions (context : Context) (first second : SymbolDescription)
    (bound : context.next + 1 ≤ context.maximum) :
    (do
      let (one, afterOne) ← description first context
      let (two, afterTwo) ← description second afterOne
      pure (one, two, afterTwo)) =
    (Except.ok
      (Sym.mk context.digest context.next first,
       Sym.mk context.digest (context.next + 1) second,
       {context with next := context.next + 1 + 1}) : Except Error (Sym × Sym × Context)) := by
  have firstBound : context.next ≤ context.maximum :=
    Nat.le_trans (Nat.le_succ context.next) bound
  simp [description, integer, firstBound, bound, bind, pure, Except.bind, Except.pure]

end Silmaril.Cerberus.Elaboration.Freshness
