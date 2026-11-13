module

public import Silmaril.Cerberus.Elaboration.Lifetimes.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Lifetimes
open Silmaril.Cerberus
open Construction

/-- Diagnostic descriptions do not affect lifetime identity. -/
theorem contains_same_key (first second : Sym) (type : Ctype)
    (same : first.key = second.key) : contains first [(second, type)] = true := by
  simp only [contains, List.any_cons, List.any_nil, Bool.or_false, same, decide_true]

theorem returnRun_empty (location : Loc) (label : Sym) (arguments : List Pure) :
    returnRun location label [] arguments = Construction.run label arguments := rfl

theorem returnRun_singleton (location : Loc) (label symbol : Sym) (type : Ctype)
    (arguments : List Pure) :
    returnRun location label [(symbol, type)] arguments =
    strongSequence (wildcard .unit) (MemoryActions.staticKill location type (symbolPure symbol))
      (Construction.run label arguments) := rfl

end Silmaril.Cerberus.Elaboration.Lifetimes
