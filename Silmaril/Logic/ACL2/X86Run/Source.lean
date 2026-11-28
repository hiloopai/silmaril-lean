-- Generated from corpus/acl2/x86-run/acl2-8.7.json by tools/acl2-x86isa/check_x86_run.py.
module

public import Silmaril.Logic.ACL2.X86Run.Signature
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run

open Recursive

example : (addSymbol : old.Symbol 2).val = ⟨"ACL2", "BINARY-+"⟩ := rfl
example : (zpSymbol : old.Symbol 1).val = ⟨"ACL2", "ZP"⟩ := rfl
example : (faultSymbol : old.Symbol 1).val = ⟨"X86ISA", "FAULT"⟩ := rfl
example : (msSymbol : old.Symbol 1).val = ⟨"X86ISA", "MS"⟩ := rfl
example : (stepSymbol : old.Symbol 1).val = ⟨"X86ISA", "X86-FETCH-DECODE-EXECUTE"⟩ := rfl
example : (runSymbol : members.Symbol 2).val = ⟨"X86ISA", "X86-RUN"⟩ := rfl

def sourceBody : Body old members 2 :=
  .ite (.app faultSymbol (fun _ => .var 1))
    (.base (.var 1))
    (.ite (.app msSymbol (fun _ => .var 1))
      (.base (.var 1))
      (.ite (.app zpSymbol (fun _ => .var 0))
        (.base (.var 1))
        (.call runSymbol
          ![.app addSymbol ![.app minusOneSymbol Fin.elim0, .var 0],
            .app stepSymbol (fun _ => .var 1)])))

def declaration : Block old := block sourceBody

def halted : Sentence declaration.signature :=
  ⟨2, Term.implies
    (.ite
      (.app (declaration.inclusion.symbol msSymbol) (fun _ => .var 1))
      (.app (declaration.inclusion.symbol msSymbol) (fun _ => .var 1))
      (.app (declaration.inclusion.symbol faultSymbol) (fun _ => .var 1)))
    (.equal (.app (declaration.symbol runSymbol) Term.var) (.var 1))⟩

end Silmaril.Logic.ACL2.X86Run
