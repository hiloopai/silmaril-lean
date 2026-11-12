module

public import Silmaril.Wasm.Tools.Wast.Syntax.Defs
import Silmaril.Proofs.Wasm.Tools.Wast.Syntax

/-!
# The `.wast` script grammar: round trips

Proofs in `Silmaril.Proofs.Wasm.Tools.Wast.Syntax`. For every level of the
grammar (`Val`, `QuoteWat`, `Invoke`, `Exec`, `Directive`, `Script`):

* **read ∘ print = id** on well-formed trees (`…ofSExp?_toSExp`): the printer is injective
  there and the reader inverts it;
* **print ∘ read = id** on everything the reader accepts (`…toSExp_of_ofSExp?`): the reader
  accepts exactly the S-expressions that are prints, so it neither invents nor normalizes.

Together: `Script.ofSExps?` is a bijection between the prints of well-formed scripts and
well-formed scripts, and every list of S-expressions it accepts is such a print
(`Script.read_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Formats Silmaril.Formats.SExpEncoding

theorem Val.read_print {v : Val} (h : v.WF) : Val.ofSExp? v.toSExp = some v :=
  Val.ofSExp?_toSExp v h

theorem Val.print_read {x : SExp} {v : Val} (h : Val.ofSExp? x = some v) : v.toSExp = x :=
  Val.toSExp_of_ofSExp? x v h

theorem QuoteWat.read_print {m : QuoteWat} (h : m.WF) : QuoteWat.ofSExp? m.toSExp = some m :=
  QuoteWat.ofSExp?_toSExp h

theorem QuoteWat.print_read {x : SExp} {m : QuoteWat} (h : QuoteWat.ofSExp? x = some m) :
    m.toSExp = x :=
  QuoteWat.toSExp_of_ofSExp? h

theorem Exec.read_print {e : Exec} (h : e.WF) : Exec.ofSExp? e.toSExp = some e :=
  Exec.ofSExp?_toSExp h

theorem Exec.print_read {x : SExp} {e : Exec} (h : Exec.ofSExp? x = some e) : e.toSExp = x :=
  Exec.toSExp_of_ofSExp? h

theorem Directive.read_print {d : Directive} (h : d.WF) : Directive.ofSExp? d.toSExp = some d :=
  Directive.ofSExp?_toSExp d h

theorem Directive.print_read {x : SExp} {d : Directive} (h : Directive.ofSExp? x = some d) :
    d.toSExp = x :=
  Directive.toSExp_of_ofSExp? x d h

/-- **Scripts: read ∘ print = id** on well-formed scripts. -/
theorem Script.read_print {s : Script} (h : s.WF) : Script.ofSExps? s.toSExps = some s :=
  Script.ofSExps?_toSExps h

/-- **Scripts: print ∘ read = id**: what the reader accepts is the print of its result. -/
theorem Script.print_read {xs : List SExp} {s : Script} (h : Script.ofSExps? xs = some s) :
    s.toSExps = xs :=
  Script.toSExps_of_ofSExps? h

/-- On well-formed scripts the reader is exactly the inverse of the printer. -/
theorem Script.read_iff {xs : List SExp} {s : Script} (hs : s.WF) :
    Script.ofSExps? xs = some s ↔ s.toSExps = xs := by
  constructor
  · exact Script.print_read
  · rintro rfl; exact Script.read_print hs

end Silmaril.Wasm.Tools.Wast
