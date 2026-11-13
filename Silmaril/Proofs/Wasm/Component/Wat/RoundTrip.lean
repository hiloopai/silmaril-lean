module

public import Silmaril.Proofs.Wasm.Component.Wat.Sections
public import Silmaril.Proofs.Wasm.Component.Wat.WF
public import Silmaril.Proofs.Wasm.Component.Wat.Norm
public import Silmaril.Proofs.Wasm.Component.Wat.Sexp

/-!
# Component WAT: the round trip

`read (print c) = some (norm c)`; printing does not see the normal form; hence
two components print the same text exactly when they have the same normal form,
and `norm` is idempotent.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

open Silmaril.Wasm.Component.Binary

/-- **Round trip.** Reading the printed text of a component gives its normal form. -/
theorem read_print (c : Ast) : read (print c) = some (norm c) := by
  unfold read print
  rw [Sexp.read_printAll [toSexp c] ((wfl_cons _ _).2 ⟨wf_toSexp c, wfl_nil⟩)]
  exact ofSexp_toSexp c

/-- Printing does not see the normal form. -/
theorem print_norm (c : Ast) : print (norm c) = print c := by
  unfold print
  rw [toSexp_norm]

/-- `norm` is idempotent. -/
theorem norm_norm (c : Ast) : norm (norm c) = norm c := by
  have h1 := read_print (norm c)
  rw [print_norm, read_print] at h1
  exact (Option.some.inj h1).symm

/-- Two components print the same text exactly when their normal forms agree. -/
theorem print_eq_iff (c d : Ast) : print c = print d ↔ norm c = norm d := by
  constructor
  · intro h
    have := read_print c
    rw [h, read_print] at this
    exact (Option.some.inj this).symm
  · intro h
    rw [← print_norm c, h, print_norm]

/-- On normal forms, reading inverts printing exactly. -/
theorem read_print_of_norm {c : Ast} (h : norm c = c) : read (print c) = some c := by
  rw [read_print, h]

/-- Every printed text is the printing of its reading. -/
theorem print_read {t : String} {c : Ast} (h : t = print c) :
    ∃ d, read t = some d ∧ print d = t := by
  subst h
  exact ⟨norm c, read_print c, print_norm c⟩

end Silmaril.Wasm.Component.Wat
